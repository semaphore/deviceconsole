#include <stdio.h>
#include <regex.h>
#include <CoreFoundation/CoreFoundation.h>
#include <pwd.h>
#include <sys/stat.h>
#include "MobileDevice.h"

#define writeConst(fd, text) writeFully(fd, text, sizeof(text)-1)
#define spush(message, text) strncat(message, text, strnlen(text, BUFSIZ));
#define RESET               "\e[m"
#define FORMAT_BOLD         "\e[1m"
#define FORMAT_DIM          "\e[2m"
#define FORMAT_NORMAL       "\e[21m"
#define FORMAT_UNDERLINE    "\e[4m"
#define FORMAT_BLINK        "\e[5m"
#define COLOR_DEFAULT       "\e[39m"
#define COLOR_NORMAL        "\e[0m"
#define COLOR_LIGHT_RED     "\e[91m"
#define COLOR_RED           "\e[0;31m"
#define COLOR_DARK_RED      "\e[2;31m"
#define COLOR_LIGHT_GREEN   "\e[92m"
#define COLOR_GREEN         "\e[0;32m"
#define COLOR_DARK_GREEN    "\e[2;32m"
#define COLOR_LIGHT_YELLOW  "\e[0;93m"
#define COLOR_YELLOW        "\e[0;33m"
#define COLOR_DARK_YELLOW   "\e[2;33m"
#define COLOR_LIGHT_BLUE    "\e[0;94m"
#define COLOR_BLUE          "\e[0;34m"
#define COLOR_DARK_BLUE     "\e[2;34m"
#define COLOR_LIGHT_MAGENTA "\e[0;95m"
#define COLOR_MAGENTA       "\e[0;35m"
#define COLOR_DARK_MAGENTA  "\e[2;35m"
#define COLOR_LIGHT_CYAN    "\e[0;96m"
#define COLOR_CYAN          "\e[0;36m"
#define COLOR_DARK_CYAN     "\e[2;36m"
#define COLOR_LIGHT_GRAY    "\e[0;37m"
#define COLOR_WHITE         "\e[0;97m"
#define COLOR_DARK_GRAY     "\e[0;90m"
typedef struct {
    service_conn_t connection;
    CFSocketRef socket;
    CFRunLoopSourceRef source;
} DeviceConsoleConnection;

enum LOG_CHANNEL {
    LOG_PID = 0, LOG_DATE, LOG_TYPE, LOG_NAME, LOG_LIBRARY, LOG_PROCESS, LOG_MESSAGE,
};

enum MATCH_ACTION {
    HIDE, SHOW, HIGHLIGHT
};

typedef struct {
    bool matched;
    bool skipped;
    char *pid;
    char *date;
    char *type;
    char *name;
    char *library;
    char *process;
    char *color;
    char *message;
    char *line;
} LogEntry;

typedef struct {
    char *name;
    char *search;
    regex_t regex;
    bool regexCompiled;
} LogEntryMatcher;

static void __log(const char* fname, const char* level, const char* format, ...)
{
    fprintf(stdout, "%s: %s() ", level, fname);
    va_list args;
    va_start (args, format);
    vfprintf (stdout, format, args);
    va_end (args);
}

#define debug(format, ...) if(debug) { __log(__func__, COLOR_LIGHT_GREEN "D" , format, ##__VA_ARGS__); }
#define info(format, ...) __log(__func__, COLOR_NORMAL "I" , format, ##__VA_ARGS__)

static void createLogMatcher(enum LOG_CHANNEL channel, enum MATCH_ACTION matchAction, const char *name, const char *search);

static LogEntryMatcher *LogEntryMatcherInit(void);

static void freeLogEntryMatcher(LogEntryMatcher *matcher);

void readOpt(char **dst, const char *optarg);

void readOrAppendOpt(char **dst, const char *optarg);

void reassign(char **dst, const char *src);

bool prefix(const char *pre, const char *str);

bool exists(const char *value);

void scrubMessage(char **value);

void maybeFree(void *value, const char *note);

char *strrep(char *orig, const char *rep, const char *with);

static LogEntry *LogEntryInit(void);

static void freeLogEntry(LogEntry *entry);

void checkConfig(void);

static LogEntryMatcher *matchers[HIGHLIGHT + 1][LOG_MESSAGE + 1];
static CFMutableDictionaryRef liveConnections;
static CFStringRef requiredDeviceId;

static int debug = 0;

static regex_t logEntryRegex;
static bool showMatches = false;
static char *lastColor, *spammyProcs;
static bool skippedLast = false;

static size_t datelen = 17;
static size_t devicelen = 0;


//                         [Date                                                    ]    [Name        ]    [P(L)?[PID]?]      [Type        ]      [Msg]
static const char *reg = "^([[:alpha:]]{3}\\s+\\d{1,2}\\s+\\d{2}:\\d{2}:\\d{2})\\s+([[:graph:]]+)\\s+([[:print:]]+)\\s+<([[:alpha:]]+)>:\\s+(.*)$";
static const size_t maxGroups = 7;

static const char *DEFAULT_SPAMMY = "^aggregated.*"
                                    "|^apsd.*"
                                    "|^awdd.*"
                                    "|^bluetoothd.*"
                                    "|^callservicesd.*"
                                    "|^com\\.apple\\.siri.*"
                                    "|^commcenter.*"
                                    "|^coreduetd.*"
                                    "|^dasd.*"
                                    "|^dataaccessd.*"
                                    "|^gamed.*"
                                    "|^healthd.*"
                                    "|^homed.*"
                                    "|^identityservicesd.*"
                                    "|^imagent.*"
                                    "|^kernel.*"
                                    "|^locationd.*"
                                    "|^mobileassetd.*"
                                    "|^mobilewatchdog.*"
                                    "|^navd.*"
                                    "|^nsurlsessiond.*"
                                    "|^powerd.*"
                                    "|^routined.*"
                                    "|^sharingd.*"
                                    "|^springboard.*"
                                    "|^symptomsd.*"
                                    "|^usereventagent.*"
                                    "|^vmd.*"
                                    "|^wifid.*"
                                    "|^wirelessproxd.*"
                                    "|^wirelessradiomanagerd.*";

static inline void writeFully(int fd, char *buffer, size_t length) {
    while (length) {
        ssize_t result = write(fd, buffer, length);
        if (result == -1)
            break;
        buffer += result;
        length -= result;
    }
}

static char matchEntry(const char *value, LogEntryMatcher *matcher) {
    char result = 0;
    if (matcher == NULL) {
        return result;
    }
    if (matcher->regexCompiled) {
        if (regexec(&matcher->regex, value, 0, NULL, 0) == 0) {
            if (showMatches) {
                size_t vlen = strlen(value);
                if(vlen > 0 && value[vlen - 1] == '\n') {
                    char *nvalue = strdup(value);
                    nvalue[vlen - 1] = '\0';
                    printf("%s[%s%s%s] vs [%s%s%s]\n", COLOR_NORMAL, COLOR_DARK_YELLOW, matcher->name, COLOR_NORMAL, COLOR_LIGHT_YELLOW, nvalue, COLOR_NORMAL);
                    maybeFree(nvalue, "nvalue");
                } else {
                    printf("%s[%s%s%s] vs [%s%s%s]\n", COLOR_NORMAL, COLOR_DARK_YELLOW, matcher->name, COLOR_NORMAL, COLOR_LIGHT_YELLOW, value, COLOR_NORMAL);
                }
            }
            result = 1;
        } else {
            result = -1;
        }
    }
    if (result <= 0 && strcmp(matcher->search, value) == 0) {
        result = 1;
    } else if (result < 0 && prefix(matcher->search, value)) {
        result = 1;
    }
    return result;
}

static bool shouldPrintLogEntry(size_t length, LogEntry *entry) {
    enum LOG_CHANNEL index;
    char showMatch = 0;
    char hideMatch = 0;
    for (index = LOG_PID; index < LOG_MESSAGE + 1; index++) {
        char *tocheck = NULL;
        switch (index) {
            case LOG_PID:
                tocheck = entry->pid;
                break;
            case LOG_DATE:
                tocheck = entry->date;
                break;
            case LOG_TYPE:
                tocheck = entry->type;
                break;
            case LOG_NAME:
                tocheck = entry->name;
                break;
            case LOG_LIBRARY:
                tocheck = entry->library;
                break;
            case LOG_PROCESS:
                tocheck = entry->process;
                break;
            case LOG_MESSAGE:
                tocheck = entry->message;
                break;
        }
        if (tocheck && matchers[HIDE][index]) {
            hideMatch = hideMatch <= 0 ? matchEntry(tocheck, matchers[HIDE][index]) : hideMatch;
        }
        if (hideMatch <= 0 && tocheck && matchers[SHOW][index]) {
            showMatch = showMatch <= 0 ? matchEntry(tocheck, matchers[SHOW][index]) : showMatch;
        }
    }
    entry->skipped = !(showMatch >= 0 && hideMatch <= 0);
    return showMatch >= 0 && hideMatch <= 0;
}

static bool parseMessage(LogEntry *entry, const char *cursor) {
    //fastskip
    if (matchEntry(cursor + datelen + devicelen, matchers[HIDE][LOG_PROCESS]) == 1) {
        entry->skipped = true;
        return false;
    }
    regmatch_t groupArray[maxGroups];
    if ((regexec(&logEntryRegex, cursor, maxGroups, groupArray, 0)) > 0) {
        if (skippedLast) {
            return false;
        }
        entry->matched = false;
        reassign(&entry->line, cursor);
        reassign(&entry->message, cursor);
        return true;  // No more matches
    }
    entry->matched = true;
    unsigned int g = 0;
    if (exists(entry->line)) {
        size_t len = sizeof(char)*strlen(entry->line) + sizeof(char)*strlen(cursor);
        char *tmp = malloc(len + 1);
        tmp[0] = '\0';
        strcpy(tmp, entry->line);
        strcat(tmp, cursor);
        maybeFree(tmp, "tmp");
    } else {
        reassign(&entry->line, cursor);
    }
    for (g = 1; g < maxGroups; g++) {
        if (groupArray[g].rm_so == (size_t) -1)
            break;  // No more groups

        size_t len = (size_t) (groupArray[g].rm_eo - groupArray[g].rm_so);
        char *cursorCopy = malloc(len + 1);
        if(groupArray[g].rm_so > -1) {
            strncpy(cursorCopy, cursor + groupArray[g].rm_so, len);
        }
        cursorCopy[len] = '\0';
        switch (g) {
            case 1:
                reassign(&entry->date, cursorCopy);
                break;
            case 2:
                reassign(&entry->name, cursorCopy);
                break;
            case 3: {
                char *pid = strstr(cursorCopy, "[");
                char *lib = strstr(cursorCopy, "(");
                if (pid != NULL) {
                    pid++;
                    char *token, *str, *tofree;
                    tofree = str = strdup(pid);
                    token = strsep(&str, "]");
                    if (token != NULL) {
                        reassign(&entry->pid, token);
                    }
                    maybeFree(tofree, "tofree");
                    if (lib == NULL) {
                        tofree = str = strdup(cursorCopy);
                        token = strsep(&str, "[");
                        if (token != NULL) {
                            reassign(&entry->process, token);
                        }
                        maybeFree(tofree, "tofree");
                    }
                }
                if (lib != NULL) {
                    lib++;
                    char *token, *str, *tofree;
                    tofree = str = strdup(lib);
                    token = strsep(&str, ")");
                    if (token != NULL) {
                        reassign(&entry->library, token);
                    }
                    maybeFree(tofree, "tofree");
                    tofree = str = strdup(cursorCopy);
                    token = strsep(&str, "(");
                    if (token != NULL) {
                        reassign(&entry->process, token);
                    }
                    maybeFree(tofree, "tofree");
                }
            }
                break;
            case 4:
                reassign(&entry->type, cursorCopy);
                break;
            case 5:
                reassign(&entry->message, cursorCopy);
                break;
            default:
                break;
        }
        maybeFree(cursorCopy, "cursorCopy");
    }
    return true;
}

void reassign(char **dst, const char *src) {
    if(src == NULL) {
        return;
    }
    if(exists(*dst)) {
        maybeFree(*dst, "reassign *dst");
        (*dst) = NULL;
    }
    *dst = strdup(src);
}

bool prefix(const char *pre, const char *str) {
    char cp;
    char cs = '\0';
    if (!*pre)
        return true;
    while ((cp = *pre++) && (cs = *str++)) {
        if (cp != cs)
            return false;
    }
    if (!cs)
        return false;
    return true;
}

bool exists(const char *value) {
    return value != NULL;
}

void maybeFree(void *value, const char* note) {
    debug("FREED %s\n", note);
    free(value);
}

const unsigned int fsize = 9;
char *finds[][fsize] = (char *[][fsize]) {{"\\134", "\\M-b\\M^@\\M-&", "\\M-b\\M^T\\M^O", "\\M-b\\M^T\\M^C", "\\M-b\\M^T\\M^W", "\\M-b\\M^@\\M^Y", "\\M-B\\240", "\\n", "\\^[["},
                                          {"\\",    "…",               "┏","┃","┗","'", " ",          "\n",  "\e["}};

void scrubMessage(char **value) {
    int i = 0;
    for (; i < sizeof(finds[i]) / sizeof(char *); i++) {
        char *find = finds[0][i];
        char *rep = finds[1][i];
        char *n = strrep(*value, find, rep);
        if (n != NULL) {
            reassign(value, n);
            maybeFree(n, "n");
        }
    }
}

void ensureNewLine(char **message) {
    if(message == NULL || *message == NULL)
        return;
    size_t mlen = strlen(*message);
    if ((*message)[mlen - 1] != '\n') {
        if (mlen + 1 > 5 * BUFSIZ) {
            char *tmp = strdup(*message);
            maybeFree(*message, "message");
            *message = malloc(mlen + 1);
            (*message)[0] = '\0';
            strcpy(*message, tmp);
            maybeFree(tmp, "tmp");
        }
        (*message)[mlen+1] = '\n';
    }
}

static const char *spc = " ";
static const char *colon = ":";

static void writeLogEntry(int fd, LogEntry *buffer) {
    if (buffer->skipped) {
        return;
    }
    char *message = malloc(5 * BUFSIZ);
    message[0] = '\0';
    if (!buffer->matched) {
        if (exists(lastColor)) {
            reassign(&buffer->color, lastColor);
            maybeFree(lastColor, "lastColor");
            lastColor = NULL;
            spush(message, buffer->color);
        } else {
            spush(message, FORMAT_NORMAL COLOR_LIGHT_GRAY);
        }
        spush(message, buffer->message);
        ensureNewLine(&message);
        scrubMessage(&message);
        writeFully(fd, message, strlen(message));
        maybeFree(message, "message write free");
        return;
    }
    if (exists(buffer->date)) {
        spush(message, FORMAT_NORMAL COLOR_NORMAL);
        spush(message, buffer->date);
        spush(message, spc);
    }
    if (exists(buffer->name)) {
        spush(message, COLOR_LIGHT_BLUE);
        spush(message, buffer->name);
        spush(message, spc);
    }
    bool litproc = false;
    if (exists(buffer->process)) {
        if (matchEntry(buffer->process, matchers[HIGHLIGHT][LOG_PROCESS]) > 0) {
            spush(message, FORMAT_BOLD COLOR_LIGHT_YELLOW);
            spush(message, buffer->process);
            spush(message, FORMAT_NORMAL);
            litproc = true;
        } else {
            spush(message, COLOR_CYAN);
            spush(message, buffer->process);
        }
    }
    if (exists(buffer->library)) {
        if (litproc || matchEntry(buffer->library, matchers[HIGHLIGHT][LOG_LIBRARY]) > 0) {
            spush(message, FORMAT_BOLD COLOR_DARK_YELLOW);
            size_t libsize = sizeof(char)*strlen(buffer->library) + sizeof(char)*2+1;
            char *lib = malloc(libsize);
            lib[0] = '\0';
            snprintf(lib, libsize, "(%s)", buffer->library);
            spush(message, lib);
            maybeFree(lib, "lib");
            spush(message, FORMAT_NORMAL);
        } else {
            spush(message, COLOR_DARK_CYAN);
            size_t libsize = sizeof(char)*strlen(buffer->library) + sizeof(char)*2+1;
            char *lib = malloc(libsize);
            lib[0] = '\0';
            snprintf(lib, libsize, "(%s)", buffer->library);
            spush(message, lib);
            maybeFree(lib, "lib");
        }
    }
    if (exists(buffer->pid)) {
        if (litproc) {
            spush(message, FORMAT_BOLD COLOR_DARK_YELLOW);
            size_t libsize = sizeof(char)*strlen(buffer->pid) + sizeof(char)*2+1;
            char *lib = malloc(libsize);
            lib[0] = '\0';
            snprintf(lib, libsize, "[%s]", buffer->pid);
            spush(message, lib);
            maybeFree(lib, "lib");
            spush(message, FORMAT_NORMAL);
            litproc = true;
        } else {
            spush(message, COLOR_DARK_CYAN);
            size_t libsize = sizeof(char)*strlen(buffer->pid) + sizeof(char)*2+1;
            char *lib = malloc(libsize);
            lib[0] = '\0';
            snprintf(lib, libsize, "[%s]", buffer->pid);
            spush(message, lib);
            maybeFree(lib, "lib");
        }
    }
    spush(message, spc);
    if (exists(buffer->type)) {
        size_t levelLength = strlen(buffer->type);
        if (levelLength > 4) {
            const char *logLevelColor;
            const char *msgLevelColor;
            if (strcmp(buffer->type, "Debug") == 0 || strcmp(buffer->type, "TRACE") == 0) {
                logLevelColor = COLOR_DARK_MAGENTA;
                msgLevelColor = litproc ? FORMAT_BOLD COLOR_LIGHT_MAGENTA : COLOR_LIGHT_MAGENTA;
            } else if (strcmp(buffer->type, "Warning") == 0) {
                logLevelColor = COLOR_DARK_YELLOW;
                msgLevelColor = litproc ? FORMAT_BOLD COLOR_LIGHT_YELLOW : COLOR_LIGHT_YELLOW;
            } else if (strcmp(buffer->type, "Error") == 0) {
                logLevelColor = COLOR_DARK_RED;
                msgLevelColor = litproc ? FORMAT_BOLD COLOR_LIGHT_RED : COLOR_LIGHT_RED;
            } else if (strcmp(buffer->type, "Notice") == 0) {
                logLevelColor = litproc ? FORMAT_BOLD COLOR_LIGHT_GRAY : COLOR_DARK_GRAY;
                msgLevelColor = litproc ? FORMAT_BOLD COLOR_LIGHT_GRAY : COLOR_DARK_GRAY;
            } else if (strcmp(buffer->type, "Fault") == 0) {
                logLevelColor = FORMAT_UNDERLINE COLOR_LIGHT_GRAY;
                msgLevelColor = litproc ? FORMAT_BOLD COLOR_LIGHT_GRAY : COLOR_DARK_GRAY;
            } else {
                goto level_unformatted;
            }
            spush(message, logLevelColor);
            spush(message, buffer->type);
            spush(message, colon);
            spush(message, RESET COLOR_NORMAL);
            spush(message, spc);
            if (exists(buffer->message)) {
                //                scrubMessage(&buffer->message);
                if (!litproc && matchEntry(buffer->message, matchers[HIGHLIGHT][LOG_MESSAGE]) > 0) {
                    reassign(&buffer->color, COLOR_LIGHT_YELLOW);
                    spush(message, COLOR_LIGHT_YELLOW);
                    spush(message, buffer->message);
                } else {
                    reassign(&buffer->color, msgLevelColor);
                    spush(message, msgLevelColor);
                    spush(message, buffer->message);
                }
            }
        } else {
            level_unformatted:
            spush(message, COLOR_LIGHT_GRAY);
            spush(message, buffer->type);
            spush(message, RESET);
            spush(message, colon);
            spush(message, spc);
            if (exists(buffer->message)) {
                //                scrubMessage(&buffer->message);
                if (!litproc && matchEntry(buffer->message, matchers[HIGHLIGHT][LOG_MESSAGE]) > 0) {
                    reassign(&buffer->color, COLOR_LIGHT_YELLOW);
                    spush(message, COLOR_LIGHT_YELLOW);
                    spush(message, buffer->message);
                    spush(message, spc);
                } else {
                    reassign(&buffer->color, COLOR_LIGHT_GRAY);
                    spush(message, COLOR_LIGHT_GRAY);
                    spush(message, buffer->message);
                    spush(message, spc);
                }
            }
        }
    } else {
        if (exists(buffer->message)) {
            if (matchEntry(buffer->message, matchers[HIGHLIGHT][LOG_MESSAGE]) > 0) {
                reassign(&buffer->color, COLOR_LIGHT_YELLOW);
                spush(message, COLOR_LIGHT_YELLOW);
                spush(message, buffer->message);
            } else {
                //                scrubMessage(&buffer->message);
                reassign(&buffer->color, COLOR_LIGHT_GRAY);
                spush(message, COLOR_LIGHT_GRAY);
                spush(message, buffer->message);
            }
        }
    }
    ensureNewLine(&message);
    scrubMessage(&message);
    writeFully(fd, message, strlen(message));
    maybeFree(message, "message");
}

static void SocketCallback(CFSocketRef s, CFSocketCallBackType type, CFDataRef address, const void *data, void *info) {
    // Skip null bytes
    if(!data) {
        return;
    }
    ssize_t length = CFDataGetLength(data);
    const char *buffer = (const char *) CFDataGetBytePtr(data);
    LogEntry *entry = LogEntryInit();
    while (length) {
        while (*buffer == '\0') {
            buffer++;
            length--;
            if (length == 0) {
                freeLogEntry(entry);
                return;
            }
        }
        size_t extentLength = 0;
        while ((buffer[extentLength] != '\0') && extentLength != length) {
            extentLength++;
        }
        if (extentLength > 0 && parseMessage(entry, buffer)) {
            if (shouldPrintLogEntry(extentLength, entry)) {
                writeLogEntry(1, entry);
            }
        } else {
            entry->skipped = true;
        }
        length -= extentLength;
        buffer += extentLength;
    }
    skippedLast = entry->skipped;
    if (exists(entry->color)) {
        reassign(&lastColor, entry->color);
    }
    freeLogEntry(entry);
}

static LogEntry *LogEntryInit() {
    LogEntry *entry = (LogEntry *) malloc(sizeof(LogEntry));
    if(!entry) {
        debug("Could not allocate memory.\n");
        exit(-1);
    }
    entry->pid = NULL;
    entry->date = NULL;
    entry->type = NULL;
    entry->name = NULL;
    entry->library = NULL;
    entry->process = NULL;
    entry->color = NULL;
    entry->message = NULL;
    entry->line = NULL;
    entry->matched = false;
    entry->skipped = false;
    return entry;
}

static void freeLogEntry(LogEntry *entry) {
    maybeFree(entry->line, "entry->line");
    maybeFree(entry->date, "entry->date");
    maybeFree(entry->name, "entry->name");
    maybeFree(entry->library, "entry->library");
    maybeFree(entry->pid, "entry->pid");
    maybeFree(entry->process, "entry->process");
    maybeFree(entry->type, "entry->type");
    maybeFree(entry->message, "entry->message");
    maybeFree(entry->color, "entry->color");
    maybeFree(entry, "entry");
}

static void createLogMatcher(enum LOG_CHANNEL channel, enum MATCH_ACTION matchAction, const char *name, const char *search) {
    char *nsearch = strdup(search);
    if (matchers[matchAction][channel]) {
        char *osearch = strdup(matchers[matchAction][channel]->search);
        readOrAppendOpt(&nsearch, osearch);
        debug("Combined [%s]\n[%s]->\n[%s]\n", search, osearch, nsearch);
        freeLogEntryMatcher(matchers[matchAction][channel]);
        maybeFree(osearch, "osearch");
    }
    matchers[matchAction][channel] = LogEntryMatcherInit();
    LogEntryMatcher *matcher = matchers[matchAction][channel];

    reassign(&matcher->name, name);
    reassign(&matcher->search, nsearch);

    int ret = regcomp(&matcher->regex, nsearch, REG_EXTENDED | REG_ENHANCED | REG_NOSUB | REG_ICASE);
    if (ret != 0) {
        debug("Compilation failed for %s\n", nsearch);
        regfree(&matcher->regex);
        matcher->regexCompiled = false;
    } else {
        matcher->regexCompiled = true;
    }
    maybeFree(nsearch, "nsearch");
}

static LogEntryMatcher *LogEntryMatcherInit() {
    LogEntryMatcher *entry = (LogEntryMatcher *) malloc(sizeof(LogEntryMatcher));
    if(!entry) {
        debug("Could not allocate memory.\n");
        exit(-1);
    }
    entry->name = NULL;
    entry->search = NULL;
    return entry;
}

static void freeLogEntryMatcher(LogEntryMatcher *matcher) {
    maybeFree(matcher->name, "matcher->name");
    maybeFree(matcher->search, "matcher->search");
    if (matcher->regexCompiled)
        regfree(&matcher->regex);
    maybeFree(matcher, "matcher");
}

void readOrAppendOpt(char **dst, const char *optarg) {
    if (*dst != NULL) {
        char *hpn = malloc(sizeof(char)*strlen(optarg) + 1 + sizeof(char)*strlen(*dst) + 1);
        hpn[0] = '\0';
        strcpy(hpn, optarg);
        strcat(hpn, "|");
        strcat(hpn, *dst);
        reassign(dst, hpn);
        maybeFree(hpn, "hpn");
        debug("Combined flags: %s\n", *dst);
    } else {
        readOpt(dst, optarg);
    }
}

static void DeviceNotificationCallback(am_device_notification_callback_info *info, void *unknown) {
    struct am_device *device = info->dev;
    switch (info->msg) {
        case ADNCI_MSG_CONNECTED: {
            if (debug) {
                CFStringRef deviceId = AMDeviceCopyDeviceIdentifier(device);
                CFStringRef str = CFStringCreateWithFormat(kCFAllocatorDefault, NULL, CFSTR("deviceconsole connected: %@"), deviceId);
                CFRelease(deviceId);
                CFShow(str);
                CFRelease(str);
            }
            if (requiredDeviceId) {
                CFStringRef deviceId = AMDeviceCopyDeviceIdentifier(device);

                Boolean isRequiredDevice = CFEqual(deviceId, requiredDeviceId);
                CFRelease(deviceId);
                if (!isRequiredDevice)
                    break;
            }
            if (AMDeviceConnect(device) == MDERR_OK) {
                if (AMDeviceIsPaired(device) && (AMDeviceValidatePairing(device) == MDERR_OK)) {
                    if (AMDeviceStartSession(device) == MDERR_OK) {
                        service_conn_t connection;
                        if (AMDeviceStartService(device, AMSVC_SYSLOG_RELAY, &connection, NULL) == MDERR_OK) {
                            if (devicelen == 0) {
                                CFStringRef deviceName = AMDeviceCopyValue(device, 0, CFSTR("DeviceName"));
                                if (deviceName != NULL) {
                                    devicelen = (size_t) CFStringGetLength(deviceName);
                                    char buff[MAX_INPUT];
                                    CFStringGetCString(deviceName, buff, MAX_INPUT, kCFStringEncodingASCII);
                                    debug("Discovered device %s\n", buff);
                                    CFRelease(deviceName);
                                }
                            }
                            CFSocketRef socket = CFSocketCreateWithNative(kCFAllocatorDefault, connection, kCFSocketDataCallBack, SocketCallback, NULL);
                            if (socket) {
                                CFRunLoopSourceRef source = CFSocketCreateRunLoopSource(kCFAllocatorDefault, socket, 0);
                                if (source) {
                                    CFRunLoopAddSource(CFRunLoopGetMain(), source, kCFRunLoopCommonModes);
                                    AMDeviceRetain(device);
                                    DeviceConsoleConnection *data = malloc(sizeof *data);
                                    data->connection = connection;
                                    data->socket = socket;
                                    data->source = source;
                                    CFDictionarySetValue(liveConnections, device, data);
                                    CFRelease(source);
                                    return;
                                }
                            }
                        }
                        AMDeviceStopSession(device);
                    }
                }
            }
            AMDeviceDisconnect(device);
            break;
        }
        case ADNCI_MSG_DISCONNECTED: {
            if (debug) {
                CFStringRef deviceId = AMDeviceCopyDeviceIdentifier(device);
                CFStringRef str = CFStringCreateWithFormat(kCFAllocatorDefault, NULL, CFSTR("deviceconsole disconnected: %@"), deviceId);
                CFShow(str);
                CFRelease(str);
                CFRelease(deviceId);
            }
            DeviceConsoleConnection *data = (DeviceConsoleConnection *) CFDictionaryGetValue(liveConnections, device);
            if (data) {
                CFDictionaryRemoveValue(liveConnections, device);
                AMDeviceRelease(device);
                CFRunLoopRemoveSource(CFRunLoopGetMain(), data->source, kCFRunLoopCommonModes);
                CFRelease(data->source);
                CFRelease(data->socket);
                int i;
                for (i = 0; i < LOG_MESSAGE + 1; i++) {
                    if (matchers[HIDE][i])
                        freeLogEntryMatcher(matchers[HIDE][i]);
                    if (matchers[SHOW][i])
                        freeLogEntryMatcher(matchers[SHOW][i]);
                    if (matchers[HIGHLIGHT][i])
                        freeLogEntryMatcher(matchers[HIGHLIGHT][i]);
                }
                AMDeviceStopSession(device);
                AMDeviceDisconnect(device);
            }
            break;
        }
        default:
            break;
    }
}

void printUsage(char *const argv[]) {
    fprintf(stderr, "\nUsage: %s [options]\n"
                    "Options:\n NOTE: regex are all case insensitive\n"
                    " -d \t\t\t\tdebug = 1\n"
                    " -u <udid>\t\t\tShow only logs from a specific device\n"
                    " -m <arbitrary prefix|string|regex>\tHighlight these messages\n\t\t\t\tCan be prefix, exact-match string, or regex (ie: \"anything you can think of...\") NOTE: Wrap in quotes to protect spaces.\n"
                    " -p <processes to hide>\tHide processes from output \n\t\t\t\tCan be prefix, exact-match string, or regex (ie: \"apsd.*|nsurlsessiond.*|kernel.*\") NOTE: Wrap in quotes to protect spaces.\n"
                    " -P <processes to show>\tShow *only* these processes from output \n\t\t\t\tCan be prefix, exact-match string, or regex (ie: \"apsd.*|nsurlsessiond.*|kernel.*\") NOTE: Wrap in quotes to protect spaces.\n"
                    " -i <processes to highlight>\tHighlight these processes\n\t\t\t\tCan be prefix, exact-match string, or regex (ie: \"apsd.*|nsurlsessiond.*|kernel.*\") NOTE: Wrap in quotes to protect spaces.\n"
                    " -S \t\t\t\tHides common spammy processes from output (ie: \"kernel.*|apsd.*|nsurlsessiond.*|symptomsd.*|^SpringBoard.*|CommCenter.*|WirelessRadioManagerd.*\")\n"
                    " -T \t\t\t\tHides common spammy processes from output using local config file found at ~/.deviceconsole/spammyprocs.txt (created automatically if it does not exist).\n"
                    " -l <librar[y|ies] to hide>\tHide librar[y|ies] from output NOTE: these are the values found in parentheses following the process name) \n\t\t\t\tCan be prefix, exact-match string, or regex (ie: \"CFNetwork.*|libblah.*\") NOTE: Wrap in quotes to protect spaces.\n"
                    " -L <librar[y|ies] to show>\tShow *only* these librar[y|ies] from output NOTE: these are the values found in parentheses following the process name) \n\t\t\t\tCan be prefix, exact-match string, or regex (ie: \"CFNetwork.*|libblah.*\") NOTE: Wrap in quotes to protect spaces.\n"
                    " -h <librar[y|ies] to highlight>\tHighlight these librar[y|ies] from output NOTE: these are the values found in parentheses following the process name) \n\t\t\t\tCan be prefix, exact-match string, or regex (ie: \"CFNetwork.*|libblah.*\") NOTE: Wrap in quotes to protect spaces.\n",
            argv[0]);
}


int main(int argc, char *const argv[]) {
    if ((argc == 2) && (strcmp(argv[1], "--help") == 0)) {
        printUsage(argv);
        return 1;
    }
    checkConfig();
    int c;
    while ((c = getopt(argc, argv, "dh:i:l:L:m:NP:p:STu:x")) != -1) {
        switch (c) {
            case 'd':
                debug = 1;
                break;
            case 'i':
                createLogMatcher(LOG_PROCESS, HIGHLIGHT, "Highlight Process", optarg);
                break;
            case 'm':
                createLogMatcher(LOG_MESSAGE, HIGHLIGHT, "Highlight Message", optarg);
                break;
            case 'h':
                createLogMatcher(LOG_LIBRARY, HIGHLIGHT, "Highlight Library", optarg);
                break;
            case 'S':
                createLogMatcher(LOG_PROCESS, HIDE, "Hide Process", spammyProcs);
                break;
            case 'T':
                createLogMatcher(LOG_PROCESS, HIDE, "Hide Process", spammyProcs);
                break;
            case 'p':
                createLogMatcher(LOG_PROCESS, HIDE, "Hide Process", optarg);
                break;
            case 'P':
                createLogMatcher(LOG_PROCESS, SHOW, "Required Process", optarg);
                break;
            case 'l':
                createLogMatcher(LOG_LIBRARY, HIDE, "Hide Libraries", optarg);
                break;
            case 'L':
                createLogMatcher(LOG_LIBRARY, SHOW, "Required Libraries", optarg);
                break;
            case 'N':
                debug("Showing log messages matched by hide/show flag(s).\n");
                showMatches = true;
                break;
            case 'u':
                if (requiredDeviceId)
                    CFRelease(requiredDeviceId);
                requiredDeviceId = CFStringCreateWithCString(kCFAllocatorDefault, optarg, kCFStringEncodingASCII);
                break;
            case '?':
                printUsage(argv);
                return 1;
            default:
                abort();
        }
    }
    char err_buf[BUFSIZ];
    int reti = regcomp(&logEntryRegex, reg, REG_ENHANCED | REG_EXTENDED | REG_ICASE);
    if (reti) {
        regerror(reti, &logEntryRegex, err_buf, BUFSIZ);
        debug("regcomp: %s\n", err_buf);
        exit(1);
    }
    liveConnections = CFDictionaryCreateMutable(kCFAllocatorDefault, 0, NULL, NULL);
    am_device_notification *notification;
    AMDeviceNotificationSubscribe(DeviceNotificationCallback, 0, 0, NULL, &notification);
    CFRunLoopRun();
    return 0;
}

void checkConfig() {
    struct passwd *pw = getpwuid(getuid());
    const char *homedir = pw->pw_dir;

    char *filepath = malloc(strlen(homedir) + strlen("/.deviceconsole") + strlen("/spammyprocs.txt"));
    filepath[0] = '\0';
    strcpy(filepath, homedir);
    strcat(filepath, "/.deviceconsole");
    errno = 0;
    if (mkdir(filepath, 0755) && errno != EEXIST) {
        bool exists = access(filepath, F_OK) == 0;
        if(!exists) {
            debug("Could not create config directory: %s %d\n", filepath, errno);
            maybeFree(filepath, "filepath");
            return;
        }
    }
    strcat(filepath, "/spammyprocs.txt");
    bool exists = access(filepath, F_OK) == 0;

    FILE *fd = fopen(filepath, exists ? "r+" : "w+");
    if (fd == NULL) {
        debug("Could not read config file: %s %d\n", filepath, errno);
        maybeFree(filepath, "filepath");
        return;
    }
    fseek(fd, 0L, SEEK_END);
    long flen = ftell(fd);
    size_t textsize = (size_t) (flen == -1 ? 0 : flen);
    fseek(fd, 0L, SEEK_SET);
    if (textsize == 0) {
        char *towrite = malloc(strlen("spammyprocs=") + strlen(DEFAULT_SPAMMY));
        towrite[0] = '\0';
        strcpy(towrite, "spammyprocs=");
        strcat(towrite, DEFAULT_SPAMMY);
        if (fputs(towrite, fd))
            fwrite("\n", sizeof(char), 1, fd);
        fclose(fd);
        maybeFree(towrite, "towrite");
        spammyProcs = strdup(DEFAULT_SPAMMY);
        debug("Wrote config for spammy procs %s (feel free to modify it).\n", filepath);
    } else if (exists && textsize > 0) {
        spammyProcs = malloc(textsize);
        fscanf(fd, "spammyprocs=%s", spammyProcs);
        fclose(fd);
        debug("Read config for spammy procs %s\n\tspammyProcs = \"%s\"\n", filepath, spammyProcs);
    } else {
        spammyProcs = strdup(DEFAULT_SPAMMY);
    }
    maybeFree(filepath, "filepath");
}

void readOpt(char **dst, const char *optarg) {
    *dst = malloc(strlen(optarg) + 1);
    strncpy(*dst, optarg, strnlen(optarg, BUFSIZ));
}

// You must free the result if result is non-NULL.
char *strrep(char *orig, const char *rep, const char *with) {
    char *result; // the return string
    char *ins;    // the next insert point
    char *tmp;    // varies
    size_t len_rep;  // length of rep (the string to remove)
    size_t len_with; // length of with (the string to replace rep with)
    size_t len_front; // distance between rep and end of last rep
    int count;    // number of replacements

    // sanity checks and initialization
    if (!orig || !rep)
        return NULL;
    len_rep = strlen(rep);
    if (len_rep == 0)
        return NULL; // empty rep causes infinite loop during count
    if (!with)
        with = "";
    len_with = strlen(with);

    // count the number of replacements needed
    ins = orig;
    for (count = 0; (tmp = strstr(ins, rep)); ++count) {
        ins = tmp + len_rep;
    }
    tmp = result = malloc(strlen(orig) + (len_with - len_rep) * count + 1);
    if (!result)
        return NULL;

    // first time through the loop, all the variable are set correctly
    // from here on,
    //    tmp points to the end of the result string
    //    ins points to the next occurrence of rep in orig
    //    orig points to the remainder of orig after "end of rep"
    while (count--) {
        ins = strstr(orig, rep);
        len_front = ins - orig;
        tmp = strncpy(tmp, orig, len_front) + len_front;
        tmp = strcpy(tmp, with) + len_with;
        orig += len_front + len_rep; // move to next "end of rep"
    }
    strcpy(tmp, orig);
    return result;
}

/*
 // Mask for the UTF-8 digit range.
 const int kNum = 0x30;

 // Converts a three-digit ASCII (UTF-8) representation of an octal number `xyz` to an integer.
 int decodeOctal(int x, int y, int z) {
    return (x & 0x3) << 6 | (y & 0x7) << 3 | (z & 0x7);
 }

 // Returns true when `byte` is within the UTF-8 7-bit digit range (0x30 to 0x39).
 bool isDigit(int byte) {
    return (byte & 0xf0) == kNum;
 }


char *decodeSyslog(char *line) {
    // UTF-8 values for \, M, -, ^.
    const int kBackslash = 0x5c;
    const int kM = 0x4d;
    const int kDash = 0x2d;
    const int kCaret = 0x5e;

    unsigned byte
    a = 1;
    final
    List<int> bytes = utf8_encode(line);
    final
    List<int>
    out = <int>[];
    for (int i = 0; i < bytes.length;) {
        if (bytes[i] != kBackslash || i > bytes.length - 4) {
            // Unmapped byte: copy as-is.
            out.add(bytes[i++]);
        } else {
            // Mapped byte: decode next 4 bytes.
            if (bytes[i + 1] == kM && bytes[i + 2] == kCaret) {
                // \M^x form: bytes in range 0x80 to 0x9f.
                out.add((bytes[i + 3] & 0x7f) + 0x40);
            } else if (bytes[i + 1] == kM && bytes[i + 2] == kDash) {
                // \M-x form: bytes in range 0xa0 to 0xf7.
                out.add(bytes[i + 3] | 0x80);
            } else if (bytes.getRange(i + 1, i + 3).every(isDigit)) {
                // \ddd form: octal representation (only used for \134 and \240).
                out.add(decodeOctal(bytes[i + 1], bytes[i + 2], bytes[i + 3]));
            } else {
                // Unknown form: copy as-is.
                out.addAll(bytes.getRange(0, 4));
            }
            i += 4;
        }
    }
    return UTF8.decode(out);
}*/
