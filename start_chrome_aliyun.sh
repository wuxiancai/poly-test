#!/bin/bash

# Ubuntu Chrome启动脚本
# 设置颜色输出
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# 获取Chrome完整版本号（只查找项目根目录）
get_chrome_version() {
    if [ -x "$SCRIPT_DIR/google-chrome" ]; then
        "$SCRIPT_DIR/google-chrome" --version | awk '{print $3}'
    elif [ -x "$SCRIPT_DIR/chrome" ]; then
        "$SCRIPT_DIR/chrome" --version | awk '{print $3}'
    else
        echo "Chrome not found"
        return 1
    fi
}

# 检查已安装的 chromedriver 是否匹配当前 Chrome
check_driver() {
    CHROME_VERSION=$(get_chrome_version)
    if [ "$CHROME_VERSION" = "Chrome not found" ]; then
        echo -e "${RED}Chrome 未安装${NC}"
        return 1
    fi
    
    CHROME_MAJOR_MINOR=$(echo "$CHROME_VERSION" | cut -d'.' -f1-2)

    # 只查找项目根目录下的 chromedriver
    DRIVER_PATH=""
    for path in "$SCRIPT_DIR/chromedriver"; do
        if [ -x "$path" ]; then
            DRIVER_PATH="$path"
            break
        fi
    done

    if [ -z "$DRIVER_PATH" ]; then
        echo -e "${RED}chromedriver 未安装${NC}"
        return 1
    fi


    DRIVER_VERSION=$("$DRIVER_PATH" --version | awk '{print $2}')
    DRIVER_MAJOR_MINOR=$(echo "$DRIVER_VERSION" | cut -d'.' -f1-2)

    echo -e "${YELLOW}Chrome 版本: $CHROME_VERSION${NC}"
    echo -e "${YELLOW}chromedriver 版本: $DRIVER_VERSION${NC}"

    if [ "$CHROME_VERSION" != "$DRIVER_VERSION" ]; then
        echo -e "${RED}版本不匹配，需更新驱动${NC}"
        return 1
    fi

    echo -e "${GREEN}版本匹配，驱动正常${NC}"
    return 0
}

# 自动安装兼容的 chromedriver（Ubuntu版本）
install_driver() {
    echo -e "${YELLOW}尝试下载安装兼容的 chromedriver...${NC}"
    CHROME_VERSION=$(get_chrome_version)
    BASE_VERSION=$(echo "$CHROME_VERSION" | cut -d'.' -f1-3)
    PATCH_VERSION=$(echo "$CHROME_VERSION" | cut -d'.' -f4)

    TMP_DIR="/tmp/chromedriver_update"
    mkdir -p "$TMP_DIR"
    cd "$TMP_DIR" || return 1
    
    for ((i=0; i<3; i++)); do
        TRY_PATCH=$((PATCH_VERSION - i))
        TRY_VERSION="${BASE_VERSION}.${TRY_PATCH}"
        DRIVER_URL="https://storage.googleapis.com/chrome-for-testing-public/${TRY_VERSION}/linux64/chromedriver-linux64.zip"

        echo -e "${YELLOW}尝试版本: $TRY_VERSION${NC}"

        curl -sfLo chromedriver.zip "$DRIVER_URL"
        if [ $? -eq 0 ]; then
            echo -e "${GREEN}成功下载 chromedriver ${TRY_VERSION}${NC}"
            rm -rf chromedriver-linux64*
            unzip -qo chromedriver.zip
            mv chromedriver-linux64/chromedriver "$HOME/chromedriver"
            chmod +x "$HOME/chromedriver"
            echo -e "${GREEN}安装成功: $("$HOME/chromedriver" --version)${NC}"
            cd "$HOME"
            return 0
        fi
    done

    echo -e "${RED}未能下载兼容 chromedriver（尝试了 3 个 patch 版本）${NC}"
    return 1
}

# 主流程
echo -e "${YELLOW}开始执行浏览器启动流程...${NC}"

if ! check_driver; then
    echo -e "${YELLOW}驱动不兼容，尝试修复...${NC}"
    if install_driver; then
        check_driver || {
            echo -e "${RED}驱动更新后仍然不兼容${NC}"
            exit 1
        }
    else
        echo -e "${RED}驱动更新失败${NC}"
        exit 1
    fi
fi

export DISPLAY=:1

# 设置X11授权
if [ -f "$HOME/.Xauthority" ]; then
    export XAUTHORITY="$HOME/.Xauthority"
else
    # 尝试生成授权文件
    touch "$HOME/.Xauthority"
    export XAUTHORITY="$HOME/.Xauthority"
fi

echo -e "${YELLOW}使用 DISPLAY=1"
echo -e "${YELLOW}使用 XAUTHORITY=$XAUTHORITY${NC}"

# 启动 Chrome（调试端口）- 只用项目根目录下的 chrome
echo -e "${GREEN}启动 Chrome 中...${NC}"
if [ -x "$SCRIPT_DIR/google-chrome" ]; then
    "$SCRIPT_DIR/google-chrome" \
        --remote-debugging-port=9222 \
        --no-sandbox \
        --disable-gpu \
        --disable-software-rasterizer \
        --disable-dev-shm-usage \
        --disable-background-networking \
        --disable-default-apps \
        --disable-extensions \
        --disable-sync \
        --metrics-recording-only \
        --no-first-run \
        --disable-translate \
        --disable-background-timer-throttling \
        --disable-backgrounding-occluded-windows \
        --disable-renderer-backgrounding \
        --disable-features=TranslateUI,BlinkGenPropertyTrees,SitePerProcess,IsolateOrigins \
        --noerrdialogs \
        --user-data-dir="$HOME/ChromeDebug" \
        about:blank
else
    echo -e "${RED}Chrome 未找到${NC}"
    exit 1
fi
