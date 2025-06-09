#!/bin/bash

# 设置颜色输出
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

# 获取Chrome完整版本号（如：135.0.7049.96）
get_chrome_version() {
    /Applications/Google\ Chrome.app/Contents/MacOS/Google\ Chrome --version | awk '{print $3}'
}

# 检查已安装的 chromedriver 是否匹配当前 Chrome
check_driver() {
    CHROME_VERSION=$(get_chrome_version)
    CHROME_MAJOR_MINOR=$(echo "$CHROME_VERSION" | cut -d'.' -f1-2)

    # 检查并创建必要的目录
    if [ ! -d "/usr/local/bin" ]; then
        echo "目录 /usr/local/bin 不存在，正在创建..."
        sudo mkdir -p /usr/local/bin
        sudo chown $(whoami):admin /usr/local/bin
        sudo chmod 755 /usr/local/bin
    else
        echo "目录 /usr/local/bin 已存在，跳过创建步骤"
        # 如果你仍然希望确保权限正确，可以取消下面两行的注释
        # sudo chown $(whoami):admin /usr/local/bin
        # sudo chmod 755 /usr/local/bin
    fi

    # 查找 chromedriver 路径
    DRIVER_PATH=""
    for path in "/usr/local/bin/chromedriver" "/opt/homebrew/bin/chromedriver"; do
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

# 自动安装兼容的 chromedriver（尝试最多 3个 patch 子版本）
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
        DRIVER_URL="https://storage.googleapis.com/chrome-for-testing-public/${TRY_VERSION}/mac-arm64/chromedriver-mac-arm64.zip"

        echo -e "${YELLOW}尝试版本: $TRY_VERSION${NC}"

        curl -sfLo chromedriver.zip "$DRIVER_URL"
        if [ $? -eq 0 ]; then
            echo -e "${GREEN}成功下载 chromedriver ${TRY_VERSION}${NC}"
            rm -rf chromedriver-mac-arm64*
            unzip -qo chromedriver.zip
            sudo mv chromedriver-mac-arm64/chromedriver /usr/local/bin/chromedriver
            sudo chmod +x /usr/local/bin/chromedriver
            echo -e "${GREEN}安装成功: $(/usr/local/bin/chromedriver --version)${NC}"
            return 0
        fi
    done

    echo -e "${RED}未能下载兼容 chromedriver(尝试了 3 个 patch 版本）${NC}"
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

# 更新PATH环境变量
export PATH="/usr/local/bin:$PATH"

# 启动 Chrome（调试端口）
echo -e "${GREEN}启动 Chrome 中...${NC}"
"/Applications/Google Chrome.app/Contents/MacOS/Google Chrome" \
    --remote-debugging-port=9222 \
    --disable-translate \
    --no-first-run \
    --disable-extensions \
    --user-data-dir="$HOME/ChromeDebug" \
    https://polymarket.com/markets/crypto

echo -e "${GREEN}Chrome 已成功启动${NC}"