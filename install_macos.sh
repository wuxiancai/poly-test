#!/bin/bash

# 设置颜色输出
RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m'

echo "=== macOS 自动化安装脚本 ==="

# 检查系统和芯片类型
if [[ "$(uname)" != "Darwin" ]]; then
    echo "${RED}错误: 此脚本只能在 macOS 系统上运行${NC}"
    exit 1
fi

CHIP_TYPE=$(uname -m)
echo "检测到芯片类型: $CHIP_TYPE"

if [[ "$CHIP_TYPE" == "arm64" ]]; then
    BREW_PREFIX="/opt/homebrew"
else
    BREW_PREFIX="/usr/local"
fi

# 自动确认所有提示

export HOMEBREW_NO_AUTO_UPDATE=1
export NONINTERACTIVE=1
export CI=1
# 在 HOSTS 文件中添加 github.com 和 raw.githubusercontent.com 的记录
#echo "185.199.108.153 raw.githubusercontent.com" | sudo tee -a /etc/hosts
#echo "185.199.109.153 raw.githubusercontent.com" | sudo tee -a /etc/hosts
#echo "185.199.110.153 raw.githubusercontent.com" | sudo tee -a /etc/hosts
#echo "185.199.111.153 raw.githubusercontent.com" | sudo tee -a /etc/hosts

# 检查并安装 Homebrew (自动模式)
if ! command -v brew &> /dev/null; then
    echo "正在安装 Homebrew..."
    NONINTERACTIVE=1 /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
    
    if [[ "$CHIP_TYPE" == "arm64" ]]; then
        echo 'eval "$(/opt/homebrew/bin/brew shellenv)"' >> ~/.zshrc
        eval "$(/opt/homebrew/bin/brew shellenv)"
    fi
fi

# 更新 Homebrew
brew update

# 安装 Python 3.9 (自动模式)
echo "安装 Python 3.9..."
brew install python@3.9 --force
brew link --force --overwrite python@3.9
echo "安装 python-tk@3.9 (自动模式)"
brew install python-tk@3.9 --force
brew install wget

# 创建虚拟环境
echo "创建虚拟环境..."
python3.9 -m venv venv --clear
source venv/bin/activate

# 升级 pip3
echo "升级 pip3..."
python3.9 -m pip install --upgrade pip

# 安装依赖 (使用 pip3)
echo "安装依赖..."
pip3 install --no-cache-dir selenium
pip3 install --no-cache-dir pyautogui
pip3 install --no-cache-dir screeninfo
pip3 install --no-cache-dir requests
# pip3 install --no-cache-dir pytesseract
# pip3 install --no-cache-dir opencv-python-headless  # 安装headless版本，通常更稳定



# 配置 Python 环境变量 (避免重复添加)
echo "配置环境变量..."
if ! grep -q "# Python 配置" ~/.zshrc; then
    echo '# Python 配置' >> ~/.zshrc
    echo "export PATH=\"${BREW_PREFIX}/opt/python@3.9/bin:\$PATH\"" >> ~/.zshrc
    echo 'export TK_SILENCE_DEPRECATION=1' >> ~/.zshrc
fi

# 检查并安装 Chrome 和 ChromeDriver
echo "检查 Chrome 和 ChromeDriver..."

# 检查 Chrome 是否已安装
if [ -d "/Applications/Google Chrome.app" ]; then
    echo "${GREEN}Chrome 已安装${NC}"
    CHROME_INSTALLED=true
else
    echo "Chrome 未安装"
    CHROME_INSTALLED=false
fi

# 检查 ChromeDriver 是否已安装
if command -v chromedriver &> /dev/null; then
    echo "${GREEN}ChromeDriver 已安装${NC}"
    CHROMEDRIVER_INSTALLED=true
else
    echo "ChromeDriver 未安装"
    CHROMEDRIVER_INSTALLED=false
fi

# 根据检查结果进行安装
if [ "$CHROME_INSTALLED" = false ]; then
    echo "安装 Chrome..."
    brew install --cask google-chrome --force
fi

if [ "$CHROMEDRIVER_INSTALLED" = false ]; then
    echo "安装 ChromeDriver..."
    brew install chromedriver --force
fi

chmod +x start_chrome.sh
# 创建自动启动脚本

cat > run_trader.sh << 'EOL'
#! /bin/bash

# 打印接收到的参数，用于调试
echo "run_trader.sh received args: $@"

# 激活虚拟环境
source venv/bin/activate

# 运行交易程序
exec python3 -u crypto_trader.py "$@"
EOL

chmod +x run_trader.sh


# 验证安装
echo "=== 验证安装 ==="
echo "Python 路径: $(which python3)"
echo "Python 版本: $(python3 --version)"
echo "Pip 版本: $(pip3 --version)"
echo "已安装的包:"
pip3 list

echo "${GREEN}安装完成！${NC}"
echo "使用说明:"
echo "1. 直接运行 ./run_trader.sh 即可启动程序"
echo "2. 程序会自动启动 Chrome 并运行交易脚本"
echo "3. 所有配置已自动完成，无需手动操作"

# 自动清理安装缓存
brew cleanup -s
pip3 cache purge

# 添加安装检查
echo "\n${GREEN}===== 安装检查 =====${NC}"
echo "检查关键组件是否正确安装..."

# 初始化错误计数和错误列表
ERROR_COUNT=0
ERROR_LIST=""

# 检查 Homebrew
if ! command -v brew &> /dev/null; then
    ERROR_COUNT=$((ERROR_COUNT+1))
    ERROR_LIST="${ERROR_LIST}\n${RED}[未安装] Homebrew${NC} - 请运行: /bin/bash -c \"\$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)\""
fi

# 检查 Python 3.9
if ! command -v python3.9 &> /dev/null; then
    ERROR_COUNT=$((ERROR_COUNT+1))
    ERROR_LIST="${ERROR_LIST}\n${RED}[未安装] Python 3.9${NC} - 请运行: brew install python@3.9 --force && brew link --force --overwrite python@3.9"
fi

# 检查 pip3
if ! command -v pip3 &> /dev/null; then
    ERROR_COUNT=$((ERROR_COUNT+1))
    ERROR_LIST="${ERROR_LIST}\n${RED}[未安装] pip3${NC} - 请运行: python3.9 -m pip install --upgrade pip"
fi

# 检查 Chrome
if [ ! -d "/Applications/Google Chrome.app" ]; then
    ERROR_COUNT=$((ERROR_COUNT+1))
    ERROR_LIST="${ERROR_LIST}\n${RED}[未安装] Google Chrome${NC} - 请运行: brew install --cask google-chrome --force"
fi

# 检查 ChromeDriver
if ! command -v chromedriver &> /dev/null; then
    ERROR_COUNT=$((ERROR_COUNT+1))
    ERROR_LIST="${ERROR_LIST}\n${RED}[未安装] ChromeDriver${NC} - 请运行: brew install chromedriver --force"
fi

# 检查 python-tk@3.9
if ! brew list python-tk@3.9 &> /dev/null; then
    ERROR_COUNT=$((ERROR_COUNT+1))
    ERROR_LIST="${ERROR_LIST}\n${RED}[未安装] python-tk@3.9${NC} - 请运行: brew install python-tk@3.9 --force"
fi

# 检查关键Python包
PACKAGES=("selenium" "pyautogui" "screeninfo" "requests")
for pkg in "${PACKAGES[@]}"; do
    if ! pip3 list | grep -i "$pkg" &> /dev/null; then
        ERROR_COUNT=$((ERROR_COUNT+1))
        ERROR_LIST="${ERROR_LIST}\n${RED}[未安装] Python包: $pkg${NC} - 请运行: pip3 install --no-cache-dir $pkg"
    fi
done

# 检查虚拟环境
if [ ! -d "venv" ]; then
    ERROR_COUNT=$((ERROR_COUNT+1))
    ERROR_LIST="${ERROR_LIST}\n${RED}[未创建] Python虚拟环境${NC} - 请运行: python3.9 -m venv venv --clear"
fi

# 检查环境变量配置
if ! grep -q "# Python 配置" ~/.zshrc; then
    ERROR_COUNT=$((ERROR_COUNT+1))
    ERROR_LIST="${ERROR_LIST}\n${RED}[未配置] Python环境变量${NC} - 请检查 ~/.zshrc 文件中的 Python 配置"
fi

# 检查启动脚本权限
if [ ! -x "run_trader.sh" ]; then
    ERROR_COUNT=$((ERROR_COUNT+1))
    ERROR_LIST="${ERROR_LIST}\n${RED}[未设置] run_trader.sh 执行权限${NC} - 请运行: chmod +x run_trader.sh"
fi

# 输出检查结果
if [ $ERROR_COUNT -eq 0 ]; then
    echo "${GREEN}所有组件已成功安装!${NC}"
else
    echo "${RED}检测到 $ERROR_COUNT 个安装问题:${NC}"
    echo -e "$ERROR_LIST"
    echo "\n您可以单独安装上述未成功安装的组件,无需重新运行整个脚本。"
fi
