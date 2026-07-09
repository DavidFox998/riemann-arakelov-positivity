#!/bin/bash
if [ -f /usr/local/lib/workshop-devguard.sh ]; then
    source /usr/local/lib/workshop-devguard.sh
    devguard_acquire "${APP_PORT:-3001}"
fi
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")"
lake exe cache get
lake build
