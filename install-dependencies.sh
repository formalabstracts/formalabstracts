#!/bin/bash
set -xev
if [[ ! -d /lean ]]; then
    mkdir /lean
    chown travis /lean
    su -c "./download-lean.sh" -m travis
fi
