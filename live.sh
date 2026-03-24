#!/bin/sh

trap 'echo "\nStopping watchers..."; kill $TECTONIC_PID $BS_PID; exit' INT TERM EXIT

echo "Starting Tectonic watcher..."
tectonic -X watch &
TECTONIC_PID=$!

echo "Starting Browser-Sync..."
npx browser-sync start --server --files "**/*.pdf" --reload-delay 500 --no-ui &
BS_PID=$!

wait
