#!/bin/bash

echo "=========== MSTRS -> TRS translation ==========="
# Iterate over all files ending with ".mstrs" in the current directory
for file in *.mstrs; do
    # Check if the file exists
    if [ -e "$file" ]; then
        # Extract the file name (without extension) and create the target file name
        filename="${file%.*}"
        target_file="${filename}.trs"

        # Copy the file with information output
        echo "Translate $file to $target_file..."

        sml @SMLload=mstrs_checker_v0.03/mstrsck.amd64-darwin "$file" -tt > "$target_file"

        echo "Translate complete."
    else
        echo "File $file does not exist."
    fi
done
