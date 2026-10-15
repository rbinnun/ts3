package main

import (
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"strings"
)

func main() {
	if len(os.Args) != 2 {
		fmt.Fprintln(os.Stderr, "usage: go run every_file.go universe_folder")
		os.Exit(64)
	}
	root := os.Args[1]
	problem := filepath.WalkDir(root, func(path string, entry fs.DirEntry, problem error) error {
		if problem != nil {
			return problem
		}
		if path != root && strings.HasPrefix(entry.Name(), ".") {
			if entry.IsDir() {
				return filepath.SkipDir
			}
			return nil
		}
		if entry.IsDir() {
			return nil
		}
		relative, problem := filepath.Rel(root, path)
		if problem != nil {
			return problem
		}
		fmt.Printf("universe_file(%q).\n", filepath.ToSlash(relative))
		return nil
	})
	if problem != nil {
		fmt.Fprintln(os.Stderr, problem)
		os.Exit(1)
	}
}
