cc -c init/init.S -o init/init.o
cc -o init/init init/init.o -nostdlib -Wl,--build-id=none -Wl,-Tinit/stage1.lds -no-pie
objdump -d init/init
(cd ../packit; cargo run --features cli -- pack --input ../svsm/init --output ../svsm/fs.file)
