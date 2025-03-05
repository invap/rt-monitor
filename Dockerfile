FROM ubuntu:24.10

RUN apt update && apt install -y \
python3 \
pipx \
build-essential \
gdb \
lldb \
python-is-python3 \
curl \
git 

RUN pipx install poetry 

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y

ENV PATH="$PATH:~/.local/bin"

WORKDIR /home/workspace
