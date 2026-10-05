#!/usr/bin/env bash
# Deploy the playground backend to icvm0175. Run from the EPFL network or VPN (port 22 on
# the VM is not reachable from outside).
#
# The image is built on the VM: it matches that host's architecture and nothing large has
# to cross the network. The previous stack lives on in /root/demo, stopped, as a rollback
# target: `ssh root@icvm0175.epfl.ch 'cd demo && docker compose up -d'`.
set -euo pipefail
cd "$(dirname "$0")"

H=root@icvm0175.epfl.ch
REMOTE=/root/playground
OLD=/root/demo

# certs, acme and the generated conf.d live only on the VM. Create them if missing and
# seed them from the old stack, so Let's Encrypt is never asked to reissue.
ssh "$H" "mkdir -p $REMOTE/server $REMOTE/deploy/proxy/vhost.d
for d in certs acme conf.d stream.d dhparam; do
    mkdir -p $REMOTE/deploy/proxy/\$d
    if [ -d $OLD/proxy/\$d ]; then cp -an $OLD/proxy/\$d/. $REMOTE/deploy/proxy/\$d/ 2>/dev/null || true; fi
done"

# No -o/-g: the local uid means nothing on the VM. No --delete under proxy/ either, or we
# would remove the runtime directories above out from under the proxy's bind mounts.
rsync -rlptz ./docker-compose.yml "$H:$REMOTE/deploy/"
rsync -rlptz ./proxy/vhost.d/ "$H:$REMOTE/deploy/proxy/vhost.d/"
rsync -rlptz --delete \
    --exclude target --exclude project/target --exclude .bsp --exclude .metals \
    ../server/ "$H:$REMOTE/server/"

# Build before stopping anything, so a build failure costs no downtime.
ssh "$H" "cd $REMOTE/deploy && docker compose build playground"

# Both stacks bind :80 and :443, so the old one has to go down first.
ssh "$H" "cd $OLD && docker compose down --remove-orphans"
# --force-recreate: a changed vhost.d file does not change any container's config, so
# without it compose would leave a stale proxy running.
ssh "$H" "cd $REMOTE/deploy && docker compose up -d --force-recreate && sleep 15 && docker compose ps"
ssh "$H" "docker exec refinement-types-letsproxy-1 nginx -t"

echo
echo "=== verification from this machine ==="
u=https://icvm0175.epfl.ch
for probe in "GET / 200" "GET /PSEMHUB/hub 404" "GET /bandwidth/index.cgi?x=1 404"; do
    set -- $probe
    printf "%-6s %-28s -> %s (expect %s)\n" "$1" "$2" \
        "$(curl -sS -m 20 -o /dev/null -w '%{http_code}' -X "$1" "$u$2" || echo FAILED)" "$3"
done
for m in TRACK TRACE; do
    printf "%-6s %-28s -> %s (expect 405)\n" "$m" "/" \
        "$(curl -sS -m 20 -o /dev/null -w '%{http_code}' -X "$m" "$u/" || echo FAILED)"
done

echo
echo "=== a snippet that must compile (empty output = success) ==="
curl -sS -m 60 -X POST --data-binary @- "$u/" <<'SNIPPET'
def max(x: Int, y: Int): { v: Int with v >= x && v >= y } =
  if (x > y) x else y
SNIPPET

echo
echo "=== a snippet that must fail ==="
curl -sS -m 60 -X POST --data-binary @- "$u/" <<'SNIPPET'
def max(x: Int, y: Int): { v: Int with v >= x && v >= y } =
  if (x > y) y else x
SNIPPET

echo
echo "Then check for stray listeners on the VM (Nessus saw 2000/tcp and 5060/tcp):"
echo "  ssh $H ss -tlnp"
