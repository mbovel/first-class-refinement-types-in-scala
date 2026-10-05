# Included by nginx-proxy in the server block for icvm0175.epfl.ch.
include /etc/nginx/vhost.d/default;

# Reject HTTP debug methods at the proxy (Nessus plugin 11213).
if ($request_method ~* ^(TRACE|TRACK)$) {
    return 405;
}

# Snippets are small; the nginx-proxy default is 4096M.
client_max_body_size 64k;

# A compilation can take seconds, and the backend gives up on its own after 30.
proxy_read_timeout 60s;
