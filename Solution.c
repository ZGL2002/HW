#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define EPS 1e-9
#define INF 1e100
#define PI 3.14159265358979323846

typedef struct {
    double x;
    double y;
} Point;

typedef struct {
    Point *p;
    int n;
} Polygon;

typedef struct {
    double x;
    double y;
} Vec;

static Polygon A = {0}, B = {0};
static Vec *base_dirs = NULL;
static int base_dir_count = 0;
static int base_dir_cap = 0;
static double search_limit = 0.0;

static double sqr(double x) { return x * x; }

static double cross(Point a, Point b, Point c) {
    return (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x);
}

static int point_on_segment(Point a, Point b, Point p) {
    if (fabs(cross(a, b, p)) > EPS) return 0;
    double minx = a.x < b.x ? a.x : b.x;
    double maxx = a.x > b.x ? a.x : b.x;
    double miny = a.y < b.y ? a.y : b.y;
    double maxy = a.y > b.y ? a.y : b.y;
    return p.x >= minx - EPS && p.x <= maxx + EPS && p.y >= miny - EPS && p.y <= maxy + EPS;
}

static int proper_segment_intersect(Point a, Point b, Point c, Point d) {
    double c1 = cross(a, b, c);
    double c2 = cross(a, b, d);
    double c3 = cross(c, d, a);
    double c4 = cross(c, d, b);
    return ((c1 > EPS && c2 < -EPS) || (c1 < -EPS && c2 > EPS)) &&
           ((c3 > EPS && c4 < -EPS) || (c3 < -EPS && c4 > EPS));
}

static int point_in_polygon_strict(const Polygon *poly, Point q, double dx, double dy) {
    int wn = 0;
    for (int i = 0; i < poly->n; ++i) {
        Point p1 = poly->p[i];
        Point p2 = poly->p[(i + 1) % poly->n];
        p1.x += dx; p1.y += dy;
        p2.x += dx; p2.y += dy;

        if (point_on_segment(p1, p2, q)) {
            return 0;
        }

        int up = (p1.y <= q.y + EPS);
        int up2 = (p2.y > q.y + EPS);
        int down = (p1.y > q.y + EPS);
        int down2 = (p2.y <= q.y + EPS);
        double cr = cross(p1, p2, q);

        if (up && up2 && cr > EPS) ++wn;
        if (down && down2 && cr < -EPS) --wn;
    }
    return wn != 0;
}

static int polygons_overlap_strict(double dx, double dy) {
    for (int i = 0; i < A.n; ++i) {
        Point a1 = A.p[i];
        Point a2 = A.p[(i + 1) % A.n];
        for (int j = 0; j < B.n; ++j) {
            Point b1 = B.p[j];
            Point b2 = B.p[(j + 1) % B.n];
            b1.x += dx; b1.y += dy;
            b2.x += dx; b2.y += dy;
            if (proper_segment_intersect(a1, a2, b1, b2)) {
                return 1;
            }
        }
    }

    for (int i = 0; i < A.n; ++i) {
        if (point_in_polygon_strict(&B, A.p[i], dx, dy)) {
            return 1;
        }
    }
    for (int i = 0; i < B.n; ++i) {
        Point q = B.p[i];
        q.x += dx;
        q.y += dy;
        if (point_in_polygon_strict(&A, q, 0.0, 0.0)) {
            return 1;
        }
    }

    for (int i = 0; i < A.n; ++i) {
        Point p1 = A.p[i];
        Point p2 = A.p[(i + 1) % A.n];
        Point mid = {(p1.x + p2.x) * 0.5, (p1.y + p2.y) * 0.5};
        if (point_in_polygon_strict(&B, mid, dx, dy)) {
            return 1;
        }
    }

    for (int i = 0; i < B.n; ++i) {
        Point p1 = B.p[i];
        Point p2 = B.p[(i + 1) % B.n];
        Point mid = {(p1.x + p2.x) * 0.5 + dx, (p1.y + p2.y) * 0.5 + dy};
        if (point_in_polygon_strict(&A, mid, 0.0, 0.0)) {
            return 1;
        }
    }

    return 0;
}

static void add_dir(double x, double y) {
    double len = sqrt(x * x + y * y);
    if (len < 1e-12) return;
    x /= len;
    y /= len;

    for (int i = 0; i < base_dir_count; ++i) {
        if (fabs(base_dirs[i].x - x) < 1e-10 && fabs(base_dirs[i].y - y) < 1e-10) return;
    }

    if (base_dir_count == base_dir_cap) {
        int new_cap = base_dir_cap == 0 ? 64 : base_dir_cap * 2;
        Vec *new_buf = (Vec *)realloc(base_dirs, (size_t)new_cap * sizeof(Vec));
        if (!new_buf) exit(1);
        base_dirs = new_buf;
        base_dir_cap = new_cap;
    }
    base_dirs[base_dir_count].x = x;
    base_dirs[base_dir_count].y = y;
    ++base_dir_count;
}

static void build_base_dirs(void) {
    base_dir_count = 0;

    for (int i = 0; i < A.n; ++i) {
        Point p1 = A.p[i], p2 = A.p[(i + 1) % A.n];
        double ex = p2.x - p1.x;
        double ey = p2.y - p1.y;
        add_dir(-ey, ex);
        add_dir(ey, -ex);
    }
    for (int i = 0; i < B.n; ++i) {
        Point p1 = B.p[i], p2 = B.p[(i + 1) % B.n];
        double ex = p2.x - p1.x;
        double ey = p2.y - p1.y;
        add_dir(-ey, ex);
        add_dir(ey, -ex);
    }

    for (int i = 0; i < 16; ++i) {
        double ang = 2.0 * PI * (double)i / 16.0;
        add_dir(cos(ang), sin(ang));
    }

    add_dir(1.0, 0.0);
    add_dir(0.0, 1.0);
    add_dir(-1.0, 0.0);
    add_dir(0.0, -1.0);
}

static double find_exit_along_dir(double ux, double uy, double dx, double dy) {
    if (!polygons_overlap_strict(dx, dy)) return 0.0;

    double hi = 1e-6;
    while (hi < search_limit && polygons_overlap_strict(dx + ux * hi, dy + uy * hi)) {
        hi *= 2.0;
    }
    if (hi >= search_limit && polygons_overlap_strict(dx + ux * hi, dy + uy * hi)) {
        return INF;
    }

    double lo = 0.0;
    double prev = 0.0;
    int found = 0;
    for (int s = 1; s <= 24; ++s) {
        double t = hi * (double)s / 24.0;
        if (!polygons_overlap_strict(dx + ux * t, dy + uy * t)) {
            lo = prev;
            hi = t;
            found = 1;
            break;
        }
        prev = t;
    }
    if (!found) {
        lo = prev;
    }

    for (int it = 0; it < 45; ++it) {
        double mid = 0.5 * (lo + hi);
        if (polygons_overlap_strict(dx + ux * mid, dy + uy * mid)) {
            lo = mid;
        } else {
            hi = mid;
        }
    }

    return hi;
}

static Vec solve_one(double dx, double dy) {
    Vec ans = {0.0, 0.0};
    if (!polygons_overlap_strict(dx, dy)) {
        return ans;
    }

    double best_len = INF;
    double best_ang = 0.0;

    for (int i = 0; i < base_dir_count; ++i) {
        double ux = base_dirs[i].x;
        double uy = base_dirs[i].y;
        double step = find_exit_along_dir(ux, uy, dx, dy);
        if (step >= INF / 2) continue;
        if (step < best_len) {
            best_len = step;
            ans.x = ux * step;
            ans.y = uy * step;
            best_ang = atan2(uy, ux);
        }
    }

    if (best_len >= INF / 2) {
        return ans;
    }

    double delta = PI / 6.0;
    for (int round = 0; round < 8; ++round) {
        int improved = 0;
        for (int k = -2; k <= 2; ++k) {
            double ang = best_ang + delta * (double)k;
            double ux = cos(ang), uy = sin(ang);
            double step = find_exit_along_dir(ux, uy, dx, dy);
            if (step < best_len) {
                best_len = step;
                ans.x = ux * step;
                ans.y = uy * step;
                best_ang = ang;
                improved = 1;
            }
        }
        delta *= 0.5;
        if (!improved && delta < 1e-4) break;
    }

    return ans;
}

int main(void) {
    int na = 0, nb = 0;
    if (scanf("%d %d", &na, &nb) != 2) {
        return 0;
    }

    if (na < 3 || nb < 3) {
        return 0;
    }

    A.n = na;
    B.n = nb;
    A.p = (Point *)malloc((size_t)na * sizeof(Point));
    B.p = (Point *)malloc((size_t)nb * sizeof(Point));
    if (!A.p || !B.p) {
        free(A.p);
        free(B.p);
        return 0;
    }

    double minx = INF, miny = INF, maxx = -INF, maxy = -INF;

    for (int i = 0; i < na; ++i) {
        if (scanf("%lf %lf", &A.p[i].x, &A.p[i].y) != 2) return 0;
        if (A.p[i].x < minx) minx = A.p[i].x;
        if (A.p[i].x > maxx) maxx = A.p[i].x;
        if (A.p[i].y < miny) miny = A.p[i].y;
        if (A.p[i].y > maxy) maxy = A.p[i].y;
    }
    for (int i = 0; i < nb; ++i) {
        if (scanf("%lf %lf", &B.p[i].x, &B.p[i].y) != 2) return 0;
        if (B.p[i].x < minx) minx = B.p[i].x;
        if (B.p[i].x > maxx) maxx = B.p[i].x;
        if (B.p[i].y < miny) miny = B.p[i].y;
        if (B.p[i].y > maxy) maxy = B.p[i].y;
    }

    double diag = sqrt(sqr(maxx - minx) + sqr(maxy - miny));
    search_limit = diag * 8.0 + 10.0;
    if (search_limit < 10.0) search_limit = 10.0;

    build_base_dirs();

    char token[64];
    int K = 0;

    if (scanf("%63s", token) != 1) {
        free(A.p);
        free(B.p);
        free(base_dirs);
        return 0;
    }

    if (strcmp(token, "OK") == 0) {
        printf("OK\n");
        fflush(stdout);
        if (scanf("%d", &K) != 1) {
            free(A.p);
            free(B.p);
            free(base_dirs);
            return 0;
        }
    } else {
        K = atoi(token);
    }

    if (K < 0) K = 0;

    printf("%d\n", K);
    fflush(stdout);

    for (int i = 0; i < K; ++i) {
        double dx = 0.0, dy = 0.0;
        if (scanf("%lf %lf", &dx, &dy) != 2) {
            dx = 0.0;
            dy = 0.0;
        }

        Vec v = solve_one(dx, dy);
        if (fabs(v.x) < 5e-7) v.x = 0.0;
        if (fabs(v.y) < 5e-7) v.y = 0.0;
        printf("%.5f %.5f\n", v.x, v.y);
        fflush(stdout);
    }

    printf("OK\n");
    fflush(stdout);

    free(A.p);
    free(B.p);
    free(base_dirs);
    return 0;
}
