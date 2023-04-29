void reach_error() {}

int main()
{
	int *i, *p, *q, **r, **s, **t;
	p = &i;
	r = &p;
	s = &q;
	*s = p;
	s = *r;
	t = r;
}