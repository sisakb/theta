int main()
{
	int x, y, *p, **r, *q, **s;
	p = &x;
	r = &p;
	q = &y;
	s = &q;
	r = s;
}
