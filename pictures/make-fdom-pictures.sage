#Code to make the png images of fundamental domains. Modified based on David Lowry-Duda's LMFDB code.
gp.read("fdom.gp")
from sage.misc.decorators import options, rename_keyword
from sage.plot.hyperbolic_polygon import HyperbolicPolygon
from sage.libs.pari.convert_sage import gen_to_sage

#To encode the png file as a string.
def encode_mcurve_plot(P, transparent=True):
    from io import BytesIO as IO
    from matplotlib.backends.backend_agg import FigureCanvasAgg
    from base64 import b64encode
    from urllib.parse import quote

    virtual_file = IO()
    fig = P.matplotlib(axes_pad=None)
    ax = fig.axes[0]
    ax.set_xlim(xmin=-1, xmax=1)
    ax.set_ylim(ymin=-1, ymax=1)
    fig.set_canvas(FigureCanvasAgg(fig))
    fig.set_size_inches(2.5, 2.5) # images are 200 x 200 on the website
    fig.savefig(virtual_file, format='png', bbox_inches='tight', transparent=transparent, dpi=120)
    virtual_file.seek(0)
    buf = virtual_file.getbuffer()
    return "data:image/png;base64," + quote(b64encode(buf))

#To make a hyperbolic polygon given the vertices.
@rename_keyword(color='rgbcolor')
@options(alpha=1, fill=True, thickness=0, rgbcolor="blue", zorder=2, linestyle='solid')
def my_hyperbolic_polygon(pts, model="PD", resolution=200, circlecolor='black', add_circle=False, **options):
    r"""
    Return a hyperbolic polygon in the hyperbolic plane with vertices ``pts``.

    This is on the poincare disk, but doesn't add random black circles
    repeatedly like the default version.

    INPUT:

    - ``pts`` -- a list or tuple of complex numbers

    OPTIONS:

    - ``alpha`` -- default: 1

    - ``fill`` -- default: ``False``

    - ``thickness`` -- default: 1

    - ``rgbcolor`` -- default: ``'blue'``

    - ``linestyle`` -- (default: ``'solid'``) the style of the line, which is
      one of ``'dashed'``, ``'dotted'``, ``'solid'``, ``'dashdot'``, or
      ``'--'``, ``':'``, ``'-'``, ``'-.'``, respectively
    """
    if not model == "PD":
        raise ValueError("Only the disk model is supported")
    from sage.plot.all import Graphics
    g = Graphics()
    g._set_extra_kwds(g._extract_kwds_for_show(options))

    g.add_primitive(HyperbolicPolygon(pts, model, options))
    g.set_aspect_ratio(1)
    if add_circle:
        g = g + circle((0, 0), 1, rgbcolor=circlecolor)
    return g

#Make the level 1 pictures for all D in Dlist
def make_pictures_level1(Dlist):
    for D in Dlist:
        gp.setrand(1)
        A = gp.alginit_Qdisc(D)
        gp.setrand(1)
        X = gp.afuchinit(A);
        verts = gen_to_sage(pari(gp.afuchvertices(X, 1)));
        g = my_hyperbolic_polygon(verts, add_circle = True);
        pngstr = encode_mcurve_plot(g, remove_axes = True, figsize = [4, 4])
        fil = open(f"../data/fdompictures/{D}_1.fdom", "w")
        fil.write(f"{pngstr}")


def possible_D(Dmin, Dmax):
    L = [];
    for D in range(Dmin, Dmax + 1):
        if len(factor(D)) % 2 == 0 and is_squarefree(D):
            L.append(D)
    return L

