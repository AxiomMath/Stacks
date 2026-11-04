module

public import StacksFrontier.AlgebraicGeometry.Descent.ZariskiModuleChartComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A glueing datum of sheaves of modules from isomorphisms over the pairwise overlaps

`Stacks.SheafOfModules.ModulesGlueData` — the shape in which Stacks 00AM is consumed in
algebraic geometry — asks for its transitions as `𝒪_S(V)`-linear *equivalences of the modules of
sections* over every open `V` of the base contained in the images of two charts, together with
their compatibility with restriction and the cocycle condition. A construction, by contrast,
produces its transitions as **isomorphisms of sheaves of modules** over the overlap of two
charts. This file converts the second into the first.

The translation itself is `AlgebraicGeometry.localAppEquiv`: an isomorphism of the restrictions
to an open `W` of `S` of two sheaves of `𝒪_S`-modules induces, over every open `V ≤ W`, a linear
equivalence of the modules of sections. Taking `W` to be the overlap of the images of the `i`-th
and `j`-th charts and the two modules to be the pushforwards of the chart modules — whose
sections over `V` *are* `Stacks.SheafOfModules.openSections` — gives the transition, and
`AlgebraicGeometry.localAppFun_naturality` gives its compatibility with restriction. So only the
cocycle condition remains to be supplied, and it is asked for in the one place it cannot be
derived.

## Comparison with what was already available

`AlgebraicGeometry.modulesGlueDataOfDescentData` builds a glueing datum too, but out of a
*descent datum* for the pullback pseudofunctor, which carries a transition for every object
mapping to two members of the covering. The input here is strictly smaller: one isomorphism per
*pair* of charts, over the overlap of their images. The charts are also arbitrary open immersions
rather than the inclusions of open subschemes of `S`.

## Main definitions

* `Stacks.SheafOfModules.pushforwardChart`: the `i`-th chart module, pushed forward to the base.
* `Stacks.SheafOfModules.chartOverlap`: the overlap of the images of two charts.
* `Stacks.SheafOfModules.ModulesGlueData.ofOverlapIso`: **the glueing datum of a family of
  sheaves of modules on the charts together with isomorphisms of their pushforwards over the
  pairwise overlaps satisfying the cocycle condition on sections.** Its glued module is
  `Stacks.SheafOfModules.ModulesGlueData.glued`, with the comparison isomorphisms
  `Stacks.SheafOfModules.ModulesGlueData.chartIso`, and it is quasi-coherent as soon as the
  charts are, by `Stacks.SheafOfModules.ModulesGlueData.isQuasicoherent_glued`.
* `Stacks.SheafOfModules.restrictPushforwardIso`: **the restriction along `a ≫ f` of the
  pushforward along `f` of a sheaf of modules is its restriction along `a`** — the isomorphism
  that produces the input above out of a comparison of the chart modules themselves, given on a
  scheme mapping into both charts.

## Main results

* `Stacks.SheafOfModules.ModulesGlueData.ofOverlapIso_trans`: the transition of the datum is the
  sections map of the given isomorphism, so the cocycle hypothesis is stated in the same
  vocabulary in which it is discharged.
* `Stacks.SheafOfModules.ModulesGlueData.ofOverlapIso_cocycle_of_id`: the cocycle hypothesis is
  satisfiable — the identities of the restrictions of a single sheaf of modules satisfy it — so
  the statement is not vacuous.

## Implementation notes

The three opens `chartOverlap f i j`, `chartOverlap f j k` and `chartOverlap f i k` over which
the three isomorphisms of a cocycle triangle live are different, and the three sections maps are
therefore taken at three different ambient opens. That is harmless because
`AlgebraicGeometry.localApp` records the ambient open in the type of its argument and the bound
`V ≤ W` as a separate hypothesis: an open `V` inside all three chart images is inside all three
overlaps, and the three sections maps are maps of the same two modules of sections over `V`.

No transport along an equality of opens appears anywhere, which is what makes this cheap; the
image-presentation form `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp`, which takes
`f ''ᵁ W = V` as an argument, would need one.

## No tag is claimed

Stacks 00AM is carried by `Stacks.SheafOfModules.ModulesGlueData.glued` and
`Stacks.SheafOfModules.ModulesGlueData.chartIso` already; this file only changes the shape in
which the datum is presented.

## References

* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Tag 01NV](https://stacks.math.columbia.edu/tag/01NV)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

variable {S : Scheme.{u}} {ι : Type u} {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ S)
  [∀ i, IsOpenImmersion (f i)]

/-- The overlap of the images of the `i`-th and the `j`-th chart, as an open of the base. This is
the open over which the comparison of the two charts is given. -/
abbrev chartOverlap (i j : ι) : S.Opens := (f i).opensRange ⊓ (f j).opensRange

variable (mod : ∀ i, (Y i).Modules)

/-- The `i`-th chart module, pushed forward to the base. Its sections over an open `V` of the
base are `Stacks.SheafOfModules.openSections (f i) (mod i) V`, the sections of the chart module
over the preimage of `V`. -/
abbrev pushforwardChart (i : ι) : S.Modules := (Scheme.Modules.pushforward (f i)).obj (mod i)

namespace ModulesGlueData

/-- **A glueing datum of sheaves of modules from isomorphisms over the pairwise overlaps.** The
charts carry the modules `mod i`, and the comparison of the `i`-th with the `j`-th is given as an
isomorphism of their pushforwards restricted to the overlap of the two chart images; the cocycle
condition is asked for on sections, over the opens contained in three chart images.

The transition over an open `V` of the base contained in two chart images is the sections map of
the given isomorphism, `AlgebraicGeometry.localAppEquiv`, and its compatibility with restriction
is the naturality of that sections map, so neither has to be supplied. -/
def ofOverlapIso
    (e : ∀ i j : ι, Scheme.Modules.restrict (pushforwardChart f mod i) (chartOverlap f i j).ι ≅
      Scheme.Modules.restrict (pushforwardChart f mod j) (chartOverlap f i j).ι)
    (he : ∀ (i j k : ι) (V : S.Opens) (hi : V ≤ (f i).opensRange)
      (hj : V ≤ (f j).opensRange) (hk : V ≤ (f k).opensRange)
      (s : ToType (openSections (f i) (mod i) V)),
        localAppFun (e j k).hom V (le_inf hj hk)
            (localAppFun (e i j).hom V (le_inf hi hj) s) =
          localAppFun (e i k).hom V (le_inf hi hk) s) :
    ModulesGlueData S f where
  mod := mod
  trans := fun i j {V} hi hj => localAppEquiv (e i j) V (le_inf hi hj)
  trans_map := fun i j {_V _W} hi hj hWV s =>
    (localAppFun_naturality (e i j).hom (le_inf hi hj)
      (le_inf (hWV.trans hi) (hWV.trans hj)) (homOfLE hWV) s).symm
  trans_trans := fun i j k {V} hi hj hk s => he i j k V hi hj hk s

/-- The transition of `Stacks.SheafOfModules.ModulesGlueData.ofOverlapIso` is the sections map of
the given isomorphism. -/
@[simp] theorem ofOverlapIso_trans
    (e : ∀ i j : ι, Scheme.Modules.restrict (pushforwardChart f mod i) (chartOverlap f i j).ι ≅
      Scheme.Modules.restrict (pushforwardChart f mod j) (chartOverlap f i j).ι)
    (he : ∀ (i j k : ι) (V : S.Opens) (hi : V ≤ (f i).opensRange)
      (hj : V ≤ (f j).opensRange) (hk : V ≤ (f k).opensRange)
      (s : ToType (openSections (f i) (mod i) V)),
        localAppFun (e j k).hom V (le_inf hj hk)
            (localAppFun (e i j).hom V (le_inf hi hj) s) =
          localAppFun (e i k).hom V (le_inf hi hk) s)
    (i j : ι) {V : S.Opens} (hi : V ≤ (f i).opensRange) (hj : V ≤ (f j).opensRange)
    (s : ToType (openSections (f i) (mod i) V)) :
    (ofOverlapIso f mod e he).trans i j hi hj s =
      localAppFun (e i j).hom V (le_inf hi hj) s := rfl

/-- The charts of `Stacks.SheafOfModules.ModulesGlueData.ofOverlapIso` are the given modules. -/
@[simp] theorem ofOverlapIso_mod
    (e : ∀ i j : ι, Scheme.Modules.restrict (pushforwardChart f mod i) (chartOverlap f i j).ι ≅
      Scheme.Modules.restrict (pushforwardChart f mod j) (chartOverlap f i j).ι)
    (he : ∀ (i j k : ι) (V : S.Opens) (hi : V ≤ (f i).opensRange)
      (hj : V ≤ (f j).opensRange) (hk : V ≤ (f k).opensRange)
      (s : ToType (openSections (f i) (mod i) V)),
        localAppFun (e j k).hom V (le_inf hj hk)
            (localAppFun (e i j).hom V (le_inf hi hj) s) =
          localAppFun (e i k).hom V (le_inf hi hk) s) :
    (ofOverlapIso f mod e he).mod = mod := rfl

/-- **The cocycle hypothesis of `Stacks.SheafOfModules.ModulesGlueData.ofOverlapIso` is
satisfiable**, so the construction is not vacuous: for one sheaf of modules `M` on the base, the
sections maps of the identity of its restrictions to the overlaps compose as the hypothesis asks.

Only the unit law of the sections map, `AlgebraicGeometry.localAppFun_id`, is used. -/
theorem ofOverlapIso_cocycle_of_id (M : S.Modules) (i j k : ι) (V : S.Opens)
    (hi : V ≤ (f i).opensRange) (hj : V ≤ (f j).opensRange) (hk : V ≤ (f k).opensRange)
    (s : ToType (M.val.obj (op V))) :
    localAppFun (𝟙 (Scheme.Modules.restrict M (chartOverlap f j k).ι)) V (le_inf hj hk)
        (localAppFun (𝟙 (Scheme.Modules.restrict M (chartOverlap f i j).ι)) V
          (le_inf hi hj) s) =
      localAppFun (𝟙 (Scheme.Modules.restrict M (chartOverlap f i k).ι)) V (le_inf hi hk) s :=
  (localAppFun_id M V (le_inf hj hk) _).trans
    ((localAppFun_id M V (le_inf hi hj) s).trans
      (localAppFun_id M V (le_inf hi hk) s).symm)

end ModulesGlueData

/-! ### The input side: a pushforward restricted to an open of the base -/

/-- **The restriction of a pushforward along a factoring morphism.** Let `f : Y ⟶ S` be an open
immersion and let `a : Z ⟶ Y` be an open immersion with `a ≫ f = c`. Then the restriction along
`c` of the pushforward along `f` of a sheaf of modules `N` on `Y` is the restriction of `N`
along `a`.

This is the input side of `Stacks.SheafOfModules.ModulesGlueData.ofOverlapIso`. A construction
produces its comparison of two charts as an isomorphism of the restrictions of the *chart*
modules to a scheme mapping into both charts — the two modules live on different schemes, so
there is no other place to compare them — whereas the glueing datum reads its transitions on the
pushforwards to the base. Taking `c` to be the inclusion of the overlap of the two chart images
and `a`, respectively, the two liftings of that inclusion through the charts, this isomorphism
converts the one into the other.

It is `AlgebraicGeometry.openChartIso` written with `AlgebraicGeometry.Scheme.Modules.restrict`
in place of the inverse image of the pullback pseudofunctor; restriction along an open immersion
is *not* the inverse image but only isomorphic to it
(`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`), so the two statements are
different and this one needs no pseudofunctor vocabulary. -/
@[sga "4 IV 14.3" "Open component of Φ∘j_*"]
def restrictPushforwardIso {S Y Z : Scheme.{u}} (f : Y ⟶ S) [IsOpenImmersion f] (a : Z ⟶ Y)
    [IsOpenImmersion a] {c : Z ⟶ S} [IsOpenImmersion c] (h : a ≫ f = c) (N : Y.Modules) :
    Scheme.Modules.restrict ((Scheme.Modules.pushforward f).obj N) c ≅
      Scheme.Modules.restrict N a :=
  ((Scheme.Modules.restrictFunctorCongr h).app _).symm ≪≫
    (Scheme.Modules.restrictFunctorComp a f).app _ ≪≫
      (Scheme.Modules.restrictFunctor a).mapIso
        ((Scheme.Modules.restrictFunctorAdjCounitIso f).app N)

end Stacks.SheafOfModules

end
