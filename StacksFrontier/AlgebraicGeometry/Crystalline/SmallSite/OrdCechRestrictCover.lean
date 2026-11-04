module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CechComparison
public import StacksFrontier.CategoryTheory.Sites.CechComplexAlternatingComparison
import StacksCore.Tactic.StacksAttribute

/-!
# The alternating Čech complex of a restriction cover of an object of `Cris(X/S)`

`StacksFrontier/CategoryTheory/Sites/CechComplexAlternatingHomotopy.lean` lifts
[Stacks, Tag 01FM] off the opens of a topological space: for a family `U : ι → C` of objects of
a category with finite products, each of them subterminal, the inclusion of the alternating Čech
cochain complex into the full one is a homotopy equivalence, and the *ordered* Čech complex —
the one a consumer of [Stacks, Tag 07MN] indexes by, its terms being products over the strictly
increasing tuples — therefore has the cohomology of the full one in every degree.  This file
instantiates that theory at the covering families of the small crystalline site, and composes
it with `cechComplexRestrictIso` so that the complex it computes the cohomology of is the Čech
complex of the covering family *as a family in the site*.

## The choice of ambient category

The covering families of `Cris(X/S)` are the families of restrictions `A|_{V_i} ⟶ A` attached to
a family `V : ι → T.Opens` of opens of the ambient scheme of `A`
(`Crystalline.GlobalCrystallineSituation.restrictCoverage`), so they are families of objects of
the slice `Over A`, and `Over A` does *not* have finite products: what this site supplies is the
products of the restrictions alone, `hasProduct_overMk_restrictOpenHom`.

The ambient category is therefore taken to be the opens of the ambient scheme, `T.Opens`, and
the coefficient presheaf to be `(restrictOpenFunctor A).op ⋙ F`.  Nothing is assumed in doing
so and no instance is postulated on `Over A`:

* `T.Opens` is a complete lattice, hence has all finite products
  (`CategoryTheory.Limits.CompleteLattice.hasFiniteLimits_of_semilatticeInf_orderTop`), and the
  product of a tuple is its infimum, `...CechComplex.inter_eq_iInf`;
* `T.Opens` is thin, so the hypothesis `hU` of the lifted theory is free,
  `isSubterminal_ambientOpen`.  On the slice it is not free, and there it is
  `isSubterminal_overMk_restrictOpenHom`;
* the two readings agree degree by degree: the object `inter V t` of the lifted theory is, after
  restriction, the iterated fibre product `A|_{V_{t_0}} ×_A ⋯ ×_A A|_{V_{t_p}}` of the covering
  family, which is `restrictOpenPiFan_pt` together with
  `isLimit_restrictOpenPiFan`.  Globally this is `cechComplexRestrictIso`, and
  `restrictCechComplexIso` below is the composite: the Čech complex of the lifted theory *is*
  the Čech complex of the covering family of the site.

## Main results

* `isSubterminal_ambientOpen` — every open of the ambient scheme is subterminal, which
  discharges the one hypothesis of the lifted theory.
* `restrictOpenPiFan_pt` and `restrictOpenPresheaf_obj_inter` — the degreewise matching: the
  `inter` of the lifted theory is the iterated fibre product of the restriction cover, and the
  coefficient group in degree `p` at the tuple `t` is `F(A|_{V_{t_0} ∩ ⋯ ∩ V_{t_p}})`.
* `restrictCechComplex`, `restrictCechComplexAlt`, `restrictCechComplexOrd` and
  `restrictCechAltInclusion` — the full, alternating and ordered Čech cochain complexes of the
  restriction cover, and the canonical inclusion of the second into the first.
* `restrictCechAltInclusionHomotopyEquiv` and
  `restrictCechAltInclusion_homotopyEquivalence` — **[Stacks, Tag 01FM] for a restriction cover
  of an object of `Cris(X/S)`.**
* `restrictCechComplexIso` — the full Čech complex of the lifted theory is the Čech complex of
  the restriction cover read as a covering family of the site,
  `Stacks.CechSite.cechComplex` of `restrictOpenHypercover`.
* `restrictOrdCechHomotopyEquiv`, `restrictOrdCechHomologyIso` and
  `restrictOrdCechCohomologyIso` — **the ordered Čech complex of a restriction cover is
  homotopy equivalent to the full Čech complex of the cover, and its cohomology is in every
  degree the Čech cohomology of that covering family of `Cris(X/S)`.**

## What this does not do

`restrictOrdCechCohomologyIso` lands the step of [Stacks, Tag 07MN] left as "insert future
reference here" only as far as *Čech* cohomology of the covering family.  Nothing here carries
the tag `07MN`, and three things of the remark are untouched.  [Stacks, Tag 03F7] carries Čech
cohomology of a covering family to the cohomology of the *covered object*, whereas `Cris(X/S)`
has no terminal object and the `RΓ(Cris(X/S), -)` of the remark is the global
`...SmallSite.cohomologyFunctor`.  The ordered Čech complex here is built from the sections of
`F` over the restrictions, whereas the bottom row of the remark's double complex is
`...SmallSite.ordCechModule`, built from the `...SmallSite.CechSystem.tupleSections`, which are
limits over the level filtration of a Čech system; **those two complexes are identified** in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/OrdCechSystemIdentification.lean`, by
constructing the Čech system of the cover and `...SmallSite.restrictOrdCechComplexIso`.  And of
the remark's other inputs, [Stacks, Tag 07JH] and [Stacks, Tag 07LG] are proved elsewhere, as
`...SmallSite.crystalPairFunctor_isEquivalence` and
`...SmallSite.crystalPairDeRhamComplex_computesCohomology`.
A note here used to count [Stacks, Tag 07LM] with them; that is no longer the state of the
library — its vanishing clause is `...SmallSite.vanishing07LM` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Vanishing07LMProof.lean`, proved for every
sheaf of `𝒪_{X/S}`-modules satisfying conditions (1) and (2) of [Stacks, Tag 07JN].  What the
remark takes from the tag is the agreement of `RΓ` of `F` and of `F ⊗ Ω^*_{X/S}`, and that is
still unavailable at a general crystal: the complex `F ⊗ Ω^*_{X/S}` is constructed only at
`F = 𝒪_{X/S}`.

## References

* [Stacks Project, Tag 01FK](https://stacks.math.columbia.edu/tag/01FK)
* [Stacks Project, Tag 01FM](https://stacks.math.columbia.edu/tag/01FM)
* [Stacks Project, Tag 03F7](https://stacks.math.columbia.edu/tag/03F7)
* [Stacks Project, Tag 07MN](https://stacks.math.columbia.edu/tag/07MN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped AlgebraicGeometry
open Stacks.CategoryTheory.CechComplex

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening

variable {S : GlobalCrystallineSituation.{u}} (A : CrystallineThickening S)

/-! ### The hypothesis of the lifted theory, on the opens of the ambient scheme -/

/-- **Every open of the ambient scheme of an object of `Cris(X/S)` is a subterminal object of
the category of opens.**  This is the hypothesis `hU` of the lifted alternating Čech theory, at
the ambient category used here, and it holds of every object: the category of opens of a space
is thin, two parallel morphisms of it being two proofs of one inequality.

On the slice `Over A` the same hypothesis is not free — a covering morphism there has to be a
monomorphism — and it is `isSubterminal_overMk_restrictOpenHom`. -/
theorem isSubterminal_ambientOpen (W : A.obj.thickening.target.scheme.Opens) :
    IsSubterminal W :=
  fun _ _ _ => Subsingleton.elim _ _

/-! ### The degreewise matching with the covering family in the slice -/

section Matching

variable {ι : Type w} (V : ι → A.obj.thickening.target.scheme.Opens)

/-- **The `inter` of the lifted Čech theory is the iterated fibre product of the restriction
cover.**  The degree-`p` term of the Čech complex of a covering family of a site is built from
the sections over the `(p+1)`-fold fibre products `A|_{V_{t_0}} ×_A ⋯ ×_A A|_{V_{t_p}}`; this
says that the vertex of the fan which `isLimit_restrictOpenPiFan` proves to be such a product is
the restriction of `A` to `inter V t`, on the nose.

This is the matching the ambient category asked for: the lifted theory is read at `T.Opens`,
where the finite products exist, and its intersections are carried to the fibre products of the
slice by `restrictOpenOverFunctor`. -/
theorem restrictOpenPiFan_pt {m : ℕ} (t : Fin m → ι) :
    (restrictOpenPiFan A V t).pt = Over.mk (A.restrictOpenHom (inter V t)) :=
  rfl

/-- **The coefficient group of the Čech complex of the restriction cover, at a tuple `t`, is the
group of sections of `F` over the restriction of `A` to the intersection of the members of the
tuple.**  The product of opens occurring in `inter` is their infimum. -/
theorem restrictOpenPresheaf_obj_inter
    (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{w'}) {m : ℕ} (t : Fin m → ι) :
    ((restrictOpenFunctor A).op ⋙ F).obj (op (inter V t)) =
      F.obj (op (A.restrictOpen (⨅ a, V (t a)))) := by
  rw [inter_eq_iInf]
  rfl

end Matching

/-! ### The complexes of the restriction cover -/

section Complexes

variable {ι : Type w} [LinearOrder ι] (V : ι → A.obj.thickening.target.scheme.Opens)
  (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{max w w'})

/-- **The full Čech cochain complex of a restriction cover of an object of `Cris(X/S)`**: in
degree `p` the product, over all `(p+1)`-tuples `t` of indices, of the sections of `F` over
`A|_{V_{t_0} ∩ ⋯ ∩ V_{t_p}}`, with the alternating sum of the restrictions as differential. -/
def restrictCechComplex : CochainComplex AddCommGrpCat.{max w w'} ℕ :=
  Alternating.cechCochainComplex ((restrictOpenFunctor A).op ⋙ F) V

/-- **The alternating Čech cochain complex of a restriction cover of an object of
`Cris(X/S)`**: the subcomplex of `restrictCechComplex` of the cochains that are alternating in
the tuple.  That the alternating cochains are a subcomplex is [Stacks, Tag 01FK], and it needs
the members of the family to be subterminal, which here is `isSubterminal_ambientOpen`. -/
def restrictCechComplexAlt : CochainComplex AddCommGrpCat.{max w w'} ℕ :=
  Alternating.cechCochainComplexAlt ((restrictOpenFunctor A).op ⋙ F) V
    fun i => isSubterminal_ambientOpen A (V i)

/-- **The ordered Čech cochain complex of a restriction cover of an object of `Cris(X/S)`**: in
degree `p` the product over the strictly increasing tuples only.  This is the shape the double
complex of [Stacks, Tag 07MN] has its bottom row in, its terms being indexed by
`...SmallSite.OrdCechTuple`, which is the `...CechComplex.Alternating.OrdTuple` of the lifted
theory. -/
def restrictCechComplexOrd : CochainComplex AddCommGrpCat.{max w w'} ℕ :=
  Alternating.cechCochainComplexOrd ((restrictOpenFunctor A).op ⋙ F) V

/-- The canonical inclusion of the alternating Čech complex of a restriction cover into the full
one. -/
def restrictCechAltInclusion : restrictCechComplexAlt A V F ⟶ restrictCechComplex A V F :=
  Alternating.cechAltInclusion ((restrictOpenFunctor A).op ⋙ F) V
    fun i => isSubterminal_ambientOpen A (V i)

omit [LinearOrder ι] in
/-- The degree-`p` term of the full Čech complex of a restriction cover. -/
@[simp]
theorem restrictCechComplex_X (p : ℕ) :
    (restrictCechComplex A V F).X p =
      AddCommGrpCat.of (Alternating.CechCochain ((restrictOpenFunctor A).op ⋙ F) V p) :=
  Alternating.cechCochainComplex_X _ _ p

/-- The degree-`p` term of the ordered Čech complex of a restriction cover. -/
@[simp]
theorem restrictCechComplexOrd_X (p : ℕ) :
    (restrictCechComplexOrd A V F).X p =
      AddCommGrpCat.of (Alternating.CechCochainOrd ((restrictOpenFunctor A).op ⋙ F) V p) :=
  Alternating.cechCochainComplexOrd_X _ _ p

/-! ### [Stacks, Tag 01FM] for a restriction cover -/

/-- **[Stacks, Tag 01FM] for a restriction cover of an object of `Cris(X/S)`.**  The canonical
inclusion of the alternating Čech cochain complex of the cover into the full Čech cochain
complex is a homotopy equivalence; signed sorting is a homotopy inverse.

The family of opens is arbitrary: it need not cover the ambient scheme, exactly as at the space
level.  The hypothesis of the lifted theory is discharged by `isSubterminal_ambientOpen` and
nothing is assumed here. -/
@[stacks 01FM "for a restriction cover of an object of the small crystalline site"]
def restrictCechAltInclusionHomotopyEquiv :
    HomotopyEquiv (restrictCechComplexAlt A V F) (restrictCechComplex A V F) :=
  Alternating.cechAltInclusionHomotopyEquiv ((restrictOpenFunctor A).op ⋙ F) V
    fun i => isSubterminal_ambientOpen A (V i)

/-- **[Stacks, Tag 01FM] for a restriction cover of an object of `Cris(X/S)`**, in the
`homotopyEquivalences` morphism-property spelling. -/
@[stacks 01FM "a restriction cover's alternating inclusion lies in homotopyEquivalences"]
theorem restrictCechAltInclusion_homotopyEquivalence :
    (HomologicalComplex.homotopyEquivalences AddCommGrpCat.{max w w'} (ComplexShape.up ℕ))
      (restrictCechAltInclusion A V F) :=
  Alternating.cechAltInclusion_homotopyEquivalence _ _ _

/-! ### The ordered complex, which is what [Stacks, Tag 07MN] indexes by -/

/-- **The ordered Čech complex of a restriction cover is homotopy equivalent to the full Čech
complex of that cover.**  The isomorphism of complexes of [Stacks, Tag 01FK] (2) composed with
the homotopy equivalence of [Stacks, Tag 01FM]. -/
def restrictOrdCechHomotopyEquiv :
    HomotopyEquiv (restrictCechComplexOrd A V F) (restrictCechComplex A V F) :=
  Alternating.cechOrdHomotopyEquiv ((restrictOpenFunctor A).op ⋙ F) V
    fun i => isSubterminal_ambientOpen A (V i)

/-- **The ordered Čech complex of a restriction cover of an object of `Cris(X/S)` has the
cohomology of the full Čech complex of that cover, in every degree.** -/
def restrictOrdCechHomologyIso (j : ℕ) :
    (restrictCechComplexOrd A V F).homology j ≅ (restrictCechComplex A V F).homology j :=
  Alternating.cechCochainComplexOrdHomologyIso ((restrictOpenFunctor A).op ⋙ F) V
    (fun i => isSubterminal_ambientOpen A (V i)) j

/-! ### The identification with the Čech complex of the covering family of the site -/

/-- **The full Čech complex of the lifted theory is the Čech complex of the restriction cover
read as a covering family of `Cris(X/S)`.**  `...CechComplex.Alternating.cechCochainComplexIso`
identifies the explicitly assembled complex of cochain groups with
`CategoryTheory.cechComplexFunctor`, and `cechComplexRestrictIso` identifies that with
`Stacks.CechSite.cechComplex` of `restrictOpenHypercover`. -/
def restrictCechComplexIso :
    restrictCechComplex A V F ≅ Stacks.CechSite.cechComplex (restrictOpenHypercover A V) F :=
  Alternating.cechCochainComplexIso ((restrictOpenFunctor A).op ⋙ F) V ≪≫
    (cechComplexRestrictIso A V F).symm

/-- **The ordered Čech complex of a restriction cover of an object of `Cris(X/S)` computes the
Čech cohomology of that covering family, in every degree.**

This is the step of [Stacks, Tag 07MN] that the source leaves as "a general result in cohomology
on sites, namely that the alternating Čech complex computes the cohomology provided it gives the
correct answer on all the pieces (insert future reference here)", as far as the *Čech* cohomology
of the family: [Stacks, Tag 01FM] says the alternating and the full Čech complexes are homotopy
equivalent, [Stacks, Tag 01FK] (2) says the alternating and the ordered ones are isomorphic, and
`restrictCechComplexIso` says the full one is the Čech complex of the covering family.  Passing
from Čech cohomology of the family to the cohomology of the covered object is
[Stacks, Tag 03F7], which is not applied here; it is applied, to this very isomorphism, in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/OrdCechCoveredObject.lean`
(`...SmallSite.restrictOrdCechOverCohomologyIso`), which cannot be imported here. -/
def restrictOrdCechCohomologyIso (j : ℕ) :
    (restrictCechComplexOrd A V F).homology j ≅
      Stacks.CechSite.cechCohomology (restrictOpenHypercover A V) F j :=
  Alternating.cechCochainComplexOrdHomologyIsoCechComplex ((restrictOpenFunctor A).op ⋙ F) V
      (fun i => isSubterminal_ambientOpen A (V i)) j ≪≫
    (cechCohomologyRestrictIso A V F j).symm

end Complexes

end Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening

end

end
