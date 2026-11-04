module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePerfectSections
public import StacksFrontier.Homology.Perfect.Colimit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The affine base case of essential surjectivity for perfect objects along a limit of spaces

Stacks 09RJ asserts, in Situation 09RH, that the category of perfect objects of `D(𝒪_X)` is the
colimit of the categories of perfect objects of the `D(𝒪_{X_i})`.  Full faithfulness is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectObjects.lean`.  The remaining half,
*essential surjectivity*, is proved in the source by the induction principle of Stacks 08GP over
the quasi-compact objects of `(X_0)_{étale}`.  **This file delivers the base case of that
induction**, condition (1) of the induction principle: the case in which the object of the small
étale site is affine.

The source settles the affine case by the scheme-level Stacks 09RF, read through the comparison
of the small étale and the Zariski site (Stacks 071Q, 08HG).  That route is not available here —
the scheme-level Stacks 09RF is formalized in
`StacksFrontier/AlgebraicGeometry/Perfect/LimitPerfectObjects.lean` only as its canonical cocone, so
neither its full faithfulness nor its essential surjectivity can be used.  The route taken
instead is the one the affine case of Stacks 09RF itself takes, applied directly on the small
étale site of a representable algebraic space: the affine ring-translation dictionary

`Φ_R : D(R) ≌ D_QCoh(𝒪_{h_U})`  for `U` with affine underlying scheme `Spec R`

of Stacks 08H1, together with affine base change `Lg^*Φ_R ≅ Φ_{R'}(- ⊗^L_R R')`, reduces the
statement to the ring-level Stacks 0BC7: a perfect complex over a filtered colimit of rings
descends to a finite stage.  Nothing of the scheme-level Stacks 09RF, and nothing of the glueing
lemma Stacks 08HB, is used.

## The situation, in the affine case

A directed inverse system of algebraic spaces with affine transition morphisms, all of whose
members are represented by objects of the big fppf site with affine underlying scheme, is a
filtered diagram `V : J ⥤ (BigFppfOver B S hS)ᵒᵖ` — contravariant, because the transition
morphisms of the system point from the later stage to the earlier — and the limit of the system,
again represented by an affine object, is the vertex of a cocone `c` on `V`.  The ring of global
functions turns `V` into a filtered diagram of rings `V ⋙ bigFppfSectionsRing` and `c` into a
cocone on it.

## Main results

* `AlgebraicGeometry.Space.exists_isPerfect_representedAffineStage`: **the affine base case of the
  essential-surjectivity half of Stacks 09RJ.**  Every perfect object of `D(𝒪_{h_U})` on the limit
  is, at some stage `j`, the derived pullback along `h_U ⟶ h_{V_j}` of a perfect object of
  `D(𝒪_{h_{V_j}})`.

## Main definitions

* `AlgebraicGeometry.Space.bigFppfSectionsRing`: global sections as a contravariant functor on the
  big fppf category over `S`, `U ↦ Γ(U, 𝒪)`.
* `AlgebraicGeometry.Space.coconeProjection`: the component of a cocone in
  `(BigFppfOver B S hS)ᵒᵖ`, read as a morphism out of the vertex in the big fppf category.

## The carried hypotheses

Two hypotheses are carried, and neither is any part of the conclusion of Stacks 09RJ or of
Stacks 09RF.

*`hc`: the diagram of rings of global functions has the ring of the limit as its colimit.*  In
Situation 09RH the limit `X = lim X_i` is given, with affine transition morphisms; for an affine
member of the system that hypothesis *is* the statement that the ring of the limit is the filtered
colimit of the rings of the stages, since a limit of affine schemes along affine transition
morphisms is the spectrum of the colimit of their rings.  So `hc` is a reading of the Situation's
own hypothesis "`X` is the limit of the `X_i`" in the affine case, an input of the source's proof,
and not a clause of its conclusion: it mentions no derived category, no perfect object and no
comparison functor, only the rings of global functions.  The scheme-level affine base case
`AlgebraicGeometry.AffinePerfectLimit.exists_isPerfect_stage` of
`StacksFrontier/AlgebraicGeometry/Perfect/LimitPerfectObjectsSupplement.lean` takes the same input in
the same shape, as does the ring-level Stacks 0BC7 itself.

A route to discharging `hc` from a limit taken in schemes rather than in algebraic spaces exists
in Mathlib: `AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone` turns a limit cone of qcqs schemes
with affine transition morphisms into a colimit cocone of their rings of global functions.  It is
not used here because applying it would need the cocone `c` to be exhibited as the opposite of a
limit cone of the underlying schemes — that is, the representability of the limit algebraic space
by the scheme-theoretic limit — which is a hypothesis of the same weight as `hc` itself, plus the
transport across `(Jᵒᵖ)ᵒᵖ ≃ J` that the shape of the Mathlib statement forces.

*`PreservesColimit (V ⋙ bigFppfSectionsRing B S hS) (forget CommRingCat)`: the colimit of rings is
computed on underlying sets.*  This is the instance premise of Stacks 0BC7, passed through
unchanged; the source's proof uses the description of the colimit ring by elements.  Mathlib
supplies it whenever the index category lives in the universe of the schemes, which is the only
case Situation 09RH needs, and it is stated as an instance premise so that instance search
discharges it there.

Nothing else is assumed.  In particular the perfectness of the descended object is *proved*, not
hypothesised, and so is the identification of its derived pullback with the given object; neither
the existence of a glued object for an elementary distinguished square (Stacks 08HB (1)) nor any
clause of the scheme-level Stacks 09RF appears.

## What is not here

The induction of Stacks 08GP that globalises this base case over the quasi-compact objects of
`(X_0)_{étale}` is not run, so essential surjectivity for Stacks 09RJ is **not** proved: the step
for an elementary distinguished square needs clause (1) of the glueing lemma Stacks 08HB, the
existence of the glued object, and only its clause (2),
`AlgebraicGeometry.Space.exists_hom_of_glueData` of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/MayerVietorisGlueing.lean`, which takes the glued
datum as input, is in the tree.  Nothing below is tagged, since a fragment of 09RJ's essential
surjectivity is not 09RJ.

## Implementation notes

The statement is about the represented algebraic spaces `h_U = yoneda.obj U` rather than about
abstract members of a `AlgebraicGeometry.Space.DescentSituation`: the affine translation
dictionary `AlgebraicGeometry.Space.representedAffineDerivedAssociated` and its base change
`AlgebraicGeometry.Space.representedAffineDerivedBaseChangeIso` are stated for an object of the
big fppf site with affine underlying scheme, which is exactly what an affine object of the small
étale site of `X_0` provides, and the derived pullback used is the canonical
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback` rather than a carried system.

The three steps of the proof are:

* `E` is pseudo-coherent, hence lies in `D_QCoh`, so the counit `Φ_R(RΓ(E)) ⟶ E` is invertible
  (`AlgebraicGeometry.Space.isIso_representedAffineDerivedAdjunction_counit_app`), and `RΓ(E)` is
  a perfect object of `D(R)`
  (`AlgebraicGeometry.Space.isPerfect_representedAffineDerivedSections_obj`);
* Stacks 0BC7 descends `RΓ(E)` to a perfect `M_j ∈ D(R_j)` with `RΓ(E) ≅ M_j ⊗^L_{R_j} R`;
* affine base change identifies `Lg_j^*(Φ_{R_j}M_j)` with `Φ_R(M_j ⊗^L_{R_j} R)`, and `Φ_{R_j}M_j`
  is perfect (`AlgebraicGeometry.Space.isPerfect_representedAffineDerivedAssociated_obj`).

The ring diagram and the ring cocone are the images of `V` and `c` under
`AlgebraicGeometry.Space.bigFppfSectionsRing`, so the ring map `R_j ⟶ R` at a stage is the one
`AlgebraicGeometry.Space.representedAffineDerivedBaseChangeIso` uses on the nose
(`AlgebraicGeometry.Scheme.Γ_map` is a `rfl` lemma); this is why the diagram is not taken as
separate data with a compatibility hypothesis.

## References

* [Stacks Project, Lemma 75.24.3 (Tag 09RJ)](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Lemma 75.9.3 (Tag 08GP)](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Lemma 36.29.3 (Tag 09RF)](https://stacks.math.columbia.edu/tag/09RF)
* [Stacks Project, Lemma 15.76.18 (Tag 0BC7)](https://stacks.math.columbia.edu/tag/0BC7)
* [Stacks Project, Lemma 75.13.6 (Tag 08H1)](https://stacks.math.columbia.edu/tag/08H1)
* [Stacks Project, Lemma 75.10.8 (Tag 08HB)](https://stacks.math.columbia.edu/tag/08HB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Global sections as a functor on the big fppf category over `S`**: `U ↦ Γ(U, 𝒪)`, with a
morphism `g : U' ⟶ U` sent to the induced map of rings of global functions.  It is
`AlgebraicGeometry.Scheme.Γ` composed with the passage to the underlying scheme, so its value on
a morphism is `AlgebraicGeometry.Space.representedAffineCommRingCatHom` on the nose. -/
@[ega "0 12.1.3" "special case"]
abbrev bigFppfSectionsRing : (BigFppfOver B S hS)ᵒᵖ ⥤ CommRingCat.{u} :=
  (BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ

/-- **The projection from the vertex of a cocone in `(BigFppfOver B S hS)ᵒᵖ` to a member of the
diagram**, read in the big fppf category over `S`: the component `c.ι.app j` of the cocone turned
around.  This is that component and nothing else; it exists only so that the source of the
morphism is spelled `c.pt` rather than the value at `j` of the constant diagram at `c.pt`, which
is the same object but blocks instance search for a property of it. -/
abbrev coconeProjection {J : Type v} [Category.{v} J] {V : J ⥤ (BigFppfOver B S hS)ᵒᵖ}
    (c : Cocone V) (j : J) : c.pt.unop ⟶ (V.obj j).unop :=
  (c.ι.app j).unop

section AffineBase

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

variable {J : Type v} [Category.{v} J] [IsFiltered J] (V : J ⥤ (BigFppfOver B S hS)ᵒᵖ)
  (c : Cocone V)
  [∀ j : J, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j).unop)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt.unop)]

/-- **The affine base case of the essential-surjectivity half of Stacks 09RJ.**  Let
`V : J ⥤ (BigFppfOver B S hS)ᵒᵖ` be a filtered diagram of objects of the big fppf category over
`S` with affine underlying schemes — a directed inverse system of affine algebraic spaces, written
contravariantly — and let `c` be a cocone on it whose vertex again has affine underlying scheme,
such that the induced cocone of rings of global functions is a colimit.  Write `U = c.pt` for the
limit object, `V_j` for the stages, `R = Γ(U, 𝒪)` and `R_j = Γ(V_j, 𝒪)`.

Then every perfect object `E` of `D(𝒪_{h_U})` is, at some stage `j`, the derived pullback along
`h_U ⟶ h_{V_j}` of a perfect object of `D(𝒪_{h_{V_j}})`.

This is condition (1) of the induction principle of Stacks 08GP in the source's proof of the
essential surjectivity of the comparison out of the colimit of the categories of perfect objects.
Its proof is not the source's reduction to the scheme-level Stacks 09RF, which is unavailable
here; it is the affine dictionary `D(R) ≌ D_QCoh(𝒪_{h_U})` of Stacks 08H1 together with affine
base change and the ring-level Stacks 0BC7.  The hypothesis `hc` and the instance premise on the
forgetful functor are carried; see "The carried hypotheses" in this file's module documentation
for why neither is part of the conclusion. -/
theorem exists_isPerfect_representedAffineStage
    [PreservesColimit (V ⋙ bigFppfSectionsRing B S hS) (forget CommRingCat.{u})]
    (hc : IsColimit ((bigFppfSectionsRing B S hS).mapCocone c))
    (E : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj c.pt.unop)
      (isAlgebraicSpace_yoneda B S hS c.pt.unop)))
    (hE : (smallEtaleRingedSite B S hS (yoneda.obj c.pt.unop)
      (isAlgebraicSpace_yoneda B S hS c.pt.unop)).IsPerfect E) :
    ∃ (j : J) (Ej : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj (V.obj j).unop)
        (isAlgebraicSpace_yoneda B S hS (V.obj j).unop))),
      (smallEtaleRingedSite B S hS (yoneda.obj (V.obj j).unop)
          (isAlgebraicSpace_yoneda B S hS (V.obj j).unop)).IsPerfect Ej ∧
        Nonempty ((smallEtaleDerivedModulePullback B S hS
          (representedSpaceMap B S hS (coconeProjection B S hS c j))).obj Ej ≅ E) := by
  have hQ := qcohDerived_of_isPerfect B S hS
    ⟨yoneda.obj c.pt.unop, isAlgebraicSpace_yoneda B S hS c.pt.unop⟩ E hE
  have hcounit : IsIso ((representedAffineDerivedAdjunction B S hS c.pt.unop).counit.app E) :=
    isIso_representedAffineDerivedAdjunction_counit_app B S hS c.pt.unop E hQ
  obtain ⟨j, Mj, hMj, ⟨eM⟩⟩ := (StacksDraft.Perfect.perfectComplexes_filteredColimit
    (V ⋙ bigFppfSectionsRing B S hS) ((bigFppfSectionsRing B S hS).mapCocone c) hc).1
    ((representedAffineDerivedSections B S hS c.pt.unop).obj E)
    (isPerfect_representedAffineDerivedSections_obj B S hS c.pt.unop E hE)
  refine ⟨j, (representedAffineDerivedAssociated B S hS (V.obj j).unop).obj Mj,
    isPerfect_representedAffineDerivedAssociated_obj B S hS (V.obj j).unop Mj hMj, ⟨?_⟩⟩
  exact (representedAffineDerivedBaseChangeIso B S hS (coconeProjection B S hS c j)).app Mj ≪≫
    (representedAffineDerivedAssociated B S hS c.pt.unop).mapIso eM.symm ≪≫
    @asIso _ _ _ _ _ hcounit

end AffineBase

end AlgebraicGeometry.Space

end
