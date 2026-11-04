module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitByPointResolutionFunctorialityAbelian
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitByPointResolutionFunctorialityModule
import StacksCore.Tactic.StacksAttribute

/-!
# Derived lower shriek of a complex is unchanged under a functor with a common resolution

Let `f : C' ⥤ C` be a functor between small categories carrying their chaotic topologies, let
`g^{-1}` be the inverse image of the induced morphism of ringed topoi — restriction along `f` —
and let `U_•` be a cosimplicial object of `C'` such that both `U_•` and its image `f(U_•)` are
point resolutions, so that the criterion of [Stacks, Tag 08Q9] applies on both sites. Then

`Lπ'_! ∘ g^{-1} = Lπ_!`

**as an isomorphism of functors of a bounded above complex of coefficients**, with values in
`D(Ab)` at abelian coefficients and in `D(B)` at module coefficients.

## Main results

* `Stacks.ChaoticSite.AbelianValued.derivedColimitPresheafRestrictionComplexNatIso`: the
  statement at abelian coefficients, as an isomorphism of functors on the complexes of abelian
  presheaves on `C` that are strictly bounded above by `0`.
* `Stacks.ChaoticSite.ModuleValued.derivedColimitInverseImageComplexNatIso`: the statement at
  module coefficients, as an isomorphism of functors on the complexes of `B̲`-modules on `C` that
  are strictly bounded above by `0`.

## What is proved and what it rests on

Both sides are the total complex of **one and the same double complex**: the double complex of
`g^{-1}K^•` on `U_•` has in the column `p` the extended Moore complex of `(g^{-1}K^p)(U_•)`,
which is the extended Moore complex of `K^p(f(U_•))`, the column `p` of the double complex of
`K^•` on `f(U_•)`. Evaluating the restriction of a diagram on `U_•` and evaluating the diagram
itself on `f(U_•)` are both precomposition with `(U_• ⋙ f).op`, so the two double complexes are
equal on the nose — `Stacks.ChaoticSite.ModuleValued.mooreBicomplex_inverseImageAlongAFunctor`
and its abelian twin — and so are the maps they induce. The comparison is therefore the composite
of the two instances of the derived form of [Stacks, Tag 08Q9] for complexes,
`Stacks.ChaoticSite.ModuleValued.totalQIsoDerivedColimitOfResolution` at `U_•` on `C'` and at
`f(U_•)` on `C`, with nothing in between.

The resolutions that those two comparisons take as a parameter are chosen **independently on the
two sites**: `Stacks.ChaoticSite.chosenProjectiveResolution` picks, for each complex strictly
bounded above by `0`, a resolution by projective objects of the category it lives in, by
[Stacks, Tag 0646]. Nothing asks `g^{-1}` to carry a resolution on `C` to a resolution on `C'`,
and nothing asks it to preserve projectives — which it does not. This is why the statement for
complexes costs no more than the statement at the heart: the only input that crosses between the
two sites is the equality of the two double complexes.

Naturality in the complex is
`Stacks.ChaoticSite.ModuleValued.totalQIsoDerivedColimitOfResolution_naturality_of_epi` on each
side: the chosen resolutions are degreewise epimorphic, so a morphism of complexes lifts to them
on the nose and the comparison does not depend on the lift.

## Implementation notes

`Stacks.ChaoticSite.inverseImageAlongAFunctor` is a `def`, hence opaque to tactics, while the
double complex is built from reducible definitions. The equality of the two double complexes is
therefore spent **once, in term mode**, as the type ascription that gives
`Stacks.ChaoticSite.ModuleValued.totalQIsoDerivedColimitInverseImage` and its naturality their
statements: those are the comparison on `C'` and its naturality, read at the double complex of
`K^•` on `f(U_•)` rather than at the double complex of `g^{-1}K^•` on `U_•`. After that both
factors of the comparison have the same middle object on the nose, and the naturality of the
composite is isomorphism algebra which no tactic has to see through a `def`.

## The domain

The source states Tag 08QA for functors `D(C) ⥤ D(Ab)`, resp. `D(C, B̲) ⥤ D(B)`, on the
unbounded derived category. The isomorphisms of functors proved here have as domain the full
subcategory `Stacks.ChaoticSite.strictlyLEZero` of complexes of coefficients strictly bounded
above by `0`, which is where the development's derived form of [Stacks, Tag 08Q9] for complexes
is available, and they contain the forms at the heart —
`Stacks.ChaoticSite.AbelianValued.derivedColimitPresheafRestrictionNatIso` and
`Stacks.ChaoticSite.ModuleValued.derivedColimitInverseImageNatIso` — as the special case of a
complex concentrated in degree `0`.

What an arbitrary unbounded complex needs is not a different argument on the two sites but a
different computation of `Lπ_!` on one site: the second filtration of the double complex,
`Stacks.ChaoticSite.ModuleValued.quasiIso_mooreBicomplexTotalMap`, is proved from the vanishing
of the columns above `0`, and the total complex of the double complex of an unbounded complex is
not `Lπ_!` of it. The route for the unbounded statement is instead the dévissage
`StacksDraft.CompactDevissage.natIsoOfIsCompactlyGenerated` along the compact generators
`j_{U!}B̲_U` of `D(C, B̲)`, for which the comparison has first to be constructed as a morphism of
triangulated functors — the `Lπ'_!`-adjunct of `g^{-1}` applied to the unit of
`Stacks.CategoryHomology.totalDerivedColimitAdjunction` — and then identified, on each generator,
with the comparison at the heart.

## References

* [Stacks Project, Tag 08QA](https://stacks.math.columbia.edu/tag/08QA)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08PH](https://stacks.math.columbia.edu/tag/08PH)
* [Stacks Project, Tag 0646](https://stacks.math.columbia.edu/tag/0646)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.CategoryHomology

namespace Stacks.ChaoticSite

universe v₀ u₀ u

attribute [local instance] HasDerivedCategory.standard

/-! ### Resolutions of a bounded above complex, chosen once and for all -/

/-- **A chosen resolution of a complex strictly bounded above by `0` by projective objects, whose
structure morphism is epimorphic in every degree**, as produced by [Stacks, Tag 0646]. The
degreewise epimorphism is what makes a morphism of complexes lift to the resolutions on the nose,
so that no functorial choice of resolution is needed for naturality. -/
def chosenProjectiveResolution {A : Type u₀} [Category.{v₀} A] [Abelian A] [EnoughProjectives A]
    (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] :
    ProjectiveResolutionLemma.ProjectiveResolutionComplex K 0 :=
  (ProjectiveResolutionLemma.statement3 (0 : ℤ) K inferInstance).choose

/-- The structure morphism of `Stacks.ChaoticSite.chosenProjectiveResolution` is epimorphic in
every degree. -/
lemma epi_chosenProjectiveResolution_α {A : Type u₀} [Category.{v₀} A] [Abelian A]
    [EnoughProjectives A] (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] (n : ℤ) :
    Epi ((chosenProjectiveResolution K).α.f n) :=
  (ProjectiveResolutionLemma.statement3 (0 : ℤ) K inferInstance).choose_spec n

/-- **The complexes of coefficients strictly bounded above by `0`**, as a full subcategory of the
complexes of coefficients. This is the domain of the comparisons of this file. -/
def strictlyLEZero (A : Type u₀) [Category.{v₀} A] [HasZeroMorphisms A] :
    ObjectProperty (CochainComplex A ℤ) :=
  fun K => K.IsStrictlyLE 0

namespace ModuleValued

variable {C C' : Type u} [SmallCategory C] [SmallCategory C'] {B : Type u} [Ring B]

/-! ### Module coefficients -/

/-- **The double complex of the inverse image of a complex on `U_•` is the double complex of the
complex itself on `f(U_•)`.** Both are precomposition of the complex with `(U_• ⋙ f).op`
columnwise, so this is an equality of double complexes. -/
lemma mooreBicomplex_inverseImageAlongAFunctor (f : C' ⥤ C) (U : CosimplicialObject C')
    (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ) :
    mooreBicomplex U (((inverseImageAlongAFunctor C C' f B).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) = mooreBicomplex (U ⋙ f) K :=
  rfl

/-- **The derived form of [Stacks, Tag 08Q9] on `C'`, for the inverse image of a complex on `C`,
read at the double complex of that complex on `f(U_•)`**: `Q(Tot(Z_K)) ≅ Lπ'_!(g^{-1}K^•)`. This
is `Stacks.ChaoticSite.ModuleValued.totalQIsoDerivedColimitOfResolution` at `U_•` on `C'`, whose
source is the total complex of the double complex of `g^{-1}K^•` on `U_•`; that double complex is
the double complex of `K^•` on `f(U_•)` by
`Stacks.ChaoticSite.ModuleValued.mooreBicomplex_inverseImageAlongAFunctor`, and this definition
is where that equality is spent. -/
def totalQIsoDerivedColimitInverseImage (f : C' ⥤ C) (U : CosimplicialObject C')
    (hU : IsPointResolution U) (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ)
    [K.IsStrictlyLE 0] :
    DerivedCategory.Q.obj ((mooreBicomplex (U ⋙ f) K).total (ComplexShape.up ℤ)) ≅
      (totalDerivedColimit C' (ModuleCat.{u} B)).obj (DerivedCategory.Q.obj
        (((inverseImageAlongAFunctor C C' f B).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)) :=
  have := (chosenProjectiveResolution (((inverseImageAlongAFunctor C C' f B).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K)).projective
  have := (chosenProjectiveResolution (((inverseImageAlongAFunctor C C' f B).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K)).boundedAbove
  have := (chosenProjectiveResolution (((inverseImageAlongAFunctor C C' f B).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K)).quasiIso
  totalQIsoDerivedColimitOfResolution U hU
    (((inverseImageAlongAFunctor C C' f B).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    (chosenProjectiveResolution (((inverseImageAlongAFunctor C C' f B).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K)).complex
    (chosenProjectiveResolution (((inverseImageAlongAFunctor C C' f B).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K)).α

/-- **`Stacks.ChaoticSite.ModuleValued.totalQIsoDerivedColimitInverseImage` is natural in the
complex**, read at the double complex on `f(U_•)`: the map of total complexes induced by
`φ : K^• ⟶ L^•` through the double complexes on `f(U_•)` is the map induced by `g^{-1}φ` through
the double complexes on `U_•`. -/
lemma totalQIsoDerivedColimitInverseImage_naturality (f : C' ⥤ C) (U : CosimplicialObject C')
    (hU : IsPointResolution U) {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ}
    [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (φ : K ⟶ L) :
    DerivedCategory.Q.map (HomologicalComplex₂.total.map
          ((mooreBicomplexFunctor (U ⋙ f)).map φ) (ComplexShape.up ℤ)) ≫
        (totalQIsoDerivedColimitInverseImage f U hU L).hom =
      (totalQIsoDerivedColimitInverseImage f U hU K).hom ≫
        (totalDerivedColimit C' (ModuleCat.{u} B)).map (DerivedCategory.Q.map
          (((inverseImageAlongAFunctor C C' f B).mapHomologicalComplex
            (ComplexShape.up ℤ)).map φ)) :=
  have := (chosenProjectiveResolution (((inverseImageAlongAFunctor C C' f B).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K)).projective
  have := (chosenProjectiveResolution (((inverseImageAlongAFunctor C C' f B).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K)).boundedAbove
  have := (chosenProjectiveResolution (((inverseImageAlongAFunctor C C' f B).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K)).quasiIso
  have := (chosenProjectiveResolution (((inverseImageAlongAFunctor C C' f B).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj L)).projective
  have := (chosenProjectiveResolution (((inverseImageAlongAFunctor C C' f B).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj L)).boundedAbove
  have := (chosenProjectiveResolution (((inverseImageAlongAFunctor C C' f B).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj L)).quasiIso
  totalQIsoDerivedColimitOfResolution_naturality_of_epi U hU
    (chosenProjectiveResolution (((inverseImageAlongAFunctor C C' f B).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K)).α
    (chosenProjectiveResolution (((inverseImageAlongAFunctor C C' f B).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L)).α
    (epi_chosenProjectiveResolution_α _)
    (((inverseImageAlongAFunctor C C' f B).mapHomologicalComplex (ComplexShape.up ℤ)).map φ)

/-- **The comparison on `C`, at a chosen resolution.** This is
`Stacks.ChaoticSite.ModuleValued.totalQIsoDerivedColimitOfResolution` at `f(U_•)` on `C`, read at
the resolution `Stacks.ChaoticSite.chosenProjectiveResolution` of `K^•`. -/
def totalQIsoDerivedColimitChosen (f : C' ⥤ C) (U : CosimplicialObject C')
    (hfU : IsPointResolution (U ⋙ f)) (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ)
    [K.IsStrictlyLE 0] :
    DerivedCategory.Q.obj ((mooreBicomplex (U ⋙ f) K).total (ComplexShape.up ℤ)) ≅
      (totalDerivedColimit C (ModuleCat.{u} B)).obj (DerivedCategory.Q.obj K) :=
  have := (chosenProjectiveResolution K).projective
  have := (chosenProjectiveResolution K).boundedAbove
  have := (chosenProjectiveResolution K).quasiIso
  totalQIsoDerivedColimitOfResolution (U ⋙ f) hfU K (chosenProjectiveResolution K).complex
    (chosenProjectiveResolution K).α

/-- **`Stacks.ChaoticSite.ModuleValued.totalQIsoDerivedColimitChosen` is natural in the
complex.** -/
lemma totalQIsoDerivedColimitChosen_naturality (f : C' ⥤ C) (U : CosimplicialObject C')
    (hfU : IsPointResolution (U ⋙ f)) {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ}
    [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (φ : K ⟶ L) :
    DerivedCategory.Q.map (HomologicalComplex₂.total.map
          ((mooreBicomplexFunctor (U ⋙ f)).map φ) (ComplexShape.up ℤ)) ≫
        (totalQIsoDerivedColimitChosen f U hfU L).hom =
      (totalQIsoDerivedColimitChosen f U hfU K).hom ≫
        (totalDerivedColimit C (ModuleCat.{u} B)).map (DerivedCategory.Q.map φ) :=
  have := (chosenProjectiveResolution K).projective
  have := (chosenProjectiveResolution K).boundedAbove
  have := (chosenProjectiveResolution K).quasiIso
  have := (chosenProjectiveResolution L).projective
  have := (chosenProjectiveResolution L).boundedAbove
  have := (chosenProjectiveResolution L).quasiIso
  totalQIsoDerivedColimitOfResolution_naturality_of_epi (U ⋙ f) hfU
    (chosenProjectiveResolution K).α (chosenProjectiveResolution L).α
    (epi_chosenProjectiveResolution_α _) φ

/-- **Stacks 08QA in `D(B)` for a bounded above complex, at one complex.** The derived lower
shriek on `C'` of the inverse image of a complex `K^•` of `B̲`-modules on `C` is the derived lower
shriek of `K^•` on `C`. Both are the total complex of the one double complex
`Z^{p, q} = (K^p(f(U_•)))^q`, by the derived form of [Stacks, Tag 08Q9] for complexes read on
`C'` at `U_•` and on `C` at `f(U_•)`; the resolutions the two readings need are chosen
independently on the two sites. -/
def derivedColimitInverseImageComplexIso (f : C' ⥤ C) (U : CosimplicialObject C')
    (hU : IsPointResolution U) (hfU : IsPointResolution (U ⋙ f))
    (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ) [K.IsStrictlyLE 0] :
    (totalDerivedColimit C' (ModuleCat.{u} B)).obj (DerivedCategory.Q.obj
        (((inverseImageAlongAFunctor C C' f B).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)) ≅
      (totalDerivedColimit C (ModuleCat.{u} B)).obj (DerivedCategory.Q.obj K) :=
  (totalQIsoDerivedColimitInverseImage f U hU K).symm ≪≫ totalQIsoDerivedColimitChosen f U hfU K

/-- **`Stacks.ChaoticSite.ModuleValued.derivedColimitInverseImageComplexIso` is natural in the
complex.** Each of its two factors is, and both are read at the same map of total complexes — the
one induced by `φ` through the double complexes on `f(U_•)`. -/
lemma derivedColimitInverseImageComplexIso_naturality (f : C' ⥤ C) (U : CosimplicialObject C')
    (hU : IsPointResolution U) (hfU : IsPointResolution (U ⋙ f))
    {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0]
    (φ : K ⟶ L) :
    (totalDerivedColimit C' (ModuleCat.{u} B)).map (DerivedCategory.Q.map
          (((inverseImageAlongAFunctor C C' f B).mapHomologicalComplex
            (ComplexShape.up ℤ)).map φ)) ≫
        (derivedColimitInverseImageComplexIso f U hU hfU L).hom =
      (derivedColimitInverseImageComplexIso f U hU hfU K).hom ≫
        (totalDerivedColimit C (ModuleCat.{u} B)).map (DerivedCategory.Q.map φ) := by
  dsimp only [derivedColimitInverseImageComplexIso, Iso.trans_hom, Iso.symm_hom]
  rw [← cancel_epi (totalQIsoDerivedColimitInverseImage f U hU K).hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  slice_lhs 1 2 => rw [← totalQIsoDerivedColimitInverseImage_naturality f U hU φ]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact totalQIsoDerivedColimitChosen_naturality f U hfU φ

/-- **Stacks 08QA in `D(B)` for bounded above complexes, as an isomorphism of functors.** Let
`f : C' ⥤ C` be a functor between small categories with their chaotic topologies, let `B` be a
ring, let `g^{-1}` be the inverse image of the induced morphism of ringed topoi — restriction of
diagrams of `B`-modules along `f` — and let `U_•` be a cosimplicial object of `C'` such that both
`U_•` and `f(U_•)` are point resolutions. Then

`Lπ'_! ∘ g^{-1} = Lπ_!`

as functors from the complexes of `B̲`-modules on `C` strictly bounded above by `0` to `D(B)`. -/
@[stacks 08QA "the identification `Lπ'_! ∘ g^{-1} = Lπ_!` with values in `D(B)`, at module \
  coefficients, as an isomorphism of functors of a COMPLEX of coefficients strictly bounded \
  above by `0`, whose domain contains the complexes concentrated in degree `0`, so that the \
  statement specialises to the form at the heart (the two isomorphisms are not compared). The source states the identification on the unbounded `D(C, B̲)`; the module docstring \
  records what the unbounded case needs, namely the dévissage along the compact generators, the \
  total complex of the double complex of an unbounded complex not being `Lπ_!` of it"]
def derivedColimitInverseImageComplexNatIso (f : C' ⥤ C) (U : CosimplicialObject C')
    (hU : IsPointResolution U) (hfU : IsPointResolution (U ⋙ f)) :
    (strictlyLEZero (Cᵒᵖ ⥤ ModuleCat.{u} B)).ι ⋙
        (inverseImageAlongAFunctor C C' f B).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q ⋙ totalDerivedColimit C' (ModuleCat.{u} B) ≅
      (strictlyLEZero (Cᵒᵖ ⥤ ModuleCat.{u} B)).ι ⋙
        DerivedCategory.Q ⋙ totalDerivedColimit C (ModuleCat.{u} B) :=
  NatIso.ofComponents
    (fun K =>
      haveI : CochainComplex.IsStrictlyLE K.obj 0 := K.property
      derivedColimitInverseImageComplexIso f U hU hfU K.obj)
    (fun {K L} φ => by
      have : CochainComplex.IsStrictlyLE K.obj 0 := K.property
      have : CochainComplex.IsStrictlyLE L.obj 0 := L.property
      exact derivedColimitInverseImageComplexIso_naturality f U hU hfU φ.hom)

end ModuleValued

namespace AbelianValued

variable {C C' : Type u} [SmallCategory C] [SmallCategory C']

/-! ### Abelian coefficients -/

/-- **The double complex of the restriction of a complex on `U_•` is the double complex of the
complex itself on `f(U_•)`.** Both are precomposition of the complex with `(U_• ⋙ f).op`
columnwise, so this is an equality of double complexes. -/
lemma mooreBicomplex_presheafRestriction (f : C' ⥤ C) (U : CosimplicialObject C')
    (K : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ) :
    mooreBicomplex U (((Stacks.CategoryHomology.presheafRestriction.{u, u, u}
        f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) = mooreBicomplex (U ⋙ f) K :=
  rfl

/-- **The derived form of [Stacks, Tag 08Q9] on `C'`, for the restriction of a complex on `C`,
read at the double complex of that complex on `f(U_•)`**: `Q(Tot(Z_K)) ≅ Lπ'_!(g^{-1}K^•)`. -/
def totalQIsoDerivedColimitPresheafRestriction (f : C' ⥤ C) (U : CosimplicialObject C')
    (hU : IsPointResolution U) (K : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ)
    [K.IsStrictlyLE 0] :
    DerivedCategory.Q.obj ((mooreBicomplex (U ⋙ f) K).total (ComplexShape.up ℤ)) ≅
      (totalDerivedColimit C' AddCommGrpCat.{u}).obj (DerivedCategory.Q.obj
        (((Stacks.CategoryHomology.presheafRestriction.{u, u, u} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)) :=
  have := (chosenProjectiveResolution (((Stacks.CategoryHomology.presheafRestriction.{u, u, u}
    f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).projective
  have := (chosenProjectiveResolution (((Stacks.CategoryHomology.presheafRestriction.{u, u, u}
    f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).boundedAbove
  have := (chosenProjectiveResolution (((Stacks.CategoryHomology.presheafRestriction.{u, u, u}
    f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).quasiIso
  totalQIsoDerivedColimitOfResolution U hU
    (((Stacks.CategoryHomology.presheafRestriction.{u, u, u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K)
    (chosenProjectiveResolution (((Stacks.CategoryHomology.presheafRestriction.{u, u, u}
      f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).complex
    (chosenProjectiveResolution (((Stacks.CategoryHomology.presheafRestriction.{u, u, u}
      f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).α

/-- **`Stacks.ChaoticSite.AbelianValued.totalQIsoDerivedColimitPresheafRestriction` is natural in
the complex**, read at the double complex on `f(U_•)`. -/
lemma totalQIsoDerivedColimitPresheafRestriction_naturality (f : C' ⥤ C)
    (U : CosimplicialObject C') (hU : IsPointResolution U)
    {K L : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0]
    (φ : K ⟶ L) :
    DerivedCategory.Q.map (HomologicalComplex₂.total.map
          ((mooreBicomplexFunctor (U ⋙ f)).map φ) (ComplexShape.up ℤ)) ≫
        (totalQIsoDerivedColimitPresheafRestriction f U hU L).hom =
      (totalQIsoDerivedColimitPresheafRestriction f U hU K).hom ≫
        (totalDerivedColimit C' AddCommGrpCat.{u}).map (DerivedCategory.Q.map
          (((Stacks.CategoryHomology.presheafRestriction.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).map φ)) :=
  have := (chosenProjectiveResolution (((Stacks.CategoryHomology.presheafRestriction.{u, u, u}
    f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).projective
  have := (chosenProjectiveResolution (((Stacks.CategoryHomology.presheafRestriction.{u, u, u}
    f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).boundedAbove
  have := (chosenProjectiveResolution (((Stacks.CategoryHomology.presheafRestriction.{u, u, u}
    f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).quasiIso
  have := (chosenProjectiveResolution (((Stacks.CategoryHomology.presheafRestriction.{u, u, u}
    f).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)).projective
  have := (chosenProjectiveResolution (((Stacks.CategoryHomology.presheafRestriction.{u, u, u}
    f).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)).boundedAbove
  have := (chosenProjectiveResolution (((Stacks.CategoryHomology.presheafRestriction.{u, u, u}
    f).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)).quasiIso
  totalQIsoDerivedColimitOfResolution_naturality_of_epi U hU
    (chosenProjectiveResolution (((Stacks.CategoryHomology.presheafRestriction.{u, u, u}
      f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).α
    (chosenProjectiveResolution (((Stacks.CategoryHomology.presheafRestriction.{u, u, u}
      f).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)).α
    (epi_chosenProjectiveResolution_α _)
    (((Stacks.CategoryHomology.presheafRestriction.{u, u, u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).map φ)

/-- **The comparison on `C`, at a chosen resolution.** -/
def totalQIsoDerivedColimitChosen (f : C' ⥤ C) (U : CosimplicialObject C')
    (hfU : IsPointResolution (U ⋙ f)) (K : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ)
    [K.IsStrictlyLE 0] :
    DerivedCategory.Q.obj ((mooreBicomplex (U ⋙ f) K).total (ComplexShape.up ℤ)) ≅
      (totalDerivedColimit C AddCommGrpCat.{u}).obj (DerivedCategory.Q.obj K) :=
  have := (chosenProjectiveResolution K).projective
  have := (chosenProjectiveResolution K).boundedAbove
  have := (chosenProjectiveResolution K).quasiIso
  totalQIsoDerivedColimitOfResolution (U ⋙ f) hfU K (chosenProjectiveResolution K).complex
    (chosenProjectiveResolution K).α

/-- **`Stacks.ChaoticSite.AbelianValued.totalQIsoDerivedColimitChosen` is natural in the
complex.** -/
lemma totalQIsoDerivedColimitChosen_naturality (f : C' ⥤ C) (U : CosimplicialObject C')
    (hfU : IsPointResolution (U ⋙ f)) {K L : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ}
    [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (φ : K ⟶ L) :
    DerivedCategory.Q.map (HomologicalComplex₂.total.map
          ((mooreBicomplexFunctor (U ⋙ f)).map φ) (ComplexShape.up ℤ)) ≫
        (totalQIsoDerivedColimitChosen f U hfU L).hom =
      (totalQIsoDerivedColimitChosen f U hfU K).hom ≫
        (totalDerivedColimit C AddCommGrpCat.{u}).map (DerivedCategory.Q.map φ) :=
  have := (chosenProjectiveResolution K).projective
  have := (chosenProjectiveResolution K).boundedAbove
  have := (chosenProjectiveResolution K).quasiIso
  have := (chosenProjectiveResolution L).projective
  have := (chosenProjectiveResolution L).boundedAbove
  have := (chosenProjectiveResolution L).quasiIso
  totalQIsoDerivedColimitOfResolution_naturality_of_epi (U ⋙ f) hfU
    (chosenProjectiveResolution K).α (chosenProjectiveResolution L).α
    (epi_chosenProjectiveResolution_α _) φ

/-- **Stacks 08QA in `D(Ab)` for a bounded above complex, at one complex.** The derived lower
shriek on `C'` of the restriction of a complex `K^•` of abelian presheaves on `C` is the derived
lower shriek of `K^•` on `C`. Both are the total complex of the one double complex
`Z^{p, q} = (K^p(f(U_•)))^q`. -/
def derivedColimitPresheafRestrictionComplexIso (f : C' ⥤ C) (U : CosimplicialObject C')
    (hU : IsPointResolution U) (hfU : IsPointResolution (U ⋙ f))
    (K : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ) [K.IsStrictlyLE 0] :
    (totalDerivedColimit C' AddCommGrpCat.{u}).obj (DerivedCategory.Q.obj
        (((Stacks.CategoryHomology.presheafRestriction.{u, u, u} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)) ≅
      (totalDerivedColimit C AddCommGrpCat.{u}).obj (DerivedCategory.Q.obj K) :=
  (totalQIsoDerivedColimitPresheafRestriction f U hU K).symm ≪≫
    totalQIsoDerivedColimitChosen f U hfU K

/-- **`Stacks.ChaoticSite.AbelianValued.derivedColimitPresheafRestrictionComplexIso` is natural in
the complex.** -/
lemma derivedColimitPresheafRestrictionComplexIso_naturality (f : C' ⥤ C)
    (U : CosimplicialObject C') (hU : IsPointResolution U) (hfU : IsPointResolution (U ⋙ f))
    {K L : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0]
    (φ : K ⟶ L) :
    (totalDerivedColimit C' AddCommGrpCat.{u}).map (DerivedCategory.Q.map
          (((Stacks.CategoryHomology.presheafRestriction.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).map φ)) ≫
        (derivedColimitPresheafRestrictionComplexIso f U hU hfU L).hom =
      (derivedColimitPresheafRestrictionComplexIso f U hU hfU K).hom ≫
        (totalDerivedColimit C AddCommGrpCat.{u}).map (DerivedCategory.Q.map φ) := by
  dsimp only [derivedColimitPresheafRestrictionComplexIso, Iso.trans_hom, Iso.symm_hom]
  rw [← cancel_epi (totalQIsoDerivedColimitPresheafRestriction f U hU K).hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  slice_lhs 1 2 => rw [← totalQIsoDerivedColimitPresheafRestriction_naturality f U hU φ]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact totalQIsoDerivedColimitChosen_naturality f U hfU φ

/-- **Stacks 08QA in `D(Ab)` for bounded above complexes, as an isomorphism of functors.** Let
`f : C' ⥤ C` be a functor between small categories with their chaotic topologies, let `g^{-1}` be
restriction of abelian presheaves along `f`, and let `U_•` be a cosimplicial object of `C'` such
that both `U_•` and `f(U_•)` are point resolutions. Then

`Lπ'_! ∘ g^{-1} = Lπ_!`

as functors from the complexes of abelian presheaves on `C` strictly bounded above by `0` to
`D(Ab)`. -/
@[stacks 08QA "the identification `Lπ'_! ∘ g^{-1} = Lπ_!` with values in `D(Ab)`, at abelian \
  coefficients, as an isomorphism of functors of a COMPLEX of coefficients strictly bounded \
  above by `0`, whose domain contains the complexes concentrated in degree `0`, so that the \
  statement specialises to the form at the heart (the two isomorphisms are not compared). The source states the identification on the unbounded `D(C)`; the module docstring \
  records what the unbounded case needs, namely the dévissage along the compact generators, the \
  total complex of the double complex of an unbounded complex not being `Lπ_!` of it"]
def derivedColimitPresheafRestrictionComplexNatIso (f : C' ⥤ C) (U : CosimplicialObject C')
    (hU : IsPointResolution U) (hfU : IsPointResolution (U ⋙ f)) :
    (strictlyLEZero (Cᵒᵖ ⥤ AddCommGrpCat.{u})).ι ⋙
        (Stacks.CategoryHomology.presheafRestriction.{u, u, u} f).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q ⋙ totalDerivedColimit C' AddCommGrpCat.{u} ≅
      (strictlyLEZero (Cᵒᵖ ⥤ AddCommGrpCat.{u})).ι ⋙
        DerivedCategory.Q ⋙ totalDerivedColimit C AddCommGrpCat.{u} :=
  NatIso.ofComponents
    (fun K =>
      haveI : CochainComplex.IsStrictlyLE K.obj 0 := K.property
      derivedColimitPresheafRestrictionComplexIso f U hU hfU K.obj)
    (fun {K L} φ => by
      have : CochainComplex.IsStrictlyLE K.obj 0 := K.property
      have : CochainComplex.IsStrictlyLE L.obj 0 := L.property
      exact derivedColimitPresheafRestrictionComplexIso_naturality f U hU hfU φ.hom)

end AbelianValued

end Stacks.ChaoticSite

end
