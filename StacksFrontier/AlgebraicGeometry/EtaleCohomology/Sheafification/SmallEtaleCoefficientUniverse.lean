module
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCohomologyFilteredColimitsTypeU
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftInjective
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftInjectiveSmallSite

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleLocallyBijective
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelianSheaves
public import StacksFrontier.CategoryTheory.Sites.LocallyBijectiveUniverse
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftCohomology

/-!
# Étale cohomology does not depend on the coefficient universe

Let `X : Scheme.{u}`. Abelian sheaves on the small étale site of `X` can be taken with sections in
`AddCommGrpCat.{u}`, the universe of the morphisms of the site, or in any larger universe; the
universe lift `F ↦ F ⋙ uliftFunctor` passes from the first to the second. This file shows that
the universe lift does not change étale cohomology:

  `H ^ n (X_étale, F) ≃+ H ^ n (X_étale, F ⋙ uliftFunctor)`

for every abelian sheaf `F` with sections in `Type u` and every coefficient universe
`max (u + 1) v`.

## Main results

* `AlgebraicGeometry.Scheme.preservesInjectiveObjects_uliftSheafFunctor_affineEtale` and
  `AlgebraicGeometry.Scheme.preservesInjectiveObjects_uliftSheafFunctor_smallEtale`: the universe
  lift carries injective abelian sheaves to injective abelian sheaves, on the affine étale site
  and on the small étale site.
* `AlgebraicGeometry.Scheme.smallEtaleSheafHUliftAddEquiv`: **the comparison of cohomology**, at
  arbitrary `Ext` universes on the two sides.
* `AlgebraicGeometry.Scheme.smallEtaleConstantSheafHAddEquiv`: the same for constant sheaves on
  two isomorphic groups living in the two coefficient universes.

## Implementation notes

The comparison is `Stacks.Sheaves.UniverseLift.sheafHUliftAddEquiv`, whose two inputs are
enough injectives in `Sheaf X.smallEtaleTopology AddCommGrpCat.{u}`, which is Mathlib's
Grothendieck abelian category, and preservation of injective objects by the universe lift.

The second is where the size of the site enters. The small étale site is not essentially small at
`u` — `∐ i : I, X` is étale over `X` for every `I : Type u` — so the small-site argument
`_root_.Stacks.Cohomology.CoefficientLowering.sheafCompose_preservesInjectiveObjects` does not
apply to it directly. It applies to a small model of the affine étale site, which is essentially
small at `u`, and the statement is carried from there to the affine étale site and then to the
small étale site by
`Stacks.Sheaves.UniverseLift.preservesInjectiveObjects_uliftSheafFunctor_of_isEquivalence`, along
the two dense-subsite equivalences of sheaf categories: the small model's induced topology, and
Mathlib's `AlgebraicGeometry.Scheme.AffineEtale.Spec`. Both are equivalences in either coefficient
universe, the first by the comparison lemma for a cover-dense functor and the second by
`CategoryTheory.Functor.isEquivalence_of_isOneHypercoverDense`.

## References

* [Stacks Project, Tag 03OK](https://stacks.math.columbia.edu/tag/03OK): étale cohomology as
  cohomology on the small étale site.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open Stacks.Sheaves.UniverseLift

universe w₁ w₂ s v u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- **On the affine étale site the universe lift preserves injective abelian sheaves.** The site is
essentially small at `u`; on a small model, with the induced topology, the statement is
`_root_.Stacks.Cohomology.CoefficientLowering.sheafCompose_preservesInjectiveObjects`, and
restriction along the small model is an equivalence of sheaf categories in both coefficient
universes. -/
theorem preservesInjectiveObjects_uliftSheafFunctor_affineEtale :
    (uliftSheafFunctor.{s, u} (AffineEtale.topology X)).PreservesInjectiveObjects := by
  let e := equivSmallModel.{u} X.AffineEtale
  let J₀ := e.inverse.inducedTopology (AffineEtale.topology X)
  let : EssentiallySmall.{max u s} (SmallModel.{u} X.AffineEtale) :=
    essentiallySmall_lift.{s, u} _
  let : HasSheafify J₀ AddCommGrpCat.{max u s} :=
    hasSheafify_addCommGrpCat_of_essentiallySmall.{max u s} J₀
  have : AddCommGrpCat.uliftFunctor.{s, u}.PreservesInjectiveObjects :=
    preservesInjectiveObjects_addCommGrpCat_uliftFunctor.{s, u}
  have h : (uliftSheafFunctor.{s, u} J₀).PreservesInjectiveObjects :=
    _root_.Stacks.Cohomology.CoefficientLowering.sheafCompose_preservesInjectiveObjects J₀
      AddCommGrpCat.uliftFunctor.{s, u}
  have : (e.inverse.sheafPushforwardContinuous AddCommGrpCat.{max u s} J₀
      (AffineEtale.topology X)).IsEquivalence :=
    have : ∀ Y, HasLimitsOfShape (StructuredArrow Y e.inverse.op) AddCommGrpCat.{max u s} :=
      fun _ ↦ inferInstance
    inferInstance
  exact preservesInjectiveObjects_uliftSheafFunctor_of_isEquivalence.{s, u} e.inverse J₀
    (AffineEtale.topology X) h

/-- **On the small étale site the universe lift preserves injective abelian sheaves.** This is
`AlgebraicGeometry.Scheme.preservesInjectiveObjects_uliftSheafFunctor_affineEtale` carried along
the dense subsite of affine schemes étale over `X`, whose restriction of sheaves is an
equivalence in both coefficient universes. -/
theorem preservesInjectiveObjects_uliftSheafFunctor_smallEtale :
    (uliftSheafFunctor.{s, u} X.smallEtaleTopology).PreservesInjectiveObjects := by
  have : ((AffineEtale.Spec X).sheafPushforwardContinuous AddCommGrpCat.{max u s}
      (AffineEtale.topology X) X.smallEtaleTopology).IsEquivalence :=
    Functor.isEquivalence_of_isOneHypercoverDense.{u} _ _ _ _
  exact preservesInjectiveObjects_uliftSheafFunctor_of_isEquivalence.{s, u} (AffineEtale.Spec X)
    (AffineEtale.topology X) X.smallEtaleTopology
    (preservesInjectiveObjects_uliftSheafFunctor_affineEtale X)

/-- **Étale cohomology does not depend on the coefficient universe.** For an abelian sheaf `F` on
the small étale site of `X : Scheme.{u}` with sections in `Type u`,

  `H ^ n (X_étale, F) ≃+ H ^ n (X_étale, F ⋙ uliftFunctor)`,

the right-hand side computed with coefficients in `AddCommGrpCat.{max (u + 1) v}`. The two `Ext`
universes are arbitrary. -/
def smallEtaleSheafHUliftAddEquiv
    [HasExt.{w₁} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [HasExt.{w₂} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H.{w₁} F n ≃+
      Sheaf.H.{w₂} ((uliftSheafFunctor.{max (u + 1) v, u} X.smallEtaleTopology).obj F) n :=
  letI : HasSheafify X.smallEtaleTopology AddCommGrpCat.{max u (max (u + 1) v)} :=
    hasSheafify_smallEtaleTopology.{u, v} X
  letI : X.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{max u (max (u + 1) v)} :=
    wEqualsLocallyBijective_smallEtaleTopology.{u, v} X
  letI : HasExt.{w₂} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u (max (u + 1) v)}) :=
    ‹HasExt.{w₂} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})›
  have : (uliftSheafFunctor.{max (u + 1) v, u} X.smallEtaleTopology).PreservesInjectiveObjects :=
    preservesInjectiveObjects_uliftSheafFunctor_smallEtale X
  sheafHUliftAddEquiv.{w₁, w₂, max (u + 1) v, u} X.smallEtaleTopology F n

/-- **`smallEtaleSheafHUliftAddEquiv` is natural in the sheaf**: it intertwines `H ^ n` of a
morphism with `H ^ n` of its universe lift. -/
theorem smallEtaleSheafHUliftAddEquiv_naturality
    [HasExt.{w₁} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [HasExt.{w₂} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (ψ : F ⟶ G) (n : ℕ)
    (x : Sheaf.H.{w₁} F n) :
    smallEtaleSheafHUliftAddEquiv.{w₁, w₂, v} X G n (Sheaf.H.map ψ n x) =
      Sheaf.H.map ((uliftSheafFunctor.{max (u + 1) v, u} X.smallEtaleTopology).map ψ) n
        (smallEtaleSheafHUliftAddEquiv.{w₁, w₂, v} X F n x) :=
  let : HasSheafify X.smallEtaleTopology AddCommGrpCat.{max u (max (u + 1) v)} :=
    hasSheafify_smallEtaleTopology.{u, v} X
  let : X.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{max u (max (u + 1) v)} :=
    wEqualsLocallyBijective_smallEtaleTopology.{u, v} X
  let : HasExt.{w₂} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u (max (u + 1) v)}) :=
    ‹HasExt.{w₂} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})›
  have : (uliftSheafFunctor.{max (u + 1) v, u} X.smallEtaleTopology).PreservesInjectiveObjects :=
    preservesInjectiveObjects_uliftSheafFunctor_smallEtale X
  sheafHUliftAddEquiv_naturality X.smallEtaleTopology ψ n x

/-- **Étale cohomology with constant coefficients does not depend on the coefficient universe.**
For abelian groups `M₀ : AddCommGrpCat.{u}` and `M : AddCommGrpCat.{max (u + 1) v}` with
`M₀ ≃+ M`,

  `H ^ n (X_étale, M₀) ≃+ H ^ n (X_étale, M)`,

the two constant sheaves being taken with coefficients in their own universes. The two `Ext`
universes are arbitrary.

This is `AlgebraicGeometry.Scheme.smallEtaleSheafHUliftAddEquiv` at the constant sheaf `M₀`,
followed by `H ^ n` of the identification of the universe lift of a constant sheaf with the
constant sheaf on the universe lift of its value
(`Stacks.Sheaves.UniverseLift.uliftSheafFunctorConstantSheafIso`) and of that value with `M`. -/
def smallEtaleConstantSheafHAddEquiv
    [HasExt.{w₁} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [HasExt.{w₂} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    {M₀ : AddCommGrpCat.{u}} {M : AddCommGrpCat.{max (u + 1) v}} (e : M₀ ≃+ M) (n : ℕ) :
    Sheaf.H.{w₁} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj M₀) n ≃+
      Sheaf.H.{w₂} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj M) n :=
  letI : HasSheafify X.smallEtaleTopology AddCommGrpCat.{max u (max (u + 1) v)} :=
    hasSheafify_smallEtaleTopology.{u, v} X
  letI : X.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{max u (max (u + 1) v)} :=
    wEqualsLocallyBijective_smallEtaleTopology.{u, v} X
  (smallEtaleSheafHUliftAddEquiv.{w₁, w₂, v} X _ n).trans
    ((extFunctorObj.{w₂} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
        (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ))) n).mapIso
      (uliftSheafFunctorConstantSheafIso.{max (u + 1) v, u} X.smallEtaleTopology M₀ ≪≫
        (constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).mapIso
          (AddEquiv.ulift.trans e).toAddCommGrpIso)).addCommGroupIsoToAddEquiv

end AlgebraicGeometry.Scheme

end
