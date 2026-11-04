module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.SiteEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessAlongAnExactFunctor

/-!
# Perfectness under reindexing along an equivalence of sites

Let `(C, O)` be a ringed site and let `e : C' ≌ C` be an equivalence of sites. Reindexing along
`e` is an equivalence between the sheaves of `O`-modules and the sheaves of modules over the
transported structure sheaf on `C'`. This file proves that a complex of `O`-modules is perfect
(Stacks 08G5) exactly when its reindexing is. It is the perfect counterpart of
`AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_reindex_iff`, and follows the same
argument with strictly perfect local models in place of strictly perfect approximations.

## Main results

* `Stacks.SheafOfModules.exists_strictlyPerfect_quasiIso_reindex_iff`: strictly perfect local
  models correspond under reindexing along an equivalence of sites.
* `AlgebraicGeometry.RingedSite.hasStrictlyPerfectQuasiIso_reindex_iff`: the local model over
  an object of the reindexed ringed site is the local model over its image.
* `AlgebraicGeometry.RingedSite.isPerfectComplex_reindex_iff`: perfectness of complexes is
  invariant under an equivalence of ringed sites.
* `AlgebraicGeometry.RingedSite.isPerfectComplex_of_iso`: perfectness of complexes is invariant
  under isomorphism.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u v u₁ v₁ u₂ v₂

namespace Stacks.SheafOfModules

section Reindex

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'}
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  (R : Sheaf J RingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J' AddCommGrpCat.{w}] [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- An exact functor of sheaves of modules carrying the unit to the unit carries a strictly perfect
complex with a quasi-isomorphism to a complex `L` to one with a quasi-isomorphism to the image of
`L`. -/
private theorem exists_strictlyPerfect_quasiIso_map {D : Type*} [Category D]
    {K : GrothendieckTopology D} {S : Sheaf K RingCat.{w}}
    [HasSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {R : Sheaf J RingCat.{w}}
    (F : SheafOfModules.{w} R ⥤ SheafOfModules.{w} S) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (eU : F.obj (SheafOfModules.unit R) ≅ SheafOfModules.unit S)
    {L : CochainComplex (SheafOfModules.{w} R) ℤ} {L' : CochainComplex (SheafOfModules.{w} S) ℤ}
    (eL : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L ≅ L')
    (h : ∃ P : CochainComplex (SheafOfModules.{w} R) ℤ, IsStrictlyPerfect R P ∧
      ∃ q : P ⟶ L, QuasiIso q) :
    ∃ P : CochainComplex (SheafOfModules.{w} S) ℤ, IsStrictlyPerfect S P ∧
      ∃ q : P ⟶ L', QuasiIso q := by
  obtain ⟨P, hP, q, hq⟩ := h
  have : F.PreservesHomology := Functor.preservesHomologyOfExact F
  exact ⟨_, SheafOfModules.isStrictlyPerfect_map F eU hP,
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map q ≫ eL.hom, inferInstance⟩

/-- **Strictly perfect local models correspond under reindexing along an equivalence of sites.**
A complex `L` of `R`-modules receives a quasi-isomorphism from a strictly perfect complex exactly
when its reindexing along `e` does, over the transported sheaf of rings. -/
theorem exists_strictlyPerfect_quasiIso_reindex_iff
    (L : CochainComplex (SheafOfModules.{w} R) ℤ) :
    (∃ P : CochainComplex (SheafOfModules.{w} (reindexRing J' e R)) ℤ,
      IsStrictlyPerfect (reindexRing J' e R) P ∧
        ∃ q : P ⟶ ((reindexEquivalence.{w, w} (J' := J') e R).functor.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L, QuasiIso q) ↔
      ∃ P : CochainComplex (SheafOfModules.{w} R) ℤ, IsStrictlyPerfect R P ∧
        ∃ q : P ⟶ L, QuasiIso q := by
  let Φ := reindexEquivalence.{w, w} (J' := J') e R
  have : Φ.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : Φ.inverse.Additive := Functor.additive_of_preserves_binary_products _
  -- reindexing carries the unit module to the unit module on the nose
  let eU : Φ.functor.obj (SheafOfModules.unit R) ≅ SheafOfModules.unit (reindexRing J' e R) :=
    Iso.refl _
  constructor
  · exact exists_strictlyPerfect_quasiIso_map Φ.inverse
      (Φ.inverse.mapIso eU.symm ≪≫ (Φ.unitIso.app _).symm)
      ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).unitIso.app L).symm
  · exact exists_strictlyPerfect_quasiIso_map Φ.functor eU (Iso.refl _)

end Reindex

end Stacks.SheafOfModules

namespace AlgebraicGeometry.RingedSite

open Stacks.SheafOfModules

section Iso

variable (X : RingedSite.{u, v, w})
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Perfectness of a complex is invariant under isomorphism**: a quasi-isomorphism from a
strictly perfect complex to the restriction of one complex, followed by the restriction of an
isomorphism, is one to the restriction of the other. -/
theorem isPerfectComplex_of_iso
    {E E' : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eE : E ≅ E') (hE : X.IsPerfectComplex E) : X.IsPerfectComplex E' := by
  intro U
  obtain ⟨S, hS, hdata⟩ := hE U
  refine ⟨S, hS, fun V f hf => ?_⟩
  obtain ⟨P, hP, q, hq⟩ := hdata f hf
  exact ⟨P, hP, q ≫ ((SheafOfModules.overFunctor.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapHomologicalComplex
      (ComplexShape.up ℤ)).map eE.hom, inferInstance⟩

end Iso

section Reindex

variable (X : RingedSite.{u, v, w}) {C' : Type u} [Category.{v} C'] (J' : GrothendieckTopology C')
  (e : C' ≌ X.C) [e.functor.IsContinuous J' X.J] [e.inverse.IsContinuous X.J J']
  [e.inverse.IsDenseSubsite X.J J']
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ V : C', HasSheafify (J'.over V) AddCommGrpCat.{w}]
  [∀ V : C', (J'.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **A strictly perfect local model over an object of the reindexed ringed site** is one over
its image: the restriction of the reindexing to `V` is the reindexing, along the localized
equivalence, of the restriction to `e.functor.obj V`. -/
theorem hasStrictlyPerfectQuasiIso_reindex_iff
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (V : C') :
    (X.reindex J' e).HasStrictlyPerfectQuasiIso
        (((reindexEquivalence.{w, w} (J' := J') e
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).functor.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) V ↔
      X.HasStrictlyPerfectQuasiIso K (e.functor.obj V) :=
  exists_strictlyPerfect_quasiIso_reindex_iff (J' := J'.over V) (overSiteEquivalence e V)
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (e.functor.obj V))
    (X.restrictComplex K (e.functor.obj V))

/-- **Perfectness of a complex is invariant under an equivalence of ringed sites** (Stacks 08G5).
A complex of `O`-modules on `X` is perfect exactly when its reindexing along an equivalence of
sites `e : C' ≌ X.C` is perfect on the reindexed ringed site. -/
theorem isPerfectComplex_reindex_iff
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (X.reindex J' e).IsPerfectComplex
        (((reindexEquivalence.{w, w} (J' := J') e
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).functor.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ↔
      X.IsPerfectComplex K := by
  constructor
  · intro h U
    obtain ⟨S', hS', hdata'⟩ := h (e.inverse.obj U)
    refine ⟨((Sieve.generate S').functorPullback e.inverse).arrows, ?_, ?_⟩
    · rw [Sieve.generate_sieve]
      exact e.inverse.cover_lift X.J J' hS'
    · rintro W g ⟨W', a, f', hf', -⟩
      exact X.hasStrictlyPerfectQuasiIso_of_hom K
        ((e.counitIso.app W).inv ≫ e.functor.map a)
        ((hasStrictlyPerfectQuasiIso_reindex_iff X J' e K W').1 (hdata' f' hf'))
  · intro h U'
    obtain ⟨S, hS, hdata⟩ := h (e.functor.obj U')
    refine ⟨((Sieve.generate S).functorPullback e.functor).arrows, ?_, ?_⟩
    · rw [Sieve.generate_sieve]
      exact e.functor.cover_lift J' X.J hS
    · rintro W' g ⟨W, a, f, hf, -⟩
      exact (hasStrictlyPerfectQuasiIso_reindex_iff X J' e K W').2
        (X.hasStrictlyPerfectQuasiIso_of_hom K a (hdata f hf))

end Reindex

end AlgebraicGeometry.RingedSite
