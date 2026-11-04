module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Representatives
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherenceAlongAnExactFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.LocalNature
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSiteComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.Functoriality

/-!
# Pseudo-coherence under an equivalence of ringed sites

Let `(C, O)` be a ringed site and let `e : C' ≌ C` be an equivalence of sites. Reindexing along
`e` is an equivalence between the sheaves of `O`-modules and the sheaves of modules over the
transported structure sheaf on `C'`. This file proves that a complex of `O`-modules is
`m`-pseudo-coherent (Stacks 08FT) exactly when its reindexing is, and that an object of the
derived category is `m`-pseudo-coherent exactly when a complex representing it is.

The local datum of pseudo-coherence is a strictly perfect complex mapping to the restriction of
the given complex, by a map inducing isomorphisms on cohomology in degrees `> m` and an
epimorphism in degree `m` (`AlgebraicGeometry.RingedSite.HasStrictlyPerfectApproximation`).

## Main results

* `Stacks.SheafOfModules.exists_strictlyPerfect_approximation_reindex_iff`: such approximations
  correspond under reindexing along an equivalence of sites.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_iff_isPseudoCoherentComplexFrom`: an object
  of `D(O)` is `m`-pseudo-coherent exactly when a complex representing it is.
* `AlgebraicGeometry.RingedSite.hasStrictlyPerfectApproximation_reindex_iff`: the local datum
  over an object of the reindexed ringed site is the local datum over its image.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_reindex_iff`: `m`-pseudo-coherence
  of a complex is invariant under an equivalence of ringed sites.

## Implementation notes

The covering families are transported by cover lifting: a covering sieve of `e.functor.obj U'`
pulls back along `e.functor` to a covering sieve of `U'`, and a member `g` of the pulled back
sieve has `e.functor.map g` factoring through a member of the original covering, so the
approximation over that member restricts to `e.functor.obj` of the source of `g`. On a slice the
reindexing of the restriction is the restriction of the reindexing on the nose
(`Stacks.SheafOfModules.over_reindex_eq`), so the slice statement is the global statement for
the localized equivalence `Stacks.SheafOfModules.overSiteEquivalence`.

## References

* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w d u v u₁ v₁ u₂ v₂

namespace Stacks.SheafOfModules

section Reindex

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'}
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  (R : Sheaf J RingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J' AddCommGrpCat.{w}] [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- An exact functor of sheaves of modules carrying the unit to the unit carries a strictly perfect
approximation in degrees `≥ m` of a complex `L` to one of the image of `L`. -/
private theorem exists_strictlyPerfect_approximation_map {D : Type*} [Category D]
    {K : GrothendieckTopology D} {S : Sheaf K RingCat.{w}}
    [HasSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {R : Sheaf J RingCat.{w}}
    (F : SheafOfModules.{w} R ⥤ SheafOfModules.{w} S) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (eU : F.obj (SheafOfModules.unit R) ≅ SheafOfModules.unit S)
    {L : CochainComplex (SheafOfModules.{w} R) ℤ} {L' : CochainComplex (SheafOfModules.{w} S) ℤ}
    (eL : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L ≅ L') {m : ℤ}
    (h : ∃ P : CochainComplex (SheafOfModules.{w} R) ℤ, IsStrictlyPerfect R P ∧
      ∃ α : P ⟶ L, (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
        Epi (HomologicalComplex.homologyMap α m)) :
    ∃ P : CochainComplex (SheafOfModules.{w} S) ℤ, IsStrictlyPerfect S P ∧
      ∃ α : P ⟶ L', (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
        Epi (HomologicalComplex.homologyMap α m) := by
  obtain ⟨P, hP, α, hiso, hepi⟩ := h
  have : F.PreservesHomology := Functor.preservesHomologyOfExact F
  exact ⟨_, SheafOfModules.isStrictlyPerfect_map F eU hP,
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map α ≫ eL.hom,
    fun j hj => AlgebraicGeometry.RingedSite.isIso_homologyMap_comp_iso _ eL j
      (AlgebraicGeometry.RingedSite.isIso_homologyMap_map F α j (hiso j hj)),
    AlgebraicGeometry.RingedSite.epi_homologyMap_comp_iso _ eL m
      (AlgebraicGeometry.RingedSite.epi_homologyMap_map F α m hepi)⟩

/-- **Strictly perfect approximations correspond under reindexing along an equivalence of
sites.** A complex `L` of `R`-modules receives a strictly perfect complex by a map inducing
isomorphisms on cohomology in degrees `> m` and an epimorphism in degree `m` exactly when its
reindexing along `e` does, over the transported sheaf of rings. -/
theorem exists_strictlyPerfect_approximation_reindex_iff
    (L : CochainComplex (SheafOfModules.{w} R) ℤ) (m : ℤ) :
    (∃ P : CochainComplex (SheafOfModules.{w} (reindexRing J' e R)) ℤ,
      IsStrictlyPerfect (reindexRing J' e R) P ∧
        ∃ α : P ⟶ ((reindexEquivalence.{w, w} (J' := J') e R).functor.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L,
          (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
            Epi (HomologicalComplex.homologyMap α m)) ↔
      ∃ P : CochainComplex (SheafOfModules.{w} R) ℤ, IsStrictlyPerfect R P ∧
        ∃ α : P ⟶ L, (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
          Epi (HomologicalComplex.homologyMap α m) := by
  let Φ := reindexEquivalence.{w, w} (J' := J') e R
  have : Φ.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : Φ.inverse.Additive := Functor.additive_of_preserves_binary_products _
  -- reindexing carries the unit module to the unit module on the nose
  let eU : Φ.functor.obj (SheafOfModules.unit R) ≅ SheafOfModules.unit (reindexRing J' e R) :=
    Iso.refl _
  exact ⟨exists_strictlyPerfect_approximation_map Φ.inverse
      (Φ.inverse.mapIso eU.symm ≪≫ (Φ.unitIso.app _).symm)
      ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).unitIso.app L).symm,
    exists_strictlyPerfect_approximation_map Φ.functor eU (Iso.refl _)⟩

end Reindex

end Stacks.SheafOfModules

namespace AlgebraicGeometry.RingedSite

open Stacks.SheafOfModules

section Representatives

variable (X : RingedSite.{u, v, w})
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : X.C, (SheafOfModules.overFunctor.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).Additive]
  [∀ U : X.C, PreservesFiniteLimits (SheafOfModules.overFunctor.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [∀ U : X.C, PreservesFiniteColimits (SheafOfModules.overFunctor.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- An object of `D(O)` is `m`-pseudo-coherent exactly when a complex representing it is
(Stacks 08FU (2) for one direction, the definition for the other). -/
theorem isPseudoCoherentFrom_iff_isPseudoCoherentComplexFrom
    {K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (e : DerivedCategory.Q.obj K ≅ E) (m : ℤ) :
    X.IsPseudoCoherentFrom E m ↔ X.IsPseudoCoherentComplexFrom K m :=
  ⟨fun h => X.isPseudoCoherentComplexFrom_of_iso_general E m h K e, fun h => ⟨K, h, ⟨e⟩⟩⟩

end Representatives

section Reindex

variable (X : RingedSite.{u, v, w}) {C' : Type u} [Category.{v} C'] (J' : GrothendieckTopology C')
  (e : C' ≌ X.C) [e.functor.IsContinuous J' X.J] [e.inverse.IsContinuous X.J J']
  [e.inverse.IsDenseSubsite X.J J']
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ V : C', HasSheafify (J'.over V) AddCommGrpCat.{w}]
  [∀ V : C', (J'.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **A strictly perfect approximation over an object of the reindexed ringed site** is one over
its image: the restriction of the reindexing to `V` is the reindexing, along the localized
equivalence, of the restriction to `e.functor.obj V`. -/
theorem hasStrictlyPerfectApproximation_reindex_iff
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (m : ℤ) (V : C') :
    (X.reindex J' e).HasStrictlyPerfectApproximation
        (((reindexEquivalence.{w, w} (J' := J') e
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).functor.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) m V ↔
      X.HasStrictlyPerfectApproximation K m (e.functor.obj V) :=
  exists_strictlyPerfect_approximation_reindex_iff (J' := J'.over V) (overSiteEquivalence e V)
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (e.functor.obj V))
    (X.restrictComplex K (e.functor.obj V)) m

/-- **`m`-pseudo-coherence of a complex is invariant under an equivalence of ringed sites.** A
complex of `O`-modules on `X` is `m`-pseudo-coherent exactly when its reindexing along an
equivalence of sites `e : C' ≌ X.C` is `m`-pseudo-coherent on the reindexed ringed site. -/
theorem isPseudoCoherentComplexFrom_reindex_iff
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (m : ℤ) :
    (X.reindex J' e).IsPseudoCoherentComplexFrom
        (((reindexEquivalence.{w, w} (J' := J') e
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).functor.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) m ↔
      X.IsPseudoCoherentComplexFrom K m := by
  constructor
  · intro h
    refine (X.isPseudoCoherentComplexFrom_iff K m).2 fun U => ?_
    obtain ⟨S', hS', hdata'⟩ := h (e.inverse.obj U)
    refine ⟨((Sieve.generate S').functorPullback e.inverse).arrows, ?_, ?_⟩
    · rw [Sieve.generate_sieve]
      exact e.inverse.cover_lift X.J J' hS'
    · rintro W g ⟨W', a, f', hf', -⟩
      exact X.hasStrictlyPerfectApproximation_of_hom K m
        ((e.counitIso.app W).inv ≫ e.functor.map a)
        ((hasStrictlyPerfectApproximation_reindex_iff X J' e K m W').1 (hdata' f' hf'))
  · intro h U'
    obtain ⟨S, hS, hdata⟩ := (X.isPseudoCoherentComplexFrom_iff K m).1 h (e.functor.obj U')
    refine ⟨((Sieve.generate S).functorPullback e.functor).arrows, ?_, ?_⟩
    · rw [Sieve.generate_sieve]
      exact e.functor.cover_lift J' X.J hS
    · rintro W' g ⟨W, a, f, hf, -⟩
      exact (hasStrictlyPerfectApproximation_reindex_iff X J' e K m W').2
        (X.hasStrictlyPerfectApproximation_of_hom K m a (hdata f hf))

end Reindex

end AlgebraicGeometry.RingedSite
