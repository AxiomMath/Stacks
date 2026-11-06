module

public import StacksFrontier.AlgebraicGeometry.Spaces.DualizingUniqueness.Assembly
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.ModelBiduality
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DualizingUniqueness.SpaceTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SliceDerivedBiduality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitFinitePresentationSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleTypesUnderEquivalence

/-!
# Uniqueness of dualizing complexes on an algebraic space

**Stacks 0E52.** Let `X` be a locally Noetherian algebraic space over a scheme `S`. If `K` and
`K'` are dualizing complexes on `X`, then `K' ≅ K ⊗^L_{𝒪_X} L` for some invertible object `L` of
`D(𝒪_X)`.

The proof is the source's, read on the equi-universe model of the small étale ringed site of
`X`, which carries the derived internal Hom and the derived tensor product of `D(𝒪_X)`. The
object `N = R𝓗om(K', K)` is invertible: on every étale chart `K'` is locally a shift of `K`,
because two dualizing complexes on a locally Noetherian scheme are
(`Stacks.Duality.exists_mem_derivedPullback_iso_shift_of_isDualizingComplex`), and
`R𝓗om(K, K) ≅ 𝒪_X`. Biduality (Stacks 0E51) gives `K' ≅ R𝓗om(N, K) ≅ K ⊗^L N⁻¹`.

## Main results

* `AlgebraicGeometry.RingedSite.nonempty_derivedSheafHom_self_iso_of_isIso_derivedBiduality`:
  biduality at the structure sheaf gives `R𝓗om(K, K) ≅ O`.
* `AlgebraicGeometry.Space.exists_isInvertible_tensor_iso_of_isIso_derivedBiduality`: the
  statement of Stacks 0E52 from biduality on the model at `𝒪` and at `K'`.

## References

* [Stacks Project, Tag 0E52](https://stacks.math.columbia.edu/tag/0E52)
* [Stacks Project, Tag 0E51](https://stacks.math.columbia.edu/tag/0E51)
* [Stacks Project, Tag 0A7F](https://stacks.math.columbia.edu/tag/0A7F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

universe u

namespace Stacks.SheafOfModules

/-- Weak sheafification of abelian presheaves on a small site, from the project's global
instance, made a local instance of high priority so that the lemmas below do not pick up the
section variable `[HasSheafify J AddCommGrpCat.{u}]`. -/
private abbrev hasWeakSheafifyAddCommGrpCat {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) : HasWeakSheafify J AddCommGrpCat.{u} :=
  inferInstance

attribute [local instance high] hasWeakSheafifyAddCommGrpCat

attribute [-instance] instHasWeakSheafifyOfHasSheafify

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [Limits.HasBinaryProducts C] [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasSheafify J AddCommGrpCat.{u}] [Limits.HasBinaryProducts C]
  [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The free sheaf of modules on the empty index type is zero. -/
theorem isZero_free_pEmpty :
    Limits.IsZero (_root_.SheafOfModules.free (R := R) PEmpty.{u + 1}) := by
  rw [Limits.IsZero.iff_id_eq_zero]
  exact (_root_.SheafOfModules.freeHomEquiv _).injective (funext fun x => x.elim)

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [Limits.HasBinaryProducts C] [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{u}] in
/-- **A zero sheaf of modules is of finite presentation**: on every slice it is the cokernel of
the empty presentation. -/
theorem isFinitePresentation_of_isZero {M : _root_.SheafOfModules.{u} R} (hM : Limits.IsZero M) :
    M.IsFinitePresentation := by
  have hz : ∀ Y : C, Limits.IsZero (M.over Y) := fun Y =>
    Functor.map_isZero (_root_.SheafOfModules.overFunctor R Y) hM
  let P : ∀ Y : C, (M.over Y).Presentation := fun Y =>
    { generators :=
        { I := PEmpty.{u + 1}
          s := fun x => x.elim
          epi := ⟨fun g h _ => (hz Y).eq_of_src g h⟩ }
      relations :=
        { I := PEmpty.{u + 1}
          s := fun x => x.elim
          epi := ⟨fun g h _ => (Limits.IsZero.of_mono (Limits.kernel.ι _)
            isZero_free_pEmpty).eq_of_src g h⟩ } }
  have hcov : ∀ Y : C, Sieve.ofObjects (id : C → C) Y ∈ J Y := fun Y => by
    refine GrothendieckTopology.covering_of_eq_top J ?_
    rw [Sieve.ext_iff]
    intro _ f
    simp [Sieve.top_apply]
  let q : M.QuasicoherentData :=
    { I := C
      X := id
      coversTop := hcov
      presentation := P }
  exact ⟨q, ⟨fun Y => ⟨⟨inferInstanceAs (Finite PEmpty.{u + 1})⟩,
    ⟨inferInstanceAs (Finite PEmpty.{u + 1})⟩⟩⟩⟩

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [Limits.HasBinaryProducts C] in
/-- **The cohomology sheaves of the structure sheaf in degree zero are of finite presentation**:
`H^0` is the structure sheaf and the others vanish. -/
theorem isFinitePresentation_homology_singleFunctor_unit
    [HasDerivedCategory (_root_.SheafOfModules.{u} R)] (n : ℤ) :
    ((DerivedCategory.homologyFunctor _ n).obj ((DerivedCategory.singleFunctor _ 0).obj
      (_root_.SheafOfModules.unit R))).IsFinitePresentation := by
  by_cases hn : n = 0
  · subst hn
    exact Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _).symm
      (Stacks.SheafOfModules.Site.unit_isFinitePresentation (R := R))
  · refine isFinitePresentation_of_isZero ?_
    rcases lt_or_gt_of_ne hn with h | h
    · exact DerivedCategory.isZero_of_isGE _ 0 n h
    · exact DerivedCategory.isZero_of_isLE _ 0 n h

end Stacks.SheafOfModules

namespace AlgebraicGeometry.RingedSite

variable (Y : RingedSite.{u, u, u})
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]

/-- **Biduality at the structure sheaf gives `R𝓗om(K, K) ≅ O`.** If the biduality morphism
`O ⟶ R𝓗om(R𝓗om(O, K), K)` is an isomorphism, then so is `R𝓗om(K, K) ≅ O`, through
`R𝓗om(O, K) ≅ K` (Stacks 08JD). -/
theorem nonempty_derivedSheafHom_self_iso_of_isIso_derivedBiduality
    (K : @DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) _ _
      (HasDerivedCategory.standard _))
    (h : IsIso (derivedBiduality Y K
      ((@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard _) 0).obj
        (SheafOfModules.unit _)))) :
    Nonempty (((@derivedSheafHomBifunctor Y (HasDerivedCategory.standard _)).obj (op K)).obj K ≅
      (@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard _) 0).obj
        (SheafOfModules.unit _)) := by
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  exact ⟨((derivedSheafHomBifunctor Y).mapIso (derivedStructureSheafHomIso Y K).op).app K ≪≫
    (@asIso _ _ _ _ (derivedBiduality Y K _) h).symm⟩

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **Stacks 0E52 from biduality on the model.** Let `X` be a locally Noetherian algebraic space
and `K`, `K'` dualizing complexes on `X`. If the biduality morphisms of `R𝓗om(-, K)` on the
equi-universe model are isomorphisms at the structure sheaf and at `K'`, then
`K' ≅ K ⊗^L_{𝒪_X} L` for an invertible object `L` of `D(𝒪_X)`. -/
theorem exists_isInvertible_tensor_iso_of_isIso_derivedBiduality
    (hN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (K K' : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (hK : IsDualizingComplexOnSpace B S hS X.1 X.2 hN K)
    (hK' : IsDualizingComplexOnSpace B S hS X.1 X.2 hN K')
    (hO : IsIso (RingedSite.derivedBiduality (smallEtaleModelRingedSite B S hS X.1 X.2)
      ((modelDerivedEquivalence B S hS X.1 X.2).functor.obj K.obj)
      ((@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard _) 0).obj
        (SheafOfModules.unit _))))
    (hK'bid : IsIso (RingedSite.derivedBiduality (smallEtaleModelRingedSite B S hS X.1 X.2)
      ((modelDerivedEquivalence B S hS X.1 X.2).functor.obj K.obj)
      ((modelDerivedEquivalence B S hS X.1 X.2).functor.obj K'.obj))) :
    letI := derivedMonoidalOfModel B S hS X.1 X.2
    ∃ L, IsInvertible L ∧ Nonempty (K'.obj ≅ K.obj ⊗ L) :=
  exists_isInvertible_tensor_iso_of_model B S hS X.1 X.2 K.obj K'.obj
    (exists_isInvertibleObject_tensor_iso_of_dualizing_of_biduality B S hS X hN K K' hK hK'
      (RingedSite.nonempty_derivedSheafHom_self_iso_of_isIso_derivedBiduality
        (smallEtaleModelRingedSite B S hS X.1 X.2) _ hO)
      ⟨@asIso _ _ _ _ (RingedSite.derivedBiduality (smallEtaleModelRingedSite B S hS X.1 X.2) _ _)
        hK'bid⟩)

/-- **Stacks 0E52.** Let `S` be a scheme and `X` a locally Noetherian algebraic space over `S`. If
`K` and `K'` are dualizing complexes on `X` (Stacks 0E4Z), then `K'` is isomorphic to
`K ⊗^L_{𝒪_X} L` for some invertible object `L` of `D(𝒪_X)`.

`D(𝒪_X)` is the derived category of the `𝒪_X`-modules on the small étale site of `X`, and
`⊗^L_{𝒪_X}` with its unit `𝒪_X` is `AlgebraicGeometry.Space.derivedMonoidalOfModel`, the derived
tensor product of Stacks 0FPT read on the equi-universe model of the small étale ringed site.
The proof is the source's: `R𝓗om(K', K)` is invertible because affine locally `K'` is a shift
of `K` (Stacks 0A7F, 0ATP) and `R𝓗om(K, K) = 𝒪_X`, and `K' ≅ R𝓗om(R𝓗om(K', K), K)` by
biduality (Stacks 0E51). -/
@[stacks 0E52]
theorem exists_isInvertible_tensor_iso_of_isDualizingComplexOnSpace
    (hN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (K K' : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (hK : IsDualizingComplexOnSpace B S hS X.1 X.2 hN K)
    (hK' : IsDualizingComplexOnSpace B S hS X.1 X.2 hN K') :
    letI := derivedMonoidalOfModel B S hS X.1 X.2
    ∃ L, IsInvertible L ∧ Nonempty (K'.obj ≅ K.obj ⊗ L) :=
  exists_isInvertible_tensor_iso_of_isIso_derivedBiduality B S hS X hN K K' hK hK'
    (isIso_derivedBiduality_model_unit B S hS X.1 X.2 hN K hK)
    (isIso_derivedBiduality_model_of_isDualizingComplexOnSpace B S hS X.1 X.2 hN K K' hK hK')

end AlgebraicGeometry.Space
