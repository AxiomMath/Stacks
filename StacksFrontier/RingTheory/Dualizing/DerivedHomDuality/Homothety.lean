module

public import StacksFrontier.RingTheory.Dualizing.Biduality
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.HomothetyOverRing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Canonical biduality for a dualizing complex

The biduality criterion `Dualizing.isIso_dualizingBidualityMor_of_truncLE_pseudoCoherent` of
[stacks 0A7C] reduces invertibility of the canonical morphism `K ⟶ RHom_A(RHom_A(K, ω), ω)` to
four hypotheses, all read at the preimages of `ω` and `K` under the scalar equivalence out of
which the adjunction of [stacks 0A63] is built: invertibility of the derived homothety
`A ⟶ RHom_A(ω, ω)`, finite injective dimension of `ω`, finite Tor amplitude of
`RHom_A(ω, ω)`, and pseudo-coherence of every truncation of `K`. This file discharges all four
from the dualizing hypothesis of [stacks 0A7B] together with finiteness of the cohomology of
`K`, so that the canonical biduality morphism is unconditionally an isomorphism on objects with
finite cohomology.

The homothety hypothesis is
`Dualizing.isIso_derivedHomothety_of_restrictScalars_isDualizingComplex` of
  `DerivedHomothety/HomothetyOverRing.lean`, applied to `ULift.ringEquiv`; the inverse of the
scalar equivalence *is* restriction of scalars along it, by `rfl`. Finite injective dimension
transports because restriction of scalars along a ring isomorphism is an exact equivalence
preserving injective objects. The Tor-amplitude hypothesis is free once the homothety is
invertible: `RHom_A(ω, ω)` is then the tensor unit, so tensoring it with a module placed in degree
zero returns that module in degree zero, and the amplitude is `[0, 0]`. Pseudo-coherence of the
truncations is finiteness of their cohomology (Tag 064Q over a Noetherian ring), which the
truncation triangle reduces to finiteness of the cohomology of `K` itself, transported along
restriction of scalars.

## Main definitions

* `Dualizing.uliftRestrict` — restriction of scalars along `ULift A ≃+* A`, the inverse of the
  scalar equivalence of [stacks 0A63].
* `Dualizing.derivedHomSelfIsoUnit` — the identification of `RHom_A(ω, ω)` with the tensor unit
  for a dualizing complex `ω`.
* `Dualizing.uliftRestrictHomologyIso` — restriction of scalars commutes with the homology
  functors on derived categories.

## Main results

* `Dualizing.isIso_derivedHomothety_ulift_of_isDualizingComplex`,
  `Dualizing.hasFiniteInjectiveDimension_scalarPreimage`,
  `Dualizing.torAmplitude_derivedHomSelf` and
  `Dualizing.isPseudoCoherent_truncLE_scalarPreimage` — the four hypotheses of the criterion.
* `Dualizing.isIso_dualizingBidualityMor_of_isDualizingComplex` — biduality with only
  pseudo-coherence of the argument left as a hypothesis.
* `Dualizing.isIso_dualizingBidualityMor_of_finiteCohomology` — **canonical biduality**: for `ω`
  a dualizing complex over a Noetherian ring and `K` with finite cohomology in every degree,
  `K ⟶ RHom_A(RHom_A(K, ω), ω)` is an isomorphism.
* `Dualizing.finite_homology_truncLEObj` and `Dualizing.isPseudoCoherent_truncLEObj` — the
  truncations of an object with finite cohomology over a Noetherian ring are pseudo-coherent.

## Implementation notes

No `@[stacks 0A7C]` attribute is placed here.
`Dualizing.isIso_dualizingBidualityMor_of_finiteCohomology` is the morphism-level content of one
of the assertions of that tag (`canonical biduality`) but is not stated as the natural
isomorphism the tag asserts, so an attribute here would wrongly mark the whole tag as formalized.

## References

* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 064Q](https://stacks.math.columbia.edu/tag/064Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex

namespace Dualizing

open StacksDraft.DerivedHom

universe u

/-! ### The hypotheses of the biduality criterion -/

section Final

universe v

attribute [local instance 5000] HasDerivedCategory.standard

variable (A : Type u) [CommRing A]

/-- Restriction of scalars along `ULift A ≃+* A`. This is the inverse of the scalar equivalence
out of which `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing` is built, by `rfl`. -/
abbrev uliftRestrict : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} (ULift.{v} A) :=
  ModuleCat.restrictScalars.{max u v} (ULift.ringEquiv : ULift.{v} A ≃+* A).toRingHom

/-- **The derived homothety of a dualizing complex is invertible.** This is the hypothesis
`hone` of `Dualizing.isIso_dualizingBidualityMor_of_ulift`:
`Dualizing.isIso_derivedHomothety_of_restrictScalars_isDualizingComplex` at the scalar
isomorphism `ULift A ≃+* A`, whose restriction of scalars is the inverse of the scalar
equivalence. -/
theorem isIso_derivedHomothety_ulift_of_isDualizingComplex [IsNoetherianRing A]
    (ω : DerivedCategory (ModuleCat.{max u v} A)) (hω : IsDualizingComplex ω) :
    IsIso (derivedHomothety
      (derivedHomAdjunctionULift.{u, v, max u v + 1} (R := A)).toDerivedHomAdjunction
      (DerivedCategory.Q.obj (𝟙_ (Model.Complex (ULift.{v} A))))
      (derivedHomAdjunctionULift.{u, v, max u v + 1} (R := A)).tensorUnitLeft
      ((derivedScalarEquivalence.{u, v} A).inverse.obj ω)) :=
  isIso_derivedHomothety_of_restrictScalars_isDualizingComplex
    (ULift.ringEquiv : ULift.{v} A ≃+* A)
    (derivedHomAdjunctionULift.{u, v, max u v + 1} (R := A)) ω hω

/-- **Injective amplitude transports to the lifted scalars.** Restriction of scalars along
`ULift A ≃+* A` is an exact equivalence preserving injective objects, so it carries a bounded
complex of injectives representing `ω` to one representing the scalar preimage of `ω`. -/
theorem hasInjectiveAmplitude_scalarPreimage (ω : DerivedCategory (ModuleCat.{max u v} A))
    (a b : ℤ) (hω : StacksDraft.InjectiveDimension.HasInjectiveAmplitude ω a b) :
    StacksDraft.InjectiveDimension.HasInjectiveAmplitude
      ((derivedScalarEquivalence.{u, v} A).inverse.obj ω) a b := by
  obtain ⟨I, hge, hle, hinj, ⟨eI⟩⟩ := hω
  have hF : (uliftRestrict.{u, v} A).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
      (ULift.ringEquiv : ULift.{v} A ≃+* A)
  refine ⟨((uliftRestrict.{u, v} A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I,
    isStrictlyGE_mapHomologicalComplex (uliftRestrict.{u, v} A) I a hge,
    isStrictlyLE_mapHomologicalComplex (uliftRestrict.{u, v} A) I b hle,
    fun i => (uliftRestrict.{u, v} A).injective_obj_of_injective (hinj i), ⟨?_⟩⟩
  exact (uliftRestrict.{u, v} A).mapDerivedCategory.mapIso eI ≪≫
    (Functor.mapDerivedCategoryFactors (uliftRestrict.{u, v} A)).app I

/-- **Finite injective dimension transports to the lifted scalars.** This is the hypothesis
`hω` of `Dualizing.isIso_dualizingBidualityMor_of_truncLE_pseudoCoherent`. -/
theorem hasFiniteInjectiveDimension_scalarPreimage
    (ω : DerivedCategory (ModuleCat.{max u v} A))
    (hω : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension ω) :
    StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension
      ((derivedScalarEquivalence.{u, v} A).inverse.obj ω) := by
  obtain ⟨a, b, hamp⟩ := hω
  exact ⟨a, b, hasInjectiveAmplitude_scalarPreimage.{u, v} A ω a b hamp⟩

/-- **Derived Hom from a dualizing complex to itself is the tensor unit.** This is the content
of the homothety condition of [stacks 0A7B], read at the model-level adjunction over the lifted
ring. -/
def derivedHomSelfIsoUnit [IsNoetherianRing A]
    (ω : DerivedCategory (ModuleCat.{max u v} A)) (hω : IsDualizingComplex ω) :
    DerivedCategory.Q.obj (𝟙_ (Model.Complex (ULift.{v} A))) ≅
      (derivedHomAdjunctionULift.{u, v, max u v + 1} (R := A)).hom.obj
        (Opposite.op ((derivedScalarEquivalence.{u, v} A).inverse.obj ω),
          (derivedScalarEquivalence.{u, v} A).inverse.obj ω) :=
  have := isIso_derivedHomothety_ulift_of_isDualizingComplex.{u, v} A ω hω
  asIso (derivedHomothety
    (derivedHomAdjunctionULift.{u, v, max u v + 1} (R := A)).toDerivedHomAdjunction
    (DerivedCategory.Q.obj (𝟙_ (Model.Complex (ULift.{v} A))))
    (derivedHomAdjunctionULift.{u, v, max u v + 1} (R := A)).tensorUnitLeft
    ((derivedScalarEquivalence.{u, v} A).inverse.obj ω))

/-- **Derived Hom from a dualizing complex to itself has Tor amplitude `[0, 0]`.** This is the
hypothesis `hTor` of `Dualizing.isIso_dualizingBidualityMor_of_truncLE_pseudoCoherent`: by
`Dualizing.derivedHomSelfIsoUnit` the object `RHom(ω, ω)` is the tensor unit, so tensoring it
with a module placed in degree zero returns that module in degree zero. -/
theorem torAmplitude_derivedHomSelf [IsNoetherianRing A]
    (ω : DerivedCategory (ModuleCat.{max u v} A)) (hω : IsDualizingComplex ω) :
    let D := derivedHomAdjunctionULift.{u, v, max u v + 1} (R := A)
    ∃ a b : ℤ, ∀ (N : ModuleCat.{max u v} (ULift.{v} A)) (i : ℤ), i ∉ Set.Icc a b →
      Limits.IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{max u v} (ULift.{v} A)) i).obj
        (D.tensor.obj
          (D.hom.obj
            (Opposite.op ((derivedScalarEquivalence.{u, v} A).inverse.obj ω),
              (derivedScalarEquivalence.{u, v} A).inverse.obj ω),
            (DerivedCategory.singleFunctor (ModuleCat.{max u v} (ULift.{v} A)) 0).obj N))) := by
  intro D
  refine ⟨0, 0, fun N i hi => ?_⟩
  have hi' : i ≠ 0 := fun h => hi (by simp [h])
  let e := derivedHomSelfIsoUnit.{u, v} A ω hω
  refine Limits.IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor
    (ModuleCat.{max u v} (ULift.{v} A)) i).mapIso
    (D.tensor.mapIso (Iso.prod e.symm (Iso.refl _)) ≪≫ D.tensorUnitLeft _))
  rcases lt_or_gt_of_ne hi' with h | h
  · exact DerivedCategory.isZero_of_isGE _ 0 i h
  · exact DerivedCategory.isZero_of_isLE _ 0 i h

/-- **Biduality for a dualizing complex, reduced to pseudo-coherence of the argument.** The
canonical biduality morphism `K ⟶ RHom_A(RHom_A(K, ω), ω)` of [stacks 0A7C] is invertible as
soon as every truncation of the scalar preimage of `K` is pseudo-coherent. All three remaining
hypotheses of `Dualizing.isIso_dualizingBidualityMor_of_truncLE_pseudoCoherent` are supplied by
the dualizing hypothesis of [stacks 0A7B]. -/
@[sga "6 III 4.9.2" "special case"]
theorem isIso_dualizingBidualityMor_of_isDualizingComplex [IsNoetherianRing A]
    (ω K : DerivedCategory (ModuleCat.{max u v} A)) (hω : IsDualizingComplex ω)
    (hK : ∀ n : ℤ, StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((DerivedCategory.TStructure.t.truncLE n).obj
        ((derivedScalarEquivalence.{u, v} A).inverse.obj K))) :
    IsIso (dualizingBidualityMor.{u, v} A ω K) :=
  isIso_dualizingBidualityMor_of_truncLE_pseudoCoherent A ω K
    (isIso_derivedHomothety_ulift_of_isDualizingComplex.{u, v} A ω hω)
    (hasFiniteInjectiveDimension_scalarPreimage.{u, v} A ω hω.finiteInjectiveDimension)
    (torAmplitude_derivedHomSelf.{u, v} A ω hω) hK

end Final

/-! ### Pseudo-coherence of the truncations -/

section Coherence

universe u₂ u₃ v₂

open StacksDraft.PseudoCoherence CategoryTheory.Pretriangulated

attribute [local instance 5000] HasDerivedCategory.standard
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- The identity map of a module, as a semilinear equivalence onto its restriction of scalars
along a ring isomorphism. -/
abbrev restrictScalarsSemilinearEquiv {T : Type u₂} {S : Type u₃} [Ring T] [Ring S]
    (e : S ≃+* T) (M : ModuleCat.{v₂} T) :
    LinearEquiv (σ' := (e : S →+* T)) (e.symm : T →+* S) M
      ((ModuleCat.restrictScalars.{v₂} e.toRingHom).obj M) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change r • x = e (e.symm r) • x
    rw [e.apply_symm_apply]

/-- Finiteness of a module is preserved by restriction of scalars along a ring isomorphism. -/
theorem finite_restrictScalars_ringEquiv {T : Type u₂} {S : Type u₃} [Ring T] [Ring S]
    (e : S ≃+* T) (M : ModuleCat.{v₂} T) [Module.Finite T M] :
    Module.Finite S ((ModuleCat.restrictScalars.{v₂} e.toRingHom).obj M) :=
  Module.Finite.of_surjective (restrictScalarsSemilinearEquiv e M).toLinearMap
    (restrictScalarsSemilinearEquiv e M).surjective

variable {T : Type u₂} [CommRing T] [IsNoetherianRing T]

/-- **The truncation `τ^{≤ m}` preserves finiteness of cohomology.** Below the truncation bound
the long exact sequence of the truncation triangle makes the comparison a monomorphism, and a
submodule of a finite module over a Noetherian ring is finite; above the bound the cohomology
vanishes. -/
theorem finite_homology_truncLEObj (L : DerivedCategory (ModuleCat.{v₂} T))
    (hL : ∀ k : ℤ, Module.Finite T
      ((DerivedCategory.homologyFunctor (ModuleCat.{v₂} T) k).obj L)) (m k : ℤ) :
    Module.Finite T ((DerivedCategory.homologyFunctor (ModuleCat.{v₂} T) k).obj
      ((DerivedCategory.TStructure.t.truncLE m).obj L)) := by
  by_cases hk : k ≤ m
  · let Tr := (DerivedCategory.TStructure.t.triangleLEGE m (m + 1) rfl).obj L
    have hTr : Tr ∈ distTriang (DerivedCategory (ModuleCat.{v₂} T)) :=
      DerivedCategory.TStructure.t.triangleLEGE_distinguished m (m + 1) rfl L
    have h3 : DerivedCategory.TStructure.t.IsGE
        ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj L) (m + 1) := inferInstance
    have hmono : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{v₂} T) k).map Tr.mor₁) := by
      rw [DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff Tr hTr (k - 1) k (by omega)]
      exact (DerivedCategory.isZero_of_isGE (hX := h3) _ (m + 1) (k - 1) (by omega)).eq_of_src _ _
    have : IsNoetherian T ((DerivedCategory.homologyFunctor (ModuleCat.{v₂} T) k).obj Tr.obj₂) :=
      @isNoetherian_of_isNoetherianRing_of_finite T _ _ _ _ _ (hL k)
    exact Module.Finite.of_injective
      ((DerivedCategory.homologyFunctor (ModuleCat.{v₂} T) k).map Tr.mor₁).hom
      ((ModuleCat.mono_iff_injective _).1 hmono)
  · have : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{v₂} T) k).obj
        ((DerivedCategory.TStructure.t.truncLE m).obj L)) :=
      ModuleCat.isZero_iff_subsingleton.mp
        (DerivedCategory.isZero_of_isLE _ m k (by omega))
    infer_instance

/-- **Over a Noetherian ring, every truncation of an object with finite cohomology is
pseudo-coherent.** This is the hypothesis `hK` of
`Dualizing.isIso_dualizingBidualityMor_of_truncLE_pseudoCoherent`, at the base ring. -/
theorem isPseudoCoherent_truncLEObj [Small.{v₂} T] (L : DerivedCategory (ModuleCat.{v₂} T))
    (hL : ∀ k : ℤ, Module.Finite T
      ((DerivedCategory.homologyFunctor (ModuleCat.{v₂} T) k).obj L)) (m : ℤ) :
    IsPseudoCoherent ((DerivedCategory.TStructure.t.truncLE m).obj L) :=
  ((pseudoCoherent_iff_boundedAbove_finite_homology
      ((DerivedCategory.TStructure.t.truncLE m).obj L) 0 PUnit).2.1).mpr
    ⟨⟨m, fun i hi => DerivedCategory.isZero_of_isLE _ m i hi⟩,
      fun k => finite_homology_truncLEObj L hL m k⟩

end Coherence

/-! ### Biduality for a dualizing complex -/

section Capstone

universe v

attribute [local instance 5000] HasDerivedCategory.standard
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

open StacksDraft.PseudoCoherence

variable (A : Type u) [CommRing A]

/-- **Restriction of scalars along `ULift A ≃+* A` commutes with the homology functors.** It is
an exact functor, so on a representing complex the comparison is the short-complex homology
comparison. -/
def uliftRestrictHomologyIso (K : DerivedCategory (ModuleCat.{max u v} A)) (k : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} A)) k).obj
        ((derivedScalarEquivalence.{u, v} A).inverse.obj K) ≅
      (uliftRestrict.{u, v} A).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) k).obj K) := by
  have hF : (uliftRestrict.{u, v} A).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
      (ULift.ringEquiv : ULift.{v} A ≃+* A)
  let X := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj X ≅ K := DerivedCategory.Q.objObjPreimageIso K
  exact (DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} A)) k).mapIso
        ((uliftRestrict.{u, v} A).mapDerivedCategory.mapIso e.symm) ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} A)) k).mapIso
        ((Functor.mapDerivedCategoryFactors (uliftRestrict.{u, v} A)).app X) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} (ULift.{v} A)) k).app
        (((uliftRestrict.{u, v} A).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≪≫
      (X.sc k).mapHomologyIso (uliftRestrict.{u, v} A) ≪≫
      (uliftRestrict.{u, v} A).mapIso
        ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} A) k).app X).symm ≪≫
      (uliftRestrict.{u, v} A).mapIso
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) k).mapIso e)

/-- **Finiteness of cohomology transports to the lifted scalars.** -/
theorem finite_homology_scalarPreimage (K : DerivedCategory (ModuleCat.{max u v} A))
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K)) (k : ℤ) :
    Module.Finite (ULift.{v} A)
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} A)) k).obj
        ((derivedScalarEquivalence.{u, v} A).inverse.obj K)) := by
  have _ := hK k
  have hfin : Module.Finite (ULift.{v} A) ((uliftRestrict.{u, v} A).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) k).obj K)) :=
    finite_restrictScalars_ringEquiv (ULift.ringEquiv : ULift.{v} A ≃+* A) _
  exact Module.Finite.equiv (uliftRestrictHomologyIso.{u, v} A K k).symm.toLinearEquiv

/-- **Every truncation of the scalar preimage of an object with finite cohomology is
pseudo-coherent.** This is the remaining hypothesis `hK` of
`Dualizing.isIso_dualizingBidualityMor_of_isDualizingComplex`. -/
theorem isPseudoCoherent_truncLE_scalarPreimage [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{max u v} A))
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K)) (n : ℤ) :
    IsPseudoCoherent ((DerivedCategory.TStructure.t.truncLE n).obj
      ((derivedScalarEquivalence.{u, v} A).inverse.obj K)) := by
  have _ : IsNoetherianRing (ULift.{v} A) :=
    isNoetherianRing_of_ringEquiv A ULift.ringEquiv.symm
  exact isPseudoCoherent_truncLEObj _
    (fun k => finite_homology_scalarPreimage.{u, v} A K hK k) n

/-- **Canonical biduality for a dualizing complex, [stacks 0A7C].** For `ω` a dualizing complex
over a Noetherian ring `A` and `K` an object of the derived category with finite cohomology in
every degree, the canonical morphism `K ⟶ RHom_A(RHom_A(K, ω), ω)` is an isomorphism. -/
@[sga "5 I App.7.3" "special case", sga "6 III 4.9.2" "special case"]
theorem isIso_dualizingBidualityMor_of_finiteCohomology [IsNoetherianRing A]
    (ω K : DerivedCategory (ModuleCat.{max u v} A)) (hω : IsDualizingComplex ω)
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K)) :
    IsIso (dualizingBidualityMor.{u, v} A ω K) :=
  isIso_dualizingBidualityMor_of_isDualizingComplex.{u, v} A ω K hω
    (isPseudoCoherent_truncLE_scalarPreimage.{u, v} A K hK)

end Capstone

end Dualizing

end
