module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleEulerFormula
public import StacksFrontier.AlgebraicGeometry.Meromorphic.RegularSectionExistence

/-!
# The vanishing criterion for the Euler characteristic of an invertible coherent triple

Let `A` be a Noetherian local ring of depth at least three, let `f ∈ 𝔪` be a nonzerodivisor, and
let `(F, F₀, α)` be a coherent triple for `(A, f)` whose two members are invertible. Its Euler
characteristic vanishes exactly when the member `F` on the punctured spectrum is trivial, that is
isomorphic to the structure sheaf there. This is the criterion of [Stacks, Tag 0F28].

## Main results

* `Stacks.Algebraization.CoherentTriple.eulerCharacteristic_eq_zero_iff_isTrivial`:
  **[Stacks, Tag 0F28]** — the Euler characteristic vanishes exactly when the
  punctured-spectrum member of the triple is trivial.
* `Stacks.Algebraization.isTrivial_of_bijective_closedFibreMap` and
  `Stacks.Algebraization.isIso_closedFibreMap_of_isTrivial`: the two halves of the criterion,
  read on the closed-fibre map of a prepared extension.
* `Stacks.Algebraization.injective_closedFibreMap_of_pushforward`: the closed-fibre map of the
  prepared extension given by the direct image of the punctured-spectrum member is injective.

## Implementation notes

By the Euler-characteristic formula the Euler characteristic vanishes exactly when the canonical
map on global sections is surjective, and over the prepared extension given by the direct image of
the punctured-spectrum member that happens exactly when the closed-fibre map is surjective. So the
criterion is the statement that the closed-fibre map of that prepared extension is bijective
exactly when the punctured-spectrum member is trivial.

For the forward direction, the closed-fibre map identifies the global sections of the prepared
extension modulo `f` with the global sections of the closed-fibre member, and the latter is a free
module of rank one because an invertible module on the spectrum of a local ring is trivial. A
finite module over a Noetherian local ring on which `f` acts regularly and whose reduction modulo
`f` is free of rank one is itself free of rank one — freeness descends from the reduction by
`Module.free_quotSMulTop_iff_free` and the rank is read off the base change — so the prepared
extension is the structure sheaf of `Spec A`, and its restriction to the punctured spectrum, which
is the triple's punctured-spectrum member, is the structure sheaf there.

For the converse, if the punctured-spectrum member is trivial then so is the prepared extension,
because the structure sheaf of `Spec A` is the direct image of its own restriction when the depth
is at least two. Hence so is its restriction to the closed fibre, whose global sections are `A/fA`;
and over `A/fA`, which has depth at least two, both that restriction and the triple's closed-fibre
member are the direct images of their restrictions to the punctured closed fibre. The compatibility
datum of the prepared extension makes the closed-fibre map an isomorphism over the punctured closed
fibre, and a morphism whose inverse image is an isomorphism between two modules recovered from
their inverse images is itself an isomorphism.

The lengths are read through `Module.length`, and surjectivity of a map with a finite-length
cokernel is the vanishing of that length; that is
`Stacks.Algebraization.length_cokernel_toNat_eq_zero_iff_surjective`, the cokernel being of finite
length by `Stacks.Algebraization.finiteLength_cokernel_globalSectionsMap`.

## References

* [Stacks Project, Tag 0F28](https://stacks.math.columbia.edu/tag/0F28)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing Opposite
open TopologicalSpace
open scoped TensorProduct

universe u

namespace Stacks.Algebraization

/-! ### Trivial modules on an affine scheme -/

/-- The global sections of the structure sheaf of `Spec A`, as an `A`-module, are `A`. -/
public noncomputable def unitSpecSectionsEquiv (A : Type u) [CommRing A] :
    ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj
      (SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf)) ≃ₗ[A] A := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
  refine { e.toAddEquiv with map_smul' := ?_ }
  intro a x
  change e (e.symm a * (show Γ(Spec (CommRingCat.of A), ⊤) from x)) = a * e x
  rw [map_mul, e.apply_symm_apply]

/-- **A quasi-coherent module on `Spec A` whose global sections are free of rank one is the
structure sheaf.** The module is the tilde of its global sections, and the tilde of `A` is the
structure sheaf. -/
public noncomputable def specModuleIsoUnitOfSectionsEquiv (A : Type u) [CommRing A]
    (F : (Spec (CommRingCat.of A)).Modules) [F.IsQuasicoherent]
    (e : ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj F) ≃ₗ[A] A) :
    F ≅ SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf :=
  (asIso F.fromTildeΓ).symm ≪≫ (tilde.functor (CommRingCat.of A)).mapIso e.toModuleIso ≪≫
    tildeSelf

/-- The quotient of a local ring by an element of its maximal ideal is local. -/
private theorem isLocalRing_quotient_span_singleton_of_mem_maximalIdeal {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} (hf : f ∈ maximalIdeal A) : IsLocalRing (A ⧸ Ideal.span {f}) :=
  haveI : Nontrivial (A ⧸ Ideal.span {f}) := Ideal.Quotient.nontrivial_iff.mpr fun h =>
    (maximalIdeal.isMaximal A).ne_top
      (top_unique (h ▸ Ideal.span_le.mpr (by simpa using hf)))
  IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {f})) Ideal.Quotient.mk_surjective

/-- The reduction of `A` modulo a single element is the quotient by the ideal it generates. -/
public noncomputable def quotSMulTopRingEquiv (A : Type u) [CommRing A] (f : A) :
    QuotSMulTop f A ≃ₗ[A] (A ⧸ Ideal.span {f}) :=
  Submodule.quotEquivOfEq _ _ (by rw [← Submodule.ideal_span_singleton_smul]; simp)

/-- **A finite module over a Noetherian local ring whose reduction modulo a regular element of
the maximal ideal is free of rank one is itself free of rank one.** Freeness of the reduction
gives freeness of the module by `Module.free_quotSMulTop_iff_free`, and the rank is read off the
base change along `A → A/fA`. -/
public theorem nonempty_linearEquiv_ring_of_quotSMulTop (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (f : A) (hf : f ∈ maximalIdeal A) (hreg : IsSMulRegular M f)
    [Nontrivial (A ⧸ Ideal.span {f})]
    (e : QuotSMulTop f M ≃ₗ[A] (A ⧸ Ideal.span {f})) :
    Nonempty (M ≃ₗ[A] A) := by
  have : Module.Free (A ⧸ Ideal.span {f}) (QuotSMulTop f M) := Module.Free.of_equiv
    (e.extendScalarsOfSurjective (S := A ⧸ Ideal.span {f}) Ideal.Quotient.mk_surjective).symm
  have : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  have : Module.Free A M := (Module.free_quotSMulTop_iff_free A M
    (by simpa only [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] using hf) hreg).mp
      inferInstance
  let ET : (A ⧸ Ideal.span {f}) ⊗[A] M ≃ₗ[A ⧸ Ideal.span {f}] (A ⧸ Ideal.span {f}) :=
    ((QuotSMulTop.equivQuotTensor f M).symm.trans e).extendScalarsOfSurjective
      (S := A ⧸ Ideal.span {f}) Ideal.Quotient.mk_surjective
  have hdim : Module.finrank A M = 1 := by
    rw [← Module.finrank_baseChange (R := A ⧸ Ideal.span {f}), ET.finrank_eq]
    simp
  exact ⟨LinearEquiv.ofFinrankEq M A (by simpa using hdim)⟩

/-! ### Surjectivity from the vanishing of the cokernel length -/

/-- **A map whose cokernel has finite length is surjective exactly when that length is zero.** -/
public theorem length_cokernel_toNat_eq_zero_iff_surjective
    {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (g : M →ₗ[R] N)
    (h : IsFiniteLength R (N ⧸ LinearMap.range g)) :
    (Module.length R (N ⧸ LinearMap.range g)).toNat = 0 ↔ Function.Surjective g := by
  rw [ENat.toNat_eq_zero]
  simp only [Module.length_ne_top_iff.mpr h, or_false, Module.length_eq_zero_iff,
    Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top]

/-! ### Isomorphisms detected on inverse images -/

/-- **A morphism between two objects recovered from their images under a left adjoint is an
isomorphism as soon as its image is.** -/
public theorem isIso_of_isIso_pullback_of_isIso_unit {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {X Y : C} (g : X ⟶ Y)
    [IsIso (adj.unit.app X)] [IsIso (adj.unit.app Y)] [IsIso (L.map g)] : IsIso g := by
  have : IsIso (g ≫ adj.unit.app Y) := by
    rw [← adj.unit_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right g (adj.unit.app Y)

/-! ### The closed-fibre map of the direct-image prepared extension -/

/-- **The closed-fibre map of the prepared extension given by the direct image of the
punctured-spectrum member of an invertible coherent triple is injective.** Its global sections
are a finite module of depth at least two over `A`, so
`Stacks.Algebraization.injective_closedFibreMap_of_two_le_depth` applies. -/
public theorem injective_closedFibreMap_of_pushforward (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf : f ∈ maximalIdeal A) (T : CoherentTriple A f)
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf
      (Stacks.Divisors.puncturedSpectrum A).toScheme.ringCatSheaf.2 T.F]
    (P : PreparedExtension A f T)
    (hP : P.F' = (Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum A).ι).obj T.F)
    (hdepth : 2 ≤ Module.depth A (maximalIdeal A) A) :
    Function.Injective P.closedFibreMap := by
  have hcP : _root_.SheafOfModules.IsCoherent P.F' := P.coherent
  have hftP : P.F'.IsFiniteType := _root_.SheafOfModules.IsCoherent.isFiniteType
  have hunit : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction
      (Stacks.Divisors.puncturedSpectrum A).ι).unit.app P.F') :=
    ((Scheme.Modules.pullbackPushforwardAdjunction
      (Stacks.Divisors.puncturedSpectrum A).ι).unit.isIso_app_iff_of_iso
        (eqToIso hP)).mpr (isIso_unit_pushforward_puncturedSpectrum A T.F hdepth)
  exact injective_closedFibreMap_of_two_le_depth A f hf T P
    (finite_globalSections_of_isCoherent P.F' P.coherent)
    (two_le_depth_globalSections_of_isIso_unit A P.F' hunit)

/-! ### The two halves of the criterion -/

/-- **A prepared extension whose closed-fibre map is bijective has a trivial
punctured-spectrum member.** The closed-fibre map identifies the global sections of the prepared
extension modulo `f` with those of the closed-fibre member, which are free of rank one because an
invertible module on the spectrum of a local ring is trivial; so the global sections of the
prepared extension are free of rank one and the prepared extension is the structure sheaf of
`Spec A`. -/
public theorem isTrivial_of_bijective_closedFibreMap (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf : f ∈ maximalIdeal A) (T : CoherentTriple A f)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (closedFibre A f).presheaf
      (closedFibre A f).ringCatSheaf.2 T.F₀]
    (P : PreparedExtension A f T) (hbij : Function.Bijective P.closedFibreMap) :
    Stacks.SheafOfModules.IsTrivial (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf
      (Stacks.Divisors.puncturedSpectrum A).toScheme.ringCatSheaf.2 T.F := by
  have := isLocalRing_quotient_span_singleton_of_mem_maximalIdeal hf
  have hcP : _root_.SheafOfModules.IsCoherent P.F' := P.coherent
  have hqcP : P.F'.IsQuasicoherent := isQuasicoherent_of_isCoherent P.F'
  have hfin : Module.Finite A ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj P.F') :=
    finite_globalSections_of_isCoherent P.F' P.coherent
  obtain ⟨e₀⟩ := AlgebraicGeometry.nonempty_iso_unit_of_isInvertible_spec_isLocalRing
    (A ⧸ Ideal.span {f}) T.F₀
  let e₀' := (moduleSpecΓFunctor (R := CommRingCat.of (A ⧸ Ideal.span {f}))).mapIso e₀ ≪≫
    (unitSpecSectionsEquiv (A ⧸ Ideal.span {f})).toModuleIso
  let E₀ := ((ModuleCat.restrictScalars
    (Ideal.Quotient.mk (Ideal.span {f}))).mapIso e₀').toLinearEquiv
  let E : QuotSMulTop f ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj P.F') ≃ₗ[A]
      (A ⧸ Ideal.span {f}) :=
    (closedFibreSectionsEquivQuotSMulTop A f P.F').symm.trans
      ((LinearEquiv.ofBijective P.closedFibreMap.hom hbij).trans E₀)
  have hr : IsSMulRegular ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj P.F') f :=
    (by simpa using P.regular ⊤ :
      IsSMulRegular Γ(P.F', ⊤) ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f))
  obtain ⟨e⟩ := nonempty_linearEquiv_ring_of_quotSMulTop A
    ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj P.F') f hf hr E
  exact ⟨P.alpha'.symm ≪≫
    (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).mapIso
      (specModuleIsoUnitOfSectionsEquiv A P.F' e) ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback
        (Stacks.Divisors.puncturedSpectrum A).ι).app _).symm ≪≫
      Scheme.Modules.restrictUnitIso (Stacks.Divisors.puncturedSpectrum A).ι⟩

/-- **If the punctured-spectrum member of an invertible coherent triple is trivial, then the
closed-fibre map of the prepared extension given by its direct image is an isomorphism.** The
prepared extension is then the structure sheaf of `Spec A`, so its restriction to the closed
fibre and the closed-fibre member of the triple are both the direct images of their restrictions
to the punctured closed fibre, over which the compatibility datum makes the closed-fibre map an
isomorphism. -/
public theorem isIso_closedFibreMap_of_isTrivial (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf : f ∈ maximalIdeal A) (hreg : IsRegular f)
    (T : CoherentTriple A f)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (closedFibre A f).presheaf
      (closedFibre A f).ringCatSheaf.2 T.F₀]
    (hdepth : 3 ≤ Module.depth A (maximalIdeal A) A) (P : PreparedExtension A f T)
    (hP : P.F' = (Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum A).ι).obj T.F)
    (hT : Stacks.SheafOfModules.IsTrivial
      (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf
      (Stacks.Divisors.puncturedSpectrum A).toScheme.ringCatSheaf.2 T.F) :
    IsIso P.closedFibreMap := by
  have := isLocalRing_quotient_span_singleton_of_mem_maximalIdeal hf
  have hd2 : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A :=
    (show (2 : ℕ∞) ≤ 3 by decide).trans hdepth
  let U := Stacks.Divisors.puncturedSpectrum A
  let O := SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf
  let adj := Scheme.Modules.pullbackPushforwardAdjunction U.ι
  have hOA : IsIso (adj.unit.app O) :=
    isIso_unit_puncturedSpectrum_of_isInvertible A O hd2
  let eU : (Scheme.Modules.pullback U.ι).obj O ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf :=
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app _).symm ≪≫
      Scheme.Modules.restrictUnitIso U.ι
  obtain ⟨eT⟩ := hT
  let eP : P.F' ≅ O := eqToIso hP ≪≫
    (Scheme.Modules.pushforward U.ι).mapIso (eT ≪≫ eU.symm) ≪≫ (asIso (adj.unit.app O)).symm
  have hcP : _root_.SheafOfModules.IsCoherent P.F' := P.coherent
  have hqcP : P.F'.IsQuasicoherent := isQuasicoherent_of_isCoherent P.F'
  let eM := ((moduleSpecΓFunctor (R := CommRingCat.of A)).mapIso eP).toLinearEquiv.trans
    (unitSpecSectionsEquiv A)
  let G := (Scheme.Modules.pullback (closedImmersion A f)).obj P.F'
  have hcG : _root_.SheafOfModules.IsCoherent G :=
    AlgebraicGeometry.isCoherent_pullback (closedImmersion A f) P.F'
  have hqcG : G.IsQuasicoherent := isQuasicoherent_of_isCoherent G
  let : Module A ((moduleSpecΓFunctor (R := CommRingCat.of (A ⧸ Ideal.span {f}))).obj G) :=
    ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {f}))).obj
      ((moduleSpecΓFunctor (R := CommRingCat.of (A ⧸ Ideal.span {f}))).obj G)).isModule
  let : IsScalarTower A (A ⧸ Ideal.span {f})
      ((moduleSpecΓFunctor (R := CommRingCat.of (A ⧸ Ideal.span {f}))).obj G) :=
    ⟨fun a b m => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  let eG : ((moduleSpecΓFunctor (R := CommRingCat.of (A ⧸ Ideal.span {f}))).obj G) ≃ₗ[
      A ⧸ Ideal.span {f}] (A ⧸ Ideal.span {f}) :=
    ((closedFibreSectionsEquivQuotSMulTop A f P.F').trans
      ((QuotSMulTop.congr f eM).trans (quotSMulTopRingEquiv A f))).extendScalarsOfSurjective
        (S := A ⧸ Ideal.span {f}) Ideal.Quotient.mk_surjective
  let eG' := specModuleIsoUnitOfSectionsEquiv (A ⧸ Ideal.span {f}) G eG
  let j₀ := (puncturedClosedFibre A f).ι
  let adj₀ := Scheme.Modules.pullbackPushforwardAdjunction j₀
  have hdB : 2 ≤ Module.depth (A ⧸ Ideal.span {f}) (maximalIdeal (A ⧸ Ideal.span {f}))
      (A ⧸ Ideal.span {f}) := by
    apply (ENat.add_le_add_iff_right (show (1 : ℕ∞) ≠ ⊤ by simp)).mp
    simpa only [show (2 : ℕ∞) + 1 = 3 by rfl,
      depth_quotient_span_singleton_add_one A f hf hreg] using hdepth
  have hOU : IsIso (adj₀.unit.app
      (SheafOfModules.unit (closedFibre A f).ringCatSheaf)) := by
    dsimp only [adj₀, j₀]
    rw [puncturedClosedFibre_eq_puncturedSpectrum A f hf]
    exact isIso_unit_puncturedSpectrum_of_isInvertible (A ⧸ Ideal.span {f}) _ hdB
  have hGu : IsIso (adj₀.unit.app G) := (adj₀.unit.isIso_app_iff_of_iso eG').mpr hOU
  have hF₀u : IsIso (adj₀.unit.app T.F₀) :=
    isIso_unit_puncturedClosedFibre A f hf hreg T.F₀ hdepth
  have hi : IsIso ((Scheme.Modules.pullbackComp j₀ (closedImmersion A f)).inv.app P.F' ≫
      (Scheme.Modules.pullback j₀).map P.alpha₀') := by
    rw [← P.compatible]
    infer_instance
  have hpa : IsIso ((Scheme.Modules.pullback j₀).map P.alpha₀') :=
    IsIso.of_isIso_comp_left
      ((Scheme.Modules.pullbackComp j₀ (closedImmersion A f)).inv.app P.F') _
  have : IsIso P.alpha₀' := isIso_of_isIso_pullback_of_isIso_unit adj₀ P.alpha₀'
  unfold PreparedExtension.closedFibreMap
  infer_instance

/-! ### The criterion -/

/-- **Stacks Project, Tag 0F28.** For an invertible coherent triple over a Noetherian local ring
of depth at least three, the Euler characteristic of the triple vanishes exactly when the member
on the punctured spectrum is trivial.

By the Euler-characteristic formula the vanishing is the surjectivity of the canonical map on
global sections, which for the prepared extension given by the direct image of the
punctured-spectrum member is the surjectivity of the closed-fibre map; that map is injective by
`Stacks.Algebraization.injective_closedFibreMap_of_pushforward`, and the two halves of the
criterion are
`Stacks.Algebraization.isTrivial_of_bijective_closedFibreMap` and
`Stacks.Algebraization.isIso_closedFibreMap_of_isTrivial`. -/
@[stacks 0F28 "vanishing criterion"]
public theorem CoherentTriple.eulerCharacteristic_eq_zero_iff_isTrivial (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (f : A) (hf : f ∈ maximalIdeal A) (hreg : IsRegular f)
    (T : CoherentTriple A f)
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf
      (Stacks.Divisors.puncturedSpectrum A).toScheme.ringCatSheaf.2 T.F]
    [AlgebraicGeometry.SheafOfModules.IsInvertible (closedFibre A f).presheaf
      (closedFibre A f).ringCatSheaf.2 T.F₀]
    (hdepth : 3 ≤ Module.depth A (maximalIdeal A) A) :
    T.eulerCharacteristic hf hreg = 0 ↔
      Stacks.SheafOfModules.IsTrivial (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf
        (Stacks.Divisors.puncturedSpectrum A).toScheme.ringCatSheaf.2 T.F := by
  let := puncturedSectionsModule A T.F
  let := puncturedClosedFibreSectionsModule A f
    ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀)
  obtain ⟨P, hP, -, hiff⟩ := exists_preparedExtension_length_cokernel_eq A f hf hreg T hdepth
  rw [CoherentTriple.eulerCharacteristic_eq_length_cokernel A f hf hreg T hdepth,
    Int.natCast_eq_zero, length_cokernel_toNat_eq_zero_iff_surjective _
      (finiteLength_cokernel_globalSectionsMap A f hf hreg T hdepth), hiff]
  refine ⟨fun hs => isTrivial_of_bijective_closedFibreMap A f hf T P
    ⟨injective_closedFibreMap_of_pushforward A f hf T P hP
      ((show (2 : ℕ∞) ≤ 3 by decide).trans hdepth), hs⟩, fun ht => ?_⟩
  have : IsIso P.closedFibreMap := isIso_closedFibreMap_of_isTrivial A f hf hreg T hdepth P hP ht
  exact (ConcreteCategory.bijective_of_isIso _).surjective

end Stacks.Algebraization

end
