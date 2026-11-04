module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Fibres of the second map of a Stein factorization

Let `f : X ⟶ S` be universally closed, quasi-separated and locally of finite type, and let
`X ⟶ f.normalization ⟶ S` be the factorization of
`Stacks.SteinFactorization.toNormalization_fromNormalization`.  Then every fibre of the integral
map `π = f.fromNormalization` is finite, and the residue field of `f.normalization` at a point is
a finite extension of the residue field of `S` at its image.

## Main results

* `Stacks.SteinFactorization.finite_preimage_singleton_fromNormalization`: the fibres of `π` are
  finite.
* `Stacks.SteinFactorization.finite_residueFieldMap_fromNormalization`: the residue field
  extensions along `π` are finite.

## References

* [Stacks Project, Tag 0E0M](https://stacks.math.columbia.edu/tag/0E0M)
-/


@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.SteinFactorization

/-- A Noetherian sober space all of whose points are closed is finite. -/
public theorem finite_of_noetherianSpace_of_t1Space (α : Type*) [TopologicalSpace α]
    [NoetherianSpace α] [T1Space α] [QuasiSober α] : Finite α := by
  have hfin : (irreducibleComponents α).Finite :=
    NoetherianSpace.finite_irreducibleComponents
  have hsing : ∀ Z ∈ irreducibleComponents α, Z.Finite := by
    intro Z hZ
    obtain ⟨x, hx⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
    rw [← hx.def, isClosed_singleton.closure_eq]
    exact Set.finite_singleton x
  have huniv : (Set.univ : Set α).Finite := by
    rw [← sUnion_irreducibleComponents (X := α)]
    exact hfin.sUnion hsing
  exact Set.finite_univ_iff.mp huniv

/-- A ring that is integral over a field has Krull dimension zero. -/
public theorem krullDimLE_zero_of_isIntegral {R A : Type*} [CommRing R] [CommRing A]
    (φ : R →+* A) (hφ : φ.IsIntegral) (hR : IsField R) : Ring.KrullDimLE 0 A := by
  let := hR.toField
  refine Ring.KrullDimLE.mk₀ fun I hI ↦ ?_
  have : I.IsPrime := hI
  refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' φ hφ I ?_
  have hp : (I.comap φ).IsPrime := Ideal.IsPrime.comap φ
  have : I.comap φ = ⊥ := (Ideal.eq_bot_or_top (I.comap φ)).resolve_right hp.ne_top
  rw [this]
  exact Ideal.bot_isMaximal

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The fibre of an integral morphism over a point is a T1 space. -/
public theorem t1Space_fiber_of_isIntegralHom {Y : Scheme.{u}} (g : Y ⟶ S) [IsIntegralHom g]
    (s : S) : T1Space (g.fiber s) := by
  have : IsIntegralHom (g.fiberToSpecResidueField s) :=
    inferInstanceAs (IsIntegralHom (Limits.pullback.snd g (S.fromSpecResidueField s)))
  have : IsAffine (g.fiber s) := inferInstance
  have : AlgebraicGeometry.IsIntegral (Spec (S.residueField s)) :=
    (affine_isIntegral_iff _).mpr inferInstance
  have hR : IsField Γ(Spec (S.residueField s), ⊤) :=
    isField_of_isIntegral_of_subsingleton _
  have hint := (g.fiberToSpecResidueField s).isIntegral_app ⊤ (isAffineOpen_top _)
  have : Ring.KrullDimLE 0 Γ(g.fiber s, ⊤) :=
    krullDimLE_zero_of_isIntegral _ hint hR
  have : T1Space (Spec Γ(g.fiber s, ⊤)) :=
    ⟨fun p ↦ (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).2 p.2.isMaximal'⟩
  exact (g.fiber s).isoSpec.inv.homeomorph.t1Space

/-- For a morphism locally of finite type, the residue field at a point that is closed in its
fibre is a finite extension of the residue field at the image of the point. -/
public theorem finite_residueFieldMap_of_isClosed_inter {A B : Scheme.{u}} (h : A ⟶ B)
    [LocallyOfFiniteType h] (a : A) {C : Set A} (hC : IsClosed C)
    (hCa : C ∩ h ⁻¹' {h a} = {a}) : (h.residueFieldMap a).hom.Finite := by
  have hcl : IsClosed {h.asFiber a} := by
    have e : (h.fiberι (h a)) ⁻¹' C = {h.asFiber a} := by
      ext w
      have hwfib : h.fiberι (h a) w ∈ h ⁻¹' {h a} := h.apply_fiberι (h a) w
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hw
        have : h.fiberι (h a) w = a := hCa.subset ⟨hw, hwfib⟩
        exact (h.fiberι (h a)).isEmbedding.injective (by simpa using this)
      · intro hw
        subst hw
        rw [Scheme.Hom.fiberι_asFiber]
        exact hCa.symm.subset rfl |>.1
    rw [← e]
    exact hC.preimage (h.fiberι (h a)).continuous
  have hci : IsClosedImmersion (h.asFiberHom a) :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [h.range_asFiberHom a]; exact hcl)
  have : LocallyOfFiniteType (h.fiberToSpecResidueField (h a)) :=
    inferInstanceAs
      (LocallyOfFiniteType (Limits.pullback.snd h (B.fromSpecResidueField (h a))))
  have hlft : LocallyOfFiniteType (h.asFiberHom a ≫ h.fiberToSpecResidueField (h a)) :=
    inferInstance
  rw [h.asFiberHom_fiberToSpecResidueField a] at hlft
  have : IsFinite (Spec.map (h.residueFieldMap a)) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr hlft
  exact (IsFinite.SpecMap_iff _).mp this

/-- If `M` is a finite `K`-module through `K ⟶ L ⟶ M` and `L ⟶ M` is injective, then `L` is a
finite `K`-module. -/
public theorem ringHom_finite_of_comp {K L M : Type*} [CommRing K] [CommRing L] [CommRing M]
    [IsNoetherianRing K] (α : K →+* L) (β : L →+* M) (hβ : Function.Injective β)
    (h : (β.comp α).Finite) : α.Finite := by
  let := α.toAlgebra
  let := β.toAlgebra
  let := (β.comp α).toAlgebra
  have : IsScalarTower K L M := .of_algebraMap_eq' rfl
  have : Module.Finite K M := h
  exact Module.Finite.of_injective (IsScalarTower.toAlgHom K L M).toLinearMap hβ

/-- The version of `ringHom_finite_of_comp` for a composition in `CommRingCat`. -/
public theorem hom_finite_of_comp {K L M : CommRingCat.{u}} [IsNoetherianRing K] (α : K ⟶ L)
    (β : L ⟶ M) (hβ : Function.Injective β.hom) (h : (α ≫ β).hom.Finite) : α.hom.Finite := by
  rw [CommRingCat.hom_comp] at h
  exact ringHom_finite_of_comp α.hom β.hom hβ h

section Factorization

variable [QuasiCompact f] [QuasiSeparated f]

/-- Applying the second map of the factorization after the first gives back `f`. -/
private theorem fromNormalization_toNormalization (x : X) :
    f.fromNormalization (f.toNormalization x) = f x := by
  rw [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization]

private theorem mem_preimage_toNormalization_fiberι (s : S) (w : f.fiber s) :
    f.toNormalization (f.fiberι s w) ∈ f.fromNormalization ⁻¹' {s} := by
  simp only [Set.mem_preimage, Set.mem_singleton_iff, fromNormalization_toNormalization]
  exact f.apply_fiberι s w

/-- The map from the fibre of `f` over `s` to the fibre over `s` of the second map of the
factorization, induced by the first map of the factorization. -/
private noncomputable def fibreMap (s : S) (w : f.fiber s) : f.fromNormalization.fiber s :=
  (f.fromNormalization.fiberHomeo s).symm ⟨_, mem_preimage_toNormalization_fiberι f s w⟩

private theorem fiberι_fibreMap (s : S) (w : f.fiber s) :
    f.fromNormalization.fiberι s (fibreMap f s w) = f.toNormalization (f.fiberι s w) := by
  simp [fibreMap]

private theorem continuous_fibreMap (s : S) : Continuous (fibreMap f s) :=
  (f.fromNormalization.fiberHomeo s).symm.continuous.comp
    (Continuous.subtype_mk (f.toNormalization.continuous.comp (f.fiberι s).continuous)
      (mem_preimage_toNormalization_fiberι f s))

end Factorization

variable [UniversallyClosed f] [QuasiSeparated f]

private theorem surjective_fibreMap (s : S) : Function.Surjective (fibreMap f s) := by
  intro v
  obtain ⟨x, hx⟩ := (surjective_toNormalization f).surj (f.fromNormalization.fiberι s v)
  have hfx : f x = s := by
    rw [← fromNormalization_toNormalization f x, hx]
    exact f.fromNormalization.apply_fiberι s v
  obtain ⟨w, hw⟩ : x ∈ Set.range (f.fiberι s) := (f.range_fiberι s).ge hfx
  refine ⟨w, ?_⟩
  apply (f.fromNormalization.fiberHomeo s).injective
  exact Subtype.ext (by simp [fiberι_fibreMap, hw, hx])

variable [LocallyOfFiniteType f]

/-- For a universally closed, quasi-separated morphism `f` that is locally of finite type, the
fibres of the second map `π` of the factorization `X ⟶ f.normalization ⟶ S` are finite. -/
@[stacks 0E0M "finite_fibre"]
public theorem finite_preimage_singleton_fromNormalization (s : S) :
    (f.fromNormalization ⁻¹' {s}).Finite := by
  have : IsLocallyNoetherian (f.fiber s) :=
    inferInstanceAs (IsLocallyNoetherian (Limits.pullback f (S.fromSpecResidueField s)))
  have : IsNoetherian (f.fiber s) := ⟨⟩
  have : NoetherianSpace (f.fromNormalization.fiber s) :=
    noetherianSpace_of_surjective _ (continuous_fibreMap f s) (surjective_fibreMap f s)
  have : T1Space (f.fromNormalization.fiber s) :=
    t1Space_fiber_of_isIntegralHom f.fromNormalization s
  have : Finite (f.fromNormalization.fiber s) := finite_of_noetherianSpace_of_t1Space _
  have : Finite ↥(f.fromNormalization ⁻¹' {s}) :=
    Finite.of_equiv _ (f.fromNormalization.fiberHomeo s).toEquiv
  exact Set.finite_coe_iff.mp this

/-- Every point of `f.normalization` is the image under the first map of the factorization of a
point of `X` that is closed in its `f`-fibre. -/
private theorem exists_closed_in_fibre (s' : f.normalization) :
    ∃ x : X, f.toNormalization x = s' ∧
      ∃ C : Set X, IsClosed C ∧ C ∩ f ⁻¹' {f x} = {x} := by
  set s := f.fromNormalization s' with hs
  obtain ⟨v, hv⟩ : s' ∈ Set.range (f.fromNormalization.fiberι s) :=
    (f.fromNormalization.range_fiberι s).ge hs.symm
  have : T1Space (f.fromNormalization.fiber s) :=
    t1Space_fiber_of_isIntegralHom f.fromNormalization s
  have hpre : IsClosed (fibreMap f s ⁻¹' {v}) :=
    (isClosed_singleton (x := v)).preimage (continuous_fibreMap f s)
  obtain ⟨w₀, hw₀⟩ := surjective_fibreMap f s v
  obtain ⟨w, hwZ, hwcl⟩ :=
    nonempty_inter_closedPoints (X := f.fiber s) ⟨w₀, hw₀⟩ hpre.isLocallyClosed
  have hwv : fibreMap f s w = v := hwZ
  refine ⟨f.fiberι s w, ?_, ?_⟩
  · rw [← hv, ← hwv, fiberι_fibreMap]
  · have hfx : f (f.fiberι s w) = s := f.apply_fiberι s w
    set e := f.fiberHomeo s with he
    have himg : IsClosed ({e w} : Set ↥(f ⁻¹' {s})) := by
      have h := e.isClosedMap {w} hwcl
      rwa [Set.image_singleton] at h
    obtain ⟨C, hC, hCeq⟩ := isClosed_induced_iff.mp himg
    refine ⟨C, hC, ?_⟩
    rw [hfx]
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hyC, hys⟩
      have hy : (⟨y, hys⟩ : ↥(f ⁻¹' {s})) ∈ Subtype.val ⁻¹' C := hyC
      rw [hCeq] at hy
      exact congrArg Subtype.val hy
    · rintro rfl
      refine ⟨?_, hfx⟩
      have hy : (e w) ∈ Subtype.val ⁻¹' C := by rw [hCeq]; rfl
      exact hy

/-- For a universally closed, quasi-separated morphism `f` that is locally of finite type, the
residue field of `f.normalization` at a point is a finite extension of the residue field of `S` at
its image under the second map `π` of the factorization: the ring map `κ(π s') ⟶ κ(s')` makes
`κ(s')` a finite `κ(π s')`-module. -/
@[stacks 0E0M "finite_residue_extensions"]
public theorem finite_residueFieldMap_fromNormalization (s' : f.normalization) :
    (f.fromNormalization.residueFieldMap s').hom.Finite := by
  obtain ⟨x, hx, C, hC, hCx⟩ := exists_closed_in_fibre f s'
  subst hx
  have key : ((f.toNormalization ≫ f.fromNormalization).residueFieldMap x).hom.Finite := by
    rw [Scheme.Hom.toNormalization_fromNormalization]
    exact finite_residueFieldMap_of_isClosed_inter f x hC hCx
  rw [Scheme.residueFieldMap_comp] at key
  exact hom_finite_of_comp _ _ (f.toNormalization.residueFieldMap x).hom.injective key

end Stacks.SteinFactorization
