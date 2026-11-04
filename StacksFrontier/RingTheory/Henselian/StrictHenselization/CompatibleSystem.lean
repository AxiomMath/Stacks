module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.SeparableClosure
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.ExistenceData

/-!
# A compatible system of strict henselizations

Let `(R_i, f_{ij})` be a directed system of local rings along local homomorphisms, and let
`Ω` be a separably closed field with maps `κ(R_i) → Ω` compatible with the residue field maps of
the `f_{ij}`. Let `κ_i^{sep}` be the separable closure of `κ(R_i)` inside `Ω`, so that
`κ_i^{sep} ⊆ κ_j^{sep}` for `i ≤ j`, and let `R_i → R_i^{sh}` be a strict henselization of `R_i`
with respect to `κ_i^{sep}` (Stacks 04GP). The maps `R_i^{sh} → R_j^{sh}` of Stacks 04GU over the
`f_{ij}` inducing the inclusions `κ_i^{sep} ⊆ κ_j^{sep}` on residue fields form a directed
system: by the uniqueness half of 04GU, the identity and the composites are again the maps of
04GU, since they induce the identity and the composite inclusions of residue fields. This is the
input of `Stacks.StrictHenselization.DirectLimit.isStrictHenselization_directLimit`, which
identifies the colimit of the system with a strict henselization of the colimit.

## Main definitions

* `Stacks.StrictHenselization.CompatibleSystem.mapOfResidue`: the ring map of Stacks 04GU, with
  the structure map of the target given as a ring map rather than as an algebra instance.
* `Stacks.StrictHenselization.CompatibleSystem.transition`: the map `R_i^{sh} → R_j^{sh}` over
  `f_{ij}` inducing `κ_i^{sep} ⊆ κ_j^{sep}`.

## Main results

* `Stacks.StrictHenselization.CompatibleSystem.eq_transition`: `transition` is the only local
  ring map over `f_{ij}` compatible with the residue maps to `Ω`.
* `Stacks.StrictHenselization.CompatibleSystem.directedSystem_transition`: the transition maps
  form a directed system.
* `Stacks.StrictHenselization.CompatibleSystem.exists_directedSystem_isStrictHenselization`:
  **a directed system of local rings along local maps, with compatible residue maps to a
  separably closed field, has a directed system of strict henselizations over it.**

## References

* [StacksProject 04GP](https://stacks.math.columbia.edu/tag/04GP)
* [StacksProject 04GU](https://stacks.math.columbia.edu/tag/04GU)
* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u v w

namespace Stacks.StrictHenselization.CompatibleSystem

section MapOfResidue

variable {R : Type u} {A : Type v} {S : Type w} [CommRing R] [CommRing A] [IsLocalRing A]
  [Algebra R A] [CommRing S] [HenselianLocalRing S]
  (hind : (CommAlgCat.etale.{max u v} R).ind.{max u v} (CommAlgCat.of R (ULift.{u} A)))
  (g : R →+* S) (φ : ResidueField A →+* ResidueField S)
  (hφ : φ.comp ((residue A).comp (algebraMap R A)) = (residue S).comp g)

/-- **The ring map of Stacks 04GU, over a ring map `g : R → S`**: the `R`-algebra map
`A → S` inducing `φ` on residue fields, for the `R`-algebra structure `g` on `S`
(`HenselianLocalRing.indEtaleAlgHomOfResidue`). -/
def mapOfResidue : A →+* S :=
  letI := g.toAlgebra
  (HenselianLocalRing.indEtaleAlgHomOfResidue hind φ hφ : A →+* S)

/-- `mapOfResidue` lies over `g`. -/
theorem mapOfResidue_comp_algebraMap : (mapOfResidue hind g φ hφ).comp (algebraMap R A) = g :=
  letI := g.toAlgebra
  (HenselianLocalRing.indEtaleAlgHomOfResidue hind φ hφ).comp_algebraMap

/-- `mapOfResidue` is local. -/
theorem isLocalHom_mapOfResidue : IsLocalHom (mapOfResidue hind g φ hφ) := by
  let := g.toAlgebra
  have := HenselianLocalRing.isLocalHom_indEtaleAlgHomOfResidue hind φ hφ
  exact ⟨fun a ha => IsLocalHom.map_nonunit
    (f := HenselianLocalRing.indEtaleAlgHomOfResidue hind φ hφ) a ha⟩

/-- `mapOfResidue` induces `φ` on residue fields. -/
theorem residue_comp_mapOfResidue :
    (residue S).comp (mapOfResidue hind g φ hφ) = φ.comp (residue A) :=
  letI := g.toAlgebra
  HenselianLocalRing.comp_residue_indEtaleAlgHomOfResidue hind φ hφ

/-- `mapOfResidue` is the only ring map over `g` inducing `φ` on residue fields. -/
theorem eq_mapOfResidue (h : A →+* S) (hg : h.comp (algebraMap R A) = g)
    (hloc : IsLocalHom h) (hres : (residue S).comp h = φ.comp (residue A)) :
    h = mapOfResidue hind g φ hφ := by
  let := g.toAlgebra
  let hA : A →ₐ[R] S := { h with commutes' := fun r => RingHom.congr_fun hg r }
  have := HenselianLocalRing.indEtaleAlgHomOfResidue_unique hind φ hφ hA
    ⟨fun a ha => hloc.map_nonunit a ha⟩ hres
  exact congrArg AlgHom.toRingHom this

end MapOfResidue

/-- The residue field of a local ring is its residue field at the maximal ideal. -/
def residueFieldEquivIdeal (S : Type u) [CommRing S] [IsLocalRing S] :
    ResidueField S ≃+* (maximalIdeal S).ResidueField :=
  (AlgEquiv.ofBijective (Algebra.ofId (ResidueField S) (maximalIdeal S).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal S))).toRingEquiv

/-- `residueFieldEquivIdeal` on a residue class. -/
theorem residueFieldEquivIdeal_residue (S : Type u) [CommRing S] [IsLocalRing S] (x : S) :
    residueFieldEquivIdeal S (residue S x) = algebraMap S (maximalIdeal S).ResidueField x :=
  (IsScalarTower.algebraMap_apply S (S ⧸ maximalIdeal S) _ x).symm

section System

variable {ι : Type w} [Preorder ι]
  {R : ι → Type u} [∀ i, CommRing (R i)] [∀ i, IsLocalRing (R i)]
  (f : ∀ i j, i ≤ j → R i →+* R j) (hf : ∀ i j h, IsLocalHom (f i j h))
  {Ω : Type v} [Field Ω] [IsSepClosed Ω] [∀ i, Algebra (maximalIdeal (R i)).ResidueField Ω]
  (hω : ∀ i j (h : i ≤ j) (r : R i),
    algebraMap _ Ω (algebraMap (R j) (maximalIdeal (R j)).ResidueField (f i j h r)) =
      algebraMap _ Ω (algebraMap (R i) (maximalIdeal (R i)).ResidueField r))
  {Rsh : ι → Type u} [∀ i, CommRing (Rsh i)] [∀ i, IsLocalRing (Rsh i)]
  [∀ i, Algebra (R i) (Rsh i)]
  (H : ∀ i, IsStrictHenselization (R i)
    (separableClosure (maximalIdeal (R i)).ResidueField Ω) (Rsh i))

/-- The residue field of `R_i^{sh}`, identified with `κ_i^{sep} ⊆ Ω`, mapped into `Ω`. -/
def residueToΩ (i : ι) : ResidueField (Rsh i) →+* Ω :=
  (algebraMap (separableClosure (maximalIdeal (R i)).ResidueField Ω) Ω).comp
    (((H i).residueFieldEquiv.symm : (maximalIdeal (Rsh i)).ResidueField →+* _).comp
      (residueFieldEquivIdeal (Rsh i) : ResidueField (Rsh i) →+* _))

omit [Preorder ι] in
/-- The map of `residueToΩ` is injective, being a map of fields. -/
theorem residueToΩ_injective (i : ι) : Function.Injective (residueToΩ H i) :=
  (residueToΩ H i).injective

omit [Preorder ι] in
/-- `residueToΩ` on the image of `R_i` is the given map `κ(R_i) → Ω`. -/
theorem residueToΩ_residue_algebraMap (i : ι) (r : R i) :
    residueToΩ H i (residue (Rsh i) (algebraMap (R i) (Rsh i) r)) =
      algebraMap _ Ω (algebraMap (R i) (maximalIdeal (R i)).ResidueField r) := by
  have := (H i).isLocalHom
  have h1 : (H i).residueFieldEquiv (algebraMap _ (separableClosure _ Ω)
      (algebraMap (R i) (maximalIdeal (R i)).ResidueField r)) =
      algebraMap (Rsh i) (maximalIdeal (Rsh i)).ResidueField (algebraMap (R i) (Rsh i) r) := by
    rw [← Ideal.ResidueField.map_algebraMap (maximalIdeal (R i)) (maximalIdeal (Rsh i))
      (algebraMap (R i) (Rsh i)) (maximalIdeal_comap (algebraMap (R i) (Rsh i))).symm r]
    exact RingHom.congr_fun (H i).residueFieldEquiv_comp _
  simp only [residueToΩ, RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom,
    residueFieldEquivIdeal_residue]
  rw [← h1, RingEquiv.symm_apply_apply]
  rfl

omit [IsSepClosed Ω] in
include hf hω in
/-- For `i ≤ j`, the separable closure of `κ(R_i)` in `Ω` is contained in that of `κ(R_j)`. -/
theorem separableClosure_le {i j : ι} (hij : i ≤ j) (x : Ω)
    (hx : x ∈ separableClosure (maximalIdeal (R i)).ResidueField Ω) :
    x ∈ separableClosure (maximalIdeal (R j)).ResidueField Ω := by
  have := hf i j hij
  let : Algebra (maximalIdeal (R i)).ResidueField (maximalIdeal (R j)).ResidueField :=
    (Ideal.ResidueField.map (maximalIdeal (R i)) (maximalIdeal (R j)) (f i j hij)
      (maximalIdeal_comap (f i j hij)).symm).toAlgebra
  have : IsScalarTower (maximalIdeal (R i)).ResidueField (maximalIdeal (R j)).ResidueField Ω := by
    refine IsScalarTower.of_algebraMap_eq fun y => ?_
    obtain ⟨r, rfl⟩ := Ideal.algebraMap_residueField_surjective (maximalIdeal (R i)) y
    rw [RingHom.algebraMap_toAlgebra, Ideal.ResidueField.map_algebraMap, hω]
  rw [mem_separableClosure_iff] at hx ⊢
  exact IsSeparable.tower_top _ hx

/-- The inclusion `κ_i^{sep} ⊆ κ_j^{sep}` inside `Ω`. -/
def sepClosureInclusion {i j : ι} (hij : i ≤ j) :
    separableClosure (maximalIdeal (R i)).ResidueField Ω →+*
      separableClosure (maximalIdeal (R j)).ResidueField Ω where
  toFun x := ⟨x.1, separableClosure_le f hf hω hij x.1 x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The map of residue fields `κ(R_i^{sh}) = κ_i^{sep} ⊆ κ_j^{sep} = κ(R_j^{sh})`. -/
def residueMap {i j : ι} (hij : i ≤ j) : ResidueField (Rsh i) →+* ResidueField (Rsh j) :=
  ((residueFieldEquivIdeal (Rsh j)).symm : (maximalIdeal (Rsh j)).ResidueField →+* _).comp
    (((H j).residueFieldEquiv : _ →+* (maximalIdeal (Rsh j)).ResidueField).comp
      ((sepClosureInclusion f hf hω hij).comp
        (((H i).residueFieldEquiv.symm : (maximalIdeal (Rsh i)).ResidueField →+* _).comp
          (residueFieldEquivIdeal (Rsh i) : ResidueField (Rsh i) →+* _))))

/-- `residueMap` is compatible with the maps to `Ω`. -/
theorem residueToΩ_residueMap {i j : ι} (hij : i ≤ j) (y : ResidueField (Rsh i)) :
    residueToΩ H j (residueMap f hf hω H hij y) = residueToΩ H i y := by
  simp only [residueToΩ, residueMap, RingHom.coe_comp, Function.comp_apply,
    RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, RingEquiv.symm_apply_apply]
  rfl

/-- The residue square of Stacks 04GU for `residueMap`. -/
theorem residueMap_comp {i j : ι} (hij : i ≤ j) :
    (residueMap f hf hω H hij).comp ((residue (Rsh i)).comp (algebraMap (R i) (Rsh i))) =
      (residue (Rsh j)).comp ((algebraMap (R j) (Rsh j)).comp (f i j hij)) := by
  refine RingHom.ext fun r => residueToΩ_injective H j ?_
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [residueToΩ_residueMap, residueToΩ_residue_algebraMap, residueToΩ_residue_algebraMap, hω]

/-- **The transition map `R_i^{sh} → R_j^{sh}`**: the local ring map of Stacks 04GU over
`f_{ij}` inducing the inclusion `κ_i^{sep} ⊆ κ_j^{sep}` on residue fields. -/
def transition (i j : ι) (hij : i ≤ j) : Rsh i →+* Rsh j :=
  haveI := (H j).henselian
  mapOfResidue (H i).isFilteredColimitEtale ((algebraMap (R j) (Rsh j)).comp (f i j hij))
    (residueMap f hf hω H hij) (residueMap_comp f hf hω H hij)

/-- The transition maps lie over the `f_{ij}`. -/
theorem transition_algebraMap {i j : ι} (hij : i ≤ j) (x : R i) :
    transition f hf hω H i j hij (algebraMap (R i) (Rsh i) x) =
      algebraMap (R j) (Rsh j) (f i j hij x) :=
  haveI := (H j).henselian
  RingHom.congr_fun (mapOfResidue_comp_algebraMap _ _ _ _) x

/-- The transition maps are local. -/
theorem isLocalHom_transition {i j : ι} (hij : i ≤ j) :
    IsLocalHom (transition f hf hω H i j hij) :=
  haveI := (H j).henselian
  isLocalHom_mapOfResidue _ _ _ _

/-- The transition maps are compatible with the residue maps to `Ω`. -/
theorem residueToΩ_transition {i j : ι} (hij : i ≤ j) (y : Rsh i) :
    residueToΩ H j (residue (Rsh j) (transition f hf hω H i j hij y)) =
      residueToΩ H i (residue (Rsh i) y) := by
  have := (H j).henselian
  have h := RingHom.congr_fun (residue_comp_mapOfResidue (H i).isFilteredColimitEtale
    ((algebraMap (R j) (Rsh j)).comp (f i j hij)) (residueMap f hf hω H hij)
    (residueMap_comp f hf hω H hij)) y
  simp only [RingHom.coe_comp, Function.comp_apply] at h
  rw [transition, h, residueToΩ_residueMap]

/-- **Uniqueness of the transition maps** (the uniqueness half of Stacks 04GU): a local ring map
`R_i^{sh} → R_j^{sh}` over `f_{ij}` compatible with the residue maps to `Ω` is the transition
map. -/
theorem eq_transition {i j : ι} (hij : i ≤ j) (h : Rsh i →+* Rsh j)
    (hcomm : ∀ x, h (algebraMap (R i) (Rsh i) x) = algebraMap (R j) (Rsh j) (f i j hij x))
    (hloc : IsLocalHom h)
    (hres : ∀ y, residueToΩ H j (residue (Rsh j) (h y)) = residueToΩ H i (residue (Rsh i) y)) :
    h = transition f hf hω H i j hij := by
  have := (H j).henselian
  refine eq_mapOfResidue _ _ _ _ h (RingHom.ext hcomm) hloc (RingHom.ext fun y => ?_)
  refine residueToΩ_injective H j ?_
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [hres, residueToΩ_residueMap]

/-- **The transition maps form a directed system.** The identity of `R_i^{sh}` and the
composite `R_i^{sh} → R_j^{sh} → R_k^{sh}` satisfy the characterization of
`eq_transition`. -/
theorem directedSystem_transition [DirectedSystem R fun i j h => f i j h] :
    DirectedSystem Rsh fun i j h => transition f hf hω H i j h := by
  refine ⟨fun i x => ?_, fun k j i hij hjk x => ?_⟩
  · have hid : RingHom.id (Rsh i) = transition f hf hω H i i le_rfl := by
      refine eq_transition f hf hω H le_rfl _ (fun x => ?_) inferInstance fun y => rfl
      have hfx : f i i le_rfl x = x := DirectedSystem.map_self (f := fun i j h => f i j h) x
      rw [RingHom.id_apply, hfx]
    exact (RingHom.congr_fun hid x).symm
  · have hcomp : (transition f hf hω H j k hjk).comp (transition f hf hω H i j hij) =
        transition f hf hω H i k (hij.trans hjk) := by
      have := isLocalHom_transition f hf hω H hij
      have := isLocalHom_transition f hf hω H hjk
      refine eq_transition f hf hω H (hij.trans hjk) _ (fun x => ?_) inferInstance fun y => ?_
      · have hfx : f j k hjk (f i j hij x) = f i k (hij.trans hjk) x :=
          DirectedSystem.map_map (f := fun i j h => f i j h) hij hjk x
        rw [RingHom.comp_apply, transition_algebraMap, transition_algebraMap, hfx]
      · rw [RingHom.comp_apply, residueToΩ_transition, residueToΩ_transition]
    exact RingHom.congr_fun hcomp x

end System

/-- **A compatible system of strict henselizations** (Stacks 04GP and 04GU). Let `(R_i, f_{ij})`
be a directed system of local rings along local homomorphisms, and let `Ω` be a separably closed
field with maps `κ(R_i) → Ω` compatible with the residue field maps of the `f_{ij}`. Then there
are strict henselizations `R_i → R_i^{sh}`, with respect to separable algebraic closures
`κ_i^{sep}` of the residue fields (the separable closures of `κ(R_i)` in `Ω`), and ring maps
`R_i^{sh} → R_j^{sh}` over the `f_{ij}` forming a directed system. -/
theorem exists_directedSystem_isStrictHenselization {ι : Type w} [Preorder ι]
    {R : ι → Type u} [∀ i, CommRing (R i)] [∀ i, IsLocalRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j) [DirectedSystem R fun i j h => f i j h]
    (hf : ∀ i j h, IsLocalHom (f i j h))
    (Ω : Type v) [Field Ω] [IsSepClosed Ω] [∀ i, Algebra (maximalIdeal (R i)).ResidueField Ω]
    (hω : ∀ i j (h : i ≤ j) (r : R i),
      algebraMap _ Ω (algebraMap (R j) (maximalIdeal (R j)).ResidueField (f i j h r)) =
        algebraMap _ Ω (algebraMap (R i) (maximalIdeal (R i)).ResidueField r)) :
    ∃ (Rsh : ι → Type u) (_ : ∀ i, CommRing (Rsh i)) (_ : ∀ i, IsLocalRing (Rsh i))
      (_ : ∀ i, Algebra (R i) (Rsh i)) (κsep : ι → Type v) (_ : ∀ i, Field (κsep i))
      (_ : ∀ i, Algebra (maximalIdeal (R i)).ResidueField (κsep i))
      (_ : ∀ i, IsSepClosure (maximalIdeal (R i)).ResidueField (κsep i))
      (fsh : ∀ i j, i ≤ j → Rsh i →+* Rsh j),
      DirectedSystem Rsh (fun i j h => fsh i j h) ∧
        (∀ i, Nonempty (IsStrictHenselization (R i) (κsep i) (Rsh i))) ∧
        ∀ i j (hij : i ≤ j) x,
          fsh i j hij (algebraMap (R i) (Rsh i) x) = algebraMap (R j) (Rsh j) (f i j hij x) := by
  choose Rsh ring loc alg hsh using fun i =>
    exists_isStrictHenselization (R i) (separableClosure (maximalIdeal (R i)).ResidueField Ω)
  let H : ∀ i, IsStrictHenselization (R i)
      (separableClosure (maximalIdeal (R i)).ResidueField Ω) (Rsh i) := fun i => (hsh i).some
  exact ⟨Rsh, ring, loc, alg, fun i => separableClosure (maximalIdeal (R i)).ResidueField Ω,
    inferInstance, inferInstance, inferInstance, transition f hf hω H,
    directedSystem_transition f hf hω H, hsh,
    fun i j hij x => transition_algebraMap f hf hω H hij x⟩

end Stacks.StrictHenselization.CompatibleSystem

end
