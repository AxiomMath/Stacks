module

public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Algebra.Polynomial.Lifts

/-!
# The absolute Galois group of an intermediate field of a separable closure

Let `L` be a separable closure of a field `F`, `E` an intermediate field of `L/F`, and `Ω` a field
containing `L`. Let `κ` be a field embedded in `Ω` with image the image of `E`. Then `L` is
identified with the separable closure of `κ` in `Ω`, and the absolute Galois group
`Gal(κ^{sep}/κ)`, computed inside `Ω`, is the subgroup of `Gal(L/F)` fixing `E`, as topological
groups.

## Main results

* `Stacks.EtaleCohomology.sepClosureRingEquiv` — `L ≅ κ^{sep}`, through `L → Ω`.
* `Stacks.EtaleCohomology.sepClosureAutToGal` — the restriction map
  `Gal(κ^{sep}/κ) → Gal(L/F)`, continuous (`continuous_sepClosureAutToGal`), injective, with image
  the fixing subgroup of `E` (`mem_range_sepClosureAutToGal_iff`).
* `Stacks.EtaleCohomology.sepClosureAutHomeomorphFixingSubgroup` — the resulting homeomorphism
  `Gal(κ^{sep}/κ) ≃ₜ E.fixingSubgroup`, multiplicative
  (`sepClosureAutHomeomorphFixingSubgroup_mul`).
-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace Stacks.EtaleCohomology

/-- A polynomial whose coefficients lie in the image of `g` after `f` is the image of a polynomial
along `g`. -/
theorem exists_map_eq_map_of_coeff_mem_range {A B C : Type u} [CommRing A] [CommRing B]
    [CommRing C] (f : A →+* C) (g : B →+* C) (p : A[X])
    (hp : ∀ n, f (p.coeff n) ∈ Set.range g) : ∃ q : B[X], q.map g = p.map f :=
  (Polynomial.mem_lifts _).1 ((Polynomial.lifts_iff_coeff_lifts _).2 fun n => by
    simpa only [Polynomial.coeff_map] using hp n)

/-- **Separability descends along an inclusion of images.** If `x` is separable over a field `A`
inside `Ω` and the image of `A` in `Ω` lies in the image of a field `B`, then `x` is separable
over `B`. -/
theorem isSeparable_of_forall_mem_range {A B Ω : Type u} [Field A] [Field B] [Field Ω]
    [Algebra A Ω] [Algebra B Ω] (h : ∀ a : A, algebraMap A Ω a ∈ Set.range (algebraMap B Ω))
    {x : Ω} (hx : IsSeparable A x) : IsSeparable B x := by
  obtain ⟨q, hq⟩ := exists_map_eq_map_of_coeff_mem_range (algebraMap A Ω) (algebraMap B Ω)
    (minpoly A x) (fun n => h _)
  have hsep : q.Separable := (Polynomial.separable_map (algebraMap B Ω)).1 (by
    rw [hq]
    exact Polynomial.Separable.map (f := algebraMap A Ω) hx)
  have hroot : aeval x q = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, hq, ← eval₂_eq_eval_map, ← aeval_def, minpoly.aeval]
  exact hsep.of_dvd (minpoly.dvd B x hroot)

section SepClosure

variable {F L Ω κ : Type u} [Field F] [Field L] [Field Ω] [Field κ]
  [Algebra F L] [Algebra L Ω] [Algebra F Ω] [IsScalarTower F L Ω] [Algebra κ Ω]
  [IsSepClosed L] [Algebra.IsSeparable F L]
  (E : IntermediateField F L)
  (hE : ∀ z : Ω, z ∈ Set.range (algebraMap κ Ω) ↔ ∃ e ∈ E, algebraMap L Ω e = z)

omit [IsSepClosed L] [Algebra.IsSeparable F L] in
include hE in
/-- The image of `F` in `Ω` lies in the image of `κ`. -/
theorem algebraMap_mem_range_of_sepClosure (f : F) :
    algebraMap F Ω f ∈ Set.range (algebraMap κ Ω) :=
  (hE _).2 ⟨algebraMap F L f, E.algebraMap_mem f, (IsScalarTower.algebraMap_apply F L Ω f).symm⟩

omit [IsSepClosed L] in
include hE in
/-- Every element of `L` is separable over `κ` inside `Ω`. -/
theorem algebraMap_mem_separableClosure (l : L) :
    algebraMap L Ω l ∈ separableClosure κ Ω := by
  rw [mem_separableClosure_iff]
  refine isSeparable_of_forall_mem_range (algebraMap_mem_range_of_sepClosure E hE) ?_
  exact (Algebra.IsSeparable.isSeparable F l).map (IsScalarTower.toAlgHom F L Ω)
    (algebraMap L Ω).injective

omit [Algebra F Ω] [IsScalarTower F L Ω] [Algebra.IsSeparable F L] in
include hE in
/-- Every element of `Ω` separable over `κ` comes from `L`. -/
theorem exists_algebraMap_eq_of_mem_separableClosure {z : Ω} (hz : z ∈ separableClosure κ Ω) :
    ∃ l : L, algebraMap L Ω l = z := by
  have hκL : ∀ c : κ, algebraMap κ Ω c ∈ Set.range (algebraMap L Ω) := fun c => by
    obtain ⟨e, -, he⟩ := (hE (algebraMap κ Ω c)).1 ⟨c, rfl⟩
    exact ⟨e, he⟩
  have : Algebra.IsSeparable L (IntermediateField.adjoin L {z}) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable L Ω).2
      (isSeparable_of_forall_mem_range hκL hz)
  obtain ⟨l, hl⟩ := IsSepClosed.algebraMap_surjective L (IntermediateField.adjoin L {z})
    ⟨z, IntermediateField.mem_adjoin_simple_self L z⟩
  exact ⟨l, congrArg Subtype.val hl⟩

/-- **`L` is the separable closure of `κ` in `Ω`**, through `L → Ω`. -/
def sepClosureRingEquiv : L ≃+* separableClosure κ Ω :=
  RingEquiv.ofBijective ((algebraMap L Ω).codRestrict (separableClosure κ Ω).toSubalgebra
      (algebraMap_mem_separableClosure E hE))
    ⟨fun a b h => (algebraMap L Ω).injective (congrArg Subtype.val h), fun z => by
      obtain ⟨l, hl⟩ := exists_algebraMap_eq_of_mem_separableClosure E hE z.2
      exact ⟨l, Subtype.ext hl⟩⟩

/-- `sepClosureRingEquiv E hE l`, read in `Ω`, is the image of `l` under `L → Ω`. -/
theorem coe_sepClosureRingEquiv (l : L) :
    (sepClosureRingEquiv E hE l : Ω) = algebraMap L Ω l := rfl

include hE in
/-- An element of `E`, read in `κ^{sep}`, comes from `κ`. -/
theorem exists_sepClosureRingEquiv_eq_algebraMap {e : L} (he : e ∈ E) :
    ∃ c : κ, sepClosureRingEquiv E hE e = algebraMap κ (separableClosure κ Ω) c := by
  obtain ⟨c, hc⟩ := (hE (algebraMap L Ω e)).2 ⟨e, he, rfl⟩
  exact ⟨c, Subtype.ext hc.symm⟩

/-- The `F`-automorphism of `L` induced by a `κ`-automorphism of `κ^{sep}`. -/
def sepClosureAutToGalAux (σ : Gal(separableClosure κ Ω/κ)) : Gal(L/F) :=
  AlgEquiv.ofRingEquiv (f := (sepClosureRingEquiv E hE).trans
      (σ.toRingEquiv.trans (sepClosureRingEquiv E hE).symm)) (fun f => by
    obtain ⟨c, hc⟩ := exists_sepClosureRingEquiv_eq_algebraMap E hE (E.algebraMap_mem f)
    change (sepClosureRingEquiv E hE).symm (σ (sepClosureRingEquiv E hE (algebraMap F L f))) = _
    rw [hc, σ.commutes, ← hc, RingEquiv.symm_apply_apply])

/-- `sepClosureAutToGalAux E hE σ` is `σ` conjugated by `sepClosureRingEquiv E hE`. -/
theorem sepClosureAutToGalAux_apply (σ : Gal(separableClosure κ Ω/κ)) (l : L) :
    sepClosureAutToGalAux E hE σ l =
      (sepClosureRingEquiv E hE).symm (σ (sepClosureRingEquiv E hE l)) := rfl

/-- **The restriction map `Gal(κ^{sep}/κ) → Gal(L/F)`.** -/
def sepClosureAutToGal : Gal(separableClosure κ Ω / κ) →* Gal(L / F) where
  toFun := sepClosureAutToGalAux E hE
  map_one' := by
    ext l
    rw [sepClosureAutToGalAux_apply]
    exact (sepClosureRingEquiv E hE).symm_apply_apply l
  map_mul' σ τ := by
    ext l
    change sepClosureAutToGalAux E hE (σ * τ) l =
      sepClosureAutToGalAux E hE σ (sepClosureAutToGalAux E hE τ l)
    rw [sepClosureAutToGalAux_apply, sepClosureAutToGalAux_apply, sepClosureAutToGalAux_apply,
      RingEquiv.apply_symm_apply]
    rfl

/-- `sepClosureRingEquiv E hE` intertwines `sepClosureAutToGal E hE σ` with `σ`. -/
theorem sepClosureRingEquiv_sepClosureAutToGal (σ : Gal(separableClosure κ Ω/κ)) (l : L) :
    sepClosureRingEquiv E hE (sepClosureAutToGal E hE σ l) = σ (sepClosureRingEquiv E hE l) :=
  RingEquiv.apply_symm_apply _ _

/-- **The characterization of the restriction map**: `σ` and its image agree on `L ⊆ Ω`. -/
theorem algebraMap_sepClosureAutToGal (σ : Gal(separableClosure κ Ω/κ)) (l : L) :
    algebraMap L Ω (sepClosureAutToGal E hE σ l) =
      (σ ⟨algebraMap L Ω l, algebraMap_mem_separableClosure E hE l⟩ : Ω) :=
  congrArg Subtype.val (sepClosureRingEquiv_sepClosureAutToGal E hE σ l)

/-- The restriction map `Gal(κ^{sep}/κ) → Gal(L/F)` is injective. -/
theorem sepClosureAutToGal_injective : Function.Injective (sepClosureAutToGal E hE) := by
  intro σ τ h
  ext z
  obtain ⟨l, rfl⟩ := (sepClosureRingEquiv E hE).surjective z
  rw [← sepClosureRingEquiv_sepClosureAutToGal, ← sepClosureRingEquiv_sepClosureAutToGal, h]

/-- The `κ`-automorphism of `κ^{sep}` induced by an element of `Gal(L/F)` fixing `E`. -/
def sepClosureAutOfFixing (g : Gal(L/F)) (hg : ∀ e ∈ E, g e = e) :
    Gal(separableClosure κ Ω / κ) :=
  AlgEquiv.ofRingEquiv (f := (sepClosureRingEquiv E hE).symm.trans
      (g.toRingEquiv.trans (sepClosureRingEquiv E hE))) (fun c => by
    obtain ⟨e, he, hec⟩ := (hE (algebraMap κ Ω c)).1 ⟨c, rfl⟩
    have h1 : sepClosureRingEquiv E hE e = algebraMap κ (separableClosure κ Ω) c :=
      Subtype.ext hec
    change sepClosureRingEquiv E hE (g ((sepClosureRingEquiv E hE).symm
      (algebraMap κ (separableClosure κ Ω) c))) = _
    rw [← h1, RingEquiv.symm_apply_apply, hg e he])

/-- **The image of the restriction map is the fixing subgroup of `E`.** -/
theorem mem_range_sepClosureAutToGal_iff (g : Gal(L/F)) :
    g ∈ (sepClosureAutToGal E hE).range ↔ g ∈ E.fixingSubgroup := by
  constructor
  · rintro ⟨σ, rfl⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro e he
    obtain ⟨c, hc⟩ := exists_sepClosureRingEquiv_eq_algebraMap E hE he
    apply (sepClosureRingEquiv E hE).injective
    rw [sepClosureRingEquiv_sepClosureAutToGal, hc, σ.commutes]
  · intro hg
    rw [IntermediateField.mem_fixingSubgroup_iff] at hg
    refine ⟨sepClosureAutOfFixing E hE g hg, ?_⟩
    ext l
    change (sepClosureRingEquiv E hE).symm (sepClosureRingEquiv E hE
      (g ((sepClosureRingEquiv E hE).symm (sepClosureRingEquiv E hE l)))) = g l
    rw [RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]

/-- **The restriction map is continuous** for the Krull topologies. -/
theorem continuous_sepClosureAutToGal : Continuous (sepClosureAutToGal E hE) := by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  intro N hN
  rw [map_one, krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨E', hfin, hO⟩ := hN
  let b := Module.finBasis F E'
  let S : Set (separableClosure κ Ω) := Set.range fun i => sepClosureRingEquiv E hE (b i : L)
  have : Finite S := Set.finite_range _ |>.to_subtype
  have := IntermediateField.finiteDimensional_adjoin fun x (_ : x ∈ S) =>
    Algebra.IsIntegral.isIntegral (R := κ) x
  refine mem_nhds_iff.mpr ⟨(IntermediateField.adjoin κ S).fixingSubgroup, ?_,
    IntermediateField.fixingSubgroup_isOpen _,
    (IntermediateField.adjoin κ S).fixingSubgroup.one_mem⟩
  intro σ hσ
  apply hO
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  have hb : ∀ i, sepClosureAutToGal E hE σ (b i : L) = b i := fun i =>
    (sepClosureRingEquiv E hE).injective ((sepClosureRingEquiv_sepClosureAutToGal E hE σ _).trans
      (hσ _ (IntermediateField.subset_adjoin κ S ⟨i, rfl⟩)))
  intro x hx
  have hx' : x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : L) := by
    have h := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    rw [IntermediateField.coe_sum] at h
    exact h.symm
  rw [hx', map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hb]

/-- The restriction map onto the fixing subgroup of `E`, as an equivalence. -/
def sepClosureAutEquivFixingSubgroup : Gal(separableClosure κ Ω / κ) ≃ E.fixingSubgroup :=
  Equiv.ofBijective (fun σ => ⟨sepClosureAutToGal E hE σ,
      (mem_range_sepClosureAutToGal_iff E hE _).1 ⟨σ, rfl⟩⟩)
    ⟨fun σ τ h => sepClosureAutToGal_injective E hE (congrArg Subtype.val h), fun g => by
      obtain ⟨σ, hσ⟩ := (mem_range_sepClosureAutToGal_iff E hE g.1).2 g.2
      exact ⟨σ, Subtype.ext hσ⟩⟩

variable [IsSepClosed Ω]

/-- **`Gal(κ^{sep}/κ)` is the fixing subgroup of `E`, as topological spaces**: a continuous
bijection from a compact space to a Hausdorff one. -/
def sepClosureAutHomeomorphFixingSubgroup :
    Gal(separableClosure κ Ω / κ) ≃ₜ E.fixingSubgroup :=
  haveI : Algebra.IsIntegral F L := inferInstance
  haveI : T2Space Gal(L / F) := krullTopology_t2
  haveI : IsGalois κ (separableClosure κ Ω) := IsSepClosure.isGalois
  Continuous.homeoOfEquivCompactToT2 (f := sepClosureAutEquivFixingSubgroup E hE)
    ((continuous_sepClosureAutToGal E hE).subtype_mk _)

/-- The homeomorphism `sepClosureAutHomeomorphFixingSubgroup E hE` is the restriction map
`sepClosureAutToGal E hE`. -/
theorem coe_sepClosureAutHomeomorphFixingSubgroup (σ : Gal(separableClosure κ Ω/κ)) :
    (sepClosureAutHomeomorphFixingSubgroup E hE σ : Gal(L / F)) = sepClosureAutToGal E hE σ :=
  rfl

/-- The homeomorphism `sepClosureAutHomeomorphFixingSubgroup E hE` is multiplicative. -/
theorem sepClosureAutHomeomorphFixingSubgroup_mul (σ τ : Gal(separableClosure κ Ω/κ)) :
    sepClosureAutHomeomorphFixingSubgroup E hE (σ * τ) =
      sepClosureAutHomeomorphFixingSubgroup E hE σ *
        sepClosureAutHomeomorphFixingSubgroup E hE τ :=
  Subtype.ext ((sepClosureAutToGal E hE).map_mul σ τ)

end SepClosure

end Stacks.EtaleCohomology

end
