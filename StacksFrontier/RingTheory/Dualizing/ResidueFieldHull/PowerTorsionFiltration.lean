module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.Algebra.Module.InjectiveHull.Basic
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Dualizing.Artinian
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingFlatIsomorphism

/-!
# Injective hulls of the residue field: descent to quotients and the power-torsion filtration

Let `R` be a Noetherian local ring with maximal ideal `𝔪` and residue field `κ`, and let `E` be an
injective hull of `κ` as an `R`-module, presented by an essential monomorphism `i : κ ⟶ E` in
`ModuleCat R`.  This file shows that injective hulls descend along a surjection of rings, that
the submodules `E[𝔪^(n+1)]` are injective hulls of `κ` over `R / 𝔪^(n+1)` and exhaust `E`, and
that an `𝔪`-power torsion module whose socle has finite dimension `n` over `κ` embeds into `E^n`.

It was split from `StacksFrontier.RingTheory.Dualizing.ResidueFieldHull`, which re-exports it.

## Main definitions

* `Dualizing.kernelTorsion` and `Dualizing.kernelTorsionInclusion` — the submodule of `E`
  annihilated by the kernel of a surjection `R →+* S`, as an `S`-module, and the canonical
  factorization of `i` through it.
* `Dualizing.maximalIdealPowTorsion` and
  `Dualizing.residueFieldToMaximalIdealPowTorsion` — the filtration `E[𝔪^(n+1)]` of `E` and the
  induced residue-field inclusions.

## Main results

* `Dualizing.isInjectiveHull_kernelTorsion_of_surjective` — injective hulls descend along a
  surjection of rings.
* `Dualizing.maximalIdealPowTorsion_isInjectiveHull` and
  `Dualizing.iSup_maximalIdealPowTorsion_eq_top` — the filtration consists of injective hulls over
  the quotient rings, and exhausts `E`.
* `Dualizing.exists_injective_to_pi_injectiveHull` — a torsion module with `n`-dimensional socle
  embeds into `E^n`.

## Implementation notes

The source of Tag 08Z4 identifies an independently named injective hull `E_n` over `R / 𝔪^(n+1)`
with `E[𝔪^(n+1)]`; since independently chosen hulls are only isomorphic, the submodule of `E` is
taken as the definition and the identification becomes a theorem.  Natural numbers index the
positive powers, so index `n` corresponds to exponent `n + 1`.

## References

* [Stacks Project, Tag 08Z2](https://stacks.math.columbia.edu/tag/08Z2)
* [Stacks Project, Tag 08Z3](https://stacks.math.columbia.edu/tag/08Z3)
* [Stacks Project, Tag 08Z4](https://stacks.math.columbia.edu/tag/08Z4)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace Dualizing

section QuotientRing

/-- The submodule `E[RingHom.ker f]`, with its module structure over the
codomain of a surjective ring homomorphism. -/
public noncomputable def kernelTorsion {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Surjective f)
    (E : ModuleCat.{w} R) : ModuleCat.{w} S :=
  letI : Module S (Submodule.torsionBySet R E (RingHom.ker f)) :=
    Module.compHom _ (RingHom.quotientKerEquivOfSurjective hf).symm.toRingHom
  ModuleCat.of S (Submodule.torsionBySet R E (RingHom.ker f))

/-- The canonical factorization through the submodule annihilated by the
kernel. Its composite with the subtype inclusion is the original map. -/
public noncomputable def kernelTorsionInclusion
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f)
    {K : ModuleCat.{w} S} {E : ModuleCat.{w} R}
    (i : (ModuleCat.restrictScalars.{w} f).obj K ⟶ E) :
    K ⟶ kernelTorsion f hf E := by
  letI : Module S (Submodule.torsionBySet R E (RingHom.ker f)) :=
    Module.compHom _ (RingHom.quotientKerEquivOfSurjective hf).symm.toRingHom
  have hmem (x : K) : i.hom x ∈ Submodule.torsionBySet R E (RingHom.ker f) := by
    rw [Submodule.mem_torsionBySet_iff]; intro ⟨r, hr⟩
    change r • i.hom x = 0
    calc
      r • i.hom x = i.hom (r • (show (ModuleCat.restrictScalars f).obj K from x)) :=
        (i.hom.map_smul r _).symm
      _ = 0 := by
        rw [ModuleCat.restrictScalars.smul_def, (RingHom.mem_ker).mp hr, zero_smul]
        exact i.hom.map_zero
  let j : K →ₗ[S] (kernelTorsion f hf E) :=
    { toFun := fun x => ⟨i.hom x, hmem x⟩
      map_add' := fun x y => Subtype.ext (map_add i.hom x y)
      map_smul' := by
        intro s x; apply Subtype.ext
        obtain ⟨r, rfl⟩ := hf s
        change i.hom (f r • x) = _
        calc
          i.hom (f r • x) = r • i.hom x := by
            change i.hom (r • (show (ModuleCat.restrictScalars f).obj K from x)) = _
            exact i.hom.map_smul r _
          _ = _ := by
            change r • i.hom x =
              (( ((RingHom.quotientKerEquivOfSurjective hf).symm (f r)) •
                (⟨i.hom x, hmem x⟩ : Submodule.torsionBySet R E (RingHom.ker f)) :
                Submodule.torsionBySet R E (RingHom.ker f)) : E)
            rw [RingHom.quotientKerEquivOfSurjective_symm_apply]
            simp only [Submodule.torsionBySet.mk_smul, Submodule.coe_smul] }
  exact ModuleCat.ofHom j

/-- The kernel-torsion inclusion has the same underlying value in `E` as the
original map. -/
@[simp]
public theorem kernelTorsionInclusion_apply
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f)
    {K : ModuleCat.{w} S} {E : ModuleCat.{w} R}
    (i : (ModuleCat.restrictScalars.{w} f).obj K ⟶ E) (x : K) :
    ((show Submodule.torsionBySet R E (RingHom.ker f) from
      (kernelTorsionInclusion f hf i).hom x) : E) = i.hom x := by
  unfold kernelTorsionInclusion; rfl

/-- The canonical factorization through the kernel-annihilated submodule is a
monomorphism whenever the original map is. -/
public instance mono_kernelTorsionInclusion
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f)
    {K : ModuleCat.{w} S} {E : ModuleCat.{w} R}
    (i : (ModuleCat.restrictScalars.{w} f).obj K ⟶ E) [Mono i] :
    Mono (kernelTorsionInclusion f hf i) := by
  rw [ModuleCat.mono_iff_injective]; intro x y h
  apply (ModuleCat.mono_iff_injective i).mp (inferInstance : Mono i)
  simpa only [kernelTorsionInclusion_apply] using congrArg Subtype.val h

private noncomputable def kernelTorsionToE
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (E : ModuleCat.{w} R) :
    (ModuleCat.restrictScalars.{w} f).obj (kernelTorsion f hf E) ⟶ E := by
  letI : Module S (Submodule.torsionBySet R E (RingHom.ker f)) :=
    Module.compHom _ (RingHom.quotientKerEquivOfSurjective hf).symm.toRingHom
  exact
  ModuleCat.ofHom (X := (ModuleCat.restrictScalars f).obj (kernelTorsion f hf E)) (Y := E)
    { toFun := fun x => (x : Submodule.torsionBySet R E (RingHom.ker f)).1
      map_add' := by intro x y; rfl
      map_smul' := by
        intro r x
        change ((((RingHom.quotientKerEquivOfSurjective hf).symm (f r)) •
          (show Submodule.torsionBySet R E (RingHom.ker f) from x) :
          Submodule.torsionBySet R E (RingHom.ker f)) : E) =
          r • ((show Submodule.torsionBySet R E (RingHom.ker f) from x) : E)
        rw [RingHom.quotientKerEquivOfSurjective_symm_apply]
        rw [Submodule.torsionBySet.mk_smul]
        rfl }

private theorem injective_kernelTorsion
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (E : ModuleCat.{w} R)
    (hE : Injective E) : Injective (kernelTorsion f hf E) := by
  refine ⟨?_⟩; intro X Y g j hj
  let jR := (ModuleCat.restrictScalars.{w} f).map j
  let gR := (ModuleCat.restrictScalars.{w} f).map g ≫ kernelTorsionToE f hf E
  have hjR : Mono jR := inferInstance
  obtain ⟨hR, hhR⟩ := @Injective.factors _ _ E hE _ _ gR jR hjR
  refine ⟨kernelTorsionInclusion f hf hR, ?_⟩
  ext x
  apply Subtype.ext
  have h := congrArg (fun k : (ModuleCat.restrictScalars f).obj X ⟶ E => k.hom x) hhR
  change hR.hom (j.hom x) = (g.hom x : Submodule.torsionBySet R E (RingHom.ker f)).1 at h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply,
    kernelTorsionInclusion_apply] using h

private theorem essentialMono_iff_nonzero_multiple
    {R : Type u} [Ring R] {M N : ModuleCat.{w} R}
    (i : M ⟶ N) [Mono i] :
    Module.IsEssentialMono i ↔
      ∀ x : N, x ≠ 0 → ∃ r : R, r • x ∈ LinearMap.range i.hom ∧ r • x ≠ 0 := by
  let e := ModuleCat.subobjectModule N
  have hImage : e (Subobject.mk i) = LinearMap.range i.hom :=
    subobjectModule_mk_eq_range i
  constructor
  · intro hi x hx
    let P : Submodule R N := R ∙ x
    have hP : P ≠ ⊥ := by simpa [P, Submodule.span_singleton_eq_bot] using hx
    have hmeet := hi (e.symm P) (by simpa using hP)
    have hmeet' : P ⊓ LinearMap.range i.hom ≠ ⊥ := fun hz => hmeet <| e.injective <| by
      rwa [OrderIso.map_inf, e.apply_symm_apply, hImage, e.map_bot]
    obtain ⟨y, hy⟩ := Submodule.nonzero_mem_of_bot_lt
      ((bot_lt_iff_ne_bot).2 hmeet')
    obtain ⟨hyP, hyI⟩ := Submodule.mem_inf.mp y.2
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hyP
    have hy0 : y.1 ≠ 0 := fun hz => hy (Subtype.ext hz)
    exact ⟨r, by simpa [hr] using hyI, by simpa [hr] using hy0⟩
  · intro hi B hB hbot
    have hbot' := congrArg e hbot
    rw [OrderIso.map_inf, hImage, e.map_bot] at hbot'
    have hB' : e B ≠ ⊥ := by simpa using hB
    obtain ⟨x, hx⟩ := Submodule.nonzero_mem_of_bot_lt
      ((bot_lt_iff_ne_bot).2 hB')
    have hx0 : x.1 ≠ 0 := fun hz => hx (Subtype.ext hz)
    obtain ⟨r, hrI, hr0⟩ := hi x.1 hx0
    have hmem : r • x.1 ∈ e B ⊓ LinearMap.range i.hom := ⟨Submodule.smul_mem _ r x.2, hrI⟩
    rw [hbot'] at hmem
    exact hr0 (by simpa using hmem)

/-- **Stacks Project, Tag 08Z2.** For a surjective ring homomorphism, the
submodule of an injective hull annihilated by the kernel is an injective hull
over the quotient ring. -/
@[stacks 08Z2]
public theorem isInjectiveHull_kernelTorsion_of_surjective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f)
    {K : ModuleCat.{w} S} {E : ModuleCat.{w} R}
    (i : (ModuleCat.restrictScalars.{w} f).obj K ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    Module.IsInjectiveHull (kernelTorsionInclusion f hf i) := by
  refine ⟨injective_kernelTorsion f hf E hi.1, ?_⟩
  apply (essentialMono_iff_nonzero_multiple (kernelTorsionInclusion f hf i)).2
  intro x hx
  have hxE : ((show Submodule.torsionBySet R E (RingHom.ker f) from x) : E) ≠ 0 :=
    fun hz => hx (Subtype.ext hz)
  obtain ⟨r, ⟨k, hk⟩, hr0⟩ :=
    (essentialMono_iff_nonzero_multiple i).1 hi.2 _ hxE
  have hsmul :
      ((show Submodule.torsionBySet R E (RingHom.ker f) from f r • x) : E) =
        r • ((show Submodule.torsionBySet R E (RingHom.ker f) from x) : E) :=
    (kernelTorsionToE f hf E).hom.map_smul r x
  refine ⟨f r, ?_, ?_⟩
  · change ∃ k : K, (kernelTorsionInclusion f hf i).hom k = f r • x
    refine ⟨k, Subtype.ext ?_⟩
    rw [hsmul]
    exact (kernelTorsionInclusion_apply f hf i k).trans hk
  · exact fun hz => hr0 (hsmul.symm.trans (congrArg Subtype.val hz))

end QuotientRing

section PowerTorsionFiltration



private theorem essentialMono_of_subobject_le
    {C : Type*} [Category C] [Limits.HasZeroObject C] [Limits.HasPullbacks C]
    {K P E : C} (i : K ⟶ E) (j : P ⟶ E) [Mono i] [Mono j]
    (hi : Module.IsEssentialMono i)
    (hij : Subobject.mk i ≤ Subobject.mk j) :
    Module.IsEssentialMono j := by
  intro q hq hj
  exact hi q hq (le_bot_iff.mp ((inf_le_inf_left q hij).trans_eq hj))


/-- The submodule of `E` annihilated by the `(n + 1)`-st power of the maximal ideal. -/
public abbrev maximalIdealPowTorsion (R : Type u) [CommRing R] [IsLocalRing R]
    (E : ModuleCat.{v} R) (n : ℕ) : Submodule R E :=
  Submodule.torsionBySet R E ((IsLocalRing.maximalIdeal R) ^ (n + 1) : Ideal R)

/-- The residue field is annihilated by every positive power of the maximal ideal. This witness
supplies its canonical module structure over the corresponding quotient ring. -/
public abbrev residueFieldIsTorsionByMaximalIdealPow
    (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) :
    Module.IsTorsionBySet R (IsLocalRing.ResidueField R)
      ((IsLocalRing.maximalIdeal R) ^ (n + 1) : Ideal R) :=
  fun x a ↦ by
    rw [Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq,
      (IsLocalRing.residue_eq_zero_iff (a : R)).2
      (Ideal.pow_le_self (Nat.succ_ne_zero n) a.property), zero_mul]

/-- Any module identified with the residue field is annihilated by every positive power of the
maximal ideal. -/
public abbrev residueFieldModelIsTorsionByMaximalIdealPow
    (R : Type u) [CommRing R] [IsLocalRing R] (K : ModuleCat.{v} R)
    (e : IsLocalRing.ResidueField R ≃ₗ[R] K) (n : ℕ) :
    Module.IsTorsionBySet R K
      ((IsLocalRing.maximalIdeal R) ^ (n + 1) : Ideal R) :=
  fun x a ↦ by
    rw [← e.apply_symm_apply x, ← e.map_smul]
    simpa using congrArg e
      (@residueFieldIsTorsionByMaximalIdealPow R _ _ n (e.symm x) a)

/-- The canonical map from the residue field into the submodule annihilated by a positive power
of the maximal ideal, induced by its map into `E`. -/
public noncomputable def residueFieldToMaximalIdealPowTorsion
    (R : Type u) [CommRing R] [IsLocalRing R]
    {K E : ModuleCat.{v} R} (e : IsLocalRing.ResidueField R ≃ₗ[R] K)
    (i : K ⟶ E) (n : ℕ) :
    let hK := residueFieldModelIsTorsionByMaximalIdealPow R K e n
    letI := hK.module
    K →ₗ[R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1)]
      maximalIdealPowTorsion R E n := by
  let hK := residueFieldModelIsTorsionByMaximalIdealPow R K e n
  letI := hK.module
  exact
    { toFun := fun x ↦ ⟨i.hom x, by
        rw [Submodule.mem_torsionBySet_iff]
        intro a
        rw [← i.hom.map_smul]
        exact (congrArg i.hom <| @hK x a).trans i.hom.map_zero⟩
      map_add' := fun _ _ ↦ Subtype.ext (i.hom.map_add _ _)
      map_smul' := fun q x ↦ Quotient.inductionOn' q fun r ↦
        Subtype.ext (i.hom.map_smul r x) }

/-- Injectivity of the canonical residue-field map is inherited from the map into `E`. -/
public abbrev residueFieldToMaximalIdealPowTorsion_injective
    (R : Type u) [CommRing R] [IsLocalRing R]
    {K E : ModuleCat.{v} R} (e : IsLocalRing.ResidueField R ≃ₗ[R] K)
    (i : K ⟶ E) (hi : Function.Injective i.hom) (n : ℕ) :
    Function.Injective (residueFieldToMaximalIdealPowTorsion R e i n) :=
  fun _ _ h ↦ by
    apply hi
    have h' := congrArg Subtype.val h
    dsimp only [residueFieldToMaximalIdealPowTorsion] at h'
    exact h'

private theorem injectiveHull_comp_iso
    {C : Type*} [Category C] [Limits.HasZeroObject C] [Limits.HasPullbacks C]
    {A B B' : C}
    (i : A ⟶ B) [Mono i] (hi : Module.IsInjectiveHull i) (e : B ≅ B') :
    Module.IsInjectiveHull (i ≫ e.hom) := by
  refine ⟨Injective.of_iso e hi.1, ?_⟩
  let Φ := Subobject.mapIsoToOrderIso e
  intro q hq hzero
  let p := Φ.symm q
  have hp : p ≠ ⊥ := by
    intro hp0
    apply hq
    calc
      q = Φ p := (Φ.apply_symm_apply q).symm
      _ = Φ ⊥ := congrArg Φ hp0
      _ = ⊥ := Φ.map_bot
  apply hi.2 p hp
  apply Φ.injective
  calc
    Φ (p ⊓ Subobject.mk i) = Φ p ⊓ Φ (Subobject.mk i) := Φ.map_inf _ _
    _ = q ⊓ Subobject.mk (i ≫ e.hom) := by
      have hΦ : Φ (Subobject.mk i) = Subobject.mk (i ≫ e.hom) := by
        change (Subobject.map e.hom).obj (Subobject.mk i) = _
        exact Subobject.map_mk i e.hom
      rw [show Φ p = q from Φ.apply_symm_apply q, hΦ]
    _ = ⊥ := hzero
    _ = Φ ⊥ := Φ.map_bot.symm

private theorem primaryComponent_maximalIdeal_eq_iSup
    (R : Type u) [CommRing R] [IsLocalRing R] (E : ModuleCat.{v} R) :
    Ideal.primaryComponent E (IsLocalRing.maximalIdeal R) =
      ⨆ n : ℕ, maximalIdealPowTorsion R E n := by
  let m := IsLocalRing.maximalIdeal R
  have hm : Monotone (fun n : ℕ => Submodule.torsionBySet R E (m ^ n : Ideal R)) :=
    fun a b hab => Submodule.torsionBySet_le_torsionBySet_pow a b hab m
  simpa only [Ideal.primaryComponent, maximalIdealPowTorsion, m] using
    (hm.iSup_nat_add 1).symm

/-- **Stacks Project, Tag 08Z4.** The submodule of an injective hull of the residue field
annihilated by a positive power of the maximal ideal is an injective hull over the corresponding
quotient ring. This is the canonical realization of the source's equality
`E_n = E[𝔪^(n + 1)]`. -/
@[stacks 08Z4 "the submodules E_n"]
public theorem maximalIdealPowTorsion_isInjectiveHull
    (R : Type u) [CommRing R] [IsLocalRing R]
    (K E : ModuleCat.{v} R) (e : IsLocalRing.ResidueField R ≃ₗ[R] K)
    (i : K ⟶ E) [Mono i]
    (hE : Module.IsInjectiveHull i) (n : ℕ) :
    let hK := residueFieldModelIsTorsionByMaximalIdealPow R K e n
    letI := hK.module
    let j := residueFieldToMaximalIdealPowTorsion R e i n
    letI : Mono (ModuleCat.ofHom j) :=
      (ModuleCat.mono_iff_injective _).2
        (residueFieldToMaximalIdealPowTorsion_injective R e i
          ((ModuleCat.mono_iff_injective i).1 (by infer_instance)) n)
    Module.IsInjectiveHull (ModuleCat.ofHom j) := by
  let I : Ideal R := (IsLocalRing.maximalIdeal R) ^ (n + 1)
  let hK := residueFieldModelIsTorsionByMaximalIdealPow R K e n
  let : Module (R ⧸ I) K := hK.module
  let f : R →+* R ⧸ I := Ideal.Quotient.mk I
  let Kq : ModuleCat.{v} (R ⧸ I) := ModuleCat.of (R ⧸ I) K
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  let kEquiv : (ModuleCat.restrictScalars f).obj Kq ≃ₗ[R] K :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        change (Ideal.Quotient.mk I r • x : K) = r • x
        exact Module.IsTorsionBySet.mk_smul hK r x }
  let kIso : (ModuleCat.restrictScalars f).obj Kq ≅ K := kEquiv.toModuleIso
  let iq : (ModuleCat.restrictScalars f).obj Kq ⟶ E := kIso.hom ≫ i
  have hiqEq : kIso.hom ≫ i = iq := rfl
  have : Mono iq := by
    rw [← hiqEq]
    infer_instance
  have hiq : Module.IsInjectiveHull iq := ⟨hE.1, fun q hq => by
    change q ⊓ Subobject.mk iq ≠ ⊥
    rw [Subobject.mk_eq_mk_of_comm iq i kIso hiqEq]
    exact hE.2 q hq⟩
  have hq : Module.IsInjectiveHull (kernelTorsionInclusion f hf iq) :=
    isInjectiveHull_kernelTorsion_of_surjective f hf iq hiq
  let T : Submodule R E := maximalIdealPowTorsion R E n
  have hker : RingHom.ker f = I := Ideal.mk_ker
  have hUT : Submodule.torsionBySet R E (RingHom.ker f) = T := by
    rw [hker]
  let tEquiv : kernelTorsion f hf E ≃ₗ[R ⧸ I] ModuleCat.of (R ⧸ I) T :=
    { toFun := fun x => ⟨x.1, by
        rw [← hUT]
        exact x.prop⟩
      invFun := fun x => ⟨x.1, by
        change x.1 ∈ Submodule.torsionBySet R E (RingHom.ker f)
        rw [hUT]
        exact x.prop⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun q x => by
        induction q using Quotient.inductionOn' with
        | h r =>
          apply Subtype.ext
          let xt : T := ⟨(x : Submodule.torsionBySet R E (RingHom.ker f)).1, by
            rw [← hUT]; exact (x : Submodule.torsionBySet R E (RingHom.ker f)).prop⟩
          have ht : (Ideal.Quotient.mk I r : R ⧸ I) • xt = r • xt :=
            Submodule.torsionBySet.mk_smul I r xt
          exact ((kernelTorsionToE f hf E).hom.map_smul r x).trans
            (congrArg (fun y : T => (y : E)) ht).symm }
  let tIso : kernelTorsion f hf E ≅ ModuleCat.of (R ⧸ I) T :=
    tEquiv.toModuleIso
  let j0 := residueFieldToMaximalIdealPowTorsion R e i n
  have jEq : kernelTorsionInclusion f hf iq ≫ tIso.hom =
      ModuleCat.ofHom j0 := by
    ext x
    simp [j0, tIso, tEquiv, kIso, kEquiv, iq,
      residueFieldToMaximalIdealPowTorsion, Function.comp_apply]
    rfl
  have : Mono (ModuleCat.ofHom j0) := by rw [← jEq]; infer_instance
  change Module.IsInjectiveHull (ModuleCat.ofHom j0)
  have hcomp := injectiveHull_comp_iso _ hq tIso
  exact ⟨hcomp.1, fun q hq0 => by simpa only [← jEq] using hcomp.2 q hq0⟩

/-- **Stacks Project, Tag 08Z4.** The submodules annihilated by positive powers of the maximal
ideal exhaust an injective hull of the residue field. -/
@[stacks 08Z4 "the union"]
public theorem iSup_maximalIdealPowTorsion_eq_top
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (K E : ModuleCat.{v} R) (e : IsLocalRing.ResidueField R ≃ₗ[R] K)
    (i : K ⟶ E) [Mono i]
    (hE : Module.IsInjectiveHull i) :
    (⨆ n : ℕ, maximalIdealPowTorsion R E n) = ⊤ := by
  let P : Submodule R E := Ideal.primaryComponent E (IsLocalRing.maximalIdeal R)
  have : Module.Injective R E := (Module.injective_iff_injective_object R E).mpr hE.1
  have hPInj : Module.Injective R P :=
    Module.injective_primaryComponent E (IsLocalRing.maximalIdeal R)
  have hmem (x : K) : i.hom x ∈ P := by
    change i.hom x ∈ Ideal.primaryComponent E (IsLocalRing.maximalIdeal R)
    rw [primaryComponent_maximalIdeal_eq_iSup]
    apply Submodule.mem_iSup_of_mem 0
    rw [Submodule.mem_torsionBySet_iff]
    intro a
    rw [← i.hom.map_smul]
    exact (congrArg i.hom
      (@residueFieldModelIsTorsionByMaximalIdealPow R _ _ K e 0 x a)).trans
      i.hom.map_zero
  let g : K ⟶ ModuleCat.of R P := ModuleCat.ofHom (i.hom.codRestrict P hmem)
  let j : ModuleCat.of R P ⟶ E := ModuleCat.ofHom P.subtype
  have : Mono j := (ModuleCat.mono_iff_injective j).2 P.subtype_injective
  have hfac : i = g ≫ j := by ext x; rfl
  have hIso : IsIso j := (Module.injective_iff_isIso_essentialMono R P).mp hPInj E j
    (essentialMono_of_subobject_le i j hE.2 (Subobject.mk_le_mk_of_comm g hfac))
  rw [← primaryComponent_maximalIdeal_eq_iSup]
  exact P.range_subtype.symm.trans
    (LinearMap.range_eq_top.mpr ((ConcreteCategory.isIso_iff_bijective j).mp hIso).2)

end PowerTorsionFiltration

section EmbedIntoHull

/-- **Stacks Project, Tag 08Z3.** A module which is power-torsion for the maximal ideal embeds
in the direct sum of as many copies of an injective hull of the residue field as the dimension
of its socle. -/
@[stacks 08Z3]
public theorem exists_injective_to_pi_injectiveHull
    (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type v) (E : Type u) [AddCommGroup M] [Module R M] [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ ModuleCat.of R E) [Mono i]
    (hi : Module.IsInjectiveHull i)
    (hM : ∀ x : M, ∃ e : ℕ, ∀ r ∈ (IsLocalRing.maximalIdeal R ^ e : Ideal R),
      r • x = 0)
    (n : ℕ)
    [Module.Finite (R ⧸ IsLocalRing.maximalIdeal R)
      (Submodule.torsionBySet R M (IsLocalRing.maximalIdeal R))]
    (hn : Module.finrank (R ⧸ IsLocalRing.maximalIdeal R)
      (Submodule.torsionBySet R M (IsLocalRing.maximalIdeal R)) = n) :
    ∃ f : M →ₗ[R] (Fin n → E), Function.Injective f := by
  let I : Ideal R := IsLocalRing.maximalIdeal R
  let K := R ⧸ IsLocalRing.maximalIdeal R
  let S : Submodule R M := Submodule.torsionBySet R M I
  let : Field K := IsLocalRing.ResidueField.field R
  let moduleKS : Module K S := by dsimp [K, S, I]; infer_instance
  let : Module K S := moduleKS
  let : Module.Free K S := @Module.Free.of_divisionRing K S _ _ moduleKS
  let : Module.Injective R E := (Module.injective_iff_injective_object R E).mpr hi.1
  let e : S ≃ₗ[K] (Fin n → K) :=
    LinearEquiv.ofFinrankEq S (Fin n → K) (by simpa [S, K, I, Module.finrank_pi] using hn)
  let g : S →ₗ[R] (Fin n → E) :=
    LinearMap.pi fun j => i.hom.comp (((LinearMap.proj j).comp e.toLinearMap).restrictScalars R)
  have hg : Function.Injective g := by
    intro x y hxy
    apply e.injective
    funext j
    exact (ModuleCat.mono_iff_injective i).mp inferInstance (congrFun hxy j)
  obtain ⟨f, hf⟩ := Module.Injective.extension_property R (Fin n → E)
    S M S.subtype S.subtype_injective g
  let T : Submodule R M := LinearMap.ker f
  have hT0 : Submodule.torsionBySet R T I = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hs : (x : M) ∈ S := (Submodule.mem_torsionBySet_iff _ _).mpr
      (fun a => congrArg Subtype.val ((Submodule.mem_torsionBySet_iff _ _).mp hx a))
    have hfg : g (⟨(x : M), hs⟩ : S) = 0 := by
      simpa [T, LinearMap.mem_ker.mp x.property] using
        (congrArg (fun h : S →ₗ[R] (Fin n → E) => h ⟨(x : M), hs⟩) hf).symm
    have he : (⟨(x : M), hs⟩ : S) = 0 := hg (by simpa using hfg)
    exact Subtype.ext (congrArg (fun y : S => (y : M)) he)
  refine ⟨f, (LinearMap.ker_eq_bot).mp ?_⟩
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨e, he⟩ := hM x
  have ht : (⟨x, hx⟩ : T) ∈
      Submodule.torsionBySet R T ((I ^ e : Ideal R) : Set R) :=
    (Submodule.mem_torsionBySet_iff _ _).mpr (fun a => Subtype.ext (he a a.property))
  rcases Nat.eq_zero_or_pos e with rfl | he0
  · simpa using he 1 (by simp)
  · rw [torsionBySet_pow_eq_bot I hT0 e he0] at ht
    exact congrArg Subtype.val ht

end EmbedIntoHull

end Dualizing
