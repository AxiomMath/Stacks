module

public import Mathlib.Algebra.Colimit.Module
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import StacksCore.Algebra.Algebra.Basic

/-! ## Localization of a module as a directed colimit of away-localizations

For a commutative ring `R`, a multiplicative subset `S ⊆ R` and an `R`-module `M`, the
localization `S⁻¹M` is the directed colimit of the away-localizations `M_f = M[1/f]` over
`f ∈ S`, where `S` carries the divisibility preorder (`f ≤ g` iff `f ∣ g` in `R`) and the
transition map `M_f → M_g` for `f ∣ g` is the one induced by the universal property of
`M_f`.

This is Stacks 00CR.  Following the hint there, the colimit is identified with `S⁻¹M` by
showing that the canonical map `M → colim_{f ∈ S} M_f` satisfies the universal property of
the localization (`IsLocalizedModule`), so that `IsLocalizedModule.iso` produces the
equivalence.
-/

@[expose] public section

suppress_compilation

universe u v

/-! ### Invertible actions on direct limits -/

namespace Module.DirectLimit

variable {R ι : Type*} [CommSemiring R] [Preorder ι] {G : ι → Type*}
  [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)] [DecidableEq ι]
  {f : ∀ i j, i ≤ j → G i →ₗ[R] G j} [Nonempty ι] [IsDirectedOrder ι]
  [DirectedSystem G (f · · ·)]

/-- If `r : R` acts invertibly on a cofinal set of components of a directed system of
`R`-modules, then it acts invertibly on the direct limit. -/
theorem isUnit_algebraMap_end {r : R}
    (H : ∀ i, ∃ j, i ≤ j ∧ IsUnit (algebraMap R (Module.End R (G j)) r)) :
    IsUnit (algebraMap R (Module.End R (DirectLimit G f)) r) := by
  rw [Module.End.isUnit_iff]
  constructor
  · intro z₁ z₂ hz
    obtain ⟨i, x, y, rfl, rfl⟩ := exists_of₂ z₁ z₂
    simp only [Module.algebraMap_end_apply, ← map_smul] at hz
    obtain ⟨j, hij, hj⟩ := exists_eq_of_of_eq hz
    obtain ⟨k, hjk, hk⟩ := H j
    have hxy : f j k hjk (f i j hij x) = f j k hjk (f i j hij y) :=
      ((Module.End.isUnit_iff _).mp hk).injective <| by
        simpa using DFunLike.congr_arg (f j k hjk) hj
    calc of R ι G f i x = of R ι G f k (f j k hjk (f i j hij x)) := by rw [of_f, of_f]
      _ = of R ι G f k (f j k hjk (f i j hij y)) := by rw [hxy]
      _ = of R ι G f i y := by rw [of_f, of_f]
  · intro z
    obtain ⟨i, x, rfl⟩ := exists_of z
    obtain ⟨j, hij, hj⟩ := H i
    obtain ⟨y, hy⟩ := ((Module.End.isUnit_iff _).mp hj).surjective (f i j hij x)
    rw [Module.algebraMap_end_apply] at hy
    exact ⟨of R ι G f j y, by rw [Module.algebraMap_end_apply, ← map_smul, hy, of_f]⟩

end Module.DirectLimit

/-! ### The Stacks 00CR diagram -/

variable {R : Type u} [CommRing R] {S : Submonoid R}
variable {M : Type v} [AddCommGroup M] [Module R M]

open Submonoid (powers mem_powers)

namespace LocalizedModule

/-- The index category of the Stacks 00CR colimit diagram: elements of `S`, preordered by
divisibility in `R`.  `f ≤ g ↔ (f : R) ∣ (g : R)` matches the Stacks convention
`g ≥ f ↔ g = f·f''` for some `f'' ∈ R`. -/
@[ext]
structure AwayIndex (S : Submonoid R) where
  /-- The underlying element of `S`. -/
  val : S

namespace AwayIndex

instance : Preorder (AwayIndex S) where
  le a b := (a.val : R) ∣ (b.val : R)
  le_refl _ := dvd_refl _
  le_trans _ _ _ := dvd_trans

theorem le_def {a b : AwayIndex S} : a ≤ b ↔ (a.val : R) ∣ (b.val : R) := Iff.rfl

instance : One (AwayIndex S) where
  one := ⟨1⟩

lemma one_def : (1 : AwayIndex S) = .mk 1 := rfl

instance : IsDirectedOrder (AwayIndex S) where
  directed a b :=
    ⟨⟨a.val * b.val⟩, ⟨(b.val : R), by push_cast; ring⟩, ⟨(a.val : R), by push_cast; ring⟩⟩

instance : DecidableEq (AwayIndex S) := Classical.decEq _

end AwayIndex

theorem isUnit_algebraMap_end_localizedModule_powers {a b : R} (h : a ∣ b)
    (x : powers a) :
    IsUnit (algebraMap R (Module.End R (LocalizedModule (powers b) M)) (x : R)) := by
  obtain ⟨n, hn⟩ := x.2
  have hb : IsUnit (algebraMap R (Module.End R (LocalizedModule (powers b) M)) a) :=
    Module.isUnit_algebraMap_end_of_dvd h
      (IsLocalizedModule.map_units (mkLinearMap (powers b) M) ⟨b, mem_powers b⟩)
  rw [← hn, map_pow]
  exact hb.pow n

/-- The transition map `M_f → M_g` of the Stacks 00CR diagram, for `f ∣ g`: the map induced
by the universal property of `M_f`, since every power of `f` acts invertibly on `M_g`. -/
noncomputable def awayTransition {a b : AwayIndex S} (h : a ≤ b) :
    LocalizedModule (powers (a.val : R)) M →ₗ[R] LocalizedModule (powers (b.val : R)) M :=
  IsLocalizedModule.lift (powers (a.val : R)) (mkLinearMap (powers (a.val : R)) M)
    (mkLinearMap (powers (b.val : R)) M)
    (isUnit_algebraMap_end_localizedModule_powers h)

theorem awayTransition_comp_mkLinearMap {a b : AwayIndex S} (h : a ≤ b) :
    awayTransition (M := M) h ∘ₗ mkLinearMap (powers (a.val : R)) M =
      mkLinearMap (powers (b.val : R)) M :=
  IsLocalizedModule.lift_comp (powers (a.val : R)) _ _ _

theorem awayTransition_mkLinearMap {a b : AwayIndex S} (h : a ≤ b) (m : M) :
    awayTransition h (mkLinearMap (powers (a.val : R)) M m) =
      mkLinearMap (powers (b.val : R)) M m :=
  LinearMap.congr_fun (awayTransition_comp_mkLinearMap h) m

lemma awayTransition_mk {a b : AwayIndex S} (h : a ≤ b) (m : M) :
    awayTransition h (mk m 1) = mk m 1 := awayTransition_mkLinearMap ..

theorem awayTransition_trans {a b c : AwayIndex S} (hab : a ≤ b) (hbc : b ≤ c) :
    awayTransition (M := M) hbc ∘ₗ awayTransition hab = awayTransition (hab.trans hbc) := by
  apply IsLocalizedModule.ext (powers (a.val : R)) (mkLinearMap (powers (a.val : R)) M)
    (isUnit_algebraMap_end_localizedModule_powers (dvd_trans hab hbc))
  simp [LinearMap.comp_assoc, awayTransition_comp_mkLinearMap]

instance : DirectedSystem
    (fun f : AwayIndex S => LocalizedModule (powers (f.val : R)) M)
    (fun _ _ h => awayTransition h) where
  map_self a x := by
    have : awayTransition (M := M) (le_refl a) =
        LinearMap.id (M := LocalizedModule (powers (a.val : R)) M) := by
      apply IsLocalizedModule.linearMap_ext (powers (a.val : R))
        (mkLinearMap (powers (a.val : R)) M) (mkLinearMap (powers (a.val : R)) M)
      rw [awayTransition_comp_mkLinearMap, LinearMap.id_comp]
    exact LinearMap.congr_fun this x
  map_map _ _ _ hij hjk x := LinearMap.congr_fun (awayTransition_trans hij hjk) x

variable (S M) in
/-- The colimit `colim_{f ∈ S} M_f` of the Stacks 00CR diagram. -/
abbrev AwayColimit : Type (max u v) :=
  Module.DirectLimit (fun f : AwayIndex S => LocalizedModule (powers (f.val : R)) M)
    fun _ _ h => awayTransition h

variable (S M) in
/-- The canonical map `M → colim_{f ∈ S} M_f`, embedding `M` at the index `1 ∈ S`. -/
noncomputable def awayColimitMk : M →ₗ[R] AwayColimit S M :=
  Module.DirectLimit.of R (AwayIndex S)
      (fun f : AwayIndex S => LocalizedModule (powers (f.val : R)) M)
      (fun _ _ h => awayTransition h) 1 ∘ₗ
    mkLinearMap _ M

theorem awayColimitMk_apply (m : M) : awayColimitMk S M m = Module.DirectLimit.of R _ _ _ 1
    (mkLinearMap (powers (((1 : S) : R))) M m) := rfl

@[simp]
theorem of_mk_one (i : AwayIndex S) (m : M) :
    Module.DirectLimit.of R _ _ _ i (mk m 1) = awayColimitMk S M m := by
  have h1i : (1 : AwayIndex S) ≤ i := AwayIndex.le_def.mpr (one_dvd _)
  rw [← awayTransition_mk h1i m, Module.DirectLimit.of_f, awayColimitMk_apply,
    mkLinearMap_apply]

theorem isUnit_algebraMap_end_of_stage_dvd {s : S} {g : AwayIndex S}
    (h : (s : R) ∣ (g.val : R)) :
    IsUnit (algebraMap R (Module.End R (LocalizedModule (powers (g.val : R)) M)) (s : R)) :=
  isUnit_algebraMap_end_localizedModule_powers h ⟨(s : R), mem_powers _⟩

/-- The canonical map `M → colim_{f ∈ S} M_f` exhibits the colimit as the localization of
`M` at `S`.  This is the universal-property formulation of Stacks 00CR. -/
instance : IsLocalizedModule S (awayColimitMk S M) where
  map_units s := Module.DirectLimit.isUnit_algebraMap_end fun i =>
    ⟨⟨i.val * s⟩, AwayIndex.le_def.mpr ⟨(s : R), by push_cast; ring⟩,
      isUnit_algebraMap_end_of_stage_dvd ⟨(i.val : R), by push_cast; ring⟩⟩
  surj z := by
    obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
    induction x using LocalizedModule.induction_on with
    | _ m t =>
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp t.2
      refine ⟨(m, i.val ^ n), ?_⟩
      rw [Submonoid.smul_def, ← map_smul, smul'_mk, SubmonoidClass.coe_pow, hn,
        ← Submonoid.smul_def, mk_cancel, of_mk_one]
  exists_of_eq {m m'} h := by
    obtain ⟨j, h1j, hj⟩ := Module.DirectLimit.exists_eq_of_of_eq h
    rw [awayTransition_mkLinearMap, awayTransition_mkLinearMap, mkLinearMap_apply,
      mkLinearMap_apply] at hj
    obtain ⟨u, hu⟩ := mk_eq.mp hj
    exact ⟨⟨(u : R), Submonoid.powers_le.mpr j.val.2 u.2⟩, by
      simpa [Submonoid.smul_def] using hu⟩

variable (S M) in
/-- **Stacks 00CR.** `S⁻¹M = colim_{f ∈ S} M_f`: the localization of `M` at `S` is the
directed colimit of the away-localizations `M_f` over `f ∈ S` with the divisibility
preorder, with transition maps `M_f → M_g` for `f ∣ g` induced by the universal
property. -/
@[stacks 00CR]
noncomputable def equivAwayColimit : LocalizedModule S M ≃ₗ[R] AwayColimit S M :=
  IsLocalizedModule.iso S (awayColimitMk S M)

end LocalizedModule
