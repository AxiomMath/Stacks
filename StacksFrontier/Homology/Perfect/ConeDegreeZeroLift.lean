module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.TensorProduct.Free
public import StacksFrontier.Homology.Perfect.QuasiIsoDegreeZero

/-!
# Lifting degree-zero cocycles from a fibre, through a model of a mapping cone

Let `Φ : C ⟶ D` be a map of `ℤ`-indexed complexes of `R`-modules with `D⁻¹ = 0`, and let
`ρ : R →+* S` be a ring map (in the application `S` is the residue field at a prime). Suppose
that `u : P ⟶ cone(Φ)` is a quasi-isomorphism from a complex `P` with `P⁻¹ = 0` whose degree-zero
term is finite free, and which is *minimal at `ρ`* in degree zero: after base change along `ρ`
the differential out of `P⁰` vanishes and `u` detects coboundaries on `P⁰`.

`StacksDraft.ConeLift.exists_cocycle_lift` says that then every degree-zero cocycle of `C ⊗ S`
lifts to a degree-zero cocycle of `C`, as soon as

* `H⁰(Φ ⊗ S)` and `H¹(Φ ⊗ S)` are injective, and
* every degree-zero cocycle of `D ⊗ S` lifts to a degree-zero cocycle of `D`.

This is the module-theoretic heart of
[Stacks, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2), in the form used by
[Stacks, Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3): there `C` computes the
cohomology of an invertible module on `X ×_S Y`, `D` the cohomology of its restrictions to the
two faces, and the conclusion is that the trivializing section of the fibre lifts. The source
argues with minimal complexes for `C` and for `D` separately; here a single complex, minimal in
degree zero, for the mapping cone is used, which is what
[Stacks, Tag 0BYP](https://stacks.math.columbia.edu/tag/0BYP) produces.

The proof: lift the image of the given cocycle `x` in `D ⊗ S` to a cocycle `y'` of `D`; the
class of `inr y'` comes from a cocycle `q` of `P`, and minimality makes `q` vanish modulo
`ker ρ`. By minimality and the two injectivity hypotheses, the cocycles of `P` whose image is
cohomologous to `inr` of a cocycle of `D` span `P⁰` modulo `ker ρ`, so by Nakayama
([Stacks, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)) a scalar `r ≡ 1 mod ker ρ`
multiplies `P⁰` into them. Then `r • y'` differs from `Φ c` for a cocycle `c` of `C` by
something vanishing modulo `ker ρ`, and `c` is the lift.

## Main results

* `StacksDraft.ConeLift.mem_smul_top_of_one_tmul_eq_zero`: in a finite free module, an element
  killed by `1 ⊗ -` lies in `(ker ρ) • ⊤`.
* `StacksDraft.ConeLift.bcObj`, `bcMap`, `bcUnit`: base change along `ρ`, read back as `R`-modules
  through restriction of scalars, with the unit `m ↦ 1 ⊗ m`. Working in `R`-modules keeps every
  element in one type, so the additive and `R`-linear algebra needs no transport.
* `StacksDraft.ConeLift.exists_cocycle_lift`: the lifting statement above.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
open scoped ChangeOfRings TensorProduct

universe u

namespace StacksDraft.ConeLift

variable {R : Type u} [CommRing R]

/-- In a finite free module, an element `q` with `1 ⊗ q = 0` in `S ⊗_R M` lies in
`(ker (R → S)) • M`: its coordinates in a basis are killed by `R → S`. -/
theorem mem_smul_top_of_one_tmul_eq_zero {S : Type*} [CommRing S] [Algebra R S] {M : Type*}
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] (q : M)
    (h : (1 : S) ⊗ₜ[R] q = 0) :
    q ∈ (RingHom.ker (algebraMap R S)) • (⊤ : Submodule R M) := by
  classical
  let b := Module.Free.chooseBasis R M
  have hrep : ∀ i, algebraMap R S (b.repr q i) = 0 := fun i => by
    simpa [Algebra.TensorProduct.basis_repr_tmul] using
      congrArg (fun t => (Algebra.TensorProduct.basis S b).repr t i) h
  rw [← b.sum_repr q]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hrep i) Submodule.mem_top

variable {S : Type u} [CommRing S] (ρ : R →+* S)

/-- Base change along `ρ`, read back as an `R`-module. -/
noncomputable abbrev bcObj (M : ModuleCat.{u} R) : ModuleCat.{u} R :=
  (ModuleCat.restrictScalars.{u} ρ).obj ((ModuleCat.extendScalars.{u, u, u} ρ).obj M)

/-- Base change of a map along `ρ`, read back as a map of `R`-modules. -/
noncomputable abbrev bcMap {M N : ModuleCat.{u} R} (f : M ⟶ N) : bcObj ρ M ⟶ bcObj ρ N :=
  (ModuleCat.restrictScalars.{u} ρ).map ((ModuleCat.extendScalars.{u, u, u} ρ).map f)

/-- The unit `m ↦ 1 ⊗ m` of base change along `ρ`. -/
noncomputable abbrev bcUnit (M : ModuleCat.{u} R) : M ⟶ bcObj ρ M :=
  (ModuleCat.ExtendRestrictScalarsAdj.unit.{u, u, u} ρ).app M

/-- Extension of scalars is additive. -/
theorem extendScalars_additive : (ModuleCat.extendScalars.{u, u, u} ρ).Additive where
  map_add {M N f g} := by
    ext m
    simp

/-- Base change along `ρ` sends a composite `f ≫ g` to the composite of the base changes. -/
theorem bcMap_apply_bcMap {M N L : ModuleCat.{u} R} (f : M ⟶ N) (g : N ⟶ L)
    (x : bcObj ρ M) : (bcMap ρ g).hom ((bcMap ρ f).hom x) = (bcMap ρ (f ≫ g)).hom x := by
  rw [bcMap, bcMap, bcMap, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  rfl

/-- The base-change unit is natural: `bcMap ρ f (1 ⊗ m) = 1 ⊗ f m`. -/
theorem bcMap_bcUnit {M N : ModuleCat.{u} R} (f : M ⟶ N) (m : M) :
    (bcMap ρ f).hom ((bcUnit ρ M).hom m) = (bcUnit ρ N).hom (f.hom m) := rfl

/-- Base change along `ρ` is additive on maps. -/
theorem bcMap_add {M N : ModuleCat.{u} R} (f g : M ⟶ N) :
    bcMap ρ (f + g) = bcMap ρ f + bcMap ρ g := by
  have := extendScalars_additive ρ
  rw [bcMap, Functor.map_add, Functor.map_add]

/-- Base change along `ρ` commutes with negation of maps. -/
theorem bcMap_neg {M N : ModuleCat.{u} R} (f : M ⟶ N) : bcMap ρ (-f) = -bcMap ρ f := by
  have := extendScalars_additive ρ
  rw [bcMap, Functor.map_neg, Functor.map_neg]

/-- Base change along `ρ` commutes with subtraction of maps. -/
theorem bcMap_sub {M N : ModuleCat.{u} R} (f g : M ⟶ N) :
    bcMap ρ (f - g) = bcMap ρ f - bcMap ρ g := by
  have := extendScalars_additive ρ
  rw [bcMap, Functor.map_sub, Functor.map_sub]

/-- Base change along `ρ` sends the identity to the identity. -/
theorem bcMap_id (M : ModuleCat.{u} R) : bcMap ρ (𝟙 M) = 𝟙 _ := by
  rw [bcMap, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]

/-- A scalar `a` with `ρ a = 1` acts as the identity on a base change along `ρ`. -/
theorem smul_bcObj_eq_self {M : ModuleCat.{u} R} {a : R} (ha : ρ a = 1) (t : bcObj ρ M) :
    a • t = t := by
  show ρ a • (t : (ModuleCat.extendScalars.{u, u, u} ρ).obj M) = t
  rw [ha, one_smul]

/-- A scalar `a` with `ρ a = 0` acts as zero on a base change along `ρ`. -/
theorem smul_bcObj_eq_zero {M : ModuleCat.{u} R} {a : R} (ha : ρ a = 0) (t : bcObj ρ M) :
    a • t = 0 := by
  show ρ a • (t : (ModuleCat.extendScalars.{u, u, u} ρ).obj M) = 0
  rw [ha, zero_smul]

/-- In a finite free module, an element killed by the base-change unit lies in `(ker ρ) • ⊤`. -/
theorem mem_smul_top_of_bcUnit_eq_zero {M : ModuleCat.{u} R} [Module.Free R M]
    [Module.Finite R M] (q : M) (h : (bcUnit ρ M).hom q = 0) :
    q ∈ (RingHom.ker ρ) • (⊤ : Submodule R M) := by
  let : Algebra R S := ρ.toAlgebra
  exact mem_smul_top_of_one_tmul_eq_zero (S := S) q h

/-- **Lifting a degree-zero cocycle of the fibre.** Let `Φ : C ⟶ D` with `D⁻¹ = 0`, and let
`u : P ⟶ cone Φ` be a quasi-isomorphism with `P⁰` finite free, minimal at `ρ` in degree zero
(`hmin₁`, `hmin₂`). If `H⁰(Φ ⊗ S)` and `H¹(Φ ⊗ S)` are injective (`h0`, `h1`) and degree-zero
cocycles of `D ⊗ S` lift to `D` (`hsurj`), then every degree-zero cocycle `x` of `C ⊗ S` lifts
to a degree-zero cocycle of `C`. -/
theorem exists_cocycle_lift {C D : CochainComplex (ModuleCat.{u} R) ℤ} (Φ : C ⟶ D)
    (hD : IsZero (D.X (-1)))
    (P : CochainComplex (ModuleCat.{u} R) ℤ) [Module.Free R (P.X 0)] [Module.Finite R (P.X 0)]
    (u : P ⟶ mappingCone Φ) [QuasiIso u]
    (hmin₁ : ∀ q : P.X 0, (bcUnit ρ (P.X 1)).hom ((P.d 0 1).hom q) = 0)
    (hmin₂ : ∀ q : P.X 0, (∃ w : bcObj ρ ((mappingCone Φ).X (-1)),
        (bcMap ρ ((mappingCone Φ).d (-1) 0)).hom w = (bcUnit ρ _).hom ((u.f 0).hom q)) →
      (bcUnit ρ (P.X 0)).hom q = 0)
    (h0 : ∀ x : bcObj ρ (C.X 0), (bcMap ρ (C.d 0 1)).hom x = 0 →
      (bcMap ρ (Φ.f 0)).hom x = 0 → x = 0)
    (h1 : ∀ c : bcObj ρ (C.X 1), (bcMap ρ (C.d 1 2)).hom c = 0 → ∀ e : bcObj ρ (D.X 0),
      (bcMap ρ (Φ.f 1)).hom c = (bcMap ρ (D.d 0 1)).hom e →
        ∃ c' : bcObj ρ (C.X 0), (bcMap ρ (C.d 0 1)).hom c' = c)
    (hsurj : ∀ y : bcObj ρ (D.X 0), (bcMap ρ (D.d 0 1)).hom y = 0 →
      ∃ y' : D.X 0, (D.d 0 1).hom y' = 0 ∧ (bcUnit ρ _).hom y' = y)
    (x : bcObj ρ (C.X 0)) (hx : (bcMap ρ (C.d 0 1)).hom x = 0) :
    ∃ c : C.X 0, (C.d 0 1).hom c = 0 ∧ (bcUnit ρ _).hom c = x := by
  classical
  -- the structure maps of the cone in degrees `-1, 0, 1`
  let inl0 : C.X 0 ⟶ (mappingCone Φ).X (-1) := (mappingCone.inl Φ).v 0 (-1) (by omega)
  let inl1 : C.X 1 ⟶ (mappingCone Φ).X 0 := (mappingCone.inl Φ).v 1 0 (by omega)
  let inr0 : D.X 0 ⟶ (mappingCone Φ).X 0 := (mappingCone.inr Φ).f 0
  let fst0 : (mappingCone Φ).X 0 ⟶ C.X 1 := (mappingCone.fst Φ).1.v 0 1 (by omega)
  let fst1 : (mappingCone Φ).X 1 ⟶ C.X 2 := (mappingCone.fst Φ).1.v 1 2 (by omega)
  let fstm : (mappingCone Φ).X (-1) ⟶ C.X 0 := (mappingCone.fst Φ).1.v (-1) 0 (by omega)
  let snd0 : (mappingCone Φ).X 0 ⟶ D.X 0 := (mappingCone.snd Φ).v 0 0 (add_zero _)
  let snd1 : (mappingCone Φ).X 1 ⟶ D.X 1 := (mappingCone.snd Φ).v 1 1 (add_zero _)
  let sndm : (mappingCone Φ).X (-1) ⟶ D.X (-1) := (mappingCone.snd Φ).v (-1) (-1) (add_zero _)
  have F1 : inl0 ≫ (mappingCone Φ).d (-1) 0 = Φ.f 0 ≫ inr0 - C.d 0 1 ≫ inl1 :=
    mappingCone.inl_v_d Φ 0 (-1) 1 (by omega) (by omega)
  have F2 : inr0 ≫ (mappingCone Φ).d 0 1 = D.d 0 1 ≫ (mappingCone.inr Φ).f 1 :=
    mappingCone.inr_f_d Φ 0 1
  have F3 : (mappingCone Φ).d (-1) 0 ≫ fst0 = -fstm ≫ C.d 0 1 :=
    mappingCone.d_fst_v Φ (-1) 0 1 (by omega) (by omega)
  have F4 : (mappingCone Φ).d (-1) 0 ≫ snd0 = fstm ≫ Φ.f 0 + sndm ≫ D.d (-1) 0 :=
    mappingCone.d_snd_v Φ (-1) 0 (by omega)
  have F5 : (mappingCone Φ).d 0 1 ≫ fst1 = -fst0 ≫ C.d 1 2 :=
    mappingCone.d_fst_v Φ 0 1 2 (by omega) (by omega)
  have F6 : (mappingCone Φ).d 0 1 ≫ snd1 = fst0 ≫ Φ.f 1 + snd0 ≫ D.d 0 1 :=
    mappingCone.d_snd_v Φ 0 1 rfl
  have F7 : fst0 ≫ inl1 + snd0 ≫ inr0 = 𝟙 _ := mappingCone.id_X Φ 0 1 (by omega)
  have hsndm : sndm = 0 := hD.eq_of_tgt _ _
  have F8 : fstm ≫ inl0 = 𝟙 _ := by
    have h := mappingCone.id_X Φ (-1) 0 (by omega)
    have hz : sndm ≫ (mappingCone.inr Φ).f (-1) = 0 := by rw [hsndm, zero_comp]
    rw [hz, add_zero] at h
    exact h
  have F9a : inr0 ≫ fst0 = 0 := mappingCone.inr_f_fst_v Φ 0 1 (by omega)
  have F9b : inr0 ≫ snd0 = 𝟙 _ := mappingCone.inr_f_snd_v Φ 0
  -- elementwise forms
  have e1S : ∀ c : bcObj ρ (C.X 0), (bcMap ρ ((mappingCone Φ).d (-1) 0)).hom
      ((bcMap ρ inl0).hom c) = (bcMap ρ inr0).hom ((bcMap ρ (Φ.f 0)).hom c) -
        (bcMap ρ inl1).hom ((bcMap ρ (C.d 0 1)).hom c) := fun c => by
    rw [bcMap_apply_bcMap, bcMap_apply_bcMap, bcMap_apply_bcMap, F1, bcMap_sub]; rfl
  have e2 : ∀ y : D.X 0, (D.d 0 1).hom y = 0 → ((mappingCone Φ).d 0 1).hom (inr0.hom y) = 0 :=
    fun y hy => by
      have := congrArg (fun m => m.hom y) F2
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
      rw [this, hy, map_zero]
  -- Step A: lift `Φ x`.
  have hΦx : (bcMap ρ (D.d 0 1)).hom ((bcMap ρ (Φ.f 0)).hom x) = 0 := by
    rw [bcMap_apply_bcMap, Φ.comm, ← bcMap_apply_bcMap, hx, map_zero]
  obtain ⟨y', hy'd, hy'x⟩ := hsurj _ hΦx
  -- Step B: `inr y'` comes from a cocycle of `P`.
  obtain ⟨q, -, w, hqw⟩ := StacksDraft.QuasiIsoDegreeZero.exists_cocycle_of_quasiIso u
    (inr0.hom y') (e2 y' hy'd)
  -- Step C: `q` vanishes modulo `ker ρ`.
  have hq0 : (bcUnit ρ (P.X 0)).hom q = 0 := by
    refine hmin₂ q ⟨(bcMap ρ inl0).hom x + (bcUnit ρ _).hom w, ?_⟩
    rw [map_add, e1S, hx, map_zero, sub_zero, bcMap_bcUnit, hqw, map_add, ← hy'x,
      bcMap_bcUnit]
  have hqI := mem_smul_top_of_bcUnit_eq_zero ρ q hq0
  -- Step D: the submodule of "good" cocycles, and Nakayama.
  let TY (Y : Submodule R (D.X 0)) : Submodule R (P.X 0) :=
    { carrier := {q | ∃ y ∈ Y, ∃ w : (mappingCone Φ).X (-1),
        (u.f 0).hom q = inr0.hom y + ((mappingCone Φ).d (-1) 0).hom w}
      add_mem' := by
        rintro a b ⟨ya, hya, wa, ha⟩ ⟨yb, hyb, wb, hb⟩
        refine ⟨ya + yb, add_mem hya hyb, wa + wb, ?_⟩
        rw [map_add, ha, hb, map_add, map_add]; abel
      zero_mem' := ⟨0, zero_mem _, 0, by simp⟩
      smul_mem' := by
        rintro a b ⟨y, hy, w, h⟩
        refine ⟨a • y, Submodule.smul_mem _ _ hy, a • w, ?_⟩
        rw [map_smul, h, map_smul, map_smul, smul_add] }
  let T := TY (LinearMap.ker (D.d 0 1).hom)
  let T0 := TY (LinearMap.ker (D.d 0 1).hom ⊓ LinearMap.ker (bcUnit ρ _).hom)
  have hspan : (⊤ : Submodule R (P.X 0)) ≤ T ⊔ (RingHom.ker ρ) • ⊤ := by
    intro q₀ _
    set z₀ : bcObj ρ ((mappingCone Φ).X 0) := (bcUnit ρ _).hom ((u.f 0).hom q₀) with hz₀
    have hz₀d : (bcMap ρ ((mappingCone Φ).d 0 1)).hom z₀ = 0 := by
      rw [hz₀, bcMap_bcUnit]
      have := congrArg (fun m => m.hom q₀) (u.comm 0 1)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
      rw [this, ← bcMap_bcUnit, hmin₁, map_zero]
    set c := (bcMap ρ fst0).hom z₀
    set e := (bcMap ρ snd0).hom z₀
    have hc : (bcMap ρ (C.d 1 2)).hom c = 0 := by
      have := congrArg (fun t => (bcMap ρ fst1).hom t) hz₀d
      simp only [map_zero] at this
      rw [bcMap_apply_bcMap, F5, bcMap_neg, ModuleCat.hom_neg, LinearMap.neg_apply,
        neg_eq_zero] at this
      rw [bcMap_apply_bcMap]
      exact this
    have hce : (bcMap ρ (Φ.f 1)).hom c = (bcMap ρ (D.d 0 1)).hom (-e) := by
      have := congrArg (fun t => (bcMap ρ snd1).hom t) hz₀d
      simp only [map_zero] at this
      rw [bcMap_apply_bcMap, F6, bcMap_add] at this
      rw [map_neg, eq_neg_iff_add_eq_zero, bcMap_apply_bcMap, bcMap_apply_bcMap]
      simpa using this
    obtain ⟨c', hc'⟩ := h1 c hc (-e) hce
    set e'' := e + (bcMap ρ (Φ.f 0)).hom c'
    have he''d : (bcMap ρ (D.d 0 1)).hom e'' = 0 := by
      rw [map_add, bcMap_apply_bcMap ρ (Φ.f 0) (D.d 0 1), Φ.comm, ← bcMap_apply_bcMap, hc',
        hce, map_neg, add_neg_cancel]
    have hz₀dec : z₀ = (bcMap ρ inr0).hom e'' +
        (bcMap ρ ((mappingCone Φ).d (-1) 0)).hom ((bcMap ρ inl0).hom (-c')) := by
      have h7 := congrArg (fun m => (bcMap ρ m).hom z₀) F7
      simp only [bcMap_add, bcMap_id, ModuleCat.hom_add, LinearMap.add_apply,
        ModuleCat.hom_id, LinearMap.id_apply] at h7
      rw [← bcMap_apply_bcMap, ← bcMap_apply_bcMap] at h7
      rw [map_neg, map_neg, e1S, hc', map_add]
      rw [← h7]
      abel
    obtain ⟨y'', hy''d, hy''e⟩ := hsurj e'' he''d
    obtain ⟨q₁, -, w₁, hq₁w⟩ := StacksDraft.QuasiIsoDegreeZero.exists_cocycle_of_quasiIso u
      (inr0.hom y'') (e2 y'' hy''d)
    have hq₁T : q₁ ∈ T := ⟨y'', hy''d, w₁, hq₁w⟩
    have hdiff : (bcUnit ρ (P.X 0)).hom (q₀ - q₁) = 0 := by
      refine hmin₂ _ ⟨(bcMap ρ inl0).hom (-c') - (bcUnit ρ _).hom w₁, ?_⟩
      have key : (bcUnit ρ _).hom ((u.f 0).hom (q₀ - q₁)) = z₀ - ((bcMap ρ inr0).hom e'' +
          (bcMap ρ ((mappingCone Φ).d (-1) 0)).hom ((bcUnit ρ _).hom w₁)) := by
        rw [map_sub (u.f 0).hom, map_sub (bcUnit ρ _).hom, hq₁w, map_add (bcUnit ρ _).hom,
          ← bcMap_bcUnit ρ inr0 y'', hy''e, ← bcMap_bcUnit ρ ((mappingCone Φ).d (-1) 0) w₁]
      rw [map_sub, key, hz₀dec]
      abel
    have hdI := mem_smul_top_of_bcUnit_eq_zero ρ _ hdiff
    have : q₀ = q₁ + (q₀ - q₁) := by abel
    rw [this]
    exact Submodule.add_mem_sup hq₁T hdI
  obtain ⟨r, hr1, hrT⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (Module.Finite.fg_top) le_rfl hspan
  have hρr : ρ r = 1 := by
    have : ρ (r - 1) = 0 := hr1
    rwa [map_sub, map_one, sub_eq_zero] at this
  -- Step E: `r • q` is in `T0`.
  have hIT : (RingHom.ker ρ) • T ≤ T0 := by
    refine Submodule.smul_le.2 fun a ha t ⟨y, hy, w, h⟩ => ⟨a • y, ⟨?_, ?_⟩, a • w, ?_⟩
    · exact Submodule.smul_mem _ _ hy
    · change (bcUnit ρ _).hom _ = 0
      rw [map_smul]; exact smul_bcObj_eq_zero ρ ha _
    · rw [map_smul, h, map_smul, map_smul, smul_add]
  have hrq : r • q ∈ T0 := by
    apply hIT
    refine Submodule.smul_induction_on hqI (fun a ha m _ => ?_) (fun a b ha hb => ?_)
    · rw [smul_comm]
      exact Submodule.smul_mem_smul ha (hrT ⟨m, Submodule.mem_top, rfl⟩)
    · rw [smul_add]; exact Submodule.add_mem _ ha hb
  obtain ⟨y₀, ⟨-, hy₀⟩, w₀, hw₀⟩ := hrq
  -- Step F: the difference is a coboundary `d (inl c)`.
  set W := w₀ - r • w
  have hW : ((mappingCone Φ).d (-1) 0).hom W = inr0.hom (r • y' - y₀) := by
    have h' : (u.f 0).hom (r • q) = inr0.hom (r • y') + ((mappingCone Φ).d (-1) 0).hom (r • w) := by
      rw [map_smul, hqw, smul_add, map_smul, map_smul]
    have h'' := hw₀.symm.trans h'
    rw [map_sub, map_sub, sub_eq_sub_iff_add_eq_add, add_comm, h'', add_comm]
  set c := fstm.hom W
  have hcd : (C.d 0 1).hom c = 0 := by
    have := congrArg (fun m => m.hom W) F3
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_neg,
      LinearMap.neg_apply] at this
    rw [hW] at this
    have h9 := congrArg (fun m => m.hom (r • y' - y₀)) F9a
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] at h9
    rw [h9] at this
    exact neg_eq_zero.1 this.symm
  have hcΦ : (Φ.f 0).hom c = r • y' - y₀ := by
    have := congrArg (fun m => m.hom W) F4
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_add,
      LinearMap.add_apply, hsndm, ModuleCat.hom_zero, LinearMap.zero_apply, map_zero,
      add_zero] at this
    rw [hW] at this
    have h9 := congrArg (fun m => m.hom (r • y' - y₀)) F9b
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
      LinearMap.id_apply] at h9
    rw [h9] at this
    exact this.symm
  -- Step G: `c` lifts `x`.
  refine ⟨c, hcd, ?_⟩
  rw [← sub_eq_zero]
  apply h0
  · rw [map_sub, bcMap_bcUnit, hcd, map_zero, hx, sub_zero]
  · rw [map_sub, bcMap_bcUnit, hcΦ, map_sub, map_smul, hy₀, sub_zero, hy'x,
      smul_bcObj_eq_self ρ hρr, sub_self]

end StacksDraft.ConeLift

end
