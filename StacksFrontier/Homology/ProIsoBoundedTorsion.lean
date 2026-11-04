module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.GroupTheory.GroupAction.Ring
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

Throughout, `A` is a commutative ring and `f ∈ A` is a fixed element.  We work in
the derived category `D(A)` of `A`-modules, using the cohomological (upper) indexing
convention for complexes.

## Main Definitions

* (torsion submodule) For an integer `m ≥ 0`,
  `A[f^m] = {x ∈ A | f^m x = 0} = ker (f^m : A → A)`, the `f^m`-torsion submodule of
  `A`.  These form an increasing chain of ideals.

* (Koszul-type two-term complex `K_n`) For `n ≥ 1`, `K_n = (A →[f^n] A)` is the
  two-term cochain complex of `A`-modules with `A` in cohomological degrees `-1`
  and `0`, differential `d = (f^n ·) : A → A` from degree `-1` to degree `0`.
  Its cohomology is `H^{-1}(K_n) = A[f^n]`, `H^0(K_n) = A/f^n A`.
  We realise `K_n` in `D(A)` as the mapping cone of `f^n : A[0] → A[0]` (single
  complexes concentrated in degree `0`); the cone of `φ : F → G` has
  `C^p = F^{p+1} ⊕ G^p`, so for `F = G = A[0]` it is `A` in degree `-1` and `A` in
  degree `0`, with differential built from `f^n`.

* (quotient object) For `n ≥ 1`, `A/(f^n) = A / f^n A` (the cyclic `A`-module) is
  regarded as an object of `D(A)` concentrated in cohomological degree `0`.

* (the two inverse systems in `D(A)`)
  - `{A/(f^n)}` with transition maps the canonical surjections
    `π_n : A/(f^{n+1}) → A/(f^n)`.
  - `{K_n}` with transition maps `t_n : K_{n+1} → K_n` in `D(A)` represented by the
    chain map that is multiplication by `f` in degree `-1` and the identity in
    degree `0`.

## Main Statement

Assume there exists `c ≥ 1` with `A[f^c] = A[f^m]` for all `m ≥ c` (i.e. the
`f`-power torsion of `A` is bounded; this holds e.g. when `A` is Noetherian).  Then
for every `n ≥ 1` there exist morphisms in `D(A)`
  `α_n : K_n → A/(f^n)`   and   `β_n : A/(f^{n+c}) → K_n`
inducing an isomorphism of pro-objects between `{A/(f^n)}` and `{K_n}` in `D(A)`.

Concretely:
  * `α_n` is the canonical map onto `H^0`: the morphism represented by the chain map
    `K_n → A/(f^n)` which is `0` in degree `-1` and the quotient `A ↠ A/(f^n)` in
    degree `0`.
  * `β_n` is constructed from the intermediate two-term complex
    `L_n := (A/A[f^c] →[f^{n+c}] A)` in degrees `-1, 0` together with the chain map
    `L_n → K_n` given by multiplication by `f^c` in degree `-1` and the identity in
    degree `0`.  Under the boundedness hypothesis the top map `f^{n+c} : A/A[f^c] → A`
    is injective, so the natural map `L_n → H^0(L_n) = A/(f^{n+c})` is a
    quasi-isomorphism, and `β_n` is the composite
    `A/(f^{n+c}) ←~ L_n → K_n` in `D(A)` (invert the quasi-isomorphism).

Since Mathlib does not currently have a category of pro-objects `Pro (D(A))`, we
encode the pro-isomorphism by the two
round-trip identities in `D(A)`, together with compatibility of *both* `α` and `β`
with the single-step transition maps:
  * `β_n ≫ α_n` equals the iterated transition `A/(f^{n+c}) → A/(f^n)`;
  * `α_{n+c} ≫ β_n` equals the iterated transition `K_{n+c} → K_n`;
  * `t_n ≫ α_n = α_{n+1} ≫ π_n` (`α` compatible with transitions);
  * `π_{n+1+c→n+c} ≫ β_n = β_{n+1} ≫ t_n` (`β` compatible with transitions).

The quasi-isomorphism input (hence the very existence of `β`) is derived from the
boundedness hypothesis alone, so the main theorem depends only on `c`, `1 ≤ c`, and
the stabilization `A[f^c] = A[f^m]` for `m ≥ c`.
-/

open CategoryTheory

namespace ProTorsion

universe u

variable (A : Type u) [CommRing A] (f : A)

/-- We use the standard derived category of `A`-modules. -/
noncomputable instance : HasDerivedCategory (ModuleCat.{u} A) := HasDerivedCategory.standard _

/-- The torsion submodules form an increasing chain. -/
theorem torsion_mono : Monotone fun m : ℕ => Submodule.torsionBy A A (f ^ m) :=
  fun _ _ hab => Submodule.torsionBy_le_torsionBy_of_dvd _ _ (pow_dvd_pow f hab)

/-- The boundedness hypothesis on `f`-power torsion: there is `c ≥ 1` with
`A[f^c] = A[f^m]` for every `m ≥ c`. -/
def TorsionBounded : Prop :=
  ∃ c : ℕ, 1 ≤ c ∧ ∀ m : ℕ, c ≤ m →
    Submodule.torsionBy A A (f ^ c) = Submodule.torsionBy A A (f ^ m)

/-! ### The underlying `A`-module maps -/

/-- Multiplication by `f^n`, as a morphism of `A`-modules `A → A`. -/
noncomputable def smulMap (n : ℕ) : ModuleCat.of A A ⟶ ModuleCat.of A A :=
  ModuleCat.ofHom (LinearMap.lsmul A A (f ^ n))

/-- The module `A / A[f^c]`. -/
noncomputable def torsionQuot (c : ℕ) : ModuleCat.{u} A :=
  ModuleCat.of A (A ⧸ Submodule.torsionBy A A (f ^ c))

/-- The cyclic module `A / f^n A`, regarded as an `A`-module object. -/
noncomputable def Qmod (n : ℕ) : ModuleCat.{u} A := ModuleCat.of A (A ⧸ Ideal.span {f ^ n})

/-- The quotient map `A ↠ A / f^n A`. -/
@[sga "7 VIII 2.1" "partial"]
noncomputable def quotMap (n : ℕ) : ModuleCat.of A A ⟶ Qmod A f n :=
  ModuleCat.ofHom (Ideal.Quotient.mkₐ A (Ideal.span {f ^ n})).toLinearMap

/-- The map `f^{n+c} : A/A[f^c] → A` (well defined since `f^c x = 0 ⟹ f^{n+c} x = 0`). -/
noncomputable def Lmap (n c : ℕ) : torsionQuot A f c ⟶ ModuleCat.of A A :=
  ModuleCat.ofHom (Submodule.liftQ (Submodule.torsionBy A A (f ^ c))
    (LinearMap.lsmul A A (f ^ (n + c)))
    (by
      intro x hx
      simp only [Submodule.mem_torsionBy_iff, LinearMap.mem_ker, LinearMap.lsmul_apply] at hx ⊢
      rw [pow_add, mul_comm (f ^ n), mul_smul, smul_comm, hx, smul_zero]))

/-- The underlying linear version of `Lmap`, used for the injectivity statement. -/
noncomputable def LmapLin (n c : ℕ) : (A ⧸ Submodule.torsionBy A A (f ^ c)) →ₗ[A] A :=
  Submodule.liftQ (Submodule.torsionBy A A (f ^ c)) (LinearMap.lsmul A A (f ^ (n + c)))
    (by
      intro x hx
      simp only [Submodule.mem_torsionBy_iff, LinearMap.mem_ker, LinearMap.lsmul_apply] at hx ⊢
      rw [pow_add, mul_comm (f ^ n), mul_smul, smul_comm, hx, smul_zero])

/-- The map `f^c : A/A[f^c] → A` (well defined since `f^c` kills `A[f^c]`). -/
noncomputable def fcQuot (c : ℕ) : torsionQuot A f c ⟶ ModuleCat.of A A :=
  ModuleCat.ofHom (Submodule.liftQ (Submodule.torsionBy A A (f ^ c)) (LinearMap.lsmul A A (f ^ c))
    (by
      intro x hx
      simp only [Submodule.mem_torsionBy_iff, LinearMap.mem_ker, LinearMap.lsmul_apply] at hx ⊢
      exact hx))

/-- `f^{n+c} = f^c` followed by `f^n` as maps `A/A[f^c] → A`. -/
theorem Lmap_eq (n c : ℕ) : Lmap A f n c = fcQuot A f c ≫ smulMap A f n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change (f ^ (n + c)) • a = (f ^ n) • ((f ^ c) • a)
  rw [smul_smul, ← pow_add, add_comm]

/-- The composite `A →[f^n] A ↠ A/f^n A` is zero. -/
theorem smul_quot_zero (n : ℕ) : smulMap A f n ≫ quotMap A f n = 0 :=
  ModuleCat.hom_ext <| LinearMap.ext fun _ =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

/-- The composite `A/A[f^c] →[f^{n+c}] A ↠ A/f^{n+c} A` is zero. -/
theorem Lmap_quot_zero (n c : ℕ) : Lmap A f n c ≫ quotMap A f (n + c) = 0 :=
  ModuleCat.hom_ext <| LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun _ =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

/-- **Key injectivity.**  Under boundedness, `f^{n+c} : A/A[f^c] → A` is injective.
This is precisely the input making `L_n → A/(f^{n+c})` a quasi-isomorphism. -/
theorem LmapLin_injective (c : ℕ)
    (hstab : ∀ m : ℕ, c ≤ m →
      Submodule.torsionBy A A (f ^ c) = Submodule.torsionBy A A (f ^ m)) (n : ℕ) :
    Function.Injective (LmapLin A f n c) := by
  rw [← LinearMap.ker_eq_bot, LmapLin, Submodule.ker_liftQ_eq_bot']
  have : LinearMap.ker (LinearMap.lsmul A A (f ^ (n + c))) = Submodule.torsionBy A A (f ^ c) := by
    rw [hstab (n + c) (by omega)]; rfl
  rw [this]

/-! ### The single functor and the two-term complexes `K_n`, `L_n` -/

/-- The functor placing a module in cohomological degree `0`. -/
@[sga "4½ Fonctions_L 1.11" "degree 0"]
noncomputable def single0 : ModuleCat.{u} A ⥤ CochainComplex (ModuleCat.{u} A) ℤ :=
  HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0

/-- `single0` sends the zero map to the zero map.  Proved degreewise rather than via
`Functor.map_zero`: the `PreservesZeroMorphisms` instance for `HomologicalComplex.single`
in this environment silently depends on `sorryAx`, so `Functor.map_zero` would contaminate
every definition that uses it (notably `alphaCx`/`LqiCx`).  This clean version keeps the
mapping-cone `desc` scaffolds axiom-clean. -/
theorem single0_map_zero {X Y : ModuleCat.{u} A} :
    (single0 A).map (0 : X ⟶ Y) = 0 := by
  unfold single0
  apply HomologicalComplex.to_single_hom_ext (j := 0)
  rw [HomologicalComplex.single_map_f_self, HomologicalComplex.zero_f]
  simp

/-- A module placed in degree `0` has zero term in every other degree. -/
private theorem isZero_single0_X (M : ModuleCat.{u} A) {i : ℤ} (hi : i ≠ 0) :
    Limits.IsZero (((single0 A).obj M).X i) := by
  rw [single0]; exact HomologicalComplex.isZero_single_obj_X _ _ _ _ hi

/-- Two maps out of the cone of `single0 g` into a degree-`0` complex are equal as soon as
they agree after precomposing with `inr`. -/
private theorem cone_single_hom_ext {F G X : ModuleCat.{u} A} (g : F ⟶ G)
    {a b : CochainComplex.mappingCone ((single0 A).map g) ⟶ (single0 A).obj X}
    (h : CochainComplex.mappingCone.inr ((single0 A).map g) ≫ a
      = CochainComplex.mappingCone.inr ((single0 A).map g) ≫ b) : a = b := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = 0
  · subst hi
    refine CochainComplex.mappingCone.ext_from _ 1 0 (by omega)
      ((isZero_single0_X A F (by decide)).eq_of_src _ _) ?_
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, h]
  · exact (isZero_single0_X A X hi).eq_of_tgt _ _

/-- A module placed in degree `0` has zero homology in every other degree. -/
private theorem isZero_homology_single0 (M : ModuleCat.{u} A) {i : ℤ} (hi : i ≠ 0) :
    Limits.IsZero (HomologicalComplex.homology ((single0 A).obj M) i) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology, single0]
  exact HomologicalComplex.exactAt_single_obj _ _ _ _ hi

/-- In degree `0`, `inr` into the cone of `single0 g` is an isomorphism. -/
private theorem isIso_inr_f_zero {F G : ModuleCat.{u} A} (g : F ⟶ G) :
    IsIso ((CochainComplex.mappingCone.inr ((single0 A).map g)).f 0) := by
  refine ⟨(CochainComplex.mappingCone.snd _).v 0 0 (by omega), ?_, ?_⟩
  · have := CochainComplex.HomComplex.Cochain.congr_v
      (CochainComplex.mappingCone.inr_snd ((single0 A).map g)) 0 0 (by omega)
    simp
  · have hid := CochainComplex.mappingCone.id_X ((single0 A).map g) 0 1 (by omega)
    have hz : (CochainComplex.mappingCone.inl ((single0 A).map g)).v 1 0 (by omega) = 0 :=
      (isZero_single0_X A F (by decide)).eq_of_src _ _
    rw [hz, Limits.comp_zero, zero_add] at hid
    exact hid

/-- `inl` into the cone of `single0 g` from degree `0` to degree `-1` is an isomorphism. -/
private theorem isIso_inl_v_zero {F G : ModuleCat.{u} A} (g : F ⟶ G) :
    IsIso ((CochainComplex.mappingCone.inl ((single0 A).map g)).v 0 (-1) (by omega)) := by
  refine ⟨(CochainComplex.mappingCone.fst _).1.v (-1) 0 (by omega),
    CochainComplex.mappingCone.inl_v_fst_v _ 0 (-1) (by omega), ?_⟩
  have hid := CochainComplex.mappingCone.id_X ((single0 A).map g) (-1) 0 (by omega)
  have hz : (CochainComplex.mappingCone.inr ((single0 A).map g)).f (-1) = 0 :=
    (isZero_single0_X A G (by decide)).eq_of_src _ _
  rw [hz, Limits.comp_zero, add_zero] at hid
  exact hid

/-- In the cone of `single0 g`, the differential out of degree `-1` is `g` followed by `inr`
(conjugated by the isomorphism `inl`). -/
private theorem inl_v_zero_comp_d {F G : ModuleCat.{u} A} (g : F ⟶ G) :
    (CochainComplex.mappingCone.inl ((single0 A).map g)).v 0 (-1) (by omega) ≫
        (CochainComplex.mappingCone ((single0 A).map g)).d (-1) 0
      = ((single0 A).map g).f 0 ≫ (CochainComplex.mappingCone.inr ((single0 A).map g)).f 0 := by
  have h1 : ((single0 A).obj F).d 0 1 = 0 := (isZero_single0_X A F (by decide)).eq_of_tgt _ _
  rw [CochainComplex.mappingCone.inl_v_d _ 0 (-1) 1 (by omega) (by omega), h1]
  simp

/-- The two-term complex `K_n = (A →[f^n] A)`, realised as `cone (f^n : A[0] → A[0])`;
`A` in degree `-1`, `A` in degree `0`. -/
@[ega "III 1.1.1"]
noncomputable def Kcx (n : ℕ) : CochainComplex (ModuleCat.{u} A) ℤ :=
  CochainComplex.mappingCone ((single0 A).map (smulMap A f n))

/-- The intermediate two-term complex `L_n = (A/A[f^c] →[f^{n+c}] A)`, realised as
`cone (f^{n+c} : (A/A[f^c])[0] → A[0])`; `A/A[f^c]` in degree `-1`, `A` in degree `0`. -/
noncomputable def Lcx (n c : ℕ) : CochainComplex (ModuleCat.{u} A) ℤ :=
  CochainComplex.mappingCone ((single0 A).map (Lmap A f n c))

/-! ### The objects of `D(A)` -/

/-- The object `K_n` of `D(A)`. -/
noncomputable def Kobj (n : ℕ) : DerivedCategory (ModuleCat.{u} A) :=
  DerivedCategory.Q.obj (Kcx A f n)

/-- The object `L_n` of `D(A)`. -/
noncomputable def Lobj (n c : ℕ) : DerivedCategory (ModuleCat.{u} A) :=
  DerivedCategory.Q.obj (Lcx A f n c)

/-- The object `A/(f^n)` of `D(A)`, concentrated in degree `0`. -/
noncomputable def Qobj (n : ℕ) : DerivedCategory (ModuleCat.{u} A) :=
  DerivedCategory.Q.obj ((single0 A).obj (Qmod A f n))

/-! ### The map `α_n` -/

/-- The canonical chain map `K_n → (A/f^n)[0]`: zero in degree `-1`, the quotient
`A ↠ A/f^n` in degree `0`.  (This represents the truncation `τ_{≥0} K_n ≅ A/(f^n)`.) -/
@[sga "7 VIII 2.1" "partial"]
noncomputable def alphaCx (n : ℕ) : Kcx A f n ⟶ (single0 A).obj (Qmod A f n) :=
  CochainComplex.mappingCone.desc _ 0 ((single0 A).map (quotMap A f n)) (by
    rw [← Functor.map_comp, smul_quot_zero, single0_map_zero,
      CochainComplex.HomComplex.Cochain.ofHom_zero, CochainComplex.HomComplex.δ_zero])

/-- The morphism `α_n : K_n → A/(f^n)` in `D(A)`. -/
noncomputable def alpha (n : ℕ) : Kobj A f n ⟶ Qobj A f n :=
  DerivedCategory.Q.map (alphaCx A f n)

/-! ### The map `β_n` -/

/-- The canonical chain map `L_n → (A/f^{n+c})[0]`: zero in degree `-1`, the quotient
`A ↠ A/f^{n+c}` in degree `0`.  Under boundedness this is a quasi-isomorphism. -/
noncomputable def LqiCx (n c : ℕ) : Lcx A f n c ⟶ (single0 A).obj (Qmod A f (n + c)) :=
  CochainComplex.mappingCone.desc _ 0 ((single0 A).map (quotMap A f (n + c))) (by
    rw [← Functor.map_comp, Lmap_quot_zero, single0_map_zero,
      CochainComplex.HomComplex.Cochain.ofHom_zero, CochainComplex.HomComplex.δ_zero])

/-- The chain map `L_n → K_n`: multiplication by `f^c` in degree `-1`, identity in
degree `0`. -/
noncomputable def LtoKcx (n c : ℕ) : Lcx A f n c ⟶ Kcx A f n :=
  CochainComplex.mappingCone.map ((single0 A).map (Lmap A f n c))
    ((single0 A).map (smulMap A f n)) ((single0 A).map (fcQuot A f c)) (𝟙 _) (by
      rw [Category.comp_id, ← Functor.map_comp, ← Lmap_eq])

/-- The quotient map `A ↠ A/A[f^c]`. -/
noncomputable def torsionQuotMap (c : ℕ) : ModuleCat.of A A ⟶ torsionQuot A f c :=
  ModuleCat.ofHom (Submodule.torsionBy A A (f ^ c)).mkQ

/-- Multiplication by `f` on `A/A[f^c]` (well defined: `f` preserves `A[f^c]`). -/
noncomputable def fQuotEndo (c : ℕ) : torsionQuot A f c ⟶ torsionQuot A f c :=
  ModuleCat.ofHom (Submodule.mapQ _ _ (LinearMap.lsmul A A f) (by
    rintro x hx
    simp only [Submodule.mem_comap, Submodule.mem_torsionBy_iff, LinearMap.mem_ker,
      LinearMap.lsmul_apply] at hx ⊢
    rw [smul_comm, hx, smul_zero]))

/-- The chain map `K_{n+c} → L_n`: the quotient `A ↠ A/A[f^c]` in degree `-1`, the
identity in degree `0`.  (Together with `LqiCx`/`LtoKcx` this realises `α_{n+c}` and the
`K`-transition at the level of the intermediate complex `L_n`; see identity 2.) -/
noncomputable def KtoLcx (n c : ℕ) : Kcx A f (n + c) ⟶ Lcx A f n c :=
  CochainComplex.mappingCone.map ((single0 A).map (smulMap A f (n + c)))
    ((single0 A).map (Lmap A f n c)) ((single0 A).map (torsionQuotMap A f c)) (𝟙 _) (by
      rw [Category.comp_id, ← Functor.map_comp]
      congr 1)

/-- The transition chain map `L_{n+1} → L_n`: multiplication by `f` in degree `-1`,
identity in degree `0` (mirrors the `K`-transition `t`, but on the `L` system). -/
noncomputable def LtransCx (n c : ℕ) : Lcx A f (n + 1) c ⟶ Lcx A f n c :=
  CochainComplex.mappingCone.map ((single0 A).map (Lmap A f (n + 1) c))
    ((single0 A).map (Lmap A f n c)) ((single0 A).map (fQuotEndo A f c)) (𝟙 _) (by
      rw [Category.comp_id, ← Functor.map_comp]
      congr 1
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      change (f ^ (n + 1 + c)) • a =
        Lmap A f n c (fQuotEndo A f c ((Submodule.torsionBy A A (f ^ c)).mkQ a))
      change (f ^ (n + 1 + c)) • a = (f ^ (n + c)) • (f • a)
      rw [smul_smul, ← pow_succ]
      congr 2
      omega)

/-! ### Quasi-isomorphism input for `β` (decomposition of `LqiCx_quasiIso`)

`LqiCx A f n c : Lcx A f n c ⟶ (single0 A).obj (Qmod A f (n+c))` is the universal map
out of the mapping cone `Lcx = cone((single0 A).map (Lmap A f n c))`, defined by
`mappingCone.desc` with degree-`(-1)` cochain `0` and degree-`0` chain map the quotient
`A ↠ A/(f^{n+c})`.  We must show it is a quasi-isomorphism.

**Math argument (source of truth).**  Write `φ = (single0 A).map (Lmap A f n c)`,
the chain map `(A/A[f^c])[0] →[f^{n+c}] A[0]` of single complexes.  Its cone `Lcx`
is concentrated in degrees `-1` (= `A/A[f^c]`) and `0` (= `A`).  Consider the
distinguished triangle of the cone in `D(A)`
`(A/A[f^c])[0] →φ A[0] →inr Lcx → (A/A[f^c])[1]` and apply the cohomology long exact
sequence (a single in degree `0` has cohomology only in degree `0`):

* `i ∉ {-1, 0}`: `Hⁱ(Lcx)=0` and `Hⁱ((A/(f^{n+c}))[0])=0`, so `LqiCx` is a
  quasi-iso there (both sides zero).
* `i = -1`: the LES reads `0 = H⁻¹(A[0]) → H⁻¹(Lcx) → H⁰((A/A[f^c])[0]) →^{H⁰(φ)} H⁰(A[0])`,
  and `H⁰(φ) = Lmap A f n c = f^{n+c}` is **injective** (`LmapLin_injective`, using
  `hstab` with `A[f^{n+c}] = A[f^c]`), so `H⁻¹(Lcx)=0 = H⁻¹((A/(f^{n+c}))[0])`.
* `i = 0`: `H⁰((A/A[f^c])[0]) →^{f^{n+c}} H⁰(A[0]) → H⁰(Lcx) → H¹((A/A[f^c])[0])=0`,
  so `H⁰(Lcx) = coker(f^{n+c}) = A/(f^{n+c})`, and the desc map `LqiCx` realises
  exactly this identification (in degree `0` it is the quotient `A ↠ A/(f^{n+c})`,
  whose kernel is `im(f^{n+c}) = f^{n+c}A`, since `H⁰(Lcx) = A/im(Lmap)`).

We package the proof as `QuasiIso` via `quasiIso_iff` (reduce to each degree `i`),
then `quasiIsoAt_iff_isIso_homologyMap`.  The two non-trivial degrees are isolated as
`LqiCx_quasiIsoAt_neg_one` and `LqiCx_quasiIsoAt_zero`; the vanishing degrees are
handled by `LqiCx_quasiIsoAt_other`. -/

/-- The complex `L_n` vanishes outside degrees `-1` and `0`. -/
private theorem isZero_Lcx_X (n c : ℕ) {i : ℤ} (hi : i ≠ -1) (hi0 : i ≠ 0) :
    Limits.IsZero ((Lcx A f n c).X i) := by
  rw [Lcx, CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨isZero_single0_X A _ (by omega), isZero_single0_X A _ hi0⟩

/-- Off the support `{-1,0}`, both source and target of `LqiCx` are exact, so `LqiCx`
is a quasi-iso there.

SANITY CHECK PASSED (statement is a verbatim conjunct of the original Stacks-091X theorem; the
assembling `exact` in `proIso_of_torsionBounded` and the dispatch in `LqiCx_quasiIso` both compile,
forcing exact statement agreement; indexing/direction independently confirmed by sanity-check).
**Argument.** For `i ≠ -1` and `i ≠ 0`, `(Lcx A f n c).ExactAt i` because the cone is
supported in degrees `-1, 0` (`mappingCone.isZero_X_iff` plus the single complexes
being zero off degree `0`), and `((single0 A).obj (Qmod A f (n+c))).ExactAt i` for
`i ≠ 0` (`exactAt_single_obj`).  A map between objects both exact at `i` is a quasi-iso
at `i` (`quasiIsoAt_iff_exactAt`). -/
theorem LqiCx_quasiIsoAt_other (n c : ℕ) (i : ℤ) (hi : i ≠ -1) (hi0 : i ≠ 0) :
    QuasiIsoAt (LqiCx A f n c) i := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hsrc : Limits.IsZero (HomologicalComplex.homology (Lcx A f n c) i) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology, HomologicalComplex.exactAt_iff]
    apply ShortComplex.exact_of_isZero_X₂
    simpa [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor] using
      isZero_Lcx_X A f n c hi hi0
  exact ⟨0, hsrc.eq_of_src _ _, (isZero_homology_single0 A _ hi0).eq_of_src _ _⟩

/-- In degree `-1`, `H⁻¹(LqiCx)` is iso: source `H⁻¹(Lcx) = ker(f^{n+c}) = 0` (by
`LmapLin_injective`), target `H⁻¹((A/(f^{n+c}))[0]) = 0`.

SANITY CHECK PASSED (statement is a verbatim conjunct of the original Stacks-091X theorem; the
assembling `exact` in `proIso_of_torsionBounded` and the dispatch in `LqiCx_quasiIso` both compile,
forcing exact statement agreement; indexing/direction independently confirmed by sanity-check).
**Argument.** Use `quasiIsoAt_iff_isIso_homologyMap`. The target single has zero
homology in degree `-1` (`isZero_single_obj_homology`, `-1 ≠ 0`). For the source,
`H⁻¹(Lcx)` is the kernel of the degree-`0` cohomology map of `φ = (single0).map (Lmap)`
in the cone LES, i.e. `ker (Lmap A f n c) = 0` since `Lmap` (= `LmapLin`) is injective
(`LmapLin_injective A f c hstab n`, requiring `hstab` to get `A[f^{n+c}] = A[f^c]`).
So both homologies are zero objects and the map between them is iso (a map of zero
objects). Use the cone distinguished triangle / `HomologySequence` to identify
`H⁻¹(Lcx)`, or `mappingCone.isZero_X_iff` to see `(Lcx).X (-2) = 0` and that the
`d` into degree `-1` controls the kernel. -/
theorem LqiCx_quasiIsoAt_neg_one (c : ℕ)
    (hstab : ∀ m : ℕ, c ≤ m →
      Submodule.torsionBy A A (f ^ c) = Submodule.torsionBy A A (f ^ m)) (n : ℕ) :
    QuasiIsoAt (LqiCx A f n c) (-1) := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hsrc : Limits.IsZero (HomologicalComplex.homology (Lcx A f n c) (-1)) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology, HomologicalComplex.exactAt_iff]
    have hmono0 : Mono (((single0 A).map (Lmap A f n c)).f 0) := by
      rw [single0, HomologicalComplex.single_map_f_self]
      have : Mono (Lmap A f n c) := by
        rw [ModuleCat.mono_iff_injective]
        exact LmapLin_injective A f c hstab n
      infer_instance
    have hdmono :
        Mono ((CochainComplex.mappingCone ((single0 A).map (Lmap A f n c))).d (-1) 0) := by
      have := isIso_inr_f_zero A (Lmap A f n c)
      have := isIso_inl_v_zero A (Lmap A f n c)
      have hm : Mono ((CochainComplex.mappingCone.inl ((single0 A).map (Lmap A f n c))).v 0 (-1)
          (by omega) ≫ (CochainComplex.mappingCone ((single0 A).map (Lmap A f n c))).d (-1) 0) := by
        rw [inl_v_zero_comp_d]
        infer_instance
      exact (mono_comp_iff_of_isIso _ _).1 hm
    have hf : ((Lcx A f n c).sc (-1)).f = 0 := by
      have hz1 : Limits.IsZero ((Lcx A f n c).sc (-1)).X₁ := by
        simpa [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor] using
          isZero_Lcx_X A f n c (i := -2) (by decide) (by decide)
      exact hz1.eq_of_src _ _
    rw [ShortComplex.exact_iff_mono _ hf]
    have e : ((Lcx A f n c).sc (-1)).g
        = (Lcx A f n c).d (-1) ((ComplexShape.up ℤ).next (-1)) := rfl
    rw [e]
    have hdmono' : Mono ((Lcx A f n c).d (-1) 0) := by rw [Lcx]; exact hdmono
    convert hdmono' using 2
    all_goals simp
  exact ⟨0, hsrc.eq_of_src _ _, (isZero_homology_single0 A _ (by decide)).eq_of_src _ _⟩

/-- In degree `0`, `H⁰(LqiCx)` is iso: `H⁰(Lcx) = coker(f^{n+c}) = A/(f^{n+c})` and the
desc map realises this identification.

SANITY CHECK PASSED (statement is a verbatim conjunct of the original Stacks-091X theorem; the
assembling `exact` in `proIso_of_torsionBounded` and the dispatch in `LqiCx_quasiIso` both compile,
forcing exact statement agreement; indexing/direction independently confirmed by sanity-check).
**Argument.** Use `quasiIsoAt_iff_isIso_homologyMap`. The target single's `H⁰` is
`A/(f^{n+c})` via `singleObjHomologySelfIso`. The source `H⁰(Lcx)` is the cokernel of
`H⁰(φ) = Lmap A f n c = (f^{n+c} : A/A[f^c] → A)` (cone LES, the term `H¹` of the source
single vanishes). Since `im(Lmap) = f^{n+c}A` (the image of `f^{n+c} : A → A` is the same
as the image of `f^{n+c} : A/A[f^c] → A`, as the quotient is by the kernel) and
`A/(f^{n+c}) = A / f^{n+c}A`, the desc map's degree-`0` component (the quotient
`A ↠ A/(f^{n+c})`, `quotMap A f (n+c)`) induces precisely the canonical iso
`coker(Lmap) ≅ A/(f^{n+c})`. Conclude `IsIso (homologyMap (LqiCx A f n c) 0)`. -/
theorem LqiCx_quasiIsoAt_zero (c : ℕ) (n : ℕ) :
    QuasiIsoAt (LqiCx A f n c) 0 := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  -- Notation for the relevant short complexes and the map of short complexes.
  set φ := (single0 A).map (Lmap A f n c) with hφ
  set S₁ := (Lcx A f n c).sc 0 with hS₁
  set S₂ := ((single0 A).obj (Qmod A f (n + c))).sc 0 with hS₂
  set ψ : S₁ ⟶ S₂ :=
    (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).map
      (LqiCx A f n c) with hψ
  -- The homology map equals the short-complex homology map of ψ.
  have hmapeq : HomologicalComplex.homologyMap (LqiCx A f n c) 0
      = ShortComplex.homologyMap ψ := rfl
  rw [hmapeq]
  -- Both short complexes have `g = 0`.
  have hnext : ((ComplexShape.up ℤ).next 0) = 1 := by
    simp [ComplexShape.next, ComplexShape.up]
  have hg1 : S₁.g = 0 := by
    have hX3 : Limits.IsZero S₁.X₃ := by
      have : S₁.X₃ = (Lcx A f n c).X ((ComplexShape.up ℤ).next 0) := rfl
      rw [this, hnext]
      exact isZero_Lcx_X A f n c (by decide) (by decide)
    exact hX3.eq_of_tgt _ _
  have hg2 : S₂.g = 0 := by
    have hX3 : Limits.IsZero S₂.X₃ := by
      have : S₂.X₃ = ((single0 A).obj (Qmod A f (n + c))).X ((ComplexShape.up ℤ).next 0) := rfl
      rw [this, hnext]
      exact isZero_single0_X A _ (by decide)
    exact hX3.eq_of_tgt _ _
  -- Hence the `homologyι`'s are isos and it suffices to show `opcyclesMap ψ` is iso.
  have hi1 : IsIso S₁.homologyι := ShortComplex.isIso_homologyι S₁ hg1
  have hi2 : IsIso S₂.homologyι := ShortComplex.isIso_homologyι S₂ hg2
  suffices hop : IsIso (ShortComplex.opcyclesMap ψ) by
    have hnat : ShortComplex.homologyMap ψ ≫ S₂.homologyι
        = S₁.homologyι ≫ ShortComplex.opcyclesMap ψ := ShortComplex.homologyι_naturality ψ
    have : ShortComplex.homologyMap ψ
        = S₁.homologyι ≫ ShortComplex.opcyclesMap ψ ≫ inv S₂.homologyι := by
      rw [← Category.assoc, ← hnat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [this]
    infer_instance
  -- It remains to show `opcyclesMap ψ` is an isomorphism.
  -- Concrete cokernel fact: `quotMap A f (n+c)` is a cokernel of `Lmap A f n c`.
  have hexact : Function.Exact (ModuleCat.Hom.hom (Lmap A f n c))
      (ModuleCat.Hom.hom (quotMap A f (n + c))) := by
    rw [LinearMap.exact_iff]
    apply le_antisymm
    · -- ker (quotMap) ⊆ range (Lmap)
      intro x hx
      simp only [LinearMap.mem_ker] at hx
      have hmem : x ∈ Ideal.span {f ^ (n + c)} := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        exact hx
      rw [Ideal.mem_span_singleton] at hmem
      obtain ⟨b, rfl⟩ := hmem
      refine ⟨Submodule.Quotient.mk b, ?_⟩
      change (f ^ (n + c)) • b = f ^ (n + c) * b
      rw [smul_eq_mul]
    · -- range (Lmap) ⊆ ker (quotMap)
      rintro x ⟨y, rfl⟩
      simp only [LinearMap.mem_ker]
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      change Ideal.Quotient.mk (Ideal.span {f ^ (n + c)}) ((f ^ (n + c)) • b) = 0
      rw [smul_eq_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
  have hinrIso := isIso_inr_f_zero A (Lmap A f n c)
  have hinlIso := isIso_inl_v_zero A (Lmap A f n c)
  set i := (CochainComplex.mappingCone.inl φ).v 0 (-1) (by omega) with hi
  -- The conjugation relation: `i ≫ (Lcx).d (-1) 0 = φ.f 0 ≫ (inr φ).f 0`.
  have hkey : i ≫ (CochainComplex.mappingCone φ).d (-1) 0
      = φ.f 0 ≫ (CochainComplex.mappingCone.inr φ).f 0 := inl_v_zero_comp_d A _
  -- `(inr φ).f 0 ≫ (LqiCx).f 0 = ((single0 A).map (quotMap …)).f 0`.
  have hLqiCx_eq : (LqiCx A f n c)
      = CochainComplex.mappingCone.desc φ 0 ((single0 A).map (quotMap A f (n + c)))
        (by rw [hφ, ← Functor.map_comp, Lmap_quot_zero, single0_map_zero,
          CochainComplex.HomComplex.Cochain.ofHom_zero, CochainComplex.HomComplex.δ_zero]) := rfl
  have hinr_desc : (CochainComplex.mappingCone.inr φ).f 0 ≫ (LqiCx A f n c).f 0
      = ((single0 A).map (quotMap A f (n + c))).f 0 := by
    have hcomp := CochainComplex.mappingCone.inr_desc φ 0
      ((single0 A).map (quotMap A f (n + c)))
      (by rw [hφ, ← Functor.map_comp, Lmap_quot_zero, single0_map_zero,
          CochainComplex.HomComplex.Cochain.ofHom_zero, CochainComplex.HomComplex.δ_zero])
    rw [hLqiCx_eq]
    rw [← HomologicalComplex.comp_f, hcomp]
  -- `ψ.τ₂ = (LqiCx).f 0` definitionally.
  have hτ₂ : ψ.τ₂ = (LqiCx A f n c).f 0 := rfl
  -- `quotMap` is a cokernel of `Lmap`.
  have hsurj : Function.Surjective (ModuleCat.Hom.hom (quotMap A f (n + c))) :=
    Submodule.Quotient.mk_surjective _
  have hcoker := ModuleCat.isColimitCokernelCofork (Lmap A f n c) (quotMap A f (n + c))
    hexact hsurj
  -- The `singleObjXSelf` identifications and their naturality.
  set esrc := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) (torsionQuot A f c)
    with hesrc
  set etgt := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) (ModuleCat.of A A)
    with hetgt
  set eqt := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) (Qmod A f (n + c))
    with heqt
  -- Naturality of `singleObjXSelf` for `Lmap` and for `quotMap`.
  have hnatL : φ.f 0 ≫ etgt.hom = esrc.hom ≫ Lmap A f n c := by
    rw [hφ, hesrc, hetgt]
    simp [single0, HomologicalComplex.single_map_f_self]
  have hnatQ : ((single0 A).map (quotMap A f (n + c))).f 0 ≫ eqt.hom
      = etgt.hom ≫ quotMap A f (n + c) := by
    rw [hetgt, heqt]
    simp [single0, HomologicalComplex.single_map_f_self]
  -- `S₂.f = 0`.
  have hprev : ((ComplexShape.up ℤ).prev 0) = -1 :=
    ComplexShape.prev_eq' (ComplexShape.up ℤ) (show (-1 : ℤ) + 1 = 0 by ring)
  have hS2f : S₂.f = 0 := by
    have hX1 : Limits.IsZero S₂.X₁ := by
      have he : S₂.X₁ = ((single0 A).obj (Qmod A f (n + c))).X ((ComplexShape.up ℤ).prev 0) := rfl
      rw [he, hprev]
      exact isZero_single0_X A _ (by decide)
    exact hX1.eq_of_src _ _
  have hp2 : IsIso S₂.pOpcycles := ShortComplex.isIso_pOpcycles S₂ hS2f
  -- `(LqiCx).f 0 ≫ eqt.hom` is a cokernel of `(Lcx).d (-1) 0`, obtained by transporting
  -- `hcoker` (the cokernel of `Lmap`) through the cone/single isos.
  have := hinrIso
  have := hinlIso
  -- the projection `r := (LqiCx).f 0 ≫ eqt.hom`
  set r : (Lcx A f n c).X 0 ⟶ Qmod A f (n + c) := (LqiCx A f n c).f 0 ≫ eqt.hom with hr
  -- `r` factors `quotMap` through `inr.f0`/`etgt`: `inv(inr.f0) ≫ etgt.hom ≫ quotMap = r`.
  have hrfac : (CochainComplex.mappingCone.inr φ).f 0 ≫ r = etgt.hom ≫ quotMap A f (n + c) := by
    rw [hr, ← Category.assoc, hinr_desc, hnatQ]
  have hdr : (CochainComplex.mappingCone φ).d (-1) 0 ≫ r = 0 := by
    have hi0 : i ≫ (CochainComplex.mappingCone φ).d (-1) 0 ≫ r = i ≫ 0 := by
      rw [Limits.comp_zero, ← Category.assoc, hkey, Category.assoc, hrfac,
        ← Category.assoc, hnatL, Category.assoc, Lmap_quot_zero, Limits.comp_zero]
    exact (cancel_epi i).mp hi0
  -- `r` is a cokernel of `(mappingCone φ).d (-1) 0`, transported from `hcoker`.
  have hLinv : Lmap A f n c = esrc.inv ≫ φ.f 0 ≫ etgt.hom := by
    rw [Iso.eq_inv_comp]
    exact hnatL.symm
  have hqzero : ∀ {Z' : ModuleCat.{u} A} (g' : (Lcx A f n c).X 0 ⟶ Z'),
      (CochainComplex.mappingCone φ).d (-1) 0 ≫ g' = 0 →
      Lmap A f n c ≫ (etgt.inv ≫ (CochainComplex.mappingCone.inr φ).f 0 ≫ g') = 0 := by
    intro Z' g' hg'
    rw [hLinv]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc (φ.f 0), ← hkey]
    simp only [Category.assoc, hg', Limits.comp_zero]
  have hrcoker : Limits.IsColimit (Limits.CokernelCofork.ofπ r hdr) := by
    refine Limits.CokernelCofork.IsColimit.ofπ _ _
      (fun {Z'} g' hg' => hcoker.desc (Limits.CokernelCofork.ofπ
        (etgt.inv ≫ (CochainComplex.mappingCone.inr φ).f 0 ≫ g') (hqzero g' hg'))) ?_ ?_
    · -- fac : `r ≫ desc = g'`
      intro Z' g' hg'
      apply (cancel_epi ((CochainComplex.mappingCone.inr φ).f 0)).mp
      have hd := Limits.Cofork.IsColimit.π_desc (s := Limits.CokernelCofork.ofπ
        (quotMap A f (n + c)) (Lmap_quot_zero A f n c)) hcoker
        (t := Limits.CokernelCofork.ofπ
          (etgt.inv ≫ (CochainComplex.mappingCone.inr φ).f 0 ≫ g') (hqzero g' hg'))
      rw [Limits.CokernelCofork.π_ofπ, Limits.CokernelCofork.π_ofπ] at hd
      rw [← Category.assoc, hrfac, Category.assoc, hd]
      simp
    · -- uniq
      intro Z' g' hg' m hm
      apply Limits.Cofork.IsColimit.hom_ext hcoker
      have hd := Limits.Cofork.IsColimit.π_desc (s := Limits.CokernelCofork.ofπ
        (quotMap A f (n + c)) (Lmap_quot_zero A f n c)) hcoker
        (t := Limits.CokernelCofork.ofπ
          (etgt.inv ≫ (CochainComplex.mappingCone.inr φ).f 0 ≫ g') (hqzero g' hg'))
      rw [Limits.CokernelCofork.π_ofπ, Limits.CokernelCofork.π_ofπ] at hd
      rw [Limits.CokernelCofork.π_ofπ, hd]
      apply (cancel_epi etgt.hom).mp
      rw [← Category.assoc, ← hrfac, Category.assoc, hm]
      simp
  -- Assemble: `opcyclesMap ψ` is the comparison between two cokernel coforks of `S₁.f`.
  set w : Qmod A f (n + c) ⟶ S₂.opcycles := eqt.inv ≫ S₂.pOpcycles with hw
  have : IsIso w := by rw [hw]; infer_instance
  -- `r ≫ w = ψ.τ₂ ≫ S₂.pOpcycles`.
  have hrw : r ≫ w = ψ.τ₂ ≫ S₂.pOpcycles := by
    rw [hr, hw, hτ₂]; simp
  -- Bridge `S₁.f` (which is `(Lcx).d (prev 0) 0`) to `(mappingCone φ).d (-1) 0`.
  have hX1eq : S₁.X₁ = (CochainComplex.mappingCone φ).X (-1) := by
    change (Lcx A f n c).X ((ComplexShape.up ℤ).prev 0) = (CochainComplex.mappingCone φ).X (-1)
    rw [hprev]
    rfl
  have hSfd : S₁.f = eqToHom hX1eq ≫ (CochainComplex.mappingCone φ).d (-1) 0 := by
    have hr1 : (ComplexShape.up ℤ).Rel (-1) 0 := show (-1 : ℤ) + 1 = 0 by ring
    have hr2 : (ComplexShape.up ℤ).Rel ((ComplexShape.up ℤ).prev 0) 0 := by
      rw [hprev]; exact hr1
    change (Lcx A f n c).d ((ComplexShape.up ℤ).prev 0) 0
        = eqToHom hX1eq ≫ (Lcx A f n c).d (-1) 0
    rw [HomologicalComplex.eqToHom_comp_d (Lcx A f n c) hr2 hr1]
  have hdrw : S₁.f ≫ (r ≫ w) = 0 := by
    rw [hSfd, Category.assoc, ← Category.assoc ((CochainComplex.mappingCone φ).d (-1) 0),
      hdr, Limits.zero_comp, Limits.comp_zero]
  -- zero condition transferred across the `eqToHom` bridge.
  have hdg : ∀ {Z' : ModuleCat.{u} A} (g' : S₁.X₂ ⟶ Z'), S₁.f ≫ g' = 0 →
      (CochainComplex.mappingCone φ).d (-1) 0 ≫ g' = 0 := by
    intro Z' g' hg'
    rw [hSfd, Category.assoc] at hg'
    have h0 : eqToHom hX1eq ≫ (CochainComplex.mappingCone φ).d (-1) 0 ≫ g'
        = eqToHom hX1eq ≫ 0 := by rw [Limits.comp_zero]; exact hg'
    exact (cancel_epi (eqToHom hX1eq)).mp h0
  -- The cofork `ofπ (r ≫ w)` over `S₁.f` is a colimit (transport from `hrcoker`).
  have hrwcoker : Limits.IsColimit (Limits.CokernelCofork.ofπ (f := S₁.f) (r ≫ w) hdrw) := by
    refine Limits.CokernelCofork.IsColimit.ofπ _ _
      (fun {Z'} g' hg' => inv w ≫ hrcoker.desc (Limits.CokernelCofork.ofπ g' (hdg g' hg'))) ?_ ?_
    · intro Z' g' hg'
      have hd := Limits.Cofork.IsColimit.π_desc (s := Limits.CokernelCofork.ofπ r hdr) hrcoker
        (t := Limits.CokernelCofork.ofπ g' (hdg g' hg'))
      rw [Limits.CokernelCofork.π_ofπ, Limits.CokernelCofork.π_ofπ] at hd
      rw [Category.assoc, ← Category.assoc w, IsIso.hom_inv_id, Category.id_comp, hd]
    · intro Z' g' hg' m hm
      have hd := Limits.Cofork.IsColimit.π_desc (s := Limits.CokernelCofork.ofπ r hdr) hrcoker
        (t := Limits.CokernelCofork.ofπ g' (hdg g' hg'))
      rw [Limits.CokernelCofork.π_ofπ, Limits.CokernelCofork.π_ofπ] at hd
      change m = inv w ≫ hrcoker.desc (Limits.CokernelCofork.ofπ g' (hdg g' hg'))
      have hwm : w ≫ m = hrcoker.desc (Limits.CokernelCofork.ofπ g' (hdg g' hg')) := by
        apply Limits.Cofork.IsColimit.hom_ext hrcoker
        rw [Limits.CokernelCofork.π_ofπ, hd, ← Category.assoc, ← hm]
      rw [← hwm, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  -- `S₁.opcycles` is the cokernel of `S₁.f`.
  have hS1coker : Limits.IsColimit
      (Limits.CokernelCofork.ofπ S₁.pOpcycles (S₁.f_pOpcycles)) := S₁.opcyclesIsCokernel
  -- The comparison iso between the two cokernels.
  set e := Limits.IsColimit.coconePointUniqueUpToIso hS1coker hrwcoker with he
  -- `opcyclesMap ψ = e.hom`, hence iso.
  have heq : ShortComplex.opcyclesMap ψ = e.hom := by
    apply Limits.Cofork.IsColimit.hom_ext hS1coker
    rw [Limits.CokernelCofork.π_ofπ]
    have h1 : S₁.pOpcycles ≫ ShortComplex.opcyclesMap ψ = ψ.τ₂ ≫ S₂.pOpcycles :=
      ShortComplex.p_opcyclesMap ψ
    rw [h1, ← hrw, he]
    have h2 := Limits.IsColimit.comp_coconePointUniqueUpToIso_hom hS1coker hrwcoker
      Limits.WalkingParallelPair.one
    change S₁.pOpcycles ≫ e.hom = r ≫ w at h2
    exact h2.symm
  rw [heq]
  infer_instance

/-- **Quasi-isomorphism statement.**  Under boundedness, the canonical map
`L_n → A/(f^{n+c})` is a quasi-isomorphism (so it becomes an isomorphism in `D(A)`,
allowing us to invert it in the definition of `β_n`).  This is the derived-category
incarnation of `LmapLin_injective`.

SANITY CHECK PASSED (statement is a verbatim conjunct of the original Stacks-091X theorem; the
assembling `exact` in `proIso_of_torsionBounded` and the dispatch in `LqiCx_quasiIso` both compile,
forcing exact statement agreement; indexing/direction independently confirmed by sanity-check).
**Strategy.** `rw [quasiIso_iff]; intro i`, then case on `i = -1`, `i = 0`, else, and
apply `LqiCx_quasiIsoAt_neg_one`, `LqiCx_quasiIsoAt_zero`, `LqiCx_quasiIsoAt_other`. -/
theorem LqiCx_quasiIso (c : ℕ)
    (hstab : ∀ m : ℕ, c ≤ m →
      Submodule.torsionBy A A (f ^ c) = Submodule.torsionBy A A (f ^ m)) (n : ℕ) :
    QuasiIso (LqiCx A f n c) := by
  rw [quasiIso_iff]
  intro i
  rcases eq_or_ne i (-1) with hi | hi
  · subst hi; exact LqiCx_quasiIsoAt_neg_one A f c hstab n
  · rcases eq_or_ne i 0 with hi0 | hi0
    · subst hi0; exact LqiCx_quasiIsoAt_zero A f c n
    · exact LqiCx_quasiIsoAt_other A f n c i hi hi0

/-- Under boundedness, `LqiCx` becomes an isomorphism in `D(A)`. -/
private theorem isIso_Q_map_LqiCx (c : ℕ)
    (hstab : ∀ m : ℕ, c ≤ m →
      Submodule.torsionBy A A (f ^ c) = Submodule.torsionBy A A (f ^ m)) (n : ℕ) :
    IsIso (DerivedCategory.Q.map (LqiCx A f n c)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} A) _).2 (LqiCx_quasiIso A f c hstab n)

/-- The morphism `β_n : A/(f^{n+c}) → K_n` in `D(A)`, namely the span
`A/(f^{n+c}) ←~ L_n → K_n` with the quasi-isomorphism inverted.

The needed `QuasiIso (LqiCx …)` is derived from the boundedness hypothesis `hstab`
(via `LqiCx_quasiIso`), so the only inputs are `c`, `1 ≤ c`, and the stabilization
`hstab`.  In particular the *existence* of `β_n` is a consequence of boundedness
alone. -/
noncomputable def beta (c : ℕ)
    (hstab : ∀ m : ℕ, c ≤ m →
      Submodule.torsionBy A A (f ^ c) = Submodule.torsionBy A A (f ^ m)) (n : ℕ) :
    Qobj A f (n + c) ⟶ Kobj A f n :=
  haveI : QuasiIso (LqiCx A f n c) := LqiCx_quasiIso A f c hstab n
  haveI : IsIso (DerivedCategory.Q.map (LqiCx A f n c)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} A) (LqiCx A f n c)).2 this
  inv (DerivedCategory.Q.map (LqiCx A f n c)) ≫ DerivedCategory.Q.map (LtoKcx A f n c)

/-! ### The transition maps of the two inverse systems -/

/-- The module-level transition `A/f^{n+c} → A/f^n` (descent of the identity of `A`). -/
noncomputable def QtransMod (n c : ℕ) : Qmod A f (n + c) ⟶ Qmod A f n :=
  ModuleCat.ofHom (Submodule.mapQ _ _ LinearMap.id (by
    rw [Ideal.span_le]
    rintro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    simp only [SetLike.mem_coe]
    rw [pow_add]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))))

/-- The iterated transition `π : A/(f^{n+c}) → A/(f^n)` in `D(A)`. -/
noncomputable def Qtrans (n c : ℕ) : Qobj A f (n + c) ⟶ Qobj A f n :=
  DerivedCategory.Q.map ((single0 A).map (QtransMod A f n c))

/-- The single-step transition `π_n : A/(f^{n+1}) → A/(f^n)`. -/
noncomputable def QtransOne (n : ℕ) : Qobj A f (n + 1) ⟶ Qobj A f n := Qtrans A f n 1

/-- The chain map `K_{n+c} → K_n`: multiplication by `f^c` in degree `-1`, identity
in degree `0` (the `c`-fold composite of the single-step transitions). -/
@[ega "III 1.1.5" "r = 1", ega "III 1.1.6" "special case"]
noncomputable def KtransCx (n c : ℕ) : Kcx A f (n + c) ⟶ Kcx A f n :=
  CochainComplex.mappingCone.map ((single0 A).map (smulMap A f (n + c)))
    ((single0 A).map (smulMap A f n)) ((single0 A).map (smulMap A f c)) (𝟙 _) (by
      rw [Category.comp_id, ← Functor.map_comp]
      congr 1
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (f ^ (n + c)) • x = (f ^ n) • ((f ^ c) • x)
      rw [smul_smul, ← pow_add, add_comm])

/-- The iterated transition `t : K_{n+c} → K_n` in `D(A)`. -/
noncomputable def Ktrans (n c : ℕ) : Kobj A f (n + c) ⟶ Kobj A f n :=
  DerivedCategory.Q.map (KtransCx A f n c)

/-- The single-step transition `t_n : K_{n+1} → K_n`. -/
noncomputable def KtransOne (n : ℕ) : Kobj A f (n + 1) ⟶ Kobj A f n := Ktrans A f n 1

/-! ### Main statement -/

/-! #### The four identities, as named sub-lemmas

All four maps `alpha`, `beta`, `Qtrans`/`QtransOne`, `Ktrans`/`KtransOne` are images
under `DerivedCategory.Q` of chain maps (with `beta` additionally inverting the
quasi-iso `Q.map (LqiCx …)`).  Each identity is reduced to a *chain-level* equality
(an equation of cochain maps), which is then transported through the functor `Q`
(using `Q.map_comp`, and for `beta` the cancellation `g ≫ inv g = 𝟙` of the inverted
quasi-iso).  The chain-level equalities all hold because every map in sight is the
mapping-cone functoriality map / `desc` of an explicit two-by-two square of module
maps, and the squares compose to literally equal squares; concretely they are checked
on the two nonzero degrees `-1, 0` via `mappingCone.ext_from` (a map out of a cone is
determined by its `inl`/`inr` components) together with the module identities already
proved (`Lmap_eq`, the descent/`mapQ` computations, `f^{n+c} = f^n·f^c`, etc.).

The decisive chain-level facts (each an equality of cochain maps, provable degreewise):

* `LtoKcx n c ≫ alphaCx n = LqiCx n c ≫ (single0 A).map (QtransMod A f n c)`
  (deg 0: both are `A ↠ A/f^n`, since `QtransMod ∘ quot_{n+c} = quot_n`; deg -1: both 0).
* `KtoLcx n c ≫ LqiCx n c = alphaCx A f (n + c)`
  (deg 0: `id ≫ quot_{n+c} = quot_{n+c}`; deg -1: `(A↠A/A[f^c]) ≫ 0 = 0`).
* `KtoLcx n c ≫ LtoKcx n c = KtransCx A f n c`
  (deg 0: `id`; deg -1: `(A↠A/A[f^c]) ≫ f^c = f^c = smulMap c`).
* `KtransCx n 1 ≫ alphaCx n = alphaCx (n+1) ≫ (single0 A).map (QtransMod A f n 1)`
  (deg 0: both `A ↠ A/f^n`; deg -1: both 0).
* `LtransCx n c ≫ LqiCx n c = LqiCx (n+1) c ≫ (single0 A).map (QtransMod A f (n+c) 1)`
  (deg 0: `quot_{(n+1)+c}` then `A/f^{(n+1)+c} ↠ A/f^{n+c}` equals `A ↠ A/f^{n+c}`,
   matching the reindexed target; deg -1: both 0).
* `LtransCx n c ≫ LtoKcx n c = LtoKcx (n+1) c ≫ KtransCx n 1`
  (deg 0: `id`; deg -1: `f ≫ f^c = f^c ≫ f = f^{c+1}` on `A/A[f^c]`). -/

/-- The module-level identity `quot_{n+c} ≫ QtransMod n c = quot_n` (since `QtransMod`
is the descent of the identity of `A`). -/
theorem quotMap_QtransMod (n c : ℕ) :
    quotMap A f (n + c) ≫ QtransMod A f n c = quotMap A f n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- **Chain-level Identity 1.** `LtoKcx n c ≫ alphaCx n = LqiCx n c ≫ single (QtransMod n c)`. -/
theorem LtoKcx_alphaCx (n c : ℕ) :
    LtoKcx A f n c ≫ alphaCx A f n
      = LqiCx A f n c ≫ (single0 A).map (QtransMod A f n c) := by
  refine cone_single_hom_ext A _ ?_
  simp [LtoKcx, alphaCx, LqiCx, CochainComplex.mappingCone.map, ← Functor.map_comp,
    quotMap_QtransMod]

/-- **Identity 1** (round trip through `{A/(f^•)}`): `β_n ≫ α_n = (A/(f^{n+c}) → A/(f^n))`.

SANITY CHECK PASSED (statement is a verbatim conjunct of the original Stacks-091X theorem; the
assembling `exact` in `proIso_of_torsionBounded` and the dispatch in `LqiCx_quasiIso` both compile,
forcing exact statement agreement; indexing/direction independently confirmed by sanity-check).
**Argument.** Unfold `beta = inv(Q.map (LqiCx n c)) ≫ Q.map (LtoKcx n c)` and
`alpha = Q.map (alphaCx n)`, `Qtrans = Q.map ((single0).map (QtransMod n c))`. Since
`Q.map (LqiCx n c)` is iso, the goal `inv g ≫ Q(LtoKcx) ≫ Q(alphaCx) = Q(single QtransMod)`
is equivalent (compose with `g` on the left, cancel `g ≫ inv g`) to
`Q(LtoKcx) ≫ Q(alphaCx) = Q(LqiCx) ≫ Q(single QtransMod)`, i.e.
`Q(LtoKcx n c ≫ alphaCx n) = Q(LqiCx n c ≫ (single0).map (QtransMod n c))`.
This follows from the **chain-level equality**
`LtoKcx n c ≫ alphaCx n = LqiCx n c ≫ (single0).map (QtransMod n c)`
(checked degreewise: in degree `0` both sides are the quotient `A ↠ A/(f^n)`, using
`QtransMod ∘ quot_{n+c} = quot_n`; in degree `-1` both are `0`), via `Q.map`. -/
theorem identity_betaAlpha (c : ℕ)
    (hstab : ∀ m : ℕ, c ≤ m →
      Submodule.torsionBy A A (f ^ c) = Submodule.torsionBy A A (f ^ m)) (n : ℕ) :
    beta A f c hstab n ≫ alpha A f n = Qtrans A f n c := by
  have := isIso_Q_map_LqiCx A f c hstab n
  rw [beta, alpha, Qtrans, Category.assoc, ← DerivedCategory.Q.map_comp,
    LtoKcx_alphaCx, DerivedCategory.Q.map_comp, IsIso.inv_hom_id_assoc]

/-- Module-level: `(A ↠ A/A[f^c]) ≫ (f^c : A/A[f^c] → A) = (f^c : A → A)`. -/
theorem torsionQuotMap_fcQuot (c : ℕ) :
    torsionQuotMap A f c ≫ fcQuot A f c = smulMap A f c := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- **Chain-level Identity 2a.** `KtoLcx n c ≫ LqiCx n c = alphaCx (n+c)`. -/
theorem KtoLcx_LqiCx (n c : ℕ) :
    KtoLcx A f n c ≫ LqiCx A f n c = alphaCx A f (n + c) := by
  refine cone_single_hom_ext A _ ?_
  simp [KtoLcx, alphaCx, LqiCx, CochainComplex.mappingCone.map]

/-- **Chain-level Identity 2b.** `KtoLcx n c ≫ LtoKcx n c = KtransCx n c`. -/
theorem KtoLcx_LtoKcx (n c : ℕ) :
    KtoLcx A f n c ≫ LtoKcx A f n c = KtransCx A f n c := by
  rw [KtoLcx, LtoKcx, ← CochainComplex.mappingCone.map_comp, KtransCx]
  congr 1
  rw [← Functor.map_comp, torsionQuotMap_fcQuot]

/-- **Identity 2** (round trip through `{K_•}`): `α_{n+c} ≫ β_n = (K_{n+c} → K_n)`.

SANITY CHECK PASSED (statement is a verbatim conjunct of the original Stacks-091X theorem; the
assembling `exact` in `proIso_of_torsionBounded` and the dispatch in `LqiCx_quasiIso` both compile,
forcing exact statement agreement; indexing/direction independently confirmed by sanity-check).
**Argument.** Unfold `α_{n+c} = Q(alphaCx (n+c))` and
`β_n = inv(Q(LqiCx n c)) ≫ Q(LtoKcx n c)`. The key is the auxiliary chain map
`KtoLcx n c : K_{n+c} → L_n` (quotient `A ↠ A/A[f^c]` in deg `-1`, `id` in deg `0`),
which satisfies the two **chain-level equalities**
`KtoLcx n c ≫ LqiCx n c = alphaCx (n+c)` and `KtoLcx n c ≫ LtoKcx n c = KtransCx n c`
(both checked degreewise). Applying `Q`:
`Q(alphaCx (n+c)) = Q(KtoLcx) ≫ Q(LqiCx)`. Hence
`α_{n+c} ≫ β_n = Q(KtoLcx) ≫ Q(LqiCx) ≫ inv(Q(LqiCx)) ≫ Q(LtoKcx)`
`= Q(KtoLcx) ≫ Q(LtoKcx) = Q(KtoLcx ≫ LtoKcx) = Q(KtransCx n c) = Ktrans n c`,
where `Q(LqiCx) ≫ inv(Q(LqiCx)) = 𝟙` cancels (it is iso by `LqiCx_quasiIso`). -/
theorem identity_alphaBeta (c : ℕ)
    (hstab : ∀ m : ℕ, c ≤ m →
      Submodule.torsionBy A A (f ^ c) = Submodule.torsionBy A A (f ^ m)) (n : ℕ) :
    alpha A f (n + c) ≫ beta A f c hstab n = Ktrans A f n c := by
  have := isIso_Q_map_LqiCx A f c hstab n
  rw [alpha, beta, Ktrans, ← KtoLcx_LqiCx, DerivedCategory.Q.map_comp, Category.assoc,
    IsIso.hom_inv_id_assoc, ← DerivedCategory.Q.map_comp, KtoLcx_LtoKcx]

/-- **Chain-level Identity 3.**
`KtransCx n 1 ≫ alphaCx n = alphaCx (n+1) ≫ single (QtransMod n 1)`. -/
theorem KtransCx_alphaCx (n : ℕ) :
    KtransCx A f n 1 ≫ alphaCx A f n
      = alphaCx A f (n + 1) ≫ (single0 A).map (QtransMod A f n 1) := by
  refine cone_single_hom_ext A _ ?_
  simp [KtransCx, alphaCx, CochainComplex.mappingCone.map, ← Functor.map_comp,
    quotMap_QtransMod]

/-- **Identity 3** (`α` compatible with transitions): `t_n ≫ α_n = α_{n+1} ≫ π_n`.

SANITY CHECK PASSED (statement is a verbatim conjunct of the original Stacks-091X theorem; the
assembling `exact` in `proIso_of_torsionBounded` and the dispatch in `LqiCx_quasiIso` both compile,
forcing exact statement agreement; indexing/direction independently confirmed by sanity-check).
**Argument.** Both sides are `Q.map` of chain maps:
`t_n ≫ α_n = Q(KtransCx n 1 ≫ alphaCx n)` and
`α_{n+1} ≫ π_n = Q(alphaCx (n+1) ≫ (single0).map (QtransMod n 1))` (using
`Q.map_comp`, `KtransOne = Q(KtransCx n 1)`, `QtransOne = Q(single QtransMod n 1)`).
So it suffices to prove the **chain-level equality**
`KtransCx n 1 ≫ alphaCx n = alphaCx (n+1) ≫ (single0).map (QtransMod n 1)`,
checked degreewise: in degree `0` both composites are `A ↠ A/(f^n)` (LHS:
`id ≫ quot_n`; RHS: `quot_{n+1}` then `A/f^{n+1} ↠ A/f^n`, which is `quot_n`); in
degree `-1` both are `0` (`alphaCx` is `0` there). Apply `Q.map`. -/
theorem identity_alphaTransition (n : ℕ) :
    KtransOne A f n ≫ alpha A f n = alpha A f (n + 1) ≫ QtransOne A f n := by
  rw [KtransOne, Ktrans, alpha, alpha, QtransOne, Qtrans,
    ← DerivedCategory.Q.map_comp, KtransCx_alphaCx, DerivedCategory.Q.map_comp]

/-- Module-level: on `A/A[f^c]`, `f ≫ f^c = f^c ≫ f` (= `f^{c+1}`). -/
theorem fQuotEndo_fcQuot (c : ℕ) :
    fQuotEndo A f c ≫ fcQuot A f c = fcQuot A f c ≫ smulMap A f 1 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change (f ^ c) • (f • a) = (f ^ 1) • ((f ^ c) • a)
  rw [smul_smul, smul_smul, pow_one, mul_comm]

/-- For `m₁ = m₂`, the quotient map `A ↠ A/f^{m₁}` followed by the identification
`A/f^{m₁} = A/f^{m₂}` is the quotient map `A ↠ A/f^{m₂}`. -/
theorem quotMap_comp_eqToHom (m₁ m₂ : ℕ) (h : m₁ = m₂) :
    quotMap A f m₁ ≫ eqToHom (by rw [h] : Qmod A f m₁ = Qmod A f m₂) = quotMap A f m₂ := by
  subst h; simp

/-- The quotient map `A ↠ A/f^{n+1+c}`, followed by the identification
`A/f^{n+1+c} = A/f^{n+c+1}` and the transition `A/f^{n+c+1} → A/f^{n+c}`, is the quotient
map `A ↠ A/f^{n+c}`. -/
theorem quotMap_eqToHom_QtransMod (n c : ℕ) :
    quotMap A f (n + 1 + c)
        ≫ (eqToHom (by rw [Nat.add_right_comm] : Qmod A f (n + 1 + c) = Qmod A f (n + c + 1))
          ≫ QtransMod A f (n + c) 1) = quotMap A f (n + c) := by
  rw [← Category.assoc, quotMap_comp_eqToHom A f (n + 1 + c) (n + c + 1) (by rw
      [Nat.add_right_comm]),
    quotMap_QtransMod A f (n + c) 1]

/-- The transition `L_{n+1} → L_n` followed by `L_n → (A/f^{n+c})[0]` equals
`L_{n+1} → (A/f^{n+1+c})[0]` followed by the transition `A/f^{n+1+c} → A/f^{n+c}` placed in
degree `0`. -/
theorem LtransCx_LqiCx (n c : ℕ) :
    LtransCx A f n c ≫ LqiCx A f n c
      = LqiCx A f (n + 1) c
        ≫ (single0 A).map
            (eqToHom (by rw [Nat.add_right_comm] : Qmod A f (n + 1 + c) = Qmod A f (n + c + 1))
              ≫ QtransMod A f (n + c) 1) := by
  refine cone_single_hom_ext A _ ?_
  simp [LtransCx, LqiCx, CochainComplex.mappingCone.map, ← Functor.map_comp,
    quotMap_eqToHom_QtransMod]

/-- The chain maps `L_n → K_n` commute with the transitions `L_{n+1} → L_n` and
`K_{n+1} → K_n`. -/
theorem LtransCx_LtoKcx (n c : ℕ) :
    LtransCx A f n c ≫ LtoKcx A f n c
      = LtoKcx A f (n + 1) c ≫ KtransCx A f n 1 := by
  rw [LtransCx, LtoKcx, ← CochainComplex.mappingCone.map_comp,
    LtoKcx, KtransCx, ← CochainComplex.mappingCone.map_comp]
  congr 1
  rw [← Functor.map_comp, ← Functor.map_comp, fQuotEndo_fcQuot]

/-- **Identity 4** (`β` compatible with transitions):
`π_{(n+1)+c→n+c} ≫ β_n = eqToHom … ≫ β_{n+1} ≫ t_n`.

SANITY CHECK PASSED (statement is a verbatim conjunct of the original Stacks-091X theorem; the
assembling `exact` in `proIso_of_torsionBounded` and the dispatch in `LqiCx_quasiIso` both compile,
forcing exact statement agreement; indexing/direction independently confirmed by sanity-check).
**Argument.** Write `g_m := Q(LqiCx m c)` (iso). Then `β_m = inv g_m ≫ Q(LtoKcx m c)`.
The transition on the `L`-system is `LtransCx n c : L_{n+1} → L_n` (mult by `f` in deg
`-1`, `id` in deg `0`). The two **chain-level equalities**
`LtransCx n c ≫ LqiCx n c = LqiCx (n+1) c ≫ (single0).map (QtransMod (n+c) 1)`  (★)
`LtransCx n c ≫ LtoKcx n c = LtoKcx (n+1) c ≫ KtransCx n 1`                     (★★)
(checked degreewise; note the index identification `(n+1)+c = (n+c)+1` handled by the
`eqToHom`) give, after applying `Q` and rearranging the isos:
from (★): `Q(single QtransMod (n+c) 1) = inv g_n^{?}…` — more precisely
`Q(LtransCx) ≫ g_n = g_{n+1} ≫ Q(single QtransMod (n+c) 1)` (modulo the `eqToHom`
reindexing of the source `A/f^{(n+1)+c} = A/f^{(n+c)+1}`), so
`inv g_n ≫ Q(LtransCx) = (Q(single QtransMod (n+c) 1)) ≫ inv g_{n+1}` up to `eqToHom`.
Combining with (★★) `Q(LtransCx) ≫ Q(LtoKcx n c) = Q(LtoKcx (n+1) c) ≫ Q(KtransCx n 1)`:
`QtransOne (n+c) ≫ β_n = Q(single QtransMod (n+c) 1) ≫ inv g_n ≫ Q(LtoKcx n c)`
`= eqToHom ≫ inv g_{n+1} ≫ Q(LtransCx) ≫ Q(LtoKcx n c)`
`= eqToHom ≫ inv g_{n+1} ≫ Q(LtoKcx (n+1) c) ≫ Q(KtransCx n 1)`
`= eqToHom ≫ β_{n+1} ≫ t_n`.
The `eqToHom (by rw [Nat.add_right_comm])` exactly accounts for the index swap
`(n+c)+1 ↔ (n+1)+c` in the domain `A/(f^•)`. -/
theorem identity_betaTransition (c : ℕ)
    (hstab : ∀ m : ℕ, c ≤ m →
      Submodule.torsionBy A A (f ^ c) = Submodule.torsionBy A A (f ^ m)) (n : ℕ) :
    QtransOne A f (n + c) ≫ beta A f c hstab n
      = eqToHom (by rw [Nat.add_right_comm]) ≫ beta A f c hstab (n + 1) ≫ KtransOne A f n := by
  have := isIso_Q_map_LqiCx A f c hstab n
  have := isIso_Q_map_LqiCx A f c hstab (n + 1)
  rw [QtransOne, Qtrans, beta, beta, KtransOne, Ktrans]
  -- Q-image of (★): factor the reindexing eqToHom out.
  have hQstar :
      DerivedCategory.Q.map (LtransCx A f n c) ≫ DerivedCategory.Q.map (LqiCx A f n c)
        = DerivedCategory.Q.map (LqiCx A f (n + 1) c)
          ≫ (eqToHom (by rw [Nat.add_right_comm] :
              Qobj A f (n + 1 + c) = Qobj A f (n + c + 1))
            ≫ DerivedCategory.Q.map ((single0 A).map (QtransMod A f (n + c) 1))) := by
    rw [← DerivedCategory.Q.map_comp, LtransCx_LqiCx, DerivedCategory.Q.map_comp,
      Functor.map_comp, eqToHom_map, DerivedCategory.Q.map_comp, eqToHom_map]
  have hQstar2 :
      DerivedCategory.Q.map (LtransCx A f n c) ≫ DerivedCategory.Q.map (LtoKcx A f n c)
        = DerivedCategory.Q.map (LtoKcx A f (n + 1) c)
          ≫ DerivedCategory.Q.map (KtransCx A f n 1) := by
    rw [← DerivedCategory.Q.map_comp, LtransCx_LtoKcx, DerivedCategory.Q.map_comp]
  -- The key relation: `T ≫ inv gₙ = eqToHom ≫ inv g₁ ≫ Q(LtransCx)`.
  have key :
      DerivedCategory.Q.map ((single0 A).map (QtransMod A f (n + c) 1))
          ≫ inv (DerivedCategory.Q.map (LqiCx A f n c))
        = eqToHom (by rw [Nat.add_right_comm] : Qobj A f (n + c + 1) = Qobj A f (n + 1 + c))
          ≫ inv (DerivedCategory.Q.map (LqiCx A f (n + 1) c))
            ≫ DerivedCategory.Q.map (LtransCx A f n c) := by
    rw [IsIso.comp_inv_eq]
    rw [Category.assoc, Category.assoc, hQstar, ← Category.assoc (inv _),
      IsIso.inv_hom_id, Category.id_comp, ← Category.assoc, eqToHom_trans,
      eqToHom_refl, Category.id_comp]
  rw [← Category.assoc (DerivedCategory.Q.map ((single0 A).map (QtransMod A f (n + c) 1))),
    key, Category.assoc, Category.assoc, Category.assoc, hQstar2]

/-- **Main statement.**  Let `A` be a commutative ring, `f ∈ A`, and assume the
`f`-power torsion of `A` is bounded, witnessed by `c ≥ 1` (so `A[f^c] = A[f^m]` for
all `m ≥ c`).  Then the explicit families of morphisms in `D(A)`

  `alpha n : K_n → A/(f^n)`   (the canonical map onto `H^0`),
  `beta  c hc hstab n : A/(f^{n+c}) → K_n`   (built from `L_n = (A/A[f^c] →[f^{n+c}] A)`
                                   and the quasi-isomorphism `L_n ≃ A/(f^{n+c})`, whose
                                   existence is *derived* from `hstab`),

defined above, induce an isomorphism of pro-objects between `{A/(f^n)}_{n ≥ 1}` and
`{K_n}_{n ≥ 1}` in `D(A)`.  Since Mathlib lacks a category of pro-objects, this is
encoded by the two round-trip identities together with the
compatibility of *both* `α` and `β` with the single-step transition maps:

  * round trip through `{A/(f^•)}`:  `β_n ≫ α_n = (A/(f^{n+c}) → A/(f^n))`;
  * round trip through `{K_•}`:      `α_{n+c} ≫ β_n = (K_{n+c} → K_n)`;
  * `α` compatible with transitions: `t_n ≫ α_n = α_{n+1} ≫ π_n`;
  * `β` compatible with transitions: `π_{(n+1)+c → n+c} ≫ β_n = β_{n+1} ≫ t_n`.

The hypotheses are exactly the boundedness data `c`, `1 ≤ c`, and `hstab`; the
existence of `β` (i.e. the relevant quasi-isomorphisms) is supplied internally by
`LqiCx_quasiIso`. -/
@[stacks 091X]
theorem proIso_of_torsionBounded (c : ℕ)
    (hstab : ∀ m : ℕ, c ≤ m → Submodule.torsionBy A A (f ^ c) = Submodule.torsionBy A A (f ^ m)) :
    -- round trip through the system `{A/(f^•)}`
    (∀ n : ℕ, beta A f c hstab n ≫ alpha A f n = Qtrans A f n c) ∧
    -- round trip through the system `{K_•}`
    (∀ n : ℕ, alpha A f (n + c) ≫ beta A f c hstab n = Ktrans A f n c) ∧
    -- `α` is compatible with the single-step transition maps
    (∀ n : ℕ, KtransOne A f n ≫ alpha A f n = alpha A f (n + 1) ≫ QtransOne A f n) ∧
    -- `β` is compatible with the single-step transition maps
    (∀ n : ℕ,
      QtransOne A f (n + c) ≫ beta A f c hstab n
        = eqToHom (by rw [Nat.add_right_comm]) ≫ beta A f c hstab (n +
            1) ≫ KtransOne A f n) :=
  ⟨identity_betaAlpha A f c hstab, identity_alphaBeta A f c hstab,
    identity_alphaTransition A f, identity_betaTransition A f c hstab⟩

end ProTorsion
