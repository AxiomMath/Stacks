module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derivations along an algebra map

Let `R` and `C` be algebras over a commutative ring `A'`, let `w : R →ₐ[A'] C` and let `N` be a
`C`-module. A *derivation of `R` along `w`* with values in `N` is an additive map `δ : R → N`
killing the image of `A'` and satisfying `δ(r s) = w(r) δ(s) + w(s) δ(r)`; equivalently, an
`A'`-derivation `R → N` for the `R`-module structure on `N` induced by `w`. Such derivations
correspond to algebra maps `R → C ⊕ N` into the trivial square-zero extension lying over `w`.

## Main definitions

* `Stacks.ChartGlue.DerAlong w N`: the derivations of `R` along `w` with values in `N`, a
  `C`-module.
* `Stacks.ChartGlue.DerAlong.ofDiff`: the difference of two lifts along a square-zero ideal.
* `Stacks.ChartGlue.DerAlong.addHom`: the sum of an algebra map and a derivation along it with
  values in a square-zero ideal.
* `Stacks.ChartGlue.TrivExt C N`: the trivial square-zero extension of `C` by `N`.
* `Stacks.ChartGlue.DerAlong.liftHom`: the algebra map `R → C ⊕ N` over `w` attached to a
  derivation along `w`.
* `Stacks.ChartGlue.DerAlong.ofLift`: the derivation attached to an algebra map `R → C ⊕ N`
  over `w`.

## Main results

* `Stacks.ChartGlue.DerAlong.liftHom_ofLift`, `Stacks.ChartGlue.DerAlong.ofLift_liftHom`:
  derivations along `w` correspond to algebra maps `R → C ⊕ N` lying over `w`.

## Implementation notes

A derivation along `w` is `Derivation A' R N` for the `R`-module structure on `N` induced by `w`.
It is a separate structure because that module structure is not an instance, so derivations
along several algebra maps `R → C` with values in one `C`-module can be considered together.
-/

@[expose] public section

universe u v w

namespace Stacks.ChartGlue

/-! ### Derivations along an algebra map -/

variable {A' : Type w} [CommRing A'] {R : Type*} [CommRing R] [Algebra A' R]
  {C : Type u} [CommRing C] [Algebra A' C]

/-- A derivation of `R` along an algebra map `w : R → C`, with values in a `C`-module `N`. -/
@[ext, sga "3 VIIA 1.2.0" "special case"]
structure DerAlong (w : R →ₐ[A'] C) (N : Type v) [AddCommGroup N] [Module C N] where
  /-- The underlying function. -/
  toFun : R → N
  /-- Additivity. -/
  map_add' : ∀ r s, toFun (r + s) = toFun r + toFun s
  /-- Vanishing on the image of `A'`. -/
  map_algebraMap' : ∀ a : A', toFun (algebraMap A' R a) = 0
  /-- The Leibniz rule along `w`. -/
  leibniz' : ∀ r s, toFun (r * s) = w r • toFun s + w s • toFun r

namespace DerAlong

variable {N : Type v} [AddCommGroup N] [Module C N] {w : R →ₐ[A'] C}

/-- The coercion of a derivation along `w` to a function `R → N`. -/
instance : CoeFun (DerAlong w N) (fun _ ↦ R → N) := ⟨DerAlong.toFun⟩

/-- The field `toFun` is the coercion to a function. -/
@[simp] lemma toFun_eq_coe (δ : DerAlong w N) : δ.toFun = δ := rfl

/-- A derivation along `w` is additive. -/
lemma map_add (δ : DerAlong w N) (r s : R) : δ (r + s) = δ r + δ s := δ.map_add' r s

/-- A derivation along `w` vanishes on the image of `A'`. -/
lemma map_algebraMap (δ : DerAlong w N) (a : A') : δ (algebraMap A' R a) = 0 :=
  δ.map_algebraMap' a

/-- The Leibniz rule `δ (r s) = w r • δ s + w s • δ r`. -/
lemma leibniz (δ : DerAlong w N) (r s : R) : δ (r * s) = w r • δ s + w s • δ r :=
  δ.leibniz' r s

/-- A derivation along `w` vanishes at `0`. -/
@[simp] lemma map_zero (δ : DerAlong w N) : δ 0 = 0 := by
  have := δ.map_add 0 0
  rw [add_zero] at this
  exact add_eq_left.mp this.symm

/-- A derivation along `w` vanishes at `1`. -/
@[simp] lemma map_one (δ : DerAlong w N) : δ 1 = 0 := by
  have := δ.map_algebraMap 1
  rwa [_root_.map_one] at this

/-- A derivation along `w` commutes with negation. -/
lemma map_neg (δ : DerAlong w N) (r : R) : δ (-r) = -δ r :=
  eq_neg_of_add_eq_zero_left (by rw [← δ.map_add, neg_add_cancel, map_zero])

/-- A derivation along `w` commutes with subtraction. -/
lemma map_sub (δ : DerAlong w N) (r s : R) : δ (r - s) = δ r - δ s := by
  rw [sub_eq_add_neg, δ.map_add, δ.map_neg, ← sub_eq_add_neg]

/-- A derivation along `w` is `A'`-linear. -/
lemma map_smul (δ : DerAlong w N) (a : A') (r : R) :
    δ (a • r) = algebraMap A' C a • δ r := by
  rw [Algebra.smul_def, δ.leibniz, δ.map_algebraMap, smul_zero, add_zero, w.commutes]

/-- The zero derivation along `w`. -/
instance : Zero (DerAlong w N) := ⟨⟨fun _ ↦ 0, fun _ _ ↦ (add_zero 0).symm, fun _ ↦ rfl,
  fun _ _ ↦ by simp⟩⟩
/-- The pointwise sum of two derivations along `w`. -/
instance : Add (DerAlong w N) := ⟨fun δ ε ↦ ⟨fun r ↦ δ r + ε r,
  fun r s ↦ by rw [δ.map_add, ε.map_add]; abel,
  fun a ↦ by rw [δ.map_algebraMap, ε.map_algebraMap, add_zero],
  fun r s ↦ by rw [δ.leibniz, ε.leibniz, smul_add, smul_add]; abel⟩⟩
/-- The pointwise negation of a derivation along `w`. -/
instance : Neg (DerAlong w N) := ⟨fun δ ↦ ⟨fun r ↦ -δ r,
  fun r s ↦ by rw [δ.map_add, neg_add],
  fun a ↦ by rw [δ.map_algebraMap, neg_zero],
  fun r s ↦ by rw [δ.leibniz, neg_add, smul_neg, smul_neg]⟩⟩
/-- The pointwise scalar multiple of a derivation along `w` by an element of `C`. -/
instance : SMul C (DerAlong w N) := ⟨fun c δ ↦ ⟨fun r ↦ c • δ r,
  fun r s ↦ by rw [δ.map_add, smul_add],
  fun a ↦ by rw [δ.map_algebraMap, smul_zero],
  fun r s ↦ by rw [δ.leibniz, smul_add, smul_comm c (w r), smul_comm c (w s)]⟩⟩

/-- The zero derivation sends every element to `0`. -/
@[simp] lemma zero_apply (r : R) : (0 : DerAlong w N) r = 0 := rfl
/-- The sum of two derivations is computed pointwise. -/
@[simp] lemma add_apply (δ ε : DerAlong w N) (r : R) : (δ + ε) r = δ r + ε r := rfl
/-- The negation of a derivation is computed pointwise. -/
@[simp] lemma neg_apply (δ : DerAlong w N) (r : R) : (-δ) r = -δ r := rfl
/-- The scalar multiple of a derivation is computed pointwise. -/
@[simp] lemma smul_apply (c : C) (δ : DerAlong w N) (r : R) : (c • δ) r = c • δ r := rfl

/-- The derivations along `w` form an additive commutative group under pointwise operations. -/
instance : AddCommGroup (DerAlong w N) where
  add_assoc _ _ _ := DerAlong.ext (funext fun _ ↦ add_assoc _ _ _)
  zero_add _ := DerAlong.ext (funext fun _ ↦ zero_add _)
  add_zero _ := DerAlong.ext (funext fun _ ↦ add_zero _)
  add_comm _ _ := DerAlong.ext (funext fun _ ↦ add_comm _ _)
  neg_add_cancel _ := DerAlong.ext (funext fun _ ↦ neg_add_cancel _)
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- The difference of two derivations is computed pointwise. -/
@[simp] lemma sub_apply (δ ε : DerAlong w N) (r : R) : (δ - ε) r = δ r - ε r := by
  rw [sub_eq_add_neg, add_apply, neg_apply, ← sub_eq_add_neg]

/-- The derivations along `w` form a `C`-module under pointwise operations. -/
instance : Module C (DerAlong w N) where
  one_smul _ := DerAlong.ext (funext fun _ ↦ one_smul _ _)
  mul_smul _ _ _ := DerAlong.ext (funext fun _ ↦ mul_smul _ _ _)
  smul_zero _ := DerAlong.ext (funext fun _ ↦ smul_zero _)
  smul_add _ _ _ := DerAlong.ext (funext fun _ ↦ smul_add _ _ _)
  add_smul _ _ _ := DerAlong.ext (funext fun _ ↦ add_smul _ _ _)
  zero_smul _ := DerAlong.ext (funext fun _ ↦ zero_smul _ _)

/-- Postcomposition of a derivation with a `C`-linear map. -/
def postcomp {N' : Type*} [AddCommGroup N'] [Module C N'] (h : N →ₗ[C] N') (δ : DerAlong w N) :
    DerAlong w N' :=
  ⟨fun r ↦ h (δ r), fun r s ↦ by rw [δ.map_add, _root_.map_add],
    fun a ↦ by rw [δ.map_algebraMap, _root_.map_zero],
    fun r s ↦ by rw [δ.leibniz, _root_.map_add, h.map_smul, h.map_smul]⟩

/-- Postcomposition with `h` sends `δ r` to `h (δ r)`. -/
@[simp] lemma postcomp_apply {N' : Type*} [AddCommGroup N'] [Module C N'] (h : N →ₗ[C] N')
    (δ : DerAlong w N) (r : R) : postcomp h δ r = h (δ r) := rfl

/-- The pair of two derivations along `w`, with values in the product module. -/
def prod {N' : Type*} [AddCommGroup N'] [Module C N'] (δ : DerAlong w N) (ε : DerAlong w N') :
    DerAlong w (N × N') :=
  ⟨fun r ↦ (δ r, ε r), fun r s ↦ by rw [δ.map_add, ε.map_add]; rfl,
    fun a ↦ by rw [δ.map_algebraMap, ε.map_algebraMap]; rfl,
    fun r s ↦ by rw [δ.leibniz, ε.leibniz]; rfl⟩

/-- The pair `δ.prod ε` sends `r` to `(δ r, ε r)`. -/
@[simp] lemma prod_apply {N' : Type*} [AddCommGroup N'] [Module C N'] (δ : DerAlong w N)
    (ε : DerAlong w N') (r : R) : δ.prod ε r = (δ r, ε r) := rfl

/-- The first component of `δ.prod ε` is `δ`. -/
lemma postcomp_fst_prod {N' : Type*} [AddCommGroup N'] [Module C N'] (δ : DerAlong w N)
    (ε : DerAlong w N') : (δ.prod ε).postcomp (LinearMap.fst C N N') = δ := rfl

/-- The second component of `δ.prod ε` is `ε`. -/
lemma postcomp_snd_prod {N' : Type*} [AddCommGroup N'] [Module C N'] (δ : DerAlong w N)
    (ε : DerAlong w N') : (δ.prod ε).postcomp (LinearMap.snd C N N') = ε := rfl

/-- A derivation with values in `N × N'` is the pair of its two components. -/
lemma eq_prod {N' : Type*} [AddCommGroup N'] [Module C N'] (θ : DerAlong w (N × N')) :
    θ = (θ.postcomp (LinearMap.fst C N N')).prod (θ.postcomp (LinearMap.snd C N N')) := rfl

/-- The sum `δ + ε` is the pair `δ.prod ε` postcomposed with the sum map `N × N → N`. -/
lemma add_eq_postcomp_prod (δ ε : DerAlong w N) :
    δ + ε = (δ.prod ε).postcomp (LinearMap.coprod LinearMap.id LinearMap.id) := rfl

/-- The scalar multiple `c • δ` is `δ` postcomposed with multiplication by `c`. -/
lemma smul_eq_postcomp (c : C) (δ : DerAlong w N) :
    c • δ = δ.postcomp (c • LinearMap.id) := rfl

/-- A derivation along `w : R → C` with values in a module over a `C`-algebra `D`, read as a
derivation along the composite `R → C → D`. -/
def baseChange {D : Type*} [CommRing D] [Algebra A' D] [Algebra C D] (f : C →ₐ[A'] D)
    (hf : ∀ c, algebraMap C D c = f c) {N' : Type*} [AddCommGroup N'] [Module C N']
    [Module D N'] [IsScalarTower C D N'] (δ : DerAlong w N') : DerAlong (f.comp w) N' :=
  ⟨δ, δ.map_add, δ.map_algebraMap, fun r s ↦ by
    rw [δ.leibniz, AlgHom.comp_apply, AlgHom.comp_apply, ← hf, ← hf, algebraMap_smul,
      algebraMap_smul]⟩

/-- The base change of `δ` has the same underlying function as `δ`. -/
@[simp] lemma baseChange_apply {D : Type*} [CommRing D] [Algebra A' D] [Algebra C D]
    (f : C →ₐ[A'] D) (hf : ∀ c, algebraMap C D c = f c) {N' : Type*} [AddCommGroup N']
    [Module C N'] [Module D N'] [IsScalarTower C D N'] (δ : DerAlong w N') (r : R) :
    δ.baseChange f hf r = δ r := rfl

/-- Pushforward of a derivation along an algebra map `f : C → D` and an `f`-semilinear map of
modules. -/
def map {D : Type*} [CommRing D] [Algebra A' D] (f : C →ₐ[A'] D) {N' : Type*} [AddCommGroup N']
    [Module D N'] (g : N →ₛₗ[(f : C →+* D)] N') (δ : DerAlong w N) : DerAlong (f.comp w) N' :=
  ⟨fun r ↦ g (δ r), fun r s ↦ by rw [δ.map_add, _root_.map_add],
    fun a ↦ by rw [δ.map_algebraMap, _root_.map_zero],
    fun r s ↦ by rw [δ.leibniz, _root_.map_add, g.map_smulₛₗ, g.map_smulₛₗ]; rfl⟩

/-- The pushforward `δ.map f g` sends `r` to `g (δ r)`. -/
@[simp] lemma map_apply {D : Type*} [CommRing D] [Algebra A' D] (f : C →ₐ[A'] D) {N' : Type*}
    [AddCommGroup N'] [Module D N'] (g : N →ₛₗ[(f : C →+* D)] N') (δ : DerAlong w N) (r : R) :
    δ.map f g r = g (δ r) := rfl

/-- Pushforward along `f` and `g` is additive in the derivation. -/
lemma map_add_map {D : Type*} [CommRing D] [Algebra A' D] (f : C →ₐ[A'] D) {N' : Type*}
    [AddCommGroup N'] [Module D N'] (g : N →ₛₗ[(f : C →+* D)] N') (δ ε : DerAlong w N) :
    (δ + ε).map f g = δ.map f g + ε.map f g :=
  DerAlong.ext (funext fun _ ↦ _root_.map_add g _ _)

/-- Pushforward along `f` and `g` commutes with subtraction of derivations. -/
lemma map_sub_map {D : Type*} [CommRing D] [Algebra A' D] (f : C →ₐ[A'] D) {N' : Type*}
    [AddCommGroup N'] [Module D N'] (g : N →ₛₗ[(f : C →+* D)] N') (δ ε : DerAlong w N) :
    (δ - ε).map f g = δ.map f g - ε.map f g :=
  DerAlong.ext (funext fun r ↦ by simp [_root_.map_sub])

/-- A derivation along `w`, read as a derivation along an algebra map `w'` equal to `w`. -/
def cast {w' : R →ₐ[A'] C} (h : w = w') (δ : DerAlong w N) : DerAlong w' N :=
  ⟨δ, δ.map_add, δ.map_algebraMap, fun r s ↦ by subst h; exact δ.leibniz r s⟩

/-- The cast of `δ` has the same underlying function as `δ`. -/
@[simp] lemma cast_apply {w' : R →ₐ[A'] C} (h : w = w') (δ : DerAlong w N) (r : R) :
    δ.cast h r = δ r := rfl

/-- The inverse of `baseChange`: a derivation along `f ∘ w` with values in a `D`-module, read as
a derivation along `w` for the restricted `C`-module structure. -/
def descend {D : Type*} [CommRing D] [Algebra A' D] [Algebra C D] (f : C →ₐ[A'] D)
    (hf : ∀ c, algebraMap C D c = f c) {N' : Type*} [AddCommGroup N'] [Module C N']
    [Module D N'] [IsScalarTower C D N'] (δ : DerAlong (f.comp w) N') : DerAlong w N' :=
  ⟨δ, δ.map_add, δ.map_algebraMap, fun r s ↦ by
    rw [δ.leibniz, AlgHom.comp_apply, AlgHom.comp_apply, ← hf, ← hf, algebraMap_smul,
      algebraMap_smul]⟩

/-- The descent of `δ` has the same underlying function as `δ`. -/
@[simp] lemma descend_apply {D : Type*} [CommRing D] [Algebra A' D] [Algebra C D]
    (f : C →ₐ[A'] D) (hf : ∀ c, algebraMap C D c = f c) {N' : Type*} [AddCommGroup N']
    [Module C N'] [Module D N'] [IsScalarTower C D N'] (δ : DerAlong (f.comp w) N') (r : R) :
    δ.descend f hf r = δ r := rfl

/-- The difference of two algebra maps `R → C` agreeing modulo a square-zero ideal `J`, as a
derivation along the second with values in `J`. -/
def ofDiff (J : Ideal C) (hJ : J ^ 2 = ⊥) (w₁ w₂ : R →ₐ[A'] C) (h : ∀ r, w₁ r - w₂ r ∈ J) :
    DerAlong w₂ J :=
  ⟨fun r ↦ ⟨w₁ r - w₂ r, h r⟩,
    fun r s ↦ Subtype.ext (by simp only [_root_.map_add, Submodule.coe_add]; abel),
    fun a ↦ Subtype.ext (by simp),
    fun r s ↦ Subtype.ext (by
      have h0 : (w₁ r - w₂ r) * (w₁ s - w₂ s) = 0 := by
        rw [← Ideal.mem_bot, ← hJ, pow_two]
        exact Ideal.mul_mem_mul (h r) (h s)
      simp only [_root_.map_mul, Submodule.coe_add, Submodule.coe_smul, smul_eq_mul]
      linear_combination h0)⟩

/-- The derivation `ofDiff J hJ w₁ w₂ h` sends `r` to `w₁ r - w₂ r`. -/
@[simp] lemma coe_ofDiff_apply (J : Ideal C) (hJ : J ^ 2 = ⊥) (w₁ w₂ : R →ₐ[A'] C)
    (h : ∀ r, w₁ r - w₂ r ∈ J) (r : R) : (ofDiff J hJ w₁ w₂ h r : C) = w₁ r - w₂ r := rfl

/-- The sum `w + δ : R → C` of an algebra map and a derivation along it with values in a
square-zero ideal. -/
def addHom (J : Ideal C) (hJ : J ^ 2 = ⊥) (δ : DerAlong w J) : R →ₐ[A'] C where
  toFun r := w r + δ r
  map_one' := by simp
  map_mul' r s := by
    have h0 : (δ r : C) * δ s = 0 := by
      rw [← Ideal.mem_bot, ← hJ, pow_two]
      exact Ideal.mul_mem_mul (δ r).2 (δ s).2
    simp only [_root_.map_mul, δ.leibniz, Submodule.coe_add, Submodule.coe_smul, smul_eq_mul]
    linear_combination -h0
  map_zero' := by simp
  map_add' r s := by simp only [_root_.map_add, δ.map_add, Submodule.coe_add]; abel
  commutes' a := by simp [δ.map_algebraMap]

/-- The algebra map `addHom J hJ δ` sends `r` to `w r + δ r`. -/
@[simp] lemma addHom_apply (J : Ideal C) (hJ : J ^ 2 = ⊥) (δ : DerAlong w J) (r : R) :
    addHom J hJ δ r = w r + δ r := rfl

end DerAlong

/-! ### The trivial square-zero extension of a commutative ring -/

section TrivExt

variable (C) (N : Type v) [AddCommGroup N] [Module C N]

/-- The trivial square-zero extension `C ⊕ N` of a commutative ring by a module: Mathlib's
`TrivSqZeroExt C N` for the bimodule structure on `N` in which the right action is the left
one, which is the only one a module over a commutative ring carries. -/
@[ega "0 16.4.6.4",
  ega "0 18.2.3",
  ega "0 20.4.13",
  ega "0 22.1.3",
  ega "IV 20.2.13" "more general",
  ega "IV 20.2.16" "partial", sga "3 II 2.1" "special case", sga "7 VI 1.15", sga "7 VI 1.3(c)"]
def TrivExt : Type _ := TrivSqZeroExt C N

namespace TrivExt

/-- The right action of `C` on `N`, through commutativity. -/
abbrev opModule : Module Cᵐᵒᵖ N :=
  Module.compHom N ((RingHom.id C).fromOpposite fun x y ↦ Commute.all x y)

/-- The trivial square-zero extension `C ⊕ N` is a commutative ring. -/
instance : CommRing (TrivExt C N) :=
  letI := opModule C N
  haveI : IsCentralScalar C N := ⟨fun _ _ ↦ rfl⟩
  inferInstanceAs (CommRing (TrivSqZeroExt C N))

/-- The inclusion of the ring. -/
def inl : C →+* TrivExt C N :=
  letI := opModule C N
  haveI : IsCentralScalar C N := ⟨fun _ _ ↦ rfl⟩
  TrivSqZeroExt.inlHom C N

/-- The `A'`-algebra structure on `C ⊕ N` through the inclusion of `C`. -/
instance : Algebra A' (TrivExt C N) := ((inl C N).comp (algebraMap A' C)).toAlgebra

variable {C N}

/-- The ring component. -/
def fst (x : TrivExt C N) : C := TrivSqZeroExt.fst (R := C) (M := N) x

/-- The module component. -/
def snd (x : TrivExt C N) : N := TrivSqZeroExt.snd (R := C) (M := N) x

/-- An element from its two components. -/
def mk (c : C) (n : N) : TrivExt C N := (c, n)

omit [CommRing C] [AddCommGroup N] [Module C N] in
/-- The ring component of `mk c n` is `c`. -/
@[simp] lemma fst_mk (c : C) (n : N) : (mk c n).fst = c := rfl
omit [CommRing C] [AddCommGroup N] [Module C N] in
/-- The module component of `mk c n` is `n`. -/
@[simp] lemma snd_mk (c : C) (n : N) : (mk c n).snd = n := rfl

omit [CommRing C] [AddCommGroup N] [Module C N] in
/-- Two elements of `C ⊕ N` with the same components are equal. -/
@[ext] lemma ext {x y : TrivExt C N} (h₁ : x.fst = y.fst) (h₂ : x.snd = y.snd) : x = y :=
  TrivSqZeroExt.ext h₁ h₂

/-- The ring component of `0` is `0`. -/
@[simp] lemma fst_zero : (0 : TrivExt C N).fst = 0 := rfl
/-- The module component of `0` is `0`. -/
@[simp] lemma snd_zero : (0 : TrivExt C N).snd = 0 := rfl
/-- The ring component of `1` is `1`. -/
@[simp] lemma fst_one : (1 : TrivExt C N).fst = 1 := rfl
/-- The module component of `1` is `0`. -/
@[simp] lemma snd_one : (1 : TrivExt C N).snd = 0 := rfl
/-- The ring component of a sum is the sum of the ring components. -/
@[simp] lemma fst_add (x y : TrivExt C N) : (x + y).fst = x.fst + y.fst := rfl
/-- The module component of a sum is the sum of the module components. -/
@[simp] lemma snd_add (x y : TrivExt C N) : (x + y).snd = x.snd + y.snd := rfl
/-- The ring component of a product is the product of the ring components. -/
@[simp] lemma fst_mul (x y : TrivExt C N) : (x * y).fst = x.fst * y.fst := rfl
/-- The module component of `x * y` is `x.fst • y.snd + y.fst • x.snd`. -/
@[simp] lemma snd_mul (x y : TrivExt C N) : (x * y).snd = x.fst • y.snd + y.fst • x.snd := rfl
/-- The ring component of `inl C N c` is `c`. -/
@[simp] lemma fst_inl (c : C) : (inl C N c).fst = c := rfl
/-- The module component of `inl C N c` is `0`. -/
@[simp] lemma snd_inl (c : C) : (inl C N c).snd = 0 := rfl
/-- The ring component of the image of `a : A'` is its image in `C`. -/
@[simp] lemma fst_algebraMap (a : A') :
    (algebraMap A' (TrivExt C N) a).fst = algebraMap A' C a := rfl
/-- The module component of the image of `a : A'` is `0`. -/
@[simp] lemma snd_algebraMap (a : A') : (algebraMap A' (TrivExt C N) a).snd = 0 := rfl

variable (A' C N)

/-- The projection of the trivial square-zero extension to the ring. -/
def fstHom : TrivExt C N →ₐ[A'] C where
  toFun := TrivExt.fst
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The projection `fstHom` sends an element to its ring component. -/
@[simp] lemma fstHom_apply (x : TrivExt C N) : fstHom A' C N x = x.fst := rfl

/-- The inclusion of the ring, as an algebra map. -/
def inlHom : C →ₐ[A'] TrivExt C N where
  toRingHom := inl C N
  commutes' _ := rfl

/-- The algebra map `inlHom` is the inclusion `inl`. -/
@[simp] lemma inlHom_apply (c : C) : inlHom A' C N c = inl C N c := rfl

/-- The projection to the ring is a retraction of the inclusion of the ring. -/
lemma fstHom_comp_inlHom : (fstHom A' C N).comp (inlHom A' C N) = AlgHom.id A' C := rfl

/-- The projection to the ring is surjective. -/
lemma fstHom_surjective : Function.Surjective (fstHom A' C N) :=
  fun c ↦ ⟨inlHom A' C N c, rfl⟩

/-- The kernel of the projection to the ring has square zero. -/
@[ega "0 20.4.13" "partial"]
lemma ker_fstHom_sq : RingHom.ker (fstHom A' C N) ^ 2 = ⊥ := by
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro x hx y hy
  rw [RingHom.mem_ker] at hx hy
  rw [Ideal.mem_bot]
  exact ext (by simp [fst_mul, show x.fst = 0 from hx])
    (by simp [snd_mul, show x.fst = 0 from hx, show y.fst = 0 from hy])

variable {A' C N}

/-- The trivial square-zero extension is functorial in a `C`-linear map of the module. -/
def map {N' : Type*} [AddCommGroup N'] [Module C N'] (h : N →ₗ[C] N') :
    TrivExt C N →ₐ[A'] TrivExt C N' where
  toFun x := mk x.fst (h x.snd)
  map_one' := ext rfl (map_zero h)
  map_mul' x y := ext rfl (by simp [snd_mul])
  map_zero' := ext rfl (map_zero h)
  map_add' x y := ext rfl (by simp [snd_add])
  commutes' a := ext rfl (by simp)

/-- The functorial map `map h` preserves the ring component. -/
@[simp] lemma fst_map {N' : Type*} [AddCommGroup N'] [Module C N'] (h : N →ₗ[C] N')
    (x : TrivExt C N) : (map (A' := A') h x).fst = x.fst := rfl
/-- The functorial map `map h` applies `h` to the module component. -/
@[simp] lemma snd_map {N' : Type*} [AddCommGroup N'] [Module C N'] (h : N →ₗ[C] N')
    (x : TrivExt C N) : (map (A' := A') h x).snd = h x.snd := rfl

/-- The functorial map `map h` lies over the identity of `C`. -/
lemma fstHom_comp_map {N' : Type*} [AddCommGroup N'] [Module C N'] (h : N →ₗ[C] N') :
    (fstHom A' C N').comp (map h) = fstHom A' C N := rfl

/-- Change of the ring of a trivial square-zero extension along an algebra map `h : C → C'`, for
a `C'`-module viewed as a `C`-module through `h`. -/
def baseMap {C' : Type*} [CommRing C'] [Algebra A' C'] [Module C' N] [Algebra C C']
    [IsScalarTower C C' N] (h : C →ₐ[A'] C') (hh : ∀ c, algebraMap C C' c = h c) :
    TrivExt C N →ₐ[A'] TrivExt C' N where
  toFun x := mk (h x.fst) x.snd
  map_one' := ext (map_one h) rfl
  map_mul' x y := ext (map_mul h _ _) (by
    simp only [snd_mul, snd_mk, fst_mk, ← hh, algebraMap_smul])
  map_zero' := ext (map_zero h) rfl
  map_add' x y := ext (map_add h _ _) rfl
  commutes' a := ext (h.commutes a) rfl

/-- The ring component of `baseMap h hh x` is `h x.fst`. -/
@[simp] lemma fst_baseMap {C' : Type*} [CommRing C'] [Algebra A' C'] [Module C' N] [Algebra C C']
    [IsScalarTower C C' N] (h : C →ₐ[A'] C') (hh : ∀ c, algebraMap C C' c = h c)
    (x : TrivExt C N) : (baseMap h hh x).fst = h x.fst := rfl
/-- The module component of `baseMap h hh x` is `x.snd`. -/
@[simp] lemma snd_baseMap {C' : Type*} [CommRing C'] [Algebra A' C'] [Module C' N] [Algebra C C']
    [IsScalarTower C C' N] (h : C →ₐ[A'] C') (hh : ∀ c, algebraMap C C' c = h c)
    (x : TrivExt C N) : (baseMap h hh x).snd = x.snd := rfl

/-- Functoriality of the trivial square-zero extension in an algebra map of the rings and a
semilinear map of the modules. -/
def mapSemilinear {D : Type*} [CommRing D] [Algebra A' D] {N' : Type*} [AddCommGroup N']
    [Module D N'] (f : C →ₐ[A'] D) (g : N →ₛₗ[(f : C →+* D)] N') :
    TrivExt C N →ₐ[A'] TrivExt D N' where
  toFun x := mk (f x.fst) (g x.snd)
  map_one' := ext (map_one f) (map_zero g)
  map_mul' x y := ext (map_mul f _ _) (by simp [snd_mul, g.map_smulₛₗ])
  map_zero' := ext (map_zero f) (map_zero g)
  map_add' x y := ext (map_add f _ _) (by simp [snd_add])
  commutes' a := ext (f.commutes a) (by simp)

/-- The ring component of `mapSemilinear f g x` is `f x.fst`. -/
@[simp] lemma fst_mapSemilinear {D : Type*} [CommRing D] [Algebra A' D] {N' : Type*}
    [AddCommGroup N'] [Module D N'] (f : C →ₐ[A'] D) (g : N →ₛₗ[(f : C →+* D)] N')
    (x : TrivExt C N) : (mapSemilinear f g x).fst = f x.fst := rfl
/-- The module component of `mapSemilinear f g x` is `g x.snd`. -/
@[simp] lemma snd_mapSemilinear {D : Type*} [CommRing D] [Algebra A' D] {N' : Type*}
    [AddCommGroup N'] [Module D N'] (f : C →ₐ[A'] D) (g : N →ₛₗ[(f : C →+* D)] N')
    (x : TrivExt C N) : (mapSemilinear f g x).snd = g x.snd := rfl

/-- For a square-zero ideal `J` of `C`, the sum map `C ⊕ J → C`, `(c, j) ↦ c + j`. -/
def sumHom (J : Ideal C) (hJ : J ^ 2 = ⊥) : TrivExt C J →ₐ[A'] C where
  toFun x := x.fst + x.snd
  map_one' := by simp
  map_mul' x y := by
    have h0 : (x.snd : C) * y.snd = 0 := by
      rw [← Ideal.mem_bot, ← hJ, pow_two]
      exact Ideal.mul_mem_mul x.snd.2 y.snd.2
    simp only [fst_mul, snd_mul, Submodule.coe_add, Submodule.coe_smul, smul_eq_mul]
    linear_combination -h0
  map_zero' := by simp
  map_add' x y := by simp only [fst_add, snd_add, Submodule.coe_add]; abel
  commutes' a := by simp

/-- The sum map sends `x` to `x.fst + x.snd`. -/
@[simp] lemma sumHom_apply (J : Ideal C) (hJ : J ^ 2 = ⊥) (x : TrivExt C J) :
    sumHom (A' := A') J hJ x = x.fst + x.snd := rfl

end TrivExt

namespace DerAlong

variable {C N} {w : R →ₐ[A'] C}

/-- The algebra map `R → C ⊕ N` over `w` attached to a derivation along `w`. -/
def liftHom (δ : DerAlong w N) : R →ₐ[A'] TrivExt C N where
  toFun r := TrivExt.mk (w r) (δ r)
  map_one' := TrivExt.ext (_root_.map_one w) δ.map_one
  map_mul' r s := TrivExt.ext (_root_.map_mul w r s) (δ.leibniz r s)
  map_zero' := TrivExt.ext (_root_.map_zero w) δ.map_zero
  map_add' r s := TrivExt.ext (_root_.map_add w r s) (δ.map_add r s)
  commutes' a := TrivExt.ext (w.commutes a) (δ.map_algebraMap a)

/-- The ring component of `δ.liftHom r` is `w r`. -/
@[simp] lemma fst_liftHom (δ : DerAlong w N) (r : R) : (δ.liftHom r).fst = w r := rfl
/-- The module component of `δ.liftHom r` is `δ r`. -/
@[simp] lemma snd_liftHom (δ : DerAlong w N) (r : R) : (δ.liftHom r).snd = δ r := rfl

/-- The lift of `δ` lies over `w`. -/
lemma fstHom_comp_liftHom (δ : DerAlong w N) :
    (TrivExt.fstHom A' C N).comp δ.liftHom = w := AlgHom.ext fun _ ↦ rfl

/-- The derivation along `w` attached to an algebra map `R → C ⊕ N` lying over `w`. -/
def ofLift (W : R →ₐ[A'] TrivExt C N) (hW : (TrivExt.fstHom A' C N).comp W = w) :
    DerAlong w N :=
  ⟨fun r ↦ (W r).snd, fun r s ↦ by simp only [_root_.map_add, TrivExt.snd_add],
    fun a ↦ by rw [W.commutes]; exact TrivExt.snd_algebraMap (A' := A') a,
    fun r s ↦ by
      have h₁ : (W r).fst = w r := congrArg (fun φ : R →ₐ[A'] C ↦ φ r) hW
      have h₂ : (W s).fst = w s := congrArg (fun φ : R →ₐ[A'] C ↦ φ s) hW
      rw [_root_.map_mul, TrivExt.snd_mul, h₁, h₂]⟩

/-- The derivation `ofLift W hW` sends `r` to the module component of `W r`. -/
@[simp] lemma ofLift_apply (W : R →ₐ[A'] TrivExt C N) (hW : (TrivExt.fstHom A' C N).comp W = w)
    (r : R) : ofLift W hW r = (W r).snd := rfl

/-- The lift of `ofLift W hW` is `W`. -/
lemma liftHom_ofLift (W : R →ₐ[A'] TrivExt C N) (hW : (TrivExt.fstHom A' C N).comp W = w) :
    (ofLift W hW).liftHom = W := by
  ext r
  · exact (AlgHom.congr_fun hW r).symm
  · rfl

/-- The derivation attached to the lift of `δ` is `δ`. -/
lemma ofLift_liftHom (δ : DerAlong w N) : ofLift δ.liftHom δ.fstHom_comp_liftHom = δ :=
  DerAlong.ext rfl

/-- A derivation along `w` is determined by its lift. -/
lemma liftHom_injective : Function.Injective (liftHom : DerAlong w N → R →ₐ[A'] TrivExt C N) :=
  fun _ _ h ↦ DerAlong.ext (funext fun r ↦
    congrArg TrivExt.snd (AlgHom.congr_fun h r))

/-- The lift of `δ.postcomp h` is the lift of `δ` followed by `TrivExt.map h`. -/
lemma liftHom_postcomp {N' : Type*} [AddCommGroup N'] [Module C N'] (h : N →ₗ[C] N')
    (δ : DerAlong w N) : (δ.postcomp h).liftHom = (TrivExt.map h).comp δ.liftHom :=
  AlgHom.ext fun _ ↦ rfl

/-- The lift of `δ.baseChange f hf` is the lift of `δ` followed by `TrivExt.baseMap f hf`. -/
lemma liftHom_baseChange {D : Type*} [CommRing D] [Algebra A' D] [Algebra C D] (f : C →ₐ[A'] D)
    (hf : ∀ c, algebraMap C D c = f c) {N' : Type*} [AddCommGroup N'] [Module C N']
    [Module D N'] [IsScalarTower C D N'] (δ : DerAlong w N') :
    (δ.baseChange f hf).liftHom = (TrivExt.baseMap f hf).comp δ.liftHom :=
  AlgHom.ext fun _ ↦ rfl

/-- The lift of `δ.map f g` is the lift of `δ` followed by `TrivExt.mapSemilinear f g`. -/
lemma liftHom_map {D : Type*} [CommRing D] [Algebra A' D] (f : C →ₐ[A'] D) {N' : Type*}
    [AddCommGroup N'] [Module D N'] (g : N →ₛₗ[(f : C →+* D)] N') (δ : DerAlong w N) :
    (δ.map f g).liftHom = (TrivExt.mapSemilinear f g).comp δ.liftHom :=
  AlgHom.ext fun _ ↦ rfl

/-- The sum `w + δ` is the composite of the lift with the sum map. -/
lemma addHom_eq_comp (J : Ideal C) (hJ : J ^ 2 = ⊥) (δ : DerAlong w J) :
    addHom J hJ δ = (TrivExt.sumHom J hJ).comp δ.liftHom :=
  AlgHom.ext fun _ ↦ rfl

/-- The zero derivation lifts to the inclusion of the ring. -/
lemma liftHom_zero : (0 : DerAlong w N).liftHom = (TrivExt.inlHom A' C N).comp w :=
  AlgHom.ext fun _ ↦ rfl

end DerAlong

end TrivExt

end Stacks.ChartGlue

end
