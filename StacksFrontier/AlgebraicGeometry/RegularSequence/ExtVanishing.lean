module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Center.Linear
public import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing of `Ext` below the length of a regular sequence of global functions

Let `X` be a scheme, let `N` and `E` be `𝒪_X`-modules and let `f_1, …, f_c ∈ Γ(X, 𝒪_X)` be
global functions such that

* each `f_j` annihilates `N`, and
* `f_1, …, f_c` is a weakly regular sequence on `E`: multiplication by `f_1` is injective on
  `E`, multiplication by `f_2` is injective on `E/f_1E`, and so on.

Then `Ext^q_{𝒪_X}(N, E) = 0` for every `q < c`.

The engine is two steps on the long exact sequence of `Ext` attached to
`0 → E --f--> E → E/fE → 0`, for `f` acting injectively on `E` and as zero on every
`Ext`-group out of `N`: in degree `0` injectivity of `f` on `E` forces `Hom(N, E) = 0`, and in
degree `q + 1` the group `Ext^{q+1}(N, E)` is a quotient of `Ext^q(N, E/fE)`. Both are proved
here for an arbitrary abelian category and an element of its centre, which is the form the
`𝒪_X`-module statement instantiates: a global function acts on every `𝒪_X`-module naturally,
hence as an element of the centre of `𝒪_X`-modules.

## Main definitions

* `Stacks.RegularSequence.globalSmulCenter`: a global function on a scheme, as an element of
  the centre of the category of `𝒪_X`-modules — multiplication by it on every `𝒪_X`-module at
  once.
* `Stacks.RegularSequence.IsWeaklyRegularOn`: a list of global functions is weakly regular on
  an `𝒪_X`-module, i.e. each successive multiplication is a monomorphism on the iterated
  quotient.

## Main results

* `Stacks.RegularSequence.subsingleton_ext_zero_of_mono` and
  `Stacks.RegularSequence.subsingleton_ext_succ_of_subsingleton_cokernel`: the two steps of the
  induction, in an arbitrary abelian category.
* `Stacks.RegularSequence.comp_mk₀_center_eq_zero`: an element of the centre annihilating `N`
  acts as zero on every `Ext`-group out of `N`.
* `Stacks.RegularSequence.subsingleton_ext_of_isWeaklyRegularOn`: **the vanishing**,
  `Ext^q_{𝒪_X}(N, E) = 0` for `q` below the length of the sequence.

## Implementation notes

No declaration here carries a `@[stacks 0G5I]` attribute. [Stacks, Tag 0G5I] states the
vanishing for a closed immersion `i : Z → X` which is *regular of codimension `c`*, `E`
locally free and `N = i_*F`, and its proof has two halves. What is proved here is the second
half, steps 2–5 of that proof — the induction along a regular sequence — in a form that needs
neither local freeness of `E` (weak regularity of the sequence on `E` is the hypothesis the
induction actually uses), nor that `N` be a pushforward (annihilation by the sequence is what
is used), nor that `X` be affine. The missing half is step 1, the reduction "it suffices to
prove this affine locally on `X`", which is the local-to-global spectral sequence of `Ext`,
[Stacks, Tag 0BQP]; this library has that tag's Ext sheaves and the second page
`H^p(X, SheafExt^q(K, L))` of its spectral sequence
(`Stacks.SheafOfModules.derivedSheafExt` and
`Stacks.SheafOfModules.hypercohomologySpectralSequence_e₂_derivedSheafExt`) but not the
convergence to `Ext^{p + q}` that the reduction consumes, and the regular sequence of
Tag 0G5I exists only locally on `X`, so the statement below cannot be specialised to the tag
without it.

The centre of the category is used rather than a `CategoryTheory.Linear` structure on
`𝒪_X`-modules over `Γ(X, 𝒪_X)`: the two steps need only that one morphism is natural in the
module, and `CategoryTheory.Linear.ofRingMorphism` recovers the scalar action on `Ext`-groups
from the centre inside the proof, so no linear structure is imposed on `X.Modules` globally.

`IsWeaklyRegularOn` takes the quotient as `CategoryTheory.Limits.cokernel` of multiplication,
so `E/(f_1, …, f_j)E` is the iterated cokernel and no quotient construction is chosen.

## References

* [Stacks Project, Tag 0G5I](https://stacks.math.columbia.edu/tag/0G5I)
* [Stacks Project, Tag 0BQP](https://stacks.math.columbia.edu/tag/0BQP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe w v u

namespace Stacks.RegularSequence

/-! ### The two steps of the induction, in an abelian category -/

section Core

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- An element `a` of the centre of an abelian category which annihilates `N` acts as zero on
every `Ext`-group out of `N`: postcomposing `x : Ext^q(N, M)` with `a` at `M` gives `0`. -/
theorem comp_mk₀_center_eq_zero (N M : C) (a : CatCenter C) (ha : a.app N = 0) {q : ℕ}
    (x : Abelian.Ext.{w} N M q) :
    x.comp (Abelian.Ext.mk₀ (a.app M)) (add_zero q) = 0 := by
  let : ∀ P Q : C, SMul (CatCenter C) (P ⟶ Q) :=
    Linear.smulOfRingMorphism (RingHom.id (CatCenter C))
  let : Linear (CatCenter C) C := Linear.ofRingMorphism (RingHom.id (CatCenter C))
  have hid (P : C) : a • 𝟙 P = a.app P := by
    show a.app P ≫ 𝟙 P = _
    exact Category.comp_id _
  have key : a • x = (Abelian.Ext.mk₀ (a • 𝟙 N)).comp x (zero_add q) := by
    rw [Abelian.Ext.mk₀_smul, Abelian.Ext.smul_comp, Abelian.Ext.mk₀_id_comp]
  rw [← hid M, ← Abelian.Ext.smul_eq_comp_mk₀, key, hid N, ha, Abelian.Ext.mk₀_zero,
    Abelian.Ext.zero_comp]

/-- **Degree zero.** If `g : E ⟶ E` is a monomorphism which acts as zero on `Hom(N, E)`, then
`Hom(N, E) = 0`: a morphism `N ⟶ E` killed by a monomorphism is zero. -/
theorem subsingleton_ext_zero_of_mono (N : C) {E : C} (g : E ⟶ E) [Mono g]
    (hg : ∀ x : Abelian.Ext.{w} N E 0, x.comp (Abelian.Ext.mk₀ g) (add_zero 0) = 0) :
    Subsingleton (Abelian.Ext.{w} N E 0) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  refine Abelian.Ext.postcomp_mk₀_injective_of_mono N g ?_
  rw [map_zero]
  exact hg x

/-- **The inductive step.** If `g : E ⟶ E` is a monomorphism which acts as zero on every
`Ext`-group out of `N`, then `Ext^{q+1}(N, E)` is a quotient of `Ext^q(N, E/gE)`; so it
vanishes as soon as the latter does. -/
theorem subsingleton_ext_succ_of_subsingleton_cokernel (N : C) {E : C} (g : E ⟶ E) [Mono g]
    (hg : ∀ (q : ℕ) (x : Abelian.Ext.{w} N E q),
      x.comp (Abelian.Ext.mk₀ g) (add_zero q) = 0)
    {q : ℕ} (h : Subsingleton (Abelian.Ext.{w} N (cokernel g) q)) :
    Subsingleton (Abelian.Ext.{w} N E (q + 1)) := by
  have hmono : Mono (ShortComplex.cokernelSequence g).f := by
    dsimp only [ShortComplex.cokernelSequence]
    infer_instance
  have hS : (ShortComplex.cokernelSequence g).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact g) hmono inferInstance
  have h' : Subsingleton (Abelian.Ext.{w} N (ShortComplex.cokernelSequence g).X₃ q) := h
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨x₃, hx₃⟩ :=
    Abelian.Ext.covariant_sequence_exact₁ N hS x (hg (q + 1) x) (n₀ := q) rfl
  rw [h'.elim x₃ 0, Abelian.Ext.zero_comp] at hx₃
  exact hx₃.symm

end Core

attribute [local instance] HasExt.standard

/-! ### Multiplication by a global function on all `𝒪_X`-modules at once -/

variable (X : Scheme.{u})

/-- Multiplication by a global function `r ∈ Γ(X, 𝒪_X)` on every `𝒪_X`-module, as an element
of the centre of the category of `𝒪_X`-modules: on sections over `U` it is multiplication by
the restriction of `r` to `U`. -/
def globalSmulCenter (r : Γ(X, ⊤)) : CatCenter X.Modules where
  app M := (⟨{
    app := fun U => by
      letI : CommRing (X.ringCatSheaf.obj.obj U) :=
        inferInstanceAs (CommRing (X.presheaf.obj U))
      exact ModuleCat.ofHom
        (X.ringCatSheaf.obj.map U.unop.leTop.op r •
          LinearMap.id (R := X.ringCatSheaf.obj.obj U) (M := M.val.obj U))
    naturality := fun {U V} f => by
      ext x
      change X.ringCatSheaf.obj.map V.unop.leTop.op r • (M.val.map f).hom x =
        (M.val.map f).hom (X.ringCatSheaf.obj.map U.unop.leTop.op r • x)
      rw [M.val.map_smul]
      congr 1
      exact congrArg (fun g => RingCat.Hom.hom g r)
        (X.ringCatSheaf.obj.map_comp U.unop.leTop.op f) }⟩ : M ⟶ M)
  naturality {M N} φ := by
    ext U x
    exact ((φ.val.app (.op U)).hom.map_smul _ x).symm

/-- On sections, the centre element `globalSmulCenter X r` is multiplication by the restriction
of `r`. -/
theorem globalSmulCenter_app_app (r : Γ(X, ⊤)) (M : X.Modules) (U : X.Opens) (m : Γ(M, U)) :
    ((globalSmulCenter X r).app M).app U m = X.presheaf.map U.leTop.op r • m := rfl

/-! ### Weakly regular sequences of global functions -/

/-- A list of global functions is *weakly regular* on an `𝒪_X`-module `E` when multiplication
by its head is a monomorphism on `E` and its tail is weakly regular on the quotient of `E` by
that multiplication. The empty list is weakly regular on every module. -/
@[ega "0 15.2.2" "special case"]
def IsWeaklyRegularOn {X : Scheme.{u}} : X.Modules → List Γ(X, ⊤) → Prop
  | _, [] => True
  | E, r :: fs =>
    Mono ((globalSmulCenter X r).app E) ∧
      IsWeaklyRegularOn (cokernel ((globalSmulCenter X r).app E)) fs

variable {X}

/-- The empty list is weakly regular on every `𝒪_X`-module. -/
@[simp]
theorem isWeaklyRegularOn_nil (E : X.Modules) : IsWeaklyRegularOn E [] := trivial

/-- Unfolding `IsWeaklyRegularOn` on a nonempty list: `r :: fs` is weakly regular on `E` if and
only if multiplication by `r` is a monomorphism on `E` and `fs` is weakly regular on its
cokernel. -/
theorem isWeaklyRegularOn_cons_iff (E : X.Modules) (r : Γ(X, ⊤)) (fs : List Γ(X, ⊤)) :
    IsWeaklyRegularOn E (r :: fs) ↔
      Mono ((globalSmulCenter X r).app E) ∧
        IsWeaklyRegularOn (cokernel ((globalSmulCenter X r).app E)) fs :=
  Iff.rfl

/-! ### The vanishing -/

/-- **`Ext` vanishes below the length of an annihilating regular sequence.** Let `N` and `E` be
`𝒪_X`-modules and let `fs` be a list of global functions on `X` each of which annihilates `N`
and which is weakly regular on `E`. Then `Ext^q_{𝒪_X}(N, E) = 0` for every `q` smaller than the
length of `fs`.

This is steps 2–5 of the proof of [Stacks, Tag 0G5I]. -/
theorem subsingleton_ext_of_isWeaklyRegularOn (N : X.Modules) :
    ∀ (fs : List Γ(X, ⊤)) (E : X.Modules),
      (∀ r ∈ fs, (globalSmulCenter X r).app N = 0) → IsWeaklyRegularOn E fs →
        ∀ q, q < fs.length → Subsingleton (Abelian.Ext N E q) := by
  intro fs
  induction fs with
  | nil => intro E _ _ q hq; simp at hq
  | cons r fs ih =>
    intro E hann hreg q hq
    rw [isWeaklyRegularOn_cons_iff] at hreg
    have := hreg.1
    have hr : (globalSmulCenter X r).app N = 0 := hann r List.mem_cons_self
    have hkill : ∀ (p : ℕ) (x : Abelian.Ext N E p),
        x.comp (Abelian.Ext.mk₀ ((globalSmulCenter X r).app E)) (add_zero p) = 0 :=
      fun p x => comp_mk₀_center_eq_zero N E (globalSmulCenter X r) hr x
    obtain _ | n := q
    · exact subsingleton_ext_zero_of_mono N _ (hkill 0)
    · refine subsingleton_ext_succ_of_subsingleton_cokernel N _ hkill ?_
      exact ih _ (fun s hs => hann s (List.mem_cons_of_mem r hs)) hreg.2 n
        (by simpa using Nat.succ_lt_succ_iff.mp hq)

end Stacks.RegularSequence

end
