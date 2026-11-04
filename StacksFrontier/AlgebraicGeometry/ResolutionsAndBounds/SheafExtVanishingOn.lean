module

public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.InternalHomInjectiveSections

/-!
# Vanishing of the sheaf Ext on an open subset

Let `(X, 𝒪_X)` be a ringed space, `G` an `𝒪_X`-module with an injective resolution `I^•`, and
`A` an `𝒪_X`-module. The cohomology sheaves of `𝓗om(A, I^•)` are the sheaf Ext's
`𝓔xt^q(A, G)`. This file records how their vanishing on an open subset `W` propagates:

* if `A|_W = 0` then `𝓔xt^q(A, G)|_W = 0` for every `q`;
* along a short exact sequence `0 ⟶ A' ⟶ A ⟶ A'' ⟶ 0`, through the long exact sequence of
  sheaf Ext's;
* for a finite free `A`, `𝓔xt^q(A, G) = 0` for every `q ≥ 1`.

## Main definitions

* `Stacks.SheafHomInjective.VanishesOn`: a sheaf of modules vanishes on an open subset when all
  its sections over opens contained in it vanish.

## Main results

* `Stacks.SheafHomInjective.vanishesOn_homology_cx_of_vanishesOn`: vanishing of `𝓔xt` where the
  first variable vanishes.
* `Stacks.SheafHomInjective.vanishesOn_homology_X₂_of_shortExact` and its two companions: the
  three ways the long exact sequence propagates vanishing.
* `Stacks.SheafHomInjective.isZero_homology_cx_free`: the vanishing for a finite free module.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules.InternalHom Stacks.PresheafOfModules.InternalHom

universe u

namespace Stacks.SheafHomInjective

variable {X : Type u} [TopologicalSpace X]
    {O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

/-- A sheaf of modules **vanishes on** an open subset `W` when all its sections over the opens
contained in `W` vanish. -/
def VanishesOn (E : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (W : Opens X) :
    Prop :=
  ∀ V : Opens X, V ≤ W → ∀ s : E.val.obj (op V), s = 0

/-- A module vanishing on `W` vanishes on every open subset `W' ≤ W`. -/
theorem VanishesOn.mono {E : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    {W W' : Opens X} (h : VanishesOn E W) (hW : W' ≤ W) : VanishesOn E W' :=
  fun V hV => h V (hV.trans hW)

/-- If `E` vanishes on `W`, then its restriction `E.over W` is a zero object. -/
theorem isZero_over_of_vanishesOn
    {E : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)} {W : Opens X}
    (h : VanishesOn E W) : IsZero (E.over W) := by
  rw [IsZero.iff_id_eq_zero]
  ext V s
  exact h V.unop.left (leOfHom V.unop.hom) s

/-- If the restriction `E.over W` is a zero object, then `E` vanishes on `W`. -/
theorem vanishesOn_of_isZero_over
    {E : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)} {W : Opens X}
    (h : IsZero (E.over W)) : VanishesOn E W := by
  intro V hV s
  exact congrArg (fun f => f.val.app (op (Over.mk (homOfLE hV))) s) (h.eq_of_src (𝟙 _) 0)

/-- `E` vanishes on `W` if and only if `E.over V` is a zero object for every open `V ≤ W`. -/
theorem vanishesOn_iff_forall_isZero_over
    {E : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)} {W : Opens X} :
    VanishesOn E W ↔ ∀ V : Opens X, V ≤ W → IsZero (E.over V) :=
  ⟨fun h _ hV => isZero_over_of_vanishesOn (h.mono hV),
    fun h => vanishesOn_of_isZero_over (h W le_rfl)⟩

/-- In an exact sequence, vanishing of the outer terms on `W` forces vanishing of the middle. -/
theorem vanishesOn_X₂
    {T : ShortComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))}
    (hT : T.Exact) {W : Opens X} (h₁ : VanishesOn T.X₁ W) (h₃ : VanishesOn T.X₃ W) :
    VanishesOn T.X₂ W := by
  rw [vanishesOn_iff_forall_isZero_over] at h₁ h₃ ⊢
  intro V hV
  have := SheafOfModules.overFunctor_preservesHomology.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf O) V
  exact (hT.map
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) V)).isZero_X₂
    ((h₁ V hV).eq_of_src _ _) ((h₃ V hV).eq_of_tgt _ _)

/-- A subobject of a module vanishing on `W` vanishes on `W`. -/
theorem vanishesOn_of_mono
    {E E' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (f : E ⟶ E') [Mono f]
    {W : Opens X} (h : VanishesOn E' W) : VanishesOn E W := by
  rw [vanishesOn_iff_forall_isZero_over] at h ⊢
  intro V hV
  exact IsZero.of_mono ((SheafOfModules.overFunctor.{u} _ V).map f) (h V hV)

/-- A quotient of a module vanishing on `W` vanishes on `W`. -/
theorem vanishesOn_of_epi
    {E E' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (f : E ⟶ E') [Epi f]
    {W : Opens X} (h : VanishesOn E W) : VanishesOn E' W := by
  rw [vanishesOn_iff_forall_isZero_over] at h ⊢
  intro V hV
  exact IsZero.of_epi ((SheafOfModules.overFunctor.{u} _ V).map f) (h V hV)

/-- The cohomology of a complex vanishes on `W` where the corresponding term does. -/
theorem vanishesOn_homology
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℕ) (q : ℕ)
    {W : Opens X} (h : VanishesOn (K.X q) W) : VanishesOn (K.homology q) W :=
  vanishesOn_of_epi (K.homologyπ q) (vanishesOn_of_mono (K.iCycles q) h)

/-- The internal Hom out of a module vanishing on `W` vanishes on `W`. -/
theorem vanishesOn_internalHom
    {A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)} {W : Opens X}
    (h : VanishesOn A W) (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    VanishesOn ((SH O A).obj I) W := by
  intro V hV α
  apply PresheafOfModules.hom_ext
  intro Z
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  have hs : s = 0 := h Z.unop.left ((leOfHom Z.unop.hom).trans hV) s
  rw [hs, map_zero, map_zero]

/-- **`𝓔xt^q(A, G)` vanishes where `A` does.** -/
theorem vanishesOn_homology_cx_of_vanishesOn
    {A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)} {W : Opens X}
    (h : VanishesOn A W)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℕ)
    (q : ℕ) : VanishesOn ((cx O A K).homology q) W :=
  vanishesOn_homology _ q (vanishesOn_internalHom h (K.X q))

/-! ### The long exact sequence of sheaf Ext's -/

section LongExact

variable {S : ShortComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))}
  (hS : S.ShortExact)
  (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℕ)
  [∀ n, Injective (K.X n)] {W : Opens X}
include hS

/-- `𝓔xt^q(A'', G) ⟶ 𝓔xt^q(A, G) ⟶ 𝓔xt^q(A', G)`: vanishing of the outer terms on `W` gives
vanishing of the middle. -/
theorem vanishesOn_homology_X₂_of_shortExact (q : ℕ)
    (h₃ : VanishesOn ((cx O S.X₃ K).homology q) W) (h₁ : VanishesOn ((cx O S.X₁ K).homology q) W) :
    VanishesOn ((cx O S.X₂ K).homology q) W :=
  vanishesOn_X₂ ((cx_shortExact hS K).homology_exact₂ q) h₃ h₁

/-- `𝓔xt^q(A', G) ⟶ 𝓔xt^{q+1}(A'', G) ⟶ 𝓔xt^{q+1}(A, G)`. -/
theorem vanishesOn_homology_X₃_succ_of_shortExact (q : ℕ)
    (h₁ : VanishesOn ((cx O S.X₁ K).homology q) W)
    (h₂ : VanishesOn ((cx O S.X₂ K).homology (q + 1)) W) :
    VanishesOn ((cx O S.X₃ K).homology (q + 1)) W :=
  vanishesOn_X₂ ((cx_shortExact hS K).homology_exact₁ q (q + 1) (by simp)) h₁ h₂

/-- `𝓔xt^q(A, G) ⟶ 𝓔xt^q(A', G) ⟶ 𝓔xt^{q+1}(A'', G)`. -/
theorem vanishesOn_homology_X₁_of_shortExact (q : ℕ)
    (h₂ : VanishesOn ((cx O S.X₂ K).homology q) W)
    (h₃ : VanishesOn ((cx O S.X₃ K).homology (q + 1)) W) :
    VanishesOn ((cx O S.X₁ K).homology q) W :=
  vanishesOn_X₂ ((cx_shortExact hS K).homology_exact₃ q (q + 1) (by simp)) h₂ h₃

end LongExact

/-- **`𝓔xt^{q+1}(𝒪^{⊕ I}, G) = 0`** for a finite free module. -/
theorem isZero_homology_cx_free (I : Type u) [Finite I]
    {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (R : InjectiveResolution G)
    (q : ℕ) : IsZero ((cx O (SheafOfModules.free I) R.cocomplex).homology (q + 1)) :=
  ((cx O (SheafOfModules.free I) R.cocomplex).exactAt_iff_isZero_homology _).1
    (exactAt_cx_free I R q)

/-- A zero module vanishes on every open subset. -/
theorem vanishesOn_of_isZero {E : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (h : IsZero E) (W : Opens X) : VanishesOn E W :=
  vanishesOn_of_isZero_over (Functor.map_isZero (SheafOfModules.overFunctor.{u} _ W) h)

end Stacks.SheafHomInjective

end
