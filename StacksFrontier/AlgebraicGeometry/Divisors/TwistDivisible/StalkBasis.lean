module

public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.DualStalk

/-!
# From a local frame to a basis of a stalk

A section `σ` of an `𝒪_X`-module `F` over an open `V` is a *local frame* when, over every open
`W ≤ V`, every section of `F` over `W` is uniquely a multiple of `σ|_W`. This file proves that
the germ of a local frame at a point `y ∈ V` is then a basis of the stalk `F_y` over the local
ring `𝒪_{X,y}`: the map `r ↦ r · germ_y σ` is bijective.

This is the step that converts the sectionwise trivialization an invertible module carries on a
neighbourhood of every point — a rank-one dual basis in the sense of
`Stacks.SheafOfModules.DualBasisOne` — into the statement about one stalk that a local
computation at a point needs. The argument is the usual germ chase: a germ is represented over
some open, shrink that open inside `V`, apply the hypothesis there, and transport the answer
back along `germ_res`.

## Main results

* `Stacks.Divisors.TwistDivisible.bijective_smul_germAt`: **the germ of a local frame is a
  basis of the stalk.**
* `Stacks.Divisors.TwistDivisible.exists_res_eq`: two sections with the same germ at `y` agree
  on a neighbourhood of `y`; this is Mathlib's `TopCat.Presheaf.germ_eq` read for a sheaf of
  modules.

## Implementation notes

**Why the restriction maps are renamed.** `Stacks.SheafOfModules.SheafHomStalk.resLE` and
`germAt` take their section in `(commVal F).obj (op W)`, whereas the `Module Γ(X, W) Γ(F, W)`
instance Mathlib registers — the one that makes `c • t` elaborate — is keyed on `Γ(F, W)`. The
two types are equal, but instance search is syntactic, so a statement about `c • resLE F h t`
fails to synthesize an `HSMul`. `res` and `resO` are the same maps with their codomains
declared at the `Γ(-, -)` spelling, and the four small lemmas below are `resLE`'s lemmas read
through them.

**No rewriting under a germ.** `germAt F W y hy` is not a bundled morphism, so `rw` inside its
argument builds a motive over the module of sections and fails at `implicit` transparency; the
surjectivity half is therefore assembled with `congrArg` and `Eq.trans`, which form no motive.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules.SheafHomStalk
open Stacks.AlgebraicGeometry.ReflexiveModules (ringGermAt stalkHom stalkHom_germAt)

universe u

namespace Stacks.Divisors.TwistDivisible

variable {X : Scheme.{u}}

/-- **Restriction of a section of an `𝒪_X`-module**, with the codomain declared at the
`Γ(-, -)` spelling so that the action of `Γ(X, W')` on it resolves by instance search. -/
noncomputable abbrev res (F : X.Modules) {W' W : X.Opens} (h : W' ≤ W) (t : Γ(F, W)) : Γ(F, W') :=
  F.presheaf.map (homOfLE h).op t

/-- **Restriction of a section of the structure sheaf**, at the `Γ(-, -)` spelling. -/
noncomputable abbrev resO {W' W : X.Opens} (h : W' ≤ W) (c : Γ(X, W)) : Γ(X, W') :=
  X.presheaf.map (homOfLE h).op c

/-- The germ of a restricted section is the germ of the section. -/
theorem germAt_res (F : X.Modules) {W' W : X.Opens} (h : W' ≤ W) {y : X} (hy : y ∈ W')
    (t : Γ(F, W)) : germAt F W' y hy (res F h t) = germAt F W y (h hy) t :=
  germAt_resLE F h hy t

/-- The germ of a scalar multiple is the product of the germs. -/
theorem germAt_smul' (F : X.Modules) {W : X.Opens} {y : X} (hy : y ∈ W) (c : Γ(X, W))
    (t : Γ(F, W)) :
    germAt F W y hy (c • t) = ringGermAt X W y hy c • germAt F W y hy t :=
  germAt_smul F hy c t

/-- Restriction is linear over restriction of scalars. -/
theorem res_smul (F : X.Modules) {W' W : X.Opens} (h : W' ≤ W) (c : Γ(X, W)) (t : Γ(F, W)) :
    res F h (c • t) = resO h c • res F h t :=
  resLE_smul F h c t

/-- Restricting twice is restricting once. -/
theorem res_res (F : X.Modules) {W'' W' W : X.Opens} (h : W' ≤ W) (h' : W'' ≤ W')
    (t : Γ(F, W)) : res F h' (res F h t) = res F (h'.trans h) t :=
  resLE_resLE F h h' t

/-- The germ of a restricted function is the germ of the function. -/
theorem ringGermAt_res {y : X} {W W' : X.Opens} (hle : W' ≤ W) (hy : y ∈ W') (c : Γ(X, W)) :
    ringGermAt X W' y hy (resO hle c) = ringGermAt X W y (hle hy) c :=
  TopCat.Presheaf.germ_res_apply X.sheaf.obj (homOfLE hle) y hy c

/-- **Two sections with the same germ agree on a smaller open.** This is
`TopCat.Presheaf.germ_eq` for the underlying sheaf of abelian groups, with the two inclusions it
produces identified — a poset has at most one morphism between two objects. -/
theorem exists_res_eq {F : X.Modules} {y : X} {W : X.Opens} (hyW : y ∈ W)
    (t t' : Γ(F, W)) (h : germAt F W y hyW t = germAt F W y hyW t') :
    ∃ (W' : X.Opens) (_ : y ∈ W') (hle : W' ≤ W), res F hle t = res F hle t' := by
  obtain ⟨W', hyW', i, j, hij⟩ :=
    TopCat.Presheaf.germ_eq (C := Ab.{u}) (commVal F).presheaf y hyW hyW t t' h
  exact ⟨W', hyW', leOfHom i,
    (PresheafOfModules.congr_map_apply (commVal F) (Subsingleton.elim _ _) t).trans
      (hij.trans (PresheafOfModules.congr_map_apply (commVal F) (Subsingleton.elim _ _) t'))⟩

/-- **The germ of a local frame is a basis of the stalk.** If every section of `F` over every
open `W ≤ V` is uniquely a multiple of `σ|_W`, then multiplication by the germ of `σ` at a point
`y ∈ V` is a bijection from the local ring `𝒪_{X,y}` onto the stalk `F_y`.

Injectivity: two germs of functions agreeing against `germ_y σ` are represented by functions on
a common open, and the two multiples have the same germ, hence agree after shrinking; the
hypothesis there cancels `σ`. Surjectivity: a germ of `F` is represented over some open, which
is shrunk inside `V`, and the hypothesis writes the representative as a multiple of `σ`. -/
theorem bijective_smul_germAt {F : X.Modules} {V : X.Opens} {y : X} (hyV : y ∈ V)
    (σ : Γ(F, V))
    (h : ∀ (W : X.Opens) (hW : W ≤ V),
      Function.Bijective (fun c : Γ(X, W) => c • res F hW σ)) :
    Function.Bijective (fun r : ringStalk X.sheaf y => r • germAt F V y hyV σ) := by
  constructor
  · intro r r' hrr'
    obtain ⟨W₁, hyW₁, c₁, hc₁⟩ := TopCat.Presheaf.exists_germ_eq X.sheaf.obj r
    obtain ⟨W₂, hyW₂, c₂, hc₂⟩ := TopCat.Presheaf.exists_germ_eq X.sheaf.obj r'
    have hyW : y ∈ (W₁ ⊓ W₂) ⊓ V := ⟨⟨hyW₁, hyW₂⟩, hyV⟩
    have hWV : (W₁ ⊓ W₂) ⊓ V ≤ V := inf_le_right
    have hW1 : (W₁ ⊓ W₂) ⊓ V ≤ W₁ := le_trans inf_le_left inf_le_left
    have hW2 : (W₁ ⊓ W₂) ⊓ V ≤ W₂ := le_trans inf_le_left inf_le_right
    have hr₁ : ringGermAt X _ y hyW (resO hW1 c₁) = r := (ringGermAt_res hW1 hyW c₁).trans hc₁
    have hr₂ : ringGermAt X _ y hyW (resO hW2 c₂) = r' := (ringGermAt_res hW2 hyW c₂).trans hc₂
    have key : germAt F _ y hyW (resO hW1 c₁ • res F hWV σ)
        = germAt F _ y hyW (resO hW2 c₂ • res F hWV σ) := by
      rw [germAt_smul', germAt_smul', germAt_res, hr₁, hr₂]
      exact hrr'
    obtain ⟨W', hyW', hle, hz⟩ := exists_res_eq hyW _ _ key
    rw [res_smul, res_smul, res_res] at hz
    have hcc := (h W' (le_trans hle hWV)).1 hz
    rw [← hr₁, ← hr₂, ← ringGermAt_res hle hyW' (resO hW1 c₁),
      ← ringGermAt_res hle hyW' (resO hW2 c₂), hcc]
  · intro m
    obtain ⟨W₀, hyW₀, t, ht⟩ := exists_germ_eq F m
    have hyW : y ∈ W₀ ⊓ V := ⟨hyW₀, hyV⟩
    have hWV : W₀ ⊓ V ≤ V := inf_le_right
    obtain ⟨c, hcc⟩ := (h (W₀ ⊓ V) hWV).2 (res F (inf_le_left : W₀ ⊓ V ≤ W₀) t)
    refine ⟨ringGermAt X _ y hyW c, ?_⟩
    have h1 : germAt F _ y hyW (c • res F hWV σ)
        = ringGermAt X _ y hyW c • germAt F V y hyV σ := by
      rw [germAt_smul', germAt_res]
    exact h1.symm.trans ((congrArg (fun z => germAt F (W₀ ⊓ V) y hyW z) hcc).trans
      ((germAt_res F (inf_le_left : W₀ ⊓ V ≤ W₀) hyW t).trans ht))

end Stacks.Divisors.TwistDivisible

end
