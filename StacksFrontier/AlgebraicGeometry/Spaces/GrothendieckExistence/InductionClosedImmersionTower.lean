module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.InductionClosedSubspaceTower
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic

/-!
# Stacks 08BG for a tower of closed immersions, given Grothendieck's existence theorem

The source's statement of Stacks 08BG is about an abstract commutative diagram
`Z_1 ⟶ Z_2 ⟶ ⋯` over `X_1 ⟶ X_2 ⟶ ⋯`, `X_n = X ×_V Spec (A / Iⁿ)`, with cartesian squares, in
which only `Z_1 ⟶ X_1` is assumed to be a closed immersion; its proof first makes every
`Z_n ⟶ X_n` a closed immersion by Stacks 08B2.  This file carries out the rest of the proof:
for a tower of closed immersions `j_n : Z_n ⟶ X_n` with cartesian squares and `Z_1` proper over
`V`, the images of the `j_n` in `X` form a compatible tower of closed subspaces, and the
closed-subspace form of Stacks 08BG
(`AlgebraicGeometry.Space.closedSubspaceTowerAlgebraizes_of_existence`)
produces the closed subspace `Z ⊆ X`.

Nothing is registered: the result is conditional on Stacks 08BE and 08B9 (as the propositions of
`StacksFrontier/AlgebraicGeometry/Spaces/GrothendieckExistence/Statements.lean`) and takes the
closed immersions `j_n`, which the source obtains from Stacks 08B2, as a hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
  (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) {X : AlgebraicSpaces B S hS}
  (f : X ⟶ schemeSpace V)

/-- The image in `X` of a closed immersion into a thickening `X_n`. -/
def thickeningImage (n : ℕ) {Z : AlgebraicSpaces B S hS} (j : Z ⟶ fibreSpace V I f n)
    (hj : IsClosedImmersion B S hS j.hom) : ClosedSubspaces B S hS X.1 :=
  ⟨Subfunctor.range (j.hom ≫ (fibreInclusion V I f n).hom),
    isClosedSubspace_range_of_isClosedImmersion B S hS _ Z.2
      (isClosedImmersion_comp B S hS _ _ hj (fibreThickening V I f n).2.2)⟩

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)] in
/-- The image in `X` of a closed immersion into the thickening `X_n` lies in `X_n`. -/
theorem thickeningImage_le (n : ℕ) {Z : AlgebraicSpaces B S hS} (j : Z ⟶ fibreSpace V I f n)
    (hj : IsClosedImmersion B S hS j.hom) :
    (thickeningImage V I f n j hj).1 ≤ (thickeningSubspace V I f n).1 := by
  rintro T x ⟨z, rfl⟩
  exact (j.hom.app T z).2

/-- **Stacks 08BG for a tower of closed immersions, from Stacks 08BE and 08B9.**  Let
`j_n : Z_n ⟶ X_n` be closed immersions into the thickenings `X_n = X ×_V Spec (A / Iⁿ)`, with
maps `Z_n ⟶ Z_{n+1}` making the squares over `X_n ⟶ X_{n+1}` cartesian, and with `Z_1` proper
over `V`.  Then there is a closed subspace `Z ⊆ X`, proper over `V`, whose intersection with
every `X_n` is the image of `Z_n`. -/
theorem exists_closedSubspace_of_closedImmersion_tower (h08B9 : CompletionBijectiveOnHoms V I f)
    (h08BE : CompletionProperOverIsEquivalence V I f)
    (hcomp : IsAdicComplete I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    (hsep : IsSeparated B S hS f.hom) (hft : IsFiniteType B S hS f.hom)
    (Z : ℕ → AlgebraicSpaces B S hS) (j : ∀ n, Z n ⟶ fibreSpace V I f n)
    (k : ∀ n, Z n ⟶ Z (n + 1))
    (hsq : ∀ n, 1 ≤ n → IsPullback (k n).hom (j n).hom (j (n + 1)).hom
      (fibreTransition V I f (Nat.le_succ n)).hom)
    (hj : ∀ n, 1 ≤ n → IsClosedImmersion B S hS (j n).hom)
    (hp : IsProper B S hS ((j 1).hom ≫ (fibreInclusion V I f 1).hom ≫ f.hom)) :
    ∃ W : ClosedSubspaces B S hS X.1, IsProper B S hS (subspaceInclusion B S hS X W ≫ f).hom ∧
      ∀ n (hn : 1 ≤ n),
        W.1 ⊓ (thickeningSubspace V I f n).1 = (thickeningImage V I f n (j n) (hj n hn)).1 := by
  classical
  let Wt : ℕ → ClosedSubspaces B S hS X.1 := fun n =>
    if h : 1 ≤ n then thickeningImage V I f n (j n) (hj n h) else thickeningSubspace V I f n
  have hWt : ∀ n (hn : 1 ≤ n), Wt n = thickeningImage V I f n (j n) (hj n hn) :=
    fun n hn => dite_eq_left hn
  have hZle : ∀ n, 1 ≤ n → (Wt n).1 ≤ (thickeningSubspace V I f n).1 := fun n hn =>
    hWt n hn ▸ thickeningImage_le V I f n (j n) (hj n hn)
  have hZeq : ∀ n, 1 ≤ n → (Wt n).1 = (Wt (n + 1)).1 ⊓ (thickeningSubspace V I f n).1 := by
    intro n hn
    rw [hWt n hn, hWt (n + 1) (by omega)]
    have hw : (k n).hom ≫ (j (n + 1)).hom ≫ (fibreInclusion V I f (n + 1)).hom =
        (j n).hom ≫ (fibreInclusion V I f n).hom := by
      rw [← Category.assoc, (hsq n hn).w, Category.assoc]
      exact congrArg ((j n).hom ≫ ·)
        (congrArg (fun φ => φ.hom) (fibreTransition_comp V I f (Nat.le_succ n)))
    refine le_antisymm (le_inf ?_ (thickeningImage_le V I f n (j n) (hj n hn))) ?_
    · rintro T x ⟨z, rfl⟩
      exact ⟨(k n).hom.app T z, congrFun (congrArg (fun φ => φ.app T) hw) z⟩
    · rintro T x ⟨⟨z, hz⟩, hx⟩
      obtain ⟨w, -, hw2⟩ := Types.exists_of_isPullback
        ((hsq n hn).map ((evaluation _ (Type u)).obj T)) z ⟨x, hx⟩ (Subtype.ext hz)
      exact ⟨w, congrArg Subtype.val hw2⟩
  have hZ1 : IsProper B S hS (subspaceInclusion B S hS X (Wt 1) ≫ f).hom := by
    rw [hWt 1 le_rfl]
    have hmono : Mono ((j 1).hom ≫ (fibreInclusion V I f 1).hom) :=
      mono_of_isClosedImmersion B S hS _
        (isClosedImmersion_comp B S hS _ _ (hj 1 le_rfl) (fibreThickening V I f 1).2.2)
    have hι : (Subfunctor.range ((j 1).hom ≫ (fibreInclusion V I f 1).hom)).ι =
        inv (Subfunctor.toRange ((j 1).hom ≫ (fibreInclusion V I f 1).hom)) ≫
          ((j 1).hom ≫ (fibreInclusion V I f 1).hom) := by
      rw [IsIso.eq_inv_comp, Subfunctor.toRange_ι]
    change IsProper B S hS ((Subfunctor.range ((j 1).hom ≫ (fibreInclusion V I f 1).hom)).ι ≫ f.hom)
    rw [hι, Category.assoc, Category.assoc]
    exact isProper_comp' B S hS _ _ (Z 1).2 (schemeSpace V).2 (isProper_of_isIso B S hS _) hp
  obtain ⟨W, hWp, hW⟩ := closedSubspaceTowerAlgebraizes_of_existence V I f h08B9 h08BE hcomp hsep
    hft Wt hZle hZeq hZ1
  exact ⟨W, hWp, fun n hn => (hW n hn).trans (by rw [hWt n hn])⟩

end AlgebraicGeometry.Space

end
