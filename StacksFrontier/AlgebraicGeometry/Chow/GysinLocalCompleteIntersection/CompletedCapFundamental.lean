module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFundamentalClassRegular
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinClass
public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.CompletedClassFundamental

/-!
# Caps of bivariant classes on fundamental classes: transport lemmas

Bivariant classes capping fundamental classes to fundamental classes, as for the Gysin map `f^!` of
Stacks 0FF3 on the connected components of `X`.

All names are in the namespace `Stacks.Chow`.

## Main results

* `BivariantClass.cap_fundamentalChowClass_of_isIso`: a class that caps the fundamental class at
  the test scheme `𝟙 A` to a fundamental class does so at every test scheme isomorphic to `A`
  (Stacks 0B76 (1)).
* `bivariantCompositeOfInvertible_flatPullback_cap_fundamentalChowClass`: the composite `a ∘ g^*`
  of Stacks 0B75 with a flat pullback class of Stacks 0B78 caps `[Y]_m` to a fundamental class as
  soon as `a` caps `[P]_{m+d}` to a fundamental class (Stacks 02RE for `g^*`).
* `bivariantClassComponentCongr_cap_fundamentalChowClass`: the transports between bivariant groups
  of equal connected components preserve this.

## References

* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 02RE](https://stacks.math.columbia.edu/tag/02RE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section Transfer

variable {C : ChowSituation.{u}} {G : GysinSystem C} {Z A : Scheme.{u}} {sZ : Z ⟶ C.S}
  [LocallyOfFiniteType sZ] {sA : A ⟶ C.S} [LocallyOfFiniteType sA] {φ : Z ⟶ A}
  [LocallyOfFiniteType φ] {hφ : φ ≫ sA = sZ} {p : ℤ}

/-- **From the identity test scheme to any isomorphic one.** If `c` caps `[A]_n` at `𝟙 A` to the
fundamental class of `Z ×_A A`, then it caps `[T]_n` at every isomorphism `t : T ⟶ A` to the
fundamental class of `Z ×_A T`. -/
theorem BivariantClass.cap_fundamentalChowClass_of_isIso (c : BivariantClass C G sZ sA φ hφ p)
    (n : ℤ) (h : c.cap (𝟙 A) n (fundamentalChowClass C (𝟙 A ≫ sA) n) =
      fundamentalChowClass C (pullback.fst φ (𝟙 A) ≫ sZ) (n - p))
    {T : Scheme.{u}} (t : T ⟶ A) [IsIso t] [LocallyOfFiniteType t] :
    c.cap t n (fundamentalChowClass C (t ≫ sA) n) =
      fundamentalChowClass C (pullback.fst φ t ≫ sZ) (n - p) := by
  have hh : inv t ≫ t = 𝟙 A := IsIso.inv_hom_id t
  rw [← chowPushforwardOfIso_fundamentalChowClass C (𝟙 A ≫ sA) (t ≫ sA) (inv t)
    (by rw [← Category.assoc, hh]) n, BivariantClass.cap_chowPushforwardOfIso_map C c t (inv t)
    (𝟙 A) hh n, h]
  have : IsIso (pullback.map φ (𝟙 A) φ t (𝟙 Z) (inv t) (𝟙 A) (by simp)
      (by rw [Category.comp_id, hh])) := by
    infer_instance
  exact properChowPushforward_fundamentalChowClass_of_isIso C _ _ _ _ _ _

end Transfer

section Composite

variable (C : ChowSituation.{u}) {X P Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (φ : X ⟶ P) [LocallyOfFiniteType φ] (hφ : φ ≫ sP = sX) (g : P ⟶ Y) [LocallyOfFiniteType g]
  [Flat g] (hg : g ≫ sY = sP) (d : ℕ) (hgd : AlgebraicGeometry.RelativeDimension g d) {p : ℤ}

/-- **`(a ∘ g^*)[Y]_m` is a fundamental class** when `a` caps `[P]_{m+d}` to a fundamental class:
`g^*[Y]_m = [P ×_Y Y]_{m+d}` by Stacks 02RE and `P ×_Y Y ⟶ P` is an isomorphism. -/
theorem bivariantCompositeOfInvertible_flatPullback_cap_fundamentalChowClass
    (a : BivariantClass C (gysinSystemOfInvertible C) sX sP φ hφ p) (m : ℤ)
    (hY : schemeDeltaDimension C sY ≤ (m : EInt))
    (ha : a.cap (𝟙 P) (m - -(d : ℤ)) (fundamentalChowClass C (𝟙 P ≫ sP) (m - -(d : ℤ))) =
      fundamentalChowClass C (pullback.fst φ (𝟙 P) ≫ sX) (m - -(d : ℤ) - p)) :
    (bivariantCompositeOfInvertible C sX sP sY φ g hφ hg p (-(d : ℤ)) a
        (flatPullbackBivariantClassOfInvertible C sP sY g hg d hgd)).cap (𝟙 Y) m
        (fundamentalChowClass C (𝟙 Y ≫ sY) m) =
      fundamentalChowClass C (pullback.fst (φ ≫ g) (𝟙 Y) ≫ sX) (m - (p + -(d : ℤ))) := by
  have hY' : schemeDeltaDimension C (𝟙 Y ≫ sY) ≤ (m : EInt) :=
    (schemeDeltaDimension_congr C (Category.id_comp sY)).trans_le hY
  have hb : (flatPullbackBivariantClassOfInvertible C sP sY g hg d hgd).cap (𝟙 Y) m
      (fundamentalChowClass C (𝟙 Y ≫ sY) m) =
      fundamentalChowClass C (pullback.fst g (𝟙 Y) ≫ sP) (m - -(d : ℤ)) :=
    (flatPullbackBivariantCap_apply C sP sY g hg d hgd (flatPullbackDescends C) (𝟙 Y) m _).trans
      ((congrArg (chowGroupDegreeEquiv C _ _)
        (flatPullbackChow_fundamentalChowClass C _ _ _ _ d _ m _ hY')).trans
        (chowGroupDegreeEquiv_fundamentalChowClass C _ _))
  have ha' := a.cap_fundamentalChowClass_of_isIso (m - -(d : ℤ)) ha (pullback.fst g (𝟙 Y))
  rw [bivariantCompositeOfInvertible, bivariantComposite_cap, bivariantCompositeCap_apply]
  exact (congrArg (chowGroupDegreeEquiv C _ _) ((congrArg (properChowPushforward C _ _ _ _ _ _)
    ((congrArg (DFunLike.coe (a.cap (pullback.fst g (𝟙 Y)) (m - -(d : ℤ)))) hb).trans ha')).trans
    (properChowPushforward_fundamentalChowClass_of_isIso C _ _ _ _ _ _))).trans
    (chowGroupDegreeEquiv_fundamentalChowClass C _ _)

end Composite

section Congr

/-- The transports between the bivariant groups of two equal connected components of the target
preserve "capping the fundamental class to a fundamental class" at the identity test scheme. -/
theorem bivariantClassComponentCongr_cap_fundamentalChowClass (C : ChowSituation.{u})
    {W Z : Scheme.{u}} [LocallyConnectedSpace Z] (sW : W ⟶ C.S) [LocallyOfFiniteType sW]
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] {j₁ j₂ : _root_.ConnectedComponents Z}
    (hj : j₁ = j₂) (u₁ : W ⟶ (Z.connectedComponentOpens j₁ : Scheme.{u})) [LocallyOfFiniteType u₁]
    (u₂ : W ⟶ (Z.connectedComponentOpens j₂ : Scheme.{u})) [LocallyOfFiniteType u₂]
    (hu : u₁ ≍ u₂) (h₁ : u₁ ≫ ((Z.connectedComponentOpens j₁).ι ≫ sZ) = sW)
    (h₂ : u₂ ≫ ((Z.connectedComponentOpens j₂).ι ≫ sZ) = sW) (n : ℤ)
    (c : BivariantClass C (gysinSystemOfInvertible C) sW ((Z.connectedComponentOpens j₁).ι ≫ sZ)
      u₁ h₁ n) (m : ℤ)
    (h : c.cap (𝟙 _) m (fundamentalChowClass C (𝟙 _ ≫ ((Z.connectedComponentOpens j₁).ι ≫ sZ)) m) =
      fundamentalChowClass C (pullback.fst u₁ (𝟙 _) ≫ sW) (m - n)) :
    (bivariantClassComponentCongr C (gysinSystemOfInvertible C) sW sZ hj u₁ u₂ hu h₁ h₂ n c).cap
        (𝟙 _) m (fundamentalChowClass C (𝟙 _ ≫ ((Z.connectedComponentOpens j₂).ι ≫ sZ)) m) =
      fundamentalChowClass C (pullback.fst u₂ (𝟙 _) ≫ sW) (m - n) := by
  subst hj
  obtain rfl := eq_of_heq hu
  exact h

end Congr

end Stacks.Chow

end
