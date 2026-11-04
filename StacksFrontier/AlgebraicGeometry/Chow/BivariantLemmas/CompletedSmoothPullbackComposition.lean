module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackComposition
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedSmoothPullback
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward

/-!
# Composition of flat pullbacks along smooth morphisms, on completions

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `p : P' ⟶ P` and
`g : P ⟶ Y` be smooth morphisms of schemes locally of finite type over `S`. Their flat pullbacks
are completed bivariant classes `p^* ∈ A^*(P' ⟶ P)^∧` and `g^* ∈ A^*(P ⟶ Y)^∧`
(`Stacks.Chow.completedFlatPullbackOfSmooth`), and Stacks 02RD reads

  `(g ∘ p)^* = p^* ∘ g^*` in `A^*(P' ⟶ Y)^∧`.

## Main results

* `AlgebraicGeometry.RelativeDimension.eq_of_nonempty` — a morphism with nonempty source has at
  most one relative dimension.
* `Stacks.Chow.completedFlatPullbackOfSmooth_comp` — `(g ∘ p)^* = p^* ∘ g^*` on completions.

## References

* [Stacks Project, Tag 02RD](https://stacks.math.columbia.edu/tag/02RD)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0FF2](https://stacks.math.columbia.edu/tag/0FF2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- A morphism with nonempty source has at most one relative dimension: the fibre through a point
of the source is nonempty, and its dimension is both values. -/
theorem AlgebraicGeometry.RelativeDimension.eq_of_nonempty {X S : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] [Nonempty X] {d d' : ℕ} (hd : RelativeDimension f d)
    (hd' : RelativeDimension f d') : d = d' := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have hne : Nonempty (f.fiber (f x)) := ⟨f.asFiber x⟩
  have h := (hd (f x) hne).2.symm.trans (hd' (f x) hne).2
  exact_mod_cast h

namespace Stacks.Chow

/-- A connected component of a locally Noetherian scheme is nonempty. -/
instance nonempty_connectedComponentOpens {P : Scheme.{u}} [IsLocallyNoetherian P]
    (a : _root_.ConnectedComponents P) : Nonempty (P.connectedComponentOpens a) := by
  obtain ⟨x, rfl⟩ := _root_.ConnectedComponents.surjective_coe a
  exact ⟨⟨x, rfl⟩⟩

/-- Flat-pullback classes of Stacks 0B78 for morphisms into equal connected components, equal up
to that identification and of equal relative dimensions, are the same class. -/
theorem flatPullbackBivariantClass_heq_of_component (C : ChowSituation.{u}) {V Y : Scheme.{u}}
    (sV : V ⟶ C.S) [LocallyOfFiniteType sV] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    [IsLocallyNoetherian Y] {j₁ j₂ : _root_.ConnectedComponents Y} (hj : j₁ = j₂)
    (φ₁ : V ⟶ (Y.connectedComponentOpens j₁ : Scheme.{u})) [LocallyOfFiniteType φ₁] [Flat φ₁]
    (φ₂ : V ⟶ (Y.connectedComponentOpens j₂ : Scheme.{u})) [LocallyOfFiniteType φ₂] [Flat φ₂]
    (hφ : φ₁ ≍ φ₂) (hφ₁ : φ₁ ≫ ((Y.connectedComponentOpens j₁).ι ≫ sY) = sV)
    (hφ₂ : φ₂ ≫ ((Y.connectedComponentOpens j₂).ι ≫ sY) = sV) {r₁ r₂ : ℕ} (hr : r₁ = r₂)
    (h₁ : AlgebraicGeometry.RelativeDimension φ₁ r₁)
    (h₂ : AlgebraicGeometry.RelativeDimension φ₂ r₂) :
    flatPullbackBivariantClassOfInvertible C sV _ φ₁ hφ₁ r₁ h₁ ≍
      flatPullbackBivariantClassOfInvertible C sV _ φ₂ hφ₂ r₂ h₂ := by
  subst hj hr
  obtain rfl := eq_of_heq hφ
  rfl

variable (C : ChowSituation.{u}) {P' P Y : Scheme.{u}} (sP' : P' ⟶ C.S) [LocallyOfFiniteType sP']
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (p : P' ⟶ P) [Smooth p] [LocallyOfFiniteType p] (g : P ⟶ Y) [Smooth g]
  [LocallyOfFiniteType g] (hp : p ≫ sP = sP') (hg : g ≫ sY = sP)
  [IsLocallyNoetherian P'] [IsLocallyNoetherian P] [IsLocallyNoetherian Y]

/-- Relative dimension transports along a heterogeneous equality of morphisms into equal
connected components. -/
theorem relativeDimension_of_heq_component {V Y : Scheme.{u}} [IsLocallyNoetherian Y]
    {j₁ j₂ : _root_.ConnectedComponents Y} (hj : j₁ = j₂)
    (φ₁ : V ⟶ (Y.connectedComponentOpens j₁ : Scheme.{u})) [LocallyOfFiniteType φ₁]
    (φ₂ : V ⟶ (Y.connectedComponentOpens j₂ : Scheme.{u})) [LocallyOfFiniteType φ₂]
    (hφ : φ₁ ≍ φ₂) {d : ℕ} (h : AlgebraicGeometry.RelativeDimension φ₂ d) :
    AlgebraicGeometry.RelativeDimension φ₁ d := by
  subst hj
  obtain rfl := eq_of_heq hφ
  exact h

omit [LocallyOfFiniteType p] [LocallyOfFiniteType g] in
/-- The relative dimension of `p ≫ g` on a connected component of `P'` is the sum of those of `p`
there and of `g` on the component of `P` it lands in. -/
theorem smoothComponentRelativeDimension_comp (w : _root_.ConnectedComponents P') :
    smoothComponentRelativeDimension (p ≫ g) w =
      smoothComponentRelativeDimension p w +
        smoothComponentRelativeDimension g (p.continuous.connectedComponentsMap w) := by
  have hcomp := AlgebraicGeometry.RelativeDimension.comp_of_flat _ _
    (relativeDimension_smoothComponentRelativeDimension p w)
    (relativeDimension_smoothComponentRelativeDimension g (p.continuous.connectedComponentsMap w))
  have hres := relativeDimension_of_heq_component (Scheme.Hom.connectedComponentsMap_comp p g w)
    _ _ (Scheme.Hom.heq_resConnectedComponent_comp p g w) hcomp
  exact (relativeDimension_smoothComponentRelativeDimension (p ≫ g) w).eq_of_nonempty hres

/-- **Stacks 02RD on a connected component.** On a connected component `P'_w` of `P'`, the
composite of the flat-pullback classes of the restrictions of `p` and `g` is the flat-pullback
class of the restriction of `p ≫ g`, up to the identification of the two restrictions. -/
theorem flatPullbackBivariantClass_resConnectedComponent_comp (w : _root_.ConnectedComponents P') :
    bivariantCompositeOfInvertible C _ _ _ (p.resConnectedComponent w)
        (g.resConnectedComponent (p.continuous.connectedComponentsMap w))
        (p.resConnectedComponent_comp_ι_comp hp w)
        (g.resConnectedComponent_comp_ι_comp hg (p.continuous.connectedComponentsMap w))
        (-(smoothComponentRelativeDimension p w : ℤ))
        (-(smoothComponentRelativeDimension g (p.continuous.connectedComponentsMap w) : ℤ))
        (flatPullbackBivariantClassOfInvertible C _ _ (p.resConnectedComponent w)
            (p.resConnectedComponent_comp_ι_comp hp w) (smoothComponentRelativeDimension p w)
            (relativeDimension_smoothComponentRelativeDimension p w))
        (flatPullbackBivariantClassOfInvertible C _ _
            (g.resConnectedComponent (p.continuous.connectedComponentsMap w))
            (g.resConnectedComponent_comp_ι_comp hg (p.continuous.connectedComponentsMap w))
            (smoothComponentRelativeDimension g (p.continuous.connectedComponentsMap w))
            (relativeDimension_smoothComponentRelativeDimension g _)) ≍
      flatPullbackBivariantClassOfInvertible C _ _ ((p ≫ g).resConnectedComponent w)
          ((p ≫ g).resConnectedComponent_comp_ι_comp (comp_comp_structureMorphism_eq hp hg) w)
          (smoothComponentRelativeDimension (p ≫ g) w)
          (relativeDimension_smoothComponentRelativeDimension (p ≫ g) w) :=
  (bivariantCompositeOfInvertible_flatPullbackBivariantClass C _ _ _ _ _ _ _ _ _ _ _).trans
    (flatPullbackBivariantClass_heq_of_component C _ sY
      (Scheme.Hom.connectedComponentsMap_comp p g w).symm _ _
      (Scheme.Hom.heq_resConnectedComponent_comp p g w).symm _ _
      (smoothComponentRelativeDimension_comp p g w).symm _ _)

/-- **Stacks 02RD on completions, for smooth morphisms.** For smooth morphisms `p : P' ⟶ P` and
`g : P ⟶ Y`, the composite `p^* ∘ g^*` of their flat pullbacks in the completed bivariant groups
of Stacks 0FE0 is the flat pullback `(g ∘ p)^*` of the composite. -/
theorem completedFlatPullbackOfSmooth_comp :
    completedBivariantCompositeOfInvertible C sP' sP sY p g hp hg
        (completedFlatPullbackOfSmooth C sP' sP p hp)
        (completedFlatPullbackOfSmooth C sP sY g hg) =
      completedFlatPullbackOfSmooth C sP' sY (p ≫ g) (comp_comp_structureMorphism_eq hp hg) := by
  funext w
  rw [completedBivariantCompositeOfInvertible_of_of C sP' sP sY p g hp hg _ _ w
      (-(smoothComponentRelativeDimension p w : ℤ))
      (-(smoothComponentRelativeDimension g (p.continuous.connectedComponentsMap w) : ℤ))
      (by rw [completedFlatPullbackOfSmooth_apply, DirectSum.of_eq_same])
      (by rw [completedFlatPullbackOfSmooth_apply, DirectSum.of_eq_same]),
    completedFlatPullbackOfSmooth_apply]
  refine directSum_of_eq_of_heq (by rw [smoothComponentRelativeDimension_comp]; push_cast; ring)
    _ _ ((bivariantClassComponentCongr_heq C _ _ _ _ _ _ _ _ _ _).trans ?_)
  rw [DirectSum.of_eq_same, completedFlatPullbackOfSmooth_apply, DirectSum.of_eq_same]
  exact flatPullbackBivariantClass_resConnectedComponent_comp C sP' sP sY p g hp hg w

end Stacks.Chow

end
