module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniVanishingCut
public import StacksFrontier.AlgebraicGeometry.StalkwiseGeneration.PullbackUniverse

/-!
# Restricting a family of divisors along an immersion

Let `ψ : V → Γ(X, L)` be a linear system on a scheme `X` over a field `k`, the standing situation
`Stacks.Bertini.FamilyDivisors` of [Stacks, Tag 0G47], and let `g : Y ⟶ X` be a morphism. Pulling
the sections back along `g` gives a linear system `V → Γ(Y, g^* L)` with the same vector space and
the same basis, `Stacks.Bertini.FamilyDivisors.pullbackAlong`. Its parameter space is therefore the
parameter space of the original system, and:

* it generates `g^* L` when the original system generates `L` (hypothesis (2) of
  [Stacks, Tag 0FD6]): a section not vanishing at `g y` pulls back to one not vanishing at `y`;
* its morphism to `𝐏(V)` is the composite of `g` with the morphism of the original system, so it
  is an immersion when `g` is and the original system is immersive (hypothesis (3) of
  [Stacks, Tag 0FD6]);
* the divisor of a vector is the inverse image of its divisor on `X` ([Stacks, Tag 0B6Y]).

This is how the Bertini theorems are applied to a locally closed subscheme `M ⊆ X` — an open of a
closed subscheme — of a scheme carrying a generating and immersive linear system: the hypotheses
of [Stacks, Tag 0FD6] pass to `M` along the immersion `M ⟶ X`.

## Main definitions

* `Stacks.Bertini.FamilyDivisors.pullbackAlong`: the restricted standing situation.

## Main results

* `Stacks.Bertini.FamilyDivisors.generates_pullbackAlong`: hypothesis (2) for the restriction.
* `Stacks.Bertini.FamilyDivisors.isImmersive_pullbackAlong`: hypothesis (3) for the restriction
  along an immersion, at every basis.
* `Stacks.Bertini.FamilyDivisors.divisor_pullbackAlong`: the divisor of a vector on `Y` is the
  inverse image of its divisor on `X`.

## References

* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.Ample Stacks.ProjectiveFromSections

universe u

namespace Stacks.Bertini.FamilyDivisors

variable (D : FamilyDivisors.{u, u})

/-- **The linear system of `D` restricted along a morphism `g : Y ⟶ X`**: the scheme is `Y` over
`k` through `g`, the module is `g^* L`, a vector gives the pullback of its section, and the vector
space and its basis are those of `D`. -/
def pullbackAlong {Y : Scheme.{u}} (g : Y ⟶ D.X) : FamilyDivisors.{u, u} where
  k := D.k
  V := D.V
  X := Y
  toBase := g ≫ D.toBase
  L := (Scheme.Modules.pullback g).obj D.L
  isInvertible := Stacks.InvertiblePullback.isInvertibleModule_pullback g _
  ψ := (Stacks.SectionsVanishingOnSubscheme.pullbackSectionsLinear D.k D.toBase g D.L).comp D.ψ
  basis := D.basis

variable {D}

/-- The field of the restricted system is the field of `D`. -/
@[simp]
theorem pullbackAlong_k {Y : Scheme.{u}} (g : Y ⟶ D.X) : (D.pullbackAlong g).k = D.k := rfl

/-- The vector space of the restricted system is the vector space of `D`. -/
@[simp]
theorem pullbackAlong_V {Y : Scheme.{u}} (g : Y ⟶ D.X) : (D.pullbackAlong g).V = D.V := rfl

/-- The section of a vector of the restricted system is the pullback of its section. -/
theorem pullbackAlong_sectionOf {Y : Scheme.{u}} (g : Y ⟶ D.X) (v : D.V) :
    (D.pullbackAlong g).sectionOf v = pullbackGlobalSections g D.L (D.sectionOf v) :=
  rfl

/-- **The restricted system has the parameter space of `D`**: same field, same vector space, same
basis. -/
theorem parameterBase_pullbackAlong {Y : Scheme.{u}} (g : Y ⟶ D.X) :
    (D.pullbackAlong g).parameterBase = D.parameterBase :=
  rfl

/-- **Hypothesis (2) of [Stacks, Tag 0FD6] passes to the restriction along any morphism.** -/
theorem generates_pullbackAlong {Y : Scheme.{u}} (g : Y ⟶ D.X) (h : D.Generates) :
    (D.pullbackAlong g).Generates :=
  generatesStalks_pullbackGlobalSections' g D.L D.sectionOf h

/-- **Hypothesis (2) at a family of vectors passes to the restriction.** -/
theorem generatesBy_pullbackAlong {Y : Scheme.{u}} (g : Y ⟶ D.X) {ι : Type*} {v : ι → D.V}
    (h : D.GeneratesBy v) : (D.pullbackAlong g).GeneratesBy v :=
  generatesStalks_pullbackGlobalSections' g D.L (fun i => D.sectionOf (v i)) h

/-- **The morphism of the restricted system to `𝐏(V)` is `g` followed by the morphism of `D`.** -/
theorem toProjectiveSpace_pullbackAlong {Y : Scheme.{u}} (g : Y ⟶ D.X) {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) D.k D.V) (hb : D.GeneratesBy b) :
    (D.pullbackAlong g).toProjectiveSpace b (generatesBy_pullbackAlong g hb) =
      g ≫ D.toProjectiveSpace b hb := by
  show toProjectiveSpaceOver (fun i => (D.pullbackAlong g).sectionOf (b i))
      (generatesBy_pullbackAlong g hb) (g ≫ D.toBase) ≫ (basisProjectiveSpaceIso b).hom =
    g ≫ (toProjectiveSpaceOver (fun i => D.sectionOf (b i)) hb D.toBase ≫
      (basisProjectiveSpaceIso b).hom)
  rw [← Category.assoc,
    Stacks.SectionsVanishingOnSubscheme.comp_toProjectiveSpaceOver_self g
      (fun i => D.sectionOf (b i)) hb D.toBase (generatesBy_pullbackAlong g hb)]
  rfl

/-- **Hypothesis (3) of [Stacks, Tag 0FD6] passes to the restriction along an immersion**: the
morphism of the restricted system is the composite of the immersion `g` with an immersion. -/
theorem isImmersive_pullbackAlong {Y : Scheme.{u}} (g : Y ⟶ D.X) [AlgebraicGeometry.IsImmersion g]
    {n : ℕ} {b : Module.Basis (Fin (n + 1)) D.k D.V} {hb : D.GeneratesBy b}
    (himm : D.IsImmersive b hb) :
    (D.pullbackAlong g).IsImmersive b (generatesBy_pullbackAlong g hb) := by
  have : AlgebraicGeometry.IsImmersion (D.toProjectiveSpace b hb) := himm
  show AlgebraicGeometry.IsImmersion
    ((D.pullbackAlong g).toProjectiveSpace b (generatesBy_pullbackAlong g hb))
  rw [toProjectiveSpace_pullbackAlong g b hb]
  exact AlgebraicGeometry.IsImmersion.comp g (D.toProjectiveSpace b hb)

/-- **Hypothesis (3) for the restriction at every basis**, from hypothesis (3) for `D` at one
basis; this is the form `Stacks.Bertini.FamilyDivisors.exists_smooth_zeroScheme_sectionOf`
takes. -/
theorem isImmersive_pullbackAlong_basis {Y : Scheme.{u}} (g : Y ⟶ D.X)
    [AlgebraicGeometry.IsImmersion g] {n : ℕ}
    {b : Module.Basis (Fin (n + 1)) D.k D.V} {hb : D.GeneratesBy b} (himm : D.IsImmersive b hb)
    (hgen : D.Generates) (m : ℕ) (b' : Module.Basis (Fin (m + 1)) D.k D.V) :
    (D.pullbackAlong g).IsImmersive b'
      ((D.pullbackAlong g).generatesBy_basis (generates_pullbackAlong g hgen) b') :=
  (D.pullbackAlong g).isImmersive_basis_of_isImmersive (isImmersive_pullbackAlong g himm) b'

/-- **The divisor of a vector of the restricted system is the inverse image of its divisor**
([Stacks, Tag 0B6Y]). -/
theorem divisor_pullbackAlong {Y : Scheme.{u}} (g : Y ⟶ D.X) (v : D.V) :
    (D.pullbackAlong g).divisor v = (D.divisor v).comap g :=
  Stacks.Divisors.zeroScheme_pullback g D.L (D.sectionOf v)

end Stacks.Bertini.FamilyDivisors

end
