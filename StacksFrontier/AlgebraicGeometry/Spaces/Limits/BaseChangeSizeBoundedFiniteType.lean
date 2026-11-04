module

public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.DenseAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange

/-!
# Systems of algebraic spaces of finite type over `Spec ℤ` have bounded base changes

Let `D` be an inverse system of algebraic spaces over `S` with affine transition morphisms, every
stage of which is of finite type over `Spec ℤ`. Then the base changes of the stages along a test
scheme are uniformly bounded (`AlgebraicGeometry.Space.BaseChangeSizeBounded`): for a stage `i₀`
and a morphism `g : Z ⟶ D i₀` from an object of the site, every scheme `W` representing a base
change `D k ×_{D i₀} Z` with `k ⟶ i₀` has size at most the size of `Z`.

Indeed, the transition morphism `D k ⟶ D i₀` is locally of finite type, both stages being
locally of finite type over `S` (as they are over `Spec ℤ`), and it is affine; so its base change
`W ⟶ Z` is a morphism of schemes locally of finite type and affine, hence quasi-compact, and such
a morphism does not increase the size (Stacks 04T7,
`AlgebraicGeometry.Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact`).

This applies to the inverse systems of Noetherian approximation (Stacks 07SU), whose stages are
quasi-separated and of finite type over `Spec ℤ`; together with a bound on the index set it is
what the forms of Stacks 07SF, 07SK and 0851 for an index set smaller than the cutoff ask for.

## Main results

* `AlgebraicGeometry.Space.baseChangeSizeBounded_of_isFiniteType_viewOverIntegers`

## References

* [Stacks Project, Tag 04T7](https://stacks.math.columbia.edu/tag/04T7)
* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **An inverse system of algebraic spaces of finite type over `Spec ℤ` with affine transition
morphisms has uniformly bounded base changes.** A base change of a stage along a test scheme `Z`
is affine and locally of finite type over `Z`, so its size is at most that of `Z`. -/
theorem baseChangeSizeBounded_of_isFiniteType_viewOverIntegers {I : Type u} [Category.{u} I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hft : ∀ i, IsFiniteType B (⊤_ Scheme.{u}) hZ
      (terminal.from (viewOverIntegers B S hS hZ (D.obj i)))) :
    BaseChangeSizeBounded B S hS D := by
  intro i₀ Z g
  refine ⟨((BigFppfOver.toScheme B S hS).obj Z).size, Z.left.property, fun k W p q hpq ↦ ?_⟩
  -- the terminal object of the site over `S`
  let T : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))
  have hT : IsTerminal (yoneda.obj T) :=
    (Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _
  -- the transition morphism is locally of finite type
  have hk : IsLocallyOfFiniteType B S hS (D.map k.hom) := by
    refine isLocallyOfFiniteType_of_comp B S hS (hD k.left) (hD i₀)
      (isAlgebraicSpace_yoneda B S hS T) (D.map k.hom) (hT.from _) ?_
    rw [hT.hom_ext (D.map k.hom ≫ hT.from _) (hT.from _)]
    exact isLocallyOfFiniteType_of_isFiniteType_viewOverIntegers hZ (hD k.left) (hft k.left) _
  -- so is its base change `W ⟶ Z`, which is moreover affine
  let q₀ : W ⟶ Z := yoneda.preimage q
  have hpq' : IsPullback p (yoneda.map q₀) (D.map k.hom) g := by
    rwa [show yoneda.map q₀ = q from Functor.map_preimage yoneda q]
  have hqft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map q₀) :=
    (isLocallyOfFiniteType_yoneda_map_iff B S hS q₀).mp
      (IsLocallyOfFiniteType.of_isPullback B S hS hpq'.flip (hD k.left) (hD i₀) hk)
  have hqaff : AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map q₀) :=
    (presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS (hD k.left) (hD i₀)
      (hAffine k.hom)).2.property g p q₀ hpq'
  exact Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact ((BigFppfOver.toScheme B S hS).map q₀)

end AlgebraicGeometry.Space

end
