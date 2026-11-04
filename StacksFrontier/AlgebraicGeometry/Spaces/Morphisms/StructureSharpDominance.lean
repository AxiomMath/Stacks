module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceCommonTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalFirstOrderThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FpqcDescentAlongDominant

/-!
# Morphisms with injective structure map have full scheme-theoretic image

Let `c : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` whose structure map
`c♯ : 𝒪_Y ⟶ c_*𝒪_X` (Stacks 03G8) is injective on the sections over every étale chart of `Y`,
for instance an isomorphism. Then the scheme-theoretic image of `c` is all of `Y`: a closed
subspace `Z ⊆ Y` through which `c` factors has a defining ideal killed by `c♯`, since `c♯` factors
through the structure map of the inclusion of `Z`; so the ideal vanishes at every chart and `Z`
is everything (Stacks 03MB, injectivity).

Consequently two morphisms out of `Y` into a space separated over a common base which agree
after `c` are equal. This is the uniqueness half of the statement that a contraction
`c : X ⟶ Y` with `𝒪_Y = c_*𝒪_X` determines `Y` (Stacks 0E8A, 0E89).

## Main results

* `AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_eq_top_of_injective_structureSharp`
* `AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_eq_top_of_isIso_structureSharp`
* `AlgebraicGeometry.Space.eq_of_comp_eq_of_isIso_structureSharp`

## References

* [Stacks Project, Tag 082X](https://stacks.math.columbia.edu/tag/082X)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism whose structure map is injective on sections has full scheme-theoretic
image.** If `c♯ : 𝒪_Y ⟶ c_*𝒪_X` is injective on the sections over every étale chart of `Y`, the
scheme-theoretic image of `c` is all of `Y`. -/
theorem schemeTheoreticImageSubfunctor_eq_top_of_injective_structureSharp
    {X Y : AlgebraicSpaces B S hS} (c : X ⟶ Y)
    (hc : ∀ U, Function.Injective ((structureSharp B S hS c).hom.app U).hom) :
    schemeTheoreticImageSubfunctor B S hS c.hom = ⊤ := by
  set Z := schemeTheoreticImageSubfunctor B S hS c.hom
  have hZ : IsClosedSubspace B S hS Z :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS c.hom Y.2
  let Zc : ClosedSubspaces B S hS Y.1 := ⟨Z, hZ⟩
  let Tc : ClosedSubspaces B S hS Y.1 := ⟨⊤, isClosedSubspace_top B S hS Y⟩
  let W : AlgebraicSpaces B S hS := ⟨Z.toFunctor, hZ.1⟩
  let i : W ⟶ Y := ObjectProperty.homMk Z.ι
  let c' : X ⟶ W := ObjectProperty.homMk (toSchemeTheoreticImage B S hS c.hom)
  have hci : c' ≫ i = c := by
    ext1
    exact toSchemeTheoreticImage_ι B S hS c.hom
  refine top_le_iff.1 (le_of_forall_definingIdealAt_le B S hS Y Tc Zc fun U _ a ha => ?_)
  rw [mem_definingIdealAt_iff] at ha ⊢
  have h0 : ((structureSharp B S hS c).hom.app (op U)).hom a = 0 := by
    have happ := congrArg (fun m => (m.hom.app (op U)).hom a) (structureSharp_comp B S hS c' i)
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, RingCat.hom_comp,
      RingHom.comp_apply] at happ
    rw [← hci]
    refine happ.symm.trans ?_
    rw [ha, map_zero]
    rfl
  rw [hc (op U) (h0.trans (map_zero _).symm), map_zero]

/-- **A morphism whose structure map is an isomorphism has full scheme-theoretic image.** -/
theorem schemeTheoreticImageSubfunctor_eq_top_of_isIso_structureSharp
    {X Y : AlgebraicSpaces B S hS} (c : X ⟶ Y) [IsIso (structureSharp B S hS c)] :
    schemeTheoreticImageSubfunctor B S hS c.hom = ⊤ := by
  refine schemeTheoreticImageSubfunctor_eq_top_of_injective_structureSharp B S hS c fun U => ?_
  have : IsIso ((structureSharp B S hS c).hom.app U) := by
    have : IsIso (structureSharp B S hS c).hom :=
      (ObjectProperty.isIso_hom_iff _).2 inferInstance
    infer_instance
  exact (ConcreteCategory.bijective_of_isIso ((structureSharp B S hS c).hom.app U)).1

/-- **Morphisms out of the target of a contraction are determined after the contraction.** Let
`c : X ⟶ Y` be a morphism of algebraic spaces with `𝒪_Y = c_*𝒪_X`, i.e. with structure map an
isomorphism, and let `a b : Y ⟶ Z` be morphisms over `q : Z ⟶ T` with `q` separated. If
`c ≫ a = c ≫ b` then `a = b`. -/
theorem eq_of_comp_eq_of_isIso_structureSharp {X Y Z T : AlgebraicSpaces B S hS}
    (c : X ⟶ Y) [IsIso (structureSharp B S hS c)] (q : Z ⟶ T) (hq : IsSeparated B S hS q.hom)
    {a b : Y ⟶ Z} (hab : a ≫ q = b ≫ q) (h : c ≫ a = c ≫ b) : a = b := by
  ext1
  exact eq_of_comp_eq_of_schemeTheoreticImageSubfunctor_eq_top T.2 Y.2 Z.2 q.hom hq
    (congrArg (fun m => m.hom) hab) c.hom
    (schemeTheoreticImageSubfunctor_eq_top_of_isIso_structureSharp B S hS c)
    (congrArg (fun m => m.hom) h)

end AlgebraicGeometry.Space

end
