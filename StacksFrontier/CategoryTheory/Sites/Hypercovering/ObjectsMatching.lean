module

public import StacksFrontier.AlgebraicTopology.SimplicialObject.TruncatedExtensionEpi
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Objects

/-!
# The canonical morphism to the matching object, read through its cone legs

`CategoryTheory.SimplicialObject.Truncated.truncCoskUnit` is the canonical morphism from an
`M`-truncated simplicial object `Y` to the `M`-truncation of the `n`-th coskeleton of its
`n`-truncation, defined by the universal property of the latter as a right Kan extension. Its
composite with each cone leg of the matching object is the action of the simplicial object on the
corresponding morphism of `SimplexCategory`.

Equivalently, in the language of
`CategoryTheory.SimplicialObject.Truncated.coskFace`: the face family cut out by the canonical
morphism is the simplicial object's own action. That is `coskFace_truncCoskUnitTop`, and since the
cone legs are jointly monic (`hom_ext_of_coskFace`) it pins the canonical morphism down.

## Main definitions

* `CategoryTheory.SimplicialObject.Truncated.truncCoskUnitTop` and `truncCoskUnitAt`: the
  degree-`M + 1` component, and the component at an `M`-truncated object, of the canonical
  morphism of an `(M + 1)`-truncated simplicial object, each with an ascribed type.

## Main results

* `CategoryTheory.SimplicialObject.Truncated.truncCoskUnit_fac`: the defining property of
  `truncCoskUnit`, namely that its restriction along the inclusion of truncated simplex categories
  is the identity.
* `CategoryTheory.SimplicialObject.Truncated.truncCoskUnit_app_comp_ranCounit_app` and
  `truncCoskUnitAt_comp_ranCounit_app`: the same statement componentwise.
* `CategoryTheory.SimplicialObject.Truncated.hom_ext_of_coskFace`: two morphisms into the matching
  object that cut out the same face family are equal.
* `CategoryTheory.SimplicialObject.Truncated.coskFace_truncCoskUnitTop`: the face family cut out
  by the degree-`M + 1` component of the canonical morphism of an `(M + 1)`-truncated simplicial
  object `Z` is `Z.map`.

## References

* [Stacks Project, Tag 0187](https://stacks.math.columbia.edu/tag/0187)
* [Stacks Project, Tag 0DAV](https://stacks.math.columbia.edu/tag/0DAV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open CategoryTheory.SimplicialObject

universe v u

namespace CategoryTheory.SimplicialObject.Truncated

variable {A : Type u} [Category.{v} A]
  [∀ (k : ℕ) (F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ A),
    (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F]

/-- The defining property of `truncCoskUnit`: restricting it along the inclusion of truncated
simplex categories and composing with the counit of the right Kan extension gives the identity. -/
theorem truncCoskUnit_fac {n M : ℕ} (h : n ≤ M) (Y : SimplicialObject.Truncated A M) :
    Functor.whiskerLeft (SimplexCategory.Truncated.incl n M h).op (truncCoskUnit h Y)
        ≫ (SimplexCategory.Truncated.inclusion n).op.ranCounit.app
            ((Truncated.trunc A M n h).obj Y)
      = 𝟙 _ :=
  have := isRightKanExtension_truncation_cosk h ((Truncated.trunc A M n h).obj Y)
  Functor.liftOfIsRightKanExtension_fac _ _ _ _

/-- The componentwise form of `truncCoskUnit_fac`. -/
theorem truncCoskUnit_app_comp_ranCounit_app {n M : ℕ} (h : n ≤ M)
    (Y : SimplicialObject.Truncated A M) (x : SimplexCategory.Truncated n) :
    (truncCoskUnit h Y).app (op ⟨x.obj, x.property.trans h⟩)
        ≫ ((SimplexCategory.Truncated.inclusion n).op.ranCounit.app
            ((Truncated.trunc A M n h).obj Y)).app (op x)
      = 𝟙 _ :=
  congrArg (fun t ↦ NatTrans.app t (op x)) (truncCoskUnit_fac h Y)

/-- The degree-`M + 1` component of the canonical morphism from an `(M + 1)`-truncated simplicial
object to the `M`-th coskeleton of its `M`-truncation, with its type ascribed in the matching
object spelling. -/
noncomputable def truncCoskUnitTop {M : ℕ} (h : M ≤ M + 1)
    (Z : SimplicialObject.Truncated A (M + 1)) :
    Z.obj (op ⟨⦋M + 1⦌, le_rfl⟩)
      ⟶ matchingObj ((Truncated.trunc A (M + 1) M h).obj Z) :=
  (truncCoskUnit h Z).app (op ⟨⦋M + 1⦌, le_rfl⟩)

/-- **The cone legs of the matching object are jointly monic.** Two morphisms into the matching
object that cut out the same face family are equal. -/
theorem hom_ext_of_coskFace {M : ℕ} (Y : SimplicialObject.Truncated A M) {P : A}
    {a b : P ⟶ matchingObj Y}
    (hab : ∀ (x : SimplexCategory.Truncated M) (m : x.obj ⟶ ⦋M + 1⦌),
      coskFace Y a x m = coskFace Y b x m) : a = b := by
  have key : a ≫ ((SimplexCategory.Truncated.inclusion M).op.ranObjObjIsoLimit Y
        (op ⦋M + 1⦌)).hom
      = b ≫ ((SimplexCategory.Truncated.inclusion M).op.ranObjObjIsoLimit Y
        (op ⦋M + 1⦌)).hom := by
    refine limit.hom_ext fun f ↦ ?_
    rw [Category.assoc, Category.assoc, Functor.ranObjObjIsoLimit_hom_π]
    exact hab f.right.unop f.hom.unop
  exact (cancel_mono _).1 key

/-- The component at an `M`-truncated object `x` of the canonical morphism, with its type ascribed
in the spelling in which the counit of the right Kan extension expects it. -/
noncomputable def truncCoskUnitAt {M : ℕ} (h : M ≤ M + 1)
    (Z : SimplicialObject.Truncated A (M + 1)) (x : SimplexCategory.Truncated M) :
    Z.obj (op ⟨x.obj, x.property.trans h⟩)
      ⟶ ((Truncated.cosk M).obj ((Truncated.trunc A (M + 1) M h).obj Z)).obj (op x.obj) :=
  (truncCoskUnit h Z).app (op ⟨x.obj, x.property.trans h⟩)

/-- `truncCoskUnit_app_comp_ranCounit_app` in the ascribed spelling. -/
theorem truncCoskUnitAt_comp_ranCounit_app {M : ℕ} (h : M ≤ M + 1)
    (Z : SimplicialObject.Truncated A (M + 1)) (x : SimplexCategory.Truncated M) :
    truncCoskUnitAt h Z x
        ≫ ((SimplexCategory.Truncated.inclusion M).op.ranCounit.app
            ((Truncated.trunc A (M + 1) M h).obj Z)).app (op x)
      = 𝟙 _ :=
  truncCoskUnit_app_comp_ranCounit_app h Z x

/-- The face family cut out by the degree-`M + 1` component of the canonical morphism from an
`(M + 1)`-truncated simplicial object `Z` to the `M`-th coskeleton of its `M`-truncation is the
action of `Z` itself. -/
theorem coskFace_truncCoskUnitTop {M : ℕ} (h : M ≤ M + 1)
    (Z : SimplicialObject.Truncated A (M + 1)) (x : SimplexCategory.Truncated M)
    (m : x.obj ⟶ ⦋M + 1⦌) :
    coskFace ((Truncated.trunc A (M + 1) M h).obj Z) (truncCoskUnitTop h Z) x m
      = Z.map (ObjectProperty.homMk
          (X := (⟨x.obj, x.property.trans h⟩ : SimplexCategory.Truncated (M + 1)))
          (Y := ⟨⦋M + 1⦌, le_rfl⟩) m).op := by
  have hnat : Z.map (ObjectProperty.homMk
          (X := (⟨x.obj, x.property.trans h⟩ : SimplexCategory.Truncated (M + 1)))
          (Y := (⟨⦋M + 1⦌, le_rfl⟩ : SimplexCategory.Truncated (M + 1))) m).op
        ≫ truncCoskUnitAt h Z x
      = truncCoskUnitTop h Z
        ≫ ((Truncated.cosk M).obj ((Truncated.trunc A (M + 1) M h).obj Z)).map m.op :=
    (truncCoskUnit h Z).naturality _
  simp only [coskFace]
  rw [← Category.assoc, ← hnat, Category.assoc, truncCoskUnitAt_comp_ranCounit_app]
  exact Category.comp_id _

end CategoryTheory.SimplicialObject.Truncated

end
