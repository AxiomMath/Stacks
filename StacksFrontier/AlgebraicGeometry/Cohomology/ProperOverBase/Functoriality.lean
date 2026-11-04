module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.SchemeTheoreticImage

/-!
# Functoriality of properness of a closed subset over a base

Let `X` and `Y` be schemes locally of finite type over a base scheme `S` and let `f : X ⟶ Y` be
a morphism over `S`. Properness of a closed subset over `S` is carried along `f` in two ways.

* If `Y` is separated over `S`, the image under `f` of a closed subset of `X` proper over `S` is
  closed, and is proper over `S`.
* If `f` is proper, the inverse image under `f` of a closed subset of `Y` proper over `S` is
  proper over `S`.

The remaining case, that of a universally closed `f`, is
`AlgebraicGeometry.isProperOver_closedImage`.

## Main results

* `AlgebraicGeometry.isClosed_image_of_isProperOver` and
  `AlgebraicGeometry.isProperOver_image`: closedness and properness of the image, for a
  separated target.
* `AlgebraicGeometry.isProperOver_preimage`: properness of the inverse image along a proper
  morphism.

## Implementation notes

In the separated case the two conclusions are separate statements, the second regarding the
image as a closed subset by means of the first.

Both arguments compare closed subscheme structures by `0CYL`: in the separated case the
structure on the image is the kernel of the induced morphism, i.e. the scheme-theoretic image;
and for an inverse image it is the comap of the structure upstairs.

## References

* [Stacks Project, Tag 0AH6](https://stacks.math.columbia.edu/tag/0AH6)
* [Stacks Project, Tag 0CYQ](https://stacks.math.columbia.edu/tag/0CYQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Images under a morphism to a separated scheme -/

/-- The closed subscheme on a closed subset proper over the base is proper over a separated
base `g` after composing with `f`. -/
private lemma isProper_subschemeι_comp_comp {X Y S : Scheme.{u}}
    (p : X ⟶ S) (g : Y ⟶ S) (f : X ⟶ Y) (hfg : f ≫ g = p)
    [LocallyOfFiniteType p] [LocallyOfFiniteType g] [IsSeparated g]
    (Z : Closeds X) (hZ : IsProperOver p Z) :
    IsProper (((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ f) ≫ g) := by
  simpa only [Category.assoc, hfg] using hZ

/-- The range of the reduced closed subscheme on `Z` composed with `f` is the image of `Z`. -/
private lemma range_vanishingIdeal_subschemeι_comp {X Y : Scheme.{u}} (f : X ⟶ Y) (Z : Closeds X) :
    Set.range ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ f).base =
      f.base '' (Z : Set X) := by
  show Set.range (f.base ∘ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι.base) = _
  rw [Set.range_comp, Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]

/-- The image of a closed subset proper over the base is closed in a separated
scheme locally of finite type over that base. -/
@[stacks 0CYQ "image_separated", sga "4 XVII 6.1.1" "Clause (i)"]
lemma isClosed_image_of_isProperOver {X Y S : Scheme.{u}}
    (p : X ⟶ S) (g : Y ⟶ S) (f : X ⟶ Y) (hfg : f ≫ g = p)
    [LocallyOfFiniteType p] [LocallyOfFiniteType g] [IsSeparated g]
    (Z : Closeds X) (hZ : IsProperOver p Z) :
    IsClosed (f.base '' (Z : Set X)) := by
  have := isProper_subschemeι_comp_comp p g f hfg Z hZ
  have := IsProper.of_comp ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ f) g
  rw [← range_vanishingIdeal_subschemeι_comp]
  exact ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ f).isClosedMap.isClosed_range

/-- The image of a closed subset proper over the base is itself proper over the
base, when the target is separated and locally of finite type. -/
@[stacks 0CYQ "image_separated", ega "II 5.4.10" "more general"]
lemma isProperOver_image {X Y S : Scheme.{u}}
    (p : X ⟶ S) (g : Y ⟶ S) (f : X ⟶ Y) (hfg : f ≫ g = p)
    [LocallyOfFiniteType p] [LocallyOfFiniteType g] [IsSeparated g]
    (Z : Closeds X) (hZ : IsProperOver p Z) :
    IsProperOver g
      ⟨f.base '' (Z : Set X), isClosed_image_of_isProperOver p g f hfg Z hZ⟩ := by
  have := isProper_subschemeι_comp_comp p g f hfg Z hZ
  have := IsProper.of_comp ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ f) g
  refine (isProperOver_iff_exists_isProper g _).2
    ⟨((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ f).ker, Closeds.ext ?_,
      isProper_imageι_comp _ g⟩
  rw [Scheme.Hom.support_ker, range_vanishingIdeal_subschemeι_comp]
  exact (isClosed_image_of_isProperOver p g f hfg Z hZ).closure_eq

/-! ### Inverse images under a proper morphism -/

/-- The inverse image of a closed subset proper over the base along a proper
morphism is proper over the base. -/
@[stacks 0CYQ "preimage_proper"]
theorem isProperOver_preimage {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [IsProper f] [LocallyOfFiniteType g] (Z : Closeds Y)
    (hZ : IsProperOver g Z) :
    IsProperOver (f ≫ g) (Z.preimage f.continuous) := by
  let J : Y.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal Z
  let i : J.subscheme ⟶ Y := J.subschemeι
  let K : X.IdealSheafData := J.comap f
  have hKsupport : K.support = Z.preimage f.continuous := by
    apply SetLike.coe_injective
    show ((J.comap f).support : Set X) = (Z.preimage f.continuous : Set X)
    rw [Scheme.IdealSheafData.support_comap]
    show f ⁻¹' (J.support : Set Y) = f ⁻¹' (Z : Set Y)
    simp [J, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hKtoZ : IsProper ((J.comapIso f).hom ≫ pullback.snd f i) := by
    apply (MorphismProperty.cancel_left_of_respectsIso (P := @IsProper)
      (J.comapIso f).hom (pullback.snd f i)).2
    infer_instance
  have : IsProper (i ≫ g) := hZ
  have hKproper : IsProper (K.subschemeι ≫ f ≫ g) := by
    have hEq : ((J.comapIso f).hom ≫ pullback.snd f i) ≫ (i ≫ g) =
        K.subschemeι ≫ f ≫ g := by
      rw [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_snd,
        Scheme.IdealSheafData.subschemeMap_subschemeι]
      rfl
    rw [← hEq]
    infer_instance
  exact (isProperOver_iff_exists_isProper (f := f ≫ g) (Z := Z.preimage f.continuous)).2
    ⟨K, hKsupport, hKproper⟩

end AlgebraicGeometry

end
