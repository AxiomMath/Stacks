module

public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.ProjectiveSchemes
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The disjoint union of two smooth projective schemes

The category of smooth projective schemes over a field `k` has binary coproducts: the disjoint
union `X ⨿ Y` of the underlying schemes, with the structure morphism induced by those of `X` and
`Y`, is smooth and projective over `k`, and it is the coproduct of `X` and `Y` in the category.

## Main definitions

* `Stacks.WeilCohomology.SmoothProjectiveScheme.coprodObj`: the disjoint union `X ⨿ Y`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.coprodInl`,
  `Stacks.WeilCohomology.SmoothProjectiveScheme.coprodInr`: the coprojections.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.isColimitCoprodCofan`: they present `X ⨿ Y` as
  the coproduct of `X` and `Y`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.coprodObjIso`: the comparison with an arbitrary
  coproduct of `X` and `Y`.

## Main results

* `Stacks.WeilCohomology.SmoothProjectiveScheme.smooth_coprod_desc`: a disjoint union of smooth
  morphisms is smooth.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.isProjectiveMorphism_coprod_desc`: over a field
  a disjoint union of projective morphisms is projective.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.isColimitMapCofan`: the underlying scheme of any
  coproduct of `X` and `Y` in the category is the coproduct of the underlying schemes; conversely
  `Stacks.WeilCohomology.SmoothProjectiveScheme.isColimitOfIsColimitMapCofan`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.isCompl_range_inl_inr`: the coprojections of any
  coproduct are open immersions (`isOpenImmersion_inl`, `isOpenImmersion_inr`) onto
  complementary subsets, hence also closed immersions (`isClosedImmersion_inl`,
  `isClosedImmersion_inr`).

## Implementation notes

The objects are those of `Stacks.WeilCohomology.SmoothProjectiveScheme`, the object type of the
category of correspondences: a scheme `X.obj.left` over `Spec(k)` whose structure morphism
`X.obj.hom` is smooth and H-projective; morphisms are morphisms of schemes over `k`, with
underlying morphism of schemes `f.hom.left`.

## References

* [Stacks Project, Tag 0FHJ](https://stacks.math.columbia.edu/tag/0FHJ)
* [Stacks Project, Tag 0B46](https://stacks.math.columbia.edu/tag/0B46)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.WeilCohomology

namespace SmoothProjectiveScheme

/-- **A disjoint union of smooth morphisms is smooth**: if `f : X ⟶ S` and `g : Y ⟶ S` are
smooth, so is `coprod.desc f g : X ⨿ Y ⟶ S`. -/
theorem smooth_coprod_desc {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [Smooth f]
    [Smooth g] : Smooth (coprod.desc f g) := by
  have : IsZariskiLocalAtSource @Smooth.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth)
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth) (coprodOpenCover.{u, 0} X Y)]
  rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
  · change Smooth (coprod.inl ≫ coprod.desc f g)
    rw [coprod.inl_desc]
    infer_instance
  · change Smooth (coprod.inr ≫ coprod.desc f g)
    rw [coprod.inr_desc]
    infer_instance

/-- **Over a field, a disjoint union of projective morphisms is projective**: if
`f : X ⟶ Spec(k)` and `g : Y ⟶ Spec(k)` are projective, so is `coprod.desc f g`. -/
@[ega "II 5.5.6" "special case"]
theorem isProjectiveMorphism_coprod_desc {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (hf : IsProjectiveMorphism f)
    (hg : IsProjectiveMorphism g) : IsProjectiveMorphism (coprod.desc f g) := by
  have hS : HasAmpleInvertibleSheaf (Spec (.of k)) := (hasAmpleInvertibleSheaf_iff _).mpr
    ⟨Stacks.Ample.unitModule _, inferInstance, Stacks.Ample.isAmple_unitModule_of_isAffine _⟩
  rw [← isProjective_iff_isProjectiveMorphism_of_hasAmpleInvertibleSheaf _ hS] at hf hg ⊢
  exact isProjective_coprod_desc f g hS hf hg

variable {k : Type u} [Field k] (X Y : (SmoothProjectiveScheme k).FullSubcategory)

/-- **The disjoint union `X ⨿ Y` of two smooth projective schemes over `k`**: the coproduct of
the underlying schemes, with the structure morphism induced by those of `X` and `Y`. -/
def coprodObj : (SmoothProjectiveScheme k).FullSubcategory :=
  ⟨Over.mk (coprod.desc X.obj.hom Y.obj.hom),
    smooth_coprod_desc _ _,
    (isProjectiveMorphism_coprod_desc _ _
        ((isProjective_iff_isProjectiveMorphism_of_isAffine _).1
        (SmoothProjectiveScheme.isProjective X))
      ((isProjective_iff_isProjectiveMorphism_of_isAffine _).1
          (SmoothProjectiveScheme.isProjective Y))).isProjective⟩

/-- The underlying scheme of `coprodObj X Y` is the disjoint union of the underlying schemes. -/
@[simp]
theorem coprodObj_left : (coprodObj X Y).obj.left = (X.obj.left ⨿ Y.obj.left) :=
  rfl

/-- The structure morphism of `coprodObj X Y` is induced by those of `X` and `Y`. -/
@[simp]
theorem coprodObj_hom : (coprodObj X Y).obj.hom = coprod.desc X.obj.hom Y.obj.hom :=
  rfl

/-- The first coprojection `X ⟶ X ⨿ Y`. -/
def coprodInl : X ⟶ coprodObj X Y :=
  ObjectProperty.homMk (Over.homMk (V := (coprodObj X Y).obj) coprod.inl (coprod.inl_desc _ _))

/-- The second coprojection `Y ⟶ X ⨿ Y`. -/
def coprodInr : Y ⟶ coprodObj X Y :=
  ObjectProperty.homMk (Over.homMk (V := (coprodObj X Y).obj) coprod.inr (coprod.inr_desc _ _))

/-- The underlying morphism of schemes of `coprodInl X Y` is `coprod.inl`. -/
@[simp]
theorem coprodInl_hom_left : (coprodInl X Y).hom.left = coprod.inl :=
  rfl

/-- The underlying morphism of schemes of `coprodInr X Y` is `coprod.inr`. -/
@[simp]
theorem coprodInr_hom_left : (coprodInr X Y).hom.left = coprod.inr :=
  rfl

/-- The binary cofan of the two coprojections into `X ⨿ Y`. -/
abbrev coprodCofan : BinaryCofan X Y :=
  BinaryCofan.mk (coprodInl X Y) (coprodInr X Y)

/-- A morphism of the category is determined by its underlying morphism of schemes. -/
theorem hom_ext_left {P Q : (SmoothProjectiveScheme k).FullSubcategory} {f g : P ⟶ Q}
    (h : f.hom.left = g.hom.left) : f = g :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext h)

/-- **`X ⨿ Y` is the coproduct of `X` and `Y`** in the category of smooth projective schemes
over `k`. -/
def isColimitCoprodCofan : IsColimit (coprodCofan X Y) :=
  BinaryCofan.IsColimit.mk _
    (fun {T} a b => ObjectProperty.homMk (Over.homMk (U := (coprodObj X Y).obj) (V := T.obj)
      (coprod.desc a.hom.left b.hom.left)
      (coprod.hom_ext (by simp [Over.w a.hom]) (by simp [Over.w b.hom]))))
    (fun a b => hom_ext_left (coprod.inl_desc a.hom.left b.hom.left))
    (fun a b => hom_ext_left (coprod.inr_desc a.hom.left b.hom.left))
    (fun {T} a b m h₁ h₂ => hom_ext_left (coprod.hom_ext
      ((congrArg (fun f => f.hom.left) h₁).trans (coprod.inl_desc a.hom.left b.hom.left).symm)
      ((congrArg (fun f => f.hom.left) h₂).trans (coprod.inr_desc a.hom.left b.hom.left).symm)))

/-- Any two smooth projective schemes over `k` have a coproduct. -/
instance (X Y : (SmoothProjectiveScheme k).FullSubcategory) : HasColimit (pair X Y) :=
  HasColimit.mk ⟨_, isColimitCoprodCofan X Y⟩

/-- The category of smooth projective schemes over `k` has binary coproducts. -/
instance : HasBinaryCoproducts ((SmoothProjectiveScheme k).FullSubcategory) :=
  hasBinaryCoproducts_of_hasColimit_pair _

variable {X Y} {c : BinaryCofan X Y}

/-- The comparison isomorphism from the chosen disjoint union to any coproduct of `X` and `Y`. -/
def coprodObjIso (hc : IsColimit c) : coprodObj X Y ≅ c.pt :=
  (isColimitCoprodCofan X Y).coconePointUniqueUpToIso hc

/-- The first coprojection of `X ⨿ Y` followed by `coprodObjIso hc` is the first coprojection
of `c`. -/
@[reassoc (attr := simp)]
theorem coprodInl_coprodObjIso_hom (hc : IsColimit c) :
    coprodInl X Y ≫ (coprodObjIso hc).hom = c.inl :=
  (isColimitCoprodCofan X Y).comp_coconePointUniqueUpToIso_hom hc ⟨WalkingPair.left⟩

/-- The second coprojection of `X ⨿ Y` followed by `coprodObjIso hc` is the second
coprojection of `c`. -/
@[reassoc (attr := simp)]
theorem coprodInr_coprodObjIso_hom (hc : IsColimit c) :
    coprodInr X Y ≫ (coprodObjIso hc).hom = c.inr :=
  (isColimitCoprodCofan X Y).comp_coconePointUniqueUpToIso_hom hc ⟨WalkingPair.right⟩

/-- The underlying isomorphism of schemes of `coprodObjIso`. -/
def coprodObjIsoLeft (hc : IsColimit c) : X.obj.left ⨿ Y.obj.left ≅ c.pt.obj.left :=
  ((ObjectProperty.ι _ ⋙ Over.forget _).mapIso (coprodObjIso hc))

/-- The underlying morphism of schemes of the first coprojection of a coproduct is the
coprojection of the disjoint union of schemes, followed by an isomorphism. -/
theorem inl_hom_left (hc : IsColimit c) :
    c.inl.hom.left = coprod.inl ≫ (coprodObjIsoLeft hc).hom := by
  rw [← coprodInl_coprodObjIso_hom hc]
  rfl

/-- The underlying morphism of schemes of the second coprojection of a coproduct is the
coprojection of the disjoint union of schemes, followed by an isomorphism. -/
theorem inr_hom_left (hc : IsColimit c) :
    c.inr.hom.left = coprod.inr ≫ (coprodObjIsoLeft hc).hom := by
  rw [← coprodInr_coprodObjIso_hom hc]
  rfl

/-- **The underlying scheme of a coproduct is the coproduct of the underlying schemes.** -/
def isColimitMapCofan (hc : IsColimit c) :
    IsColimit (BinaryCofan.mk c.inl.hom.left c.inr.hom.left) :=
  BinaryCofan.isColimitMk
    (fun s => (coprodObjIsoLeft hc).inv ≫
      (coprod.desc s.inl s.inr : X.obj.left ⨿ Y.obj.left ⟶ s.pt))
    (fun s => by
      rw [inl_hom_left hc, Category.assoc, Iso.hom_inv_id_assoc]
      exact coprod.inl_desc _ _)
    (fun s => by
      rw [inr_hom_left hc, Category.assoc, Iso.hom_inv_id_assoc]
      exact coprod.inr_desc _ _)
    (fun s m h₁ h₂ => by
      rw [Iso.eq_inv_comp]
      refine coprod.hom_ext ?_ ?_
      · rw [coprod.inl_desc, ← h₁, inl_hom_left hc, Category.assoc]
      · rw [coprod.inr_desc, ← h₂, inr_hom_left hc, Category.assoc])

/-- **A cofan whose underlying cofan of schemes is a coproduct is a coproduct**: the converse of
`isColimitMapCofan`. -/
def isColimitOfIsColimitMapCofan (h : IsColimit (BinaryCofan.mk c.inl.hom.left c.inr.hom.left)) :
    IsColimit c :=
  BinaryCofan.IsColimit.mk _
    (fun {T} a b => ObjectProperty.homMk (Over.homMk (U := c.pt.obj) (V := T.obj)
      (h.desc (BinaryCofan.mk a.hom.left b.hom.left))
      (BinaryCofan.IsColimit.hom_ext h
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ T.obj.hom)
            (h.fac (BinaryCofan.mk a.hom.left b.hom.left) ⟨WalkingPair.left⟩)).trans
            ((Over.w a.hom).trans (Over.w c.inl.hom).symm)))
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ T.obj.hom)
            (h.fac (BinaryCofan.mk a.hom.left b.hom.left) ⟨WalkingPair.right⟩)).trans
            ((Over.w b.hom).trans (Over.w c.inr.hom).symm))))))
    (fun a b => hom_ext_left (h.fac (BinaryCofan.mk a.hom.left b.hom.left) ⟨WalkingPair.left⟩))
    (fun a b => hom_ext_left (h.fac (BinaryCofan.mk a.hom.left b.hom.left) ⟨WalkingPair.right⟩))
    (fun {_} a b _ h₁ h₂ => hom_ext_left (BinaryCofan.IsColimit.hom_ext h
      ((congrArg (fun f => f.hom.left) h₁).trans
        (h.fac (BinaryCofan.mk a.hom.left b.hom.left) ⟨WalkingPair.left⟩).symm)
      ((congrArg (fun f => f.hom.left) h₂).trans
        (h.fac (BinaryCofan.mk a.hom.left b.hom.left) ⟨WalkingPair.right⟩).symm)))

/-- The underlying morphism of schemes of the first coprojection of a coproduct is an open
immersion. -/
theorem isOpenImmersion_inl (hc : IsColimit c) : IsOpenImmersion c.inl.hom.left := by
  rw [inl_hom_left hc]
  infer_instance

/-- The underlying morphism of schemes of the second coprojection of a coproduct is an open
immersion. -/
theorem isOpenImmersion_inr (hc : IsColimit c) : IsOpenImmersion c.inr.hom.left := by
  rw [inr_hom_left hc]
  infer_instance

/-- The images of the two coprojections of a coproduct are complementary. -/
theorem isCompl_range_inl_inr (hc : IsColimit c) :
    IsCompl (Set.range c.inl.hom.left) (Set.range c.inr.hom.left) := by
  let E := coprodObjIsoLeft hc
  have hinl : ∀ x, c.inl.hom.left x =
      E.hom ((coprod.inl : X.obj.left ⟶ X.obj.left ⨿ Y.obj.left) x) :=
    fun x => by rw [inl_hom_left hc]; rfl
  have hinr : ∀ y, c.inr.hom.left y =
      E.hom ((coprod.inr : Y.obj.left ⟶ X.obj.left ⨿ Y.obj.left) y) :=
    fun y => by rw [inr_hom_left hc]; rfl
  refine ⟨Set.disjoint_left.mpr ?_, codisjoint_iff.mpr (Set.eq_univ_of_forall fun z => ?_)⟩
  · rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    rw [hinl, hinr] at hy
    exact AlgebraicGeometry.inl_ne_inr _ _ x y
      ((Scheme.homeoOfIso E).injective (by simpa [Scheme.homeoOfIso_apply] using hy.symm))
  · obtain ⟨w, rfl⟩ : ∃ w, E.hom w = z := ⟨E.inv z, by simp⟩
    rcases Set.eq_univ_iff_forall.mp
        (AlgebraicGeometry.isCompl_range_inl_inr X.obj.left Y.obj.left).sup_eq_top w with
      ⟨x, rfl⟩ | ⟨y, rfl⟩
    · exact Or.inl ⟨x, hinl x⟩
    · exact Or.inr ⟨y, hinr y⟩

/-- An open immersion whose range is complementary to that of another open immersion is a closed
immersion. -/
private theorem isClosedImmersion_of_isCompl_range {U V S : Scheme.{u}} (f : U ⟶ S) (g : V ⟶ S)
    [IsOpenImmersion f] [IsOpenImmersion g] (h : IsCompl (Set.range f) (Set.range g)) :
    IsClosedImmersion f :=
  IsClosedImmersion.of_isPreimmersion _ (by
    rw [h.eq_compl]
    exact g.isOpenEmbedding.isOpen_range.isClosed_compl)

/-- The underlying morphism of schemes of the first coprojection of a coproduct is a closed
immersion. -/
theorem isClosedImmersion_inl (hc : IsColimit c) : IsClosedImmersion c.inl.hom.left :=
  have := isOpenImmersion_inl hc
  have := isOpenImmersion_inr hc
  isClosedImmersion_of_isCompl_range _ c.inr.hom.left (isCompl_range_inl_inr hc)

/-- The underlying morphism of schemes of the second coprojection of a coproduct is a closed
immersion. -/
theorem isClosedImmersion_inr (hc : IsColimit c) : IsClosedImmersion c.inr.hom.left :=
  have := isOpenImmersion_inl hc
  have := isOpenImmersion_inr hc
  isClosedImmersion_of_isCompl_range _ c.inl.hom.left (isCompl_range_inl_inr hc).symm

/-- The disjoint union is nonempty as soon as the first summand is. -/
theorem nonempty_pt_of_left [Nonempty X.obj.left] : Nonempty c.pt.obj.left :=
  ⟨c.inl.hom.left (Classical.arbitrary X.obj.left)⟩

/-- The disjoint union is nonempty as soon as the second summand is. -/
theorem nonempty_pt_of_right [Nonempty Y.obj.left] : Nonempty c.pt.obj.left :=
  ⟨c.inr.hom.left (Classical.arbitrary Y.obj.left)⟩

/-- Local fibre dimension is computed on an open subscheme: the version of
`AlgebraicGeometry.fiberDimensionAt_comp_openImmersion` for a morphism `g` given together with a
factorisation `g = j ≫ f` through an open immersion. -/
private theorem fiberDimensionAt_of_comp_eq {U V S : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
    (f : V ⟶ S) (g : U ⟶ S) (h : j ≫ f = g) (x : U) :
    topologicalKrullDimAt (g.fiber (g x)) (g.asFiber x) =
      topologicalKrullDimAt (f.fiber (f (j x))) (f.asFiber (j x)) := by
  subst h
  exact fiberDimensionAt_comp_openImmersion j f x

/-- **A disjoint union is equidimensional of dimension `d` exactly when both summands are**: the
structure morphism of `X ⨿ Y` has relative dimension `d` over `k` if and only if those of `X` and
`Y` do. -/
theorem relativeDimension_pt_iff (hc : IsColimit c) (d : ℕ) :
    RelativeDimension c.pt.obj.hom d ↔
      RelativeDimension X.obj.hom d ∧ RelativeDimension Y.obj.hom d := by
  have := isOpenImmersion_inl hc
  have := isOpenImmersion_inr hc
  have hl := fiberDimensionAt_of_comp_eq _ _ _ (Over.w c.inl.hom)
  have hr := fiberDimensionAt_of_comp_eq _ _ _ (Over.w c.inr.hom)
  simp only [relativeDimension_iff_forall_topologicalKrullDimAt]
  refine ⟨fun h => ⟨fun x => (hl x).trans (h _), fun y => (hr y).trans (h _)⟩, fun ⟨hX, hY⟩ z => ?_⟩
  rcases Set.eq_univ_iff_forall.mp (isCompl_range_inl_inr hc).sup_eq_top z with
    ⟨x, rfl⟩ | ⟨y, rfl⟩
  · exact (hl x).symm.trans (hX x)
  · exact (hr y).symm.trans (hY y)

/-- **If `X` and `Y` are equidimensional of the same dimension `d`, so is `X ⨿ Y`.** -/
theorem relativeDimension_pt (hc : IsColimit c) {d : ℕ} (hX : RelativeDimension X.obj.hom d)
    (hY : RelativeDimension Y.obj.hom d) : RelativeDimension c.pt.obj.hom d :=
  (relativeDimension_pt_iff hc d).mpr ⟨hX, hY⟩

end SmoothProjectiveScheme

end Stacks.WeilCohomology

end
