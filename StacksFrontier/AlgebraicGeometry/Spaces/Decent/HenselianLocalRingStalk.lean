module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Filtered.FinallySmall
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.RegularIdealSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleStalk.ElementaryFiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.Henselization
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.ConnectedNeighborhoods
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.AffineElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhoodCofiltered
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhoodFieldPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.MonomorphismPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ChangeOfBigSites
public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse
public import StacksFrontier.RingTheory.Henselian.Henselization.Basic
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.BaseChange

/-!
# The henselian local ring as a henselization of a neighborhood stalk

The henselian local ring of a decent algebraic space at a point is a local ring, and it is a
henselization of the local ring of any elementary étale neighborhood at its distinguished
point. The comparison map is the one sending the germ of a section over a pointed open
subscheme of the neighborhood to its canonical image in the colimit of global sections, since
a pointed open subscheme of an elementary étale neighborhood is again an elementary étale
neighborhood of the same point.

## Main definitions

* `AlgebraicGeometry.Space.neighborhoodStalkMap` is the homomorphism of local rings induced by
  a morphism of elementary étale neighborhoods.
* `AlgebraicGeometry.Space.openRestrictionNeighborhood` is the elementary étale neighborhood
  obtained by restricting a neighborhood to a pointed open subscheme, and
  `AlgebraicGeometry.Space.openRestrictionSectionHom` is the induced homomorphism from the
  sections over that open subscheme into the henselian local ring.
* `AlgebraicGeometry.Space.stalkToHenselianLocalRing` is the canonical homomorphism from the
  local ring of an elementary étale neighborhood at its distinguished point into the henselian
  local ring, and `AlgebraicGeometry.Space.stalkAlgebra` is the resulting algebra structure.

## Main results

* `AlgebraicGeometry.Space.stalkToHenselianLocalRing_germ`: the canonical homomorphism sends
  the germ of a section over a pointed open subscheme to the canonical image of that section.
* `AlgebraicGeometry.Space.stalkToHenselianLocalRing_naturality`: the canonical homomorphisms
  are compatible with every morphism of elementary étale neighborhoods.
* `AlgebraicGeometry.Space.henselianLocalRing_isLocalRing`: the henselian local ring is a local
  ring.
* `AlgebraicGeometry.Space.henselianLocalRing_isHenselization`: it is a henselization of the
  local ring of any elementary étale neighborhood at its distinguished point, and
  `AlgebraicGeometry.Space.map_maximalIdeal_stalkToHenselianLocalRing`,
  `AlgebraicGeometry.Space.isLocalHom_stalkToHenselianLocalRing` and
  `AlgebraicGeometry.Space.exists_residueFieldEquiv_henselianLocalRing` identify its maximal
  ideal and its residue field.

## Implementation notes

The source states an equality of henselizations. Here the henselian local ring carries the
algebra structure of the canonical homomorphism out of the neighborhood stalk, and the
henselization statement is Mathlib's `IsLocalRing.IsHenselization` for that algebra structure.
The canonical homomorphism is pinned by its values on germs over pointed open subschemes;
a condition on global sections alone would not determine it.

Two colimits are compared. The local ring at the distinguished point is the colimit of the
sections over the pointed open subschemes, which sits in `CommRingCat.{u}`, while the henselian
local ring is a colimit in `CommRingCat.{u + 1}`; the comparison homomorphism is therefore built
from the presentation of a colimit of commutative rings as a quotient of a prequotient, which
determines a homomorphism into a ring of any size. The henselization statement compares the
colimit over the elementary étale neighborhoods of the space with the colimit over the
elementary étale neighborhoods of the neighborhood scheme: neighborhoods equipped with a map to
a fixed one are initial among all neighborhoods, and they are initial among the elementary étale
neighborhoods of the neighborhood scheme as well, because an affine open subscheme of such a
scheme neighborhood is small enough to belong to the chosen big site.

Both statements use that the category of elementary étale neighborhoods of a point of a decent
algebraic space is cofiltered, which is Stacks 0BGV: the category is cofiltered as soon as it is
nonempty, and a decent algebraic space has an affine elementary étale neighborhood at every
point by Stacks 0BBP. In the henselization statement a neighborhood is given, so it already
witnesses the nonemptiness.

## References

* [Stacks Project, Tag 0EMY](https://stacks.math.columbia.edu/tag/0EMY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Space

/-! ### Descending a compatible family of homomorphisms through a colimit of rings -/

section ColimitDesc

/-- The homomorphism out of a colimit of commutative rings restricts on each object of the
diagram to the given homomorphism. -/
theorem descOfCompatible_coconeMorphism {J : Type w} [SmallCategory J]
    (F : J ⥤ CommRingCat.{w}) {R : Type*} [CommRing R] (φ : ∀ j, (F.obj j) →+* R)
    (hφ : ∀ {j j'} (f : j ⟶ j') (a : F.obj j), φ j' (F.map f a) = φ j a)
    (j : J) (a : F.obj j) :
    descColimit F φ hφ ((CommRingCat.Colimits.coconeMorphism F j).hom a) = φ j a := rfl

/-- Lifting commutative rings to a larger universe preserves filtered colimits. -/
theorem uliftCommRingFunctor_preservesFilteredColimits :
    PreservesFilteredColimitsOfSize.{u, u} AlgebraicGeometry.commRingULiftFunctor.{u, v} where
  preserves_filtered_colimits {J} _ _ := {
    preservesColimit := fun {D} ↦ by
      let : PreservesFilteredColimitsOfSize.{u, u} (forget CommRingCat.{max u v}) :=
        preservesFilteredColimitsOfSize_of_univLE.{max u v, max u v, u, u} _
      let e : forget CommRingCat.{u} ⋙ uliftFunctor.{v, u} ≅
          AlgebraicGeometry.commRingULiftFunctor.{u, v} ⋙ forget CommRingCat.{max u v} :=
        NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
      let : PreservesColimit D
          (AlgebraicGeometry.commRingULiftFunctor.{u, v} ⋙ forget CommRingCat.{max u v}) :=
        preservesColimit_of_natIso D e
      let : HasColimitsOfSize.{u, u} CommRingCat.{max u v} :=
        hasColimitsOfSizeOfUnivLE.{max u v, max u v, u, u} _
      let : ReflectsColimit (D ⋙ AlgebraicGeometry.commRingULiftFunctor.{u, v})
          (forget CommRingCat.{max u v}) :=
        reflectsColimit_of_reflectsIsomorphisms _ _
      exact preservesColimit_of_reflects_of_preserves _ (forget CommRingCat.{max u v}) }

end ColimitDesc

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
  (x : points B S hS X)

/-! ### The stalk of an elementary étale neighborhood -/

/-- The homomorphism of local rings induced by a morphism of elementary étale neighborhoods: the
stalk map of the underlying morphism of schemes, transported along the equality of the
distinguished points. -/
def neighborhoodStalkMap {V U : ElementaryEtaleNeighborhood B S hS X hX x} (f : V ⟶ U) :
    U.scheme.left.1.presheaf.stalk U.point ⟶ V.scheme.left.1.presheaf.stalk V.point :=
  (U.scheme.left.1.presheaf.stalkCongr (.of_eq f.map_point.symm)).hom ≫
    (f.hom.left.1.stalkMap V.point)

/-- The homomorphism of local rings induced by a morphism of elementary étale neighborhoods is
local. -/
theorem neighborhoodStalkMap_isLocalHom
    {V U : ElementaryEtaleNeighborhood B S hS X hX x} (f : V ⟶ U) :
    IsLocalHom (neighborhoodStalkMap B S hS X hX x f).hom := by
  unfold neighborhoodStalkMap
  infer_instance

/-! ### Restricting an elementary étale neighborhood to a pointed open subscheme -/

/-- An open subscheme of the scheme of an elementary étale neighborhood, as an object of the
chosen big site over the base. -/
@[reducible] def openRestrictionScheme (U : ElementaryEtaleNeighborhood B S hS X hX x)
    (W : U.scheme.left.1.Opens) : BigFppfOver B S hS :=
  Over.mk ((ObjectProperty.homMk W.ι :
      (⟨W.toScheme, (Scheme.size_coe_opens_le U.scheme.left.1 W).trans_lt U.scheme.left.2⟩ :
        B.Schemes) ⟶ U.scheme.left) ≫ U.scheme.hom)

/-- The open immersion of an open subscheme of an elementary étale neighborhood into that
neighborhood. -/
def openRestrictionMap (U : ElementaryEtaleNeighborhood B S hS X hX x)
    (W : U.scheme.left.1.Opens) :
    openRestrictionScheme B S hS X hX x U W ⟶ U.scheme :=
  Over.homMk (ObjectProperty.homMk W.ι :
      (⟨W.toScheme, (Scheme.size_coe_opens_le U.scheme.left.1 W).trans_lt U.scheme.left.2⟩ :
        B.Schemes) ⟶ U.scheme.left)
    (by simp [openRestrictionScheme])

/-- A pointed open subscheme of an elementary étale neighborhood is again an elementary étale
neighborhood of the same point of the algebraic space. -/
@[reducible] def openRestrictionNeighborhood (U : ElementaryEtaleNeighborhood B S hS X hX x)
    (W : U.scheme.left.1.Opens) (hW : U.point ∈ W) :
    ElementaryEtaleNeighborhood B S hS X hX x := by
  let p : W.toScheme := ⟨U.point, hW⟩
  let e := W.ι.residueFieldMap p
  have hcontained : B.Contains (Spec (.of (W.toScheme.residueField p))) := by
    have eSpec : Spec (.of (U.scheme.left.1.residueField U.point)) ≅
        Spec (.of (W.toScheme.residueField p)) :=
      (asIso (Scheme.Spec.map e.op)).symm
    change (Spec (.of (W.toScheme.residueField p))).size < B.cutoff
    rw [← Scheme.size_congr eSpec]
    exact U.residueField_contained
  refine ⟨openRestrictionScheme B S hS X hX x U W, ⟨U.point, hW⟩, hcontained, ?_, ?_, ?_, ?_⟩
  · exact yoneda.map (openRestrictionMap B S hS X hX x U W) ≫ U.toSpace
  · apply isEtale_comp B S hS
      (etale_yoneda B S hS (openRestrictionMap B S hS X hX x U W) ?_)
      U.etale_toSpace
    change Etale W.ι
    infer_instance
  · let V := openRestrictionScheme B S hS X hX x U W
    let q : V.left.1 := ⟨U.point, hW⟩
    have hp : W.ι p = U.point := rfl
    let c := U.scheme.left.1.residueFieldCongr hp
    let e' : CommRingCat.of (U.scheme.left.1.residueField U.point) ⟶
        CommRingCat.of (W.toScheme.residueField p) := c.inv ≫ e
    have hcontainedV : B.Contains (Spec (.of (V.left.1.residueField q))) := by
      change B.Contains (Spec (.of (W.toScheme.residueField p)))
      exact hcontained
    let rV := residueFieldMap B S hS V q hcontainedV
    let rU := residueFieldMap B S hS U.scheme U.point U.residueField_contained
    let Vres := residueFieldObject B S hS V q hcontainedV
    let Ures := residueFieldObject B S hS U.scheme U.point U.residueField_contained
    have hCongr : Spec.map c.inv ≫ U.scheme.left.1.fromSpecResidueField U.point =
        U.scheme.left.1.fromSpecResidueField (W.ι p) := by
      have h := Scheme.residueFieldCongr_fromSpecResidueField hp
      calc
        Spec.map c.inv ≫ U.scheme.left.1.fromSpecResidueField U.point =
            Spec.map c.inv ≫
              (Spec.map c.hom ≫ U.scheme.left.1.fromSpecResidueField (W.ι p)) := by rw [← h]
        _ = (Spec.map c.inv ≫ Spec.map c.hom) ≫
            U.scheme.left.1.fromSpecResidueField (W.ι p) := by rw [Category.assoc]
        _ = U.scheme.left.1.fromSpecResidueField (W.ι p) := by simp [c]
    have hmap : Spec.map e' = Spec.map e ≫ Spec.map c.inv := by
      dsimp [e']
      rw [← Spec.map_comp]
    have hfactorScheme : Spec.map e' ≫ U.scheme.left.1.fromSpecResidueField U.point =
        W.toScheme.fromSpecResidueField p ≫ W.ι := by
      rw [hmap, Category.assoc, hCongr]
      exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField (f := W.ι) p
    let g₀ : Vres.left ⟶ Ures.left := ObjectProperty.homMk (Scheme.Spec.map e'.op)
    let g : Vres ⟶ Ures := Over.homMk g₀ (by
      apply B.inclusion.map_injective
      dsimp [Vres, Ures, residueFieldObject]
      change B.inclusion.map g₀ ≫ _ = _
      dsimp [g₀, ObjectProperty.homMk]
      change Spec.map e' ≫ _ = _
      exact congrArg (fun k ↦ k ≫ U.scheme.hom.1) hfactorScheme)
    have hfactor : rV ≫ openRestrictionMap B S hS X hX x U W = g ≫ rU := by
      apply Over.OverMorphism.ext
      apply B.inclusion.map_injective
      dsimp [Vres, Ures, residueFieldObject]
      dsimp [rV, rU, g, g₀, residueFieldMap]
      change W.toScheme.fromSpecResidueField q ≫ W.ι =
        Spec.map e' ≫ U.scheme.left.1.fromSpecResidueField U.point
      exact hfactorScheme.symm
    let pV : FieldValuedPoint B S hS (yoneda.obj V) :=
      ⟨V.left.1.residueField q, hcontainedV, V.left.1.fromSpecResidueField q ≫ V.hom.1,
        residueFieldMap B S hS V q hcontainedV⟩
    let pU : FieldValuedPoint B S hS (yoneda.obj U.scheme) :=
      ⟨U.scheme.left.1.residueField U.point, U.residueField_contained,
        U.scheme.left.1.fromSpecResidueField U.point ≫ U.scheme.hom.1,
        residueFieldMap B S hS U.scheme U.point U.residueField_contained⟩
    have hdom : FieldValuedPoint.Dominates B S hS (yoneda.obj U.scheme)
        (FieldValuedPoint.map B S hS (yoneda.obj V)
          (yoneda.map (openRestrictionMap B S hS X hX x U W)) pV) pU := by
      refine ⟨g, ?_⟩
      change g ≫ rU = rV ≫ openRestrictionMap B S hS X hX x U W
      exact hfactor.symm
    have hclasses :
        pointsMap B S hS (yoneda.obj V)
            (yoneda.map (openRestrictionMap B S hS X hX x U W))
            (presheafPoint B S hS V q hcontainedV) =
          presheafPoint B S hS U.scheme U.point U.residueField_contained := by
      change (FieldValuedPoint.map B S hS (yoneda.obj V)
          (yoneda.map (openRestrictionMap B S hS X hX x U W)) pV).class
          B S hS (yoneda.obj U.scheme) = pU.class B S hS (yoneda.obj U.scheme)
      exact FieldValuedPoint.class_eq_class_of_hasCommonExtension
        B S hS (yoneda.obj U.scheme)
        ⟨_, FieldValuedPoint.dominates_refl B S hS (yoneda.obj U.scheme) _, hdom⟩
    have hcomp :
        pointsMap B S hS (yoneda.obj V)
            (yoneda.map (openRestrictionMap B S hS X hX x U W) ≫ U.toSpace) =
          (pointsMap B S hS (yoneda.obj U.scheme) U.toSpace) ∘
            pointsMap B S hS (yoneda.obj V)
              (yoneda.map (openRestrictionMap B S hS X hX x U W)) := by
      funext z
      refine Quot.inductionOn z ?_
      intro z
      rfl
    change pointsMap B S hS (yoneda.obj V)
      (yoneda.map (openRestrictionMap B S hS X hX x U W) ≫ U.toSpace)
      (presheafPoint B S hS V q hcontainedV) = x
    rw [hcomp]
    change pointsMap B S hS (yoneda.obj U.scheme) U.toSpace
      (pointsMap B S hS (yoneda.obj V)
        (yoneda.map (openRestrictionMap B S hS X hX x U W))
        (presheafPoint B S hS V q hcontainedV)) = x
    rw [hclasses, U.map_point]
  · let V := openRestrictionScheme B S hS X hX x U W
    let q : V.left.1 := ⟨U.point, hW⟩
    have hp : W.ι p = U.point := rfl
    let c := U.scheme.left.1.residueFieldCongr hp
    let e' : CommRingCat.of (U.scheme.left.1.residueField U.point) ⟶
        CommRingCat.of (W.toScheme.residueField p) := c.inv ≫ e
    have hcontainedV : B.Contains (Spec (.of (V.left.1.residueField q))) := by
      change B.Contains (Spec (.of (W.toScheme.residueField p)))
      exact hcontained
    let rV := residueFieldMap B S hS V q hcontainedV
    let rU := residueFieldMap B S hS U.scheme U.point U.residueField_contained
    let Vres := residueFieldObject B S hS V q hcontainedV
    let Ures := residueFieldObject B S hS U.scheme U.point U.residueField_contained
    have hCongr : Spec.map c.inv ≫ U.scheme.left.1.fromSpecResidueField U.point =
        U.scheme.left.1.fromSpecResidueField (W.ι p) := by
      have h := Scheme.residueFieldCongr_fromSpecResidueField hp
      calc
        Spec.map c.inv ≫ U.scheme.left.1.fromSpecResidueField U.point =
            Spec.map c.inv ≫
              (Spec.map c.hom ≫ U.scheme.left.1.fromSpecResidueField (W.ι p)) := by rw [← h]
        _ = (Spec.map c.inv ≫ Spec.map c.hom) ≫
            U.scheme.left.1.fromSpecResidueField (W.ι p) := by rw [Category.assoc]
        _ = U.scheme.left.1.fromSpecResidueField (W.ι p) := by simp [c]
    have hmap : Spec.map e' = Spec.map e ≫ Spec.map c.inv := by
      dsimp [e']
      rw [← Spec.map_comp]
    have hfactorScheme : Spec.map e' ≫ U.scheme.left.1.fromSpecResidueField U.point =
        W.toScheme.fromSpecResidueField p ≫ W.ι := by
      rw [hmap, Category.assoc, hCongr]
      exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField (f := W.ι) p
    let g₀ : Vres.left ⟶ Ures.left := ObjectProperty.homMk (Scheme.Spec.map e'.op)
    let g : Vres ⟶ Ures := Over.homMk g₀ (by
      apply B.inclusion.map_injective
      dsimp [Vres, Ures, residueFieldObject]
      change B.inclusion.map g₀ ≫ _ = _
      dsimp [g₀, ObjectProperty.homMk]
      change Spec.map e' ≫ _ = _
      exact congrArg (fun k ↦ k ≫ U.scheme.hom.1) hfactorScheme)
    have : IsIso e' := by
      dsimp [e']
      infer_instance
    have : IsIso (Scheme.Spec.map e'.op) := inferInstance
    have hgi : IsIso (B.inclusion.map g₀) :=
      inferInstanceAs (IsIso (Scheme.Spec.map e'.op))
    have : IsIso g₀ :=
      (Functor.FullyFaithful.ofFullyFaithful B.inclusion).isIso_of_isIso_map g₀
    let gInv : Ures ⟶ Vres := Over.homMk (inv g₀) (by
      calc
        inv g₀ ≫ Vres.hom = inv g₀ ≫ (g.left ≫ Ures.hom) := by rw [← g.w]
        _ = inv g₀ ≫ (g₀ ≫ Ures.hom) := rfl
        _ = Ures.hom := by simp)
    have hright : g ≫ gInv = 𝟙 Vres := by
      apply Over.OverMorphism.ext
      simp [gInv, g, g₀]
    have hleft : gInv ≫ g = 𝟙 Ures := by
      apply Over.OverMorphism.ext
      simp [gInv, g, g₀]
    let gIso : Vres ≅ Ures := ⟨g, gInv, hright, hleft⟩
    have : IsIso g := gIso.isIso_hom
    have hfactor : rV ≫ openRestrictionMap B S hS X hX x U W = g ≫ rU := by
      apply Over.OverMorphism.ext
      apply B.inclusion.map_injective
      dsimp [Vres, Ures, residueFieldObject]
      dsimp [rV, rU, g, g₀, residueFieldMap]
      change W.toScheme.fromSpecResidueField q ≫ W.ι =
        Spec.map e' ≫ U.scheme.left.1.fromSpecResidueField U.point
      exact hfactorScheme.symm
    have : Mono (yoneda.map g) := inferInstance
    have : Mono (yoneda.map rU ≫ U.toSpace) := U.mono_residueField
    have hfactorYoneda : yoneda.map rV ≫
        yoneda.map (openRestrictionMap B S hS X hX x U W) ≫ U.toSpace =
        yoneda.map g ≫ (yoneda.map rU ≫ U.toSpace) := by
      calc
        _ = yoneda.map (rV ≫ openRestrictionMap B S hS X hX x U W) ≫ U.toSpace :=
          congrArg (fun f ↦ f ≫ U.toSpace)
            (yoneda.map_comp rV (openRestrictionMap B S hS X hX x U W)).symm
        _ = yoneda.map (g ≫ rU) ≫ U.toSpace :=
          congrArg (fun f ↦ f ≫ U.toSpace) (congrArg yoneda.map hfactor)
        _ = yoneda.map g ≫ (yoneda.map rU ≫ U.toSpace) := by
          rw [yoneda.map_comp]
          simp [Category.assoc]
    change Mono (yoneda.map rV ≫
      yoneda.map (openRestrictionMap B S hS X hX x U W) ≫ U.toSpace)
    rw [hfactorYoneda]
    exact mono_comp (yoneda.map g) (yoneda.map rU ≫ U.toSpace)

/-- The morphism of elementary étale neighborhoods given by an inclusion of pointed open
subschemes of a fixed neighborhood. -/
def openRestrictionNeighborhoodHom (U : ElementaryEtaleNeighborhood B S hS X hX x)
    {W W' : U.scheme.left.1.Opens} (hWW' : W ≤ W') (hW : U.point ∈ W) (hW' : U.point ∈ W') :
    openRestrictionNeighborhood B S hS X hX x U W hW ⟶
      openRestrictionNeighborhood B S hS X hX x U W' hW' := by
  let f₀ : W.toScheme ⟶ W'.toScheme := U.scheme.left.1.homOfLE hWW'
  let f₁ : (openRestrictionScheme B S hS X hX x U W).left ⟶
      (openRestrictionScheme B S hS X hX x U W').left := ObjectProperty.homMk f₀
  let f : (openRestrictionNeighborhood B S hS X hX x U W hW).scheme ⟶
      (openRestrictionNeighborhood B S hS X hX x U W' hW').scheme := Over.homMk f₁ (by
    apply B.inclusion.map_injective
    dsimp [f₁, ObjectProperty.homMk, openRestrictionScheme]
    rw [← Category.assoc, Scheme.homOfLE_ι])
  have hcomp : f ≫ openRestrictionMap B S hS X hX x U W' =
      openRestrictionMap B S hS X hX x U W := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    dsimp [f, f₁, ObjectProperty.homMk, openRestrictionMap, openRestrictionScheme]
    change f₀ ≫ W'.ι = W.ι
    rw [Scheme.homOfLE_ι]
  refine ⟨f, ?_, ?_⟩
  · change yoneda.map f ≫
      (yoneda.map (openRestrictionMap B S hS X hX x U W') ≫ U.toSpace) =
      yoneda.map (openRestrictionMap B S hS X hX x U W) ≫ U.toSpace
    calc
      yoneda.map f ≫ (yoneda.map (openRestrictionMap B S hS X hX x U W') ≫ U.toSpace) =
          (yoneda.map f ≫ yoneda.map (openRestrictionMap B S hS X hX x U W')) ≫ U.toSpace :=
            (Category.assoc _ _ _).symm
      _ = yoneda.map (f ≫ openRestrictionMap B S hS X hX x U W') ≫ U.toSpace := by
        rw [← yoneda.map_comp]
      _ = yoneda.map (openRestrictionMap B S hS X hX x U W) ≫ U.toSpace := by rw [hcomp]
  change f₀ (⟨U.point, hW⟩ : W.toScheme) = ⟨U.point, hW'⟩
  rw [Scheme.homOfLE_apply']

/-- The morphism of elementary étale neighborhoods which a morphism of neighborhoods induces
between the restrictions to a pointed open subscheme and to its preimage. -/
def openRestrictionNeighborhoodMap {V U : ElementaryEtaleNeighborhood B S hS X hX x} (f : V ⟶ U)
    (W : U.scheme.left.1.Opens) (hW : U.point ∈ W) :
    openRestrictionNeighborhood B S hS X hX x V
      (f.hom.left.1 ⁻¹ᵁ W) (by
        change f.hom.left.1 V.point ∈ W
        rw [f.map_point]
        exact hW) ⟶ openRestrictionNeighborhood B S hS X hX x U W hW := by
  let Wv : V.scheme.left.1.Opens := f.hom.left.1 ⁻¹ᵁ W
  have hWv : V.point ∈ Wv := by
    change f.hom.left.1 V.point ∈ W
    rw [f.map_point]
    exact hW
  let Rv := openRestrictionScheme B S hS X hX x V Wv
  let Ru := openRestrictionScheme B S hS X hX x U W
  let k₀ : Wv.toScheme ⟶ W.toScheme := f.hom.left.1 ∣_ W
  let k₁ : Rv.left ⟶ Ru.left := ObjectProperty.homMk k₀
  have hbase : f.hom.left ≫ U.scheme.hom = V.scheme.hom := f.hom.w
  have hbaseScheme : B.inclusion.map f.hom.left ≫ B.inclusion.map U.scheme.hom =
      B.inclusion.map V.scheme.hom := congrArg B.inclusion.map hbase
  let k : Rv ⟶ Ru := Over.homMk k₁ (by
    apply B.inclusion.map_injective
    dsimp [Rv, Ru, k₁, ObjectProperty.homMk, openRestrictionScheme]
    calc
      k₀ ≫ (W.ι ≫ U.scheme.hom.1) = (k₀ ≫ W.ι) ≫ U.scheme.hom.1 := by rw [Category.assoc]
      _ = (Wv.ι ≫ f.hom.left.1) ≫ U.scheme.hom.1 := by rw [morphismRestrict_ι]
      _ = Wv.ι ≫ (f.hom.left.1 ≫ U.scheme.hom.1) := by rw [Category.assoc]
      _ = Wv.ι ≫ (B.inclusion.map f.hom.left ≫ B.inclusion.map U.scheme.hom) := rfl
      _ = Wv.ι ≫ B.inclusion.map V.scheme.hom := by rw [hbaseScheme]
      _ = _ := rfl)
  have hsquare : k ≫ openRestrictionMap B S hS X hX x U W =
      openRestrictionMap B S hS X hX x V Wv ≫ f.hom := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    dsimp [k, k₁, Rv, Ru, ObjectProperty.homMk, openRestrictionMap, openRestrictionScheme]
    change k₀ ≫ W.ι = Wv.ι ≫ f.hom.left.1
    exact morphismRestrict_ι _ _
  refine ⟨k, ?_, ?_⟩
  · change yoneda.map k ≫ (yoneda.map (openRestrictionMap B S hS X hX x U W) ≫ U.toSpace) =
      yoneda.map (openRestrictionMap B S hS X hX x V Wv) ≫ V.toSpace
    calc
      yoneda.map k ≫ (yoneda.map (openRestrictionMap B S hS X hX x U W) ≫ U.toSpace) =
          (yoneda.map k ≫ yoneda.map (openRestrictionMap B S hS X hX x U W)) ≫ U.toSpace :=
            (Category.assoc _ _ _).symm
      _ = yoneda.map (k ≫ openRestrictionMap B S hS X hX x U W) ≫ U.toSpace := by
        rw [← yoneda.map_comp]
      _ = yoneda.map (openRestrictionMap B S hS X hX x V Wv ≫ f.hom) ≫ U.toSpace := by
        rw [hsquare]
      _ = yoneda.map (openRestrictionMap B S hS X hX x V Wv) ≫ V.toSpace := by
        rw [yoneda.map_comp, Category.assoc, f.«over»]
  change k₀ (⟨V.point, hWv⟩ : Wv.toScheme) = ⟨U.point, hW⟩
  apply Subtype.ext
  dsimp [Wv] at hWv ⊢
  change ((f.hom.left.1 ∣_ W) (⟨V.point, hWv⟩ : (f.hom.left.1 ⁻¹ᵁ W).toScheme)).1 = U.point
  exact (morphismRestrict_base_coe f.hom.left.1 W ⟨V.point, hWv⟩).trans f.map_point

/-! ### Sections over a pointed open subscheme and the henselian local ring -/

/-- The homomorphism from the sections over a pointed open subscheme of an elementary étale
neighborhood into the henselian local ring: the canonical homomorphism of that open subscheme,
viewed as an elementary étale neighborhood. -/
def openRestrictionSectionHom (hDecent : IsDecentSpace B S hS X)
    (U : ElementaryEtaleNeighborhood B S hS X hX x)
    (W : U.scheme.left.1.Opens) (hW : U.point ∈ W) :
    U.scheme.left.1.presheaf.obj (op W) →+*
      (henselianLocalRing B S hS X hX x hDecent : Type (u + 1)) :=
  (sectionHom B S hS X hX x hDecent
      (op (openRestrictionNeighborhood B S hS X hX x U W hW))).comp
    W.topIso.commRingCatIsoToRingEquiv.symm.toRingHom

/-- Restriction of sections along an inclusion of open subschemes agrees with the comparison of
the global sections of the corresponding open subschemes. -/
theorem opens_topIso_homOfLE (T : Scheme.{u}) {W W' : T.Opens} (h : W ≤ W') :
    T.presheaf.map (homOfLE h).op ≫ W.topIso.inv =
      W'.topIso.inv ≫ (T.homOfLE h).appTop := by
  have hn := (Scheme.restrictFunctorΓ (X := T)).hom.naturality (homOfLE h).op
  change (T.homOfLE h).appTop ≫ W.topIso.hom =
    W'.topIso.hom ≫ T.presheaf.map (homOfLE h).op at hn
  apply (cancel_mono W.topIso.hom).1
  calc
    _ = T.presheaf.map (homOfLE h).op := by
      rw [Category.assoc, W.topIso.inv_hom_id, Category.comp_id]
    _ = W'.topIso.inv ≫ (W'.topIso.hom ≫ T.presheaf.map (homOfLE h).op) := by
      rw [← Category.assoc, W'.topIso.inv_hom_id, Category.id_comp]
    _ = W'.topIso.inv ≫ ((T.homOfLE h).appTop ≫ W.topIso.hom) := by rw [hn.symm]
    _ = W'.topIso.inv ≫ (T.homOfLE h).appTop ≫ W.topIso.hom := rfl

/-- Sections of two neighborhoods related by the restriction along a morphism of neighborhoods
have the same image in the henselian local ring. -/
private theorem sectionHom_eq_of_map_eq (hDecent : IsDecentSpace B S hS X)
    {V U : ElementaryEtaleNeighborhood B S hS X hX x} (f : V ⟶ U)
    {a : (globalSections B S hS X hX x).obj (op U)} {b : (globalSections B S hS X hX x).obj (op V)}
    (h : (globalSections B S hS X hX x).map (op f) a = b) :
    sectionHom B S hS X hX x hDecent (op V) b = sectionHom B S hS X hX x hDecent (op U) a :=
  h ▸ sectionHom_naturality B S hS X hX x hDecent (op f) a

/-- Restricting a section to a smaller pointed open subscheme does not change its image in the
henselian local ring. -/
theorem openRestrictionSectionHom_naturality (hDecent : IsDecentSpace B S hS X)
    (U : ElementaryEtaleNeighborhood B S hS X hX x)
    {W W' : U.scheme.left.1.Opens} (hWW' : W ≤ W') (hW : U.point ∈ W) (hW' : U.point ∈ W')
    (s : U.scheme.left.1.presheaf.obj (op W')) :
    openRestrictionSectionHom B S hS X hX x hDecent U W hW
        (U.scheme.left.1.presheaf.map (homOfLE hWW').op s) =
      openRestrictionSectionHom B S hS X hX x hDecent U W' hW' s := by
  let f := openRestrictionNeighborhoodHom B S hS X hX x U hWW' hW hW'
  unfold openRestrictionSectionHom
  refine sectionHom_eq_of_map_eq B S hS X hX x hDecent f ?_
  let f₀ : W.toScheme ⟶ W'.toScheme := U.scheme.left.1.homOfLE hWW'
  change f₀.appTop.hom (W'.topIso.inv.hom s) =
    W.topIso.inv.hom ((U.scheme.left.1.presheaf.map (homOfLE hWW').op).hom s)
  exact (congrArg (fun k ↦ k s) (opens_topIso_homOfLE U.scheme.left.1 hWW')).symm

/-- Pulling a section back along a morphism of elementary étale neighborhoods does not change
its image in the henselian local ring. -/
theorem openRestrictionSectionHom_map (hDecent : IsDecentSpace B S hS X)
    {V U : ElementaryEtaleNeighborhood B S hS X hX x} (f : V ⟶ U)
    (W : U.scheme.left.1.Opens) (hW : U.point ∈ W)
    (s : U.scheme.left.1.presheaf.obj (op W)) :
    openRestrictionSectionHom B S hS X hX x hDecent V (f.hom.left.1 ⁻¹ᵁ W)
        (by change f.hom.left.1 V.point ∈ W; rw [f.map_point]; exact hW)
        (f.hom.left.1.app W s) =
      openRestrictionSectionHom B S hS X hX x hDecent U W hW s := by
  let Wv : V.scheme.left.1.Opens := f.hom.left.1 ⁻¹ᵁ W
  have hWv : V.point ∈ Wv := by
    show f.hom.left.1 V.point ∈ W
    rw [f.map_point]
    exact hW
  let fr : Wv.toScheme ⟶ W.toScheme := f.hom.left.1 ∣_ W
  have hApp : Wv.topIso.inv.hom (f.hom.left.1.app W s) = fr.appTop (W.topIso.inv.hom s) := by
    have hsquare := (arrowResLEAppIso f.hom.left.1 W Wv le_rfl).hom.w
    have hsquare' : W.topIso.hom ≫ f.hom.left.1.appLE W Wv le_rfl =
        (f.hom.left.1.resLE W Wv le_rfl).appTop ≫ Wv.topIso.hom := hsquare
    have hU : W.topIso.hom ≫ W.topIso.inv = 𝟙 _ := Iso.hom_inv_id _
    have hV : Wv.topIso.hom ≫ Wv.topIso.inv = 𝟙 _ := Iso.hom_inv_id _
    have hcomp : f.hom.left.1.appLE W Wv le_rfl ≫ Wv.topIso.inv =
        W.topIso.inv ≫ (f.hom.left.1.resLE W Wv le_rfl).appTop := by
      apply (cancel_epi W.topIso.hom).1
      calc
        W.topIso.hom ≫ (f.hom.left.1.appLE W Wv le_rfl ≫ Wv.topIso.inv) =
            (W.topIso.hom ≫ f.hom.left.1.appLE W Wv le_rfl) ≫ Wv.topIso.inv := by
              rw [Category.assoc]
        _ = ((f.hom.left.1.resLE W Wv le_rfl).appTop ≫ Wv.topIso.hom) ≫ Wv.topIso.inv := by
          rw [hsquare']
        _ = (f.hom.left.1.resLE W Wv le_rfl).appTop := by
          rw [Category.assoc, hV, Category.comp_id]
        _ = (W.topIso.hom ≫ W.topIso.inv) ≫ (f.hom.left.1.resLE W Wv le_rfl).appTop := by
          rw [hU, Category.id_comp]
    have happ : f.hom.left.1.app W = f.hom.left.1.appLE W Wv le_rfl := by
      simpa [Wv] using (Scheme.Hom.app_eq_appLE f.hom.left.1 (U := W))
    have hfr : fr = f.hom.left.1.resLE W Wv le_rfl :=
      (Scheme.Hom.resLE_eq_morphismRestrict f.hom.left.1 (U := W)).symm
    have hcomp' : f.hom.left.1.app W ≫ Wv.topIso.inv = W.topIso.inv ≫ fr.appTop := by
      rw [happ, hfr]
      exact hcomp
    exact congrArg (fun k ↦ k s) hcomp'
  unfold openRestrictionSectionHom
  exact sectionHom_eq_of_map_eq B S hS X hX x hDecent
    (openRestrictionNeighborhoodMap B S hS X hX x f W hW) hApp.symm

/-- The diagram of sections over the pointed open subschemes of an elementary étale
neighborhood, whose colimit is the local ring at the distinguished point. -/
def openNhdsSections (U : ElementaryEtaleNeighborhood B S hS X hX x) :
    (TopologicalSpace.OpenNhds U.point)ᵒᵖ ⥤ CommRingCat.{u} :=
  (TopologicalSpace.OpenNhds.inclusion U.point).op ⋙ U.scheme.left.1.presheaf

/-- The homomorphisms into the henselian local ring attached to the pointed open subschemes of
an elementary étale neighborhood are compatible with restriction. -/
theorem openRestrictionSectionHom_compatible (hDecent : IsDecentSpace B S hS X)
    (U : ElementaryEtaleNeighborhood B S hS X hX x)
    {j j' : (TopologicalSpace.OpenNhds U.point)ᵒᵖ} (f : j ⟶ j')
    (a : (openNhdsSections B S hS X hX x U).obj j) :
    openRestrictionSectionHom B S hS X hX x hDecent U j'.unop.1 j'.unop.2
        ((openNhdsSections B S hS X hX x U).map f a) =
      openRestrictionSectionHom B S hS X hX x hDecent U j.unop.1 j.unop.2 a :=
  openRestrictionSectionHom_naturality B S hS X hX x hDecent U f.unop.le j'.unop.2 j.unop.2 a

/-- The comparison of the local ring of an elementary étale neighborhood at its distinguished
point with the presentation of that colimit as a quotient of a prequotient. -/
def openNhdsSectionsColimitIso (U : ElementaryEtaleNeighborhood B S hS X hX x) :
    colimit (openNhdsSections B S hS X hX x U) ≅
      CommRingCat.Colimits.colimit (openNhdsSections B S hS X hX x U) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit (openNhdsSections B S hS X hX x U))
    (CommRingCat.Colimits.colimitIsColimit (openNhdsSections B S hS X hX x U))

/-- **Stacks 0EMY.** The canonical homomorphism from the local ring of an elementary étale
neighborhood at its distinguished point into the henselian local ring of the algebraic space. -/
@[stacks 0EMY "the canonical map from the stalk of an elementary étale neighbourhood"]
def stalkToHenselianLocalRing (hDecent : IsDecentSpace B S hS X)
    (U : ElementaryEtaleNeighborhood B S hS X hX x) :
    U.scheme.left.1.presheaf.stalk U.point →+*
      (henselianLocalRing B S hS X hX x hDecent : Type (u + 1)) :=
  (descColimit (openNhdsSections B S hS X hX x U)
      (fun j ↦ openRestrictionSectionHom B S hS X hX x hDecent U j.unop.1 j.unop.2)
      (fun f a ↦ openRestrictionSectionHom_compatible B S hS X hX x hDecent U f a)).comp
    (openNhdsSectionsColimitIso B S hS X hX x U).commRingCatIsoToRingEquiv.toRingHom

/-- The algebra structure on the henselian local ring over the local ring of an elementary étale
neighborhood at its distinguished point. -/
abbrev stalkAlgebra (hDecent : IsDecentSpace B S hS X)
    (U : ElementaryEtaleNeighborhood B S hS X hX x) :
    Algebra (U.scheme.left.1.presheaf.stalk U.point)
      (henselianLocalRing B S hS X hX x hDecent : Type (u + 1)) :=
  (stalkToHenselianLocalRing B S hS X hX x hDecent U).toAlgebra

/-- **Stacks 0EMY.** The canonical homomorphism sends the germ of a section over a pointed open
subscheme to the canonical image of that section in the henselian local ring. -/
@[stacks 0EMY "the canonical map on germs over a pointed open"]
theorem stalkToHenselianLocalRing_openGerm (hDecent : IsDecentSpace B S hS X)
    (U : ElementaryEtaleNeighborhood B S hS X hX x)
    (W : U.scheme.left.1.Opens) (hW : U.point ∈ W)
    (s : U.scheme.left.1.presheaf.obj (op W)) :
    stalkToHenselianLocalRing B S hS X hX x hDecent U
        (U.scheme.left.1.presheaf.germ W U.point hW s) =
      openRestrictionSectionHom B S hS X hX x hDecent U W hW s := by
  have hι : colimit.ι (openNhdsSections B S hS X hX x U)
        (op (⟨W, hW⟩ : TopologicalSpace.OpenNhds U.point)) ≫
      (openNhdsSectionsColimitIso B S hS X hX x U).hom =
      CommRingCat.Colimits.coconeMorphism (openNhdsSections B S hS X hX x U)
        (op (⟨W, hW⟩ : TopologicalSpace.OpenNhds U.point)) :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _
  exact congrArg
    (descColimit (openNhdsSections B S hS X hX x U)
      (fun j ↦ openRestrictionSectionHom B S hS X hX x hDecent U j.unop.1 j.unop.2)
      (fun f a ↦ openRestrictionSectionHom_compatible B S hS X hX x hDecent U f a))
    (ConcreteCategory.congr_hom hι s)

/-- The elementary étale neighborhood obtained by restricting a neighborhood to its whole scheme
maps to the neighborhood itself. -/
def openRestrictionNeighborhoodToOriginal (U : ElementaryEtaleNeighborhood B S hS X hX x) :
    openRestrictionNeighborhood B S hS X hX x U ⊤ (by simp) ⟶ U :=
  ⟨openRestrictionMap B S hS X hX x U ⊤, rfl, rfl⟩

/-- Over the whole scheme of an elementary étale neighborhood the homomorphism of
`AlgebraicGeometry.Space.openRestrictionSectionHom` is the canonical homomorphism of global
sections. -/
theorem openRestrictionSectionHom_top (hDecent : IsDecentSpace B S hS X)
    (U : ElementaryEtaleNeighborhood B S hS X hX x)
    (s : U.scheme.left.1.presheaf.obj (op ⊤)) :
    openRestrictionSectionHom B S hS X hX x hDecent U ⊤ (by simp) s =
      sectionHom B S hS X hX x hDecent (op U) s := by
  refine sectionHom_eq_of_map_eq B S hS X hX x hDecent
    (openRestrictionNeighborhoodToOriginal B S hS X hX x U) ?_
  change (⊤ : U.scheme.left.1.Opens).ι.appTop s = (⊤ : U.scheme.left.1.Opens).topIso.inv s
  simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv]
  congr 2

/-- The canonical homomorphism sends the germ of a global section of the scheme of a neighborhood
to the canonical image of that section in the henselian local ring. -/
private theorem stalkToHenselianLocalRing_germ_top (hDecent : IsDecentSpace B S hS X)
    (U : ElementaryEtaleNeighborhood B S hS X hX x) (s : U.scheme.left.1.presheaf.obj (op ⊤)) :
    stalkToHenselianLocalRing B S hS X hX x hDecent U
        (U.scheme.left.1.presheaf.germ ⊤ U.point (Set.mem_univ _) s) =
      sectionHom B S hS X hX x hDecent (op U) s :=
  (stalkToHenselianLocalRing_openGerm B S hS X hX x hDecent U ⊤ (Set.mem_univ _) s).trans
    (openRestrictionSectionHom_top B S hS X hX x hDecent U s)

/-- The germ of a section at the distinguished point, transported along the equality of the
points, is the germ of the same section at the image point. -/
private theorem stalkMap_stalkCongr_germ {Y T : Scheme.{u}} (f : Y ⟶ T) (y : Y) (t : T)
    (h : f y = t) (W : T.Opens) (hW : t ∈ W) (hmem : f y ∈ W) (s : T.presheaf.obj (op W)) :
    f.stalkMap y ((T.presheaf.stalkCongr (.of_eq h.symm)).hom.hom (T.presheaf.germ W t hW s)) =
      f.stalkMap y (T.presheaf.germ W (f y) hmem s) := by
  have hpoint : f y ⤳ t := by simpa only [h] using specializes_refl t
  rw [TopCat.Presheaf.stalkCongr_hom]
  congr 1
  simpa only [ConcreteCategory.comp_apply] using
    ConcreteCategory.congr_hom (T.presheaf.germ_stalkSpecializes hW hpoint) s

/-- **Stacks 0EMY.** The canonical homomorphisms out of the local rings of the elementary étale
neighborhoods are compatible with every morphism of neighborhoods. -/
@[stacks 0EMY "naturality of the canonical map in the neighbourhood"]
theorem stalkToHenselianLocalRing_naturality (hDecent : IsDecentSpace B S hS X)
    {V U : ElementaryEtaleNeighborhood B S hS X hX x} (f : V ⟶ U) :
    (stalkToHenselianLocalRing B S hS X hX x hDecent V).comp
        (neighborhoodStalkMap B S hS X hX x f).hom =
      stalkToHenselianLocalRing B S hS X hX x hDecent U := by
  ext z
  obtain ⟨W, hW, s, rfl⟩ := U.scheme.left.1.presheaf.exists_germ_eq z
  let Wv := f.hom.left.1 ⁻¹ᵁ W
  have hWv : V.point ∈ Wv := by
    show f.hom.left.1 V.point ∈ W
    rw [f.map_point]
    exact hW
  have hstalk : neighborhoodStalkMap B S hS X hX x f
      (U.scheme.left.1.presheaf.germ W U.point hW s) =
        V.scheme.left.1.presheaf.germ Wv V.point hWv (f.hom.left.1.app W s) := by
    have hmem : f.hom.left.1 V.point ∈ W := by rw [f.map_point]; exact hW
    calc
      _ = f.hom.left.1.stalkMap V.point
          (U.scheme.left.1.presheaf.germ W (f.hom.left.1 V.point) hmem s) :=
            stalkMap_stalkCongr_germ f.hom.left.1 V.point U.point f.map_point W hW hmem s
      _ = V.scheme.left.1.presheaf.germ Wv V.point hWv (f.hom.left.1.app W s) :=
            Scheme.Hom.germ_stalkMap_apply (f := f.hom.left.1) W V.point hmem s
  rw [RingHom.comp_apply, hstalk,
    stalkToHenselianLocalRing_openGerm B S hS X hX x hDecent V Wv hWv,
    stalkToHenselianLocalRing_openGerm B S hS X hX x hDecent U W hW]
  exact openRestrictionSectionHom_map B S hS X hX x hDecent f W hW s

/-- **Stacks 0EMY.** A global section of a refinement whose induced map of local rings is an
isomorphism has the canonical image of that section in the henselian local ring; this describes
the canonical homomorphism on germs over every pointed open subneighborhood. -/
theorem stalkToHenselianLocalRing_germ (hDecent : IsDecentSpace B S hS X)
    (U V : ElementaryEtaleNeighborhood B S hS X hX x) (f : V ⟶ U)
    [IsIso (neighborhoodStalkMap B S hS X hX x f)]
    (s : V.scheme.left.1.presheaf.obj (op ⊤)) :
    stalkToHenselianLocalRing B S hS X hX x hDecent U
        ((inv (neighborhoodStalkMap B S hS X hX x f)).hom
          ((V.scheme.left.1.presheaf.germ ⊤ V.point (Set.mem_univ _)).hom s)) =
      sectionHom B S hS X hX x hDecent (op V) s := by
  let g := (V.scheme.left.1.presheaf.germ ⊤ V.point (Set.mem_univ _)).hom s
  have h := congrArg (fun φ : _ →+* _ ↦ φ ((inv (neighborhoodStalkMap B S hS X hX x f)).hom g))
    (stalkToHenselianLocalRing_naturality B S hS X hX x hDecent f)
  rw [RingHom.comp_apply] at h
  rw [← h, show (neighborhoodStalkMap B S hS X hX x f).hom
      ((inv (neighborhoodStalkMap B S hS X hX x f)).hom g) = g from
      congrArg (fun q : CommRingCat.Hom _ _ ↦ q.hom g)
        (IsIso.inv_hom_id (neighborhoodStalkMap B S hS X hX x f))]
  exact stalkToHenselianLocalRing_germ_top B S hS X hX x hDecent V s

/-! ### The henselian local ring is a local ring -/

/-- **Stacks 0EMY.** The henselian local ring of a decent algebraic space at a point is a local
ring. -/
@[stacks 0EMY "O^h is a local ring"]
theorem henselianLocalRing_isLocalRing (hDecent : IsDecentSpace B S hS X) :
    IsLocalRing (henselianLocalRing B S hS X hX x hDecent : Type (u + 1)) := by
  have hCofiltered : IsCofiltered (ElementaryEtaleNeighborhood B S hS X hX x) :=
    ElementaryEtaleNeighborhood.isCofiltered_of_nonempty B S hS X hX x
      ⟨(exists_affine_elementaryEtaleNeighborhood' B S hS hX hDecent x).choose⟩
  let := hCofiltered
  let : IsFiltered (ElementaryEtaleNeighborhood B S hS X hX x)ᵒᵖ :=
    (isFiltered_op_iff_isCofiltered _).2 hCofiltered
  let : PreservesFilteredColimitsOfSize.{u, u + 1} (forget CommRingCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u + 1} _
  let D := liftedGlobalSections B S hS X hX x
  let H := henselianLocalRing B S hS X hX x hDecent
  have hnontrivial (j : (ElementaryEtaleNeighborhood B S hS X hX x)ᵒᵖ) :
      Nontrivial (D.obj j) :=
    (((j.unop.scheme.left.1.presheaf.germ ⊤ j.unop.point (Set.mem_univ _)).hom).comp
      ULift.ringEquiv.toRingHom).domain_nontrivial
  let : Nontrivial H := by
    apply nontrivial_of_ne (0 : H) 1
    intro h
    let j : (ElementaryEtaleNeighborhood B S hS X hX x)ᵒᵖ := IsFiltered.nonempty.some
    have heq : (colimit.ι D j).hom 0 = (colimit.ι D j).hom 1 := by simpa using h
    obtain ⟨k, _, _, hk⟩ := Concrete.isColimit_exists_of_rep_eq D (colimit.isColimit D) 0 1 heq
    let := hnontrivial k
    simp only [map_zero, map_one] at hk
    exact (zero_ne_one : (0 : D.obj k) ≠ 1) hk
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  obtain ⟨j, s, hs⟩ := Concrete.isColimit_exists_rep D (colimit.isColimit D) a
  change (colimit.ι D j).hom s = a at hs
  rw [← hs]
  let g := j.unop.scheme.left.1.presheaf.germ ⊤ j.unop.point (Set.mem_univ _)
  have hg : stalkToHenselianLocalRing B S hS X hX x hDecent j.unop (g s.down) =
      (colimit.ι D j).hom s :=
    stalkToHenselianLocalRing_germ_top B S hS X hX x hDecent j.unop s.down
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (g s.down) with hu | hu
  · exact Or.inl (hg ▸ hu.map (stalkToHenselianLocalRing B S hS X hX x hDecent j.unop))
  · right
    simpa only [map_sub, map_one, hg] using
      hu.map (stalkToHenselianLocalRing B S hS X hX x hDecent j.unop)

/-! ### Comparison with the elementary étale neighborhoods of the neighborhood scheme -/

/-- Refinements equipped with a map to a fixed elementary étale neighborhood are initial among
all elementary étale neighborhoods. -/
theorem overForget_initial (U : ElementaryEtaleNeighborhood B S hS X hX x) :
    Functor.Initial (Over.forget U) := by
  let := ElementaryEtaleNeighborhood.isCofiltered_of_nonempty B S hS X hX x ⟨U⟩
  infer_instance

/-- A morphism of elementary étale neighborhoods induces an isomorphism of the residue fields at
the distinguished points. -/
theorem neighborhood_residueFieldMap_isIso
    {V U : ElementaryEtaleNeighborhood B S hS X hX x} (f : V ⟶ U) :
    IsIso ((U.scheme.left.1.residueFieldCongr f.map_point).inv ≫
      f.hom.left.1.residueFieldMap V.point) := by
  have : Mono (yonedaEquiv.symm (neighborhoodFieldPoint B S hS X hX x V).value) := by
    rw [neighborhoodFieldPoint_morphism]
    exact V.mono_residueField
  have : Mono (yonedaEquiv.symm (neighborhoodFieldPoint B S hS X hX x U).value) := by
    rw [neighborhoodFieldPoint_morphism]
    exact U.mono_residueField
  obtain ⟨e, he⟩ := iso_of_mono_of_point_eq B S hS X hX
    (neighborhoodFieldPoint B S hS X hX x V) (neighborhoodFieldPoint B S hS X hX x U)
    ((neighborhoodFieldPoint_class B S hS X hX x V).trans
      (neighborhoodFieldPoint_class B S hS X hX x U).symm)
  have hmid : yoneda.map (neighborhoodResidueFieldMap B S hS X hX x f) ≫
      (yoneda.map (residueFieldMap B S hS U.scheme U.point U.residueField_contained) ≫
        U.toSpace) =
      yoneda.map (residueFieldMap B S hS V.scheme V.point V.residueField_contained) ≫
        V.toSpace := by
    rw [← Category.assoc, ← yoneda.map_comp, neighborhoodResidueFieldMap_comp,
      yoneda.map_comp, Category.assoc, f.«over»]
  have hk : yoneda.map (neighborhoodResidueFieldMap B S hS X hX x f) ≫
      yonedaEquiv.symm (neighborhoodFieldPoint B S hS X hX x U).value =
      yonedaEquiv.symm (neighborhoodFieldPoint B S hS X hX x V).value :=
    ((congrArg (fun t ↦ yoneda.map (neighborhoodResidueFieldMap B S hS X hX x f) ≫ t)
        (neighborhoodFieldPoint_morphism B S hS X hX x U)).trans hmid).trans
      (neighborhoodFieldPoint_morphism B S hS X hX x V).symm
  have he' : yoneda.map e.hom ≫
      yonedaEquiv.symm (neighborhoodFieldPoint B S hS X hX x U).value =
      yonedaEquiv.symm (neighborhoodFieldPoint B S hS X hX x V).value := by
    apply yonedaEquiv.injective
    simpa only [← yonedaEquiv_naturality, Equiv.apply_symm_apply] using he
  have hke : neighborhoodResidueFieldMap B S hS X hX x f = e.hom := by
    apply yoneda.map_injective
    exact (cancel_mono (yonedaEquiv.symm
      (neighborhoodFieldPoint B S hS X hX x U).value)).1 (hk.trans he'.symm)
  have : IsIso (neighborhoodResidueFieldMap B S hS X hX x f) := hke ▸ e.isIso_hom
  have : IsIso ((BigFppfOver.toScheme B S hS).map
    (neighborhoodResidueFieldMap B S hS X hX x f)) := inferInstance
  have : IsIso (Scheme.Spec.map
      ((U.scheme.left.1.residueFieldCongr f.map_point).inv ≫
        f.hom.left.1.residueFieldMap V.point).op) :=
    inferInstanceAs (IsIso ((BigFppfOver.toScheme B S hS).map
      (neighborhoodResidueFieldMap B S hS X hX x f)))
  have : IsIso ((U.scheme.left.1.residueFieldCongr f.map_point).inv ≫
      f.hom.left.1.residueFieldMap V.point).op :=
    isIso_of_reflects_iso _ Scheme.Spec
  exact isIso_of_op _

/-- The underlying morphism of schemes of a morphism of elementary étale neighborhoods is
étale. -/
theorem neighborhood_etale {V U : ElementaryEtaleNeighborhood B S hS X hX x} (f : V ⟶ U) :
    Etale f.hom.left.1 := by
  let P := MorphismProperty.inverseImage (@Etale.{u}) (BigFppfOver.toScheme B S hS)
  let : P.RespectsIso := by
    apply MorphismProperty.RespectsIso.mk
    · intro A C D e g hg
      show Etale ((BigFppfOver.toScheme B S hS).map (e.hom ≫ g))
      rw [Functor.map_comp]
      let : Etale ((BigFppfOver.toScheme B S hS).map g) := hg
      infer_instance
    · intro A C D e g hg
      show Etale ((BigFppfOver.toScheme B S hS).map (g ≫ e.hom))
      rw [Functor.map_comp]
      let : Etale ((BigFppfOver.toScheme B S hS).map g) := hg
      infer_instance
  have hid (W : BigFppfOver B S hS) : P.presheaf (𝟙 (yoneda.obj W)) := by
    apply MorphismProperty.relative.of_exists
    intro Y g
    refine ⟨Y, g, 𝟙 Y, ?_, ?_⟩
    · simpa using IsPullback.of_id_snd (f := g)
    · show Etale ((BigFppfOver.toScheme B S hS).map (𝟙 Y))
      infer_instance
  exact etale_of_etale_charts B S hS V.toSpace U.toSpace
    (by simpa using V.etale_toSpace V.scheme (𝟙 _) (hid V.scheme))
    (by simpa using U.etale_toSpace U.scheme (𝟙 _) (hid U.scheme))
    f.hom f.«over»

/-- An elementary étale neighborhood of the algebraic space equipped with a morphism to a fixed
neighborhood `U` is an elementary étale neighborhood of the scheme of `U` at its distinguished
point. -/
def overToSchemeNeighborhood (U : ElementaryEtaleNeighborhood B S hS X hX x) :
    Over U ⥤ _root_.AlgebraicGeometry.ElementaryEtaleNeighborhood U.scheme.left.1 U.point where
  obj V := ⟨{
      scheme := V.left.scheme.left.1
      point := V.left.point
      toBase := V.hom.hom.left.1
      etale_toBase := neighborhood_etale B S hS X hX x V.hom
      map_point := V.hom.map_point },
    neighborhood_residueFieldMap_isIso B S hS X hX x V.hom⟩
  map f := ObjectProperty.homMk {
    hom := f.left.hom.left.1
    «over» := congrArg (fun g ↦ g.hom.left.1) f.w
    map_point := f.left.map_point }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Passing from a neighborhood over `U` to a scheme neighborhood of the distinguished point of
`U` is faithful. -/
theorem overToSchemeNeighborhood_faithful (U : ElementaryEtaleNeighborhood B S hS X hX x) :
    (overToSchemeNeighborhood B S hS X hX x U).Faithful where
  map_injective h := by
    apply Over.OverMorphism.ext
    apply ElementaryEtaleNeighborhood.Hom.ext
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    exact congrArg (fun g ↦ g.hom.hom) h

/-- Passing from a neighborhood over `U` to a scheme neighborhood of the distinguished point of
`U` is full. -/
theorem overToSchemeNeighborhood_full (U : ElementaryEtaleNeighborhood B S hS X hX x) :
    (overToSchemeNeighborhood B S hS X hX x U).Full where
  map_surjective {V W} f := by
    let g₀ : V.left.scheme.left ⟶ W.left.scheme.left := ⟨f.hom.hom⟩
    have hg₀ : g₀ ≫ W.hom.hom.left = V.hom.hom.left := B.inclusion.map_injective f.hom.«over»
    let g : V.left.scheme ⟶ W.left.scheme := Over.homMk g₀ (by
      rw [← W.hom.hom.w, ← Category.assoc, hg₀, V.hom.hom.w])
    have hg : g ≫ W.hom.hom = V.hom.hom := Over.OverMorphism.ext hg₀
    let k : V.left ⟶ W.left := {
      hom := g
      «over» := by rw [← W.hom.«over», ← Category.assoc, ← yoneda.map_comp, hg, V.hom.«over»]
      map_point := f.hom.map_point }
    refine ⟨Over.homMk k ?_, ?_⟩
    · exact ElementaryEtaleNeighborhood.Hom.ext hg
    · rfl

/-- A scheme locally of finite type over a base has arbitrarily small affine open
neighborhoods whose size is bounded by the size of the base. -/
theorem exists_affineOpen_size_le {T Y : Scheme.{u}} (f : T ⟶ Y) [LocallyOfFiniteType f]
    (t : T) (O : T.Opens) (ht : t ∈ O) :
    ∃ W : T.Opens, IsAffineOpen W ∧ t ∈ W ∧ W ≤ O ∧ W.toScheme.size ≤ Y.size := by
  obtain ⟨V, hV, htV, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y) (x := f t) (U := ⊤) (Set.mem_univ _)
  obtain ⟨W, hW, htW, hWV⟩ := exists_isAffineOpen_mem_and_subset
    (X := T) (x := t) (U := O ⊓ f ⁻¹ᵁ V) ⟨ht, htV⟩
  let : IsAffine V.toScheme := hV
  let : IsAffine W.toScheme := hW
  refine ⟨W, hW, htW, fun a ha ↦ (hWV ha).1, ?_⟩
  exact (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact
      (f.resLE V W (fun a ha ↦ (hWV ha).2))).trans (Scheme.size_coe_opens_le Y V)

/-- A scheme neighborhood of the distinguished point of `U` which is small enough to belong to
the chosen big site is an elementary étale neighborhood of the algebraic space over `U`. -/
def schemeNeighborhoodToOver (U : ElementaryEtaleNeighborhood B S hS X hX x)
    (N : _root_.AlgebraicGeometry.ElementaryEtaleNeighborhood U.scheme.left.1 U.point)
    (hN : B.Contains N.obj.scheme) : Over U := by
  let : IsIso N.obj.residueFieldMap := N.property
  have hres : B.Contains (Spec (.of (N.obj.scheme.residueField N.obj.point))) := by
    change (Spec (.of (N.obj.scheme.residueField N.obj.point))).size < B.cutoff
    exact (Scheme.size_congr (asIso (Spec.map N.obj.residueFieldMap))).le.trans_lt
      U.residueField_contained
  let V : BigFppfOver B S hS :=
    Over.mk (⟨N.obj.toBase ≫ U.scheme.hom.1⟩ : B.obj hN ⟶ B.obj hS)
  let f : V ⟶ U.scheme := Over.homMk ⟨N.obj.toBase⟩ rfl
  let k := pointedResidueFieldMap B S hS f N.obj.point U.point N.obj.map_point
    hres U.residueField_contained
  have : IsIso ((BigFppfOver.toScheme B S hS).map k) := by
    change IsIso (Spec.map N.obj.residueFieldMap)
    infer_instance
  have : IsIso k := isIso_of_reflects_iso k (BigFppfOver.toScheme B S hS)
  let rV := residueFieldMap B S hS V N.obj.point hres
  let rU := residueFieldMap B S hS U.scheme U.point U.residueField_contained
  have hk : k ≫ rU = rV ≫ f :=
    pointedResidueFieldMap_comp B S hS f N.obj.point U.point N.obj.map_point
      hres U.residueField_contained
  let p : FieldValuedPoint B S hS X :=
    ⟨N.obj.scheme.residueField N.obj.point, hres,
      N.obj.scheme.fromSpecResidueField N.obj.point ≫ V.hom.1,
      yonedaEquiv (yoneda.map rV ≫ yoneda.map f ≫ U.toSpace)⟩
  have hp : p.class B S hS X = x := by
    apply Eq.trans _ (neighborhoodFieldPoint_class B S hS X hX x U)
    apply FieldValuedPoint.class_eq_class_of_hasCommonExtension
    refine ⟨p, FieldValuedPoint.dominates_refl B S hS X p, k, ?_⟩
    change X.map k.op (yonedaEquiv (yoneda.map rU ≫ U.toSpace)) =
      yonedaEquiv (yoneda.map rV ≫ yoneda.map f ≫ U.toSpace)
    rw [yonedaEquiv_naturality, ← Category.assoc, ← yoneda.map_comp, hk, yoneda.map_comp,
      Category.assoc]
  let M : ElementaryEtaleNeighborhood B S hS X hX x := {
    scheme := V
    point := N.obj.point
    residueField_contained := hres
    toSpace := yoneda.map f ≫ U.toSpace
    etale_toSpace := isEtale_comp B S hS
      (etale_yoneda B S hS f N.obj.etale_toBase) U.etale_toSpace
    map_point := hp
    mono_residueField := by
      change Mono (yoneda.map rV ≫ yoneda.map f ≫ U.toSpace)
      rw [← Category.assoc, ← yoneda.map_comp, ← hk, yoneda.map_comp, Category.assoc]
      let : Mono (yoneda.map rU ≫ U.toSpace) := U.mono_residueField
      infer_instance }
  exact Over.mk (show M ⟶ U from ⟨f, rfl, N.obj.map_point⟩)

/-- Elementary étale neighborhoods of the algebraic space over `U` are initial among the
elementary étale neighborhoods of the scheme of `U` at its distinguished point. -/
theorem overToSchemeNeighborhood_initial (U : ElementaryEtaleNeighborhood B S hS X hX x) :
    (overToSchemeNeighborhood B S hS X hX x U).Initial := by
  let F := overToSchemeNeighborhood B S hS X hX x U
  let : F.Full := overToSchemeNeighborhood_full B S hS X hX x U
  let : F.Faithful := overToSchemeNeighborhood_faithful B S hS X hX x U
  let : IsCofiltered
      (_root_.AlgebraicGeometry.ElementaryEtaleNeighborhood U.scheme.left.1 U.point) :=
    isCofiltered_of_isFiltered_op _
  apply Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful
  intro N
  obtain ⟨W, _, hW, _, hsize⟩ := exists_affineOpen_size_le N.obj.toBase N.obj.point ⊤
    (Set.mem_univ _)
  let M : _root_.AlgebraicGeometry.ElementaryEtaleNeighborhood U.scheme.left.1 U.point :=
    ⟨N.obj.comp (EtaleNeighborhood.ofEtale W.ι (⟨N.obj.point, hW⟩ : W.toScheme)),
      N.property.comp (EtaleNeighborhood.isElementary_ofEtale_of_isOpenImmersion W.ι
        (⟨N.obj.point, hW⟩ : W.toScheme))⟩
  exact ⟨schemeNeighborhoodToOver B S hS X hX x U M (hsize.trans_lt U.scheme.left.2),
    ⟨ObjectProperty.homMk ⟨W.ι, rfl, rfl⟩⟩⟩

/-! ### The henselization statement -/

/-- A henselization may be transported along an algebra isomorphism. -/
theorem isHenselization_of_algEquiv {R : Type u} {A : Type v} {C : Type w}
    [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A] [Algebra R A]
    [CommRing C] [IsLocalRing C] [Algebra R C]
    [IsLocalRing.IsHenselization R (IsLocalRing.ResidueField R) A]
    (e : A ≃ₐ[R] C) : IsLocalRing.IsHenselization R (IsLocalRing.ResidueField R) C := by
  have : IsLocalHom e.toRingHom := IsLocalHom.of_surjective _ e.surjective
  have := IsLocalRing.IsHenselization.henselian R (IsLocalRing.ResidueField R) (Rh := A)
  refine ⟨HenselianLocalRing.of_ringEquiv e.toRingEquiv,
    StacksDraft.indEtale_of_equiv (RingEquiv.refl R) e.toRingEquiv e.commutes
      (IsLocalRing.IsHenselization.ind_etale (R := R) (L := IsLocalRing.ResidueField R)), ?_⟩
  obtain ⟨q, hq⟩ := IsLocalRing.IsHenselization.exists_residueFieldEquiv
    (R := R) (L := IsLocalRing.ResidueField R) (Rh := A)
  refine ⟨q.trans (IsLocalRing.ResidueField.mapEquiv e.toRingEquiv), fun r ↦ ?_⟩
  show IsLocalRing.ResidueField.mapEquiv e.toRingEquiv
    (q (algebraMap _ _ (IsLocalRing.residue R r))) = _
  rw [hq]
  show IsLocalRing.ResidueField.map e.toRingHom
    (IsLocalRing.residue A (algebraMap R A r)) = _
  rw [IsLocalRing.ResidueField.map_residue]
  exact congrArg (IsLocalRing.residue C) (e.commutes r)

/-- The germ of a section over an open subscheme, computed in that open subscheme, is the germ
in the ambient scheme followed by the comparison of local rings. -/
theorem opens_germ_stalkMap {T : Scheme.{u}} (W : T.Opens) (p : W.toScheme) :
    W.topIso.inv ≫ W.toScheme.presheaf.germ ⊤ p trivial =
      T.presheaf.germ W (W.ι p) p.2 ≫ W.ι.stalkMap p :=
  calc W.topIso.inv ≫ W.toScheme.presheaf.germ ⊤ p trivial
      = W.topIso.inv ≫ (T.presheaf.germ (W.ι ''ᵁ ⊤) (W.ι p) ⟨p, trivial, rfl⟩ ≫
          (W.stalkIso p).inv) :=
        congrArg (fun t ↦ W.topIso.inv ≫ t)
          (Scheme.Opens.germ_stalkIso_inv W ⊤ p trivial).symm
    _ = (W.topIso.inv ≫ T.presheaf.germ (W.ι ''ᵁ ⊤) (W.ι p) ⟨p, trivial, rfl⟩) ≫
          (W.stalkIso p).inv := (Category.assoc _ _ _).symm
    _ = T.presheaf.germ W (W.ι p) p.2 ≫ (W.stalkIso p).inv :=
        congrArg (fun t ↦ t ≫ (W.stalkIso p).inv)
          (T.presheaf.germ_res (eqToHom W.ι_image_top) (W.ι p) ⟨p, trivial, rfl⟩)
    _ = T.presheaf.germ W (W.ι p) p.2 ≫ W.ι.stalkMap p :=
        congrArg (fun t ↦ T.presheaf.germ W (W.ι p) p.2 ≫ t) (Scheme.Opens.stalkIso_inv W p)

/-- A henselization of the local ring of an elementary étale neighborhood at its distinguished
point is isomorphic to the henselian local ring of the algebraic space, compatibly with the
canonical homomorphisms out of the global sections of the neighborhoods over it. -/
theorem exists_henselianLocalRing_equiv (hDecent : IsDecentSpace B S hS X)
    (U : ElementaryEtaleNeighborhood B S hS X hX x) (Rh : Type u) [CommRing Rh]
    (ι : _root_.AlgebraicGeometry.globalSections U.scheme.left.1 U.point ⟶
      (Functor.const _).obj (CommRingCat.of Rh))
    (hc : IsColimit (Cocone.mk _ ι)) :
    ∃ e : Rh ≃+* henselianLocalRing B S hS X hX x hDecent,
      ∀ (V : Over U) (s : V.left.scheme.left.1.presheaf.obj (op ⊤)),
        e ((ι.app (op ((overToSchemeNeighborhood B S hS X hX x U).obj V))).hom s) =
          sectionHom B S hS X hX x hDecent (op V.left) s := by
  let F := overToSchemeNeighborhood B S hS X hX x U
  let G := Over.forget U
  let D := liftedGlobalSections B S hS X hX x
  let L := AlgebraicGeometry.commRingULiftFunctor.{u, u + 1}
  let : InitiallySmall.{u}
      (_root_.AlgebraicGeometry.ElementaryEtaleNeighborhood U.scheme.left.1 U.point) :=
    Stacks.EtaleCohomology.initiallySmall_elementaryEtaleNeighborhood _ _
  let : PreservesFilteredColimitsOfSize.{u, u} L := uliftCommRingFunctor_preservesFilteredColimits
  let : PreservesColimitsOfShape
      (_root_.AlgebraicGeometry.ElementaryEtaleNeighborhood U.scheme.left.1 U.point)ᵒᵖ L :=
    FinallySmall.preservesColimitsOfShape_of_isFiltered.{u} _ _
  let : F.Initial := overToSchemeNeighborhood_initial B S hS X hX x U
  let : G.Initial := overForget_initial B S hS X hX x U
  let c₁ := (L.mapCocone (Cocone.mk _ ι)).whisker F.op
  let c₂ := (colimit.cocone D).whisker G.op
  have hc₁ : IsColimit c₁ :=
    (Functor.Final.isColimitWhiskerEquiv F.op (L.mapCocone (Cocone.mk _ ι))).symm
      (isColimitOfPreserves L hc)
  have hc₂ : IsColimit c₂ :=
    (Functor.Final.isColimitWhiskerEquiv G.op (colimit.cocone D)).symm (colimit.isColimit D)
  refine ⟨ULift.ringEquiv.symm.trans
    (hc₁.coconePointUniqueUpToIso hc₂).commRingCatIsoToRingEquiv, ?_⟩
  intro V s
  exact ConcreteCategory.congr_hom
    (hc₁.comp_coconePointUniqueUpToIso_hom hc₂ (op V)) (ULift.up s)

/-- **Stacks 0EMY.** The henselian local ring of a decent algebraic space at a point is a
henselization of the local ring of any elementary étale neighborhood at its distinguished
point. -/
@[stacks 0EMY "O^h is a henselization of the stalk", sga "3 X 4.4" "Case 2°"]
theorem henselianLocalRing_isHenselization (hDecent : IsDecentSpace B S hS X)
    (U : ElementaryEtaleNeighborhood B S hS X hX x) :
    letI := henselianLocalRing_isLocalRing B S hS X hX x hDecent
    letI := stalkAlgebra B S hS X hX x hDecent U
    IsLocalRing.IsHenselization (U.scheme.left.1.presheaf.stalk U.point)
      (IsLocalRing.ResidueField (U.scheme.left.1.presheaf.stalk U.point))
      (henselianLocalRing B S hS X hX x hDecent : Type (u + 1)) := by
  let := henselianLocalRing_isLocalRing B S hS X hX x hDecent
  let := stalkAlgebra B S hS X hX x hDecent U
  obtain ⟨Rh, _, _, _, hRh⟩ := IsLocalRing.exists_isHenselization_residueField
    (U.scheme.left.1.presheaf.stalk U.point)
  let := hRh
  obtain ⟨ι, _, hι, _, ⟨hc⟩⟩ := _root_.AlgebraicGeometry.isColimit_globalSections
    U.scheme.left.1 U.point Rh
  obtain ⟨e, he⟩ := exists_henselianLocalRing_equiv B S hS X hX x hDecent U Rh ι hc
  apply isHenselization_of_algEquiv (A := Rh)
  refine { e with commutes' := ?_ }
  intro r
  obtain ⟨W, hW, s, rfl⟩ := U.scheme.left.1.presheaf.exists_germ_eq r
  let V := openRestrictionNeighborhood B S hS X hX x U W hW
  let f : V ⟶ U := ⟨openRestrictionMap B S hS X hX x U W, rfl, rfl⟩
  let N := (overToSchemeNeighborhood B S hS X hX x U).obj (Over.mk f)
  let a := (Scheme.Opens.topIso (X := U.scheme.left.1) W).inv.hom s
  obtain ⟨g, _, hg, hleg⟩ := hι (op N)
  have hmem : N.obj.toBase N.obj.point ∈ W := hW
  have hstalk : _root_.AlgebraicGeometry.stalkMap U.scheme.left.1 U.point N
      (U.scheme.left.1.presheaf.germ W U.point hW s) =
      V.scheme.left.1.presheaf.germ ⊤ V.point trivial a := by
    have h1 : _root_.AlgebraicGeometry.stalkMap U.scheme.left.1 U.point N
        (U.scheme.left.1.presheaf.germ W U.point hW s) =
        N.obj.toBase.stalkMap N.obj.point
          (U.scheme.left.1.presheaf.germ W (N.obj.toBase N.obj.point) hmem s) := by
      exact stalkMap_stalkCongr_germ N.obj.toBase N.obj.point U.point N.obj.map_point W hW hmem s
    exact h1.trans (ConcreteCategory.congr_hom (opens_germ_stalkMap W ⟨U.point, hW⟩) s).symm
  have halg : algebraMap (U.scheme.left.1.presheaf.stalk U.point) Rh
      (U.scheme.left.1.presheaf.germ W U.point hW s) = (ι.app (op N)).hom a := by
    rw [← hg, RingHom.comp_apply, hstalk, hleg]
    rfl
  show e (algebraMap _ Rh _) = stalkToHenselianLocalRing B S hS X hX x hDecent U _
  rw [halg]
  exact (he (Over.mk f) a).trans
    (stalkToHenselianLocalRing_openGerm B S hS X hX x hDecent U W hW s).symm

/-- **Stacks 0EMY.** The canonical homomorphism from the local ring of an elementary étale
neighborhood into the henselian local ring is local. -/
theorem isLocalHom_stalkToHenselianLocalRing (hDecent : IsDecentSpace B S hS X)
    (U : ElementaryEtaleNeighborhood B S hS X hX x) :
    letI := henselianLocalRing_isLocalRing B S hS X hX x hDecent
    IsLocalHom (stalkToHenselianLocalRing B S hS X hX x hDecent U) := by
  let := henselianLocalRing_isLocalRing B S hS X hX x hDecent
  let := stalkAlgebra B S hS X hX x hDecent U
  let := henselianLocalRing_isHenselization B S hS X hX x hDecent U
  exact IsLocalRing.IsHenselization.isLocalHom
    (R := U.scheme.left.1.presheaf.stalk U.point)
    (L := IsLocalRing.ResidueField (U.scheme.left.1.presheaf.stalk U.point))

/-- **Stacks 0EMY.** The maximal ideal of the henselian local ring is generated by the image of
the maximal ideal of the local ring of any elementary étale neighborhood. -/
@[stacks 0EMY "the maximal ideal of O^h"]
theorem map_maximalIdeal_stalkToHenselianLocalRing (hDecent : IsDecentSpace B S hS X)
    (U : ElementaryEtaleNeighborhood B S hS X hX x) :
    letI := henselianLocalRing_isLocalRing B S hS X hX x hDecent
    (IsLocalRing.maximalIdeal (U.scheme.left.1.presheaf.stalk U.point)).map
        (stalkToHenselianLocalRing B S hS X hX x hDecent U) =
      IsLocalRing.maximalIdeal (henselianLocalRing B S hS X hX x hDecent : Type (u + 1)) := by
  let := henselianLocalRing_isLocalRing B S hS X hX x hDecent
  let := stalkAlgebra B S hS X hX x hDecent U
  let := henselianLocalRing_isHenselization B S hS X hX x hDecent U
  exact IsLocalRing.IsHenselization.map_maximalIdeal
    (R := U.scheme.left.1.presheaf.stalk U.point)
    (L := IsLocalRing.ResidueField (U.scheme.left.1.presheaf.stalk U.point))

/-- **Stacks 0EMY.** The residue field of the henselian local ring is the residue field of the
local ring of any elementary étale neighborhood at its distinguished point. -/
@[stacks 0EMY "the residue field of O^h"]
theorem exists_residueFieldEquiv_henselianLocalRing (hDecent : IsDecentSpace B S hS X)
    (U : ElementaryEtaleNeighborhood B S hS X hX x) :
    letI := henselianLocalRing_isLocalRing B S hS X hX x hDecent
    ∃ e : IsLocalRing.ResidueField (U.scheme.left.1.presheaf.stalk U.point) ≃+*
        IsLocalRing.ResidueField
          (henselianLocalRing B S hS X hX x hDecent : Type (u + 1)),
      ∀ r : U.scheme.left.1.presheaf.stalk U.point,
        e (IsLocalRing.residue _ r) =
          IsLocalRing.residue _ (stalkToHenselianLocalRing B S hS X hX x hDecent U r) := by
  let := henselianLocalRing_isLocalRing B S hS X hX x hDecent
  let := stalkAlgebra B S hS X hX x hDecent U
  let := henselianLocalRing_isHenselization B S hS X hX x hDecent U
  obtain ⟨e, he⟩ := IsLocalRing.IsHenselization.exists_residueFieldEquiv
    (R := U.scheme.left.1.presheaf.stalk U.point)
    (L := IsLocalRing.ResidueField (U.scheme.left.1.presheaf.stalk U.point))
    (Rh := (henselianLocalRing B S hS X hX x hDecent : Type (u + 1)))
  exact ⟨e, fun r ↦ he r⟩

end AlgebraicGeometry.Space

end
