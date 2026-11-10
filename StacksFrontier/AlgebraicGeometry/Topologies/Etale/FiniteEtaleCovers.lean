module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites

/-!
# The finite objects of the small étale site are the finite étale covers

Let `B` be a big étale site and `X` an object of `B`. The objects of the small étale site of `X`
whose structure morphism is finite form a full subcategory, and sending such an object to its
structure morphism identifies that subcategory with the category `FÉt_X` of schemes finite étale
over `X`.

The functor is fully faithful because the inclusions of the small étale site into the big étale
category over `X`, of the big étale category into schemes, and of `FÉt_X` into schemes are all
fully faithful. It is essentially surjective because a finite étale cover is of finite type and
quasi-compact over `X`, hence small enough to belong to the big site.

## Main definitions

* `AlgebraicGeometry.finiteSmallEtaleObjects`: the objects of the small étale site with finite
  structure morphism.
* `AlgebraicGeometry.finiteEtaleFromSmallEtale`: the comparison functor to `FÉt_X`.
* `AlgebraicGeometry.finiteEtaleSiteEquivalence`: the resulting equivalence of categories.

## References

* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- The objects of the small étale site of `X` whose structure morphism is finite. -/
abbrev finiteSmallEtaleObjects : ObjectProperty (SmallEtale B X.1 X.2) :=
  fun U ↦ IsFinite (B.inclusion.map U.obj.hom)

/-- The canonical functor from the small étale site of `X` to schemes over `X`. -/
abbrev smallEtaleToOver : SmallEtale B X.1 X.2 ⥤ Over X.1 :=
  SmallEtale.inclusion B X.1 X.2 ⋙ Over.post B.inclusion

/-- The comparison functor from the finite objects of the small étale site of `X` to the
category of schemes finite étale over `X`. -/
def finiteEtaleFromSmallEtale :
    (finiteSmallEtaleObjects B X).FullSubcategory ⥤ FiniteEtaleOver X.1 where
  obj U := MorphismProperty.Over.mk ⊤ ((smallEtaleToOver B X).obj U.1).hom ⟨U.2, U.1.property⟩
  map f := MorphismProperty.Over.Hom.mk (P := finiteEtale) (Q := ⊤)
    (X := X.1) ((smallEtaleToOver B X).map f.1) trivial
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

variable {B X}

/-- A scheme finite étale over `X` is small enough to be an object of the big étale site: the
structure morphism is of finite type and quasi-compact. -/
theorem finiteEtale_size_lt (Y : FiniteEtaleOver X.1) : Y.left.size < B.cutoff := by
  have : IsFinite Y.hom := Y.prop.1
  exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact Y.hom X.property

/-- A scheme finite étale over `X`, read as an object of the small étale site of `X`. -/
def smallEtaleOfFiniteEtale (Y : FiniteEtaleOver X.1) : SmallEtale B X.1 X.2 := by
  have : IsFinite Y.hom := Y.prop.1
  let U := B.obj Y.left (finiteEtale_size_lt Y)
  let hf : B.inclusion.obj U ⟶ B.inclusion.obj (B.obj X.1 X.2) := Y.hom
  let f : U ⟶ B.obj X.1 X.2 := B.inclusion.preimage hf
  refine ⟨Over.mk f, ?_⟩
  change Etale (B.inclusion.map f)
  rw [B.inclusion.map_preimage hf]
  change Etale Y.hom
  exact Y.prop.2

/-- The structure morphism of `AlgebraicGeometry.smallEtaleOfFiniteEtale` is the given finite
étale morphism. -/
theorem smallEtaleOfFiniteEtale_hom (Y : FiniteEtaleOver X.1) :
    B.inclusion.map (smallEtaleOfFiniteEtale (B := B) Y).obj.hom = Y.hom := by
  dsimp [smallEtaleOfFiniteEtale]
  let U := B.obj Y.left (finiteEtale_size_lt (B := B) Y)
  let hf : B.inclusion.obj U ⟶ B.inclusion.obj (B.obj X.1 X.2) := Y.hom
  change B.inclusion.map (B.inclusion.preimage hf) = hf
  exact B.inclusion.map_preimage hf

/-- A scheme finite étale over `X`, read as a finite object of the small étale site of `X`. -/
def finiteEtaleSiteObject (Y : FiniteEtaleOver X.1) :
    (finiteSmallEtaleObjects B X).FullSubcategory :=
  ⟨smallEtaleOfFiniteEtale Y, by
    change IsFinite (B.inclusion.map (smallEtaleOfFiniteEtale (B := B) Y).obj.hom)
    rw [smallEtaleOfFiniteEtale_hom]
    exact Y.prop.1⟩

/-- `AlgebraicGeometry.finiteEtaleSiteObject` is a section of the comparison functor. -/
def finiteEtaleFromSmallEtaleObjIso (Y : FiniteEtaleOver X.1) :
    (finiteEtaleFromSmallEtale B X).obj (finiteEtaleSiteObject Y) ≅ Y := by
  refine MorphismProperty.Over.isoMk (P := finiteEtale) (Iso.refl Y.left) ?_
  change 𝟙 Y.left ≫ Y.hom = B.inclusion.map (smallEtaleOfFiniteEtale (B := B) Y).obj.hom
  rw [smallEtaleOfFiniteEtale_hom]
  simp

variable (B X)

/-- The comparison functor is fully faithful: it is so after composing with the faithful
forgetful functor to schemes over `X`, where it is a composite of fully faithful inclusions. -/
def finiteEtaleFromSmallEtaleFullyFaithful :
    (finiteEtaleFromSmallEtale B X).FullyFaithful := by
  let hSite : (finiteSmallEtaleObjects B X).ι.FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful _
  let hInclusion : B.inclusion.FullyFaithful := (schemeSizeBelow B.cutoff).fullyFaithfulι
  let hSmall : (SmallEtale.inclusion B X.1 X.2).FullyFaithful :=
    (BigEtaleOver.IsEtaleOver B X.1 X.2).fullyFaithfulι
  let hPost : (Over.post (X := B.obj X.1 X.2) B.inclusion).FullyFaithful :=
    Functor.FullyFaithful.over (B.obj X.1 X.2) B.inclusion hInclusion
  let hSmallToOver : (smallEtaleToOver B X).FullyFaithful := by
    change ((SmallEtale.inclusion B X.1 X.2) ⋙
      Over.post (X := B.obj X.1 X.2) B.inclusion).FullyFaithful
    exact hSmall.comp hPost
  let G := MorphismProperty.Over.forget finiteEtale ⊤ X.1
  have hcomp : finiteEtaleFromSmallEtale B X ⋙ G ≅
      (finiteSmallEtaleObjects B X).ι ⋙ smallEtaleToOver B X := by
    refine NatIso.ofComponents (fun _ ↦ Iso.refl _) ?_
    intro U V f
    ext
    rfl
  have hff : ((finiteSmallEtaleObjects B X).ι ⋙ smallEtaleToOver B X).FullyFaithful :=
    hSite.comp hSmallToOver
  have hcompFF : (finiteEtaleFromSmallEtale B X ⋙ G).FullyFaithful := hff.ofIso hcomp.symm
  have : G.Faithful := inferInstance
  exact Functor.FullyFaithful.ofCompFaithful (F := finiteEtaleFromSmallEtale B X) (G := G) hcompFF

/-- The comparison functor is essentially surjective. -/
theorem finiteEtaleFromSmallEtaleEssSurj : (finiteEtaleFromSmallEtale B X).EssSurj where
  mem_essImage Y := ⟨finiteEtaleSiteObject Y, ⟨finiteEtaleFromSmallEtaleObjIso Y⟩⟩

/-- **The finite objects of the small étale site of `X` are the finite étale covers of `X`.** -/
def finiteEtaleSiteEquivalence :
    (finiteSmallEtaleObjects B X).FullSubcategory ≌ FiniteEtaleOver X.1 := by
  have : (finiteEtaleFromSmallEtale B X).IsEquivalence :=
    let h := finiteEtaleFromSmallEtaleFullyFaithful B X
    ⟨h.faithful, h.full, finiteEtaleFromSmallEtaleEssSurj B X⟩
  exact (finiteEtaleFromSmallEtale B X).asEquivalence

end AlgebraicGeometry

end
