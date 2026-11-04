module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcGermSectionsSheaf
import StacksCore.Tactic.StacksAttribute

/-!
# Naturality of the comparison morphisms of the quasi-compact site

The category `LC_α` of Hausdorff, locally quasi-compact spaces carries two topologies, the
quasi-compact one and the coarser Zariski one, and for an object `X` the identity functor on the
slice compares them: `ε_X : Sh(LC_qc/X) → Sh(LC_Zar/X)` has direct image the inclusion of
quasi-compact sheaves into Zariski sheaves and inverse image quasi-compact sheafification.
Composing with the Zariski comparison `π_X : Sh(LC_Zar/X) → Sh(X)` to sheaves on the underlying
space gives `a_X = π_X ∘ ε_X`.

This file proves, for a morphism `f : X ⟶ Y` of the site, that the two squares of topoi

```
Sh(LC_qc/X) --f_qc--> Sh(LC_qc/Y)       Sh(LC_qc/X) --f_qc--> Sh(LC_qc/Y)
     | ε_X                 | ε_Y             | a_X                  | a_Y
Sh(LC_Zar/X) -f_Zar-> Sh(LC_Zar/Y)          Sh(X) -----f-----> Sh(Y)
```

commute, and that for a proper `f` the canonical base-change map
`a_Y^{-1} ∘ f_* ⟶ f_{qc,*} ∘ a_X^{-1}` is an isomorphism.

Both squares come from one observation: the direct images compose *strictly*, because `ε_*`
leaves the underlying presheaf unchanged. Commutativity of the left square on inverse images is
then uniqueness of left adjoints, and the right square is the left square composed with the
Zariski square `zariskiComparisonSquareIso` of Stacks 0DCU.

The proper direct image clause is deduced from clause (7a) of Stacks 0DCU, as in the source. The
base-change map for `a` is the vertical composite of the base-change map for `π`, which is an
isomorphism for proper `f`, and the base-change map for `ε`. The latter is a composite of the
quasi-compact sheafification unit, the strict identification of direct images, and a counit of
the change-of-topology adjunction; the counit is always invertible because `ε_*` is fully
faithful, and the unit is invertible at `π_X^{-1}F` because `π_X^{-1}F` is already a sheaf for
the quasi-compact topology, which is Stacks 09X3.

## Main definitions

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.qcComparisonMorphism`: the
  change-of-topology morphism of topoi `ε_X`.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.zariskiComparisonMorphism` and
  `qcTopologicalMorphism`: the Zariski comparison `π_X` and the composite `a_X = π_X ∘ ε_X`, as
  morphisms of topoi.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.qcSliceMorphism`: the morphism of
  quasi-compact slice topoi `f_qc` induced by `f`.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.qcTopologicalBaseChangeMap`: the canonical
  base-change map `a_Y^{-1} ∘ f_* ⟶ f_{qc,*} ∘ a_X^{-1}`, defined for every `f`.

## Main results

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.topologyChangeSquareIso`: the
  change-of-topology square commutes.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.qcTopologicalComparisonSquareIso`: the
  square comparing the quasi-compact slice topoi with sheaves on the underlying spaces commutes.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.qcTopologicalProperDirectImageIso`: for a
  proper `f`, direct image of sheaves of sets along the underlying continuous map commutes with
  inverse image along `a_X`, `a_Y`.

## Implementation notes

The coefficients are types in an arbitrary universe containing the universe `u` of the spaces,
except in the proper direct image clause, where they are `Type u`: that is the universe at which
proper base change for the Zariski comparison, `isIso_zariskiComparisonBaseChangeMap`, and the
sections formula of Stacks 09X3 are available, both of them being proved through the germ model
of an inverse image of sheaves on a topological space.

`mateEquiv_qcTopologicalBaseChangeMap` records that `qcTopologicalBaseChangeMap` is the mate of
the composite of the two squares on direct images, which is what makes it *the* base-change map
of the right-hand square rather than one of several maps between those functors.

## References

* [Stacks Project, Tag 0D92](https://stacks.math.columbia.edu/tag/0D92)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
* [Stacks Project, Tag 09X3](https://stacks.math.columbia.edu/tag/09X3)
-/

@[expose] public noncomputable section

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

/-- The component at an object of the inverse mates correspondence: the mate of
`β : R₁ ⋙ G ⟶ H ⋙ R₂` is the unit of the first adjunction, followed by `β` at the image of the
object, followed by the counit of the second adjunction. -/
theorem mateEquiv_symm_app {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
    {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (β : TwoSquare R₁ H G R₂) (c : C) :
    ((mateEquiv adj₁ adj₂).symm β).app c =
      L₂.map (G.map (adj₁.unit.app c)) ≫ L₂.map (β.app (L₁.obj c)) ≫
        adj₂.counit.app (H.obj (L₁.obj c)) := by
  simp [mateEquiv]

end CategoryTheory

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w t

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)

/-- A quasi-compact sheaf on a localized site is a Zariski sheaf. -/
@[stacks 09WY "ε_X comes from the identity functor of LC/X, which is continuous"]
theorem isContinuous_id_zariski_qc (X : S.category) :
    (Functor.id (Over X)).IsContinuous (S.zariskiTopology.over X)
      (S.qcSite.grothendieckTopology.over X) where
  op_comp_isSheaf_of_types F :=
    (isSheaf_iff_isSheaf_of_type _ _).1 (F.property.of_le (S.zariskiTopology_over_le_qc X))

/-- Direct image for the change-of-topology morphism `ε_X : Sh(LC_qc/X) → Sh(LC_Zar/X)`. -/
def qcDirectImage (X : S.category) :
    Sheaf (S.qcSite.grothendieckTopology.over X) (Type (max u t)) ⥤
      Sheaf (S.zariskiTopology.over X) (Type (max u t)) :=
  ObjectProperty.ιOfLE fun _ hF ↦ hF.of_le (S.zariskiTopology_over_le_qc X)

/-- The change-of-topology direct image is full: it is a full subcategory inclusion. -/
instance qcDirectImage_full (X : S.category) : (qcDirectImage.{u, w, t} S X).Full :=
  ObjectProperty.full_ιOfLE _

/-- The change-of-topology direct image is faithful: it is a full subcategory inclusion. -/
instance qcDirectImage_faithful (X : S.category) : (qcDirectImage.{u, w, t} S X).Faithful :=
  ObjectProperty.faithful_ιOfLE _

/-- Inverse image for the change-of-topology morphism, i.e. quasi-compact sheafification. -/
def qcInverseImage (X : S.category) :
    Sheaf (S.zariskiTopology.over X) (Type (max u t)) ⥤
      Sheaf (S.qcSite.grothendieckTopology.over X) (Type (max u t)) :=
  letI : HasSheafify (S.qcSite.grothendieckTopology.over X) (Type (max u t)) :=
    hasSheafify_qcTopology_over.{u, w, t} S X
  sheafToPresheaf (S.zariskiTopology.over X) (Type (max u t)) ⋙
    presheafToSheaf (S.qcSite.grothendieckTopology.over X) (Type (max u t))

/-- The change-of-topology adjunction. -/
def qcComparisonAdjunction (X : S.category) :
    qcInverseImage.{u, w, t} S X ⊣ qcDirectImage.{u, w, t} S X :=
  letI : HasSheafify (S.qcSite.grothendieckTopology.over X) (Type (max u t)) :=
    hasSheafify_qcTopology_over.{u, w, t} S X
  (sheafificationAdjunction (S.qcSite.grothendieckTopology.over X)
      (Type (max u t))).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf (S.zariskiTopology.over X) (Type (max u t)))
    (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

/-- The unit of the change-of-topology adjunction is invertible at a Zariski sheaf which is
already a sheaf for the quasi-compact topology: such a sheaf is in the essential image of the
fully faithful change-of-topology direct image. -/
theorem isIso_qcComparisonAdjunction_unit_app (X : S.category)
    (G : Sheaf (S.zariskiTopology.over X) (Type (max u t)))
    (hG : Presheaf.IsSheaf (S.qcSite.grothendieckTopology.over X) G.obj) :
    IsIso ((qcComparisonAdjunction.{u, w, t} S X).unit.app G) :=
  (Adjunction.isIso_unit_app_iff_mem_essImage
    (qcComparisonAdjunction.{u, w, t} S X)).2 ⟨⟨G.obj, hG⟩, ⟨Iso.refl _⟩⟩

/-- The change-of-topology morphism of topoi `ε_X : Sh(LC_qc/X) → Sh(LC_Zar/X)`. -/
@[stacks 09WY "the induced morphism ε_X : LC_qc/X → LC_Zar/X"]
def qcComparisonMorphism (X : S.category) :
    MorphismOfTopoi
      (Sheaf (S.qcSite.grothendieckTopology.over X) (Type (max u t)))
      (Sheaf (S.zariskiTopology.over X) (Type (max u t))) :=
  letI : HasSheafify (S.qcSite.grothendieckTopology.over X) (Type (max u t)) :=
    hasSheafify_qcTopology_over.{u, w, t} S X
  { pushforward := qcDirectImage.{u, w, t} S X
    inverseImage := qcInverseImage.{u, w, t} S X
    adj := qcComparisonAdjunction.{u, w, t} S X
    preservesFiniteLimits := by
      dsimp only [qcInverseImage]
      exact comp_preservesFiniteLimits _ _ }

/-- The Zariski comparison morphism of topoi `π_X : Sh(LC_Zar/X) → Sh(X)`. -/
@[stacks 09WY "the morphism π_X : Sh(LC_Zar/X) → Sh(X)"]
def zariskiComparisonMorphism (X : S.category) :
    MorphismOfTopoi
      (Sheaf (S.zariskiTopology.over X) (Type (max u t)))
      (Sheaf (Opens.grothendieckTopology X.obj) (Type (max u t))) where
  pushforward := S.comparisonDirectImage X (Type (max u t))
  inverseImage := comparisonInverseImage.{u, w, t} S X
  adj := comparisonAdjunction.{u, w, t} S X
  preservesFiniteLimits := comparisonInverseImage_preservesFiniteLimits.{u, w, t} S X

/-- The comparison morphism of topoi `a_X : Sh(LC_qc/X) → Sh(X)`, defined as the composite
`π_X ∘ ε_X`. -/
@[stacks 09WY "the morphism of topoi a_X = π_X ∘ ε_X : Sh(LC_qc/X) → Sh(X)"]
def qcTopologicalMorphism (X : S.category) :
    MorphismOfTopoi
      (Sheaf (S.qcSite.grothendieckTopology.over X) (Type (max u t)))
      (Sheaf (Opens.grothendieckTopology X.obj) (Type (max u t))) :=
  (zariskiComparisonMorphism.{u, w, t} S X).comp (qcComparisonMorphism.{u, w, t} S X)

/-- Inverse image along `a_X`: the Zariski comparison inverse image followed by quasi-compact
sheafification. -/
abbrev qcTopologicalInverseImage (X : S.category) :
    Sheaf (Opens.grothendieckTopology X.obj) (Type (max u t)) ⥤
      Sheaf (S.qcSite.grothendieckTopology.over X) (Type (max u t)) :=
  comparisonInverseImage.{u, w, t} S X ⋙ qcInverseImage.{u, w, t} S X

/-- `a_X^{-1}` is the composite of the two inverse images, by definition of `a_X`. -/
theorem qcTopologicalMorphism_inverseImage (X : S.category) :
    (qcTopologicalMorphism.{u, w, t} S X).inverseImage =
      qcTopologicalInverseImage.{u, w, t} S X := rfl

/-- `a_{X,*}` is the composite of the two direct images, by definition of `a_X`. -/
theorem qcTopologicalMorphism_pushforward (X : S.category) :
    (qcTopologicalMorphism.{u, w, t} S X).pushforward =
      qcDirectImage.{u, w, t} S X ⋙ S.comparisonDirectImage X (Type (max u t)) := rfl

section Slice

variable {X Y : S.category} (f : X ⟶ Y)

/-- Inverse image along `f` on the localized quasi-compact sites. -/
abbrev qcSliceInverseImage :
    Sheaf (S.qcSite.grothendieckTopology.over Y) (Type (max u t)) ⥤
      Sheaf (S.qcSite.grothendieckTopology.over X) (Type (max u t)) :=
  (Over.map f).sheafPushforwardContinuous (Type (max u t))
    (S.qcSite.grothendieckTopology.over X) (S.qcSite.grothendieckTopology.over Y)

/-- The morphism of quasi-compact slice topoi induced by `f`. -/
def qcSliceMorphism :
    MorphismOfTopoi
      (Sheaf (S.qcSite.grothendieckTopology.over X) (Type (max u t)))
      (Sheaf (S.qcSite.grothendieckTopology.over Y) (Type (max u t))) :=
  letI := hasPointwiseRightKanExtension_overMap.{u, w, t} S f
  letI := hasLeftKanExtension_overMap.{u, w, t} S f
  letI : HasSheafify (S.qcSite.grothendieckTopology.over Y) (Type (max u t)) :=
    hasSheafify_qcTopology_over.{u, w, t} S Y
  { pushforward := (Over.map f).sheafPushforwardCocontinuous
      (Type (max u t)) (S.qcSite.grothendieckTopology.over X)
      (S.qcSite.grothendieckTopology.over Y)
    inverseImage := qcSliceInverseImage.{u, w, t} S f
    adj := (Over.map f).sheafAdjunctionCocontinuous
      (Type (max u t)) (S.qcSite.grothendieckTopology.over X)
      (S.qcSite.grothendieckTopology.over Y)
    preservesFiniteLimits := inferInstance }

/-- **Stacks 0D92, the change-of-topology square.** The change-of-topology morphisms commute
with the morphisms of slice topoi induced by `f`:
`ε_X^{-1} ∘ f_{Zar}^{-1} ≅ f_{qc}^{-1} ∘ ε_Y^{-1}`.

On direct images the square commutes strictly, because the change-of-topology direct image
leaves the underlying presheaf unchanged; both sides of the square on inverse images are left
adjoints of the two sides of that identity, so the isomorphism is the one supplied by uniqueness
of left adjoints. -/
@[stacks 0D92 "change-of-topology square"]
def topologyChangeSquareIso :
    (zariskiSliceMorphism.{u, w, t} S f).inverseImage ⋙ qcInverseImage.{u, w, t} S X ≅
      qcInverseImage.{u, w, t} S Y ⋙ qcSliceInverseImage.{u, w, t} S f := by
  letI := hasPointwiseRightKanExtension_overMap.{u, w, t} S f
  letI : HasSheafify (S.qcSite.grothendieckTopology.over X) (Type (max u t)) :=
    hasSheafify_qcTopology_over.{u, w, t} S X
  letI : HasSheafify (S.qcSite.grothendieckTopology.over Y) (Type (max u t)) :=
    hasSheafify_qcTopology_over.{u, w, t} S Y
  let adjX := qcComparisonAdjunction.{u, w, t} S X
  let adjY := qcComparisonAdjunction.{u, w, t} S Y
  let adjZar := (Over.map f).sheafAdjunctionCocontinuous (Type (max u t))
    (S.zariskiTopology.over X) (S.zariskiTopology.over Y)
  let adjQc := (Over.map f).sheafAdjunctionCocontinuous (Type (max u t))
    (S.qcSite.grothendieckTopology.over X) (S.qcSite.grothendieckTopology.over Y)
  let rightEq :
      (Over.map f).sheafPushforwardCocontinuous (Type (max u t))
          (S.qcSite.grothendieckTopology.over X)
          (S.qcSite.grothendieckTopology.over Y) ⋙ qcDirectImage.{u, w, t} S Y =
        qcDirectImage.{u, w, t} S X ⋙ (Over.map f).sheafPushforwardCocontinuous
          (Type (max u t)) (S.zariskiTopology.over X) (S.zariskiTopology.over Y) := rfl
  exact (adjZar.comp adjX).leftAdjointUniq
    ((adjY.comp adjQc).ofNatIsoRight (eqToIso rightEq))

/-- **Stacks 0D92, the topological comparison square.** The comparison morphisms
`a_X = π_X ∘ ε_X` to sheaves on the underlying spaces commute with the morphisms of slice topoi
induced by `f`: `a_X^{-1} ∘ g^{-1} ≅ f_{qc}^{-1} ∘ a_Y^{-1}`, where `g` is the underlying
continuous map of `f`.

It is the Zariski square of Stacks 0DCU followed by the change-of-topology square. -/
@[stacks 0D92 "topological comparison square"]
def qcTopologicalComparisonSquareIso :
    (Opens.map ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).sheafPullback
        (Type (max u t))
        (Opens.grothendieckTopology
          ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj Y))
        (Opens.grothendieckTopology
          ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj X)) ⋙
      qcTopologicalInverseImage.{u, w, t} S X ≅
    qcTopologicalInverseImage.{u, w, t} S Y ⋙ qcSliceInverseImage.{u, w, t} S f :=
  Functor.isoWhiskerRight (zariskiComparisonSquareIso.{u, w, t} S f)
      (qcInverseImage.{u, w, t} S X) ≪≫
    Functor.isoWhiskerLeft (comparisonInverseImage.{u, w, t} S Y)
      (topologyChangeSquareIso.{u, w, t} S f)

/-- Direct image along `f` on the localized quasi-compact sites, in the form
`(f_{qc,*}G)(Z/Y) = G(Z ×_Y X / X)`. -/
abbrev qcSliceDirectImage :
    Sheaf (S.qcSite.grothendieckTopology.over X) (Type (max u t)) ⥤
      Sheaf (S.qcSite.grothendieckTopology.over Y) (Type (max u t)) :=
  Functor.sheafPushforwardContinuous (Over.pullback f) (Type (max u t))
    (S.qcSite.grothendieckTopology.over Y) (S.qcSite.grothendieckTopology.over X)

/-- On direct images the change-of-topology square commutes strictly. -/
theorem qcDirectImage_comp_sliceDirectImage :
    qcDirectImage.{u, w, t} S X ⋙ sliceDirectImage S f (Type (max u t)) =
      qcSliceDirectImage.{u, w, t} S f ⋙ qcDirectImage.{u, w, t} S Y := rfl

/-- The canonical base-change map of the change-of-topology morphisms. -/
def topologyChangeBaseChangeMap :
    sliceDirectImage S f (Type (max u t)) ⋙ qcInverseImage.{u, w, t} S Y ⟶
      qcInverseImage.{u, w, t} S X ⋙ qcSliceDirectImage.{u, w, t} S f :=
  (mateEquiv (qcComparisonAdjunction.{u, w, t} S X)
      (qcComparisonAdjunction.{u, w, t} S Y)).symm
    (TwoSquare.mk _ _ _ _ (eqToHom (qcDirectImage_comp_sliceDirectImage.{u, w, t} S f)))

/-- The change-of-topology base-change map is invertible at every Zariski sheaf whose
quasi-compact sheafification unit is invertible: it is a composite of the image of that unit,
an identification of functors, and a counit of the change-of-topology adjunction, which is
invertible because the change-of-topology direct image is fully faithful. -/
theorem isIso_topologyChangeBaseChangeMap_app
    (G : Sheaf (S.zariskiTopology.over X) (Type (max u t)))
    (hG : IsIso ((qcComparisonAdjunction.{u, w, t} S X).unit.app G)) :
    IsIso ((topologyChangeBaseChangeMap.{u, w, t} S f).app G) := by
  rw [topologyChangeBaseChangeMap, mateEquiv_symm_app]
  infer_instance

/-- The canonical base-change map of the comparison morphisms `a_X`, `a_Y` to sheaves on the
underlying spaces: the Zariski base-change map followed by the change-of-topology one. -/
def qcTopologicalBaseChangeMap :
    spaceDirectImage S f (Type (max u t)) ⋙ qcTopologicalInverseImage.{u, w, t} S Y ⟶
      qcTopologicalInverseImage.{u, w, t} S X ⋙ qcSliceDirectImage.{u, w, t} S f :=
  TwoSquare.vComp
    (TwoSquare.mk _ _ _ _ (zariskiComparisonBaseChangeMap.{u, w, t} S f))
    (TwoSquare.mk _ _ _ _ (topologyChangeBaseChangeMap.{u, w, t} S f))

/-- The adjunction of `a_X` is the composite of the adjunctions of `π_X` and `ε_X`. -/
theorem qcTopologicalMorphism_adj (X : S.category) :
    (qcTopologicalMorphism.{u, w, t} S X).adj =
      (comparisonAdjunction.{u, w, t} S X).comp (qcComparisonAdjunction.{u, w, t} S X) := rfl

/-- The base-change map is the mate of the composite of the two direct-image squares, so it is
the canonical base-change map of the square of topoi of the lemma. -/
theorem mateEquiv_qcTopologicalBaseChangeMap :
    mateEquiv ((comparisonAdjunction.{u, w, t} S X).comp (qcComparisonAdjunction.{u, w, t} S X))
        ((comparisonAdjunction.{u, w, t} S Y).comp (qcComparisonAdjunction.{u, w, t} S Y))
        (TwoSquare.vComp
          (TwoSquare.mk _ _ _ _ (zariskiComparisonBaseChangeMap.{u, w, t} S f))
          (TwoSquare.mk _ _ _ _ (topologyChangeBaseChangeMap.{u, w, t} S f))) =
      TwoSquare.hComp
        (TwoSquare.mk _ _ _ _
          (eqToHom (qcDirectImage_comp_sliceDirectImage.{u, w, t} S f)))
        (TwoSquare.mk _ _ _ _
          (zariskiComparisonDirectImageSquareIso S f (Type (max u t))).hom) := by
  rw [mateEquiv_hcomp, topologyChangeBaseChangeMap, Equiv.apply_symm_apply,
    zariskiComparisonBaseChangeMap, mateEquiv_comparisonBaseChangeMap]

/-- **Stacks 09X3.** The Zariski comparison inverse image `π_X^{-1}F` of a sheaf of sets on the
space of `X` is already a sheaf for the quasi-compact topology, being the germ-model sections
presheaf. -/
theorem isSheaf_qc_comparisonInverseImage (X : S.category)
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max u t))) :
    Presheaf.IsSheaf (S.qcSite.grothendieckTopology.over X)
      ((comparisonInverseImage.{u, w, t} S X).obj F).obj :=
  (Presheaf.isSheaf_of_iso_iff (germSectionsPresheafIso S X F)).mpr
    (isSheaf_qc_germSectionsPresheaf S X F)

/-- The change-of-topology base-change map is invertible at every `π_X^{-1}F`, because
`π_X^{-1}F` is already a sheaf for the quasi-compact topology. -/
theorem isIso_whiskerLeft_topologyChangeBaseChangeMap :
    IsIso (Functor.whiskerLeft (comparisonInverseImage.{u, w, u} S X)
      (topologyChangeBaseChangeMap.{u, w, u} S f)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  exact isIso_topologyChangeBaseChangeMap_app S f _
    (isIso_qcComparisonAdjunction_unit_app S X _ (isSheaf_qc_comparisonInverseImage S X F))

/-- For a proper `f` the canonical base-change map of the comparison morphisms to sheaves on the
underlying spaces is an isomorphism. -/
theorem isIso_qcTopologicalBaseChangeMap
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u} ⇑((siteToTop S).map f)) :
    IsIso (qcTopologicalBaseChangeMap.{u, w, u} S f) := by
  have := isIso_zariskiComparisonBaseChangeMap S f hf
  have := isIso_whiskerLeft_topologyChangeBaseChangeMap.{u, w} S f
  dsimp only [qcTopologicalBaseChangeMap, TwoSquare.vComp, TwoSquare.mk]
  infer_instance

/-- **Stacks 0D92, the proper direct image clause.** If the underlying continuous map of
`f : X ⟶ Y` is proper, then direct image of sheaves of sets along it commutes with inverse image
along the comparison morphisms `a_X`, `a_Y` to sheaves on the underlying spaces:
`a_Y^{-1} ∘ f_* = f_{qc,*} ∘ a_X^{-1}`.

This is `qcTopologicalBaseChangeMap` with its invertibility supplied by
`isIso_qcTopologicalBaseChangeMap`. -/
@[stacks 0D92 "proper direct image"]
def qcTopologicalProperDirectImageIso
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u} ⇑((siteToTop S).map f)) :
    spaceDirectImage S f (Type u) ⋙ qcTopologicalInverseImage.{u, w, u} S Y ≅
      qcTopologicalInverseImage.{u, w, u} S X ⋙ qcSliceDirectImage.{u, w, u} S f :=
  have := isIso_qcTopologicalBaseChangeMap.{u, w} S f hf
  asIso (qcTopologicalBaseChangeMap.{u, w, u} S f)

end Slice

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
