module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.SubcategoryStructureSheafLowerShriek
public import StacksFrontier.CategoryTheory.Sites.FullSubcategorySite

/-!
# Full subcategories of a big site closed under the affine line

Let `X` be a scheme and let `C₁ ⊆ C₂` be full subcategories of the big fppf category over `X`,
each carrying the topology inherited from the ambient one, and write `g : Sh(C₁) ⟶ Sh(C₂)` for
the morphism of topoi of the inclusion. If `C₁` contains the base object `X/X` and contains
`U × 𝐀¹/X` whenever it contains `U/X`, then the canonical map `g_!O₁ ⟶ O₂` from the lower shriek
of the restricted structure sheaf is an isomorphism.

Such a `C₁` contains objects isomorphic over `X` to the affine line and to the affine plane over
`X`; the second comes from the identification `𝔸(1; 𝔸(1; X)) ≅ 𝔸(2; X)` of the affine line over
the affine line with the affine plane, made by comparing coordinates.

## Main definitions

* `AlgebraicGeometry.AffineSpace.affinePlaneIso`: the affine line over the affine line over a
  scheme is the affine plane over that scheme.
* `AlgebraicGeometry.AffineSpace.affineSpaceIsoOfBaseIso`: an isomorphism of base schemes induces
  an isomorphism of the affine spaces over them.
* `AlgebraicGeometry.IsClosedUnderAffineLine`: the property of a full subcategory of the big fppf
  category over `X` that it contains the affine line over each of its objects.

## Main results

* `AlgebraicGeometry.exists_mem_isoAffineLine` and
  `AlgebraicGeometry.exists_mem_isoAffinePlane`: a full subcategory containing `X/X` and closed
  under the affine line contains objects isomorphic over `X` to the affine line and to the affine
  plane over `X`.
* `AlgebraicGeometry.isIso_lowerShriekStructureSheafHom_of_isClosedUnderAffineLine`: the
  canonical map `g_!O₁ ⟶ O₂` is an isomorphism as soon as `C₁` contains `X/X` and the affine line
  over each of its objects.

## References

* [Stacks Project, Tag 07AJ](https://stacks.math.columbia.edu/tag/07AJ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe t

/-! ### The affine plane as the affine line over the affine line -/

namespace AffineSpace

variable (S : Scheme.{t})

/-- The comparison of the affine line over the affine line over `S` with the affine plane over
`S`: the two coordinates are the coordinate of the upper affine line and the pullback of the
coordinate of the lower one. -/
noncomputable def planeHom :
    𝔸(PUnit.{t + 1}; 𝔸(PUnit.{t + 1}; S)) ⟶ 𝔸(AffinePlaneIndex.{t}; S) :=
  homOfVector ((𝔸(PUnit.{t + 1}; 𝔸(PUnit.{t + 1}; S)) ↘ 𝔸(PUnit.{t + 1}; S)) ≫
      (𝔸(PUnit.{t + 1}; S) ↘ S))
    fun i ↦ cond i.down (coord (𝔸(PUnit.{t + 1}; S)) PUnit.unit)
      ((𝔸(PUnit.{t + 1}; 𝔸(PUnit.{t + 1}; S)) ↘ 𝔸(PUnit.{t + 1}; S)).appTop
        (coord S PUnit.unit))

/-- The projection of the affine plane over `S` onto the affine line over `S` given by the first
coordinate. -/
noncomputable def planeInvBase : 𝔸(AffinePlaneIndex.{t}; S) ⟶ 𝔸(PUnit.{t + 1}; S) :=
  homOfVector (𝔸(AffinePlaneIndex.{t}; S) ↘ S) fun _ ↦ coord S (ULift.up false)

/-- The comparison of the affine plane over `S` with the affine line over the affine line over
`S`: the second coordinate is read as the coordinate of the upper affine line over the first. -/
noncomputable def planeInv :
    𝔸(AffinePlaneIndex.{t}; S) ⟶ 𝔸(PUnit.{t + 1}; 𝔸(PUnit.{t + 1}; S)) :=
  homOfVector (planeInvBase S) fun _ ↦ coord S (ULift.up true)

/-- The comparison with the affine plane lies over `S`. -/
lemma planeHom_over : planeHom S ≫ (𝔸(AffinePlaneIndex.{t}; S) ↘ S) =
    (𝔸(PUnit.{t + 1}; 𝔸(PUnit.{t + 1}; S)) ↘ 𝔸(PUnit.{t + 1}; S)) ≫ (𝔸(PUnit.{t + 1}; S) ↘ S) :=
  homOfVector_over _ _

/-- The first coordinate of the affine plane pulls back to the coordinate of the lower affine
line. -/
lemma planeHom_appTop_coord_false :
    (planeHom S).appTop (coord S (ULift.up false)) =
      (𝔸(PUnit.{t + 1}; 𝔸(PUnit.{t + 1}; S)) ↘ 𝔸(PUnit.{t + 1}; S)).appTop
        (coord S PUnit.unit) :=
  homOfVector_appTop_coord _ _ _

/-- The second coordinate of the affine plane pulls back to the coordinate of the upper affine
line. -/
lemma planeHom_appTop_coord_true :
    (planeHom S).appTop (coord S (ULift.up true)) =
      coord (𝔸(PUnit.{t + 1}; S)) PUnit.unit :=
  homOfVector_appTop_coord _ _ _

/-- The comparison with the affine line over the affine line lies over the affine line. -/
lemma planeInv_over :
    planeInv S ≫ (𝔸(PUnit.{t + 1}; 𝔸(PUnit.{t + 1}; S)) ↘ 𝔸(PUnit.{t + 1}; S)) =
      planeInvBase S :=
  homOfVector_over _ _

/-- The coordinate of the upper affine line pulls back to the second coordinate of the affine
plane. -/
lemma planeInv_appTop_coord (i : PUnit.{t + 1}) :
    (planeInv S).appTop (coord (𝔸(PUnit.{t + 1}; S)) i) = coord S (ULift.up true) :=
  homOfVector_appTop_coord _ _ i

/-- The first projection of the affine plane lies over `S`. -/
lemma planeInvBase_over : planeInvBase S ≫ (𝔸(PUnit.{t + 1}; S) ↘ S) =
    𝔸(AffinePlaneIndex.{t}; S) ↘ S :=
  homOfVector_over _ _

/-- The coordinate of the affine line pulls back to the first coordinate of the affine plane. -/
lemma planeInvBase_appTop_coord (i : PUnit.{t + 1}) :
    (planeInvBase S).appTop (coord S i) = coord S (ULift.up false) :=
  homOfVector_appTop_coord _ _ i

/-- The two comparisons compose to the identity of the affine plane. -/
lemma planeInv_comp_planeHom : planeInv S ≫ planeHom S = 𝟙 _ := by
  refine AffineSpace.hom_ext ?_ fun i ↦ ?_
  · rw [Category.assoc, planeHom_over, ← Category.assoc, planeInv_over, planeInvBase_over,
      Category.id_comp]
  · obtain ⟨b⟩ := i
    simp only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply]
    cases b
    · rw [planeHom_appTop_coord_false, ← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop,
        planeInv_over, planeInvBase_appTop_coord]
      simp
    · rw [planeHom_appTop_coord_true, planeInv_appTop_coord]
      simp

/-- The two comparisons compose to the identity of the affine line over the affine line. -/
lemma planeHom_comp_planeInv : planeHom S ≫ planeInv S = 𝟙 _ := by
  refine AffineSpace.hom_ext ?_ fun i ↦ ?_
  · rw [Category.assoc, planeInv_over, Category.id_comp, planeInvBase, comp_homOfVector,
      planeHom_over]
    refine AffineSpace.hom_ext ?_ fun j ↦ ?_
    · rw [homOfVector_over]
    · rw [homOfVector_appTop_coord, Function.comp_apply, planeHom_appTop_coord_false]
  · simp only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply, planeInv_appTop_coord]
    rw [planeHom_appTop_coord_true]
    simp

/-- The affine line over the affine line over `S` is the affine plane over `S`. The
isomorphism matches the coordinate of the lower affine line with the first coordinate of the
plane and the coordinate of the upper one with the second. -/
noncomputable def affinePlaneIso :
    𝔸(PUnit.{t + 1}; 𝔸(PUnit.{t + 1}; S)) ≅ 𝔸(AffinePlaneIndex.{t}; S) where
  hom := planeHom S
  inv := planeInv S
  hom_inv_id := planeHom_comp_planeInv S
  inv_hom_id := planeInv_comp_planeHom S

/-- An isomorphism of base schemes induces an isomorphism of the affine spaces over them. -/
noncomputable def affineSpaceIsoOfBaseIso (n : Type t) {S T : Scheme.{t}} (e : S ≅ T) :
    𝔸(n; S) ≅ 𝔸(n; T) where
  hom := AffineSpace.map n e.hom
  inv := AffineSpace.map n e.inv
  hom_inv_id := by rw [← AffineSpace.map_comp, Iso.hom_inv_id, AffineSpace.map_id]
  inv_hom_id := by rw [← AffineSpace.map_comp, Iso.inv_hom_id, AffineSpace.map_id]

/-- Identifying a scheme `Y` with the affine line over `S` and then the affine line over `Y` with
the affine plane over `S` is, over `S`, the structure morphism of the affine line over `Y`
followed by the identification of `Y`. -/
lemma affineSpaceIsoOfBaseIso_trans_affinePlaneIso_hom_over {Y : Scheme.{t}}
    (e : Y ≅ 𝔸(PUnit.{t + 1}; S)) :
    (affineSpaceIsoOfBaseIso PUnit.{t + 1} e ≪≫ affinePlaneIso S).hom ≫
        (𝔸(AffinePlaneIndex.{t}; S) ↘ S) =
      (𝔸(PUnit.{t + 1}; Y) ↘ Y) ≫ e.hom ≫ (𝔸(PUnit.{t + 1}; S) ↘ S) := by
  show (AffineSpace.map PUnit.{t + 1} e.hom ≫ planeHom S) ≫ _ = _
  rw [Category.assoc, planeHom_over, ← Category.assoc, AffineSpace.map_over, Category.assoc]

end AffineSpace

/-! ### Closure of a full subcategory under the affine line -/

open AffineSpace

variable {B : BigFppfSite.{t}} {X : Scheme.{t}} {hX : B.Contains X}

/-- A full subcategory of the big fppf category over `X` contains the affine line over each of
its objects: for an object `U` of the subcategory there is an object of the subcategory whose
underlying scheme is the affine line over the underlying scheme of `U`, compatibly with the
structure morphisms to `X`. -/
def IsClosedUnderAffineLine (P : ObjectProperty (BigFppfOver B X hX)) : Prop :=
  ∀ U : BigFppfOver B X hX, P U →
    ∃ (W : BigFppfOver B X hX)
      (e : (BigFppfOver.toScheme B X hX).obj W ≅
        𝔸(PUnit.{t + 1}; (BigFppfOver.toScheme B X hX).obj U)),
      e.hom ≫ (𝔸(PUnit.{t + 1}; (BigFppfOver.toScheme B X hX).obj U) ↘
          (BigFppfOver.toScheme B X hX).obj U) ≫ BigFppfOver.str B X hX U =
        BigFppfOver.str B X hX W ∧ P W

/-- A full subcategory of the big fppf category over `X` which contains the base object `X/X` and
is closed under the affine line contains an object isomorphic over `X` to the affine line over
`X`. -/
theorem exists_mem_isoAffineLine {P : ObjectProperty (BigFppfOver B X hX)}
    (hbase : P (Over.mk (𝟙 (B.obj hX)))) (hline : IsClosedUnderAffineLine P) :
    ∃ (A : BigFppfOver B X hX)
      (e : (BigFppfOver.toScheme B X hX).obj A ≅ 𝔸(PUnit.{t + 1}; X)),
      e.hom ≫ (𝔸(PUnit.{t + 1}; X) ↘ X) = BigFppfOver.str B X hX A ∧ P A := by
  obtain ⟨W, e, he, hW⟩ := hline _ hbase
  refine ⟨W, e, ?_, hW⟩
  rw [← he]
  simp
  rfl

/-- A full subcategory of the big fppf category over `X` which is closed under the affine line and
contains an object `A` isomorphic over `X` to the affine line over `X` contains an object
isomorphic over `X` to the affine plane over `X`. -/
theorem exists_mem_isoAffinePlane {P : ObjectProperty (BigFppfOver B X hX)}
    (hline : IsClosedUnderAffineLine P) {A : BigFppfOver B X hX} (hA : P A)
    (e : (BigFppfOver.toScheme B X hX).obj A ≅ 𝔸(PUnit.{t + 1}; X))
    (he : e.hom ≫ (𝔸(PUnit.{t + 1}; X) ↘ X) = BigFppfOver.str B X hX A) :
    ∃ (A' : BigFppfOver B X hX)
      (e' : (BigFppfOver.toScheme B X hX).obj A' ≅ 𝔸(AffinePlaneIndex.{t}; X)),
      e'.hom ≫ (𝔸(AffinePlaneIndex.{t}; X) ↘ X) = BigFppfOver.str B X hX A' ∧ P A' := by
  obtain ⟨W, f, hf, hW⟩ := hline A hA
  refine ⟨W, f ≪≫ affineSpaceIsoOfBaseIso PUnit.{t + 1} e ≪≫ affinePlaneIso X, ?_, hW⟩
  rw [← hf, Iso.trans_hom, Category.assoc,
    affineSpaceIsoOfBaseIso_trans_affinePlaneIso_hom_over X e, he]

/-- Let `C₁ ⊆ C₂` be full subcategories of the big fppf category over a scheme `X`, let `C₁`
contain the base object `X/X` and the affine line over each of its objects, and let
`g : Sh(C₁) ⟶ Sh(C₂)` be the morphism of topoi of the inclusion. Then the canonical map
`g_!O₁ ⟶ O₂` from the lower shriek of the restricted structure sheaf to the structure sheaf is an
isomorphism.

The sheaf condition on the structure presheaf of `C₂` and the existence of `g_!`, a left adjoint
of the pushforward along the inclusion, are taken as hypotheses. -/
@[stacks 07AJ "part (b)"]
theorem isIso_lowerShriekStructureSheafHom_of_isClosedUnderAffineLine
    {P₁ P₂ : ObjectProperty (BigFppfOver B X hX)} (h₁₂ : P₁ ≤ P₂)
    (J₁ : GrothendieckTopology P₁.FullSubcategory)
    (J₂ : GrothendieckTopology P₂.FullSubcategory)
    (hsh : Presheaf.IsSheaf J₂ (P₂.ι.op ⋙ bigOverPresheafAb B X hX))
    [(ObjectProperty.ιOfLE h₁₂).IsContinuous J₁ J₂]
    [((ObjectProperty.ιOfLE h₁₂).sheafPushforwardContinuous
      AddCommGrpCat.{t} J₁ J₂).IsRightAdjoint]
    (hbase : P₁ (Over.mk (𝟙 (B.obj hX)))) (hline : IsClosedUnderAffineLine P₁) :
    IsIso (lowerShriekStructureSheafHom h₁₂ J₁ J₂ hsh) := by
  obtain ⟨A, e, he, hA⟩ := exists_mem_isoAffineLine hbase hline
  obtain ⟨A', e', he', hA'⟩ := exists_mem_isoAffinePlane hline hA e he
  exact isIso_lowerShriekStructureSheafHom (A := ⟨A, hA⟩) (A' := ⟨A', hA'⟩)
    h₁₂ J₁ J₂ hsh e he e' he'

/-! ### The inclusion of one full subcategory into another -/

/-! The inclusion of one full subcategory of a site into another is fully faithful, and it is
continuous and cocontinuous for the inherited topologies as soon as both subcategories are closed
under the morphism property by which every covering sieve is refinable. -/

add_to_stacks 07AJ "part (a), full faithfulness" ObjectProperty.fullyFaithfulιOfLE

add_to_stacks 07AJ "part (a), continuity" ObjectProperty.isContinuous_ιOfLE_inheritedTopology

add_to_stacks 07AJ "part (a), cocontinuity" ObjectProperty.isCocontinuous_ιOfLE_inheritedTopology

end AlgebraicGeometry

end
