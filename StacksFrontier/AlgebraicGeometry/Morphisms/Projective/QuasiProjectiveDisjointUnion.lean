module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.ClosedCoverGlue.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveCategoryClosure
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.Composite
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.RestrictBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FiniteGroupQuotient
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite disjoint unions of quasi-projective schemes

Let `S` be a scheme carrying an ample invertible sheaf. A finite disjoint union of schemes
quasi-projective over `S` is quasi-projective over `S`; equivalently, the full subcategory `QP_S`
of schemes quasi-projective over `S` is closed under finite coproducts in `Over S`.

## Main definitions

* `AlgebraicGeometry.isColimitOverCofanMk`: the disjoint union of the sources of a family of
  schemes over `S` is its coproduct in `Over S`.

## Main results

* `AlgebraicGeometry.isQuasiProjective_sigmaDesc`: for a finite family `f i : Z i ⟶ S` of
  quasi-projective morphisms the structure morphism `Sigma.desc f : ∐ Z ⟶ S` of the disjoint
  union is quasi-projective.
* `AlgebraicGeometry.quasiProjectiveOver_prop_of_isColimit_cofan`: the full subcategory `QP_S` of
  `Over S` is closed under finite coproducts.
* `AlgebraicGeometry.isQuasiProjective_coprodDesc`: the binary case, `Y ⨿ Z ⟶ S`.
* `AlgebraicGeometry.isRelativelyAmple_moduleOnSchemeSigma`: the module glued from the `L i` is
  ample relative to the disjoint union of the `f i`, read as a morphism to the disjoint union of
  copies of `S`.

## References

* [Stacks Project, Tag 0B43](https://stacks.math.columbia.edu/tag/0B43)
* [Stacks Project, Tag 0B42](https://stacks.math.columbia.edu/tag/0B42)
* [Stacks Project, Tag 01VJ](https://stacks.math.columbia.edu/tag/01VJ)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 0C4M](https://stacks.math.columbia.edu/tag/0C4M)
* [Stacks Project, Tag 01SK](https://stacks.math.columbia.edu/tag/01SK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {ι : Type u} [Finite ι] {S : Scheme.{u}} {Z : ι → Scheme.{u}}

/-! ### The glued module on a finite disjoint union -/

/-- The module on a finite disjoint union glued from invertible modules on the summands is
invertible. -/
instance isInvertibleModule_moduleOnSchemeSigma (Z : ι → Scheme.{u}) (L : ∀ i, (Z i).Modules)
    [∀ i, Stacks.Ample.IsInvertibleModule (Z i) (L i)] :
    Stacks.Ample.IsInvertibleModule (∐ Z) (StacksTag09NE.moduleOnSchemeSigma Z L) := by
  classical
  set X : Scheme.{u} := ∐ Z
  set Lcop : X.Modules := StacksTag09NE.moduleOnSchemeSigma Z L
  have hLoc (x : ↥X) :=
    StacksTag09NE.moduleOnSchemeSigma_exists_local_free Z L (show ↥(∐ Z) from x)
  choose U hU I e eI using hLoc
  have hq :=
    Stacks.FiniteLocallyFree.ModuleTFAE.localGeneratorsDataOfTrivializations_isLocallyFreeData
      Lcop U hU I e
  have hflf : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
      (C := TopologicalSpace.Opens X)
      (J := Opens.grothendieckTopology X) Lcop 1 :=
    @AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.mk.{u, u, u}
      (TopologicalSpace.Opens X) _
      (Opens.grothendieckTopology X) X.ringCatSheaf _ _ Lcop 1
      ⟨Stacks.FiniteLocallyFree.ModuleTFAE.localGeneratorsDataOfTrivializations
        Lcop U hU I e, hq, eI⟩
  exact (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry
      X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property Lcop).1
    (Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one
      (h := hflf) X.toRingedSpace Lcop)

/-! ### The summand inclusions of a finite disjoint union -/

/-- The image of a summand of a finite disjoint union of schemes is closed. -/
theorem isClosed_range_sigmaι (g : ι → Scheme.{u}) (i : ι) :
    IsClosed (Set.range (Sigma.ι g i).base) := by
  refine ⟨?_⟩
  have hcompl : (Set.range (Sigma.ι g i).base)ᶜ =
      ⋃ j ∈ {j : ι | j ≠ i}, Set.range (Sigma.ι g j).base := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hx
      obtain ⟨j, z, hz⟩ := StacksTag09NE.exists_component_point_of_sigma g x
      refine ⟨j, ?_, z, hz⟩
      rintro rfl
      exact hx ⟨z, hz⟩
    · rintro ⟨j, hji, z, hz⟩ ⟨w, hw⟩
      exact hji (congrArg Sigma.fst ((sigmaι_eq_iff g i j w z).mp (hw.trans hz.symm))).symm
  rw [hcompl]
  exact isOpen_biUnion fun j _ ↦ (Sigma.ι g j).isOpenEmbedding.isOpen_range

/-- The inclusion of a summand of a finite disjoint union of schemes is quasi-compact. -/
instance quasiCompact_sigmaι (g : ι → Scheme.{u}) (i : ι) : QuasiCompact (Sigma.ι g i) := by
  refine ⟨fun V hVopen hVcompact ↦ ?_⟩
  refine ((Sigma.ι g i).isOpenEmbedding.isEmbedding.isCompact_iff).mpr ?_
  rw [Set.image_preimage_eq_inter_range]
  exact hVcompact.inter_right (isClosed_range_sigmaι g i)

/-! ### The disjoint union of copies of the base -/

/-- For `q = Sigma.desc (fun _ => 𝟙 S) : ∐_{i} S ⟶ S` the preimage of an open `U` of `S` is the
union of the copies of `U` in the summands. -/
theorem preimage_sigmaConstDesc (U : S.Opens) :
    (Sigma.desc fun _ : ι => 𝟙 S) ⁻¹ᵁ U = ⨆ i : ι, Sigma.ι (fun _ : ι => S) i ''ᵁ U := by
  ext x
  simp only [Scheme.Hom.coe_preimage, Set.mem_preimage, TopologicalSpace.Opens.iSup_mk,
    TopologicalSpace.Opens.coe_mk, Set.mem_iUnion]
  constructor
  · intro hx
    obtain ⟨j, y, rfl⟩ := StacksTag09NE.exists_component_point_of_sigma (fun _ : ι => S) x
    refine ⟨j, y, ?_, rfl⟩
    rwa [← Scheme.Hom.comp_apply, Limits.Sigma.ι_comp_desc] at hx
  · rintro ⟨j, y, hyU, rfl⟩
    change (Sigma.ι (fun _ : ι => S) j ≫ Sigma.desc fun _ : ι => 𝟙 S) y ∈ U
    rwa [Limits.Sigma.ι_comp_desc]

/-- The morphism `∐_{i} S ⟶ S` collapsing finitely many copies of `S` is quasi-affine. -/
instance isQuasiAffineHom_sigmaConstDesc (ι : Type u) [Finite ι] (S : Scheme.{u}) :
    IsQuasiAffineHom (Sigma.desc fun _ : ι => 𝟙 S) := by
  refine ⟨fun U hU ↦ ?_⟩
  have : IsAffine ((Sigma.desc fun _ : ι => 𝟙 S) ⁻¹ᵁ U).toScheme := by
    rw [preimage_sigmaConstDesc U]
    exact IsAffineOpen.iSup_of_disjoint (fun i ↦ hU.image_of_isOpenImmersion _)
      fun i j hij ↦ (disjoint_opensRange_sigmaι (fun _ : ι => S) i j hij).mono
        ((Sigma.ι (fun _ : ι => S) i).image_le_opensRange U)
        ((Sigma.ι (fun _ : ι => S) j).image_le_opensRange U)
  infer_instance

/-- The morphism `∐_{i} S ⟶ S` collapsing finitely many copies of `S` is locally of finite
type. -/
instance locallyOfFiniteType_sigmaConstDesc (ι : Type u) [Finite ι] (S : Scheme.{u}) :
    LocallyOfFiniteType (Sigma.desc fun _ : ι => 𝟙 S) :=
  letI : IsZariskiLocalAtSource (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)
  IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance

/-- The morphism `∐_{i} S ⟶ S` collapsing finitely many copies of `S` is quasi-projective. -/
theorem isQuasiProjective_sigmaConstDesc (ι : Type u) [Finite ι] (S : Scheme.{u}) :
    IsQuasiProjective (Sigma.desc fun _ : ι => 𝟙 S) :=
  isQuasiProjective_of_isQuasiAffineHom _ inferInstance

/-! ### The disjoint union of the morphisms, read over the disjoint union of the bases -/

omit [Finite ι] in
/-- With `σ i : S ⟶ ∐_{i} S` the summand inclusions, `F = Sigma.desc (fun i => f i ≫ σ i)` and
`q = Sigma.desc (fun _ => 𝟙 S)`, one has `F ≫ q = Sigma.desc f`. -/
theorem sigmaDescToConst_comp_sigmaConstDesc (f : ∀ i, Z i ⟶ S) :
    (Sigma.desc fun i => f i ≫ Sigma.ι (fun _ : ι => S) i) ≫
        (Sigma.desc fun _ : ι => 𝟙 S) = Sigma.desc f := by
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  rw [← Category.assoc, Limits.Sigma.ι_comp_desc, Limits.Sigma.ι_comp_desc, Category.assoc,
    Limits.Sigma.ι_comp_desc, Category.comp_id]

omit [Finite ι] in
/-- On a point of the summand `Z i`, the morphism `Sigma.desc (fun j => f j ≫ σ j)` is `f i`
followed by the inclusion `σ i` of the `i`th copy of `S`. -/
theorem sigmaDescToConst_apply (f : ∀ i, Z i ⟶ S) (i : ι) (z : Z i) :
    (Sigma.desc fun j => f j ≫ Sigma.ι (fun _ : ι => S) j) (Sigma.ι Z i z) =
      Sigma.ι (fun _ : ι => S) i (f i z) := by
  rw [← Scheme.Hom.comp_apply, Limits.Sigma.ι_comp_desc, Scheme.Hom.comp_apply]

/-- For `F = Sigma.desc (fun i => f i ≫ σ i)` the preimage of the open `σ i ''ᵁ W` of the `i`th
copy of `S` is the image in `∐ Z` of the open `f i ⁻¹ᵁ W` of the summand `Z i`. -/
theorem preimage_sigmaDescToConst_image (f : ∀ i, Z i ⟶ S) (i : ι) (W : S.Opens) :
    (Sigma.desc fun j => f j ≫ Sigma.ι (fun _ : ι => S) j) ⁻¹ᵁ
        (Sigma.ι (fun _ : ι => S) i ''ᵁ W) = Sigma.ι Z i ''ᵁ (f i ⁻¹ᵁ W) := by
  ext x
  simp only [Scheme.Hom.coe_preimage, Set.mem_preimage, Scheme.Hom.coe_image, Set.mem_image]
  constructor
  · rintro ⟨w, hwW, hw⟩
    obtain ⟨j, z, rfl⟩ := StacksTag09NE.exists_component_point_of_sigma Z x
    rw [sigmaDescToConst_apply f j z] at hw
    obtain rfl : i = j :=
      congrArg Sigma.fst ((sigmaι_eq_iff (fun _ : ι => S) i j w (f j z)).mp hw)
    exact ⟨z, (Sigma.ι (fun _ : ι => S) i).isOpenEmbedding.injective hw ▸ hwW, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨f i z, hz, (sigmaDescToConst_apply f i z).symm⟩

/-- If each `f i` is quasi-compact, so is `Sigma.desc (fun i => f i ≫ σ i) : ∐ Z ⟶ ∐_{i} S`. -/
private theorem quasiCompact_sigmaDescToConst (f : ∀ i, Z i ⟶ S) (hf : ∀ i, QuasiCompact (f i)) :
    QuasiCompact (Sigma.desc fun i => f i ≫ Sigma.ι (fun _ : ι => S) i) :=
  Space.quasiCompact_sigmaDesc_of_finite _ fun i ↦ have := hf i; inferInstance

/-- If each invertible module `L i` is ample relative to `f i : Z i ⟶ S`, then the module on `∐ Z`
glued from the `L i` is ample relative to `Sigma.desc (fun i => f i ≫ σ i) : ∐ Z ⟶ ∐_{i} S`. -/
theorem isRelativelyAmple_moduleOnSchemeSigma (f : ∀ i, Z i ⟶ S) (L : ∀ i, (Z i).Modules)
    [∀ i, Stacks.Ample.IsInvertibleModule (Z i) (L i)]
    (hL : ∀ i, Stacks.RelativeAmple.IsRelativelyAmple (f i) (L i)) :
    Stacks.RelativeAmple.IsRelativelyAmple
      (Sigma.desc fun i => f i ≫ Sigma.ι (fun _ : ι => S) i)
      (StacksTag09NE.moduleOnSchemeSigma Z L) := by
  classical
  refine Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple _ _
    (quasiCompact_sigmaDescToConst f fun i ↦ (hL i).quasiCompact) fun t ↦ ?_
  obtain ⟨i, y, rfl⟩ := StacksTag09NE.exists_component_point_of_sigma (fun _ : ι => S) t
  obtain ⟨-, ⟨W, hW, rfl⟩, hyW, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (a := y) (Set.mem_univ y) isOpen_univ
  refine ⟨Sigma.ι (fun _ : ι => S) i ''ᵁ W, hW.image_of_isOpenImmersion _, ⟨y, hyW, rfl⟩, ?_⟩
  have hrange : Set.range ((f i ⁻¹ᵁ W).ι ≫ Sigma.ι Z i).base =
      Set.range (((Sigma.desc fun j => f j ≫ Sigma.ι (fun _ : ι => S) j) ⁻¹ᵁ
        (Sigma.ι (fun _ : ι => S) i ''ᵁ W)).ι).base := by
    rw [Scheme.Opens.range_ι, preimage_sigmaDescToConst_image f i W]
    simp [Set.range_comp, Scheme.Opens.range_ι]
  exact Stacks.RelativeAmpleRestrictBase.isAmple_pullbackModule_of_range_eq _ _ hrange _
    ((Stacks.RelativeAmpleRestrictBase.isAmple_pullbackModule_comp_iff _ _ _).mp
      ((Stacks.RelativeVeryAmple.isAmple_congr _ _ ((Scheme.Modules.pullback (f i ⁻¹ᵁ W).ι).mapIso
        (StacksTag09NE.pullback_moduleOnSchemeSigma Z L i).symm)).mp ((hL i).2 W hW)))

/-! ### Finite disjoint unions -/

/-- Let `S` carry an ample invertible sheaf. If `f i : Z i ⟶ S` is quasi-projective for every
member of a finite family, then the structure morphism `∐ Z ⟶ S` of the disjoint union is
quasi-projective. -/
@[stacks 0B43 "part (4), finite disjoint unions; proved through clause (6) and clause (2) over \
the base `∐ S` rather than through the ampleness of a glued module on a disjoint union, which the \
source asserts with details omitted"]
theorem isQuasiProjective_sigmaDesc (f : ∀ i, Z i ⟶ S)
    (hS : ∃ (M : S.Modules) (hM : Stacks.Ample.IsInvertibleModule S M),
      letI : Stacks.Ample.IsInvertibleModule S M := hM
      Stacks.Ample.IsAmple S M)
    (hf : ∀ i, IsQuasiProjective (f i)) : IsQuasiProjective (Sigma.desc f) := by
  classical
  have : CompactSpace S := compactSpace_of_exists_isAmple S hS
  choose L hLinv hLample using fun i ↦ (hf i).2
  have := hLinv
  have hF : IsQuasiProjective (Sigma.desc fun i => f i ≫ Sigma.ι (fun _ : ι => S) i) := by
    refine ⟨⟨?_, ?_⟩, StacksTag09NE.moduleOnSchemeSigma Z L, inferInstance,
      isRelativelyAmple_moduleOnSchemeSigma f L hLample⟩
    · let : IsZariskiLocalAtSource (@LocallyOfFiniteType.{u}) :=
        HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)
      exact IsZariskiLocalAtSource.sigmaDesc fun i ↦ have := (hf i).1.1; inferInstance
    · exact quasiCompact_sigmaDescToConst f fun i ↦ (hf i).quasiCompact
  rw [← sigmaDescToConst_comp_sigmaConstDesc f]
  exact IsQuasiProjective.comp _ _ hF (isQuasiProjective_sigmaConstDesc ι S)

/-- The disjoint union of the sources of a family of schemes over `S`, with the morphism to `S`
descended from the structure morphisms and the summand inclusions, is the coproduct of the family
in `Over S`. -/
@[ega "IV 11.10.3"]
def isColimitOverCofanMk {ι : Type u} (X : ι → Over S) :
    IsColimit (Cofan.mk (Over.mk (Sigma.desc fun i => (X i).hom))
      (fun i => Over.homMk (U := X i) (V := Over.mk (Sigma.desc fun j => (X j).hom))
        (Sigma.ι (fun j => (X j).left) i) (Limits.Sigma.ι_comp_desc _ i))) :=
  Cofan.IsColimit.mk _
    (fun t ↦ Over.homMk (Sigma.desc fun i => (t.inj i).left)
      (Sigma.hom_ext _ _ fun i ↦ by simp))
    (fun _ _ ↦ Over.OverMorphism.ext (by simp))
    (fun _ m h ↦ Over.OverMorphism.ext (Sigma.hom_ext _ _ fun i ↦ by
      simpa using congrArg Over.Hom.left (h i)))

/-- For `S` carrying an ample invertible sheaf, the full subcategory of schemes quasi-projective
over `S` is closed under finite coproducts in the category of schemes over `S`. -/
@[stacks 0B43 "part (4), finite disjoint unions, as closure of the category under finite \
coproducts", ega "II 5.3.6" "special case"]
theorem quasiProjectiveOver_prop_of_isColimit_cofan (S : Scheme.{u})
    (hS : ∃ (M : S.Modules) (hM : Stacks.Ample.IsInvertibleModule S M),
      letI : Stacks.Ample.IsInvertibleModule S M := hM
      Stacks.Ample.IsAmple S M)
    {ι : Type u} [Finite ι] {X : ι → Over S} (hX : ∀ i, quasiProjectiveOver S (X i))
    (c : Cofan X) (hc : IsColimit c) : quasiProjectiveOver S c.pt :=
  ObjectProperty.prop_of_iso _ ((isColimitOverCofanMk X).coconePointUniqueUpToIso hc)
    (isQuasiProjective_sigmaDesc (fun i ↦ (X i).hom) hS hX)

/-- Let `S` carry an ample invertible sheaf. If `g : Y ⟶ S` and `h : Z ⟶ S` are quasi-projective
then so is the structure morphism `Y ⨿ Z ⟶ S` of their disjoint union. -/
theorem isQuasiProjective_coprodDesc {Y Z S : Scheme.{u}} (g : Y ⟶ S) (h : Z ⟶ S)
    (hS : ∃ (M : S.Modules) (hM : Stacks.Ample.IsInvertibleModule S M),
      letI : Stacks.Ample.IsInvertibleModule S M := hM
      Stacks.Ample.IsAmple S M)
    (hg : IsQuasiProjective g) (hh : IsQuasiProjective h) :
    IsQuasiProjective (coprod.desc g h) := by
  have key := isQuasiProjective_sigmaDesc
    (fun i : ULift.{u} WalkingPair =>
      i.1.casesOn (motive := fun j => (j.casesOn Y Z : Scheme.{u}) ⟶ S) g h) hS
    (fun ⟨i⟩ ↦ by cases i <;> assumption)
  have he : (coprodIsoSigma Y Z).hom ≫ Sigma.desc (fun i : ULift.{u} WalkingPair =>
      i.1.casesOn (motive := fun j => (j.casesOn Y Z : Scheme.{u}) ⟶ S) g h) =
      coprod.desc g h := by
    refine coprod.hom_ext ?_ ?_
    · rw [coprod.inl_desc, ← ι_left_coprodIsoSigma_inv, Category.assoc,
        Iso.inv_hom_id_assoc, colimit.ι_desc]
      rfl
    · rw [coprod.inr_desc, ← ι_right_coprodIsoSigma_inv, Category.assoc,
        Iso.inv_hom_id_assoc, colimit.ι_desc]
      rfl
  rw [← he]
  exact IsQuasiProjective.of_isPullback (g := 𝟙 S)
    (IsPullback.of_horiz_isIso (fst := (coprodIsoSigma Y Z).hom) ⟨by simp⟩) key

end AlgebraicGeometry

end
