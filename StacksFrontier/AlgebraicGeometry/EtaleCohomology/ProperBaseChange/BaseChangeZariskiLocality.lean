module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeCommutation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMate
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.OpenBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage

/-!
# Cohomology commuting with base change is local on the base

If cohomology commutes with base change for the restriction `f⁻¹(V) ⟶ V` of a morphism of
schemes `f : X ⟶ Y` over every affine open `V` of `Y`, then it commutes with base change for `f`.
This is the first paragraph of the proof of [Stacks, Tag 0A4F], which cites the compatibility of
higher direct images with localization on the base ([Stacks, Tag 03Q8]).

## Main results

* `Stacks.Torsion.isLocallyTorsion_comp_op` — precomposition with a cocontinuous functor of
  sites preserves local torsion.
* `Stacks.EtaleCohomology.torsionSheafProperty_etaleAbelianInverseImage_of_etale` — the inverse
  image of a torsion abelian sheaf along an étale morphism is torsion.
* `Stacks.EtaleCohomology.coversTop_smallEtaleObj` — étale morphisms with jointly surjective
  images cover the final object of the small étale site.
* `Stacks.EtaleCohomology.isIso_of_isIso_etaleAbelianDerivedInverseImage` — a morphism of the
  unbounded derived category of abelian sheaves on `X_étale` is invertible as soon as its
  inverse images along a jointly surjective family of étale morphisms are.
* `Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_affineOpens` — **the locality on
  the base.**

## Implementation notes

Given a cartesian square over `g : Y' ⟶ Y`, the base change map is checked on the open cover of
`Y'` by the `U = g⁻¹(V)`, `V` affine in `Y`. For each such `U` the rectangle
`X'_U ⟶ X` over `U ⟶ Y` is pasted in two ways. Along `U ⟶ Y' ⟶ Y` its base change map is the
inverse image to `U` of the given one followed by the base change map along the open immersion
`U ⟶ Y'`; along `U ⟶ V ⟶ Y` it is the inverse image of the base change map along the open
immersion `V ⟶ Y` followed by the base change map of the restricted morphism `f⁻¹(V) ⟶ V`. Both
pastings are `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_comp_app`, base change along an
open immersion is invertible by
`Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_of_isOpenImmersion`, and the
restricted morphism satisfies the condition by hypothesis.

## References

* [Stacks Project, Tag 0A4F](https://stacks.math.columbia.edu/tag/0A4F)
* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe w v u u₁ v₁ u₂ v₂

namespace Stacks.Torsion

/-- **Local torsion is preserved by precomposition with a cocontinuous functor.** The torsion
sieve of a section of `u.op ⋙ P` over `U` is the pullback along `u` of the torsion sieve of the
same section of `P` over `u U`, and cocontinuity carries covering sieves of `u U` to covering
sieves of `U`. -/
public theorem isLocallyTorsion_comp_op {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D)
    [u.IsCocontinuous J K] (P : Dᵒᵖ ⥤ AddCommGrpCat.{w}) (hP : IsLocallyTorsion K P) :
    IsLocallyTorsion J (u.op ⋙ P) := by
  rw [isLocallyTorsion_iff_torsionSieve_mem] at hP ⊢
  intro U y
  exact J.superset_covering (fun _ _ hg => hg) (u.cover_lift J K (hP (u.obj U) y))

end Stacks.Torsion

namespace Stacks.EtaleCohomology

/-- **Étale morphisms with jointly surjective images cover the final object** of the small étale
site: over every object `W` of `X_étale`, the base changes of the family to `W` are a jointly
surjective étale family factoring through the members. -/
public theorem coversTop_smallEtaleObj {X : Scheme.{u}} {ι : Type*} {U : ι → Scheme.{u}}
    (j : ∀ i, U i ⟶ X) [∀ i, Etale (j i)] (hj : ∀ x : X, ∃ i, x ∈ Set.range (j i)) :
    X.smallEtaleTopology.CoversTop fun i ↦ smallEtaleObj (j i) := by
  intro W
  let V : ι → X.Etale := fun i ↦ smallEtaleObj (pullback.fst W.hom (j i) ≫ W.hom)
  let a : ∀ i, V i ⟶ W := fun i ↦ MorphismProperty.Over.homMk (pullback.fst W.hom (j i)) rfl trivial
  refine X.smallEtaleTopology.superset_covering ?_
    ((Scheme.ofArrows_mem_smallEtaleTopology_iff a).2 ?_)
  · rintro Z _ ⟨_, c, _, ⟨i⟩, rfl⟩
    exact ⟨i, ⟨c ≫ MorphismProperty.Over.homMk (pullback.snd W.hom (j i))
      pullback.condition.symm trivial⟩⟩
  · refine Set.eq_univ_of_forall fun w ↦ ?_
    obtain ⟨i, z, hz⟩ := hj (W.hom w)
    obtain ⟨p, hp, -⟩ := Scheme.Pullback.exists_preimage_pullback w z hz.symm
    exact Set.mem_iUnion.2 ⟨i, p, hp⟩

/-- **Invertibility in the derived category is local for the étale topology.** A morphism of the
unbounded derived category of abelian sheaves on `X_étale` is invertible as soon as its inverse
images along a family of étale morphisms with jointly surjective images are: inverse image is
exact, so it commutes with taking cohomology sheaves, and invertibility of a morphism of sheaves
is local. -/
public theorem isIso_of_isIso_etaleAbelianDerivedInverseImage {X : Scheme.{u}} {ι : Type*}
    {U : ι → Scheme.{u}} (j : ∀ i, U i ⟶ X) [∀ i, Etale (j i)]
    (hj : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (φ : K ⟶ L) (h : ∀ i, IsIso ((etaleAbelianDerivedInverseImage.{u, v} (j i)).map φ)) :
    IsIso φ := by
  rw [DerivedCategory.isIso_iff]
  intro n
  exact isIso_of_isIso_etaleAbelianInverseImage_of_coversTop _ j (coversTop_smallEtaleObj j hj)
    fun i => ((etaleAbelianInverseImage.{u, v} (j i)).isIso_mapDerivedCategory_map_iff φ).1 (h i) n

/-- **Over the preimage of an open on which the condition holds, the base change map is
invertible.** Let `V ⊆ Y` be open with cohomology commuting with base change for `f⁻¹(V) ⟶ V`.
For a cartesian square over `g : Y' ⟶ Y` and a torsion sheaf `F`, the inverse image of the base
change map `g^{-1} Rf_* F ⟶ Rf'_* (g')^{-1} F` to `U = g⁻¹(V)` is invertible: the rectangle over
`U ⟶ Y` pastes both through `U ⟶ Y'` and through `U ⟶ V`, and every other factor of the two
pastings is invertible. -/
public theorem isIso_etaleAbelianDerivedInverseImage_map_sheafDerivedBaseChange
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (hV : CohomologyCommutesWithBaseChange.{u, v} (f ∣_ V))
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y') (sq : IsPullback g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) :
    IsIso ((etaleAbelianDerivedInverseImage.{u, v} (g ⁻¹ᵁ V).ι).map
      (etaleAbelianSheafDerivedBaseChange.{u, v} f g g' f' sq.w F)) := by
  let j := (g ⁻¹ᵁ V).ι
  let k := g ∣_ V
  let ιX := (f ⁻¹ᵁ V).ι
  let fV := f ∣_ V
  have hVsq : IsPullback ιX fV f V.ι := (isPullback_morphismRestrict f V).flip
  have up : IsPullback (pullback.fst fV k) (pullback.snd fV k) fV k :=
    IsPullback.of_hasPullback fV k
  let kX := pullback.fst fV k
  let fU := pullback.snd fV k
  have hk : k ≫ V.ι = j ≫ g := morphismRestrict_ι g V
  have outer : IsPullback (kX ≫ ιX) fU f (k ≫ V.ι) := up.paste_horiz hVsq
  let jX : pullback fV k ⟶ X' := sq.lift (kX ≫ ιX) (fU ≫ j) (by
    rw [outer.w, hk, Category.assoc])
  have hjX₁ : jX ≫ g' = kX ≫ ιX := sq.lift_fst _ _ _
  have hjX₂ : jX ≫ f' = fU ≫ j := sq.lift_snd _ _ _
  have outer' : IsPullback (jX ≫ g') fU f (j ≫ g) := by rwa [hjX₁, ← hk]
  have jsq : IsPullback jX fU f' j := IsPullback.of_right outer' hjX₂ sq
  let K := (DerivedCategory.singleFunctor
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj F
  have hA := etaleAbelianDerivedBaseChange_comp_app.{u, v} g f f' g' j fU jX sq.w jsq.w
    (k ≫ V.ι) hk (kX ≫ ιX) hjX₁.symm outer.w K
  have hB := etaleAbelianDerivedBaseChange_comp_app.{u, v} V.ι f fV ιX k fU kX hVsq.w up.w
    (k ≫ V.ι) rfl (kX ≫ ιX) rfl outer.w K
  have := isIso_etaleAbelianDerivedBaseChange_of_isOpenImmersion.{u, v} f V.ι ιX fV hVsq
  have := isIso_etaleAbelianDerivedBaseChange_of_isOpenImmersion.{u, v} f' j jX fU jsq
  have hup : IsIso ((etaleAbelianDerivedBaseChange.{u, v} fV k kX fU up.w).app
      ((etaleAbelianDerivedInverseImage.{u, v} ιX).obj K)) :=
    (NatTrans.isIso_app_iff_of_iso _
      (((etaleAbelianInverseImage.{u, v} ιX).mapDerivedCategorySingleFunctor 0).app F)).2
      (hV k kX fU up ((etaleAbelianInverseImage.{u, v} ιX).obj F)
        (torsionSheafProperty_etaleAbelianInverseImage_of_etale ιX F hF))
  have hLHS : IsIso ((etaleAbelianDerivedBaseChange.{u, v} f (k ≫ V.ι) (kX ≫ ιX) fU
      outer.w).app K) := by
    rw [hB]
    infer_instance
  rwa [hA, isIso_comp_left_iff, ← Category.assoc, isIso_comp_right_iff,
    isIso_comp_right_iff] at hLHS

/-- **Cohomology commuting with base change is local on the base.** If cohomology commutes with
base change for the restriction `f⁻¹(V) ⟶ V` of `f : X ⟶ Y` over every affine open `V` of `Y`,
then it commutes with base change for `f`. The base change map of a square over `g : Y' ⟶ Y` is
checked on the open cover of `Y'` by the preimages of the affine opens of `Y`. -/
public theorem cohomologyCommutesWithBaseChange_of_affineOpens {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ V : Y.affineOpens, CohomologyCommutesWithBaseChange.{u, v} (f ∣_ V.1)) :
    CohomologyCommutesWithBaseChange.{u, v} f := by
  intro X' Y' g g' f' sq F hF
  refine isIso_of_isIso_etaleAbelianDerivedInverseImage
    (fun V : Y.affineOpens ↦ (g ⁻¹ᵁ V.1).ι) (fun y ↦ ?_) _ fun V ↦
      isIso_etaleAbelianDerivedInverseImage_map_sheafDerivedBaseChange f V.1 (hf V) g g' f' sq F hF
  obtain ⟨_, ⟨V, hV, rfl⟩, hgy, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (g y)) isOpen_univ
  exact ⟨⟨V, hV⟩, ⟨y, hgy⟩, rfl⟩

end Stacks.EtaleCohomology

end
