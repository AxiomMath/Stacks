module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMate
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.OpenBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProjectiveLineReduction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.TorsionSheavesAndRestriction

/-!
# Cohomology commuting with base change is local on the base

If cohomology commutes with base change for the restriction of `f : X ⟶ Y` over every affine open
of `Y`, then it does so for `f`. This is the use of Stacks 03Q8 made in the first paragraph of the
proof of [Stacks, Tag 0A4F]: the formation of the higher direct images commutes with Zariski
localization on the base.

Let `X' = Y' ×_Y X` with projections `g'`, `f'`, let `V ⊆ Y` be an affine open and `V' = g⁻¹V`.
The square of `f` over `V' ⟶ Y` is obtained by pasting in two ways: as the square of `f` over `g`
followed by the restriction to `V'`, and as the restriction of `f` to `V` followed by the square
of `f ∣_V` over `V' ⟶ V`. By the pasting law
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_comp_app`, the restriction to `V'` of the
base change map of `g` is invertible as soon as the base change maps of the two restrictions to
opens are — which they are by
`Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_of_isOpenImmersion` — and that of
`f ∣_V` over `V' ⟶ V` is, which is the hypothesis. A morphism of the derived category of
`Y'_étale` is invertible as soon as its restrictions to an open cover are.

## Main results

* `Stacks.EtaleCohomology.coversTop_smallEtaleObj_of_jointlySurjective` — a jointly surjective
  family of étale morphisms covers the small étale site.
* `Stacks.EtaleCohomology.isIso_of_isIso_etaleAbelianDerivedInverseImage_map` — invertibility in
  the derived category of the small étale site is local for such a family.
* `Stacks.EtaleCohomology.baseChangeZariskiLocalOnBase` — the localization on the base,
  `Stacks.EtaleCohomology.BaseChangeZariskiLocalOnBase`, holds.

## References

* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
* [Stacks Project, Tag 0A4F](https://stacks.math.columbia.edu/tag/0A4F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

/-- **A jointly surjective family of étale morphisms covers the small étale site.** Over an
étale `X`-scheme `W` the base changes `W ×_X U_i ⟶ W` are jointly surjective, and each factors
through `U_i`. -/
theorem coversTop_smallEtaleObj_of_jointlySurjective {X : Scheme.{u}} {ι : Type*}
    {U : ι → Scheme.{u}} (j : ∀ i, U i ⟶ X) [∀ i, Etale (j i)]
    (hsurj : ∀ x : X, ∃ i, x ∈ Set.range (j i)) :
    X.smallEtaleTopology.CoversTop fun i ↦ smallEtaleObj (j i) := by
  intro W
  let Z : ι → X.Etale := fun i ↦ smallEtaleObj (pullback.fst W.hom (j i) ≫ W.hom)
  let a : ∀ i, Z i ⟶ W := fun i ↦ MorphismProperty.Over.homMk (pullback.fst W.hom (j i)) rfl trivial
  have hcov : Sieve.ofArrows Z a ∈ X.smallEtaleTopology W := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_of_forall fun w => ?_
    obtain ⟨i, y, hy⟩ := hsurj (W.hom w)
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback w y hy.symm
    exact Set.mem_iUnion.2 ⟨i, z, hz⟩
  refine X.smallEtaleTopology.superset_covering ?_ hcov
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro V - ⟨i⟩
  exact ⟨i, ⟨MorphismProperty.Over.homMk (pullback.snd W.hom (j i)) pullback.condition.symm
    trivial⟩⟩

/-- **Invertibility in the derived category of the small étale site is local.** A morphism of
`D(X_étale)` whose inverse images along a jointly surjective family of étale morphisms are
invertible is invertible: its cohomology sheaves are, the inverse images being exact. -/
theorem isIso_of_isIso_etaleAbelianDerivedInverseImage_map {X : Scheme.{u}} {ι : Type*}
    {U : ι → Scheme.{u}} (j : ∀ i, U i ⟶ X) [∀ i, Etale (j i)]
    (hsurj : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (φ : K ⟶ L) (h : ∀ i, IsIso ((etaleAbelianDerivedInverseImage.{u, v} (j i)).map φ)) :
    IsIso φ := by
  rw [DerivedCategory.isIso_iff]
  intro n
  refine isIso_of_isIso_etaleAbelianInverseImage_of_coversTop _ j
    (coversTop_smallEtaleObj_of_jointlySurjective j hsurj) fun i => ?_
  exact ((etaleAbelianInverseImage.{u, v} (j i)).isIso_mapDerivedCategory_map_iff φ).1 (h i) n

/-- The inverse image of a torsion sheaf along an étale morphism is torsion: it is restriction,
and restriction along the cocontinuous functor `smallEtaleCompose j` preserves torsion. -/
theorem torsionSheafProperty_etaleAbelianInverseImage_of_etale {U X : Scheme.{u}} (j : U ⟶ X)
    [Etale j] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) :
    Stacks.Torsion.torsionSheafProperty U.smallEtaleTopology
      ((etaleAbelianInverseImage.{u, v} j).obj F) :=
  (Stacks.Torsion.torsionSheafProperty.{max (u + 1) v} U.smallEtaleTopology).prop_of_iso
    ((etaleAbelianInverseImageRestrictionIso.{u, v} j).app F).symm
    (Stacks.Torsion.torsionSheafProperty_sheafPushforwardContinuous
      (Scheme.Etale.smallEtaleCompose j) F hF)

/-- **The localization on the base.** If cohomology commutes with base change for the
restriction of `f` over every affine open of the target, then it does so for `f`. -/
theorem baseChangeZariskiLocalOnBase : BaseChangeZariskiLocalOnBase.{u, v} := by
  intro X Y f hV X' Y' g g' f' sq F hF
  set K := (DerivedCategory.singleFunctor
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj F
  refine isIso_of_isIso_etaleAbelianDerivedInverseImage_map.{u, v}
    (fun V : Y.affineOpens ↦ (g ⁻¹ᵁ V.1).ι) ?_ _ fun V ↦ ?_
  · intro y
    obtain ⟨_, ⟨V, hV, rfl⟩, hy, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g y)) isOpen_univ
    exact ⟨⟨V, hV⟩, by rwa [Opens.range_ι]⟩
  set U := V.1
  set V' := g ⁻¹ᵁ U
  set Z := f' ⁻¹ᵁ V'
  set j := f' ∣_ V'
  have t := isPullback_morphismRestrict f U
  have P1 := (isPullback_morphismRestrict f' V').flip
  have hw : (j ≫ g ∣_ U) ≫ U.ι = (Z.ι ≫ g') ≫ f := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, morphismRestrict_ι,
      Category.assoc, Category.assoc, sq.w]
  set k₂ := t.lift (j ≫ g ∣_ U) (Z.ι ≫ g') hw
  have hk₂ι : k₂ ≫ (f ⁻¹ᵁ U).ι = Z.ι ≫ g' := t.lift_snd _ _ _
  have hk₂f : k₂ ≫ f ∣_ U = j ≫ g ∣_ U := t.lift_fst _ _ _
  have sqV : IsPullback k₂ j (f ∣_ U) (g ∣_ U) := by
    refine IsPullback.of_right ?_ hk₂f t.flip
    rw [hk₂ι, morphismRestrict_ι]
    exact P1.paste_horiz sq
  have hyp : (Z.ι ≫ g') ≫ f = j ≫ (V'.ι ≫ g) := by
    rw [← hw, Category.assoc, morphismRestrict_ι]
  -- the two pastings of the outer square
  have D1 := etaleAbelianDerivedBaseChange_comp_app.{u, v} g f f' g' V'.ι j Z.ι sq.w
    (morphismRestrict_ι f' V').symm (V'.ι ≫ g) rfl (Z.ι ≫ g') rfl hyp K
  have D2 := etaleAbelianDerivedBaseChange_comp_app.{u, v} U.ι f (f ∣_ U) (f ⁻¹ᵁ U).ι
    (g ∣_ U) j k₂ (morphismRestrict_ι f U).symm hk₂f (V'.ι ≫ g) (morphismRestrict_ι g U).symm
    (Z.ι ≫ g') hk₂ι.symm hyp K
  -- the outer map is invertible, by the second pasting
  have hU := isIso_etaleAbelianDerivedBaseChange_of_isOpenImmersion.{u, v} f U.ι
    (f ⁻¹ᵁ U).ι (f ∣_ U) t.flip
  have hG := hV V (g ∣_ U) k₂ j sqV ((etaleAbelianInverseImage.{u, v} (f ⁻¹ᵁ U).ι).obj F)
    (torsionSheafProperty_etaleAbelianInverseImage_of_etale _ F hF)
  set ι0 := ((etaleAbelianInverseImage.{u, v} (f ⁻¹ᵁ U).ι).mapDerivedCategorySingleFunctor 0).app F
  have hG' : IsIso ((etaleAbelianDerivedBaseChange.{u, v} (f ∣_ U) (g ∣_ U) k₂ j sqV.w).app
      ((etaleAbelianDerivedInverseImage.{u, v} (f ⁻¹ᵁ U).ι).obj K)) :=
    (isIso_comp_right_iff _ _).1 ((congrArg IsIso
      ((etaleAbelianDerivedBaseChange.{u, v} (f ∣_ U) (g ∣_ U) k₂ j sqV.w).naturality ι0.hom)).mp
        (IsIso.comp_isIso' inferInstance hG))
  have hout : IsIso ((etaleAbelianDerivedBaseChange.{u, v} f (V'.ι ≫ g) (Z.ι ≫ g') j hyp).app
      K) := D2 ▸ inferInstance
  -- hence, by the first pasting, so is the restriction of the base change map of `g`
  have h1 := isIso_etaleAbelianDerivedBaseChange_of_isOpenImmersion.{u, v} f' V'.ι Z.ι j P1
  rw [D1] at hout
  have h2 := (isIso_comp_left_iff _ _).1 hout
  rw [← Category.assoc] at h2
  exact (isIso_comp_right_iff _ _).1 ((isIso_comp_right_iff _ _).1 h2)

end Stacks.EtaleCohomology

end
