module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.PhComparisonCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.ProperHypercovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigPhSpacesEtaleComparison
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationCartesian
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationEqualizer
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationPushforwardComparison
public import StacksFrontier.Topology.Simplicial.ProperHypercoveringFullyFaithful

/-!
# Sheaves on a proper hypercovering of an algebraic space

Let `S` be a scheme, `X` an algebraic space over `S`, `U` a simplicial algebraic space over `S`
and `a : U → X` an augmentation which is a proper hypercovering of `X` (Section 0DHI). Tag 0DHK
says that `a⁻¹ : Sh(X_étale) ⥤ Sh(U_étale)` and `a⁻¹ : Ab(X_étale) ⥤ Ab(U_étale)` are fully
faithful with essential image the cartesian sheaves and quasi-inverse `a_*`, where
`a : Sh(U_étale) → Sh(X_étale)` is the morphism of topoi of Section 0DE7.

The proof is the source's. In the commutative square of Tag 0DHJ
```
Sh((Spaces/U)_{ph, total}) --h--> Sh(U_étale)
        | a_ph                       | a
Sh((Spaces/X)_ph)        --h₋₁--> Sh(X_étale)
```
`h₋₁⁻¹` and `h⁻¹` are fully faithful (Stacks 0DGT (1), through Tag 0D96), and `a_ph⁻¹` is fully
faithful with essential image the cartesian sheaves (Stacks 0DA8, a proper surjection being a ph
covering by Stacks 0DFI). Hence `a⁻¹` is fully faithful. For a cartesian sheaf `G` on `U_étale`
the sheaf `h⁻¹G` is cartesian, so `h⁻¹G = a_ph⁻¹ℋ` with `ℋ = a_{ph, *} h⁻¹G`; the sheaf `ℋ` is the
equalizer of the direct images of the restrictions of `h⁻¹G` to `U_0` and `U_1`
(Tag 0D70), which come from `X_étale` by Stacks 0DGX (1), `U_0 → X` and `U_1 → X` being proper.
So `ℋ = h₋₁⁻¹ℋ'`, and `h⁻¹ a⁻¹ ℋ' = a_ph⁻¹ h₋₁⁻¹ ℋ' = h⁻¹ G` gives `a⁻¹ℋ' = G`. The statement for
abelian sheaves follows, the units and counits of the abelian adjunction forgetting to those of
the adjunction on sheaves of sets.

## Main results

* `BigPHSpaceSite.mem_essImage_phAugmentation_pushforward`: the direct image along `a_ph` of a
  sheaf whose restrictions to the degrees `0` and `1` come from the small étale sites comes from
  `X_étale`.
* `BigPHSpaceSite.fullyFaithfulEtaleAugmentationInverseImage`: `a⁻¹` is fully faithful.
* `BigPHSpaceSite.mem_essImage_etaleAugmentation_inverseImage`: a cartesian sheaf on `U_étale` is
  in the essential image of `a⁻¹`.
* `BigPHSpaceSite.etaleAugmentation_inverseImage_fullyFaithful_of_isProperHypercovering`:
  **Tag 0DHK**, sheaves of sets.
* `BigPHSpaceSite.etaleAugmentation_abelianInverseImage_fullyFaithful_of_isProperHypercovering`:
  **Tag 0DHK**, sheaves of abelian groups.

## Implementation notes

The category of algebraic spaces over `S` is the one of a big ph site `P` of algebraic spaces over
`S`, which supplies the ph topology of the proof; the statement itself only involves the small
étale topoi of `U` and of `X`. The essential images are those of the inverse images of the
morphisms of topoi, and "quasi-inverse `a_*`" is the invertibility of the unit of `a⁻¹ ⊣ a_*` and
of its counit at the cartesian sheaves. On abelian sheaves the inverse image is
`CategoryTheory.Sites.abelianInverseImage` and its right adjoint is the abelian direct image of
`Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward`.

## References

* [Stacks Project, Tag 0DHK](https://stacks.math.columbia.edu/tag/0DHK)
* [Stacks Project, Tag 0DHJ](https://stacks.math.columbia.edu/tag/0DHJ)
* [Stacks Project, Tag 0DA8](https://stacks.math.columbia.edu/tag/0DA8)
* [Stacks Project, Tag 0DGT](https://stacks.math.columbia.edu/tag/0DGT)
* [Stacks Project, Tag 0DGX](https://stacks.math.columbia.edu/tag/0DGX)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Section 0DHI](https://stacks.math.columbia.edu/tag/0DHI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace CategoryTheory.Functor.FullyFaithful

/-- **The essential image of a fully faithful functor preserving equalizers is closed under
equalizers.** -/
theorem mem_essImage_of_isLimit_fork {C D : Type*} [Category C] [Category D] {L : C ⥤ D}
    (hL : L.FullyFaithful) [HasEqualizers C] [PreservesLimitsOfShape WalkingParallelPair L]
    {Y₀ Y₁ : D} {f g : Y₀ ⟶ Y₁} {c : Fork f g} (hc : IsLimit c) (h₀ : L.essImage Y₀)
    (h₁ : L.essImage Y₁) : L.essImage c.pt := by
  obtain ⟨X₀, ⟨e₀⟩⟩ := h₀
  obtain ⟨X₁, ⟨e₁⟩⟩ := h₁
  let f' := hL.preimage (e₀.hom ≫ f ≫ e₁.inv)
  let g' := hL.preimage (e₀.hom ≫ g ≫ e₁.inv)
  let iso : parallelPair (L.map f') (L.map g') ≅ parallelPair f g :=
    parallelPair.ext e₀ e₁ (by simp [f']) (by simp [g'])
  exact ⟨equalizer f' g', ⟨((IsLimit.postcomposeHomEquiv iso _).symm (isLimitForkMapOfIsLimit L
    (equalizer.condition f' g') (equalizerIsEqualizer f' g'))).conePointUniqueUpToIso hc⟩⟩

end CategoryTheory.Functor.FullyFaithful

namespace AlgebraicGeometry.BigPHSpaceSite

open Space

variable {S : Scheme.{u}} (P : BigPHSpaceSite S) {A : SimplicialObject.Augmented P.Spaces}

/-- The vertex map `U_0 ⟶ U_0` is proper, being the identity. -/
theorem isProper_vertex_zero :
    Space.IsProper P.fppfSite S P.fppf_mem
      (A.left.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op).hom := by
  rw [SimplexCategory.const_eq_id]
  exact Space.isProper_of_isIso _ _ _ _

/-- The vertex map `U_1 ⟶ U_0` of the vertex `0` of a proper hypercovering is proper: it is the
face `d_1`, the composite of `U_1 ⟶ U_0 ×_X U_0` and of the first projection. -/
theorem isProper_vertex_one (hA : IsProperHypercovering P.fppfSite S P.fppf_mem A) :
    Space.IsProper P.fppfSite S P.fppf_mem
      (A.left.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op).hom := by
  let a₀ := A.hom.app (op ⦋0⦌)
  have hc : SimplexCategory.const ⦋0⦌ ⦋1⦌ 0 = SimplexCategory.δ 1 := by
    ext x
    fin_cases x
    rfl
  have e : A.left.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op =
      (SimplicialObject.Augmented.firstMatchingArrow A).hom ≫ pullback.fst a₀ a₀ := by
    rw [hc, SimplicialObject.Augmented.firstMatchingArrow_hom_fst]
    rfl
  have hfst : Space.IsProper P.fppfSite S P.fppf_mem (pullback.fst a₀ a₀).hom :=
    (Space.isProper_isStableUnderBaseChange P.fppfSite S P.fppf_mem).of_isPullback
      (IsPullback.of_hasPullback a₀ a₀).flip hA.map_zero.1
  rw [e]
  exact Space.isProper_comp' P.fppfSite S P.fppf_mem _ _ (pullback a₀ a₀).property
    (A.left.obj (op ⦋0⦌)).property hA.map_one.1 hfst

/-- The direct image along the augmentation of degree `k` of `(Spaces/U)_{ph, total}` of the
restriction of a sheaf to the degree `k` comes from `X_étale` when the restriction comes from
`U_{k, étale}` and the vertex map `U_k ⟶ U_0` is proper: it is the direct image along the
proper morphisms `U_k ⟶ U_0` and `U_0 ⟶ X` (Stacks 0DGX (1)). -/
theorem mem_essImage_componentAugmentation_pushforward
    (hA : IsProperHypercovering P.fppfSite S P.fppf_mem A) (k : ℕ)
    (hk : Space.IsProper P.fppfSite S P.fppf_mem
      (A.left.map (SimplexCategory.const ⦋0⦌ ⦋k⦌ 0).op).hom)
    (F : Sheaf (SimplicialOver.totalTopology P.topology A.left) (Type (u + 1)))
    (h : (spacesEtaleComparisonMorphism P.topology (A.left.obj (op ⦋k⦌))).inverseImage.essImage
      ((phRestrict A P.topology (op ⦋k⦌)).obj F)) :
    (spacesEtaleComparisonMorphism P.topology A.right).inverseImage.essImage
      ((SimplicialSiteSituation.Augmentation.componentAugmentation
        (SimplicialOver.situation P.topology A.left) (Cat.of (Over A.right))
        (P.topology.over A.right) (SimplicialOver.augmentation P.topology A.left A.hom)
          ⦋k⦌).pushforward.obj
        ((SimplicialOver.situation P.topology A.left).restrict ⦋k⦌ |>.obj F)) :=
  mem_essImage_bigPHMorphism_pushforward P (A.hom.app (op ⦋0⦌)) hA.isProper_zero
    (mem_essImage_bigPHMorphism_pushforward P _ hk h)

/-- **The direct image along the ph augmentation of a sheaf whose restrictions to the degrees `0`
and `1` are étale-type is étale-type.** Let `a : U → X` be a proper hypercovering and `F` a sheaf
on `(Spaces/U)_{ph, total}` whose restrictions to `(Spaces/U_0)_ph` and `(Spaces/U_1)_ph` lie in
the essential images of the inverse images along `U_{n, spaces, étale} → Spaces/U_n`. Then
`a_{ph, *} F` lies in the essential image of the inverse image along `X_{spaces, étale} →
Spaces/X`.

The direct image `a_{ph, *} F` is the equalizer of the direct images of the restrictions of `F`
to the degrees `0` and `1` (Stacks 0D70, compatibility (3)); these are the direct images along the
proper morphisms `U_0 → X` and `U_1 → U_0 → X`, which preserve étale-type sheaves by
Stacks 0DGX (1); and the essential image of the fully faithful exact functor `h_X⁻¹` is closed
under equalizers. -/
theorem mem_essImage_phAugmentation_pushforward
    (hA : IsProperHypercovering P.fppfSite S P.fppf_mem A)
    (F : Sheaf (SimplicialOver.totalTopology P.topology A.left) (Type (u + 1)))
    (h₀ : (spacesEtaleComparisonMorphism P.topology (A.left.obj (op ⦋0⦌))).inverseImage.essImage
      ((phRestrict A P.topology (op ⦋0⦌)).obj F))
    (h₁ : (spacesEtaleComparisonMorphism P.topology (A.left.obj (op ⦋1⦌))).inverseImage.essImage
      ((phRestrict A P.topology (op ⦋1⦌)).obj F)) :
    (spacesEtaleComparisonMorphism P.topology A.right).inverseImage.essImage
      ((SimplicialOver.augmentationMorphismOfTopoi P.topology A.left A.hom).pushforward.obj F) := by
  let a := SimplicialOver.augmentation P.topology A.left A.hom
  have hlim := SimplicialSiteSituation.Augmentation.totalPushforwardForkIsLimit
    (SimplicialOver.situation P.topology A.left) (Cat.of (Over A.right))
    (P.topology.over A.right) a F
  have := isIso_spacesEtaleComparison_unit P A.right
  have hff := (spacesEtaleComparisonMorphism P.topology A.right).adj.fullyFaithfulLOfIsIsoUnit
  have := (spacesEtaleComparisonMorphism P.topology A.right).preservesFiniteLimits
  have hpt := hff.mem_essImage_of_isLimit_fork hlim ?_ ?_
  · exact hpt.ofIso ((CocontinuousSimplicialSite.Augmentation.totalPushforwardIso a).app F)
  · exact mem_essImage_componentAugmentation_pushforward P hA 0 (isProper_vertex_zero P) F h₀
  · exact mem_essImage_componentAugmentation_pushforward P hA 1 (isProper_vertex_one P hA) F h₁

/-- `a⁻¹ : Sh(X_étale) ⥤ Sh(U_étale)` is fully faithful for a proper hypercovering: through the
square of Tag 0DHJ, `h⁻¹ ∘ a⁻¹ = a_ph⁻¹ ∘ h_X⁻¹` is fully faithful (Stacks 0DGT (1) and 0DA8), and
`h⁻¹` is faithful. -/
def fullyFaithfulEtaleAugmentationInverseImage
    (hA : IsProperHypercovering P.fppfSite S P.fppf_mem A) :
    (etaleAugmentationMorphism A).inverseImage.FullyFaithful := by
  have hX := isIso_spacesEtaleComparison_unit P
  have hffh := fullyFaithfulPhComparisonInverseImage (A := A) P.topology hX
  have hffph := SimplicialOver.fullyFaithfulAugmentationInverseImage A.left A.hom
    P.topology.toPretopology (IsProperHypercovering.isHypercoveringAugmentation hA)
    P.toGrothendieck_toPretopology
  haveI := hX A.right
  have hffX := (spacesEtaleComparisonMorphism P.topology A.right).adj.fullyFaithfulLOfIsIsoUnit
  have hcomp := (hffX.comp hffph).ofIso (phEtaleComparisonSquareInverseImageIso P A).symm
  exact @Functor.FullyFaithful.ofCompFaithful _ _ _ _ _ _ _ _ hffh.faithful hcomp

/-- A cartesian sheaf on `U_étale` is in the essential image of `a⁻¹`, for a proper
hypercovering. This is the second half of the proof of Tag 0DHK. -/
theorem mem_essImage_etaleAugmentation_inverseImage
    (hA : IsProperHypercovering P.fppfSite S P.fppf_mem A)
    {G : Sheaf (etaleSimplicialSite A).totalTopology (Type (u + 1))}
    (hG : (etaleSituation A).IsCartesianSheaf G) :
    (etaleAugmentationMorphism A).inverseImage.essImage G := by
  have hX := isIso_spacesEtaleComparison_unit P
  have hffh := fullyFaithfulPhComparisonInverseImage (A := A) P.topology hX
  have hffph := SimplicialOver.fullyFaithfulAugmentationInverseImage A.left A.hom
    P.topology.toPretopology (IsProperHypercovering.isHypercoveringAugmentation hA)
    P.toGrothendieck_toPretopology
  let aph := SimplicialOver.augmentationMorphismOfTopoi P.topology A.left A.hom
  let F' := (phComparisonMorphism A P.topology).inverseImage.obj G
  have hF' := isCartesianOnSections_phComparison_inverseImage (A := A) P.topology hX hG
  obtain ⟨H, ⟨e⟩⟩ := SimplicialOver.mem_essImage_augmentationInverseImage_of_isCartesianOnSections
    A.left A.hom P.topology.toPretopology (IsProperHypercovering.isHypercoveringAugmentation hA)
    P.toGrothendieck_toPretopology F' hF'
  have : IsIso aph.adj.unit :=
    @Adjunction.unit_isIso_of_L_fully_faithful _ _ _ _ _ _ _ hffph.full hffph.faithful
  have hH : (spacesEtaleComparisonMorphism P.topology A.right).inverseImage.essImage H :=
    (mem_essImage_phAugmentation_pushforward P hA F'
      (mem_essImage_phRestrict_inverseImage P.topology (op ⦋0⦌) G)
      (mem_essImage_phRestrict_inverseImage P.topology (op ⦋1⦌) G)).ofIso
      (aph.pushforward.mapIso e.symm ≪≫ (asIso (aph.adj.unit.app H)).symm)
  obtain ⟨H', ⟨e'⟩⟩ := hH
  exact ⟨H', ⟨hffh.preimageIso ((phEtaleComparisonSquareInverseImageIso P A).app H' ≪≫
    aph.inverseImage.mapIso e' ≪≫ e)⟩⟩

/-- **Stacks 0DHK, sheaves of sets.** Let `S` be a scheme, `X` an algebraic space over `S`, `U` a
simplicial algebraic space over `S` and `a : U → X` an augmentation which is a proper hypercovering
of `X`. Then `a⁻¹ : Sh(X_étale) ⥤ Sh(U_étale)` is fully faithful, its essential image consists
exactly of the cartesian sheaves, and `a_*` is a quasi-inverse: the unit of `a⁻¹ ⊣ a_*` is
invertible, and so is its counit at every cartesian sheaf. Here `a : Sh(U_étale) → Sh(X_étale)` is
the morphism of topoi of Section 0DE7, and the category of algebraic spaces over `S` is the one of
a big ph site `P`. -/
@[stacks 0DHK "sheaves of sets"]
theorem etaleAugmentation_inverseImage_fullyFaithful_of_isProperHypercovering
    (hA : IsProperHypercovering P.fppfSite S P.fppf_mem A) :
    (etaleAugmentationMorphism A).inverseImage.Full ∧
      (etaleAugmentationMorphism A).inverseImage.Faithful ∧
      (∀ G, (etaleAugmentationMorphism A).inverseImage.essImage G ↔
        (etaleSituation A).IsCartesianSheaf G) ∧
      (∀ F, IsIso ((etaleAugmentationMorphism A).adj.unit.app F)) ∧
      (∀ G, (etaleSituation A).IsCartesianSheaf G →
        IsIso ((etaleAugmentationMorphism A).adj.counit.app G)) := by
  have hff := fullyFaithfulEtaleAugmentationInverseImage P hA
  have := hff.full
  have := hff.faithful
  have hess : ∀ G, (etaleAugmentationMorphism A).inverseImage.essImage G ↔
      (etaleSituation A).IsCartesianSheaf G := fun G =>
    ⟨fun ⟨K, ⟨e⟩⟩ => SimplicialSiteSituation.isCartesianSheaf_of_iso (etaleSituation A) e
      (SimplicialSiteSituation.Augmentation.isCartesianSheaf_totalMorphismOfTopoi_inverseImage
        (etaleSituation A) _ _ (etaleAugmentation A) K),
      fun hG => mem_essImage_etaleAugmentation_inverseImage P hA hG⟩
  have hunit : IsIso (etaleAugmentationMorphism A).adj.unit :=
    Adjunction.unit_isIso_of_L_fully_faithful _
  exact ⟨hff.full, hff.faithful, hess, fun _ => inferInstance, fun G hG =>
    (etaleAugmentationMorphism A).adj.isIso_counit_app_iff_mem_essImage.2 ((hess G).2 hG)⟩

/-- A morphism of abelian sheaves is invertible when its image in sheaves of sets is. -/
private theorem isIso_of_isIso_forget_map {C : Type (u + 1)} [Category.{u + 1} C]
    {J : GrothendieckTopology C} {F G : Sheaf J AddCommGrpCat.{u + 1}} (f : F ⟶ G)
    (h : IsIso ((sheafCompose J (forget AddCommGrpCat.{u + 1})).map f)) : IsIso f :=
  isIso_of_reflects_iso f (sheafCompose J (forget AddCommGrpCat.{u + 1}))

/-- **Stacks 0DHK, sheaves of abelian groups.** Let `a : U → X` be an augmented simplicial
algebraic space which is a proper hypercovering of `X`. Then the inverse image
`a⁻¹ : Ab(X_étale) ⥤ Ab(U_étale)` on abelian sheaves is fully faithful, its essential image
consists exactly of the cartesian abelian sheaves, and the abelian direct image `a_*` is a
quasi-inverse: the unit of `a⁻¹ ⊣ a_*` is invertible, and so is its counit at every cartesian
abelian sheaf. -/
@[stacks 0DHK "sheaves of abelian groups"]
theorem etaleAugmentation_abelianInverseImage_fullyFaithful_of_isProperHypercovering
    (hA : IsProperHypercovering P.fppfSite S P.fppf_mem A) :
    (Sites.abelianInverseImage (etaleAugmentationMorphism A)).Full ∧
      (Sites.abelianInverseImage (etaleAugmentationMorphism A)).Faithful ∧
      (∀ G, (Sites.abelianInverseImage (etaleAugmentationMorphism A)).essImage G ↔
        (etaleSituation A).IsCartesianAbSheaf G) ∧
      (∀ F, IsIso ((Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward
        (etaleSimplicialSite A).totalTopology (etaleAugmentationMorphism A)).unit.app F)) ∧
      (∀ G, (etaleSituation A).IsCartesianAbSheaf G →
        IsIso ((Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward
          (etaleSimplicialSite A).totalTopology (etaleAugmentationMorphism A)).counit.app G)) := by
  obtain ⟨-, -, -, hunit, hcounit⟩ :=
    etaleAugmentation_inverseImage_fullyFaithful_of_isProperHypercovering P hA
  let JU := (etaleSimplicialSite A).totalTopology
  let JX := SpacesEtale.topology P.fppfSite S P.fppf_mem A.right
  let adj := Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward JU
    (etaleAugmentationMorphism A)
  have hunitAb : ∀ F, IsIso (adj.unit.app F) := fun F => isIso_of_isIso_forget_map _ (by
    rw [Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward_unit_forget JU
      (etaleAugmentationMorphism A) F]
    exact hunit _)
  have hcounitAb : ∀ G, (etaleSituation A).IsCartesianAbSheaf G → IsIso (adj.counit.app G) :=
    fun G hG => isIso_of_isIso_forget_map _ (by
      rw [Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward_counit_forget JU
        (etaleAugmentationMorphism A) G]
      exact hcounit _ hG)
  have : IsIso adj.unit := NatIso.isIso_of_isIso_app _
  have hff := adj.fullyFaithfulLOfIsIsoUnit
  refine ⟨hff.full, hff.faithful, fun G => ⟨fun ⟨K, ⟨e⟩⟩ => ?_, fun hG => ?_⟩, hunitAb,
    hcounitAb⟩
  · exact SimplicialSiteSituation.isCartesianSheaf_of_iso (etaleSituation A)
      ((sheafCompose JU (forget AddCommGrpCat.{u + 1})).mapIso e)
      (SimplicialSiteSituation.Augmentation.isCartesianAbSheaf_totalInverseImageAb
        (etaleSituation A) _ _ (etaleAugmentation A) K)
  · have := hcounitAb G hG
    exact ⟨_, ⟨asIso (adj.counit.app G)⟩⟩

end AlgebraicGeometry.BigPHSpaceSite

end
