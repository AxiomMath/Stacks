module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.EpsilonEssentialImage
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.EtaleComparison
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.InverseImageComparison
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.OpenClosedExactness
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.OpenClosedSequenceShortExact

/-!
# Gluing the essential image of `ε⁻¹` along an open-closed decomposition

Let `X` be an affine scheme, `i : Z ⟶ X` a closed immersion and `j : U ⟶ X` the inclusion of the
complementary open subscheme, assumed quasi-compact. An abelian sheaf `ℱ` on `X_proétale` whose
restrictions `j⁻¹ ℱ` and `i⁻¹ ℱ` come from `U_étale` and `Z_étale` comes from `X_étale`: in the
short exact sequence `0 ⟶ j_! j⁻¹ ℱ ⟶ ℱ ⟶ i_* i⁻¹ ℱ ⟶ 0` (Stacks 09AH) the outer terms come from
the étale site, because `ε⁻¹` commutes with `j_!` (Stacks 09AF) and `i_*` preserves the
essential image of `ε⁻¹`, and the essential image is closed under extensions (Stacks 09B1).

This is the inductive step of the proof of Stacks 09AK.

## Main results

* `AlgebraicGeometry.ProEtale.epsilonInverseImage_essImage_of_restrictions`: the gluing step.

## References

* [Stacks Project, Tag 09AK](https://stacks.math.columbia.edu/tag/09AK)
* [Stacks Project, Tag 09AH](https://stacks.math.columbia.edu/tag/09AH)
* [Stacks Project, Tag 09AF](https://stacks.math.columbia.edu/tag/09AF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.ProEtale

attribute [local instance] proetalePostcompose_isContinuous

/-- **The essential image of `ε⁻¹` is local on the scheme.** A sheaf of sets on `X_proétale`
whose restrictions to the members of an open covering of `X` come from the small étale sites
comes from `X_étale`. -/
theorem etaleTypeInverseImage_essImage_of_openCover {X : Scheme.{u}} {ι : Type*}
    {U : ι → Scheme.{u}} (j : ∀ a, U a ⟶ X) [∀ a, IsOpenImmersion (j a)]
    (hj : ∀ x : X, ∃ a, x ∈ Set.range (j a).base)
    (H : Sheaf (Scheme.ProEt.topology X) (Type (max (u + 1) v)))
    (hH : ∀ a, (Scheme.etaleTypeInverseImage.{v} (U a)).essImage
      (((proetalePostcompose (j a)).sheafPushforwardContinuous (Type (max (u + 1) v))
        (Scheme.ProEt.topology (U a)) (Scheme.ProEt.topology X)).obj H)) :
    (Scheme.etaleTypeInverseImage.{v} X).essImage H := by
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous X.etaleToProetale
    (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)
  have := Scheme.isIso_proetaleInverseImageAdjunction_unit.{u, v} X
  have hff := adj.fullyFaithfulLOfIsIsoUnit
  have : (Scheme.etaleTypeInverseImage.{v} X).Full := hff.full
  have : (Scheme.etaleTypeInverseImage.{v} X).Faithful := hff.faithful
  rw [← adj.isIso_counit_app_iff_mem_essImage]
  let P : ObjectProperty X.ProEt := fun W ↦
    ∃ a, ∃ W' : (U a).ProEt, IsAffineIndEtaleOverEtale (U a) W' ∧
      (proetalePostcompose (j a)).obj W' = W
  refine Sheaf.isIso_of_bijective_of_mem _ P (fun V ↦ ?_) ?_
  · -- the members of the covering, and then objects ind-étale over affine étale schemes
    let 𝒰 : V.left.OpenCover := Scheme.Cover.mkOfCovers ι (fun a ↦ pullback V.hom (j a))
      (fun a ↦ pullback.fst V.hom (j a)) (fun x ↦ by
        obtain ⟨a, y, hy⟩ := hj (V.hom x)
        obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
        exact ⟨a, z, hz⟩)
    let W (a : ι) : X.ProEt := (proetalePostcompose (j a)).obj
      ((Scheme.proetaleBaseChange (j a)).obj V)
    let ιW (a : ι) : W a ⟶ V := MorphismProperty.Over.homMk (pullback.fst V.hom (j a))
      (pullback.condition (f := V.hom) (g := j a)) trivial
    have hT : Sieve.generate (Presieve.ofArrows W ιW) ∈ Scheme.ProEt.topology X V := by
      refine Precoverage.generate_mem_toGrothendieck ?_
      change Presieve.map (Scheme.ProEt.forget X ⋙ Over.forget X) (Presieve.ofArrows W ιW) ∈
        Scheme.proetalePrecoverage _
      rw [Presieve.map_ofArrows]
      have : MorphismProperty.ContainsIdentities (@WeaklyEtale : MorphismProperty Scheme.{u}) :=
        ⟨fun _ ↦ inferInstance⟩
      exact Scheme.zariskiPrecoverage_le_propQCPrecoverage _ 𝒰.mem₀
    refine (Scheme.ProEt.topology X).transitive hT _ fun Y f hf ↦ ?_
    obtain ⟨T, b, c, ⟨a⟩, rfl⟩ := hf
    rw [Sieve.pullback_comp]
    refine (Scheme.ProEt.topology X).pullback_stable b ?_
    refine (Scheme.ProEt.topology X).superset_covering ?_
      ((CoverPreserving.of_isContinuous (proetalePostcompose (j a)) _ _).cover_preserve
        (generate_isAffineIndEtaleOverEtale_mem (U a) ((Scheme.proetaleBaseChange (j a)).obj V)))
    rintro Y' g ⟨T', g₂, g₁, hg₂, rfl⟩
    obtain ⟨T'', a₁, a₂, hT'', rfl⟩ := hg₂
    refine ⟨(proetalePostcompose (j a)).obj T'', g₁ ≫ (proetalePostcompose (j a)).map a₁,
      (proetalePostcompose (j a)).map a₂ ≫ ιW a, ⟨a, T'', hT'', rfl⟩, ?_⟩
    simp only [Category.assoc, Functor.map_comp]
  · rintro _ ⟨a, W', hW', rfl⟩
    obtain ⟨A, _, _, Ub, πU, hUa, ⟨hlim⟩⟩ := hW'.exists_isLimit
    have hA : ∀ {b c : A} (f : b ⟶ c), IsAffineHom (Ub.map f).left := fun {b c} _ ↦
      have := hUa b; have := hUa c; inferInstance
    have hC : ∀ b, CompactSpace (Ub.obj b).left := fun b ↦ have := hUa b; inferInstance
    have hQ : ∀ b, QuasiSeparatedSpace (Ub.obj b).left := fun b ↦ have := hUa b; inferInstance
    obtain ⟨hcol⟩ := @Scheme.nonempty_isColimit_of_mem_essImage (U a) A _ _
      (Ub ⋙ (U a).etaleToProetale) (Cone.mk W' πU) hlim hA hC hQ _ (hH a)
    have := hUa
    rw [← isIso_iff_bijective]
    exact @Scheme.isIso_counit_app_app_of_isColimit X A _ _
      (Ub ⋙ Scheme.Etale.smallEtaleCompose (j a))
      ((proetalePostcompose (j a)).mapCone (Cone.mk W' πU)) hlim hA hC hQ H hcol

/-- Inverse image of abelian pro-étale sheaves along a weakly étale morphism is restriction. -/
def Abelian.proetaleInverseImageIsoRestriction {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j] :
    Abelian.proetaleInverseImage.{u, v} j ≅ Abelian.proetaleRestriction.{u, v} j :=
  (Abelian.proetaleInverseImageDirectImageAdj.{u, v} j).leftAdjointUniq
    ((proetalePostcomposeAdjunction j).sheafPushforwardContinuous _ _)

/-- Inverse image of abelian pro-étale sheaves agrees with the chosen inverse image
`CategoryTheory.Functor.sheafPullback`. -/
def Abelian.proetaleInverseImageIsoSheafPullback {Z X : Scheme.{u}} (g : Z ⟶ X) :
    Abelian.proetaleInverseImage.{u, v} g ≅
      (Scheme.proetaleBaseChange g).sheafPullback AddCommGrpCat.{max (u + 1) v}
        (Scheme.ProEt.topology X) (Scheme.ProEt.topology Z) :=
  (Abelian.proetaleInverseImageDirectImageAdj.{u, v} g).leftAdjointUniq
    ((Scheme.proetaleBaseChange g).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v} _ _)

/-- Inverse image of abelian pro-étale sheaves along a composite is the composite of inverse
images. -/
def Abelian.proetaleInverseImageCompIso {Y Z X : Scheme.{u}} (a : Y ⟶ Z) (b : Z ⟶ X) :
    Abelian.proetaleInverseImage.{u, v} b ⋙ Abelian.proetaleInverseImage.{u, v} a ≅
      Abelian.proetaleInverseImage.{u, v} (a ≫ b) :=
  Functor.isoWhiskerRight (Abelian.proetaleInverseImageIsoSheafPullback b) _ ≪≫
    Functor.isoWhiskerLeft _ (Abelian.proetaleInverseImageIsoSheafPullback a) ≪≫
    Functor.sheafPullbackComp' (Scheme.proetaleBaseChangeCompIso a b) _ _ _ _ ≪≫
    (Abelian.proetaleInverseImageIsoSheafPullback (a ≫ b)).symm

/-- The underlying sheaf of sets of an inverse image of abelian pro-étale sheaves is the inverse
image of the underlying sheaf of sets. -/
def Abelian.forgetProetaleInverseImageIso {Z X : Scheme.{u}} (g : Z ⟶ X)
    (G : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}) :
    (sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v})).obj
        ((Abelian.proetaleInverseImage.{u, v} g).obj G) ≅
      ((Scheme.proetaleBaseChange g).sheafPullback (Type (max (u + 1) v))
        (Scheme.ProEt.topology X) (Scheme.ProEt.topology Z)).obj
        ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v})).obj G) := by
  have (W : Z.ProEtᵒᵖ) : PreservesColimitsOfShape
      (CostructuredArrow (Scheme.proetaleBaseChange g).op W)
      (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v}) := by
    have hf : PreservesFilteredColimitsOfSize.{u, u + 1}
        (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v}) :=
      preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) v, max (u + 1) v, u, u + 1} _
    infer_instance
  exact (sheafCompose (Scheme.ProEt.topology Z)
      (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v})).mapIso
      ((Abelian.proetaleInverseImageIsoSheafPullback g).app G) ≪≫
    ((Scheme.proetaleBaseChange g).sheafPullbackSheafComposeIso AddCommGrpCat.{max (u + 1) v}
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology Z) (CategoryTheory.forget _) G).symm

/-- **Inverse image of abelian sheaves preserves the essential image of `ε⁻¹`.** -/
theorem epsilonInverseImage_essImage_proetaleInverseImage {Z X : Scheme.{u}} (g : Z ⟶ X)
    (G : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v})
    (hG : (epsilonInverseImage.{u, v} X).essImage G) :
    (epsilonInverseImage.{u, v} Z).essImage ((Abelian.proetaleInverseImage.{u, v} g).obj G) := by
  rw [epsilonInverseImage_essImage_iff_forget] at hG ⊢
  exact (Scheme.etaleTypeInverseImage.{v} Z).essImage.prop_of_iso
    (Abelian.forgetProetaleInverseImageIso g G).symm
    (Scheme.etaleTypeInverseImage_essImage_sheafPullback X g _ hG)

/-- Every abelian sheaf on the small pro-étale site of an empty scheme comes from the étale
site: it is zero. -/
theorem epsilonInverseImage_essImage_of_isEmpty {X : Scheme.{u}} [IsEmpty X]
    (G : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}) :
    (epsilonInverseImage.{u, v} X).essImage G := by
  have := isWeakSerreClass_epsilonInverseImage_essImage.{v} X
  obtain ⟨Z₀, hZ₀, hmem⟩ := ObjectProperty.ContainsZero.exists_zero (P :=
    (epsilonInverseImage.{u, v} X).essImage)
  refine (epsilonInverseImage.{u, v} X).essImage.prop_of_iso (hZ₀.iso ?_) hmem
  exact isZero_of_forall_isZero_proetaleSections _ fun V ↦
    have : IsEmpty ((Functor.fromPUnit X).obj V.right) := ‹IsEmpty X›
    isZero_proetaleSections_of_isEmpty _ V ⟨fun x ↦ isEmptyElim (V.hom x)⟩

variable {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
  [QuasiCompact j] (hij : Set.range j.base = (Set.range i.base)ᶜ)

include hij in
/-- **Gluing the essential image of `ε⁻¹`.** Over an affine scheme `X`, an abelian sheaf on
`X_proétale` whose restrictions to a closed subscheme and to its quasi-compact open complement
come from the small étale sites comes from `X_étale`. -/
theorem epsilonInverseImage_essImage_of_restrictions [IsAffine X]
    (F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v})
    (hU : (epsilonInverseImage.{u, v} U).essImage ((Abelian.proetaleRestriction.{u, v} j).obj F))
    (hZ : (epsilonInverseImage.{u, v} Z).essImage ((Abelian.proetaleInverseImage.{u, v} i).obj F)) :
    (epsilonInverseImage.{u, v} X).essImage F := by
  have := isWeakSerreClass_epsilonInverseImage_essImage.{v} X
  refine (epsilonInverseImage.{u, v} X).essImage.prop_X₂_of_shortExact
    (shortExact_openClosedShortComplex i j hij F) ?_ ?_
  · obtain ⟨B, ⟨e⟩⟩ := hU
    exact ⟨(Stacks.EtaleCohomology.extensionByZero.{u, v} j).obj B,
      ⟨epsilonInverseImageExtensionByZeroObjIso j B ≪≫ (Abelian.extensionByZero.{u, v} j).mapIso e⟩⟩
  · rw [epsilonInverseImage_essImage_iff_forget] at hZ ⊢
    exact Scheme.etaleTypeInverseImage_essImage_pushforward X i _ hZ

end AlgebraicGeometry.ProEtale

end
