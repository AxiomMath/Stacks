module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SmallEtaleSite
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.EpsilonEssentialImageStrata
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.LocallyConstantComparison
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleSheaves
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleConstantSheaf

/-!
# Constructible sheaves on the étale and on the pro-étale site

Let `X` be a scheme and `Λ` a Noetherian ring. The inverse image `ε⁻¹` along the comparison
morphism `ε : X_proétale → X_étale` restricts to an equivalence between constructible sheaves of
`Λ`-modules on `X_étale` and constructible sheaves of `Λ`-modules on `X_proétale` (Stacks 09AK).

The functor `ε⁻¹` is fully faithful (Stacks 099T) and commutes with inverse image to the strata
of a constructible partition, so by Stacks 099Y an étale sheaf of `Λ`-modules is constructible
exactly when its inverse image is. For essential surjectivity, a constructible pro-étale sheaf
`ℱ` is shown to lie in the essential image of `ε⁻¹` locally on `X`, so over an affine open `V`.
There its restrictions to the finitely many strata come from the étale sites (Stacks 099Y), the
strata are cut out by finitely many functions on `V` (Stacks 096Y), and the restriction of `ℱ`
to `V` is glued from them by the open-closed exact sequence (Stacks 09AH) and the closedness of
the essential image under extensions (Stacks 09B1).

## Main definitions

* `AlgebraicGeometry.ProEtale.etaleInverseImageConstructible`: `ε⁻¹` between the full
  subcategories of constructible sheaves of `Λ`-modules.

## Main results

* `AlgebraicGeometry.ProEtale.isConstructibleModuleSheaf'_etaleInverseImage_iff`: an étale sheaf
  of `Λ`-modules is constructible exactly when its inverse image under `ε⁻¹` is.
* `AlgebraicGeometry.ProEtale.etaleInverseImage_essImage_of_isConstructibleModuleSheaf'`: every
  constructible pro-étale sheaf of `Λ`-modules comes from the étale site.
* `AlgebraicGeometry.ProEtale.isEquivalence_etaleInverseImageConstructible`: Stacks 09AK.

## References

* [Stacks Project, Tag 09AK](https://stacks.math.columbia.edu/tag/09AK)
* [Stacks Project, Tag 099Y](https://stacks.math.columbia.edu/tag/099Y)
* [Stacks Project, Tag 096Y](https://stacks.math.columbia.edu/tag/096Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology Stacks.ConstantSheaf

universe w v u

namespace AlgebraicGeometry.ProEtale

variable {X : Scheme.{u}} {Λ : Type v} [CommRing Λ]

/-- **`ε⁻¹` preserves and reflects local constancy of finite type after inverse image**, over a
Noetherian ring: for `g : Y ⟶ X` and an étale sheaf `𝒢` on `X`, the pro-étale inverse image of
`ε⁻¹ 𝒢` along `g` is locally constant of finite type exactly when the étale inverse image of `𝒢`
along `g` is (Stacks 099Y). -/
theorem isFiniteTypeLocallyConstantModuleSheaf_proetaleModuleInverseImage_etaleInverseImage_iff
    [IsNoetherianRing Λ] {Y : Scheme.{u}} (g : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v w} Λ)) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max v w, v}
        (Scheme.ProEt.topology Y) Λ ((proetaleModuleInverseImage.{u, v, w} g Λ).obj
          ((Scheme.etaleInverseImage.{u, w, v} X Λ).obj G)) ↔
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max v w, v}
        Y.smallEtaleTopology Λ ((Functor.sheafPullbackConstruction.sheafPullback
          (Stacks.EtaleCohomology.smallEtaleBaseChange g) (ModuleCat.{max (u + 1) v w} Λ)
          X.smallEtaleTopology Y.smallEtaleTopology).obj G) := by
  refine (ObjectProperty.prop_iff_of_iso
      (Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max v w, v}
        (Scheme.ProEt.topology Y) Λ)
      ((Scheme.etaleInverseImageCompSheafPullbackIso X (ModuleCat.{max (u + 1) v w} Λ) g).app G :
        (proetaleModuleInverseImage.{u, v, w} g Λ).obj
          ((Scheme.etaleInverseImage.{u, w, v} X Λ).obj G) ≅ _)).trans ?_
  rw [← isFinitePresentationLocallyConstantModuleSheaf_iff_isFiniteTypeLocallyConstantModuleSheaf,
    ← isFinitePresentationLocallyConstantModuleSheaf_iff_isFiniteTypeLocallyConstantModuleSheaf]
  exact ⟨isFinitePresentationLocallyConstantModuleSheaf_of_etaleInverseImage _,
    isFinitePresentationLocallyConstantModuleSheaf_etaleInverseImage _⟩

/-- **`ε⁻¹` preserves and reflects constructibility.** Over a Noetherian ring, a sheaf of
`Λ`-modules on `X_étale` is constructible exactly when its inverse image on `X_proétale` is. -/
theorem isConstructibleModuleSheaf'_etaleInverseImage_iff [IsNoetherianRing Λ]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v w} Λ)) :
    IsConstructibleModuleSheaf'.{u, v, w} X Λ ((Scheme.etaleInverseImage.{u, w, v} X Λ).obj G) ↔
      Scheme.IsConstructibleEtaleModuleSheaf.{u, v, w} X Λ G :=
  forall_congr' fun _ ↦ exists_congr fun _ ↦ forall_congr' fun _ ↦
    isFiniteTypeLocallyConstantModuleSheaf_proetaleModuleInverseImage_etaleInverseImage_iff _ G

attribute [local instance] proetalePostcompose_isContinuous

/-- **A constructible pro-étale sheaf comes from the étale site over an affine open.** Let `ℱ` be
a sheaf of `Λ`-modules on `X_proétale`, `V` an affine open of `X` and `s` a partition of `V` into
constructible locally closed strata on which `ℱ` is locally constant of finite type. Then the
underlying abelian sheaf of the inverse image of `ℱ` to `V` comes from `V_étale`. -/
theorem epsilonInverseImage_essImage_proetaleInverseImage_of_stratification [IsNoetherianRing Λ]
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)) (V : X.affineOpens)
    (s : Scheme.ConstructibleStratification X V.1)
    (hs : ∀ i, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max v w, v}
      (Scheme.ProEt.topology (s.piece i)) Λ
      ((proetaleModuleInverseImage.{u, v, w} (s.inclusion i) Λ).obj F)) :
    (epsilonInverseImage.{u, max v w} V.1.toScheme).essImage
      ((Abelian.proetaleInverseImage.{u, max v w} V.1.ι).obj
        ((sheafCompose _ (forget₂ (ModuleCat.{max (u + 1) v w} Λ)
          AddCommGrpCat.{max (u + 1) v w})).obj F)) := by
  classical
  let G := (sheafCompose _ (forget₂ (ModuleCat.{max (u + 1) v w} Λ)
    AddCommGrpCat.{max (u + 1) v w})).obj F
  have hsub (k : Fin s.n) : Set.range (s.inclusion k) ⊆ Set.range V.1.ι := by
    rw [Scheme.Opens.range_ι]
    exact s.contained k
  let t (k : Fin s.n) : s.piece k ⟶ V.1.toScheme :=
    IsOpenImmersion.lift V.1.ι (s.inclusion k) (hsub k)
  have ht (k : Fin s.n) : t k ≫ V.1.ι = s.inclusion k := IsOpenImmersion.lift_fac _ _ _
  have : ∀ k, IsImmersion (t k) := fun k ↦ by
    have := s.isImmersion k
    have : IsImmersion (t k ≫ V.1.ι) := by
      rw [ht]
      infer_instance
    exact IsImmersion.of_comp _ V.1.ι
  have hrange (k : Fin s.n) : Set.range (t k) = V.1.ι ⁻¹' Set.range (s.inclusion k) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, by rw [← Scheme.Hom.comp_apply, ht]⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, V.1.ι.isOpenEmbedding.injective (by rw [← Scheme.Hom.comp_apply, ht, hz])⟩
  choose E hE using fun k ↦ exists_finset_determinedBy_of_isConstructible
    (Y := V.1.toScheme) (T := Set.range (t k)) (by rw [hrange]; exact s.constructible k)
  refine epsilonInverseImage_essImage_of_determinedBy.{max v w} _ V.1.toScheme
    (Finset.univ.biUnion E) le_rfl s.piece t (fun y ↦ ?_)
    (fun k ↦ (hE k).mono (Finset.subset_biUnion_of_mem E (Finset.mem_univ k))) _ fun k ↦ ?_
  · have hy : V.1.ι y ∈ (V.1 : Set X) := by
      rw [← Scheme.Opens.range_ι]
      exact Set.mem_range_self y
    rw [s.covers, Set.mem_iUnion] at hy
    obtain ⟨k, hk⟩ := hy
    exact ⟨k, by rw [hrange]; exact hk⟩
  · have hmem : (epsilonInverseImage.{u, max v w} (s.piece k)).essImage
        ((sheafCompose _ (forget₂ (ModuleCat.{max (u + 1) v w} Λ)
          AddCommGrpCat.{max (u + 1) v w})).obj
          ((proetaleModuleInverseImage.{u, v, w} (s.inclusion k) Λ).obj F)) :=
      (Scheme.etaleInverseImage_essImage_iff_forget₂ _ _ _).1
        (etaleInverseImage_essImage_of_isFinitePresentationLocallyConstant _ <|
          (isFinitePresentationLocallyConstantModuleSheaf_iff_isFiniteTypeLocallyConstantModuleSheaf
            _ Λ _).2 (hs k))
    exact (epsilonInverseImage.{u, max v w} (s.piece k)).essImage.prop_of_iso
      (forget₂ProetaleModuleInverseImageIso.{u, v, w} Λ (s.inclusion k) F ≪≫
        eqToIso (congrArg (fun h ↦ (Abelian.proetaleInverseImage.{u, max v w} h).obj G)
          (ht k).symm) ≪≫
        ((Abelian.proetaleInverseImageCompIso.{max v w, u} (t k) V.1.ι).app G).symm) hmem

/-- **Every constructible pro-étale sheaf of `Λ`-modules comes from the étale site**, over a
Noetherian ring. The question is local on `X`, and over an affine open it is
`AlgebraicGeometry.ProEtale.epsilonInverseImage_essImage_proetaleInverseImage_of_stratification`.
-/
theorem etaleInverseImage_essImage_of_isConstructibleModuleSheaf' [IsNoetherianRing Λ]
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ))
    (hF : IsConstructibleModuleSheaf'.{u, v, w} X Λ F) :
    (Scheme.etaleInverseImage.{u, w, v} X Λ).essImage F := by
  rw [Scheme.etaleInverseImage_essImage_iff_forget₂,
    epsilonInverseImage_essImage_iff_forget.{max v w}]
  refine etaleTypeInverseImage_essImage_of_openCover.{max v w}
    (U := fun V : X.affineOpens ↦ V.1.toScheme) (fun V ↦ V.1.ι) (fun x ↦ ?_) _ fun V ↦ ?_
  · obtain ⟨V, hV, hxV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ (⊤ : X.Opens) from trivial)
    exact ⟨⟨V, hV⟩, by rw [Scheme.Opens.range_ι]; exact hxV⟩
  · obtain ⟨s, hs⟩ := hF V
    exact (epsilonInverseImage_essImage_iff_forget.{max v w} _ _).1
      ((epsilonInverseImage.{u, max v w} V.1.toScheme).essImage.prop_of_iso
        ((Abelian.proetaleInverseImageIsoRestriction.{max v w, u} V.1.ι).app _)
        (epsilonInverseImage_essImage_proetaleInverseImage_of_stratification F V s hs))

/-! ### Stacks 09AK -/

variable (X Λ) in
/-- The inverse image `ε⁻¹` of sheaves of `Λ`-modules, restricted to the constructible sheaves on
`X_étale`, with values in the constructible sheaves on `X_proétale`. -/
def etaleInverseImageConstructible [IsNoetherianRing Λ] :
    ObjectProperty.FullSubcategory (Scheme.IsConstructibleEtaleModuleSheaf.{u, v, w} X Λ) ⥤
      ObjectProperty.FullSubcategory (IsConstructibleModuleSheaf'.{u, v, w} X Λ) :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Scheme.etaleInverseImage.{u, w, v} X Λ)
    fun G ↦ (isConstructibleModuleSheaf'_etaleInverseImage_iff G.obj).2 G.property

variable (X Λ) in
/-- **Stacks 09AK.** Let `X` be a scheme and `Λ` a Noetherian ring. The inverse image `ε⁻¹` along
the inclusion of the small étale site into the small pro-étale site defines an equivalence between
the constructible sheaves of `Λ`-modules on `X_étale` and the constructible sheaves of
`Λ`-modules on `X_proétale`.

Constructibility on `X_étale` is `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf` and on
`X_proétale` it is `AlgebraicGeometry.ProEtale.IsConstructibleModuleSheaf'` (Stacks 09AJ). The
functor is fully faithful because the unit of `ε⁻¹ ⊣ ε_*` is invertible (Stacks 099T), and
essentially surjective by
`AlgebraicGeometry.ProEtale.etaleInverseImage_essImage_of_isConstructibleModuleSheaf'` and
`AlgebraicGeometry.ProEtale.isConstructibleModuleSheaf'_etaleInverseImage_iff`. -/
theorem isEquivalence_etaleInverseImageConstructible [IsNoetherianRing Λ] :
    (etaleInverseImageConstructible.{w, v, u} X Λ).IsEquivalence := by
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous X.etaleToProetale
    (ModuleCat.{max (u + 1) v w} Λ) X.smallEtaleTopology (Scheme.ProEt.topology X)
  have hff := adj.fullyFaithfulLOfIsIsoUnit
  have : (Scheme.etaleInverseImage.{u, w, v} X Λ).Full := hff.full
  have : (Scheme.etaleInverseImage.{u, w, v} X Λ).Faithful := hff.faithful
  have : (etaleInverseImageConstructible.{w, v, u} X Λ).Faithful :=
    Functor.Faithful.of_comp_iso (ObjectProperty.liftCompιIso _ _ _)
  have : (etaleInverseImageConstructible.{w, v, u} X Λ).Full :=
    Functor.Full.of_comp_faithful_iso (ObjectProperty.liftCompιIso _ _ _)
  have : (etaleInverseImageConstructible.{w, v, u} X Λ).EssSurj := ⟨fun F ↦ by
    obtain ⟨G, ⟨e⟩⟩ := etaleInverseImage_essImage_of_isConstructibleModuleSheaf' F.obj F.property
    exact ⟨⟨G, (isConstructibleModuleSheaf'_etaleInverseImage_iff G).1
      (ObjectProperty.prop_of_iso _ e.symm F.property)⟩, ⟨ObjectProperty.isoMk _ e⟩⟩⟩
  exact { }

end AlgebraicGeometry.ProEtale

end
