module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AmbientAffineAcyclic07MW
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BasisAnnihilation07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SmoothLiftingZariskiRestriction
public import StacksFrontier.Homology.KFlat.Bifunctor

/-!
# `Ru_{X/S, *}K ≅ Rh_*(K_T)` from a condition on sections over a basis

Fix a global crystalline situation `(p, (S, I, γ), X)` and an object `A = (U, T, δ)` of
`Cris(X/S)`; write `h : T ⟶ X` for the continuous map of
`...SmallSite.CrystallineThickening.ambientToX`, `h_*` for the pushforward of abelian sheaves
along it and `η : u_{X/S, *}G ⟶ h_*(G_T)` for the natural transformation
`...SmallSite.CrystallineThickening.zariskiDirectImageToAmbient`.

Let `K` be a bounded below complex of abelian sheaves on `Cris(X/S)` and `φ : K ⟶ J` a
quasi-isomorphism into a bounded below complex of injective abelian sheaves.  This file proves:

* if, for every open `W` in a basis of the topology of `X`, the map of complexes of abelian groups
  `Γ(W, u_{X/S, *}J) ⟶ Γ(W, h_*(J_T)) = Γ(h⁻¹(W), J_T)` given by `η` termwise is a
  quasi-isomorphism, then the derived transformation
  `Ru_{X/S, *}K ⟶ Rh_*(K_T)` (`...CrystallineThickening.derivedZariskiDirectImageToAmbient`) is an
  isomorphism at `K`, and so is the restriction `RΓ(Cris(X/S), K) ⟶ RΓ(T, K_T)`
  (`...CrystallineThickening.derivedGlobalSectionsToAmbient`);
* for `K = F ⊗ Ω^•_{X/S}` the de Rham complex of a crystal in quasi-coherent modules `F`, and an
  object `A` whose open immersion `U ⟶ X` is surjective (as for the object `(X, Y, γ)` of a smooth
  lifting, whose map to `X` is the identity), the hypothesis for the opens `W` of `X` with
  `h⁻¹(W)` affine — a basis of `X` — implies that the map
  `RΓ(Cris(X/S), F) ⟶ RΓ(T, F_T ⊗ Ω^•_{T/S,δ})` of [Stacks, Equation 07LP]
  (`...SmallSite.crystallineToAmbientDeRham`) is an isomorphism in `D⁺(Ab)`.

## The argument

A morphism of complexes of abelian sheaves on `X_Zar` which is a quasi-isomorphism on sections
over every member of a basis is a quasi-isomorphism (`quasiIso_of_isBasis_sections`): its mapping
cone has, on sections over the basis, acyclic complexes of abelian groups, so its cohomology
sheaves are killed by `1` (`...SmallSite.smul_id_homology_eq_zero_of_isBasis`, the basis lemma of
the proof of [Stacks, Tag 07Q9] with `q = 1`).  So the termwise map `u_{X/S, *}J ⟶ h_*(J_T)` is a
quasi-isomorphism.  The derived transformation at `J` is that termwise map followed by the unit
`h_*(J_T) ⟶ Rh_*(J_T)` (`...CrystallineThickening.derivedZariskiDirectImageToAmbient_fac_app`),
precomposed with the unit `u_{X/S, *}J ⟶ Ru_{X/S, *}J`; both units are invertible, `J` and `J_T`
being complexes of injectives (restriction to `T` preserves injectives,
`...CrystallineThickening.preservesInjectiveObjects_abelianAmbientRestriction`).

## What is and is not proved

Everything above is proved in full.  The sectionwise quasi-isomorphism over the basis is a
hypothesis: it is the per-affine statement proved elsewhere in the proof of part (3) of
[Stacks, Tag 07MW], and this file does not prove it.  No tag attribute is placed.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `quasiIso_of_isBasis_sections` — a morphism of complexes of abelian sheaves on `X_Zar` that is a
  quasi-isomorphism on sections over a basis is a quasi-isomorphism.
* `CrystallineThickening.isBasis_isAffineOpen_ambientToXPreimage` — when `U ⟶ X` is surjective,
  the opens `W` of `X` with `h⁻¹(W)` affine form a basis of `X`.
* `CrystallineThickening.sections_mapHomologicalComplex_zariskiDirectImageToAmbient_f` — in each
  degree, the map of complexes of the hypothesis is `zariskiDirectImageEval` at `A|_{h⁻¹(W)}`.
* `CrystallineThickening.isIso_derivedZariskiDirectImageToAmbient_app_of_quasiIso` and
  `CrystallineThickening.isIso_derivedGlobalSectionsToAmbient_app_of_quasiIso` — part (A).
* `isIso_crystallineToAmbientDeRham_of_quasiIso` and `isIso_crystallineToAmbientDeRham` — part (B),
  for a given resolution and for all resolutions.

## References

* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
* [Stacks Project, Tag 07LP](https://stacks.math.columbia.edu/tag/07LP)
* [Stacks Project, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe w w' w'' w''' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}}

/-- **A morphism of complexes of abelian sheaves on `X_Zar` that is a quasi-isomorphism on
sections over every member of a basis is a quasi-isomorphism.**  Over a basic open `W` the
sections of the mapping cone of `φ` are the mapping cone of `φ(W)`, which is acyclic; so `1` kills
the cohomology sheaves of the mapping cone (`smul_id_homology_eq_zero_of_isBasis`), which is
therefore acyclic. -/
theorem quasiIso_of_isBasis_sections
    {K L : CochainComplex (Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) ℤ} (φ : K ⟶ L)
    {ℬ : Set S.X.Opens} (hℬ : Opens.IsBasis ℬ)
    (h : ∀ W ∈ ℬ, QuasiIso ((((sheafSections (opensTopology S) AddCommGrpCat.{u + 1}).obj
      (op W)).mapHomologicalComplex (ComplexShape.up ℤ)).map φ)) :
    QuasiIso φ := by
  rw [CochainComplex.KFlatBifunctor.quasiIso_iff_acyclic_mappingCone]
  intro j
  rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero,
    ← one_smul ℤ (𝟙 _)]
  refine smul_id_homology_eq_zero_of_isBasis S _ j 1 hℬ fun W hW => ?_
  have hc := (CochainComplex.KFlatBifunctor.quasiIso_iff_acyclic_mappingCone _).1 (h W hW) j
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at hc
  rw [one_smul, ← IsZero.iff_id_eq_zero]
  exact hc.of_iso (HomologicalComplex.homologyMapIso (sectionsMappingConeIso S φ W) j)

namespace CrystallineThickening

variable (A : CrystallineThickening S)

/-- **`h : T ⟶ X` is injective**: it is the inverse of the homeomorphism `U ≃ₜ T` followed by the
open immersion `U ⟶ X`. -/
theorem ambientToX_injective : Function.Injective (ambientToX A) :=
  have : IsOpenImmersion A.obj.toX := A.property
  A.obj.toX.isOpenEmbedding.injective.comp (thickeningHomeomorph A).symm.injective

/-- **`h : T ⟶ X` is an open map**: it is the inverse of the homeomorphism `U ≃ₜ T` followed by the
open immersion `U ⟶ X`. -/
theorem isOpenMap_ambientToX : IsOpenMap (ambientToX A) :=
  have : IsOpenImmersion A.obj.toX := A.property
  A.obj.toX.isOpenEmbedding.isOpenMap.comp (thickeningHomeomorph A).symm.isOpenMap

/-- **The opens `W` of `X` with `h⁻¹(W)` affine form a basis of `X`**, when the open immersion
`U ⟶ X` is surjective.  Around a point `h(t)` of an open `W`, an affine open `V ∋ t` of `T` inside
`h⁻¹(W)` has open image `h(V) ⊆ W`, and `h⁻¹(h(V)) = V` since `h` is injective. -/
theorem isBasis_isAffineOpen_ambientToXPreimage (hA : Function.Surjective A.obj.toX) :
    Opens.IsBasis {W : S.X.Opens | IsAffineOpen (ambientToXPreimage A W)} := by
  rw [Opens.isBasis_iff_nbhd]
  intro W x hx
  obtain ⟨y, rfl⟩ := hA x
  have ht : A.obj.thickening.immersion y ∈ ambientToXPreimage A W := by
    change ambientToX A (A.obj.thickening.immersion y) ∈ W
    rwa [ambientToX_immersion]
  obtain ⟨V, hV, htV, hVW⟩ :=
    Opens.isBasis_iff_nbhd.1 A.obj.thickening.target.scheme.isBasis_affineOpens ht
  let W' : S.X.Opens := ⟨ambientToX A '' V, isOpenMap_ambientToX A _ V.isOpen⟩
  have hW' : ambientToXPreimage A W' = V :=
    Opens.ext (Set.preimage_image_eq _ (ambientToX_injective A))
  refine ⟨W', show IsAffineOpen (ambientToXPreimage A W') from hW' ▸ hV, ?_, ?_⟩
  · exact ⟨_, htV, ambientToX_immersion A y⟩
  · rintro _ ⟨t, htV', rfl⟩
    exact hVW htV'

/-- **The map of complexes in the sectionwise hypothesis, termwise**: in degree `n`, the map
`Γ(W, u_{X/S, *}Jⁿ) ⟶ Γ(h⁻¹(W), (Jⁿ)_T)` is the value of a section at `A|_{h⁻¹(W)}`,
`zariskiDirectImageEval`. -/
theorem sections_mapHomologicalComplex_zariskiDirectImageToAmbient_f
    (J : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℤ) (W : S.X.Opens)
    (n : ℤ) :
    ((((sheafSections (opensTopology S) AddCommGrpCat.{u + 1}).obj
      (op W)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (zariskiDirectImageToAmbient A)
          (ComplexShape.up ℤ)).app J)).f n =
      zariskiDirectImageEval S (forgetToOpens_restrictOpen_ambientToXPreimage_le A W) (J.X n) :=
  rfl

section Derived

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'}
    (Sheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'''} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]

/-- **Part (A) for a complex of injectives.**  Let `J` be a bounded below complex of injective
abelian sheaves on `Cris(X/S)` and `ℬ` a basis of `X` such that, over every `W ∈ ℬ`, the termwise
map `Γ(W, u_{X/S, *}J) ⟶ Γ(W, h_*(J_T))` is a quasi-isomorphism of complexes of abelian groups.
Then `Ru_{X/S, *}J ⟶ Rh_*(J_T)` is an isomorphism. -/
theorem isIso_derivedZariskiDirectImageToAmbient_app_of_injective
    (J : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℤ)
    (hJ : CochainComplex.plus _ J) [∀ n, Injective (J.X n)]
    {ℬ : Set S.X.Opens} (hℬ : Opens.IsBasis ℬ)
    (h : ∀ W ∈ ℬ, QuasiIso ((((sheafSections (opensTopology S) AddCommGrpCat.{u + 1}).obj
      (op W)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (zariskiDirectImageToAmbient A)
          (ComplexShape.up ℤ)).app J))) :
    IsIso ((derivedZariskiDirectImageToAmbient A).app
      (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj ⟨J, hJ⟩))) := by
  let Jh := (HomotopyCategory.Plus.quotient _).obj
    (⟨J, hJ⟩ : CochainComplex.Plus (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}))
  have hη : QuasiIso ((NatTrans.mapHomologicalComplex (zariskiDirectImageToAmbient A)
      (ComplexShape.up ℤ)).app J) :=
    quasiIso_of_isBasis_sections _ hℬ h
  have h1 : IsIso ((zariskiDirectImage S).rightDerivedFunctorPlusUnith.app Jh) := by
    have : ∀ n : ℤ, Injective (Jh.obj.as.X n) := fun n => inferInstanceAs (Injective (J.X n))
    infer_instance
  have h2 : IsIso (DerivedCategory.Plus.Qh.map
      ((Functor.mapHomotopyCategoryPlusNatTrans (zariskiDirectImageToAmbient A)).app Jh)) :=
    Localization.inverts _ (HomotopyCategory.Plus.quasiIso _) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hη)
  have h3 : IsIso ((ambientPushforward A).rightDerivedFunctorPlusUnith.app
      ((abelianAmbientRestriction A).mapHomotopyCategoryPlus.obj Jh)) := by
    have : ∀ n : ℤ, Injective
        (((abelianAmbientRestriction A).mapHomotopyCategoryPlus.obj Jh).obj.as.X n) :=
      fun n => inferInstanceAs (Injective ((abelianAmbientRestriction A).obj (J.X n)))
    infer_instance
  have hfac := derivedZariskiDirectImageToAmbient_fac_app A Jh
  rw [zariskiDirectImageToAmbientComparison_app] at hfac
  have : IsIso ((zariskiDirectImage S).rightDerivedFunctorPlusUnith.app Jh ≫
      (derivedZariskiDirectImageToAmbient A).app (DerivedCategory.Plus.Qh.obj Jh)) := by
    rw [hfac]
    infer_instance
  exact IsIso.of_isIso_comp_left ((zariskiDirectImage S).rightDerivedFunctorPlusUnith.app Jh) _

/-- **Part (A): `Ru_{X/S, *}K ⟶ Rh_*(K_T)` is an isomorphism** for a bounded below complex `K` of
abelian sheaves on `Cris(X/S)` with a quasi-isomorphism `φ : K ⟶ J` into a bounded below complex of
injectives, as soon as, over every member `W` of a basis of `X`, the termwise map
`Γ(W, u_{X/S, *}J) ⟶ Γ(W, h_*(J_T)) = Γ(h⁻¹(W), J_T)` is a quasi-isomorphism of complexes of
abelian groups. -/
theorem isIso_derivedZariskiDirectImageToAmbient_app_of_quasiIso
    {K J : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℤ} (φ : K ⟶ J)
    [QuasiIso φ] (hK : CochainComplex.plus _ K) (hJ : CochainComplex.plus _ J)
    [∀ n, Injective (J.X n)] {ℬ : Set S.X.Opens} (hℬ : Opens.IsBasis ℬ)
    (h : ∀ W ∈ ℬ, QuasiIso ((((sheafSections (opensTopology S) AddCommGrpCat.{u + 1}).obj
      (op W)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (zariskiDirectImageToAmbient A)
          (ComplexShape.up ℤ)).app J))) :
    IsIso ((derivedZariskiDirectImageToAmbient A).app
      (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj ⟨K, hK⟩))) := by
  let φh := (HomotopyCategory.Plus.quotient _).map
    (ObjectProperty.homMk φ :
      (⟨K, hK⟩ : CochainComplex.Plus (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})) ⟶ ⟨J, hJ⟩)
  have : IsIso (DerivedCategory.Plus.Qh.map φh) :=
    Localization.inverts _ (HomotopyCategory.Plus.quasiIso _) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff φ).2
        ((HomologicalComplex.mem_quasiIso_iff φ).2 inferInstance))
  exact (NatTrans.isIso_app_iff_of_iso _ (asIso (DerivedCategory.Plus.Qh.map φh))).2
    (isIso_derivedZariskiDirectImageToAmbient_app_of_injective A J hJ hℬ h)

variable [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]

/-- **Part (A) on derived global sections: `RΓ(Cris(X/S), K) ⟶ RΓ(T, K_T)` is an isomorphism**
under the hypotheses of `isIso_derivedZariskiDirectImageToAmbient_app_of_quasiIso`: it is
`RΓ(X_Zar, -)` of `Ru_{X/S, *}K ⟶ Rh_*(K_T)` between two isomorphisms
(`derivedZariskiDirectImageToAmbient_globalSections`). -/
theorem isIso_derivedGlobalSectionsToAmbient_app_of_quasiIso
    {K J : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℤ} (φ : K ⟶ J)
    [QuasiIso φ] (hK : CochainComplex.plus _ K) (hJ : CochainComplex.plus _ J)
    [∀ n, Injective (J.X n)] {ℬ : Set S.X.Opens} (hℬ : Opens.IsBasis ℬ)
    (h : ∀ W ∈ ℬ, QuasiIso ((((sheafSections (opensTopology S) AddCommGrpCat.{u + 1}).obj
      (op W)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (zariskiDirectImageToAmbient A)
          (ComplexShape.up ℤ)).app J))) :
    IsIso ((derivedGlobalSectionsToAmbient A).app
      (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj ⟨K, hK⟩))) := by
  have := isIso_derivedZariskiDirectImageToAmbient_app_of_quasiIso A φ hK hJ hℬ h
  rw [← derivedZariskiDirectImageToAmbient_globalSections]
  exact IsIso.comp_isIso' inferInstance
    (IsIso.comp_isIso'
      (Iso.isIso_hom ((derivedZariskiGlobalSectionsFunctor S).mapIso (@asIso _ _ _ _ _ this)))
      inferInstance)

end Derived

end CrystallineThickening

/-! ### Part (B): the map of [Stacks, Equation 07LP] -/

section DeRham

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {F : SheafOfModules.{u} (structureSheaf S)} (hF : F.IsQuasicoherentOnSite)
  (A : CrystallineThickening S)
  [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'}
    (Sheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'''} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]

/-- **Part (B), for a given resolution: the map of [Stacks, Equation 07LP] is an isomorphism.**
Let `F` be a crystal in quasi-coherent modules, `A = (U, T, δ)` an object of `Cris(X/S)` whose
open immersion `U ⟶ X` is surjective, and `φ : F ⊗ Ω^•_{X/S} ⟶ J` a quasi-isomorphism into a
bounded below complex of injective abelian sheaves.  If, for every open `W` of `X` with `h⁻¹(W)`
affine, the termwise map `Γ(W, u_{X/S, *}J) ⟶ Γ(h⁻¹(W), J_T)` is a quasi-isomorphism, then
`RΓ(Cris(X/S), F) ⟶ RΓ(T, F_T ⊗ Ω^•_{T/S,δ})` is an isomorphism: it is the restriction of global
cohomology classes of `F ⊗ Ω^•_{X/S}` between two isomorphisms. -/
theorem isIso_crystallineToAmbientDeRham_of_quasiIso
    {J : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℤ}
    (φ : (crystalDeRhamSheafData hF).complex ⟶ J) [QuasiIso φ] (hJ : CochainComplex.plus _ J)
    [∀ n, Injective (J.X n)] (hA : Function.Surjective A.obj.toX)
    (h : ∀ W : S.X.Opens, IsAffineOpen (CrystallineThickening.ambientToXPreimage A W) →
      QuasiIso ((((sheafSections (opensTopology S) AddCommGrpCat.{u + 1}).obj
        (op W)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex (CrystallineThickening.zariskiDirectImageToAmbient A)
            (ComplexShape.up ℤ)).app J))) :
    IsIso (crystallineToAmbientDeRham hF A) := by
  have : IsIso ((CrystallineThickening.derivedGlobalSectionsToAmbient A).app
      (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj
        (crystalDeRhamSheafData hF).complexPlus))) :=
    CrystallineThickening.isIso_derivedGlobalSectionsToAmbient_app_of_quasiIso A φ
      (crystalDeRhamSheafData hF).complexPlus.2 hJ
      (CrystallineThickening.isBasis_isAffineOpen_ambientToXPreimage A hA) h
  dsimp only [crystallineToAmbientDeRham, CrystalDeRhamSheafData.comparison07LP]
  exact IsIso.comp_isIso' (Iso.isIso_hom _) (IsIso.comp_isIso' this inferInstance)

/-- **Part (B): the map of [Stacks, Equation 07LP] is an isomorphism**, for an object
`A = (U, T, δ)` whose open immersion `U ⟶ X` is surjective, as soon as the hypothesis of
`isIso_crystallineToAmbientDeRham_of_quasiIso` holds for every quasi-isomorphism from
`F ⊗ Ω^•_{X/S}` into a bounded below complex of injective abelian sheaves; such a
quasi-isomorphism exists (`CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective`). -/
theorem isIso_crystallineToAmbientDeRham (hA : Function.Surjective A.obj.toX)
    (h : ∀ (J : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℤ)
      (φ : (crystalDeRhamSheafData hF).complex ⟶ J), QuasiIso φ → CochainComplex.plus _ J →
      (∀ n, Injective (J.X n)) →
      ∀ W : S.X.Opens, IsAffineOpen (CrystallineThickening.ambientToXPreimage A W) →
        QuasiIso ((((sheafSections (opensTopology S) AddCommGrpCat.{u + 1}).obj
          (op W)).mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((NatTrans.mapHomologicalComplex
              (CrystallineThickening.zariskiDirectImageToAmbient A)
              (ComplexShape.up ℤ)).app J))) :
    IsIso (crystallineToAmbientDeRham hF A) := by
  obtain ⟨J, φ, hφ, hJinj, hJ⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective
      (crystalDeRhamSheafData hF).complex 0
  have := hφ
  have := hJinj
  exact isIso_crystallineToAmbientDeRham_of_quasiIso hF A φ ⟨0, hJ⟩ hA
    (h J φ hφ ⟨0, hJ⟩ hJinj)

end DeRham

end Crystalline.GlobalCrystallineSituation.SmallSite
