module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AdequateSectionsCohomology
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.ZariskiRestriction
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicPreservesHomologyInt
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.SectionsOverObjectTruncationEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.LocallyBijectiveHomology
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackToposGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.BoundedBelowEdgeIsomorphism

/-!
# The derived direct image of a complex with adequate cohomology

Let `S` be a scheme, `(Sch/S)_τ` a chosen big site over `S`, and
`f : ((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)` the morphism of [Stacks, Tag 070U]. This file proves that the
derived direct image `Rf_*` carries `D_Adeq(𝒪)` into `D_QCoh(S)`, which is the first landing
assertion of [Stacks, Tag 070W].

## The argument

Let `K` be an object of `D_Adeq(𝒪)`, represented by a K-injective complex `I`, so that `Rf_*K` is
represented by `f_*I`. Fix a degree `n` and truncate: `τ_{≥ -m}K` for `m` large is represented by
a strictly bounded below complex `J` of injective modules, and the truncation map is represented
by a map of complexes `t : I ⟶ J`.

* `Hⁿ(f_*t)` is an isomorphism. This is local on `S`: over an affine open `V` it is the map
  `Hⁿ(I(V)) ⟶ Hⁿ(J(V))` of the cohomology over the affine object `V` of the site, which is the
  map `Hⁿ(V, K) ⟶ Hⁿ(V, τ_{≥ -m}K)`, invertible for `m` large because the higher cohomology of
  an adequate module over an affine object vanishes ([Stacks, Tag 06VM] (3)) and `K` is the
  derived limit of its truncations ([Stacks, Tag 0D6S]).
* `Hⁿ(f_*J) ≅ f_*Hⁿ(J)`, because the terms of `J` are injective and its cohomology modules are
  adequate, so all are acyclic for `f_*` ([Stacks, Tag 06VM]), and an acyclic functor preserves
  the homology of a bounded below complex of acyclic objects with acyclic homology.
* `f_*Hⁿ(J)` is quasi-coherent: `Hⁿ(J) = Hⁿ(K)` is adequate and its restriction to `S_Zar` is
  quasi-coherent by [Stacks, Tag 06VM] (1).

## Main results

* `Stacks.Adequate.BigSite.rightAcyclic_restrictModuleOfSheaf_of_isAdequate`: an adequate module
  is acyclic for the restriction `f_*` to the small Zariski site.
* `Stacks.Adequate.BigSite.nonempty_homology_derivedZariskiPushforward_iso`: `Hⁿ(Rf_*K) ≅ f_*Hⁿ(K)`
  for `K` in `D_Adeq(𝒪)`.
* `Stacks.Adequate.BigSite.isQuasicoherent_homology_derivedZariskiPushforward`: the cohomology
  sheaves of `Rf_*K` are quasi-coherent for `K` in `D_Adeq(𝒪)`.

## References

* [Stacks Project, Tag 070W](https://stacks.math.columbia.edu/tag/070W)
* [Stacks Project, Tag 06VM](https://stacks.math.columbia.edu/tag/06VM)
* [Stacks Project, Tag 0D6S](https://stacks.math.columbia.edu/tag/0D6S)
* [Stacks Project, Tag 0157](https://stacks.math.columbia.edu/tag/0157)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)

attribute [local instance] Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite
  Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### Acyclicity of adequate modules for the restriction to the small Zariski site -/

/-- **An adequate module is acyclic for the restriction `f_*` to the small Zariski site.** The
higher right derived functors of restriction of modules, read on underlying abelian sheaves, are
those of restriction of abelian sheaves, an injective module being acyclic for the latter; and
those vanish at an adequate module by [Stacks, Tag 06VM]. -/
theorem BigSite.rightAcyclic_restrictModuleOfSheaf_of_isAdequate
    [HasDerivedCategory (SheafOfModules.{u} B.structureSheaf)]
    [HasDerivedCategory (SheafOfModules.{u} S.ringCatSheaf)]
    (F : SheafOfModules.{u} B.structureSheaf) (hF : IsAdequate B F) :
    B.restrictModuleOfSheaf.rightAcyclic F := by
  let := HasDerivedCategory.standard (Sheaf B.topology AddCommGrpCat.{u})
  let := HasDerivedCategory.standard (Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{u})
  rw [Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat]
  intro n hn
  let T := SheafOfModules.toSheaf.{u} S.ringCatSheaf
  have hFG : ∀ I : SheafOfModules.{u} B.structureSheaf, Injective I →
      B.zariskiRestriction.rightAcyclic ((SheafOfModules.toSheaf B.structureSheaf).obj I) := by
    intro I hI
    rw [Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat]
    intro q hq
    refine B.isZero_rightDerived_zariskiRestriction _ (fun U _ q' hq' ↦ ?_) q hq
    obtain ⟨k, rfl⟩ : ∃ k, q' = k + 1 := ⟨q' - 1, by omega⟩
    open Stacks.Cohomology.InjectiveModuleSheafAcyclicity in
    exact isZero_rightDerived_sections_toSheaf_succAtMorphismUniverse.{u}
      B.topology B.structureSheaf I (B.opensToBig.obj U) k
  have hcomp : B.restrictModuleOfSheaf ⋙ T ≅
      SheafOfModules.toSheaf B.structureSheaf ⋙ B.zariskiRestriction := Iso.refl _
  have hz : IsZero (T.obj ((B.restrictModuleOfSheaf.rightDerived n).obj F)) :=
    (B.higherZariskiRestrictionVanishing F hF n hn).of_iso
      ((Stacks.Cohomology.rightDerivedExactPostcompositionIso B.restrictModuleOfSheaf T F n).trans
        (((Stacks.Cohomology.rightDerivedIsoOfFunctorIso hcomp n).app F).trans
          (Stacks.Cohomology.AffineComparison.rightDerivedCollapseIso
            (SheafOfModules.toSheaf B.structureSheaf) B.zariskiRestriction hFG F
            (Functor.rightAcyclic_of_exact _ F) n)))
  refine (IsZero.iff_id_eq_zero _).2 (T.map_injective ?_)
  rw [T.map_id, T.map_zero]
  exact hz.eq_of_src _ _

/-! ### Homology isomorphisms of complexes of `𝒪_S`-modules are detected on affine opens -/

/-- The coverings of an open of a scheme by affine opens, as a cofinal system of coverings. -/
def _root_.AlgebraicGeometry.Scheme.affineCoveringSystem (X : Scheme.{u}) (V : X.Opens) :
    Stacks.Cohomology.CofinalCoveringSystem (Opens.grothendieckTopology ↥X) V where
  cov 𝒰 := 𝒰 ∈ X.affineCoverings V
  isCover _ h := X.sieve₀_mem_of_mem_affineCoverings h
  cofinal 𝒰 h𝒰 := X.exists_mem_affineCoverings_nonempty_hom 𝒰 h𝒰

/-- **A map of complexes of `𝒪_X`-modules on a scheme is an isomorphism on the degree-`j`
homology sheaves as soon as it is so on the homology of the sections over every affine open.**
The homology sheaf is the sheafification of the presheaf-level homology, and a map of presheaves
which is bijective on the affine opens, a basis of the topology, is locally bijective. -/
theorem _root_.AlgebraicGeometry.Scheme.isIso_homologyMap_of_isIso_evaluation_affine
    (X : Scheme.{u}) {M N : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ} (g : M ⟶ N)
    (j : ℤ)
    (hg : ∀ V : X.Opens, IsAffineOpen V →
      IsIso ((HomologicalComplex.homologyFunctor _ (.up ℤ) j).map
        (((_root_.SheafOfModules.evaluation X.ringCatSheaf (op V)).mapHomologicalComplex
          (.up ℤ)).map g))) :
    IsIso ((HomologicalComplex.homologyFunctor _ (.up ℤ) j).map g) := by
  rw [Stacks.Cohomology.isIso_homologyMap_iff_w]
  refine Stacks.Cohomology.w_of_cofinal_local_isomorphisms (Opens.grothendieckTopology ↥X)
    X.affineOpens (fun U ↦ ⟨X.affineZeroHypercover U, X.affineZeroHypercover_sieve₀_mem U,
      fun i ↦ X.isAffineOpen_affineZeroHypercover_X U i⟩)
    (fun V _ ↦ X.affineCoveringSystem V) _ (fun V _ ↦ ⟨_, _, 𝟙 _, Category.comp_id _,
      MorphismProperty.id_mem _ _, fun 𝒰 h𝒰 i ↦ ?_⟩)
  exact Stacks.Cohomology.isIso_presheaf_homologyMap_app_of_evaluation X.ringCatSheaf g j _
    (hg _ (X.isAffineOpen_of_mem_affineCoverings h𝒰 i))

/-! ### Truncation and sections over an affine object -/

open Stacks.Cohomology.Localization.OfEssentiallySmall in
attribute [local instance 2000] HasDerivedCategory.standard in
/-- **Truncating a complex with adequate cohomology does not change its cohomology over an affine
object in the degrees above the truncation.** Let `K` be in `D_Adeq(𝒪)`, represented by a
K-injective complex `I`, let `J` be a K-injective complex representing `τ_{≥ -m}K` and `t : I ⟶ J`
a map of complexes representing the truncation. Then `t` induces an isomorphism on the degree-`n`
cohomology of the sections over an affine object as soon as `m ≥ 1 - n`.

The cohomology of the sections of a K-injective complex over `W` is the cohomology over `W` of the
object of the derived category it represents; so this is the local truncation lemma of
[Stacks, Tag 0D6W] for the Olsson--Laszlo situation of the adequate modules, whose derived-limit
hypothesis is [Stacks, Tag 0D6S]. -/
theorem BigSite.isIso_homologyMap_sectionsOver_of_truncGE
    (K : DerivedCategory (SheafOfModules.{u} B.structureSheaf))
    (hK : DerivedCategoryB.derivedCategoryB (adequate.{u, u} B) K)
    (I J : CochainComplex (SheafOfModules.{u} B.structureSheaf) ℤ) [I.IsKInjective]
    [J.IsKInjective] (m : ℕ)
    (e : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I) ≅ K)
    (ε : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj J) ≅
      (DerivedCategory.TStructure.t.truncGE (-(m : ℤ))).obj K)
    (t : I ⟶ J)
    (ht : DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map t) =
      e.hom ≫ (DerivedCategory.TStructure.t.truncGEπ (-(m : ℤ))).app K ≫ ε.inv)
    (W : B.category) [IsAffine W.left.obj] (n : ℤ) (hn : 1 - n ≤ (m : ℤ)) :
    IsIso ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℤ) n).map
      (((B.sectionsOver W).mapHomologicalComplex (.up ℤ)).map t)) := by
  let RΓ := derivedSectionsOverObject B.topology B.structureSheaf W
  let α := Stacks.Cohomology.OlssonLaszlo.OfEssentiallySmall.derivedSectionsOverObjectUnit
    B.topology B.structureSheaf W
  have h1 : IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
      (RΓ.map ((DerivedCategory.TStructure.t.truncGEπ (-(m : ℤ))).app K))) :=
    Cohomology.OlssonLaszlo.OfEssentiallySmall.isIso_homologyMap_derivedSectionsOverObject_truncGEπ
      B.topology B.structureSheaf W (adequate.{u, u} B) K hK 0
      (fun p hp F hF ↦ B.isZero_moduleCohomology_of_isAdequate F hF W p (by exact_mod_cast hp))
      (fun L c pr δ hT hc ↦
        Stacks.Cohomology.isIso_to_isDerivedLimit_truncGETower_of_derivedCategoryB
          B.adequateOlssonLaszlo K hK L pr ⟨δ, hT⟩ c hc)
      n m (by omega) (by omega)
  have h2 : IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
      (RΓ.map (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map t)))) := by
    simp only [ht, Functor.map_comp]
    infer_instance
  have hI : IsIso (α.app ((HomotopyCategory.quotient _ _).obj I)) :=
    Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective _ DerivedCategory.Qh RΓ α I
      inferInstance
  have hJ : IsIso (α.app ((HomotopyCategory.quotient _ _).obj J)) :=
    Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective _ DerivedCategory.Qh RΓ α J
      inferInstance
  have h3 : IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
      ((homotopySectionsOverObject B.topology B.structureSheaf W).map
        ((HomotopyCategory.quotient _ _).map t))) := by
    have : (homotopySectionsOverObject B.topology B.structureSheaf W).map
        ((HomotopyCategory.quotient _ _).map t) =
        (α.app _ ≫ RΓ.map (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map t))) ≫
          inv (α.app _) := by
      rw [IsIso.eq_comp_inv]
      exact α.naturality _
    rw [this, Functor.map_comp, Functor.map_comp]
    infer_instance
  have h4 : IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        (((B.sectionsOver W).mapHomologicalComplex (.up ℤ)).map t)))) := h3
  exact (NatIso.isIso_map_iff (HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{u} (.up ℤ) n)
    (((B.sectionsOver W).mapHomologicalComplex (.up ℤ)).map t)).1
    ((NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactorsh AddCommGrpCat.{u} n)
      ((HomotopyCategory.quotient _ _).map
        (((B.sectionsOver W).mapHomologicalComplex (.up ℤ)).map t))).1 h4)

attribute [local instance 2000] HasDerivedCategory.standard in
/-- **Truncating a complex with adequate cohomology does not change the cohomology of its
restriction to the small Zariski site in the degrees above the truncation.** With the notation
of `Stacks.Adequate.BigSite.isIso_homologyMap_sectionsOver_of_truncGE`, the map `t` induces an
isomorphism on `Hⁿ(f_*I) ⟶ Hⁿ(f_*J)` as soon as `m ≥ 1 - n`, this being checked on the sections
over the affine opens of `S`. -/
private theorem BigSite.isIso_homologyMap_restrictModuleOfSheaf_of_truncGE
    (K : DerivedCategory (SheafOfModules.{u} B.structureSheaf))
    (hK : DerivedCategoryB.derivedCategoryB (adequate.{u, u} B) K)
    (I J : CochainComplex (SheafOfModules.{u} B.structureSheaf) ℤ) [I.IsKInjective]
    [J.IsKInjective] (m : ℕ)
    (e : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I) ≅ K)
    (ε : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj J) ≅
      (DerivedCategory.TStructure.t.truncGE (-(m : ℤ))).obj K)
    (t : I ⟶ J)
    (ht : DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map t) =
      e.hom ≫ (DerivedCategory.TStructure.t.truncGEπ (-(m : ℤ))).app K ≫ ε.inv)
    (n : ℤ) (hn : 1 - n ≤ (m : ℤ)) :
    IsIso ((HomologicalComplex.homologyFunctor _ (.up ℤ) n).map
      ((B.restrictModuleOfSheaf.mapHomologicalComplex (.up ℤ)).map t)) := by
  refine S.isIso_homologyMap_of_isIso_evaluation_affine _ n (fun V hV ↦ ?_)
  have : IsAffine (B.opensToBig.obj V).left.obj := hV
  let G := B.restrictModuleOfSheaf
  let E := _root_.SheafOfModules.evaluation S.ringCatSheaf (op V)
  let F₂ := forget₂ (ModuleCat.{u} (S.ringCatSheaf.obj.obj (op V))) AddCommGrpCat.{u}
  have h : IsIso ((HomologicalComplex.homologyFunctor _ (.up ℤ) n).map
      ((F₂.mapHomologicalComplex (.up ℤ)).map
        ((E.mapHomologicalComplex (.up ℤ)).map ((G.mapHomologicalComplex (.up ℤ)).map t)))) :=
    B.isIso_homologyMap_sectionsOver_of_truncGE K hK I J m e ε t ht (B.opensToBig.obj V) n hn
  have : IsIso (F₂.map ((HomologicalComplex.homologyFunctor _ (.up ℤ) n).map
      ((E.mapHomologicalComplex (.up ℤ)).map ((G.mapHomologicalComplex (.up ℤ)).map t)))) :=
    (NatIso.isIso_map_iff (Stacks.Homology.exactHomologyIso F₂ n)
      ((E.mapHomologicalComplex (.up ℤ)).map ((G.mapHomologicalComplex (.up ℤ)).map t))).1 h
  exact isIso_of_reflects_iso _ F₂

/-! ### The landing of `Rf_*` -/

attribute [local instance 2000] HasDerivedCategory.standard in
/-- **The cohomology of `Rf_*K` is that of `f_*I`** for a K-injective complex `I` representing
`K`. -/
private theorem BigSite.nonempty_homology_derivedZariskiPushforward_iso_of_isKInjective
    (K : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf B.ringedSite.toRingedTopos.O)))
    (I : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf B.ringedSite.toRingedTopos.O)) ℤ) [I.IsKInjective]
    (e : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I) ≅ K) (n : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.toRingedTopos.O)) n).obj
        (B.derivedZariskiPushforward.obj K) ≅
      ((B.restrictModuleOfSheaf.mapHomologicalComplex (.up ℤ)).obj I).homology n) := by
  let f := B.zariskiRingedToposHom
  let A := SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf B.ringedSite.toRingedTopos.O)
  let G : A ⥤ SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.toRingedTopos.O) :=
    B.zariskiRingedSiteHom.toRingedToposSiteHom.pushforwardTopos
  let eG : f.pushforwardModules ≅ G := B.zariskiRingedSiteHom.pushforwardToposIsoGeneral
  have : G.Additive := BigSite.additive_restrictModuleOfSheaf B
  have : PreservesFiniteLimits G := BigSite.preservesFiniteLimits_restrictModuleOfSheaf B
  have : f.pushforwardModules.Additive := Functor.additive_of_iso eG.symm
  let α := (Stacks.Cohomology.DerivedPushforward.pushforwardOnHomotopy f).totalRightDerivedUnit
    DerivedCategory.Qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
  have hα : IsIso (α.app ((HomotopyCategory.quotient A _).obj I)) :=
    Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective _ DerivedCategory.Qh _ α I
      inferInstance
  let Hn := DerivedCategory.homologyFunctor (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.toRingedTopos.O)) n
  exact ⟨Hn.mapIso (B.derivedZariskiPushforward.mapIso e.symm) ≪≫
    Hn.mapIso (asIso (α.app ((HomotopyCategory.quotient A _).obj I))).symm ≪≫
    (DerivedCategory.homologyFunctorFactorsh _ n).app _ ≪≫
    (HomotopyCategory.homologyFunctorFactors _ (ComplexShape.up ℤ) n).app _ ≪≫
    (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).mapIso
      ((NatIso.mapHomologicalComplex eG (ComplexShape.up ℤ)).app I)⟩

/-- The degree-`q` cohomology of `K` agrees with that of a complex `J` representing `τ_{≥ a}K`,
for `a ≤ q`. -/
private def homologyIsoOfIsoTruncGE {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (K : DerivedCategory C) {a q : ℤ} (hq : a ≤ q)
    {J : CochainComplex C ℤ}
    (φ : (DerivedCategory.TStructure.t.truncGE a).obj K ≅ DerivedCategory.Q.obj J) :
    (DerivedCategory.homologyFunctor C q).obj K ≅ J.homology q :=
  @asIso _ _ _ _ ((DerivedCategory.homologyFunctor C q).map
      ((DerivedCategory.TStructure.t.truncGEπ a).app K))
      (DerivedCategory.isIso_homologyMap_truncGEπ_app a q hq K) ≪≫
    (DerivedCategory.homologyFunctor C q).mapIso φ ≪≫
    (DerivedCategory.homologyFunctorFactors C q).app J

attribute [local instance 2000] HasDerivedCategory.standard in
/-- **A strictly bounded below complex representing the truncation `τ_{≥ a}K` of a complex `K`
with adequate cohomology has adequate cohomology.** -/
private theorem BigSite.isAdequate_homology_of_iso_truncGE
    (K : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf B.ringedSite.toRingedTopos.O)))
    (hK : DerivedCategoryB.derivedCategoryB (adequate.{u, u} B) K) (a : ℤ)
    (J : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf B.ringedSite.toRingedTopos.O)) ℤ) [J.IsStrictlyGE a]
    (φ : (DerivedCategory.TStructure.t.truncGE a).obj K ≅ DerivedCategory.Q.obj J) (q : ℤ) :
    IsAdequate B (J.homology q) := by
  have := adequate_isWeakSerreClass B
  by_cases hq : a ≤ q
  · exact (adequate.{u, u} B).prop_of_iso (homologyIsoOfIsoTruncGE K hq φ) (hK q)
  · exact (adequate.{u, u} B).prop_of_isZero (ShortComplex.isZero_homology_of_isZero_X₂
      (J.sc q) (J.isZero_of_isStrictlyGE a q (by omega)))

attribute [local instance 2000] HasDerivedCategory.standard in
/-- **The cohomology sheaves of `Rf_*K` for `K` in `D_Adeq(𝒪)`**: `Hⁿ(Rf_*K) ≅ f_*Hⁿ(K)`, where
`f_*` is restriction to the small Zariski site. -/
theorem BigSite.nonempty_homology_derivedZariskiPushforward_iso
    (K : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf B.ringedSite.toRingedTopos.O)))
    (hK : DerivedCategoryB.derivedCategoryB (adequate.{u, u} B) K) (n : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.toRingedTopos.O)) n).obj
        (B.derivedZariskiPushforward.obj K) ≅
      B.zariskiRingedSiteHom.toRingedToposSiteHom.pushforwardTopos.obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf B.ringedSite.toRingedTopos.O)) n).obj K)) := by
  let A := SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf B.ringedSite.toRingedTopos.O)
  let G : A ⥤ SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.toRingedTopos.O) :=
    B.zariskiRingedSiteHom.toRingedToposSiteHom.pushforwardTopos
  have : G.Additive := BigSite.additive_restrictModuleOfSheaf B
  have : PreservesFiniteLimits G := BigSite.preservesFiniteLimits_restrictModuleOfSheaf B
  obtain ⟨I, hI, ⟨e⟩⟩ := Stacks.Cohomology.UnboundedComplexes.exists_isKInjective_iso.{u}
    (A := A) DerivedCategory.Qh K
  have : I.IsKInjective := hI
  obtain ⟨e₁⟩ := B.nonempty_homology_derivedZariskiPushforward_iso_of_isKInjective K I e n
  let m : ℕ := (1 - n).toNat
  let Y := (DerivedCategory.TStructure.t.truncGE (-(m : ℤ))).obj K
  have : Y.IsGE (-(m : ℤ)) :=
    inferInstanceAs (((DerivedCategory.TStructure.t.truncGE (-(m : ℤ))).obj K).IsGE _)
  obtain ⟨L₀, hL₀, ⟨eY⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE Y (-(m : ℤ))
  obtain ⟨J, i, hi, hJinj, hJ⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective L₀ (-(m : ℤ))
  have := hJ
  have := hJinj
  have : J.IsKInjective := CochainComplex.isKInjective_of_injective J (-(m : ℤ))
  let φ : Y ≅ DerivedCategory.Q.obj J := eY ≪≫ asIso (DerivedCategory.Q.map i)
  let ε : DerivedCategory.Qh.obj ((HomotopyCategory.quotient A _).obj J) ≅ Y :=
    (DerivedCategory.quotientCompQhIso A).app J ≪≫ φ.symm
  obtain ⟨t', ht'⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient A _).obj I) J).2
    (e.hom ≫ (DerivedCategory.TStructure.t.truncGEπ (-(m : ℤ))).app K ≫ ε.inv)
  obtain ⟨t, rfl⟩ := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_surjective t'
  have ha := @BigSite.isIso_homologyMap_restrictModuleOfSheaf_of_truncGE _ _ B K hK I J hI
      (inferInstanceAs J.IsKInjective) m e ε t ht' n (by omega)
  let e₂ : ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj J).homology n ≅
      G.obj (J.homology n) :=
    G.homologyMapIsoOfRightAcyclic J (-(m : ℤ))
      (fun k ↦ Stacks.BoundedBelowEdge.rightAcyclic_of_injective G (J.X k))
      (fun q ↦ B.rightAcyclic_restrictModuleOfSheaf_of_isAdequate _
        (B.isAdequate_homology_of_iso_truncGE K hK (-(m : ℤ)) J φ q)) n
  exact ⟨e₁ ≪≫ @asIso _ _ _ _ _ ha ≪≫ e₂ ≪≫
    G.mapIso (homologyIsoOfIsoTruncGE K (by omega) φ).symm⟩

attribute [local instance 2000] HasDerivedCategory.standard in
/-- **[Stacks, Tag 070W], the landing of `Rf_*`.** For `K` in `D_Adeq(𝒪)` on a chosen big site
over `S`, every cohomology sheaf of `Rf_*K` is a quasi-coherent `𝒪_S`-module, `f` being the
morphism of [Stacks, Tag 070U]. -/
theorem BigSite.isQuasicoherent_homology_derivedZariskiPushforward
    (K : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf B.ringedSite.toRingedTopos.O)))
    (hK : DerivedCategoryB.derivedCategoryB (adequate.{u, u} B) K) (n : ℤ) :
    SheafOfModules.isQuasicoherent S.ringCatSheaf
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.toRingedTopos.O)) n).obj
        (B.derivedZariskiPushforward.obj K)) := by
  obtain ⟨e⟩ := B.nonempty_homology_derivedZariskiPushforward_iso K hK n
  exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso e.symm
    (B.isQuasicoherent_zariskiRestrictModule _ (hK n))

end Stacks.Adequate

end
