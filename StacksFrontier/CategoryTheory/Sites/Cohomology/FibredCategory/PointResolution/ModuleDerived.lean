module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.LocallyQuasiIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackContinuousUnivLE
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitByPointResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.ModuleLowerShriekAcyclic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.Cellular
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.Derived
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.ModuleBicomplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.ModuleFreeSum
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedAdjunction

/-!
# Derived lower shriek at module coefficients computed by a fibrewise point resolution

In the situation of
`StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.Basic`, let `O` be a
sheaf of rings on the base, in the universe in which `π` is formed, and let `M` be a sheaf of
modules over `π⁻¹O`. Then `Lπ_!(M)` is isomorphic in `D(O)` to the complex of sheaves of
`O`-modules whose term in degree `-n` is the sheafification of `V ↦ M(A_{n,V})`, a presheaf of
`O(V)`-modules through `(π⁻¹O)(A_{n,V}) = O(p(A_{n,V})) = O(V)`. This is Stacks 08VB at module
coefficients, for an arbitrary fibred category over a site with a fibrewise point resolution; the
abelian version is
`StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.Derived`.

## Main definitions

* `Stacks.Sites.FibredCategory.FibredCategorySituation.modulePointSheafComplex`: the complex of
  sheaves of `O`-modules of a fibrewise point resolution.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.modulePointSheafComplexForgetIso`: its
  underlying complex of abelian sheaves is the abelian `pointSheafComplex`.

## Main results

* `Stacks.Sites.FibredCategory.FibredCategorySituation.modulePointZeroSheafifyIso`: the
  sheafification of `V ↦ H_0(G(A_{•,V}))` is `π_!` of the sheafification of `G`.
* `FibredCategorySituation.isSumOfExtensionByZeroUnits_totalSheafification`: the sheafification
  of a free presheaf of `p⁻¹O`-modules on a coproduct of representables is a direct sum of the
  `j_{U!} O_U`.
* `FibredCategorySituation.isIso_derivedModuleLowerShriekComparison_app`: `Lπ_!` is computed
  degreewise on a bounded above complex of direct sums of the `j_{U!} O_U`.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.derivedModuleLowerShriekIso`:
  Stacks 08VB at module coefficients, built from the canonical maps along a resolution
  (`derivedModuleLowerShriekIsoOfResolution`).

## References

* [Stacks Project, Tag 08VB](https://stacks.math.columbia.edu/tag/08VB)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology Simplicial
open Stacks.Cohomology.DerivedLowerShriek StacksDraft.TotalComplexQuasiIso

universe uD vD uC vC w

namespace Stacks.Sites.FibredCategory.FibredCategorySituation

variable (s : FibredCategorySituation.{uD, vD, uC, vC, w})
  (O : Sheaf s.base.J RingCat.{max w uD vD uC vC})

example : (inverseImageRing s.topology s.base.J s.p O).obj = s.p.op ⋙ O.obj := rfl

/-- Sheafification of presheaves of `p⁻¹O`-modules on the total category. -/
abbrev totalSheafification :
    PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O.obj) ⥤
      SheafOfModules.{max w uD vD uC vC} (inverseImageRing s.topology s.base.J s.p O) :=
  PresheafOfModules.sheafification (R₀ := (inverseImageRing s.topology s.base.J s.p O).obj)
    (R := inverseImageRing s.topology s.base.J s.p O) (𝟙 _)

/-- Morphisms out of the sheafification of the free presheaf of `p⁻¹O`-modules on the lifted
representable `h_U` are the sections over `U`, as a functor of the target. -/
def sheafifyFreeUliftYonedaCorepresentation (U : s.C) :
    coyoneda.obj (op ((totalSheafification s O).obj
      ((PresheafOfModules.free (s.p.op ⋙ O.obj)).obj (uliftYoneda.{max w uD vD uC}.obj U)))) ≅
      SheafOfModules.toSheaf (inverseImageRing s.topology s.base.J s.p O) ⋙
        (sheafSections s.topology AddCommGrpCat.{max w uD vD uC vC}).obj (op U) ⋙
          forget AddCommGrpCat.{max w uD vD uC vC} :=
  NatIso.ofComponents
    (fun M => Equiv.toIso ((((PresheafOfModules.freeAdjunction (s.p.op ⋙ O.obj)).comp
      (PresheafOfModules.sheafificationAdjunction
        (R₀ := (inverseImageRing s.topology s.base.J s.p O).obj)
        (R := inverseImageRing s.topology s.base.J s.p O) (𝟙 _))).homEquiv _ M).trans
          uliftYonedaEquiv))
    (fun {M N} g => by
      ext f
      exact (congrArg uliftYonedaEquiv (Adjunction.homEquiv_naturality_right
        ((PresheafOfModules.freeAdjunction (s.p.op ⋙ O.obj)).comp
          (PresheafOfModules.sheafificationAdjunction
        (R₀ := (inverseImageRing s.topology s.base.J s.p O).obj)
            (R := inverseImageRing s.topology s.base.J s.p O) (𝟙 _))) f g)).trans
        (uliftYonedaEquiv_comp _ _))

/-- Morphisms out of `j_{U!} O_U` are the sections over `U`, as a functor of the target
(Stacks 0G1V). -/
def extensionByZeroUnitCorepresentationTotal (U : s.C) :
    coyoneda.obj (op (extensionByZeroUnit (inverseImageRing s.topology s.base.J s.p O) U)) ≅
      SheafOfModules.toSheaf (inverseImageRing s.topology s.base.J s.p O) ⋙
        (sheafSections s.topology AddCommGrpCat.{max w uD vD uC vC}).obj (op U) ⋙
          forget AddCommGrpCat.{max w uD vD uC vC} :=
  NatIso.ofComponents
    (fun M => Equiv.toIso (Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv s.topology
      (inverseImageRing s.topology s.base.J s.p O) U M))
    (fun {M N} g => by
      ext φ
      exact Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv_naturality s.topology _ U φ g)

/-- **The sheafification of the free presheaf of `p⁻¹O`-modules on a representable is
`j_{U!} O_U`.** -/
def sheafifyFreeUliftYonedaIso (U : s.C) :
    (totalSheafification s O).obj
        ((PresheafOfModules.free (s.p.op ⋙ O.obj)).obj (uliftYoneda.{max w uD vD uC}.obj U)) ≅
      extensionByZeroUnit (inverseImageRing s.topology s.base.J s.p O) U :=
  (Coyoneda.fullyFaithful.preimageIso
    (sheafifyFreeUliftYonedaCorepresentation s O U ≪≫
      (extensionByZeroUnitCorepresentationTotal s O U).symm)).unop.symm

/-- **The sheafification of a free presheaf of `p⁻¹O`-modules on a coproduct of representables is
a direct sum of the `j_{U!} O_U`.** -/
lemma isSumOfExtensionByZeroUnits_totalSheafification
    {G : PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O.obj)} (hG : IsModuleFreeSum s O.obj G) :
    IsSumOfExtensionByZeroUnits (inverseImageRing s.topology s.base.J s.p O)
      ((totalSheafification s O).obj G) := by
  rw [isModuleFreeSum_iff] at hG
  obtain ⟨ι, x, ⟨e⟩⟩ := hG
  have : PreservesColimitsOfShape (Discrete ι) (totalSheafification s O) :=
    (PresheafOfModules.sheafificationAdjunction
        (R₀ := (inverseImageRing s.topology s.base.J s.p O).obj)
      (R := inverseImageRing s.topology s.base.J s.p O)
        (𝟙 _)).leftAdjoint_preservesColimits.preservesColimitsOfShape
  exact ⟨ι, x, ⟨Sigma.mapIso (fun i => (sheafifyFreeUliftYonedaIso s O (x i)).symm) ≪≫
    (PreservesCoproduct.iso (totalSheafification s O) _).symm ≪≫
      (totalSheafification s O).mapIso e⟩⟩

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **`Lπ_!` is computed degreewise on a bounded above complex of direct sums of the
`j_{U!} O_U`**, at module coefficients. -/
lemma isIso_derivedModuleLowerShriekComparison_app
    (L : CochainComplex (SheafOfModules.{max w uD vD uC vC}
      (inverseImageRing s.topology s.base.J s.p O)) ℤ) [L.IsStrictlyLE 0]
    (hL : ∀ n, IsSumOfExtensionByZeroUnits (inverseImageRing s.topology s.base.J s.p O) (L.X n)) :
    IsIso ((derivedLowerShriekComparison s.topology s.base.J s.p O).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)) := by
  have : HasExactColimitsOfShape ℕ (SheafOfModules.{max w uD vD uC vC}
    (inverseImageRing s.topology s.base.J s.p O)) := hasExactColimitsOfShape_nat _
  have : HasExactColimitsOfShape ℕ (SheafOfModules.{max w uD vD uC vC} O) :=
    hasExactColimitsOfShape_nat _
  have : PreservesColimitsOfShape ℕ (lowerShriekModules s.topology s.base.J s.p O) :=
    (Adjunction.leftAdjoint_preservesColimits.{0, 0}
      (adjunctionModules s.topology s.base.J s.p O)).preservesColimitsOfShape
  have h := StacksDraft.UnboundedLeftDerivedFunctor.derives_cellularLocalizerMorphism
    (lowerShriekModules s.topology s.base.J s.p O)
    (IsSumOfExtensionByZeroUnits (inverseImageRing s.topology s.base.J s.p O))
    (fun _ _ => isSumOfExtensionByZeroUnits_biprod _)
    (exists_epi_isSumOfExtensionByZeroUnits _)
    (s.lowerShriekModules_acyclic_anyUniverse O)
  have :=
    StacksDraft.UnboundedLeftDerivedFunctor.isLeftDerivabilityStructure_cellularLocalizerMorphism _
    (StacksDraft.UnboundedLeftDerivedFunctor.hasLeftResolutions_cellularLocalizerMorphism
      (IsSumOfExtensionByZeroUnits (inverseImageRing s.topology s.base.J s.p O))
      (fun _ _ => isSumOfExtensionByZeroUnits_biprod _)
      (exists_epi_isSumOfExtensionByZeroUnits _))
  exact CategoryTheory.LeftDerivedByResolutions.isIso_app_of_derives _ _ h DerivedCategory.Qh _ _
    ⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L,
      ⟨L, CochainComplex.isPCellular_of_isStrictlyLE _ L hL, ⟨Iso.refl _⟩⟩⟩

end Derived

variable {s} {A : s.base.C ⥤ CosimplicialObject s.C}
  (hA : A ⋙ (Functor.whiskeringRight SimplexCategory s.C s.base.C).obj s.p =
    Functor.const SimplexCategory)
  (hres : ∀ (V : s.base.C) (W : s.p.Fiber V),
    ∃ f : (Functor.Fiber.inducedFunctor (Functor.congr_obj hA V)).op ⋙ yoneda.obj W ⟶
        (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{vC + 1},
      SimplicialObject.homotopyEquivalences (Type vC) f)

/-- Sheafification of presheaves of `p⁻¹O`-modules is additive. -/
instance totalSheafification_additive : (totalSheafification s O).Additive :=
  PresheafOfModules.additive_sheafification _

/-- Sheafification of presheaves of `p⁻¹O`-modules is exact. -/
instance totalSheafification_preservesHomology : (totalSheafification s O).PreservesHomology :=
  PresheafOfModules.preservesHomology_sheafification _

/-- Restriction of sheaves of modules along the projection, followed by the underlying presheaf,
is restriction of presheaves of modules of the underlying presheaf. -/
def restrictionModulesForgetIso :
    (SheafOfModules.forget O ⋙ PresheafOfModules.restrictScalars (𝟙 O.obj)) ⋙
        moduleRestriction s O.obj ≅
      restrictionModules s.topology s.base.J s.p O ⋙
        (SheafOfModules.forget _ ⋙
          PresheafOfModules.restrictScalars (𝟙 (inverseImageRing s.topology s.base.J s.p O).obj)) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

include hres in
/-- **The sheafification of `V ↦ H_0(G(A_{•,V}))` is `π_!` of the sheafification of `G`**, for a
presheaf of `p⁻¹O`-modules `G`. -/
def modulePointZeroSheafifyIso :
    modulePointZero s hA O.obj ⋙ PresheafOfModules.sheafification (𝟙 O.obj) ≅
      totalSheafification s O ⋙ lowerShriekModules s.topology s.base.J s.p O :=
  ((modulePointZeroAdjunction s hA O.obj hres).comp
      (PresheafOfModules.sheafificationAdjunction (𝟙 O.obj))).leftAdjointUniq
    (((PresheafOfModules.sheafificationAdjunction
        (R₀ := (inverseImageRing s.topology s.base.J s.p O).obj)
        (R := inverseImageRing s.topology s.base.J s.p O) (𝟙 _)).comp
      (adjunctionModules s.topology s.base.J s.p O)).ofNatIsoRight
        (restrictionModulesForgetIso O).symm)

/-- **The complex of sheaves of `O`-modules of a fibrewise point resolution**: for a sheaf of
`p⁻¹O`-modules `M`, the sheafification of the complex of presheaves of `O`-modules
`V ↦ M(A_{•,V})`, its simplicial degree `n` sitting in cohomological degree `-n`. -/
abbrev modulePointSheafComplex
    (M : SheafOfModules.{max w uD vD uC vC} (inverseImageRing s.topology s.base.J s.p O)) :
    CochainComplex (SheafOfModules.{max w uD vD uC vC} O) ℤ :=
  ((PresheafOfModules.sheafification (𝟙 O.obj)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj ((modulePointMooreCochain s hA O.obj).obj M.val)

/-- Forgetting the module structure of the complex `V ↦ G(A_{•,V})`, read as a cochain complex,
gives the cochain complex of abelian presheaves `V ↦ G(A_{•,V})` of the underlying abelian
presheaf of `G`. -/
def modulePointMooreCochainForgetIso
    (G : PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O.obj)) :
    ((PresheafOfModules.toPresheaf O.obj).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((modulePointMooreCochain s hA O.obj).obj G) ≅
      (pointMooreCochain s A).obj G.presheaf :=
  (HomologicalComplex.mapHomologicalComplexExtendIso (PresheafOfModules.toPresheaf O.obj)
      ((modulePointMooreComplex s hA O.obj).obj G) (ComplexShape.embeddingUpIntLE (0 : ℤ))).symm ≪≫
    ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor _).mapIso
      ((modulePointMooreComplexForgetIso s hA O.obj).app G)

/-- **The underlying complex of abelian sheaves of the complex of sheaves of modules of a
fibrewise point resolution is the complex of abelian sheaves of the underlying abelian sheaf**:
forgetting the module structure of `modulePointSheafComplex` gives `pointSheafComplex`, the
sheafification of the complex of abelian presheaves `V ↦ M(A_{•,V})`. -/
def modulePointSheafComplexForgetIso
    (M : SheafOfModules.{max w uD vD uC vC} (inverseImageRing s.topology s.base.J s.p O)) :
    ((SheafOfModules.toSheaf O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (modulePointSheafComplex O hA M) ≅
      pointSheafComplex s A M.val.presheaf :=
  (Functor.mapHomologicalComplexCompIso
      (F := PresheafOfModules.sheafification (𝟙 O.obj)) (G := SheafOfModules.toSheaf O)
      (Iso.refl _) (ComplexShape.up ℤ)).app _ ≪≫
    (NatIso.mapHomologicalComplex (PresheafOfModules.sheafificationCompToSheaf (𝟙 O.obj))
      (ComplexShape.up ℤ)).app _ ≪≫
    ((Functor.mapHomologicalComplexCompIso (F := PresheafOfModules.toPresheaf O.obj)
      (G := presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC vC})
      (Iso.refl _) (ComplexShape.up ℤ)).app _).symm ≪≫
    ((presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC vC}).mapHomologicalComplex
      (ComplexShape.up ℤ)).mapIso (modulePointMooreCochainForgetIso O hA M.val)

section Derived

attribute [local instance] HasDerivedCategory.standard

include hres in
/-- **Stacks 08VB at module coefficients, along a resolution.** For a sheaf `M` of `π⁻¹O`-modules
and a bounded above resolution `π : Q ⟶ M` of its underlying presheaf of modules by free sums of
representables, the isomorphism `Lπ_!(M) ≅ Q(K)` with `K` the complex of sheaves whose term in
degree `-n` is the sheafification of `V ↦ M(A_{n,V})`. It is the composite of the canonical maps of
the proof: the sheafified resolution computes `Lπ_!` degreewise, `π_!` of a free sum is the
sheafification of `H_0` on the point resolution, and the two filtrations of the double complex
`V ↦ Q(A_{•,V})`. -/
def derivedModuleLowerShriekIsoOfResolution
    (M : SheafOfModules.{max w uD vD uC vC} (inverseImageRing s.topology s.base.J s.p O))
    (Q : CochainComplex (PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O.obj)) ℤ)
    (hQle : Q.IsStrictlyLE 0) (hQ : ∀ n, IsModuleFreeSum s O.obj (Q.X n))
    (π : Q ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M.val) [QuasiIso π] :
    (derivedLowerShriek s.topology s.base.J s.p O).obj
        ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      DerivedCategory.Q.obj (modulePointSheafComplex O hA M) := by
  let K := ((totalSheafification s O).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q
  have hKle : CochainComplex.IsStrictlyLE K 0 :=
    (CochainComplex.isStrictlyLE_iff _ 0).2 fun i hi => Functor.map_isZero
      (totalSheafification s O) (CochainComplex.isZero_of_isStrictlyLE Q 0 i hi)
  have hKP : ∀ n, IsSumOfExtensionByZeroUnits (inverseImageRing s.topology s.base.J s.p O)
      (K.X n) := fun n => isSumOfExtensionByZeroUnits_totalSheafification s O (hQ n)
  have hcounit : IsIso ((PresheafOfModules.sheafificationAdjunction
        (R₀ := (inverseImageRing s.topology s.base.J s.p O).obj)
      (R := inverseImageRing s.topology s.base.J s.p O) (𝟙 _)).counit.app M) := by
    rw [← isIso_iff_of_reflects_iso _
      (SheafOfModules.toSheaf (inverseImageRing s.topology s.base.J s.p O)),
      PresheafOfModules.toSheaf_map_sheafificationAdjunction_counit_app]
    exact (inferInstance : IsIso ((CategoryTheory.sheafificationAdjunction s.topology
      AddCommGrpCat.{max w uD vD uC vC}).counit.app _))
  have hπK :
      QuasiIso (((totalSheafification s O).mapHomologicalComplex (ComplexShape.up ℤ)).map π) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology π (totalSheafification s O)
  let eF : ((totalSheafification s O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M.val) ≅
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M :=
    (HomologicalComplex.singleMapHomologicalComplex (totalSheafification s O)
      (ComplexShape.up ℤ) 0).app M.val ≪≫
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso
        (@asIso _ _ _ _ ((PresheafOfModules.sheafificationAdjunction
          (R₀ := (inverseImageRing s.topology s.base.J s.p O).obj)
          (R := inverseImageRing s.topology s.base.J s.p O) (𝟙 _)).counit.app M) hcounit)
  let e1 : DerivedCategory.Q.obj K ≅ (DerivedCategory.singleFunctor _ 0).obj M :=
    asIso (DerivedCategory.Q.map
        (((totalSheafification s O).mapHomologicalComplex (ComplexShape.up ℤ)).map π)) ≪≫
      DerivedCategory.Q.mapIso eF
  have hcell := isIso_derivedModuleLowerShriekComparison_app s O K hKP
  let e2 : (derivedLowerShriek s.topology s.base.J s.p O).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj (((lowerShriekModules s.topology s.base.J s.p O).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) :=
    (derivedLowerShriek s.topology s.base.J s.p O).mapIso
        ((DerivedCategory.quotientCompQhIso _).app K).symm ≪≫
      asIso ((derivedLowerShriekComparison s.topology s.base.J s.p O).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) ≪≫
      (DerivedCategory.quotientCompQhIso _).app _
  let e3 : ((lowerShriekModules s.topology s.base.J s.p O).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K ≅
      ((PresheafOfModules.sheafification (𝟙 O.obj)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((modulePointZero s hA O.obj).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun n => ((modulePointZeroSheafifyIso O hA hres).app (Q.X n)).symm)
      (fun i j _ => ((modulePointZeroSheafifyIso O hA hres).inv.naturality (Q.d i j)).symm)
  have haug : ∀ p : ℤ, QuasiIso ((modulePointMooreCochainAugmentation s hA O.obj).app (Q.X p)) :=
    fun p => quasiIso_modulePointMooreCochainAugmentation s hA O.obj (Q.X p)
      (isZero_modulePointMooreComplex_homology_of_isModuleFreeSum O.obj hA hres _ (hQ p))
  have hcol := quasiIso_modulePointBicomplexColumnTotalMap s hA O.obj Q haug
  have hunit := isIso_totalSingleRowZeroUnit
    (((modulePointZero s hA O.obj).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)
  let φ : (modulePointBicomplex s hA O.obj Q).total (ComplexShape.up ℤ) ⟶
      ((modulePointZero s hA O.obj).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q :=
    HomologicalComplex₂.total.map (modulePointBicomplexColumnMap s hA O.obj Q)
        (ComplexShape.up ℤ) ≫
      inv (totalSingleRowZeroUnit
        (((modulePointZero s hA O.obj).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q))
  have hφ : QuasiIso (((PresheafOfModules.sheafification (𝟙 O.obj)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map φ) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology φ
      (PresheafOfModules.sheafification (𝟙 O.obj))
  let e4 := (asIso (DerivedCategory.Q.map
    (((PresheafOfModules.sheafification (𝟙 O.obj)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map φ))).symm
  have hsingle : CochainComplex.IsStrictlyLE ((HomologicalComplex.single
      (PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O.obj)) (ComplexShape.up ℤ) 0).obj M.val)
      0 :=
    (CochainComplex.isStrictlyLE_iff _ 0).2 fun i hi =>
      HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  have hrow := quasiIso_modulePointBicomplexTotalMap s hA O.obj π
  let e5 := asIso (DerivedCategory.Q.map
    (((PresheafOfModules.sheafification (𝟙 O.obj)).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (HomologicalComplex₂.total.map ((modulePointBicomplexFunctor s hA O.obj).map π)
      (ComplexShape.up ℤ))))
  have := hasTotal_singleColumn ((modulePointMooreCochain s hA O.obj).obj M.val) (0 : ℤ)
  have : IsIso (HomologicalComplex₂.total.map
      ((HomologicalComplex.singleMapHomologicalComplex (modulePointMooreCochain s hA O.obj)
        (ComplexShape.up ℤ) 0).app M.val).inv (ComplexShape.up ℤ)) :=
    Stacks.ChaoticSite.ModuleValued.isIso_total_map_of_isIso _
  let e6 : (modulePointMooreCochain s hA O.obj).obj M.val ≅
      (modulePointBicomplex s hA O.obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M.val)).total
          (ComplexShape.up ℤ) :=
    Stacks.ChaoticSite.ModuleValued.totalSingleColumnZeroIso
        ((modulePointMooreCochain s hA O.obj).obj M.val) ≪≫
      asIso (HomologicalComplex₂.total.map
        ((HomologicalComplex.singleMapHomologicalComplex (modulePointMooreCochain s hA O.obj)
          (ComplexShape.up ℤ) 0).app M.val).inv (ComplexShape.up ℤ))
  exact (derivedLowerShriek s.topology s.base.J s.p O).mapIso e1.symm ≪≫ e2 ≪≫
    DerivedCategory.Q.mapIso e3 ≪≫ e4 ≪≫ e5 ≪≫
      DerivedCategory.Q.mapIso (((PresheafOfModules.sheafification (𝟙 O.obj)).mapHomologicalComplex
        (ComplexShape.up ℤ)).mapIso e6).symm

include hres in
/-- **Stacks 08VB at module coefficients: `Lπ_!` is computed by the complex of sheaves of modules
of a fibrewise point resolution.** For a sheaf `M` of `π⁻¹O`-modules on the total category,
`Lπ_!(M)` is isomorphic in `D(O)` to the complex of sheaves of `O`-modules whose term in degree
`-n` is the sheafification of `V ↦ M(A_{n,V})`, an `O(V)`-module through
`(π⁻¹O)(A_{n,V}) = O(V)`: `derivedModuleLowerShriekIsoOfResolution` at a chosen resolution. -/
def derivedModuleLowerShriekIso
    (M : SheafOfModules.{max w uD vD uC vC} (inverseImageRing s.topology s.base.J s.p O)) :
    (derivedLowerShriek s.topology s.base.J s.p O).obj
        ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      DerivedCategory.Q.obj (modulePointSheafComplex O hA M) :=
  let h := exists_isModuleFreeSum_resolution s O.obj M.val
  let h₁ := h.choose_spec
  let h₂ := h₁.choose_spec
  let h₃ := h₂.choose_spec
  have := h₃.choose_spec
  derivedModuleLowerShriekIsoOfResolution O hA hres M h.choose h₁.choose h₂.choose h₃.choose

include hres in
/-- `Lπ_!(M)` is isomorphic to the complex of sheaves of the point resolution. -/
theorem nonempty_derivedModuleLowerShriekIso
    (M : SheafOfModules.{max w uD vD uC vC} (inverseImageRing s.topology s.base.J s.p O)) :
    Nonempty ((derivedLowerShriek s.topology s.base.J s.p O).obj
        ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      DerivedCategory.Q.obj (modulePointSheafComplex O hA M)) :=
  ⟨derivedModuleLowerShriekIso O hA hres M⟩

include hres in
/-- **`L_nπ_!` at module coefficients is the sheafification of the homology of `V ↦ M(A_{•,V})`**:
for a sheaf `M` of `π⁻¹O`-modules and `n ≥ 0`, `H^{-n}(Lπ_! M)` is the sheaf of `O`-modules
associated to the presheaf `V ↦ H_n(M(A_{•,V}))`. -/
theorem nonempty_derivedModuleLowerShriekHomologyIso
    (M : SheafOfModules.{max w uD vD uC vC} (inverseImageRing s.topology s.base.J s.p O))
    (n : ℕ) :
    Nonempty ((DerivedCategory.homologyFunctor _ (-(n : ℤ))).obj
        ((derivedLowerShriek s.topology s.base.J s.p O).obj
          ((DerivedCategory.singleFunctor _ 0).obj M)) ≅
      (PresheafOfModules.sheafification (𝟙 O.obj)).obj
        (((modulePointMooreComplex s hA O.obj).obj M.val).homology n)) := by
  have e := derivedModuleLowerShriekIso O hA hres M
  have hn : (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = -(n : ℤ) := by simp
  exact ⟨(DerivedCategory.homologyFunctor _ (-(n : ℤ))).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors _ (-(n : ℤ))).app _ ≪≫
    ShortComplex.mapHomologyIso (((modulePointMooreCochain s hA O.obj).obj M.val).sc (-(n : ℤ)))
      (PresheafOfModules.sheafification (𝟙 O.obj)) ≪≫
    (PresheafOfModules.sheafification (𝟙 O.obj)).mapIso
      (HomologicalComplex.extendHomologyIso _ (ComplexShape.embeddingUpIntLE (0 : ℤ)) hn)⟩

end Derived

end Stacks.Sites.FibredCategory.FibredCategorySituation
