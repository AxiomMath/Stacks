module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.AlgebraicGeometry.DeRham.HypercohomologyBridge
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyBrutalCollapse
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.AcyclicityAndBoundedBelow

/-!
# Hypercohomology of a complex of modules and of its underlying abelian sheaves

Let `X` be a ringed space and `K` a bounded below complex of `𝒪_X`-modules. Its hypercohomology
can be computed in two ways: deriving global sections in the category of `𝒪_X`-modules, which
gives `Γ(X, 𝒪_X)`-modules, or forgetting the module structure first and deriving global sections
of sheaves of abelian groups. By [Stacks, Tag 01F1] the two agree. This file records the
resulting isomorphism of abelian groups in every degree, natural in the complex.

## Main definitions

* `Stacks.Cech.Hypercohomology.abelianHypercohomology`: the hypercohomology of a bounded below
  complex of abelian sheaves.
* `Stacks.Cech.Hypercohomology.realizationNatIso`: **the comparison**, as an isomorphism of
  functors on bounded below complexes of `𝒪_X`-modules.
* `Stacks.Cech.Hypercohomology.realizationIso`: its component at a complex.

## Main results

* `Stacks.Cech.Hypercohomology.realizationIso_naturality`: the comparison is natural in the
  complex.

## References

* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)

universe u

/-! ### Brutal truncation and additive functors -/

namespace HomologicalComplex

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  [HasZeroObject C] [HasZeroObject D] (F : C ⥤ D) [F.PreservesZeroMorphisms]
  (K : CochainComplex C ℤ) (p : ℤ)

/-- A functor preserving zero morphisms carries a complex strictly supported in degrees `≥ p` to
one strictly supported in degrees `≥ p`. -/
instance isStrictlySupported_mapHomologicalComplex_stupidTrunc :
    ((F.mapHomologicalComplex (up ℤ)).obj
      (K.stupidTrunc (embeddingUpIntGE p))).IsStrictlySupported (embeddingUpIntGE p) :=
  ⟨fun i' hi' => F.map_isZero
    ((K.stupidTrunc (embeddingUpIntGE p)).isZero_X_of_isStrictlySupported _ i' hi')⟩

/-- The comparison `F(σ^{≥p}K) ⟶ σ^{≥p}F(K)`: the image of the inclusion `σ^{≥p}K ⟶ K` factors
through the brutal truncation of `F(K)`, its source being concentrated in degrees `≥ p`. -/
noncomputable def mapStupidTruncGEComparison :
    (F.mapHomologicalComplex (up ℤ)).obj (K.stupidTrunc (embeddingUpIntGE p)) ⟶
      ((F.mapHomologicalComplex (up ℤ)).obj K).stupidTrunc (embeddingUpIntGE p) :=
  StacksDraft.StupidTruncation.liftStupidTrunc _ _
    ((F.mapHomologicalComplex (up ℤ)).map (K.ιStupidTrunc (embeddingUpIntGE p)))

/-- The comparison `F(σ^{≥p}K) ⟶ σ^{≥p}F(K)` composed with the inclusion of `σ^{≥p}F(K)` is the
image of the inclusion of `σ^{≥p}K`. -/
@[reassoc (attr := simp)]
theorem mapStupidTruncGEComparison_ι :
    mapStupidTruncGEComparison F K p ≫
        ((F.mapHomologicalComplex (up ℤ)).obj K).ιStupidTrunc (embeddingUpIntGE p) =
      (F.mapHomologicalComplex (up ℤ)).map (K.ιStupidTrunc (embeddingUpIntGE p)) :=
  StacksDraft.StupidTruncation.liftStupidTrunc_ι _ _ _

/-- The comparison `F(σ^{≥p}K) ⟶ σ^{≥p}F(K)` is an isomorphism. -/
instance isIso_mapStupidTruncGEComparison : IsIso (mapStupidTruncGEComparison F K p) := by
  suffices h : ∀ q, IsIso ((mapStupidTruncGEComparison F K p).f q) from
    Hom.isIso_of_components _
  intro q
  by_cases hq : ∃ i, (embeddingUpIntGE p).f i = q
  · obtain ⟨i, hi⟩ := hq
    have h₁ := ((F.mapHomologicalComplex (up ℤ)).obj K).isIso_ιStupidTrunc_f
      (embeddingUpIntGE p) hi
    have h₂ := K.isIso_ιStupidTrunc_f (embeddingUpIntGE p) hi
    have e := congrArg (fun φ => φ.f q) (mapStupidTruncGEComparison_ι F K p)
    simp only [comp_f, Functor.mapHomologicalComplex_map_f] at e
    have : IsIso ((mapStupidTruncGEComparison F K p).f q ≫
        (((F.mapHomologicalComplex (up ℤ)).obj K).ιStupidTrunc (embeddingUpIntGE p)).f q) := by
      rw [e]; infer_instance
    exact IsIso.of_isIso_comp_right _ ((((F.mapHomologicalComplex (up ℤ)).obj K).ιStupidTrunc
      (embeddingUpIntGE p)).f q)
  · push Not at hq
    exact IsZero.isIso
      (F.map_isZero ((K.stupidTrunc (embeddingUpIntGE p)).isZero_X_of_isStrictlySupported _ q hq))
      ((((F.mapHomologicalComplex (up ℤ)).obj K).stupidTrunc
        (embeddingUpIntGE p)).isZero_X_of_isStrictlySupported _ q hq) _

/-- **Brutal truncation commutes with a functor preserving zero morphisms**:
`F(σ^{≥p}K) ≅ σ^{≥p}F(K)`, compatibly with the two inclusions. -/
noncomputable def mapStupidTruncGEIso :
    (F.mapHomologicalComplex (up ℤ)).obj (K.stupidTrunc (embeddingUpIntGE p)) ≅
      ((F.mapHomologicalComplex (up ℤ)).obj K).stupidTrunc (embeddingUpIntGE p) :=
  asIso (mapStupidTruncGEComparison F K p)

/-- **The comparison `F(σ^{≥p}K) ≅ σ^{≥p}F(K)` is compatible with the projections onto the bottom
term**, the single complex of `F(Kᵖ)` being identified with `F` of the single complex of `Kᵖ`. -/
theorem mapStupidTruncGEComparison_stupidTruncGEπ :
    mapStupidTruncGEComparison F K p ≫
        StacksDraft.StupidTruncation.stupidTruncGEπ ((F.mapHomologicalComplex (up ℤ)).obj K) p =
      (F.mapHomologicalComplex (up ℤ)).map (StacksDraft.StupidTruncation.stupidTruncGEπ K p) ≫
        (singleMapHomologicalComplex F (up ℤ) p).hom.app (K.X p) := by
  apply to_single_hom_ext
  have e := congrArg (fun φ => φ.f p) (mapStupidTruncGEComparison_ι F K p)
  simp only [comp_f, Functor.mapHomologicalComplex_map_f,
    StacksDraft.StupidTruncation.ιStupidTruncGE_f _ p p le_rfl] at e
  rw [comp_f, comp_f, StacksDraft.StupidTruncation.stupidTruncGEπ_f, ← Category.assoc, e,
    Functor.mapHomologicalComplex_map_f, StacksDraft.StupidTruncation.stupidTruncGEπ_f,
    singleMapHomologicalComplex_hom_app_self]
  simp only [Functor.map_comp, Category.assoc, ← F.map_comp_assoc, Iso.inv_hom_id, F.map_id,
    Category.id_comp]
  rfl

/-- The projection onto the bottom term of a brutal truncation is natural in the complex. -/
@[reassoc]
theorem stupidTruncMap_stupidTruncGEπ {C : Type*} [Category* C] [HasZeroMorphisms C]
    [HasZeroObject C] {K L : CochainComplex C ℤ} (φ : K ⟶ L) (p : ℤ) :
    stupidTruncMap φ (embeddingUpIntGE p) ≫ StacksDraft.StupidTruncation.stupidTruncGEπ L p =
      StacksDraft.StupidTruncation.stupidTruncGEπ K p ≫ (single C (up ℤ) p).map (φ.f p) := by
  apply to_single_hom_ext
  have e := congrArg (fun ψ => ψ.f p) (stupidTruncMap_ιStupidTrunc (embeddingUpIntGE p) φ)
  simp only [comp_f, StacksDraft.StupidTruncation.ιStupidTruncGE_f _ p p le_rfl] at e
  rw [comp_f, comp_f, StacksDraft.StupidTruncation.stupidTruncGEπ_f,
    StacksDraft.StupidTruncation.stupidTruncGEπ_f, ← Category.assoc, e, single_map_f_self,
    Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]

end HomologicalComplex

namespace Stacks.Cech.Hypercohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **The hypercohomology `Hⁿ(Y, L)` of a bounded below complex of abelian sheaves**: the `n`-th
cohomology of its bounded below derived global sections. -/
abbrev abelianHypercohomology {Y : TopCat.{u}} (L : CochainComplex.Plus (AbelianSheaf Y))
    (n : ℤ) : AddCommGrpCat.{u} :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).obj
    ((sectionsFunctor Y ⊤).rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj L))

variable (X : RingedSpace.{u, u})

/-- The underlying complex of abelian sheaves, read in the derived category, is the derived image
of the complex of modules under the exact forgetful functor. -/
def toSheafQIso :
    (SheafOfModules.toSheaf (structureSheafRing X)).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q ≅
      DerivedCategory.Plus.Q ⋙
        (SheafOfModules.toSheaf (structureSheafRing X)).mapDerivedCategoryPlus :=
  Functor.fullyFaithfulCancelRight DerivedCategory.Plus.ι
    (Functor.isoWhiskerLeft (CochainComplex.Plus.ι _)
      (SheafOfModules.toSheaf (structureSheafRing X)).mapDerivedCategoryFactors.symm)

/-- An exact functor read on bounded below derived categories commutes with cohomology. -/
def forgetPlusHomologyIso (n : ℤ) :
    (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))
          AddCommGrpCat.{u}).mapDerivedCategoryPlus ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n ≅
      DerivedCategory.Plus.homologyFunctor _ n ⋙
        forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) AddCommGrpCat.{u} :=
  Functor.isoWhiskerLeft DerivedCategory.Plus.ι
    (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
      (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) AddCommGrpCat.{u}) n)

/-- **The comparison of [Stacks, Tag 01F1] in cohomology, as an isomorphism of functors** on
bounded below complexes of `𝒪_X`-modules: the hypercohomology of the underlying complex of
abelian sheaves is the hypercohomology computed in modules, with its module structure
forgotten. -/
def realizationNatIso (n : ℤ) :
    (SheafOfModules.toSheaf (structureSheafRing X)).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q ⋙ (sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n ≅
      DerivedCategory.Plus.Q ⋙
        (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor _ n ⋙
        forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) AddCommGrpCat.{u} :=
  Functor.isoWhiskerRight (toSheafQIso X)
      ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n) ≪≫
    Functor.isoWhiskerLeft DerivedCategory.Plus.Q
      (Functor.isoWhiskerRight
        (SheafOfModules.toSheaf
          (structureSheafRing X)).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.symm
        ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n)) ≪≫
    Functor.isoWhiskerLeft DerivedCategory.Plus.Q
      (Functor.isoWhiskerRight
        (Stacks.Cohomology.ModuleComparison.rightDerivedFunctorPlus_sections_forget_iso X ⊤).symm
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n)) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.Q ⋙
        (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)).rightDerivedFunctorPlus)
      (Functor.isoWhiskerRight
          (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))
            AddCommGrpCat.{u}).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
          (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n) ≪≫
        forgetPlusHomologyIso X n)

/-- **Hypercohomology of the underlying abelian sheaves is hypercohomology in modules**
([Stacks, Tag 01F1]), for a bounded below complex `K` of `𝒪_X`-modules and every degree `n`. -/
def realizationIso (K : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing X))) (n : ℤ) :
    abelianHypercohomology
        ((SheafOfModules.toSheaf (structureSheafRing X)).mapCochainComplexPlus.obj K) n ≅
      (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) AddCommGrpCat.{u}).obj
        (hypercohomology X.sheaf K n) :=
  (realizationNatIso X n).app K

/-- **The comparison of [Stacks, Tag 01F1] is natural in the complex.** -/
theorem realizationIso_naturality
    {K L : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing X))} (f : K ⟶ L)
    (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).map
        ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map
          ((SheafOfModules.toSheaf (structureSheafRing X)).mapCochainComplexPlus.map f))) ≫
        (realizationIso X L n).hom =
      (realizationIso X K n).hom ≫
        (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) AddCommGrpCat.{u}).map
          (hypercohomologyMap X.sheaf f n) :=
  (realizationNatIso X n).hom.naturality f

/-- **The comparison of [Stacks, Tag 01F1] read through an identification** `e` of a complex of
abelian sheaves with the underlying complex of a complex of `𝒪_X`-modules. -/
def realizationIsoOfIso {L : CochainComplex.Plus (AbelianSheaf X.carrier)}
    {K : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing X))}
    (e : L ≅ (SheafOfModules.toSheaf (structureSheafRing X)).mapCochainComplexPlus.obj K)
    (n : ℤ) :
    abelianHypercohomology L n ≅
      (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) AddCommGrpCat.{u}).obj
        (hypercohomology X.sheaf K n) :=
  (DerivedCategory.Plus.Q ⋙ (sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).mapIso e ≪≫
    realizationIso X K n

/-- **The transported comparison is natural** for morphisms compatible with the
identifications. -/
theorem realizationIsoOfIso_naturality {L L' : CochainComplex.Plus (AbelianSheaf X.carrier)}
    {K K' : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing X))}
    (e : L ≅ (SheafOfModules.toSheaf (structureSheafRing X)).mapCochainComplexPlus.obj K)
    (e' : L' ≅ (SheafOfModules.toSheaf (structureSheafRing X)).mapCochainComplexPlus.obj K')
    (g : L ⟶ L') (f : K ⟶ K')
    (h : g ≫ e'.hom = e.hom ≫
      (SheafOfModules.toSheaf (structureSheafRing X)).mapCochainComplexPlus.map f) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).map
        ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map g)) ≫ (realizationIsoOfIso X e' n).hom =
      (realizationIsoOfIso X e n).hom ≫
        (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) AddCommGrpCat.{u}).map
          (hypercohomologyMap X.sheaf f n) := by
  have h' := congrArg (DerivedCategory.Plus.Q ⋙
      (sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).map h
  simp only [Functor.map_comp] at h'
  dsimp only [realizationIsoOfIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [Category.assoc, ← realizationIso_naturality]
  simp only [← Category.assoc]
  exact congrArg (· ≫ (realizationIso X K' n).hom) h'

end Stacks.Cech.Hypercohomology

end
