module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedResolutionSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionReflectsIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedQuasiIsoMultiplicative
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorTriangulated
public import StacksFrontier.CategoryTheory.Localization.LeftDerivedByResolutions

/-!
# The derived pullback along a functor of chaotic sites

Let `F : C' ⥤ C` be a functor of categories with the chaotic topology, `g` the morphism of ringed
topoi it induces together with `σ : g⁻¹O ⟶ O'`, and `φ : g^*A → A'` a map of sheaves of
differential graded algebras. The pullback `g^* : Mod(A, d) ⥤ Mod(A', d)`, `pullbackFunctor φ`,
preserves homotopies, so it induces a functor `K(A) ⥤ K(A')`; followed by the localization
functor `K(A') ⥤ D(A', d)` it has a left derived functor `Lg^* : D(A, d) ⥤ D(A', d)`, computed on
the modules whose sections over every object are orthogonal on the left to the acyclic modules
(K-projective); those resolve every module by
`SheafOfModules.DifferentialGradedModule.exists_flat_quasiIso_sectionwise`.

The point is that on such a module `P` the pullback is computed sectionwise by plain tensor
products `P(F U') ⊗_{A(F U')} A'(U')` of modules which are orthogonal on the left to the acyclic
modules, so a quasi-isomorphism between two such modules is a homotopy equivalence on sections
and stays one after tensoring; a quasi-isomorphism is detected on sections on a chaotic site.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.pullbackHomotopyFunctor`: the functor `K(A) ⥤ K(A')`
  induced by the pullback.
* `SheafOfModules.DifferentialGradedModule.chaoticDerivedPullback`: **the derived pullback
  `Lg^* : D(A, d) ⥤ D(A', d)`**, and `chaoticDerivedPullbackCounit` its counit.
* `SheafOfModules.DifferentialGradedModule.chaoticDerivedPullbackObjIso`: `Lg^*P ≅ g^*P` for a
  module `P` whose sections are K-projective.
* `SheafOfModules.DifferentialGradedModule.chaoticDerivedPullbackSectionsIso`: **the derived
  sections of the derived pullback**, `RΓ(U', Lg^*K) ≅ RΓ(F U', K) ⊗^𝐋_{A(F U')} A'(U')`,
  naturally in `K`.

## Main results

* `SheafOfModules.DifferentialGradedModule.quasiIso_pullbackFunctor_map`: the pullback carries a
  quasi-isomorphism between modules whose sections are orthogonal on the left to the acyclic
  modules to a quasi-isomorphism.
* `SheafOfModules.DifferentialGradedModule.isLeftDerivedFunctor_chaoticDerivedPullback`: the
  counit exhibits `Lg^*` as the left derived functor.
* `SheafOfModules.DifferentialGradedModule.isIso_chaoticDerivedPullbackCounit_app`: the counit is
  an isomorphism at every module whose sections are K-projective.

## Implementation notes

The sites, their morphisms and the sheaves of rings live in one universe `u`, the setting in
which this library has the calculus of fractions of the quasi-isomorphisms (Tag 0FT4); the
differential graded algebras and modules live in a second universe `m`. The resolving class is
the one of `chaoticSectionGoodModuleData`; any other resolving class on which the pullback
inverts the quasi-isomorphisms gives the same functor up to unique isomorphism, the left derived
functor being a right Kan extension. The instance arguments `HasSheafCompose`, `HasWeakSheafify`
and `HasSheafify` for the chaotic topology are always satisfied, every presheaf being a sheaf; the
first is spelled out because instance search does not determine its universe.

## References

* [Stacks Project, Lemma 24.30.1 (Tag 0FTF)](https://stacks.math.columbia.edu/tag/0FTF)
* [Stacks Project, Definition 24.30.2 (Tag 0FTG)](https://stacks.math.columbia.edu/tag/0FTG)
* [Stacks Project, Section 24.33 (Tag 0GZ8)](https://stacks.math.columbia.edu/tag/0GZ8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf

universe m u

namespace SheafOfModules

namespace DifferentialGradedModule

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra
  Stacks.SheafOfModules.botWEqualsLocallyBijective

/-! ### Quasi-isomorphisms are detected on sections -/

section Detection

variable {C : Type u} [Category.{u} C]
  {R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{u}} {A : DifferentialGradedAlgebra.{u, m} R}

/-- **On a chaotic site a homomorphism is a quasi-isomorphism as soon as it is one on the
sections over every object.** -/
theorem quasiIso_of_forall_quasiIso_sectionMap {M N : DifferentialGradedModule.{u, m, m} A}
    (g : M ⟶ N)
    (h : ∀ U : Cᵒᵖ, QuasiIso ((_root_.DifferentialGradedModule.forgetToCochainComplex
      (A.sectionAlgebra U)).map (sectionMap g U))) :
    QuasiIso g.toHomologicalComplex := by
  refine (Stacks.SheafOfModules.quasiIso_iff_forall_quasiIso_evaluation.{u, m}
    g.toHomologicalComplex).2 fun U => ?_
  have h4 : QuasiIso (((Stacks.SheafOfModules.sectionsFunctor R U).mapHomologicalComplex
      (ComplexShape.up ℤ)).map g.toHomologicalComplex) :=
    (quasiIso_iff_of_arrow_mk_iso _ _ (sectionsArrowIso g U)).2 (h U)
  have h5 : QuasiIso (((forget₂ (ModuleCat.{m} (ULift.{m, 0} ℤ)) AddCommGrpCat.{m}
      ).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((Stacks.SheafOfModules.sectionsFunctor R U).mapHomologicalComplex
          (ComplexShape.up ℤ)).map g.toHomologicalComplex)) := inferInstance
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (forget₂ (ModuleCat.{m} (R.obj.obj U)) AddCommGrpCat.{m})).1 h5

end Detection

/-! ### The pullback on the homotopy categories -/

section Pullback

variable {C : Type u} [Category.{u} C] {C' : Type u} [Category.{u} C']
  [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
  {Osharp' : Sheaf (⊥ : GrothendieckTopology C') CommRingCat.{u}}
  {F : C' ⥤ C}
  {σ : F.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj ⟶
    (Stacks.SheafOfModules.Tensor.ringSheaf Osharp').obj}
  {A : DifferentialGradedAlgebra.{u, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
  {A' : DifferentialGradedAlgebra.{u, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp')}
  (φ : DifferentialGradedAlgebra.InverseImageHom F σ A A')

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The pullback carries a quasi-isomorphism between modules whose sections are orthogonal on
the left to the acyclic modules to a quasi-isomorphism.** -/
theorem quasiIso_pullbackFunctor_map {P P' : DifferentialGradedModule.{u, m, m} A}
    (f : P ⟶ P') (hf : QuasiIso f.toHomologicalComplex)
    (hP : ∀ U : Cᵒᵖ, (_root_.DifferentialGradedModule.acyclic' (A.sectionAlgebra U)).leftOrthogonal
      ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).obj
        (P.sectionModule U)))
    (hP' : ∀ U : Cᵒᵖ,
      (_root_.DifferentialGradedModule.acyclic' (A.sectionAlgebra U)).leftOrthogonal
        ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).obj
          (P'.sectionModule U))) :
    QuasiIso ((pullbackFunctor φ).map f).toHomologicalComplex := by
  refine quasiIso_of_forall_quasiIso_sectionMap _ fun U' => ?_
  have h3 := DifferentialGraded.Bimodule.isIso_tensorFunctorToDerivedCategory_map_of_leftOrthogonal
    (pullbackBimodule φ U')
    ((_root_.DifferentialGradedModule.toHomotopyCategory _).map (sectionMap f (F.op.obj U')))
    (quasiIsomorphisms_sectionMap f _ hf) (hP _) (hP' _)
  have h4 : IsIso (((DifferentialGraded.Bimodule.tensorCompFunctor (pullbackBimodule φ U') ⋙
      _root_.DifferentialGradedModule.toHomotopyCategory (A'.sectionAlgebra U')) ⋙
        (_root_.DifferentialGradedModule.quasiIsomorphisms' (A'.sectionAlgebra U')).Q).map
          (sectionMap f (F.op.obj U'))) :=
    (NatIso.isIso_map_iff (Functor.isoWhiskerRight
      (DifferentialGraded.Bimodule.tensorCompFunctor_quotient (pullbackBimodule φ U'))
      (_root_.DifferentialGradedModule.quasiIsomorphisms' (A'.sectionAlgebra U')).Q) _).2 h3
  have h5 : _root_.DifferentialGradedModule.quasiIsomorphisms' (A'.sectionAlgebra U')
      ((_root_.DifferentialGradedModule.toHomotopyCategory (A'.sectionAlgebra U')).map
        (pullbackSectionsMap φ f U')) :=
    _root_.DifferentialGradedModule.quasiIsomorphisms'_of_isIso_Q_map _ _ h4
  have h6 := (_root_.DifferentialGradedModule.quasiIsomorphisms_map_iff' _ _).1 h5
  have e : Arrow.mk (sectionMap ((pullbackFunctor φ).map f) U') ≅
      Arrow.mk (pullbackSectionsMap φ f U') :=
    Arrow.isoMk ((pullbackSystem φ P).sectionsIso U') ((pullbackSystem φ P').sectionsIso U')
      (SectionSystem.sectionsIso_naturality (pullbackSystemMap φ f) U').symm
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    ((_root_.DifferentialGradedModule.forgetToCochainComplex (A'.sectionAlgebra U')).mapArrow.mapIso
      e)).2 h6

/-- **The pullback on the homotopy categories** `K(A) ⥤ K(A')`. -/
def pullbackHomotopyFunctor : HomotopyCategory.{u, m, m} A ⥤ HomotopyCategory.{u, m, m} A' :=
  HomotopyCategory.descend (pullbackFunctor φ) (preservesHomotopic_pullbackFunctor φ)

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The quotient functor `Mod(A, d) ⥤ K(A)` followed by the pullback on the homotopy categories
equals the pullback followed by the quotient functor `Mod(A', d) ⥤ K(A')`. -/
theorem quotient_comp_pullbackHomotopyFunctor :
    HomotopyCategory.quotient A ⋙ pullbackHomotopyFunctor φ =
      pullbackFunctor φ ⋙ HomotopyCategory.quotient A' :=
  HomotopyCategory.quotient_comp_descend _ _

variable [HasWeakSheafify (⊥ : GrothendieckTopology C) (Type m)]
  [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  [HasSheafify (⊥ : GrothendieckTopology C') AddCommGrpCat.{m}]

variable (A) in
/-- The objects of `K(A)` represented by a module whose sections over every object are
orthogonal on the left to the acyclic modules (K-projective): the resolving class of the
derived pullback. -/
def sectionGoodProperty : ObjectProperty (HomotopyCategory.{u, m, m} A) :=
  fun Y => ∀ U : Cᵒᵖ, (_root_.DifferentialGradedModule.acyclic' (A.sectionAlgebra U)).leftOrthogonal
    ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).obj
      (Y.as.sectionModule U))

variable (A) in
/-- Every object of `K(A)` receives a quasi-isomorphism from an object of the resolving class. -/
theorem exists_sectionGoodProperty (X : HomotopyCategory.{u, m, m} A) :
    ∃ (Y : HomotopyCategory.{u, m, m} A) (_ : sectionGoodProperty A Y) (s : Y ⟶ X),
      quasiIsomorphisms.{u, m, m} A s := by
  obtain ⟨Q, f, hf, hg, hk, hs⟩ := exists_flat_quasiIso_sectionwise (A := A) X.as
  exact ⟨(HomotopyCategory.quotient A).obj Q, hs, (HomotopyCategory.quotient A).map f,
    (quasiIsomorphisms_quotient_map_iff f).2 hf⟩

/-- The pullback followed by the localization functor `K(A') ⥤ D(A', d)`, the functor whose left
derived functor is `Lg^*`. -/
abbrev pullbackToDerived : HomotopyCategory.{u, m, m} A ⥤ derivedCategory.{u, m, m} A' :=
  pullbackHomotopyFunctor φ ⋙ toDerivedCategory.{u, m, m} A'

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify (⊥ : GrothendieckTopology C) (Type m)] in
/-- **The pullback inverts the quasi-isomorphisms between objects of the resolving class**, after
localization. -/
theorem isIso_pullbackToDerived_map {X Y : HomotopyCategory.{u, m, m} A} (s : X ⟶ Y)
    (hs : quasiIsomorphisms.{u, m, m} A s) (hX : sectionGoodProperty A X)
    (hY : sectionGoodProperty A Y) : IsIso ((pullbackToDerived φ).map s) := by
  obtain ⟨ψ, rfl⟩ := (HomotopyCategory.quotient A).map_surjective s
  have hψ := (quasiIsomorphisms_quotient_map_iff ψ).1 hs
  have h := quasiIso_pullbackFunctor_map φ ψ hψ hX hY
  have h' : quasiIsomorphisms.{u, m, m} A'
      ((HomotopyCategory.quotient A').map ((pullbackFunctor φ).map ψ)) :=
    (quasiIsomorphisms_quotient_map_iff _).2 h
  exact (quasiIsomorphisms.{u, m, m} A').Q_inverts _ h'

variable (A) in
omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify (⊥ : GrothendieckTopology C) (Type m)] in
/-- On a chaotic site, the quasi-isomorphisms of `K(A)` have a right calculus of fractions: this
is Tag 0FT4 for the ringed site `(C, ⊥, O)`. -/
theorem hasRightCalculusOfFractions_quasiIsomorphisms :
    (quasiIsomorphisms.{u, m, m} A).HasRightCalculusOfFractions :=
  quasiIsomorphisms_hasRightCalculusOfFractions (X := ⟨C, ⊥, Osharp⟩) A

attribute [local instance] hasRightCalculusOfFractions_quasiIsomorphisms

/-- The pullback followed by localization has a pointwise left derived functor. -/
theorem hasPointwiseLeftDerivedFunctor_pullbackToDerived :
    (pullbackToDerived φ).HasPointwiseLeftDerivedFunctor (quasiIsomorphisms.{u, m, m} A) :=
  LeftDerivedByResolutions.hasPointwiseLeftDerivedFunctor_of_resolutions
    (quasiIsomorphisms.{u, m, m} A) (sectionGoodProperty A) (exists_sectionGoodProperty A) _
    (fun s hs hX hY => isIso_pullbackToDerived_map φ s hs hX hY)

/-- The pullback followed by localization has a left derived functor with respect to the
quasi-isomorphisms of `K(A)`. -/
theorem hasLeftDerivedFunctor_pullbackToDerived :
    (pullbackToDerived φ).HasLeftDerivedFunctor (quasiIsomorphisms.{u, m, m} A) :=
  have := hasPointwiseLeftDerivedFunctor_pullbackToDerived φ
  Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor _ _

/-- **The derived pullback `Lg^* : D(A, d) ⥤ D(A', d)`** along the morphism of chaotic ringed sites
given by `F`, `σ` and `φ`: the total left derived functor of the pullback
`M ↦ g^*M = g⁻¹M ⊗_{g⁻¹A} A'` followed by the localization functor `K(A') ⥤ D(A', d)`
(Tags 0FTF and 0FTG). -/
def chaoticDerivedPullback : derivedCategory.{u, m, m} A ⥤ derivedCategory.{u, m, m} A' :=
  haveI := hasLeftDerivedFunctor_pullbackToDerived φ
  (pullbackToDerived φ).totalLeftDerived (toDerivedCategory.{u, m, m} A)
    (quasiIsomorphisms.{u, m, m} A)

/-- The counit of the derived pullback: the canonical maps `Lg^*M → g^*M`. -/
def chaoticDerivedPullbackCounit :
    toDerivedCategory.{u, m, m} A ⋙ chaoticDerivedPullback φ ⟶ pullbackToDerived φ :=
  haveI := hasLeftDerivedFunctor_pullbackToDerived φ
  (pullbackToDerived φ).totalLeftDerivedCounit (toDerivedCategory.{u, m, m} A)
    (quasiIsomorphisms.{u, m, m} A)

/-- The counit `chaoticDerivedPullbackCounit φ` exhibits `Lg^*` as the left derived functor of
`pullbackToDerived φ` with respect to the quasi-isomorphisms of `K(A)`. -/
instance isLeftDerivedFunctor_chaoticDerivedPullback :
    (chaoticDerivedPullback φ).IsLeftDerivedFunctor (chaoticDerivedPullbackCounit φ)
      (quasiIsomorphisms.{u, m, m} A) :=
  haveI := hasLeftDerivedFunctor_pullbackToDerived φ
  show ((pullbackToDerived φ).totalLeftDerived (toDerivedCategory.{u, m, m} A)
      (quasiIsomorphisms.{u, m, m} A)).IsLeftDerivedFunctor
    ((pullbackToDerived φ).totalLeftDerivedCounit (toDerivedCategory.{u, m, m} A)
      (quasiIsomorphisms.{u, m, m} A)) (quasiIsomorphisms.{u, m, m} A) from inferInstance

/-- **The value of the derived pullback on a module whose sections are K-projective** is its
pullback: the counit is an isomorphism there. -/
theorem isIso_chaoticDerivedPullbackCounit_app {P : DifferentialGradedModule.{u, m, m} A}
    (hP : ∀ U : Cᵒᵖ,
      (_root_.DifferentialGradedModule.acyclic' (A.sectionAlgebra U)).leftOrthogonal
        ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).obj
          (P.sectionModule U))) :
    IsIso ((chaoticDerivedPullbackCounit φ).app ((HomotopyCategory.quotient A).obj P)) :=
  LeftDerivedByResolutions.isIso_app_of_resolutions (quasiIsomorphisms.{u, m, m} A)
    (sectionGoodProperty A) (exists_sectionGoodProperty A) _
    (fun s hs hX hY => isIso_pullbackToDerived_map φ s hs hX hY)
    (toDerivedCategory.{u, m, m} A) (chaoticDerivedPullback φ) (chaoticDerivedPullbackCounit φ)
    ((HomotopyCategory.quotient A).obj P) hP

/-- `Lg^*P ≅ g^*P` for a module `P` whose sections are K-projective. -/
def chaoticDerivedPullbackObjIso {P : DifferentialGradedModule.{u, m, m} A}
    (hP : ∀ U : Cᵒᵖ,
      (_root_.DifferentialGradedModule.acyclic' (A.sectionAlgebra U)).leftOrthogonal
        ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).obj
          (P.sectionModule U))) :
    (chaoticDerivedPullback φ).obj
        ((toDerivedCategory.{u, m, m} A).obj ((HomotopyCategory.quotient A).obj P)) ≅
      (toDerivedCategory.{u, m, m} A').obj
        ((HomotopyCategory.quotient A').obj ((pullbackFunctor φ).obj P)) :=
  @asIso _ _ _ _ _ (isIso_chaoticDerivedPullbackCounit_app φ hP)

/-! ### The derived sections of the derived pullback -/

section Sections

variable (U' : C'ᵒᵖ)

/-- The derived base change `- ⊗^𝐋_{A(F U')} A'(U')` along the homomorphism of sections. -/
abbrev sectionDerivedBaseChange :
    _root_.DifferentialGradedModule.derivedCategory' (A.sectionAlgebra (F.op.obj U')) ⥤
      _root_.DifferentialGradedModule.derivedCategory' (A'.sectionAlgebra U') :=
  DifferentialGraded.Bimodule.derivedTensorFunctor (pullbackBimodule φ U')

/-- The sections over `U'` of the pullback are the plain base change of the sections over
`F U'`, naturally in the module. -/
def pullbackSectionsNatIso :
    pullbackFunctor φ ⋙ sectionModuleFunctor A' U' ≅
      sectionModuleFunctor A (F.op.obj U') ⋙
        DifferentialGraded.Bimodule.tensorCompFunctor (pullbackBimodule φ U') :=
  NatIso.ofComponents (fun M => (pullbackSystem φ M).sectionsIso U')
    (fun f => SectionSystem.sectionsIso_naturality (pullbackSystemMap φ f) U')

/-- The functor `K(A) ⥤ D(A'(U'))`, `M ↦ M(F U') ⊗_{A(F U')} A'(U')`, of which the derived
sections over `U'` of the derived pullback and the derived base change of the derived sections
over `F U'` are both left derived functors. -/
abbrev sectionsBaseChangeToDerived :
    HomotopyCategory.{u, m, m} A ⥤
      _root_.DifferentialGradedModule.derivedCategory' (A'.sectionAlgebra U') :=
  sectionHomotopyFunctor A (F.op.obj U') ⋙
    DifferentialGraded.Bimodule.tensorFunctorToDerivedCategory (pullbackBimodule φ U')

/-- The two descriptions of the functor `M ↦ M(F U') ⊗_{A(F U')} A'(U')` out of `K(A)`: the
derived sections over `U'` of the pullback, and the base change of the sections. -/
def pullbackToDerivedSectionsIso :
    pullbackToDerived φ ⋙ derivedSections A' U' ≅ sectionsBaseChangeToDerived φ U' :=
  CategoryTheory.Quotient.natIsoLift _ <|
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eqToIso (quotient_comp_pullbackHomotopyFunctor φ))
      (toDerivedCategory.{u, m, m} A' ⋙ derivedSections A' U') ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (pullbackFunctor φ) (derivedSectionsIso A' U') ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (pullbackSectionsNatIso φ U')
      (_root_.DifferentialGradedModule.toHomotopyCategory (A'.sectionAlgebra U') ⋙
        (_root_.DifferentialGradedModule.quasiIsomorphisms' (A'.sectionAlgebra U')).Q) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (sectionModuleFunctor A (F.op.obj U'))
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (DifferentialGraded.Bimodule.tensorCompFunctor_quotient (pullbackBimodule φ U'))
          (_root_.DifferentialGradedModule.quasiIsomorphisms' (A'.sectionAlgebra U')).Q ≪≫
        Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sectionHomotopyFunctorIso A (F.op.obj U')).symm
      (DifferentialGraded.Bimodule.tensorFunctorToDerivedCategory (pullbackBimodule φ U')) ≪≫
    Functor.associator _ _ _

/-- The comparison exhibiting the derived base change of the derived sections over `F U'` as a
left derived functor of `M ↦ M(F U') ⊗_{A(F U')} A'(U')`: the factorization of the derived
sections through the sections, followed by the comparison of the derived tensor product with the
plain one. -/
def sectionsBaseChangeCounit :
    toDerivedCategory.{u, m, m} A ⋙ (derivedSections A (F.op.obj U') ⋙
      sectionDerivedBaseChange φ U') ⟶ sectionsBaseChangeToDerived φ U' :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (derivedSectionsFactorization A (F.op.obj U')).hom
      (sectionDerivedBaseChange φ U') ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (sectionHomotopyFunctor A (F.op.obj U'))
      (DifferentialGraded.Bimodule.derivedTensorFunctorCounit (pullbackBimodule φ U'))

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify (⊥ : GrothendieckTopology C) (Type m)]
  [HasSheafify (⊥ : GrothendieckTopology C') AddCommGrpCat.{m}] in
/-- The comparison `sectionsBaseChangeCounit φ U'` is an isomorphism at every object of `K(A)`
whose sections are K-projective. -/
theorem isIso_sectionsBaseChangeCounit_app {X : HomotopyCategory.{u, m, m} A}
    (hX : sectionGoodProperty A X) : IsIso ((sectionsBaseChangeCounit φ U').app X) := by
  have h := DifferentialGraded.Bimodule.isIso_derivedTensorFunctorCounit_app_of_leftOrthogonal
    (pullbackBimodule φ U') ((sectionHomotopyFunctor A (F.op.obj U')).obj X) (hX _)
  simp only [sectionsBaseChangeCounit, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Category.id_comp]
  infer_instance

/-- The derived sections over `U'` of the derived pullback are a left derived functor of
`M ↦ M(F U') ⊗_{A(F U')} A'(U')`, the derived pullback being computed by resolutions. -/
instance isLeftDerivedFunctor_chaoticDerivedPullback_comp_derivedSections :
    (chaoticDerivedPullback φ ⋙ derivedSections A' U').IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (chaoticDerivedPullbackCounit φ) (derivedSections A' U'))
      (quasiIsomorphisms.{u, m, m} A) :=
  LeftDerivedByResolutions.isLeftDerivedFunctor_postcomp_of_resolutions
    (quasiIsomorphisms.{u, m, m} A) (sectionGoodProperty A) (exists_sectionGoodProperty A) _
    (fun s hs hX hY => isIso_pullbackToDerived_map φ s hs hX hY)
    (toDerivedCategory.{u, m, m} A) (chaoticDerivedPullback φ) (chaoticDerivedPullbackCounit φ)
    (derivedSections A' U')

/-- There is an isomorphism `RΓ(U', Lg^*K) ≅ RΓ(F U', K) ⊗^𝐋_{A(F U')} A'(U')`, natural in `K`,
compatible with the comparisons of both sides with `M ↦ M(F U') ⊗_{A(F U')} A'(U')`. -/
theorem exists_chaoticDerivedPullbackSectionsIso :
    ∃ E : chaoticDerivedPullback φ ⋙ derivedSections A' U' ≅
        derivedSections A (F.op.obj U') ⋙ sectionDerivedBaseChange φ U',
      Functor.whiskerLeft (toDerivedCategory.{u, m, m} A) E.hom ≫ sectionsBaseChangeCounit φ U' =
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (chaoticDerivedPullbackCounit φ) (derivedSections A' U')) ≫
          (pullbackToDerivedSectionsIso φ U').hom :=
  LeftDerivedByResolutions.exists_leftDerivedIso_of_resolutions
    (quasiIsomorphisms.{u, m, m} A) (sectionGoodProperty A) (exists_sectionGoodProperty A)
    (pullbackToDerived φ ⋙ derivedSections A' U') (sectionsBaseChangeToDerived φ U')
    (pullbackToDerivedSectionsIso φ U')
    (fun s hs hX hY => by
      have h : IsIso ((pullbackToDerived φ).map s) := isIso_pullbackToDerived_map φ s hs hX hY
      exact Functor.map_isIso (derivedSections A' U') ((pullbackToDerived φ).map s))
    (toDerivedCategory.{u, m, m} A) _ _ _ (sectionsBaseChangeCounit φ U')
    (fun X hX => isIso_sectionsBaseChangeCounit_app φ U' hX)

/-- **The derived sections of the derived pullback**:
`RΓ(U', Lg^*K) ≅ RΓ(F U', K) ⊗^𝐋_{A(F U')} A'(U')`, naturally in `K`. It is the canonical
isomorphism of two left derived functors of `M ↦ M(F U') ⊗_{A(F U')} A'(U')`, compatible with
their comparisons with that functor (`chaoticDerivedPullbackSectionsIso_spec`). -/
def chaoticDerivedPullbackSectionsIso :
    chaoticDerivedPullback φ ⋙ derivedSections A' U' ≅
      derivedSections A (F.op.obj U') ⋙ sectionDerivedBaseChange φ U' :=
  (exists_chaoticDerivedPullbackSectionsIso φ U').choose

/-- The isomorphism `chaoticDerivedPullbackSectionsIso φ U'` is compatible with the comparisons
of both sides with `M ↦ M(F U') ⊗_{A(F U')} A'(U')`. -/
theorem chaoticDerivedPullbackSectionsIso_spec :
    Functor.whiskerLeft (toDerivedCategory.{u, m, m} A)
        (chaoticDerivedPullbackSectionsIso φ U').hom ≫ sectionsBaseChangeCounit φ U' =
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (chaoticDerivedPullbackCounit φ) (derivedSections A' U')) ≫
        (pullbackToDerivedSectionsIso φ U').hom :=
  (exists_chaoticDerivedPullbackSectionsIso φ U').choose_spec

end Sections

end Pullback

end DifferentialGradedModule

end SheafOfModules

end
