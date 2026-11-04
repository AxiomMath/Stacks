module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.ExtensionOfScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModuleTensor.DerivedTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModuleTensor.TensorBifunctorInstances
public import StacksFrontier.Homology.KFlat.BifunctorSingleSecondFactor
public import StacksFrontier.CategoryTheory.Localization.LeftDerivedByResolutions
public import StacksFrontier.Homology.KFlat.AcyclicKFlat
public import StacksFrontier.Algebra.Homology.MapHomologicalComplexExactness
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import StacksFrontier.Algebra.Homology.TotalSingleRowNaturality
public import StacksFrontier.Homology.KFlat.BifunctorOneSidedLeft
public import StacksFrontier.Homology.KFlat.BifunctorTransport

/-!
# Derived extension of coefficients for étale sheaves of modules

Let `φ : Λ₁ → Λ₂` be a homomorphism of commutative rings and `X` a scheme.  This file constructs
the functor `- ⊗^L_{Λ₁} Λ₂ : D(X_étale, Λ₁) ⥤ D(X_étale, Λ₂)`, the horizontal arrow of the second
diagram of [Stacks, Remark 0GL6], as the total left derived functor of extension of
coefficients, and proves that it is left adjoint to restriction of coefficients.

## Main definitions

* `Stacks.EtaleCohomology.coefficientSheaf`: the constant sheaf `Λ̲₂` of `Λ₁`-modules.
* `Stacks.EtaleCohomology.etaleModuleExtendRestrictScalarsIso`: `res(F ⊗_{Λ₁} Λ₂) ≅ F ⊗_{Λ₁} Λ̲₂`.
* `Stacks.EtaleCohomology.etaleModuleDerivedExtendScalars`: derived extension of coefficients.
* `Stacks.EtaleCohomology.etaleModuleDerivedExtendRestrictAdj`: it is left adjoint to
  `Stacks.EtaleCohomology.etaleModuleDerivedRestrictScalars`.
* `Stacks.EtaleCohomology.etaleModuleDerivedExtendRestrictScalarsIso`: followed by restriction of
  coefficients it is `- ⊗^L_{Λ₁} Λ̲₂`, the derived tensor product with the constant sheaf.

## Main results

* `Stacks.EtaleCohomology.quasiIso_etaleModuleExtendScalars_map_of_kFlatLeft`: extension of
  coefficients preserves quasi-isomorphisms between complexes which are K-flat for the tensor
  product over `Λ₁`.
* `Stacks.EtaleCohomology.isIso_etaleModuleDerivedExtendScalarsCounit_app`: on such a complex the
  derived functor is extension of coefficients degreewise.

## Implementation notes

Extension of coefficients is only right exact, so it is derived along K-flat resolutions
(`Stacks.EtaleCohomology.exists_etaleModule_kFlatResolution`).  That it preserves the
quasi-isomorphisms between K-flat complexes is checked after restriction of coefficients, which
is faithful and exact, where extension of coefficients becomes tensoring with the constant sheaf
`Λ̲₂` (`etaleModuleExtendRestrictScalarsIso`).  The derived functor is built on the homotopy
category by `CategoryTheory.LeftDerivedByResolutions`, and the adjunction is
`CategoryTheory.Adjunction.derived` applied to the adjunction of the homotopy categories.

## References

* [Stacks Project, Remark 0GL6](https://stacks.math.columbia.edu/tag/0GL6)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
  [HasDerivedCategory D]

/-- Two naturality squares compose vertically. -/
theorem comp_naturality_of_squares {C : Type*} [Category C] {x x' y y' z z' : C}
    {u : x ⟶ x'} {m : y ⟶ y'} {v : z ⟶ z'} {a : x ⟶ y} {a' : x' ⟶ y'} {b : y ⟶ z}
    {b' : y' ⟶ z'} (h₁ : u ≫ a' = a ≫ m) (h₂ : m ≫ b' = b ≫ v) :
    u ≫ a' ≫ b' = (a ≫ b) ≫ v := by
  rw [reassoc_of% h₁, h₂, Category.assoc]

/-- `Tot(F(-, G))`, read in the homotopy category and localized, is `H` localized, for any
functor `H` on complexes identified with `Tot(F(-, G))`: `totalComplexQhIso` followed by the
identification. -/
def totalComplexQhFlipIso (G : CochainComplex B ℤ) {H : CochainComplex A ℤ ⥤ CochainComplex D ℤ}
    (e : (F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)).flip.obj G ≅ H) :
    HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙
        (homotopyBifunctor F).flip.obj ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj G) ⋙
        DerivedCategory.Qh ≅ H ⋙ DerivedCategory.Q :=
  NatIso.ofComponents (fun K => totalComplexQhIso F K G ≪≫ DerivedCategory.Q.mapIso (e.app K))
    (fun f => comp_naturality_of_squares (totalComplexQhIso_naturality_left F f G)
      ((DerivedCategory.Q.map_comp _ _).symm.trans ((congrArg DerivedCategory.Q.map
        (e.hom.naturality f)).trans (DerivedCategory.Q.map_comp _ _))))

/-- The component of `totalComplexQhFlipIso` at a complex `K` is `totalComplexQhIso` at `K`
followed by the image under `DerivedCategory.Q` of the component of `e` at `K`. -/
theorem totalComplexQhFlipIso_hom_app (G : CochainComplex B ℤ)
    {H : CochainComplex A ℤ ⥤ CochainComplex D ℤ}
    (e : (F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)).flip.obj G ≅ H) (K : CochainComplex A ℤ) :
    (totalComplexQhFlipIso F G e).hom.app K =
      (totalComplexQhIso F K G).hom ≫ DerivedCategory.Q.map (e.hom.app K) := rfl

end CochainComplex.KFlatBifunctor

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleMonoidalCategory etaleModuleBraidedCategory

/- The instance proofs `F.Additive`, `(F.obj X).Additive` and `HasMapBifunctor` for the tensor
product over `Λ₁` are the named ones of `ModuleTensor.TensorBifunctorInstances`, stated as
`etaleModuleDerivedTensor` records them, so that every `derivedBifunctor (etaleModuleTensor Λ₁ X)`
written here is the unfolding of `etaleModuleDerivedTensor Λ₁ X` up to proofs of the same
propositions; with independently synthesized proofs the kernel compares the two by evaluating the
derived bifunctor, which is prohibitively slow. -/
attribute [local instance high] etaleModuleTensor_additive etaleModuleTensor_obj_additive
  etaleModuleTensor_hasTotal_mapBifunctor

variable {Λ₁ Λ₂ : Type r} [CommRing Λ₁] [CommRing Λ₂] (φ : Λ₁ →+* Λ₂)

/-- The ring `Λ₂`, regarded as a `Λ₁`-module in the coefficient universe of étale sheaves. -/
abbrev coefficientModule : ModuleCat.{max (u + 1) r} Λ₁ :=
  (ModuleCat.restrictScalars φ).obj (ModuleCat.of Λ₂ (ULift.{max (u + 1) r} Λ₂))

/-- Extension of scalars along `φ` followed by restriction of scalars is tensoring on the right
with `Λ₂`, regarded as a `Λ₁`-module. -/
def extendRestrictScalarsIsoTensorRight :
    ModuleCat.extendScalars.{r, r, max (u + 1) r} φ ⋙ ModuleCat.restrictScalars φ ≅
      tensorRight (coefficientModule.{u} φ) := by
  letI := φ.toAlgebra
  exact NatIso.ofComponents (fun M =>
    ((TensorProduct.comm Λ₁ _ _).trans (TensorProduct.congr
      (ULift.moduleEquiv : ULift.{max (u + 1) r} Λ₂ ≃ₗ[Λ₁] Λ₂)
      (LinearEquiv.refl Λ₁ M))).symm.toModuleIso) (by
        intros
        ext : 1
        apply TensorProduct.ext'
        intros
        rfl)

section Sheaf

variable (X : Scheme.{u})

/-- Restriction of scalars preserves sheafification on the small étale site, being a left
adjoint. -/
local instance restrictScalars_preservesSheafification :
    X.smallEtaleTopology.PreservesSheafification
      (ModuleCat.restrictScalars.{max (u + 1) r} φ) :=
  Sheaf.preservesSheafification_of_adjunction _
    (ModuleCat.restrictCoextendScalarsAdj.{max (u + 1) r} φ)

/-- Postcomposition with tensoring on the right by a module is tensoring on the right by the
constant presheaf. -/
def whiskeringRightTensorRightIso {C : Type*} [Category C] {A : Type*} [Category A]
    [MonoidalCategory A] (M : A) :
    (Functor.whiskeringRight C A A).obj (tensorRight M) ≅
      tensorRight ((Functor.const C).obj M) :=
  NatIso.ofComponents (fun P => NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro U V f
    simp [tensorHom_def])) (by
    intro P Q g
    ext U
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The constant étale sheaf of `Λ₁`-modules with value `Λ₂`. -/
abbrev coefficientSheaf : EtaleModules.{u, r} Λ₁ X :=
  (presheafToSheaf X.smallEtaleTopology _).obj
    ((Functor.const X.Etaleᵒᵖ).obj (coefficientModule.{u} φ))

attribute [local instance] isMonoidal_W_smallEtale_module in
/-- Sheafification of étale presheaves of `Λ₁`-modules carries tensoring on the right by a
presheaf to tensoring on the right by its sheafification. -/
def tensorRightPresheafToSheafIso (Q : X.Etaleᵒᵖ ⥤ ModuleCat.{max (u + 1) r} Λ₁) :
    tensorRight Q ⋙ presheafToSheaf X.smallEtaleTopology _ ≅
      presheafToSheaf X.smallEtaleTopology _ ⋙
        tensorRight ((presheafToSheaf X.smallEtaleTopology _).obj Q) :=
  NatIso.ofComponents
    (fun P => (Functor.Monoidal.μIso (presheafToSheaf X.smallEtaleTopology _) P Q).symm)
    (by
      intro P P' g
      simp [Functor.OplaxMonoidal.δ_natural_left])

attribute [local instance] isMonoidal_W_smallEtale_module in
/-- **Extension of coefficients followed by restriction of coefficients is tensoring with the
constant sheaf `Λ₂`.**  For an étale sheaf `F` of `Λ₁`-modules, `res(F ⊗_{Λ₁} Λ₂)` is
`F ⊗_{Λ₁} Λ̲₂`. -/
def etaleModuleExtendRestrictScalarsIso :
    etaleModuleExtendScalarsUniv.{u, r} φ X ⋙ etaleModuleRestrictScalarsUniv.{u, r} φ X ≅
      tensorRight (coefficientSheaf.{u} φ X) :=
  let J := X.smallEtaleTopology
  let adj₁ := sheafificationAdjunction J (ModuleCat.{max (u + 1) r} Λ₂)
  let adj₂ := sheafificationAdjunction J (ModuleCat.{max (u + 1) r} Λ₁)
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf J _) (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (sheafComposeNatIso J
        (ModuleCat.restrictScalars.{max (u + 1) r} φ) adj₁ adj₂).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ((Functor.whiskeringRight _ _ _).mapIso
          (extendRestrictScalarsIsoTensorRight.{u} φ) ≪≫
        whiskeringRightTensorRightIso _) _ ≪≫
      tensorRightPresheafToSheafIso X _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso adj₂.counit) _ ≪≫ Functor.leftUnitor _

end Sheaf

section Acyclic

open CochainComplex.KFlatBifunctor

variable (X : Scheme.{u})

/-- Extension of coefficients is additive, being left adjoint to an additive functor. -/
instance etaleModuleExtendScalars_additive : (etaleModuleExtendScalarsUniv.{u, r} φ X).Additive :=
  (etaleModuleExtendRestrictAdj.{u, r} φ X).left_adjoint_additive

/-- The termwise complex `p ↦ Kᵖ ⊗_{Λ₁} M` is tensoring on the right with `M` applied
degreewise. -/
def rowComplexIsoMapTensorRight (K : CochainComplex (EtaleModules.{u, r} Λ₁ X) ℤ)
    (M : EtaleModules.{u, r} Λ₁ X) :
    rowComplex (etaleModuleTensor.{u, r} Λ₁ X) K M ≅
      ((tensorRight M).mapHomologicalComplex (ComplexShape.up ℤ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j _
    simp [rowComplex])

/-- **Extension of coefficients carries an acyclic complex which is K-flat in the left variable
of the tensor product to an acyclic complex.**  After restriction of coefficients, which detects
acyclicity, it is `K ⊗_{Λ₁} Λ̲₂`, the total complex of `K` against the constant sheaf `Λ̲₂`
placed in degree zero, which is acyclic by K-flatness of `K` and a K-flat resolution of `Λ̲₂`. -/
theorem acyclic_etaleModuleExtendScalars_of_kFlatLeft
    (K : CochainComplex (EtaleModules.{u, r} Λ₁ X) ℤ)
    (hK : KFlatLeft (etaleModuleTensor.{u, r} Λ₁ X) K) (hKac : K.Acyclic) :
    (((etaleModuleExtendScalarsUniv.{u, r} φ X).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).Acyclic := by
  let F := etaleModuleTensor.{u, r} Λ₁ X
  let M := coefficientSheaf.{u} φ X
  let G := (HomologicalComplex.single (EtaleModules.{u, r} Λ₁ X) (ComplexShape.up ℤ) 0).obj M
  obtain ⟨P, q, hP, -, -, hq, -⟩ := exists_etaleModule_kFlatResolution Λ₁ X G
  have h₁ : (totalComplex F.flip G K).Acyclic :=
    acyclic_totalComplex_of_kFlat_of_acyclic F.flip
      ((kFlatLeft_iff_kFlat_flip F K).1 hK) hKac q hq
      ((kFlatLeft_iff_kFlat_flip F.flip P).2 hP)
  exact (HomologicalComplex.acyclic_map_iff_of_preservesHomology _
    (etaleModuleRestrictScalarsUniv.{u, r} φ X)).1 fun i =>
    ((((((h₁ i).of_iso (HomologicalComplex.mapBifunctorFlipIso K G F (ComplexShape.up ℤ))).of_iso
      (totalSingleIso F K M)).of_iso (rowComplexIsoMapTensorRight X K M)).of_iso
      ((NatIso.mapHomologicalComplex (etaleModuleExtendRestrictScalarsIso φ X)
        (ComplexShape.up ℤ)).app K).symm).of_iso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).app K).symm)

/-- **Extension of coefficients carries a quasi-isomorphism between complexes which are K-flat
in the left variable of the tensor product to a quasi-isomorphism.**  The mapping cone is again
K-flat in the left variable, and acyclic, so its extension of coefficients is acyclic by
`acyclic_etaleModuleExtendScalars_of_kFlatLeft`; that is the mapping cone of the extended
morphism. -/
theorem quasiIso_etaleModuleExtendScalars_map_of_kFlatLeft
    {K L : CochainComplex (EtaleModules.{u, r} Λ₁ X) ℤ} (f : K ⟶ L) (hf : QuasiIso f)
    (hK : KFlatLeft (etaleModuleTensor.{u, r} Λ₁ X) K)
    (hL : KFlatLeft (etaleModuleTensor.{u, r} Λ₁ X) L) :
    QuasiIso (((etaleModuleExtendScalarsUniv.{u, r} φ X).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f) := by
  let F := etaleModuleTensor.{u, r} Λ₁ X
  have hC : KFlatLeft F (CochainComplex.mappingCone f) :=
    (kFlatLeft_iff_kFlat_flip F _).2 (kFlat_obj₃_of_distTriang F.flip _ _ _
      (HomotopyCategory.mappingCone_triangleh_distinguished f)
      ((kFlatLeft_iff_kFlat_flip F K).1 hK) ((kFlatLeft_iff_kFlat_flip F L).1 hL))
  exact (quasiIso_iff_acyclic_mappingCone _).2 fun i =>
    (acyclic_etaleModuleExtendScalars_of_kFlatLeft φ X _ hC
      ((quasiIso_iff_acyclic_mappingCone f).1 hf) i).of_iso
      (CochainComplex.mappingCone.mapHomologicalComplexIso f _)

end Acyclic

section Derived

attribute [local instance] HasDerivedCategory.standard

open CochainComplex.KFlatBifunctor CategoryTheory.LeftDerivedByResolutions

variable (X : Scheme.{u})

/-- The complexes K-flat in the left variable of the tensor product over `Λ₁`, in the homotopy
category: the resolving class for extension of coefficients. -/
abbrev kFlatLeftHomotopy :
    ObjectProperty (HomotopyCategory (EtaleModules.{u, r} Λ₁ X) (ComplexShape.up ℤ)) :=
  fun K => KFlatLeft (etaleModuleTensor.{u, r} Λ₁ X) K.as

/-- Every object of the homotopy category of étale sheaves of `Λ₁`-modules is resolved by a
complex K-flat in the left variable of the tensor product. -/
theorem exists_kFlatLeftHomotopy_resolution
    (K : HomotopyCategory (EtaleModules.{u, r} Λ₁ X) (ComplexShape.up ℤ)) :
    ∃ (P : HomotopyCategory (EtaleModules.{u, r} Λ₁ X) (ComplexShape.up ℤ))
      (_ : kFlatLeftHomotopy.{u, r} X P) (s : P ⟶ K),
      HomotopyCategory.quasiIso _ (ComplexShape.up ℤ) s := by
  obtain ⟨P, p, hP, hp⟩ := exists_etaleModule_kFlatLeft_quasiIso Λ₁ X K.as
  exact ⟨(HomotopyCategory.quotient _ _).obj P, hP, (HomotopyCategory.quotient _ _).map p,
    (HomotopyCategory.quotient_map_mem_quasiIso_iff p).2 hp⟩

/-- Extension of coefficients on the homotopy category, followed by localization. -/
abbrev etaleModuleExtendScalarsHomotopy :
    HomotopyCategory (EtaleModules.{u, r} Λ₁ X) (ComplexShape.up ℤ) ⥤
      DerivedCategory (EtaleModules.{u, r} Λ₂ X) :=
  (etaleModuleExtendScalarsUniv.{u, r} φ X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh

/-- Extension of coefficients, read on the homotopy category and localized, inverts a
quasi-isomorphism between complexes K-flat in the left variable. -/
theorem isIso_etaleModuleExtendScalarsHomotopy_map
    {K L : HomotopyCategory (EtaleModules.{u, r} Λ₁ X) (ComplexShape.up ℤ)} (s : K ⟶ L)
    (hs : HomotopyCategory.quasiIso _ (ComplexShape.up ℤ) s)
    (hK : kFlatLeftHomotopy.{u, r} X K) (hL : kFlatLeftHomotopy.{u, r} X L) :
    IsIso ((etaleModuleExtendScalarsHomotopy.{u, r} φ X).map s) := by
  have hout : QuasiIso s.out :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff s.out).1
      (by rwa [HomotopyCategory.quotient_map_out s])
  show IsIso (DerivedCategory.Qh.map
    (((etaleModuleExtendScalarsUniv.{u, r} φ X).mapHomotopyCategory (ComplexShape.up ℤ)).map s))
  rw [← HomotopyCategory.quotient_map_out s]
  exact (DerivedCategory.isIso_Qh_map_iff _).2
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
      (quasiIso_etaleModuleExtendScalars_map_of_kFlatLeft φ X s.out hout hK hL))

/-- Extension of coefficients, read on the homotopy category and localized, has a pointwise left
derived functor with respect to the quasi-isomorphisms. -/
instance etaleModuleExtendScalarsHomotopy_hasPointwiseLeftDerivedFunctor :
    (etaleModuleExtendScalarsHomotopy.{u, r} φ X).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (EtaleModules.{u, r} Λ₁ X) (ComplexShape.up ℤ)) :=
  hasPointwiseLeftDerivedFunctor_of_resolutions _ (kFlatLeftHomotopy.{u, r} X)
    (exists_kFlatLeftHomotopy_resolution X) _
    (isIso_etaleModuleExtendScalarsHomotopy_map φ X)

/-- **Derived extension of coefficients** `- ⊗^L_{Λ₁} Λ₂ : D(X_étale, Λ₁) ⥤ D(X_étale, Λ₂)`, the
total left derived functor of extension of coefficients, computed on complexes K-flat for the
tensor product over `Λ₁`. -/
def etaleModuleDerivedExtendScalars :
    DerivedCategory (EtaleModules.{u, r} Λ₁ X) ⥤ DerivedCategory (EtaleModules.{u, r} Λ₂ X) :=
  (etaleModuleExtendScalarsHomotopy.{u, r} φ X).totalLeftDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- The counit of derived extension of coefficients, comparing it with extension of
coefficients applied degreewise. -/
def etaleModuleDerivedExtendScalarsCounit :
    DerivedCategory.Qh ⋙ etaleModuleDerivedExtendScalars.{u, r} φ X ⟶
      etaleModuleExtendScalarsHomotopy.{u, r} φ X :=
  (etaleModuleExtendScalarsHomotopy.{u, r} φ X).totalLeftDerivedCounit DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- Derived extension of coefficients, with the counit `etaleModuleDerivedExtendScalarsCounit`,
is a left derived functor of extension of coefficients with respect to the quasi-isomorphisms. -/
instance etaleModuleDerivedExtendScalars_isLeftDerivedFunctor :
    (etaleModuleDerivedExtendScalars.{u, r} φ X).IsLeftDerivedFunctor
      (etaleModuleDerivedExtendScalarsCounit.{u, r} φ X)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) := by
  dsimp only [etaleModuleDerivedExtendScalars, etaleModuleDerivedExtendScalarsCounit]
  infer_instance

/-- The counit of derived extension of coefficients is invertible on a complex K-flat in the
left variable of the tensor product: there it is extension of coefficients degreewise. -/
theorem isIso_etaleModuleDerivedExtendScalarsCounit_app
    (K : HomotopyCategory (EtaleModules.{u, r} Λ₁ X) (ComplexShape.up ℤ))
    (hK : kFlatLeftHomotopy.{u, r} X K) :
    IsIso ((etaleModuleDerivedExtendScalarsCounit.{u, r} φ X).app K) :=
  isIso_app_of_resolutions _ (kFlatLeftHomotopy.{u, r} X)
    (exists_kFlatLeftHomotopy_resolution X) _
    (isIso_etaleModuleExtendScalarsHomotopy_map φ X)
    DerivedCategory.Qh _ _ K hK

/-- **Derived extension of coefficients is left adjoint to restriction of coefficients** on the
unbounded derived categories of étale sheaves of modules. -/
def etaleModuleDerivedExtendRestrictAdj :
    etaleModuleDerivedExtendScalars.{u, r} φ X ⊣ etaleModuleDerivedRestrictScalars.{u, r} φ X := by
  let W₁ := HomotopyCategory.quasiIso (EtaleModules.{u, r} Λ₁ X) (ComplexShape.up ℤ)
  let W₂ := HomotopyCategory.quasiIso (EtaleModules.{u, r} Λ₂ X) (ComplexShape.up ℤ)
  let LF := etaleModuleDerivedExtendScalars.{u, r} φ X
  let RG := etaleModuleDerivedRestrictScalars.{u, r} φ X
  let α := etaleModuleDerivedExtendScalarsCounit.{u, r} φ X
  let e := (etaleModuleRestrictScalarsUniv.{u, r} φ X).mapDerivedCategoryFactorsh
  have : RG.IsRightDerivedFunctor e.inv W₂ :=
    Functor.isRightDerivedFunctor_of_inverts W₂ RG e
  have : (LF ⋙ RG).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α RG) W₁ :=
    isLeftDerivedFunctor_postcomp_of_resolutions W₁ (kFlatLeftHomotopy.{u, r} X)
      (exists_kFlatLeftHomotopy_resolution X) _
      (isIso_etaleModuleExtendScalarsHomotopy_map φ X)
      DerivedCategory.Qh LF α RG
  have : (RG ⋙ LF).IsRightDerivedFunctor
      (Functor.whiskerRight e.inv LF ≫ (Functor.associator _ _ _).hom) W₂ :=
    Functor.isRightDerivedFunctor_of_inverts W₂ (RG ⋙ LF)
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e LF)
  exact ((etaleModuleExtendRestrictAdj.{u, r} φ X).mapHomotopyCategory
    (ComplexShape.up ℤ)).derived W₁ W₂ α e.inv

/-! ### Restriction of derived extension of coefficients is tensoring with `Λ̲₂` -/

/-- The constant sheaf `Λ̲₂` of `Λ₁`-modules, as a complex concentrated in degree zero. -/
abbrev coefficientSheafComplex : CochainComplex (EtaleModules.{u, r} Λ₁ X) ℤ :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (coefficientSheaf.{u} φ X)

/-- The comparison `res(Qh(K ⊗_{Λ₁} Λ₂)) ≅ Q(K ⊗_{Λ₁} Λ̲₂)` at a complex `K`: the isomorphism
`Qh ∘ quotient ≅ Q`, restriction of coefficients commuting with localization, and the
identification `res(F ⊗_{Λ₁} Λ₂) ≅ F ⊗_{Λ₁} Λ̲₂` degreewise. -/
def etaleModuleExtendScalarsRestrictComplexIsoApp
    (K : CochainComplex (EtaleModules.{u, r} Λ₁ X) ℤ) :
    (etaleModuleDerivedRestrictScalars.{u, r} φ X).obj
        ((HomotopyCategory.quotient _ _ ⋙ DerivedCategory.Qh).obj
          (((etaleModuleExtendScalarsUniv.{u, r} φ X).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)) ≅
      DerivedCategory.Q.obj
        (((tensorRight (coefficientSheaf.{u} φ X)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) :=
  (etaleModuleDerivedRestrictScalars.{u, r} φ X).mapIso
      ((DerivedCategory.quotientCompQhIso _).app
        (((etaleModuleExtendScalarsUniv.{u, r} φ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)) ≪≫
    (etaleModuleRestrictScalarsUniv.{u, r} φ X).mapDerivedCategoryFactors.app
      (((etaleModuleExtendScalarsUniv.{u, r} φ X).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) ≪≫
    DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso
      (etaleModuleExtendRestrictScalarsIso.{u, r} φ X) (ComplexShape.up ℤ)).app K)

/-- On complexes: extension of coefficients, localized and restricted back to `Λ₁`, is the
degreewise tensor product with `Λ̲₂`, localized. -/
def etaleModuleExtendScalarsRestrictComplexIso :
    HomotopyCategory.quotient _ _ ⋙ etaleModuleExtendScalarsHomotopy.{u, r} φ X ⋙
        etaleModuleDerivedRestrictScalars.{u, r} φ X ≅
      (tensorRight (coefficientSheaf.{u} φ X)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  NatIso.ofComponents (etaleModuleExtendScalarsRestrictComplexIsoApp φ X) (fun {K K'} f => by
    have h₁ : (etaleModuleDerivedRestrictScalars.{u, r} φ X).map (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient _ _).map
            (((etaleModuleExtendScalarsUniv.{u, r} φ X).mapHomologicalComplex
              (ComplexShape.up ℤ)).map f))) ≫
        (etaleModuleDerivedRestrictScalars.{u, r} φ X).map
          ((DerivedCategory.quotientCompQhIso _).hom.app
            (((etaleModuleExtendScalarsUniv.{u, r} φ X).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K')) =
        (etaleModuleDerivedRestrictScalars.{u, r} φ X).map
          ((DerivedCategory.quotientCompQhIso _).hom.app
            (((etaleModuleExtendScalarsUniv.{u, r} φ X).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)) ≫
        (etaleModuleDerivedRestrictScalars.{u, r} φ X).map (DerivedCategory.Q.map
          (((etaleModuleExtendScalarsUniv.{u, r} φ X).mapHomologicalComplex
            (ComplexShape.up ℤ)).map f)) := by
      rw [← Functor.map_comp, ← Functor.map_comp, DerivedCategory.quotientCompQhIso_hom_naturality]
    have h₂ := (etaleModuleRestrictScalarsUniv.{u, r} φ X).mapDerivedCategoryFactors_hom_naturality
      (((etaleModuleExtendScalarsUniv.{u, r} φ X).mapHomologicalComplex (ComplexShape.up ℤ)).map f)
    have h₃ : DerivedCategory.Q.map
          (((etaleModuleExtendScalarsUniv.{u, r} φ X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            (etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomologicalComplex
              (ComplexShape.up ℤ)).map f) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
          (etaleModuleExtendRestrictScalarsIso.{u, r} φ X) (ComplexShape.up ℤ)).hom.app K') =
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
          (etaleModuleExtendRestrictScalarsIso.{u, r} φ X) (ComplexShape.up ℤ)).hom.app K) ≫
        DerivedCategory.Q.map
          (((tensorRight (coefficientSheaf.{u} φ X)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map f) := by
      rw [← Functor.map_comp, ← Functor.map_comp, NatTrans.naturality]
    exact CochainComplex.KFlatBifunctor.comp_naturality_of_squares h₁
      (CochainComplex.KFlatBifunctor.comp_naturality_of_squares h₂ h₃))

/-- The identification of the total complex against `Λ̲₂` in degree zero with the degreewise
tensor product is natural in the complex. -/
theorem totalSingleIso_trans_rowComplexIsoMapTensorRight_naturality
    {K K' : CochainComplex (EtaleModules.{u, r} Λ₁ X) ℤ} (f : K ⟶ K') :
    HomologicalComplex.mapBifunctorMap f (𝟙 (coefficientSheafComplex.{u, r} φ X))
        (etaleModuleTensor.{u, r} Λ₁ X) (ComplexShape.up ℤ) ≫
      (totalSingleIso (etaleModuleTensor.{u, r} Λ₁ X) K' (coefficientSheaf.{u} φ X) ≪≫
        rowComplexIsoMapTensorRight X K' (coefficientSheaf.{u} φ X)).hom =
    (totalSingleIso (etaleModuleTensor.{u, r} Λ₁ X) K (coefficientSheaf.{u} φ X) ≪≫
        rowComplexIsoMapTensorRight X K (coefficientSheaf.{u} φ X)).hom ≫
      ((tensorRight (coefficientSheaf.{u} φ X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f := by
  rw [Iso.trans_hom, Iso.trans_hom, reassoc_of% (totalSingleIso_hom_naturality
    (etaleModuleTensor.{u, r} Λ₁ X) f (coefficientSheaf.{u} φ X)), Category.assoc]
  congr 1

/-- On complexes: the total complex against `Λ̲₂` placed in degree zero, read in the homotopy
category and localized, is the degreewise tensor product with `Λ̲₂`, localized. -/
def tensorCoefficientSheafComplexIso :
    HomotopyCategory.quotient _ _ ⋙
        (homotopyBifunctor (etaleModuleTensor.{u, r} Λ₁ X)).flip.obj
          ((HomotopyCategory.quotient _ _).obj (coefficientSheafComplex.{u, r} φ X)) ⋙
        DerivedCategory.Qh ≅
      (tensorRight (coefficientSheaf.{u} φ X)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  CochainComplex.KFlatBifunctor.totalComplexQhFlipIso (etaleModuleTensor.{u, r} Λ₁ X)
    (coefficientSheafComplex.{u, r} φ X)
    (NatIso.ofComponents
      (F := ((etaleModuleTensor.{u, r} Λ₁ X).map₂HomologicalComplex (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)).flip.obj (coefficientSheafComplex.{u, r} φ X))
      (G := (tensorRight (coefficientSheaf.{u} φ X)).mapHomologicalComplex (ComplexShape.up ℤ))
      (fun K => totalSingleIso (etaleModuleTensor.{u, r} Λ₁ X) K (coefficientSheaf.{u} φ X) ≪≫
        rowComplexIsoMapTensorRight X K (coefficientSheaf.{u} φ X))
      (fun f => totalSingleIso_trans_rowComplexIsoMapTensorRight_naturality φ X f))

/-- The component of `tensorCoefficientSheafComplexIso` at a complex: `totalComplexQhIso`
followed by the identification of the total complex against `Λ̲₂[0]`. -/
theorem tensorCoefficientSheafComplexIso_hom_app
    (K : CochainComplex (EtaleModules.{u, r} Λ₁ X) ℤ) :
    (tensorCoefficientSheafComplexIso.{u, r} φ X).hom.app K =
      (CochainComplex.KFlatBifunctor.totalComplexQhIso (etaleModuleTensor.{u, r} Λ₁ X) K
          (coefficientSheafComplex.{u, r} φ X)).hom ≫
        DerivedCategory.Q.map
          (totalSingleIso (etaleModuleTensor.{u, r} Λ₁ X) K (coefficientSheaf.{u} φ X) ≪≫
            rowComplexIsoMapTensorRight X K (coefficientSheaf.{u} φ X)).hom :=
  CochainComplex.KFlatBifunctor.totalComplexQhFlipIso_hom_app _ _ _ K

/-- **Derived extension of coefficients followed by restriction of coefficients is derived
tensoring with the constant sheaf `Λ̲₂`**: `res(E ⊗^L_{Λ₁} Λ₂) ≅ E ⊗^L_{Λ₁} Λ̲₂` naturally in
`E ∈ D(X_étale, Λ₁)`. -/
def etaleModuleDerivedExtendRestrictScalarsIso :
    etaleModuleDerivedExtendScalars.{u, r} φ X ⋙ etaleModuleDerivedRestrictScalars.{u, r} φ X ≅
      (etaleModuleDerivedTensor.{u, r} Λ₁ X).flip.obj
        (DerivedCategory.Q.obj (coefficientSheafComplex.{u, r} φ X)) := by
  let F := etaleModuleTensor.{u, r} Λ₁ X
  let G := coefficientSheafComplex.{u, r} φ X
  let e₀ : etaleModuleExtendScalarsHomotopy.{u, r} φ X ⋙
      etaleModuleDerivedRestrictScalars.{u, r} φ X ≅
      (homotopyBifunctor F).flip.obj ((HomotopyCategory.quotient _ _).obj G) ⋙
        DerivedCategory.Qh :=
    Quotient.natIsoLift _
      (etaleModuleExtendScalarsRestrictComplexIso φ X ≪≫
        (tensorCoefficientSheafComplexIso φ X).symm)
  have hc : ∀ K : (kFlatObjectsLeft F).FullSubcategory,
      IsIso ((Functor.whiskerLeft (kFlatObjectsLeft F).ι
        (etaleModuleDerivedExtendScalarsCounit.{u, r} φ X)).app K) := fun K =>
    isIso_etaleModuleDerivedExtendScalarsCounit_app φ X K.obj K.property
  have : IsIso (Functor.whiskerLeft (kFlatObjectsLeft F).ι
      (etaleModuleDerivedExtendScalarsCounit.{u, r} φ X)) := NatIso.isIso_of_isIso_app _
  let e₁ : kFlatQLeft F ⋙ etaleModuleDerivedExtendScalars.{u, r} φ X ⋙
      etaleModuleDerivedRestrictScalars.{u, r} φ X ≅
      (kFlatObjectsLeft F).ι ⋙ etaleModuleExtendScalarsHomotopy.{u, r} φ X ⋙
        etaleModuleDerivedRestrictScalars.{u, r} φ X :=
    Functor.associator _ _ _ ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (asIso (Functor.whiskerLeft (kFlatObjectsLeft F).ι
        (etaleModuleDerivedExtendScalarsCounit.{u, r} φ X))) _ ≪≫ Functor.associator _ _ _
  let e₂ : kFlatQLeft F ⋙ (etaleModuleDerivedTensor.{u, r} Λ₁ X).flip.obj
      (DerivedCategory.Q.obj G) ≅
      (kFlatObjectsLeft F).ι ⋙ (homotopyBifunctor F).flip.obj
        ((HomotopyCategory.quotient _ _).obj G) ⋙ DerivedCategory.Qh :=
    (derivedBifunctorLeftIso F).app (DerivedCategory.Q.obj G) ≪≫
      (derivedToDerivedLeftFac F).app G
  exact (Localization.fullyFaithfulWhiskeringLeft (kFlatQLeft F) (kFlatQuasiIsoLeft F)
    (DerivedCategory (EtaleModules.{u, r} Λ₁ X))).preimageIso
      (e₁ ≪≫ Functor.isoWhiskerLeft _ e₀ ≪≫ e₂.symm)

end Derived

end Stacks.EtaleCohomology

end
