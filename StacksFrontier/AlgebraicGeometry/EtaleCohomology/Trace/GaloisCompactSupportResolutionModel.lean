module

public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicResolutionHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisEquivariantDerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisCompactSupportAction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportExt
public import StacksFrontier.Algebra.Homology.Resolution.Defs.InjectiveResolution

/-!
# `H^m_c(X_k̄, F)` from an injective resolution of `j_! F` on the compactification

Let `k` be a field, `k̄/k` separable algebraic, `f : X ⟶ Spec k` with a compactification
`j : X ⟶ X̄` over `k`, and `F` a sheaf of `Λ`-modules on `X_étale`. For an injective resolution
`j_! F ⟶ I` on `X̄_étale`, the restriction `I|_{X̄_k̄}` is a resolution of `(j_! F)|_{X̄_k̄}` by
`Γ(X̄_k̄, -)`-acyclic sheaves
(`Stacks.EtaleCohomology.rightAcyclic_etaleModuleGlobalSections_fieldBaseChange`), so the
cohomology of the complex of sections `Γ(X̄_k̄, I|_{X̄_k̄})` is `H^m_c(X_k̄, F)` in the model
`RΓ(X̄_k̄, (j_! F)|_{X̄_k̄})` of Remark 03UI (2)
(`Stacks.EtaleCohomology.galoisCompactSupportResolutionIso`), naturally for morphisms of
resolutions over morphisms of sheaves
(`Stacks.EtaleCohomology.galoisCompactSupportResolutionIso_hom_naturality`).

Forgetting the Galois action, `Γ(X̄_k̄, I|_{X̄_k̄})` is `Γ^Gal(I)`
(`Stacks.EtaleCohomology.galoisGlobalSections_comp_underlying`, by definition): this is the
chain model of `RΓ_c^Gal(X_k̄, F)` on which the Poincaré pairing of Tag 03VM is built.

## References

* [Stacks Project, Tag 03UI](https://stacks.math.columbia.edu/tag/03UI), item (2).
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Frobenius

universe u

namespace CochainComplex.InjectiveResolution

variable {C : Type*} [Category* C] [Abelian C] {K : CochainComplex C ℤ}

/-- The resolving complex of an injective resolution, as a bounded below complex. -/
def cocomplexPlus (I : CochainComplex.InjectiveResolution K) : CochainComplex.Plus C :=
  ⟨I.cocomplex, I.boundedBelow⟩

end CochainComplex.InjectiveResolution

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

/-- Enough injectives for sheaves of `Λ`-modules on the small étale site, pinned at the object
universe. -/
local instance (priority := 3000) etaleModules_enoughInjectives_resolutionModel (Λ : Type)
    [Ring Λ] (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra.IsSeparable k kbar]

/-- Restriction to `X̄_k̄` preserves homology. -/
instance preservesHomology_etaleModuleInverseImage_fieldBaseChangeProj :
    (etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj (Over.mk j.toBase) kbar)).PreservesHomology := by
  have h := (Functor.exact_tfae
    (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar))).out 4 3
  exact h.mp ⟨inferInstance, inferInstance⟩

variable {Λ f j kbar}

/-- The comparison `(j_! F[0])|_{X̄_k̄} ⟶ I|_{X̄_k̄}` induced by an injective resolution of
`j_! F`. -/
def compactSupportResolutionRestrictionMap (F : EtaleModules.{u, 0} Λ X)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))) :
    (etaleModuleInverseImage.{u, 0} Λ
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F)) ⟶
      (etaleModuleInverseImage.{u, 0} Λ
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj I.cocomplexPlus :=
  (etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.map
    ((mapCochainComplexPlusSinglePlusIso (etaleModuleExtensionByZero.{u, 0} Λ j.immersion) F).hom ≫
      ObjectProperty.homMk I.ι)

/-- The comparison `(j_! F[0])|_{X̄_k̄} ⟶ I|_{X̄_k̄}` is an isomorphism in the bounded below
derived category. -/
instance isIso_Q_map_compactSupportResolutionRestrictionMap (F : EtaleModules.{u, 0} Λ X)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))) :
    IsIso (DerivedCategory.Plus.Q.map
      (compactSupportResolutionRestrictionMap (kbar := kbar) F I)) := by
  have : QuasiIso (compactSupportResolutionRestrictionMap (kbar := kbar) F I).hom := by
    change QuasiIso (((etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).map
        ((HomologicalComplex.singleMapHomologicalComplex (etaleModuleExtensionByZero.{u, 0} Λ
          j.immersion) (ComplexShape.up ℤ) 0).hom.app F ≫ I.ι))
    infer_instance
  have : IsIso (DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.Q.map (compactSupportResolutionRestrictionMap (kbar := kbar) F I))) :=
    inferInstanceAs (IsIso (DerivedCategory.Q.map (compactSupportResolutionRestrictionMap
      (kbar := kbar) F I).hom))
  exact isIso_of_fully_faithful DerivedCategory.Plus.ι _

/-- The terms of `I|_{X̄_k̄}` are `Γ(X̄_k̄, -)`-acyclic. -/
theorem rightAcyclic_compactSupportResolutionRestriction (F : EtaleModules.{u, 0} Λ X)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))) (n : ℤ) :
    (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk j.toBase) kbar)).rightAcyclic
      (((etaleModuleInverseImage.{u, 0} Λ
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
          I.cocomplexPlus).obj.X n) :=
  rightAcyclic_etaleModuleGlobalSections_fieldBaseChange Λ (Over.mk j.toBase) kbar
    (I.cocomplex.X n)

variable (kbar) in
/-- **`Hᵐ(Γ(X̄_k̄, I|_{X̄_k̄})) ≅ Hᵐ_c(X_k̄, F)`** for an injective resolution `I` of `j_! F` on
`X̄`, in the model `RΓ(X̄_k̄, (j_! F)|_{X̄_k̄})` of `galoisCompactSupportCohomologyGroup`. -/
def galoisCompactSupportResolutionIso (F : EtaleModules.{u, 0} Λ X)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))) (m : ℤ) :
    (((etaleModuleGlobalSections.{u, 0} Λ
      (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex
        _).obj (((etaleModuleInverseImage.{u, 0} Λ
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
            I.cocomplex)).homology m ≅
      galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) m :=
  (etaleModuleGlobalSections.{u, 0} Λ
      (fieldBaseChange (Over.mk j.toBase) kbar)).homologyIsoRightDerivedFunctorPlusOfRightAcyclic
      _ (rightAcyclic_compactSupportResolutionRestriction F I) m ≪≫
    (DerivedCategory.Plus.homologyFunctor _ m).mapIso
      ((etaleModuleGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk j.toBase) kbar)).rightDerivedFunctorPlus.mapIso
          (asIso (DerivedCategory.Plus.Q.map
            (compactSupportResolutionRestrictionMap (kbar := kbar) F I)))).symm

/-- The forward map of `galoisCompactSupportResolutionIso` is the comparison of the homology of
the acyclic complex `Γ(X̄_k̄, I|_{X̄_k̄})` with the right derived functor, followed by the inverse
of the comparison `(j_! F[0])|_{X̄_k̄} ⟶ I|_{X̄_k̄}`. -/
lemma galoisCompactSupportResolutionIso_hom (F : EtaleModules.{u, 0} Λ X)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))) (m : ℤ) :
    (galoisCompactSupportResolutionIso (f := f) kbar F I m).hom =
      ((etaleModuleGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk j.toBase) kbar)).homologyIsoRightDerivedFunctorPlusOfRightAcyclic
          _ (rightAcyclic_compactSupportResolutionRestriction F I) m).hom ≫
      (DerivedCategory.Plus.homologyFunctor _ m).map ((etaleModuleGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk j.toBase) kbar)).rightDerivedFunctorPlus.map
          (inv (DerivedCategory.Plus.Q.map
            (compactSupportResolutionRestrictionMap (kbar := kbar) F I)))) :=
  rfl

omit [Algebra.IsSeparable k kbar] in
/-- The comparison `(j_! F[0])|_{X̄_k̄} ⟶ I|_{X̄_k̄}` is natural for a morphism of resolutions
over a morphism of sheaves. -/
lemma compactSupportResolutionRestrictionMap_naturality {F F' : EtaleModules.{u, 0} Λ X}
    (v : F ⟶ F') (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)))
    (I' : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F')))
    (φ : I.cocomplex ⟶ I'.cocomplex)
    (hφ : I.ι ≫ φ = (CochainComplex.singleFunctor _ 0).map
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map v) ≫ I'.ι) :
    compactSupportResolutionRestrictionMap (kbar := kbar) F I ≫
        (etaleModuleInverseImage.{u, 0} Λ
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.map
            (ObjectProperty.homMk φ : I.cocomplexPlus ⟶ I'.cocomplexPlus) =
      (etaleModuleInverseImage.{u, 0} Λ
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.map
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.map
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map v)) ≫
        compactSupportResolutionRestrictionMap (kbar := kbar) F' I' := by
  unfold compactSupportResolutionRestrictionMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply ObjectProperty.hom_ext
  have hn := (HomologicalComplex.singleMapHomologicalComplex
    (etaleModuleExtensionByZero.{u, 0} Λ j.immersion) (ComplexShape.up ℤ) 0).hom.naturality v
  show ((HomologicalComplex.singleMapHomologicalComplex
      (etaleModuleExtensionByZero.{u, 0} Λ j.immersion) (ComplexShape.up ℤ) 0).hom.app F ≫
      I.ι) ≫ φ = ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapHomologicalComplex _).map
        ((CochainComplex.singleFunctor _ 0).map v) ≫
    (HomologicalComplex.singleMapHomologicalComplex
      (etaleModuleExtensionByZero.{u, 0} Λ j.immersion) (ComplexShape.up ℤ) 0).hom.app F' ≫ I'.ι
  rw [Category.assoc, hφ, ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ I'.ι) hn.symm

/-- **`Hᵐ(Γ(X̄_k̄, I|)) ≅ Hᵐ_c(X_k̄, F)` is natural** for a morphism of resolutions `φ : I ⟶ I'`
over a morphism of sheaves `v : F ⟶ F'`. -/
theorem galoisCompactSupportResolutionIso_hom_naturality {F F' : EtaleModules.{u, 0} Λ X}
    (v : F ⟶ F') (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)))
    (I' : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F')))
    (φ : I.cocomplex ⟶ I'.cocomplex)
    (hφ : I.ι ≫ φ = (CochainComplex.singleFunctor _ 0).map
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map v) ≫ I'.ι) (m : ℤ) :
    HomologicalComplex.homologyMap ((etaleModuleGlobalSections.{u, 0} Λ
      (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _ |>.map
        ((etaleModuleInverseImage.{u, 0} Λ
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _ |>.map φ)) m ≫
        (galoisCompactSupportResolutionIso (f := f) kbar F' I' m).hom =
      (galoisCompactSupportResolutionIso (f := f) kbar F I m).hom ≫
        (DerivedCategory.Plus.homologyFunctor _ m).map
          ((etaleModuleDerivedGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk j.toBase) kbar)).map
            (DerivedCategory.Plus.Q.map ((etaleModuleInverseImage.{u, 0} Λ
              (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.map
              ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.map
                ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map v))))) := by
  have hsq := congrArg DerivedCategory.Plus.Q.map
    (compactSupportResolutionRestrictionMap_naturality (kbar := kbar) v I I' φ hφ)
  simp only [Functor.map_comp] at hsq
  have hinv : DerivedCategory.Plus.Q.map ((etaleModuleInverseImage.{u, 0} Λ
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.map
        (ObjectProperty.homMk φ : I.cocomplexPlus ⟶ I'.cocomplexPlus)) ≫
      inv (DerivedCategory.Plus.Q.map
        (compactSupportResolutionRestrictionMap (kbar := kbar) F' I')) =
      inv (DerivedCategory.Plus.Q.map (compactSupportResolutionRestrictionMap (kbar := kbar) F I)) ≫
        DerivedCategory.Plus.Q.map ((etaleModuleInverseImage.{u, 0} Λ
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.map
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.map
              ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map v))) := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, hsq, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have hinv' := congrArg (fun x => (DerivedCategory.Plus.homologyFunctor _ m).map
    ((etaleModuleGlobalSections.{u, 0} Λ
      (fieldBaseChange (Over.mk j.toBase) kbar)).rightDerivedFunctorPlus.map x)) hinv
  simp only [Functor.map_comp] at hinv'
  have hac := (etaleModuleGlobalSections.{u, 0} Λ
    (fieldBaseChange (Over.mk j.toBase)
      kbar)).homologyIsoRightDerivedFunctorPlusOfRightAcyclic_hom_naturality
    ((etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.map
      (ObjectProperty.homMk φ : I.cocomplexPlus ⟶ I'.cocomplexPlus))
    (rightAcyclic_compactSupportResolutionRestriction F I)
    (rightAcyclic_compactSupportResolutionRestriction F' I') m
  rw [galoisCompactSupportResolutionIso_hom, galoisCompactSupportResolutionIso_hom]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hac).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hinv').trans (Category.assoc _ _ _).symm)))

end Stacks.EtaleCohomology

end
