module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticRoundTrip
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticPullbackQuasiCoherent

/-!
# Two derived pullbacks whose composite is a transition map

Let `F₁ : C' ⥤ C` and `F₂ : C ⥤ C'` be functors of categories with the chaotic topology, and
`φ₁ : g₁^*A → A'`, `φ₂ : g₂^*A' → A` maps of sheaves of differential graded algebras along the
induced morphisms of chaotic sites, such that over every object `U` of `C` the composite
`A(F₁ F₂ U) ⟶ A'(F₂ U) ⟶ A(U)` of the homomorphisms of section algebras is the restriction
homomorphism along a natural `η_U : F₁ F₂ U ⟶ U` of `Cᵒᵖ`. The canonical maps
`roundTripCounit : g₂^* g₁^* M ⟶ M` induce a natural transformation `Lg₂^* ∘ Lg₁^* ⟶ 𝟭` of
`D(A, d)`, and it is an isomorphism at every object of `QC(A, d)`: on a module `P` with
K-projective sections representing the object, the two derived pullbacks are computed by the
pullbacks, the pullback of `P` has K-projective sections again, and over `U` the canonical map is
the comparison map of quasi-coherence along `η_U`.

If the same holds the other way around, the two derived pullbacks restrict to mutually
quasi-inverse equivalences `QC(A, d) ≌ QC(A', d)`. This is the content of the proof of
Lemma 24.35.1 (Tag 0GZH), for representatives of two mutually inverse morphisms of pro-objects
whose composites are transition maps.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.roundTripHomotopyCounit`: the canonical map of the
  round trip on the homotopy category.
* `SheafOfModules.DifferentialGradedModule.roundTripDerivedCounit`: **the natural transformation
  `Lg₂^* ∘ Lg₁^* ⟶ 𝟭`** of `D(A, d)`.
* `SheafOfModules.DifferentialGradedModule.chaoticQCEquivalence`: **the equivalence
  `QC(A, d) ≌ QC(A', d)`** whose functor is the derived pullback `Lg₁^*`.

## Main results

* `SheafOfModules.DifferentialGradedModule.isIso_roundTripDerivedCounit_app`: the natural
  transformation is invertible at every object of `QC(A, d)`.

## References

* [Stacks Project, Lemma 24.35.1 (Tag 0GZH)](https://stacks.math.columbia.edu/tag/0GZH)
* [Stacks Project, Lemma 24.33.4 (Tag 0GZC)](https://stacks.math.columbia.edu/tag/0GZC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf

universe m u

namespace SheafOfModules.DifferentialGradedModule

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra
  Stacks.SheafOfModules.botWEqualsLocallyBijective

variable {C : Type u} [Category.{u} C] {C' : Type u} [Category.{u} C']
  [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
  {Osharp' : Sheaf (⊥ : GrothendieckTopology C') CommRingCat.{u}}
  {F₁ : C' ⥤ C} {F₂ : C ⥤ C'}
  {σ₁ : F₁.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj ⟶
    (Stacks.SheafOfModules.Tensor.ringSheaf Osharp').obj}
  {σ₂ : F₂.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf Osharp').obj ⟶
    (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj}
  {A : DifferentialGradedAlgebra.{u, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
  {A' : DifferentialGradedAlgebra.{u, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp')}
  (φ₁ : DifferentialGradedAlgebra.InverseImageHom F₁ σ₁ A A')
  (φ₂ : DifferentialGradedAlgebra.InverseImageHom F₂ σ₂ A' A)
  (η : F₂.op ⋙ F₁.op ⟶ 𝟭 Cᵒᵖ)
  (hη : ∀ (U : Cᵒᵖ) (b : (A.sectionAlgebra (F₁.op.obj (F₂.op.obj U))).A),
    (φ₂.sectionHom U).toAlgebraHom ((φ₁.sectionHom (F₂.op.obj U)).toAlgebraHom b) =
      (A.sectionRestriction (η.app U)).toAlgebraHom b)

/-- **The canonical map of the round trip on the homotopy category** `K(A)`. -/
def roundTripHomotopyCounit :
    pullbackHomotopyFunctor φ₁ ⋙ pullbackHomotopyFunctor φ₂ ⟶
      𝟭 (HomotopyCategory.{u, m, m} A) :=
  CategoryTheory.Quotient.natTransLift _
    { app := fun M => (HomotopyCategory.quotient A).map ((roundTripCounit φ₁ φ₂ η hη).app M)
      naturality := fun M N f => by
        show (HomotopyCategory.quotient A).map
            ((pullbackFunctor φ₂).map ((pullbackFunctor φ₁).map f)) ≫
            (HomotopyCategory.quotient A).map ((roundTripCounit φ₁ φ₂ η hη).app N) =
          (HomotopyCategory.quotient A).map ((roundTripCounit φ₁ φ₂ η hη).app M) ≫
            (HomotopyCategory.quotient A).map f
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg (HomotopyCategory.quotient A).map
          ((roundTripCounit φ₁ φ₂ η hη).naturality f) }

/-- The component of `roundTripHomotopyCounit` at the class of `M` is the class of the canonical
map `(roundTripCounit φ₁ φ₂ η hη).app M`. -/
theorem roundTripHomotopyCounit_app (M : DifferentialGradedModule.{u, m, m} A) :
    (roundTripHomotopyCounit φ₁ φ₂ η hη).app ((HomotopyCategory.quotient A).obj M) =
      (HomotopyCategory.quotient A).map ((roundTripCounit φ₁ φ₂ η hη).app M) :=
  rfl

variable [HasWeakSheafify (⊥ : GrothendieckTopology C) (Type m)]
  [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  [HasWeakSheafify (⊥ : GrothendieckTopology C') (Type m)]
  [HasSheafify (⊥ : GrothendieckTopology C') AddCommGrpCat.{m}]

/-- The canonical map of the round trip of derived pullbacks, read on `K(A)`: the counit of
`Lg₁^*`, then the counit of `Lg₂^*` at the pullback, then the class of the canonical map of the
round trip of pullbacks. -/
def roundTripLocalizedCounit :
    toDerivedCategory.{u, m, m} A ⋙ (chaoticDerivedPullback φ₁ ⋙ chaoticDerivedPullback φ₂) ⟶
      toDerivedCategory.{u, m, m} A ⋙ 𝟭 (derivedCategory.{u, m, m} A) :=
  Functor.whiskerRight (chaoticDerivedPullbackCounit φ₁) (chaoticDerivedPullback φ₂) ≫
    Functor.whiskerLeft (pullbackHomotopyFunctor φ₁) (chaoticDerivedPullbackCounit φ₂) ≫
      Functor.whiskerRight (roundTripHomotopyCounit φ₁ φ₂ η hη) (toDerivedCategory.{u, m, m} A)

/-- **The natural transformation `Lg₂^* ∘ Lg₁^* ⟶ 𝟭` of `D(A, d)`** induced by the canonical maps
of the round trip. -/
def roundTripDerivedCounit :
    chaoticDerivedPullback φ₁ ⋙ chaoticDerivedPullback φ₂ ⟶ 𝟭 (derivedCategory.{u, m, m} A) :=
  (Localization.whiskeringLeftFunctor' (toDerivedCategory.{u, m, m} A)
    (quasiIsomorphisms.{u, m, m} A) (derivedCategory.{u, m, m} A)).preimage
      (roundTripLocalizedCounit φ₁ φ₂ η hη)

/-- The component of `roundTripDerivedCounit` at the image of `X` in `D(A, d)` is the component
of `roundTripLocalizedCounit` at `X`. -/
theorem roundTripDerivedCounit_app (X : HomotopyCategory.{u, m, m} A) :
    (roundTripDerivedCounit φ₁ φ₂ η hη).app ((toDerivedCategory.{u, m, m} A).obj X) =
      (roundTripLocalizedCounit φ₁ φ₂ η hη).app X :=
  NatTrans.congr_app ((Localization.whiskeringLeftFunctor' (toDerivedCategory.{u, m, m} A)
    (quasiIsomorphisms.{u, m, m} A) (derivedCategory.{u, m, m} A)).map_preimage
      (roundTripLocalizedCounit φ₁ φ₂ η hη)) X

/-- **The natural transformation `Lg₂^* ∘ Lg₁^* ⟶ 𝟭` is invertible on `QC(A, d)`.** -/
theorem isIso_roundTripDerivedCounit_app (K : derivedCategory.{u, m, m} A) (hK : Chaotic.QC A K) :
    IsIso ((roundTripDerivedCounit φ₁ φ₂ η hη).app K) := by
  obtain ⟨M, rfl⟩ := exists_toDerivedCategory_obj_eq A K
  obtain ⟨P, f, hf, -, -, hs⟩ := exists_flat_quasiIso_sectionwise (A := A) M
  have hQ {X Y : DifferentialGradedModule.{u, m, m} A} (g : X ⟶ Y)
      (hg : QuasiIso g.toHomologicalComplex) :
      IsIso ((toDerivedCategory.{u, m, m} A).map ((HomotopyCategory.quotient A).map g)) :=
    (quasiIsomorphisms.{u, m, m} A).Q_inverts _ ((quasiIsomorphisms_quotient_map_iff g).2 hg)
  have := hQ f hf
  let e := asIso ((toDerivedCategory.{u, m, m} A).map ((HomotopyCategory.quotient A).map f))
  rw [← NatTrans.isIso_app_iff_of_iso _ e]
  have hP : IsQC (sectionDatum A)
      ((toDerivedCategory.{u, m, m} A).obj ((HomotopyCategory.quotient A).obj P)) :=
    isQC_of_iso _ e.symm ((qc_iff_isQC_sectionDatum A _).1 hK)
  have hQC := (isQC_sectionDatum_iff P).1 hP
  have hε : QuasiIso ((roundTripCounit φ₁ φ₂ η hη).app P).toHomologicalComplex := by
    refine quasiIso_of_forall_quasiIso_sectionMap _ fun U => ?_
    rw [sectionMap_roundTripCounit]
    have : QuasiIso ((_root_.DifferentialGradedModule.forgetToCochainComplex
        (A.sectionAlgebra U)).map ((roundTripSystemHom φ₁ φ₂ η hη P).app U)) :=
      quasiIso_roundTripSections φ₁ φ₂ η hη P U (hs _) hQC
    have h : QuasiIso ((_root_.DifferentialGradedModule.forgetToCochainComplex
        (A.sectionAlgebra U)).map
          ((pullbackSystem φ₂ ((pullbackFunctor φ₁).obj P)).sectionsIso U).hom ≫
        (_root_.DifferentialGradedModule.forgetToCochainComplex (A.sectionAlgebra U)).map
          ((roundTripSystemHom φ₁ φ₂ η hη P).app U)) := inferInstance
    rw [← Functor.map_comp] at h
    exact h
  have := isIso_chaoticDerivedPullbackCounit_app φ₁ hs
  have : IsIso ((chaoticDerivedPullbackCounit φ₂).app
      ((pullbackHomotopyFunctor φ₁).obj ((HomotopyCategory.quotient A).obj P))) :=
    isIso_chaoticDerivedPullbackCounit_app φ₂
      (fun U' => leftOrthogonal_sectionModule_pullbackFunctor φ₁ P U' (hs _))
  rw [roundTripDerivedCounit_app]
  dsimp only [roundTripLocalizedCounit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  rw [roundTripHomotopyCounit_app]
  refine IsIso.comp_isIso' ?_ (IsIso.comp_isIso' ?_ ?_)
  · infer_instance
  · infer_instance
  · exact hQ _ hε

/-! ### The equivalence of quasi-coherent objects -/

omit [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The derived pullback on quasi-coherent objects** `QC(A, d) ⥤ QC(A', d)`: by Tag 0GZC the
derived pullback `Lg₁^*` maps `QC(A, d)` into `QC(A', d)`. -/
def chaoticQCPullback : Chaotic.QCFullSubcategory A ⥤ Chaotic.QCFullSubcategory A' :=
  ObjectProperty.lift _ (Chaotic.QCι A ⋙ chaoticDerivedPullback φ₁)
    fun K => qc_chaoticDerivedPullback φ₁ K.obj K.property

omit [HasWeakSheafify (⊥ : GrothendieckTopology C') (Type m)] in
/-- The underlying object of `D(A', d)` of `(chaoticQCPullback φ₁).obj K` is the derived pullback
of `K`. -/
@[simp] theorem chaoticQCPullback_obj_obj (K : Chaotic.QCFullSubcategory A) :
    ((chaoticQCPullback φ₁).obj K).obj = (chaoticDerivedPullback φ₁).obj K.obj :=
  rfl

omit [HasWeakSheafify (⊥ : GrothendieckTopology C') (Type m)] in
/-- The underlying morphism of `(chaoticQCPullback φ₁).map f` is the derived pullback of `f`. -/
@[simp] theorem chaoticQCPullback_map_hom {K L : Chaotic.QCFullSubcategory A} (f : K ⟶ L) :
    ((chaoticQCPullback φ₁).map f).hom = (chaoticDerivedPullback φ₁).map f.hom :=
  rfl

/-- **The round trip of the derived pullbacks on quasi-coherent objects is the identity**: the
canonical map of the round trip is invertible on `QC(A, d)`. -/
def chaoticQCRoundTripIso (η : F₂.op ⋙ F₁.op ⟶ 𝟭 Cᵒᵖ)
    (hη : ∀ (U : Cᵒᵖ) (b : (A.sectionAlgebra (F₁.op.obj (F₂.op.obj U))).A),
      (φ₂.sectionHom U).toAlgebraHom ((φ₁.sectionHom (F₂.op.obj U)).toAlgebraHom b) =
        (A.sectionRestriction (η.app U)).toAlgebraHom b) :
    chaoticQCPullback φ₁ ⋙ chaoticQCPullback φ₂ ≅ 𝟭 (Chaotic.QCFullSubcategory A) :=
  NatIso.ofComponents
    (fun K =>
      ObjectProperty.isoMk _
        (@asIso _ _ _ _ _ (isIso_roundTripDerivedCounit_app φ₁ φ₂ η hη K.obj K.property)))
    (fun f => ObjectProperty.hom_ext _ ((roundTripDerivedCounit φ₁ φ₂ η hη).naturality f.hom))

/-- **Two derived pullbacks whose two composites are transition maps are mutually quasi-inverse
equivalences of the quasi-coherent objects** `QC(A, d) ≌ QC(A', d)`. The hypotheses are that the
composites `A(F₁ F₂ U) ⟶ A'(F₂ U) ⟶ A(U)` and `A'(F₂ F₁ U') ⟶ A(F₁ U') ⟶ A'(U')` of the
homomorphisms of section algebras are restriction homomorphisms along natural transformations
`η₁ : F₂.op ⋙ F₁.op ⟶ 𝟭` and `η₂ : F₁.op ⋙ F₂.op ⟶ 𝟭`. -/
def chaoticQCEquivalence (η₁ : F₂.op ⋙ F₁.op ⟶ 𝟭 Cᵒᵖ)
    (hη₁ : ∀ (U : Cᵒᵖ) (b : (A.sectionAlgebra (F₁.op.obj (F₂.op.obj U))).A),
      (φ₂.sectionHom U).toAlgebraHom ((φ₁.sectionHom (F₂.op.obj U)).toAlgebraHom b) =
        (A.sectionRestriction (η₁.app U)).toAlgebraHom b)
    (η₂ : F₁.op ⋙ F₂.op ⟶ 𝟭 C'ᵒᵖ)
    (hη₂ : ∀ (U' : C'ᵒᵖ) (b : (A'.sectionAlgebra (F₂.op.obj (F₁.op.obj U'))).A),
      (φ₁.sectionHom U').toAlgebraHom ((φ₂.sectionHom (F₁.op.obj U')).toAlgebraHom b) =
        (A'.sectionRestriction (η₂.app U')).toAlgebraHom b) :
    Chaotic.QCFullSubcategory A ≌ Chaotic.QCFullSubcategory A' :=
  CategoryTheory.Equivalence.mk (chaoticQCPullback φ₁) (chaoticQCPullback φ₂)
    (chaoticQCRoundTripIso φ₁ φ₂ η₁ hη₁).symm (chaoticQCRoundTripIso φ₂ φ₁ η₂ hη₂)

/-- The functor of `chaoticQCEquivalence` is `chaoticQCPullback φ₁`. -/
@[simp] theorem chaoticQCEquivalence_functor (η₁ : F₂.op ⋙ F₁.op ⟶ 𝟭 Cᵒᵖ)
    (hη₁ : ∀ (U : Cᵒᵖ) (b : (A.sectionAlgebra (F₁.op.obj (F₂.op.obj U))).A),
      (φ₂.sectionHom U).toAlgebraHom ((φ₁.sectionHom (F₂.op.obj U)).toAlgebraHom b) =
        (A.sectionRestriction (η₁.app U)).toAlgebraHom b)
    (η₂ : F₁.op ⋙ F₂.op ⟶ 𝟭 C'ᵒᵖ)
    (hη₂ : ∀ (U' : C'ᵒᵖ) (b : (A'.sectionAlgebra (F₂.op.obj (F₁.op.obj U'))).A),
      (φ₁.sectionHom U').toAlgebraHom ((φ₂.sectionHom (F₁.op.obj U')).toAlgebraHom b) =
        (A'.sectionRestriction (η₂.app U')).toAlgebraHom b) :
    (chaoticQCEquivalence φ₁ φ₂ η₁ hη₁ η₂ hη₂).functor = chaoticQCPullback φ₁ :=
  rfl

end SheafOfModules.DifferentialGradedModule
