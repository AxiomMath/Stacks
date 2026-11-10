module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticPullbackTriangulated
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticRoundTripDerived
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeAdmissible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeDistinguished
public import StacksFrontier.CategoryTheory.Functor.Derived.LeftDerivedCounitCommShift
public import StacksFrontier.Algebra.DifferentialGraded.Module.ExhaustiveCellFiltration
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedTriangulated

/-!
# The derived pullback along a functor of chaotic sites is an exact functor

Let `F : C' ⥤ C` be a functor of categories with the chaotic topology and `φ : g^*A → A'` a map
of sheaves of differential graded algebras along the morphism of chaotic ringed sites it
induces. The derived pullback `Lg^* : D(A, d) ⥤ D(A', d)` of Tag 0GZC is the total left derived
functor of the pullback `K(A) ⥤ K(A')` followed by the localization functor. The pullback on the
homotopy categories is an exact functor of triangulated categories, so its left derived functor
commutes with the translations; it is computed on the modules whose sections are K-projective,
and that class contains the cone of any homomorphism between two of its members — the sections
of the cone sit in an admissible short exact sequence between the sections of the target and the
shifted sections of the source — so `Lg^*` is triangulated. It follows that its restriction
`QC(A, d) ⥤ QC(A', d)` is triangulated as well.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.coneTriangle`: the triangle `K ⟶ L ⟶ C(f) ⟶ K[1]` of
  a homomorphism in the homotopy category, which is distinguished.

## Main results

* `SheafOfModules.DifferentialGradedModule.sectionGood_cone`: the cone of a homomorphism between
  modules whose sections are K-projective has K-projective sections.
* `SheafOfModules.DifferentialGradedModule.chaoticDerivedPullback_commShift` and
  `chaoticDerivedPullback_isTriangulated`: **the derived pullback commutes with the translations
  and is an exact functor of triangulated categories.**
* `SheafOfModules.DifferentialGradedModule.chaoticQCPullback_commShift` and
  `chaoticQCPullback_isTriangulated`: so is the derived pullback on quasi-coherent objects.

## References

* [Stacks Project, Lemma 24.33.4 (Tag 0GZC)](https://stacks.math.columbia.edu/tag/0GZC)
* [Stacks Project, Lemma 24.30.1 (Tag 0FTF)](https://stacks.math.columbia.edu/tag/0FTF)
* [Stacks Project, Tag 0FQF](https://stacks.math.columbia.edu/tag/0FQF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf CategoryTheory.Pretriangulated

universe m u

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

namespace SheafOfModules.DifferentialGradedModule

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra
  Stacks.SheafOfModules.botWEqualsLocallyBijective

/-! ### Cones of modules with K-projective sections -/

section Cone

variable {C : Type u} [Category.{u} C]
  [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
  {A : DifferentialGradedAlgebra.{u, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The cone of a homomorphism between modules whose sections are K-projective has
K-projective sections**: over every object its sections are the middle term of the admissible
short exact sequence `0 → L(U) → C(f)(U) → K(U)[1] → 0`. -/
theorem sectionGood_cone {K L : DifferentialGradedModule.{u, m, m} A} (f : K ⟶ L)
    (hK : ∀ U : Cᵒᵖ,
      (_root_.DifferentialGradedModule.acyclic' (A.sectionAlgebra U)).leftOrthogonal
        ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).obj
          (K.sectionModule U)))
    (hL : ∀ U : Cᵒᵖ,
      (_root_.DifferentialGradedModule.acyclic' (A.sectionAlgebra U)).leftOrthogonal
        ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).obj
          (L.sectionModule U)))
    (U : Cᵒᵖ) :
    (_root_.DifferentialGradedModule.acyclic' (A.sectionAlgebra U)).leftOrthogonal
      ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).obj
        ((conePackage f).cone.sectionModule U)) := by
  have hsh : (_root_.DifferentialGradedModule.acyclic' (A.sectionAlgebra U)).leftOrthogonal
      ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).obj
        ((shift K).sectionModule U)) := by
    obtain ⟨e⟩ := nonempty_sectionModule_shifted_iso K (shiftPackage K) U
    exact _root_.DifferentialGradedModule.leftOrthogonal_acyclic_of_iso _ e.symm
      (_root_.DifferentialGradedModule.leftOrthogonal_acyclic_shift 1 (hK U))
  exact _root_.DifferentialGradedModule.leftOrthogonal_acyclic_of_isAdmissibleShortExact _
    (sectionMap (conePackage f).inclusion U) (sectionMap (conePackage f).projection U)
    ((isAdmissibleShortExact_conePackage f).sectionMap U) (hL U) hsh

/-- The degree-one translation of `K(Mod(A, d))` is the shift of differential graded modules
(Tag 0FS7), for `A` over `Stacks.SheafOfModules.Tensor.ringSheaf O`. -/
theorem toRingCat_shiftFunctor_obj (M : DifferentialGradedModule.{u, m, m} A) :
    (shiftFunctor (HomotopyCategory.{u, m, m} A) (1 : ℤ)).obj
        ((HomotopyCategory.quotient A).obj M) =
      (HomotopyCategory.quotient A).obj (shift M) :=
  HomotopyCategory.shiftFunctor_obj (X := ⟨C, ⊥, Osharp⟩) A M

/-- The triangle of the cone sequence is distinguished (Tag 09QU), for `A` over
`Stacks.SheafOfModules.Tensor.ringSheaf O`. -/
theorem toRingCat_coneRotatedTriangle_distinguished {K L : DifferentialGradedModule.{u, m, m} A}
    (f : K ⟶ L) :
    coneRotatedTriangle (X := ⟨C, ⊥, Osharp⟩) f ∈ distTriang (HomotopyCategory.{u, m, m} A) :=
  coneRotatedTriangle_distinguished (X := ⟨C, ⊥, Osharp⟩) f

/-- **The triangle `K ⟶ L ⟶ C(f) ⟶ K[1]` of a homomorphism**, in the homotopy category: its
rotation is the triangle of the cone sequence, up to the sign of the identification of the
third vertex. -/
def coneTriangle {K L : DifferentialGradedModule.{u, m, m} A} (f : K ⟶ L) :
    Triangle (HomotopyCategory.{u, m, m} A) :=
  Triangle.mk ((HomotopyCategory.quotient A).map f)
    ((HomotopyCategory.quotient A).map (conePackage f).inclusion)
    (-((HomotopyCategory.quotient A).map (conePackage f).projection ≫
      eqToHom (toRingCat_shiftFunctor_obj K).symm))

/-- **The triangle of a homomorphism and its cone is distinguished.** -/
theorem coneTriangle_distinguished {K L : DifferentialGradedModule.{u, m, m} A} (f : K ⟶ L) :
    coneTriangle f ∈ distTriang (HomotopyCategory.{u, m, m} A) := by
  rw [rotate_distinguished_triangle]
  let E : ((HomotopyCategory.quotient A).obj K)⟦(1 : ℤ)⟧ ≅
      (HomotopyCategory.quotient A).obj (shift K) :=
    eqToIso (toRingCat_shiftFunctor_obj K)
  let E' : ((HomotopyCategory.quotient A).obj K)⟦(1 : ℤ)⟧ ≅
      (HomotopyCategory.quotient A).obj (shift K) :=
    { hom := -E.hom
      inv := -E.inv
      hom_inv_id := by simp
      inv_hom_id := by simp }
  refine isomorphic_distinguished _
    (toRingCat_coneRotatedTriangle_distinguished f) _ ?_
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) E' ?_ ?_ ?_
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · dsimp [Triangle.rotate, coneTriangle, coneRotatedTriangle, E', E]
    refine (Preadditive.neg_comp_neg _ _).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) (eqToHom_trans _ _)).trans ?_
    exact (congrArg (_ ≫ ·) (eqToHom_refl _ _)).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  · dsimp [Triangle.rotate, coneTriangle, coneRotatedTriangle, E', E]
    refine ((congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans
      (Category.comp_id _)).trans ?_
    refine Eq.trans ?_ (Preadditive.neg_comp _ _).symm
    refine congrArg Neg.neg ?_
    exact (((Category.id_comp _).symm.trans (congrArg (· ≫ _) (eqToHom_refl _ _).symm)).trans
      (congrArg (· ≫ _) (eqToHom_trans _ _).symm)).trans (Category.assoc _ _ _)

end Cone

/-! ### The derived pullback -/

variable {C : Type u} [Category.{u} C] {C' : Type u} [Category.{u} C']
  [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
  {Osharp' : Sheaf (⊥ : GrothendieckTopology C') CommRingCat.{u}}
  {F : C' ⥤ C}
  {σ : F.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj ⟶
    (Stacks.SheafOfModules.Tensor.ringSheaf Osharp').obj}
  {A : DifferentialGradedAlgebra.{u, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
  {A' : DifferentialGradedAlgebra.{u, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp')}
  (φ : DifferentialGradedAlgebra.InverseImageHom F σ A A')
  [HasWeakSheafify (⊥ : GrothendieckTopology C) (Type m)]
  [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  [HasSheafify (⊥ : GrothendieckTopology C') AddCommGrpCat.{m}]

/-- **The derived pullback commutes with the translations**: it is the total left derived functor
of a functor which does. -/
@[instance_reducible]
instance chaoticDerivedPullback_commShift : (chaoticDerivedPullback φ).CommShift ℤ :=
  StacksDraft.PseudoCoherence.leftDerivedCommShift (chaoticDerivedPullback φ)
    (chaoticDerivedPullbackCounit φ) (quasiIsomorphisms.{u, m, m} A) ℤ

/-- The counit of the derived pullback commutes with the translations. -/
instance chaoticDerivedPullbackCounit_commShift :
    NatTrans.CommShift (chaoticDerivedPullbackCounit φ) ℤ :=
  Functor.IsLeftDerivedFunctor.natTrans_commShift (chaoticDerivedPullback φ)
    (chaoticDerivedPullbackCounit φ) (quasiIsomorphisms.{u, m, m} A) ℤ

/-- **The derived pullback is an exact functor of triangulated categories.** Every morphism of
`D(A, d)` is, up to isomorphism, the class of a homomorphism `f` between modules whose sections
are K-projective; the counit of the derived pullback is invertible at its source, its target and
its cone, and the triangle of `f` and its cone is distinguished. -/
instance chaoticDerivedPullback_isTriangulated : (chaoticDerivedPullback φ).IsTriangulated := by
  let W := quasiIsomorphisms.{u, m, m} A
  let P := sectionGoodProperty A
  have : (LeftDerivedByResolutions.inclusionLocalizerMorphism W P).HasLeftResolutions :=
    fun M => by
      obtain ⟨K, hK, s, hs⟩ := exists_sectionGoodProperty A M
      exact ⟨{ X₁ := ⟨K, hK⟩, w := s, hw := hs }⟩
  have := LeftDerivedByResolutions.isLocalizedEquivalence_inclusionLocalizerMorphism W P
  have := LeftDerivedByResolutions.hasRightCalculusOfFractions_inverseImage_ι W P
  have : (P.ι ⋙ toDerivedCategory.{u, m, m} A).IsLocalization (W.inverseImage P.ι) :=
    LocalizerMorphism.IsLocalizedEquivalence.isLocalization
      (LeftDerivedByResolutions.inclusionLocalizerMorphism W P) (toDerivedCategory.{u, m, m} A)
  have := Localization.essSurj_mapArrow_of_hasRightCalculusOfFractions
    (P.ι ⋙ toDerivedCategory.{u, m, m} A) (W.inverseImage P.ι)
  refine Functor.isTriangulated_of_rightExtension (chaoticDerivedPullback φ)
    (chaoticDerivedPullbackCounit φ) (fun X Y g => ?_)
  obtain ⟨a, ⟨ea⟩⟩ := Functor.EssSurj.mem_essImage
    (F := (P.ι ⋙ toDerivedCategory.{u, m, m} A).mapArrow) (Arrow.mk g)
  obtain ⟨f₀, hf₀⟩ := (HomotopyCategory.quotient A).map_surjective (P.ι.map a.hom)
  refine ⟨coneTriangle f₀, coneTriangle_distinguished f₀,
    isIso_chaoticDerivedPullbackCounit_app φ a.left.property,
    isIso_chaoticDerivedPullbackCounit_app φ a.right.property,
    isIso_chaoticDerivedPullbackCounit_app φ
      (sectionGood_cone f₀ a.left.property a.right.property), ⟨?_⟩⟩
  exact eqToIso (congrArg (fun m => Arrow.mk ((toDerivedCategory.{u, m, m} A).map m)) hf₀) ≪≫ ea

/-! ### The derived pullback on quasi-coherent objects -/

/-- **The derived pullback on quasi-coherent objects commutes with the translations.** -/
@[instance_reducible]
instance chaoticQCPullback_commShift : (chaoticQCPullback φ).CommShift ℤ :=
  Functor.CommShift.ofComp ((Chaotic.QC A').liftCompιIso _ _) ℤ

/-- **The derived pullback on quasi-coherent objects is triangulated.** -/
instance chaoticQCPullback_isTriangulated : (chaoticQCPullback φ).IsTriangulated :=
  haveI : NatTrans.CommShift (F₁ := chaoticQCPullback φ ⋙ Chaotic.QCι A')
      ((Chaotic.QC A').liftCompιIso (Chaotic.QCι A ⋙ chaoticDerivedPullback φ)
        fun K => qc_chaoticDerivedPullback φ K.obj K.property).hom ℤ :=
    Functor.CommShift.ofComp_compatibility _ _
  (Functor.isTriangulated_iff_comp_right (F := chaoticQCPullback φ)
    ((Chaotic.QC A').liftCompιIso _ _)).2 inferInstance

end SheafOfModules.DifferentialGradedModule
