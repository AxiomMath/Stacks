module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.TotalComplexShift
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.Injective.Basic
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.TestingFamily
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.CategoryTheory.Sites.CechNerveHomology
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Basic
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.CohomologyZeroCanonical
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.DerivedComparison
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.ObjectAcyclicity
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SectionsComplexFunctorial
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SectionsComplexOver
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible
public import StacksFrontier.CategoryTheory.Sites.Cohomology.WeaklyContractible.CohomologyOverAWeaklyContractibleObject

/-!
# Derived sections from a weakly contractible hypercovering

A bounded-below complex of abelian sheaves can be evaluated degreewise on a hypercovering.
The total complex of the resulting cosimplicial cochain complex computes derived sections when
every object appearing in the hypercovering is weakly contractible.

## Main definitions

* `hypercoverDoubleComplex` is the bicomplex obtained by applying the alternating hypercover
  cochain complex degreewise to a bounded-below complex of abelian sheaves.
* `hypercoverTotalComplex` is its total complex.

## Main results

* `derivedSectionsIsoHypercoverTotalComplex` identifies the image of the total complex in the
  unbounded derived category with derived sections.

## References

* [Stacks Project, Tag 09A2](https://stacks.math.columbia.edu/tag/09A2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite ComplexShape Simplicial

universe w v u

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  (J : Pretopology C) (U : C)
  (K : SimplicialObject (FormalCoproduct.{w} (Over U)))

/-- The hypercover cochain complex functor in nonnegative degrees preserves zero morphisms. -/
local instance hypercoverCochainNat_preservesZeroMorphisms :
    (hypercoverCochainNatFunctor J U K).PreservesZeroMorphisms :=
  ⟨by
    intro X Y
    apply HomologicalComplex.hom_ext
    intro n
    dsimp [hypercoverCochainNatFunctor, sectionsOnOverFunctor,
      FormalCoproduct.cochainComplexFunctor,
      FormalCoproduct.cosimplicialObjectFunctor,
      AlgebraicTopology.alternatingCofaceMapComplex,
      AlgebraicTopology.AlternatingCofaceMapComplex.map, FormalCoproduct.evalOp]
    apply Pi.hom_ext
    intro i
    rw [Pi.map_π]
    simp only [comp_zero]
    exact (zero_comp).symm⟩

/-- The hypercover cochain complex functor in integer degrees preserves zero morphisms. -/
local instance hypercoverCochainInt_preservesZeroMorphisms :
    (hypercoverCochainIntFunctor J U K).PreservesZeroMorphisms :=
  ⟨by
    intro X Y
    change (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max u v w}).map
      ((hypercoverCochainNatFunctor J U K).map 0) = 0
    rw [Functor.map_zero, Functor.map_zero]⟩

private lemma exact_sections_of_isWeaklyContractible
    [Small.{v} C] [HasSheafify J.toGrothendieck (Type v)]
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]
    (hU : J.toGrothendieck.IsWeaklyContractible U) :
    exactFunctor (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) AddCommGrpCat.{max u v w}
      (sheafSectionsFunctor J U) :=
  Stacks.WeaklyContractible.exact_sheafSections_of_isWeaklyContractible J.toGrothendieck U
    (Stacks.WeaklyContractible.surjective_sections_of_isWeaklyContractible_large
      J.toGrothendieck U hU)

/-- **Weibel's acyclic assembly lemma for a morphism of doubly bounded double complexes**: a
morphism of double complexes vanishing in second degrees `< b` and first degrees `< a` which is a
quasi-isomorphism in every first degree is one on total complexes. -/
public lemma quasiIso_total_map_of_bounded
    {A : Type u} [Category.{v} A] [Abelian A]
    {Z Z' : HomologicalComplex₂ A (up ℤ) (up ℤ)} (f : Z ⟶ Z')
    (a b : ℤ)
    (hq : ∀ p q, q < b → IsZero ((Z.X p).X q))
    (hp : ∀ p, p < a → IsZero (Z.X p))
    (hq' : ∀ p q, q < b → IsZero ((Z'.X p).X q))
    (hp' : ∀ p, p < a → IsZero (Z'.X p))
    [Z.HasTotal (up ℤ)] [Z'.HasTotal (up ℤ)]
    (hf : ∀ p, QuasiIso (f.f p)) :
    QuasiIso (HomologicalComplex₂.total.map f (up ℤ)) := by
  let S := HomologicalComplex₂.shiftFunctor₂ A b
  have hS : QuasiIso (HomologicalComplex₂.total.map (S.map f) (up ℤ)) := by
    apply StacksDraft.TotalComplexQuasiIso.quasiIso_total_map _ a
    · exact fun p q _ => hq p (q + b) (by omega)
    · exact fun p hpa => (shiftFunctor _ b).map_isZero (hp p hpa)
    · exact fun p q _ => hq' p (q + b) (by omega)
    · exact fun p hpa => (shiftFunctor _ b).map_isZero (hp' p hpa)
    · intro p
      have := hf p
      exact inferInstanceAs (QuasiIso ((f.f p)⟦b⟧'))
  have : QuasiIso (HomologicalComplex₂.total.map (S.map f) (up ℤ) ≫
      (Z'.totalShift₂Iso b).hom) := inferInstance
  rw [HomologicalComplex₂.totalShift₂Iso_hom_naturality] at this
  have := quasiIso_of_comp_left (Z.totalShift₂Iso b).hom
    ((HomologicalComplex₂.total.map f (up ℤ))⟦b⟧')
  exact (CochainComplex.quasiIso_shift_iff _ b).mp this

section AbelianComparison

open HomologicalComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

private def homCochainFunctor (R : ChainComplex A ℕ) :
    A ⥤ CochainComplex AddCommGrpCat.{v} ℕ where
  obj F := ((preadditiveYoneda.obj F).mapHomologicalComplex (down ℕ).symm).obj R.op
  map g := (NatTrans.mapHomologicalComplex (preadditiveYoneda.map g) (down ℕ).symm).app R.op
  map_id F := by
    ext n x
    exact Category.comp_id x
  map_comp f g := by
    ext n x
    exact (Category.assoc x f g).symm

private def homologyZeroAugmentation (R : ChainComplex A ℕ) :
    R ⟶ (ChainComplex.single₀ A).obj (R.homology 0) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨R.pOpcycles 0 ≫ R.isoHomologyι₀.inv, by simp⟩

/-- In degree zero the canonical map out of homology is the comparison with opcycles. -/
private lemma homologyι_zero_eq (Q : ChainComplex A ℕ) :
    Q.homologyι 0 = Q.isoHomologyι₀.hom := rfl

/-- Degree `0` of a complex concentrated in degree `0` is the object itself, identically. -/
private lemma singleObjXSelf_down_zero_hom (X : A) :
    (singleObjXSelf (down ℕ) 0 X).hom = 𝟙 X := rfl

/-- On a complex concentrated in degree zero, the projection onto degree-zero opcycles followed
by the canonical identification of homology with the object is the identity. -/
private lemma pOpcycles_isoHomologyι₀_inv_singleObjHomologySelfIso_hom (X : A) :
    ((ChainComplex.single₀ A).obj X).pOpcycles 0 ≫
        ((ChainComplex.single₀ A).obj X).isoHomologyι₀.inv ≫
          (singleObjHomologySelfIso (down ℕ) 0 X).hom = 𝟙 X := by
  rw [← homologyι_singleObjOpcyclesSelfIso_inv, homologyι_zero_eq, Iso.inv_hom_id_assoc,
    pOpcycles_singleObjOpcyclesSelfIso_inv]
  exact singleObjXSelf_down_zero_hom X

private lemma quasiIso_homologyZeroAugmentation (R : ChainComplex A ℕ)
    (hR : ∀ n : ℕ, 0 < n → IsZero (R.homology n)) :
    QuasiIso (homologyZeroAugmentation R) := by
  constructor
  intro n
  cases n with
  | zero =>
    rw [quasiIsoAt_iff_isIso_homologyMap]
    have h : homologyMap (homologyZeroAugmentation R) 0 ≫
        (singleObjHomologySelfIso (down ℕ) 0 (R.homology 0)).hom = 𝟙 _ := by
      apply (cancel_epi (R.pOpcycles 0 ≫ R.isoHomologyι₀.inv)).mp
      simp only [Category.assoc, Category.comp_id]
      rw [← Category.assoc R.isoHomologyι₀.inv, ChainComplex.isoHomologyι₀_inv_naturality,
        Category.assoc, p_opcyclesMap_assoc]
      simp only [homologyZeroAugmentation, ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
      rw [pOpcycles_isoHomologyι₀_inv_singleObjHomologySelfIso_hom]
      exact Category.comp_id _
    have : IsIso (homologyMap (homologyZeroAugmentation R) 0 ≫
        (singleObjHomologySelfIso (down ℕ) 0 (R.homology 0)).hom) := by
      rw [h]; infer_instance
    exact IsIso.of_isIso_comp_right _
      (singleObjHomologySelfIso (down ℕ) 0 (R.homology 0)).hom
  | succ n =>
    rw [quasiIsoAt_iff_isIso_homologyMap]
    apply IsZero.isIso
    · exact hR _ (by omega)
    · exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
        (HomologicalComplex.ExactAt.of_isZero
          (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)))

private def homCochainMap {R S : ChainComplex A ℕ} (f : R ⟶ S) :
    homCochainFunctor S ⟶ homCochainFunctor R where
  app F := ((preadditiveYoneda.obj F).mapHomologicalComplex (down ℕ).symm).map
    ((HomologicalComplex.opFunctor A (down ℕ)).map f.op)
  naturality X Y g := by
    ext n x
    change S.X n ⟶ X at x
    change (f.f n) ≫ (x ≫ g) = ((f.f n) ≫ x) ≫ g
    exact (Category.assoc _ _ _).symm

/-- Mapping into an injective object sends epimorphisms to epimorphisms, hence preserves
homology. -/
private instance preadditiveYoneda_preservesHomology (F : A) [Injective F] :
    (preadditiveYoneda.obj F).PreservesHomology :=
  let : (preadditiveYoneda.obj F).PreservesEpimorphisms :=
    (Injective.injective_iff_preservesEpimorphisms_preadditiveYoneda_obj F).mp inferInstance
  Functor.preservesHomology_of_preservesEpis_and_kernels _

private lemma quasiIso_homCochainMap {R S : ChainComplex A ℕ} (f : R ⟶ S)
    [QuasiIso f] (F : A) [Injective F] :
    QuasiIso ((homCochainMap f).app F) :=
  HomologicalComplex.quasiIso_map_of_preservesHomology
    ((HomologicalComplex.opFunctor A (down ℕ)).map f.op) (preadditiveYoneda.obj F)

private def homSingleComparison (R : A) :
    preadditiveCoyoneda.obj (op R) ⋙ CochainComplex.single₀ AddCommGrpCat.{v} ⟶
      homCochainFunctor ((ChainComplex.single₀ A).obj R) where
  app F := (CochainComplex.fromSingle₀Equiv _ _).symm ⟨𝟙 _,
    ((preadditiveYoneda.obj F).map_isZero
      (isZero_single_obj_X (down ℕ) 0 R 1 (by omega)).op).eq_of_tgt _ _⟩
  naturality F G g := by
    apply HomologicalComplex.hom_ext
    intro n
    cases n with
    | zero =>
      simp only [comp_f]
      rfl
    | succ n =>
      exact (isZero_single_obj_X (up ℕ) 0 _ (n + 1) (by omega)).eq_of_src _ _

private lemma isIso_homSingleComparison (R F : A) :
    IsIso ((homSingleComparison R).app F) := by
  have : ∀ n, IsIso (((homSingleComparison R).app F).f n) := by
    intro n
    cases n with
    | zero =>
      change IsIso (𝟙 _)
      infer_instance
    | succ n =>
      apply IsZero.isIso
      · exact isZero_single_obj_X (up ℕ) 0 _ (n + 1) (by omega)
      · exact (preadditiveYoneda.obj F).map_isZero
          ((isZero_single_obj_X (down ℕ) 0 R (n + 1) (by omega)).op)
  exact HomologicalComplex.Hom.isIso_of_components _

private def singleExtendIso :
    CochainComplex.single₀ A ⋙ embeddingUpNat.extendFunctor A ≅
      HomologicalComplex.single A (up ℤ) 0 := by
  refine NatIso.ofComponents (fun X => HomologicalComplex.extendSingleIso
    embeddingUpNat X 0 0 rfl) ?_
  intro X Y f
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [Functor.comp_map, ComplexShape.Embedding.extendFunctor,
      HomologicalComplex.comp_f, CochainComplex.single₀,
      HomologicalComplex.extendSingleIso, HomologicalComplex.mkHomToSingle_f,
      HomologicalComplex.extendMap_f _ _ (show embeddingUpNat.f 0 = 0 from rfl),
      HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc]
  · exact (IsZero.of_iso (HomologicalComplex.isZero_single_obj_X (up ℤ) 0 X n hn)
      ((HomologicalComplex.eval A (up ℤ) n).mapIso
        (HomologicalComplex.extendSingleIso embeddingUpNat X 0 0 rfl))).eq_of_src _ _


end AbelianComparison

/-- The complex of free abelian sheaves attached to a simplicial formal coproduct over `U`. -/
private abbrev freeHypercoverComplex
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}] :=
  (_root_.CategoryTheory.SimplicialObject.freeAbelianSheafComplexFunctor
    J.toGrothendieck).obj (SectionsOver.associatedSimplicialPresheaf.{w} K)

/-- **[Stacks, Tag 01GX]**: the `Hom(-, F)` complex of the complex of free abelian sheaves of `K`
is the hypercover cochain complex of `F`, naturally in the abelian sheaf `F`. -/
private def homFunctorIsoSections
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}] :
    homCochainFunctor (freeHypercoverComplex J U K) ≅
      hypercoverCochainNatFunctor J U K :=
  homFreeAbelianSheafComplexFunctorIsoHypercoverCochain J U K

/-- The augmentation of the complex of free abelian sheaves of a hypercovering by the free
abelian sheaf on the object covered. -/
private def freeHypercoverAugmentation
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]
    (hK : IsHypercovering J K) :
    freeHypercoverComplex J U K ⟶
      (ChainComplex.single₀ _).obj
        ((presheafToSheaf J.toGrothendieck AddCommGrpCat.{max u v w}).obj
          (uliftYoneda.{max u w}.obj U ⋙ AddCommGrpCat.free)) :=
  homologyZeroAugmentation (freeHypercoverComplex J U K) ≫
    (ChainComplex.single₀ _).map (sheafHomologyZeroIso_of_isHypercovering J K hK).hom

private lemma quasiIso_freeHypercoverAugmentation
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]
    (hK : IsHypercovering J K) :
    QuasiIso (freeHypercoverAugmentation J U K hK) := by
  have h₀ := quasiIso_homologyZeroAugmentation (freeHypercoverComplex J U K)
    (isZero_sheafHomology_of_isHypercovering J K hK)
  have h₁ : QuasiIso ((ChainComplex.single₀
      (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})).map
      (sheafHomologyZeroIso_of_isHypercovering J K hK).hom) :=
    quasiIso_of_isIso ((ChainComplex.single₀
      (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})).map
      (sheafHomologyZeroIso_of_isHypercovering J K hK).hom)
  dsimp only [freeHypercoverAugmentation]
  exact quasiIso_comp (hφ := h₀) (hφ' := h₁)
    (homologyZeroAugmentation (freeHypercoverComplex J U K))
    ((ChainComplex.single₀ _).map (sheafHomologyZeroIso_of_isHypercovering J K hK).hom)

private def injectiveSectionsComparison
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]
    (hK : IsHypercovering J K) :
    homCochainFunctor
      ((ChainComplex.single₀ _).obj
        ((presheafToSheaf J.toGrothendieck AddCommGrpCat.{max u v w}).obj
          (uliftYoneda.{max u w}.obj U ⋙ AddCommGrpCat.free))) ⟶
      hypercoverCochainNatFunctor J U K :=
  homCochainMap (freeHypercoverAugmentation J U K hK) ≫
    (homFreeAbelianSheafComplexFunctorIsoHypercoverCochain J U K).hom

private lemma quasiIso_injectiveSectionsComparison
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]
    (hK : IsHypercovering J K)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) [Injective F] :
    QuasiIso ((injectiveSectionsComparison J U K hK).app F) := by
  have := quasiIso_freeHypercoverAugmentation J U K hK
  have h₀ := quasiIso_homCochainMap (freeHypercoverAugmentation J U K hK) F
  change QuasiIso ((homCochainMap (freeHypercoverAugmentation J U K hK)).app F ≫
    (homFreeAbelianSheafComplexFunctorIsoHypercoverCochain J U K).hom.app F)
  have h₁ : QuasiIso
      ((homFreeAbelianSheafComplexFunctorIsoHypercoverCochain J U K).hom.app F) :=
    quasiIso_of_isIso _
  exact quasiIso_comp (hφ := h₀) (hφ' := h₁) _ _

private def freeYonedaSectionsIso
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}] :
    preadditiveCoyoneda.obj (op
      ((presheafToSheaf J.toGrothendieck AddCommGrpCat.{max u v w}).obj
        (uliftYoneda.{max u w}.obj U ⋙ AddCommGrpCat.free))) ≅
      sheafSectionsFunctor J U := by
  let e (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) :
      ((presheafToSheaf J.toGrothendieck AddCommGrpCat.{max u v w}).obj
        (uliftYoneda.{max u w}.obj U ⋙ AddCommGrpCat.free) ⟶ F) ≃ F.obj.obj (op U) :=
    ((sheafificationAdjunction J.toGrothendieck AddCommGrpCat.{max u v w}).homEquiv _ F).trans
      (((AddCommGrpCat.adj.{max u v w}.whiskerRight Cᵒᵖ).homEquiv _ _).trans
        uliftYonedaEquiv.{max u w})
  let ea (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) :
      _ ≃+ F.obj.obj (op U) :=
    { toEquiv := e F
      map_add' := fun f g => by
        have h := (sheafificationAdjunction J.toGrothendieck
            AddCommGrpCat.{max u v w}).homAddEquiv_add
          (uliftYoneda.{max u w}.obj U ⋙ AddCommGrpCat.free) F f g
        let q := fun k => uliftYonedaEquiv.{max u w}
          ((AddCommGrpCat.adj.{max u v w}.whiskerRight Cᵒᵖ).homEquiv
            (uliftYoneda.{max u w}.obj U) F.obj k)
        exact (congrArg q h).trans (by rfl) }
  refine NatIso.ofComponents (fun F => (ea F).toAddCommGrpIso) ?_
  intro F G g
  apply ConcreteCategory.hom_ext
  intro f
  change ((presheafToSheaf J.toGrothendieck AddCommGrpCat.{max u v w}).obj
    (uliftYoneda.{max u w}.obj U ⋙ AddCommGrpCat.free) ⟶ F) at f
  change e G (f ≫ g) = g.hom.app (op U) (e F f)
  dsimp only [e, Equiv.trans_apply]
  rw [(sheafificationAdjunction J.toGrothendieck
    AddCommGrpCat.{max u v w}).homEquiv_naturality_right]
  rfl

private def sectionsComparisonNat
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]
    (hK : IsHypercovering J K) :
    sheafSectionsFunctor J U ⋙ CochainComplex.single₀ _ ⟶
      hypercoverCochainNatFunctor J U K :=
  Functor.whiskerRight (freeYonedaSectionsIso J U).inv (CochainComplex.single₀ _) ≫
    homSingleComparison _ ≫ injectiveSectionsComparison J U K hK

private lemma quasiIso_sectionsComparisonNat
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]
    (hK : IsHypercovering J K)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) [Injective F] :
    QuasiIso ((sectionsComparisonNat J U K hK).app F) := by
  have := isIso_homSingleComparison
    ((presheafToSheaf J.toGrothendieck AddCommGrpCat.{max u v w}).obj
        (uliftYoneda.{max u w}.obj U ⋙ AddCommGrpCat.free)) F
  have := quasiIso_injectiveSectionsComparison J U K hK F
  have : QuasiIso ((CochainComplex.single₀ _).map ((freeYonedaSectionsIso J U).inv.app F)) :=
    quasiIso_of_isIso _
  have : QuasiIso ((homSingleComparison
    ((presheafToSheaf J.toGrothendieck AddCommGrpCat.{max u v w}).obj
      (uliftYoneda.{max u w}.obj U ⋙ AddCommGrpCat.free))).app F) := quasiIso_of_isIso _
  dsimp only [sectionsComparisonNat, NatTrans.comp_app, Functor.whiskerRight_app]
  exact quasiIso_comp _ _

/-- The augmentation `Γ(X, F)[0] ⟶ s(F(K))` of the hypercover cochain complex by the sections on
`X`, in integer degrees and natural in the abelian sheaf `F`. -/
@[no_expose] public def sectionsComparisonInt
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]
    (hK : IsHypercovering J K) :
    sheafSectionsFunctor J U ⋙
        HomologicalComplex.single AddCommGrpCat.{max u v w} (up ℤ) 0 ⟶
      hypercoverCochainIntFunctor J U K :=
  Functor.whiskerLeft _ singleExtendIso.inv ≫
    Functor.whiskerRight (sectionsComparisonNat J U K hK) (embeddingUpNat.extendFunctor _)

/-- **Stacks 01GV and 01GW**: the augmentation `Γ(X, F)[0] ⟶ s(F(K))` is a quasi-isomorphism when
`F` is an injective abelian sheaf. -/
public lemma quasiIso_sectionsComparisonInt
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]
    (hK : IsHypercovering J K)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) [Injective F] :
    QuasiIso ((sectionsComparisonInt J U K hK).app F) := by
  have := quasiIso_sectionsComparisonNat J U K hK F
  have : QuasiIso (singleExtendIso.inv.app
    ((sheafSectionsFunctor J U).obj F)) := quasiIso_of_isIso _
  have h₂ : QuasiIso ((embeddingUpNat.extendFunctor AddCommGrpCat.{max u v w}).map
      ((sectionsComparisonNat J U K hK).app F)) :=
    HomologicalComplex.instQuasiIsoExtendMap _ _ _ _
  dsimp only [sectionsComparisonInt, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  exact quasiIso_comp (hφ' := h₂)
    (singleExtendIso.inv.app ((sheafSectionsFunctor J U).obj F))
    ((embeddingUpNat.extendFunctor AddCommGrpCat.{max u v w}).map
      ((sectionsComparisonNat J U K hK).app F))

/-- The values of an abelian sheaf on the members of a formal coproduct over `U`. -/
abbrev familySectionsFunctor (T : FormalCoproduct.{w} (Over U)) :
    Sheaf J.toGrothendieck AddCommGrpCat.{max u v w} ⥤
      Discrete T.I ⥤ AddCommGrpCat.{max u v w} :=
  sheafToPresheaf J.toGrothendieck AddCommGrpCat.{max u v w} ⋙
    (Functor.whiskeringLeft _ _ _).obj
      (Discrete.functor (fun i => op (T.obj i).left))

/-- The degreewise comparison of the hypercover cochain complex with the product of sections is
natural in the abelian sheaf. -/
lemma evalOpProductIso_naturality (n : ℕ)
    {F G : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}} (g : F ⟶ G) :
    ((hypercoverCochainNatFunctor J U K).map g).f n ≫
        (SectionsOver.evalOpProductIso J.toGrothendieck (K.obj (op ⦋n⦌)) G).hom =
      (SectionsOver.evalOpProductIso J.toGrothendieck (K.obj (op ⦋n⦌)) F).hom ≫
        CategoryTheory.Limits.Pi.map
          (fun i ↦ g.hom.app (op ((K.obj (op ⦋n⦌)).obj i).left)) := rfl

/-- The degreewise comparison of the degree-`n` term of the hypercover cochain complex of `F` with
the limit of the sections of `F` on the members of the covering in degree `n`. -/
def hypercoverDegreeComponent (n : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) :
    (hypercoverCochainNatFunctor J U K ⋙
        HomologicalComplex.eval AddCommGrpCat.{max u v w} (up ℕ) n).obj F ≅
      (familySectionsFunctor J U (K.obj (op ⦋n⦌)) ⋙ lim).obj F :=
  SectionsOver.evalOpProductIso J.toGrothendieck (K.obj (op ⦋n⦌)) F ≪≫
    Pi.isoLimit ((familySectionsFunctor J U (K.obj (op ⦋n⦌))).obj F)

/-- The component of `hypercoverDegreeComponent` at the member `i` is the projection onto `i`
after `SectionsOver.evalOpProductIso`. -/
lemma hypercoverDegreeComponent_hom_π (n : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (i : (K.obj (op ⦋n⦌)).I) :
    (hypercoverDegreeComponent J U K n F).hom ≫
        limit.π ((familySectionsFunctor J U (K.obj (op ⦋n⦌))).obj F) (Discrete.mk i) =
      (SectionsOver.evalOpProductIso J.toGrothendieck (K.obj (op ⦋n⦌)) F).hom ≫
        Pi.π (fun i ↦ F.obj.obj (op ((K.obj (op ⦋n⦌)).obj i).left)) i := by
  dsimp only [hypercoverDegreeComponent]
  exact (Category.assoc
      (SectionsOver.evalOpProductIso J.toGrothendieck (K.obj (op ⦋n⦌)) F).hom
      (Pi.isoLimit ((familySectionsFunctor J U (K.obj (op ⦋n⦌))).obj F)).hom
      (limit.π ((familySectionsFunctor J U (K.obj (op ⦋n⦌))).obj F) (Discrete.mk i))).trans
    (congrArg (fun t =>
      (SectionsOver.evalOpProductIso J.toGrothendieck (K.obj (op ⦋n⦌)) F).hom ≫ t)
      (Pi.isoLimit_hom_π ((familySectionsFunctor J U (K.obj (op ⦋n⦌))).obj F) i))

/-- Degree `n` of the hypercover cochain complex functor is naturally isomorphic to the limit of
the sections on the members of the covering in degree `n`. -/
def hypercoverDegreeIso (n : ℕ) :
    hypercoverCochainNatFunctor J U K ⋙
      HomologicalComplex.eval _ (up ℕ) n ≅
    familySectionsFunctor J U (K.obj (op ⦋n⦌)) ⋙ lim := by
  refine NatIso.ofComponents (hypercoverDegreeComponent J U K n) ?_
  intro F G g
  apply limit.hom_ext
  rintro ⟨i⟩
  rw [Category.assoc, hypercoverDegreeComponent_hom_π]
  conv_rhs => rw [Category.assoc, Functor.comp_map, lim_map, limMap_π, ← Category.assoc,
    hypercoverDegreeComponent_hom_π]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  rw [Functor.comp_map, HomologicalComplex.eval_map, evalOpProductIso_naturality]
  refine Eq.trans (Category.assoc _ _ _) ?_
  rw [Pi.map_π]
  exact (Category.assoc _ _ _).symm

private lemma exact_hypercoverDegree
    [Small.{v} C] [HasSheafify J.toGrothendieck (Type v)]
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]
    (n : ℕ)
    (hweak : ∀ i : (K.obj (op ⦋n⦌)).I,
      J.toGrothendieck.IsWeaklyContractible ((K.obj (op ⦋n⦌)).obj i).left) :
    exactFunctor _ _ (hypercoverCochainIntFunctor J U K ⋙
      HomologicalComplex.eval _ (up ℤ) n) := by
  let : AB4StarOfSize.{w} AddCommGrpCat.{max u v w} := AB4StarOfSize_shrink _
  let G := familySectionsFunctor J U (K.obj (op ⦋n⦌))
  have hG (i : Discrete (K.obj (op ⦋n⦌)).I) :
      exactFunctor _ _ (G ⋙ (evaluation _ _).obj i) :=
    exact_sections_of_isWeaklyContractible J _ (hweak i.as)
  have : PreservesFiniteLimits G := preservesFiniteLimits_of_evaluation G (fun i => (hG i).1)
  have : PreservesFiniteColimits G := preservesFiniteColimits_of_evaluation G (fun i => (hG i).2)
  let e := (Functor.isoWhiskerLeft
    (hypercoverCochainNatFunctor J U K)
    (embeddingUpNat.extendFunctorCompEvalIso AddCommGrpCat.{max u v w} (i := n) rfl)) ≪≫
      hypercoverDegreeIso J U K n
  have : PreservesFiniteLimits
      (hypercoverCochainIntFunctor J U K ⋙
        HomologicalComplex.eval _ (up ℤ) n) := preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteColimits
      (hypercoverCochainIntFunctor J U K ⋙
        HomologicalComplex.eval _ (up ℤ) n) := preservesFiniteColimits_of_natIso e.symm
  change PreservesFiniteLimits _ ∧ PreservesFiniteColimits _
  exact ⟨inferInstance, inferInstance⟩

/-- The double complex obtained by applying the alternating hypercover cochain
complex degreewise to a complex of abelian sheaves. -/
public noncomputable def hypercoverDoubleComplex
    (E : CochainComplex.Plus (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})) :
    HomologicalComplex₂ AddCommGrpCat.{max u v w} (up ℤ) (up ℤ) :=
  HomologicalComplex₂.flip
    (((hypercoverCochainIntFunctor J U K).mapHomologicalComplex (up ℤ)).obj E.obj)

/-- The total complex of the alternating hypercover cochain complex of a
bounded-below complex of abelian sheaves. -/
public noncomputable def hypercoverTotalComplex
    (E : CochainComplex.Plus (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})) :
    CochainComplex AddCommGrpCat.{max u v w} ℤ :=
  (hypercoverDoubleComplex (J := J) (U := U) (K := K) E).total (up ℤ)

attribute [local instance] HasDerivedCategory.standard

/-- A homological complex all of whose terms are zero is zero. -/
lemma isZero_complex_of_components {A : Type u} [Category.{v} A]
    [HasZeroMorphisms A] {ι : Type*} {c : ComplexShape ι} (M : HomologicalComplex A c)
    (hM : ∀ i, IsZero (M.X i)) : IsZero M :=
  (IsZero.iff_id_eq_zero _).mpr (HomologicalComplex.hom_ext _ _ fun i => (hM i).eq_of_src _ _)

private lemma hypercoverDoubleComplex_zero_left
    (E : CochainComplex.Plus (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}))
    (p : ℤ) (hp : p < 0) : IsZero ((hypercoverDoubleComplex J U K E).X p) :=
  isZero_complex_of_components _ fun q => CochainComplex.isZero_of_isStrictlyGE
    (((hypercoverCochainNatFunctor J U K).obj (E.obj.X q)).extend embeddingUpNat) 0 p hp

private lemma hypercoverDoubleComplex_zero_right
    (E : CochainComplex.Plus (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}))
    (n : ℤ) [E.obj.IsStrictlyGE n] (p q : ℤ) (hq : q < n) :
    IsZero (((hypercoverDoubleComplex J U K E).X p).X q) :=
  (HomologicalComplex.eval _ (up ℤ) p).map_isZero
    ((hypercoverCochainIntFunctor J U K).map_isZero
      (E.obj.isZero_of_isStrictlyGE n q hq))

private def hypercoverTotalMap
    {E E' : CochainComplex.Plus (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})}
    (f : E ⟶ E') : hypercoverTotalComplex J U K E ⟶ hypercoverTotalComplex J U K E' :=
  HomologicalComplex₂.total.map
    ((HomologicalComplex₂.flipFunctor _ (up ℤ) (up ℤ)).map
      (((hypercoverCochainIntFunctor J U K).mapHomologicalComplex
        (up ℤ)).map f.hom)) (up ℤ)

private lemma quasiIso_hypercoverTotalMap
    [Small.{v} C] [HasSheafify J.toGrothendieck (Type v)]
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]
    (hweak : ∀ n : ℕ, ∀ i : (K.obj (op ⦋n⦌)).I,
      J.toGrothendieck.IsWeaklyContractible ((K.obj (op ⦋n⦌)).obj i).left)
    {E E' : CochainComplex.Plus (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})}
    (f : E ⟶ E') [QuasiIso f.hom] (n : ℤ) [E.obj.IsStrictlyGE n] [E'.obj.IsStrictlyGE n] :
    QuasiIso (hypercoverTotalMap J U K f) := by
  apply quasiIso_total_map_of_bounded _ 0 n
    (hypercoverDoubleComplex_zero_right J U K E n)
    (hypercoverDoubleComplex_zero_left J U K E)
    (hypercoverDoubleComplex_zero_right J U K E' n)
    (hypercoverDoubleComplex_zero_left J U K E')
  intro p
  by_cases hp : 0 ≤ p
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    obtain ⟨hlim, hcolim⟩ := exact_hypercoverDegree J U K p (hweak p)
    let G := hypercoverCochainIntFunctor J U K ⋙
      HomologicalComplex.eval _ (up ℤ) (p : ℤ)
    have : PreservesFiniteLimits G := hlim
    have : PreservesFiniteColimits G := hcolim
    have : G.PreservesHomology := inferInstance
    have : G.Additive := Functor.additive_of_preserves_binary_products G
    exact HomologicalComplex.quasiIso_map_of_preservesHomology f.hom G
  · have := IsZero.isIso
      (hypercoverDoubleComplex_zero_left J U K E p (by omega))
      (hypercoverDoubleComplex_zero_left J U K E' p (by omega))
      (((HomologicalComplex₂.flipFunctor _ (up ℤ) (up ℤ)).map
        (((hypercoverCochainIntFunctor J U K).mapHomologicalComplex
          (up ℤ)).map f.hom)).f p)
    infer_instance

/-- The augmentation of the hypercover cochain complex, applied degreewise to a bounded below
complex of injective abelian sheaves, is a quasi-isomorphism on total complexes. -/
public lemma quasiIso_total_sectionsComparisonInt
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]
    (hK : IsHypercovering J K)
    (I : CochainComplex.Plus (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}))
    (n : ℤ) [I.obj.IsStrictlyGE n] [∀ p, Injective (I.obj.X p)] :
    QuasiIso (HomologicalComplex₂.total.map
      ((NatTrans.mapHomologicalComplex (sectionsComparisonInt J U K hK)
        (up ℤ)).app I.obj) (up ℤ)) := by
  apply quasiIso_total_map_of_bounded _ n 0
  · intro p q hq
    exact HomologicalComplex.isZero_single_obj_X (up ℤ) 0 _ q (by omega)
  · intro p hp
    exact (sheafSectionsFunctor J U ⋙
      HomologicalComplex.single _ (up ℤ) 0).map_isZero
        (I.obj.isZero_of_isStrictlyGE n p hp)
  · intro p q hq
    exact CochainComplex.isZero_of_isStrictlyGE
      (((hypercoverCochainNatFunctor J U K).obj
        (I.obj.X p)).extend embeddingUpNat) 0 q hq
  · intro p hp
    exact (hypercoverCochainIntFunctor J U K).map_isZero
      (I.obj.isZero_of_isStrictlyGE n p hp)
  · intro p
    exact quasiIso_sectionsComparisonInt J U K hK (I.obj.X p)

private def sectionsIsoHypercoverTotal_of_injective
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]
    (hK : IsHypercovering J K)
    (I : CochainComplex.Plus (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}))
    (n : ℤ) [I.obj.IsStrictlyGE n] [∀ p, Injective (I.obj.X p)] :
    DerivedCategory.Q.obj
      (((sheafSectionsFunctor J U).mapHomologicalComplex (up ℤ)).obj I.obj) ≅
      DerivedCategory.Q.obj (hypercoverTotalComplex J U K I) := by
  let G := sheafSectionsFunctor J U
  let H := hypercoverCochainIntFunctor J U K
  let Z := (H.mapHomologicalComplex (up ℤ)).obj I.obj
  let Z₀ := ((G ⋙ HomologicalComplex.single _ (up ℤ) 0).mapHomologicalComplex (up ℤ)).obj I.obj
  let f : Z₀ ⟶ Z := (NatTrans.mapHomologicalComplex (sectionsComparisonInt J U K hK)
    (up ℤ)).app I.obj
  have hf : QuasiIso (HomologicalComplex₂.total.map f (up ℤ)) :=
    quasiIso_total_sectionsComparisonInt J U K hK I n
  have := StacksDraft.TotalComplexQuasiIso.isIso_totalSingleRowZeroUnit
    ((G.mapHomologicalComplex (up ℤ)).obj I.obj)
  exact DerivedCategory.Q.mapIso
      (asIso (StacksDraft.TotalComplexQuasiIso.totalSingleRowZeroUnit
        ((G.mapHomologicalComplex (up ℤ)).obj I.obj))) ≪≫
    asIso (DerivedCategory.Q.map (HomologicalComplex₂.total.map f (up ℤ))) ≪≫
    DerivedCategory.Q.mapIso (HomologicalComplex₂.totalFlipIso Z (up ℤ)).symm

private def rightDerivedIsoOfInjectiveComplex
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (L : CochainComplex.Plus (InjectiveObject A)) :
    DerivedCategory.Plus.ι.obj (F.rightDerivedFunctorPlus.obj
      (DerivedCategory.Plus.Q.obj ((InjectiveObject.ι A).mapCochainComplexPlus.obj L))) ≅
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (up ℤ)).obj
      (((InjectiveObject.ι A).mapCochainComplexPlus.obj L).obj)) := by
  let I := (InjectiveObject.ι A).mapCochainComplexPlus.obj L
  let eI : DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient A).obj I) ≅
      DerivedCategory.Plus.Q.obj I :=
    DerivedCategory.Plus.ι.preimageIso ((DerivedCategory.quotientCompQhIso A).app I.obj)
  let eF : F.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.quotient A).obj I) ≅
      (HomotopyCategory.Plus.quotient B).obj (F.mapCochainComplexPlus.obj I) :=
    (HomotopyCategory.Plus.ι B).preimageIso ((F.mapHomotopyCategoryFactors (up ℤ)).app I.obj)
  let eFI : DerivedCategory.Plus.Qh.obj
      ((HomotopyCategory.Plus.quotient B).obj (F.mapCochainComplexPlus.obj I)) ≅
      DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj I) :=
    DerivedCategory.Plus.ι.preimageIso ((DerivedCategory.quotientCompQhIso B).app
      ((F.mapHomologicalComplex (up ℤ)).obj I.obj))
  exact DerivedCategory.Plus.ι.mapIso
    (F.rightDerivedFunctorPlus.mapIso eI.symm ≪≫
      (asIso (F.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.quotient A).obj I))).symm ≪≫
      DerivedCategory.Plus.Qh.mapIso eF ≪≫ eFI)

/-- A hypercovering by weakly contractible objects computes the derived
sections of any bounded-below complex of abelian sheaves. -/
@[stacks 09A2]
public noncomputable def derivedSectionsIsoHypercoverTotalComplex
    [Small.{v} C]
    [HasSheafify J.toGrothendieck (Type v)]
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]
    [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})]
    (hK : IsHypercovering J K)
    (hweak : ∀ n : ℕ, ∀ i : (K.obj (op ⦋n⦌)).I,
      J.toGrothendieck.IsWeaklyContractible ((K.obj (op ⦋n⦌)).obj i).left)
    (E : CochainComplex.Plus (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})) :
    DerivedCategory.Plus.ι.obj
      ((sheafSectionsFunctor J U).rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj E)) ≅
      DerivedCategory.Q.obj (hypercoverTotalComplex J U K E) := Classical.choice (by
  obtain ⟨n, hn⟩ := E.property
  have : E.obj.IsStrictlyGE n := hn
  obtain ⟨L, hL, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective E n
  have : QuasiIso i.hom := hi
  have : IsIso (DerivedCategory.Plus.Q.map i) := by
    have : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map i)) :=
      inferInstanceAs (IsIso (DerivedCategory.Q.map i.hom))
    exact isIso_of_fully_faithful DerivedCategory.Plus.ι _
  let I := (InjectiveObject.ι _).mapCochainComplexPlus.obj L
  have : L.obj.IsStrictlyGE n := hL
  have : I.obj.IsStrictlyGE n := by
    change CochainComplex.IsStrictlyGE
      (((InjectiveObject.ι _).mapHomologicalComplex (up ℤ)).obj L.obj) n
    infer_instance
  have : ∀ p, Injective (I.obj.X p) := by
    intro p
    change Injective (L.obj.X p).obj
    exact (L.obj.X p).property
  have := quasiIso_hypercoverTotalMap J U K hweak i n
  exact ⟨DerivedCategory.Plus.ι.mapIso
    ((sheafSectionsFunctor J U).rightDerivedFunctorPlus.mapIso
      (asIso (DerivedCategory.Plus.Q.map i))) ≪≫
    rightDerivedIsoOfInjectiveComplex (sheafSectionsFunctor J U) L ≪≫
    sectionsIsoHypercoverTotal_of_injective J U K hK I n ≪≫
    (asIso (DerivedCategory.Q.map (hypercoverTotalMap J U K i))).symm⟩)


section HypercoverNaturality

/-- In degree zero, the augmentation of a chain complex by its degree-zero homology is the
projection onto `opcycles` followed by the comparison of `opcycles` with homology. -/
private lemma homologyZeroAugmentation_f_zero {A : Type u} [Category.{v} A] [Abelian A]
    (R : ChainComplex A ℕ) :
    (homologyZeroAugmentation R).f 0 = R.pOpcycles 0 ≫ R.isoHomologyι₀.inv :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

omit [HasPullbacks C] in
/-- The degree-zero identification of Tag 01GE is the one *induced by the augmentation*: it is
the canonical degree-zero augmentation descended through `opcycles` and restricted along
`homologyι`. -/
private lemma sheafHomologyZeroIso_hom_eq_homologyι_descOpcycles
    (G : GrothendieckTopology C) [HasSheafify G AddCommGrpCat.{max u v w}]
    (A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type (max u v w)))
    (h₀ : Presheaf.IsLocallySurjective G (A.hom.app (op (SimplexCategory.mk 0))))
    (h₁ : Presheaf.IsLocallySurjective G
      (SimplicialObject.Augmented.edgesToFiberProduct A))
    (hm : ∀ n : ℕ, 1 ≤ n → Presheaf.IsLocallySurjective G
      (((SimplicialObject.coskAdj n).unit.app A.left).app
        (op (SimplexCategory.mk (n + 1))))) :
    (SimplicialObject.Augmented.sheafHomologyZeroIso_of_isLocallySurjective_matchingMaps
        G A h₀ h₁ hm).hom =
      ((SimplicialObject.freeAbelianSheafComplexFunctor G).obj A.left).homologyι 0 ≫
        ((SimplicialObject.freeAbelianSheafComplexFunctor G).obj A.left).descOpcycles
          (SimplicialObject.Augmented.freeAbelianSheafAugZero G A) 1 (by simp)
          (SimplicialObject.Augmented.d_comp_freeAbelianSheafAugZero G A 1) := by
  rw [SimplicialObject.Augmented.descOpcycles_freeAbelianSheafAugZero_eq,
    ← HomologicalComplex.homologyι_naturality_assoc,
    ← HomologicalComplex.homologyι_naturality_assoc,
    ← Presheaf.cechNerveSheafHomologyZeroAugmentation_eq_homologyι_descOpcycles
      (hk := SimplicialObject.Augmented.cechNerveSheafAugmentation_f_zero_eq G _)]
  rw [show (SimplicialObject.Augmented.sheafHomologyZeroIso_of_isLocallySurjective_matchingMaps
        G A h₀ h₁ hm).hom =
      ((SimplicialObject.sheafHomologyFunctor G 0).map
            ((SimplicialObject.coskAdj 1).unit.app A.left) ≫
          𝟙 _ ≫ (SimplicialObject.sheafHomologyFunctor G 0).map
            (SimplicialObject.Augmented.coskOneToCechNerve A)) ≫
        Presheaf.cechNerveSheafHomologyZeroAugmentation G
          (A.hom.app (op (SimplexCategory.mk 0))) from rfl,
    Category.id_comp, Category.assoc]
  rfl

/-- The degree-zero component of the augmentation of the free abelian sheaf complex of a
hypercovering is the free abelian sheaf functor applied to the degree-zero structure morphism. -/
private lemma freeHypercoverAugmentation_f_zero
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}] (hK : IsHypercovering J K) :
    (freeHypercoverAugmentation J U K hK).f 0 =
      SimplicialObject.Augmented.freeAbelianSheafAugZero J.toGrothendieck
        (associatedAugmentedSimplicialPresheafOver.{w} K) := by
  have hz : (freeHypercoverAugmentation J U K hK).f 0 =
      (homologyZeroAugmentation (freeHypercoverComplex J U K)).f 0 ≫
        (sheafHomologyZeroIso_of_isHypercovering J K hK).hom :=
    congrArg (fun t : (freeHypercoverComplex J U K).homology 0 ⟶
        (presheafToSheaf J.toGrothendieck AddCommGrpCat.{max u v w}).obj
          (uliftYoneda.{max u w}.obj U ⋙ AddCommGrpCat.free) ↦
        (homologyZeroAugmentation (freeHypercoverComplex J U K)).f 0 ≫ t)
      (ChainComplex.single₀_map_f_zero
        (sheafHomologyZeroIso_of_isHypercovering J K hK).hom)
  have key : (freeHypercoverComplex J U K).isoHomologyι₀.inv ≫
      (sheafHomologyZeroIso_of_isHypercovering J K hK).hom =
      (freeHypercoverComplex J U K).descOpcycles
        (SimplicialObject.Augmented.freeAbelianSheafAugZero J.toGrothendieck
          (associatedAugmentedSimplicialPresheafOver.{w} K)) 1 (by simp)
        (SimplicialObject.Augmented.d_comp_freeAbelianSheafAugZero J.toGrothendieck
          (associatedAugmentedSimplicialPresheafOver.{w} K) 1) := by
    rw [show (sheafHomologyZeroIso_of_isHypercovering J K hK).hom =
        (SimplicialObject.Augmented.sheafHomologyZeroIso_of_isLocallySurjective_matchingMaps
          J.toGrothendieck (associatedAugmentedSimplicialPresheafOver.{w} K)
          (isLocallySurjective_of_isHypercovering J K hK).1
          (isLocallySurjective_of_isHypercovering J K hK).2.1
          (isLocallySurjective_of_isHypercovering J K hK).2.2).hom from rfl,
      sheafHomologyZeroIso_hom_eq_homologyι_descOpcycles]
    exact (freeHypercoverComplex J U K).isoHomologyι₀.inv_hom_id_assoc _
  have main : (freeHypercoverComplex J U K).pOpcycles 0 ≫
      ((freeHypercoverComplex J U K).isoHomologyι₀.inv ≫
        (sheafHomologyZeroIso_of_isHypercovering J K hK).hom) =
      SimplicialObject.Augmented.freeAbelianSheafAugZero J.toGrothendieck
        (associatedAugmentedSimplicialPresheafOver.{w} K) := by
    rw [key]
    exact HomologicalComplex.p_descOpcycles _ _ _ _ _
  refine hz.trans (Eq.trans ?_ main)
  rw [homologyZeroAugmentation_f_zero]
  exact Category.assoc _ _ _

/-- A commutative square between two isomorphisms also commutes when read through the
inverses. -/
private lemma inv_square_of_hom_square {𝒜 : Type*} [Category 𝒜] {A A' B B' : 𝒜}
    (e : A ≅ B) (e' : A' ≅ B') (p : B ⟶ B') (b : A ⟶ A')
    (h : e.hom ≫ p = b ≫ e'.hom) : e.inv ≫ b = p ≫ e'.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

omit [HasPullbacks C] in
/-- **The degreewise comparison of Tag 01GX is natural in the simplicial semi-representable
object.**  A map `b` of the complexes of sections whose components are the restrictions along the
structure morphisms of `ρ` is `Hom(-, F)` of the induced map of free abelian sheaves, read through
`SectionsOver.sectionsDegreeIso`. -/
private lemma sectionsDegreeIso_comm_map (G : GrothendieckTopology C)
    [HasSheafify G AddCommGrpCat.{max u v w}]
    {L : SimplicialObject (FormalCoproduct.{w} (Over U))} (ρ : L ⟶ K)
    (F : Sheaf G AddCommGrpCat.{max u v w}) (n : ℕ)
    (b : (SectionsOver.sectionsComplex G K F).X n ⟶ (SectionsOver.sectionsComplex G L F).X n)
    (hb : ∀ (z : (SectionsOver.sectionsComplex G K F).X n) (i : (L.obj (op ⦋n⦌)).I),
      ConcreteCategory.hom
          (Pi.π (fun i ↦ F.obj.obj (op ((L.obj (op ⦋n⦌)).obj i).left)) i)
          (ConcreteCategory.hom (SectionsOver.evalOpProductIso G (L.obj (op ⦋n⦌)) F).hom
            (ConcreteCategory.hom b z)) =
        ConcreteCategory.hom
          (F.obj.map ((Over.forget U).map ((ρ.app (op ⦋n⦌)).φ i)).op)
          (ConcreteCategory.hom
            (Pi.π (fun l ↦ F.obj.obj (op ((K.obj (op ⦋n⦌)).obj l).left))
              ((ρ.app (op ⦋n⦌)).f i))
            (ConcreteCategory.hom
              (SectionsOver.evalOpProductIso G (K.obj (op ⦋n⦌)) F).hom z))) :
    (SectionsOver.sectionsDegreeIso G K F n).hom ≫
        ((preadditiveYoneda.obj F).rightOp.map
          (SectionsOver.freeAbelianSheafMap G (ρ.app (op ⦋n⦌)))).unop =
      b ≫ (SectionsOver.sectionsDegreeIso G L F n).hom := by
  apply ConcreteCategory.hom_ext
  intro z
  apply (SectionsOver.sectionsEquiv G (L.obj (op ⦋n⦌)) F).injective
  apply (Concrete.productEquiv (fun k ↦
    F.obj.obj (op ((L.obj (op ⦋n⦌)).obj k).left))).injective
  funext k
  simp only [Concrete.productEquiv_apply_apply]
  have hT' : (SectionsOver.sectionsEquiv G (K.obj (op ⦋n⦌)) F).toFun
      (ConcreteCategory.hom (SectionsOver.sectionsDegreeIso G K F n).hom z) =
      ConcreteCategory.hom (SectionsOver.evalOpProductIso G (K.obj (op ⦋n⦌)) F).hom z :=
    SectionsOver.sectionsEquiv_sectionsDegreeIso G K F n z
  have hU' : (SectionsOver.sectionsEquiv G (L.obj (op ⦋n⦌)) F).toFun
      (ConcreteCategory.hom (SectionsOver.sectionsDegreeIso G L F n).hom
        (ConcreteCategory.hom b z)) =
      ConcreteCategory.hom (SectionsOver.evalOpProductIso G (L.obj (op ⦋n⦌)) F).hom
        (ConcreteCategory.hom b z) :=
    SectionsOver.sectionsEquiv_sectionsDegreeIso G L F n _
  have hn := SectionsOver.sectionsEquiv_naturality G (ρ.app (op ⦋n⦌)) F
    (ConcreteCategory.hom (SectionsOver.sectionsDegreeIso G K F n).hom z) k
  change ConcreteCategory.hom
      (Pi.π (fun l ↦ F.obj.obj (op ((L.obj (op ⦋n⦌)).obj l).left)) k)
      ((SectionsOver.sectionsEquiv G (L.obj (op ⦋n⦌)) F).toFun
        (SectionsOver.freeAbelianSheafMap G (ρ.app (op ⦋n⦌)) ≫
          ConcreteCategory.hom (SectionsOver.sectionsDegreeIso G K F n).hom z)) =
    ConcreteCategory.hom
      (Pi.π (fun l ↦ F.obj.obj (op ((L.obj (op ⦋n⦌)).obj l).left)) k)
      ((SectionsOver.sectionsEquiv G (L.obj (op ⦋n⦌)) F).toFun
        (ConcreteCategory.hom (SectionsOver.sectionsDegreeIso G L F n).hom
          (ConcreteCategory.hom b z)))
  rw [hn, hT', hU']
  exact (hb z k).symm

variable {K} in
/-- `Hom(-, F)` of a morphism of chain complexes is contravariantly functorial. -/
private lemma homCochainMap_comp {A : Type u} [Category.{v} A] [Abelian A]
    {R S T : ChainComplex A ℕ} (f : R ⟶ S) (g : S ⟶ T) :
    homCochainMap g ≫ homCochainMap f = homCochainMap (f ≫ g) := by
  ext F : 2
  ext n x
  exact (Category.assoc (f.f n) (g.f n) x).symm

variable {K} in
/-- The complex of free abelian sheaves of a morphism of simplicial semi-representable
objects. -/
private abbrev freeHypercoverComplexMap
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]
    {L : SimplicialObject (FormalCoproduct.{w} (Over U))} (ρ : L ⟶ K) :
    freeHypercoverComplex J U L ⟶ freeHypercoverComplex J U K :=
  (_root_.CategoryTheory.SimplicialObject.freeAbelianSheafComplexFunctor
    J.toGrothendieck).map
    (((_root_.CategoryTheory.SimplicialObject.whiskering _ _).obj
      (associatedPresheafFunctorOver.{w} (X := U))).map ρ)

/-- **The augmentation is compatible with a morphism of hypercoverings.** -/
private lemma freeHypercoverComplexMap_comp_augmentation
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]
    {L : SimplicialObject (FormalCoproduct.{w} (Over U))} (ρ : L ⟶ K)
    (hK : IsHypercovering J K) (hL : IsHypercovering J L) :
    freeHypercoverComplexMap J U ρ ≫ freeHypercoverAugmentation J U K hK =
      freeHypercoverAugmentation J U L hL := by
  have hcomp : (freeHypercoverComplexMap J U ρ).f 0 ≫
      SimplicialObject.Augmented.freeAbelianSheafAugZero J.toGrothendieck
        (associatedAugmentedSimplicialPresheafOver.{w} K) =
      SimplicialObject.Augmented.freeAbelianSheafAugZero J.toGrothendieck
        (associatedAugmentedSimplicialPresheafOver.{w} L) := by
    change (Presheaf.freeAbelianSheaf J.toGrothendieck).map
          ((associatedPresheafFunctorOver.{w} (X := U)).map (ρ.app (op ⦋0⦌))) ≫
        (Presheaf.freeAbelianSheaf J.toGrothendieck).map
          (associatedPresheafAugmentationOver.{w}.app (K.obj (op ⦋0⦌))) = _
    rw [← Functor.map_comp]
    refine congrArg (fun m ↦ (Presheaf.freeAbelianSheaf J.toGrothendieck).map m) ?_
    have h := associatedPresheafAugmentationOver.{w}.naturality (ρ.app (op ⦋0⦌))
    simp only [Functor.const_obj_map] at h
    exact h
  apply (ChainComplex.toSingle₀Equiv (freeHypercoverComplex J U L) _).injective
  apply Subtype.ext
  change (freeHypercoverComplexMap J U ρ ≫ freeHypercoverAugmentation J U K hK).f 0 =
    (freeHypercoverAugmentation J U L hL).f 0
  rwa [HomologicalComplex.comp_f, freeHypercoverAugmentation_f_zero,
    freeHypercoverAugmentation_f_zero]

variable {K} in
/-- **Tag 01GX is natural in the simplicial semi-representable object.**  A Čech pullback map
`β` along `ρ : L ⟶ K` corresponds, under the identification of the complex of sections with
`Hom(s(ℤ_{F(K)}^♯), F)`, to `Hom(-, F)` of the induced map of complexes of free abelian
sheaves. -/
private lemma homFunctorIsoSections_naturality_map
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]
    {L : SimplicialObject (FormalCoproduct.{w} (Over U))} (ρ : L ⟶ K)
    (β : hypercoverCochainNatFunctor J U K ⟶ hypercoverCochainNatFunctor J U L)
    (hβ : ∀ (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (n : ℕ)
      (z : ((hypercoverCochainNatFunctor J U K).obj F).X n) (i : (L.obj (op ⦋n⦌)).I),
      ConcreteCategory.hom
          (Pi.π (fun i ↦ F.obj.obj (op ((L.obj (op ⦋n⦌)).obj i).left)) i)
          (ConcreteCategory.hom
            (SectionsOver.evalOpProductIso J.toGrothendieck (L.obj (op ⦋n⦌)) F).hom
            (ConcreteCategory.hom ((β.app F).f n) z)) =
        ConcreteCategory.hom
          (F.obj.map ((Over.forget U).map ((ρ.app (op ⦋n⦌)).φ i)).op)
          (ConcreteCategory.hom
            (Pi.π (fun l ↦ F.obj.obj (op ((K.obj (op ⦋n⦌)).obj l).left))
              ((ρ.app (op ⦋n⦌)).f i))
            (ConcreteCategory.hom
              (SectionsOver.evalOpProductIso J.toGrothendieck (K.obj (op ⦋n⦌)) F).hom z))) :
    (homFunctorIsoSections J U K).hom ≫ β =
      homCochainMap (freeHypercoverComplexMap J U ρ) ≫ (homFunctorIsoSections J U L).hom := by
  apply NatTrans.ext
  funext F
  apply HomologicalComplex.hom_ext
  intro n
  exact inv_square_of_hom_square
    (SectionsOver.sectionsDegreeIso J.toGrothendieck K F n)
    (SectionsOver.sectionsDegreeIso J.toGrothendieck L F n) _ _
    (sectionsDegreeIso_comm_map U K J.toGrothendieck ρ F n _ (hβ F n))

variable {K} in
/-- **The augmentation `Γ(X, F)[0] ⟶ s(F(K))` of Stacks 01GV and 01GW is natural in the
hypercovering**, in nonnegative degrees: pulling back along `ρ : L ⟶ K` turns the augmentation
at `K` into the augmentation at `L`. -/
private lemma sectionsComparisonNat_comp
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]
    {L : SimplicialObject (FormalCoproduct.{w} (Over U))} (ρ : L ⟶ K)
    (hK : IsHypercovering J K) (hL : IsHypercovering J L)
    (β : hypercoverCochainNatFunctor J U K ⟶ hypercoverCochainNatFunctor J U L)
    (hβ : ∀ (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (n : ℕ)
      (z : ((hypercoverCochainNatFunctor J U K).obj F).X n) (i : (L.obj (op ⦋n⦌)).I),
      ConcreteCategory.hom
          (Pi.π (fun i ↦ F.obj.obj (op ((L.obj (op ⦋n⦌)).obj i).left)) i)
          (ConcreteCategory.hom
            (SectionsOver.evalOpProductIso J.toGrothendieck (L.obj (op ⦋n⦌)) F).hom
            (ConcreteCategory.hom ((β.app F).f n) z)) =
        ConcreteCategory.hom
          (F.obj.map ((Over.forget U).map ((ρ.app (op ⦋n⦌)).φ i)).op)
          (ConcreteCategory.hom
            (Pi.π (fun l ↦ F.obj.obj (op ((K.obj (op ⦋n⦌)).obj l).left))
              ((ρ.app (op ⦋n⦌)).f i))
            (ConcreteCategory.hom
              (SectionsOver.evalOpProductIso J.toGrothendieck (K.obj (op ⦋n⦌)) F).hom z))) :
    sectionsComparisonNat J U K hK ≫ β = sectionsComparisonNat J U L hL := by
  have hsplit : ∀ (M : SimplicialObject (FormalCoproduct.{w} (Over U)))
      (hM : IsHypercovering J M),
      sectionsComparisonNat J U M hM =
        Functor.whiskerRight (freeYonedaSectionsIso J U).inv (CochainComplex.single₀ _) ≫
          homSingleComparison _ ≫
            (homCochainMap (freeHypercoverAugmentation J U M hM) ≫
              (homFunctorIsoSections J U M).hom) := fun _ _ ↦ rfl
  have step : (homCochainMap (freeHypercoverAugmentation J U K hK) ≫
      (homFunctorIsoSections J U K).hom) ≫ β =
      homCochainMap (freeHypercoverAugmentation J U L hL) ≫
        (homFunctorIsoSections J U L).hom := by
    rw [Category.assoc, homFunctorIsoSections_naturality_map J U ρ β hβ, ← Category.assoc,
      homCochainMap_comp, freeHypercoverComplexMap_comp_augmentation J U K ρ hK hL]
  rw [hsplit K hK, hsplit L hL, Category.assoc, Category.assoc, step]

variable {K} in
/-- **The augmentation `Γ(X, F)[0] ⟶ s(F(K))` of Stacks 01GV and 01GW is natural in the
hypercovering.**  For a morphism `ρ : L ⟶ K` of simplicial semi-representable objects over `U`
and any Čech pullback map `β` along it -- a map of the hypercover cochain functors whose
components are the restrictions along the structure morphisms of `ρ`, which is what `hβ` says --
the augmentation at `K` followed by `β` is the augmentation at `L`. -/
public lemma sectionsComparisonInt_comp
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]
    {L : SimplicialObject (FormalCoproduct.{w} (Over U))} (ρ : L ⟶ K)
    (hK : IsHypercovering J K) (hL : IsHypercovering J L)
    (β : hypercoverCochainNatFunctor J U K ⟶ hypercoverCochainNatFunctor J U L)
    (hβ : ∀ (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (n : ℕ)
      (z : ((hypercoverCochainNatFunctor J U K).obj F).X n) (i : (L.obj (op ⦋n⦌)).I),
      ConcreteCategory.hom
          (Pi.π (fun i ↦ F.obj.obj (op ((L.obj (op ⦋n⦌)).obj i).left)) i)
          (ConcreteCategory.hom
            (SectionsOver.evalOpProductIso J.toGrothendieck (L.obj (op ⦋n⦌)) F).hom
            (ConcreteCategory.hom ((β.app F).f n) z)) =
        ConcreteCategory.hom
          (F.obj.map ((Over.forget U).map ((ρ.app (op ⦋n⦌)).φ i)).op)
          (ConcreteCategory.hom
            (Pi.π (fun l ↦ F.obj.obj (op ((K.obj (op ⦋n⦌)).obj l).left))
              ((ρ.app (op ⦋n⦌)).f i))
            (ConcreteCategory.hom
              (SectionsOver.evalOpProductIso J.toGrothendieck (K.obj (op ⦋n⦌)) F).hom z))) :
    sectionsComparisonInt J U K hK ≫
        Functor.whiskerRight β
          (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max u v w}) =
      sectionsComparisonInt J U L hL := by
  have key : Functor.whiskerLeft (sheafSectionsFunctor J U) singleExtendIso.inv ≫
      Functor.whiskerRight (sectionsComparisonNat J U K hK)
          (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max u v w}) ≫
        Functor.whiskerRight β
          (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max u v w}) =
      Functor.whiskerLeft (sheafSectionsFunctor J U) singleExtendIso.inv ≫
        Functor.whiskerRight (sectionsComparisonNat J U L hL)
          (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max u v w}) := by
    rw [← Functor.whiskerRight_comp, sectionsComparisonNat_comp J U ρ hK hL β hβ]
  exact (Category.assoc _ _ _).trans key

end HypercoverNaturality

end Stacks.CategoryTheory.Hypercovering

end
