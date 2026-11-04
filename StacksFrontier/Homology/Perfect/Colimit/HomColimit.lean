module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Homology.KFlat.BaseChange
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.Perfect.Colimit.ModuleDescent
public import StacksFrontier.Homology.Perfect.Colimit.ComplexDescent
public import StacksFrontier.Homology.Perfect.Colimit.HomotopyHomDescent
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.RingTheory.Finiteness.Projective

/-!
# Perfect complexes over filtered colimits of rings

Let `R : I ⥤ CommRingCat` be a filtered system of commutative rings with colimit `c.pt`. Every
perfect object of the derived category of `c.pt`-modules is, up to isomorphism, the derived
extension of scalars of a perfect object living over one of the rings `R.obj i`; that is, perfect
complexes descend to a finite stage. Moreover, if `K₀` and `L₀` are objects over a fixed stage
`i₀` and `K₀` is perfect, then the morphisms between their base changes to `c.pt` are the filtered
colimit, over the stages `j` above `i₀`, of the morphisms between their base changes to `R.obj j`;
that is, a morphism over the colimit ring is already realized at some later stage, and two
morphisms realized at a stage become equal at a later one.

## Main results

* `StacksDraft.Perfect.perfectComplexes_filteredColimit` ([stacks 0BC7]): descent of perfect
  complexes to a finite stage, together with the filtered-colimit description of the morphisms out
  of a perfect complex, for the canonical derived extension of scalars of [stacks 064H].
* `StacksDraft.Perfect.perfectComplexes_filteredColimit_of_datum`: the same, for an arbitrary
  total derived extension-of-scalars datum.

## Implementation notes

The rings and the module carriers share one universe `uR`, while the universe `uI` of the filtered
index category is arbitrary. The hypothesis `PreservesColimit R (forget CommRingCat)` makes the
ring colimit a colimit of underlying sets as well, which is what the source proof uses; Mathlib's
preservation of filtered colimits, with universe shrinking where necessary, supplies it whenever
the index universe is contained in the ring universe. For larger index universes `IsColimit c` in
`CommRingCat` alone does not give this.

The Hom-colimit half of the statement quantifies existentially over a composition isomorphism
`comp` for derived extension of scalars, whose transition maps it then identifies; the
accompanying comparison equation pins `comp` down by identifying it with the ordinary
scalar-extension tower `extensionOfScalarsComplexComp` on complexes. Tag 0BC7 asserts no further
coherence properties of derived extension of scalars, so none are recorded here.

## References

* [Stacks Project, Tag 0BC7](https://stacks.math.columbia.edu/tag/0BC7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars

open scoped TensorProduct

open scoped Matrix

universe uI uR uM uA

namespace StacksDraft.Perfect

attribute [local instance] HasDerivedCategory.standard

open CochainComplex.HomComplex

/-- A commutative algebra, presented as a ring under the base, has an underlying module. -/
private def underRingModule (A : CommRingCat.{uR}) : Under A ⥤ ModuleCat.{uR} A where
  obj B := ModuleCat.of A B
  map f := ModuleCat.ofHom (CommRingCat.toAlgHom f).toLinearMap
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Forgetting the module structure recovers the underlying set of an algebra. -/
private theorem underRingModule_comp_forget (A : CommRingCat.{uR}) :
    underRingModule A ⋙ forget (ModuleCat A) =
      Under.forget A ⋙ forget CommRingCat := rfl

/-- The scalar rings over a fixed stage form a filtered colimit of their underlying sets. -/
private def scalarModules_isColimit
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{uR}) [PreservesColimit R (forget CommRingCat)]
    (c : Cocone R) (hc : IsColimit c) (i : I) :
    IsColimit ((underRingModule (R.obj i) ⋙ forget _).mapCocone (c.underPost i)) :=
  (Functor.Final.isColimitWhiskerEquiv (Under.forget i)
    ((forget CommRingCat).mapCocone c)).symm
      (isColimitOfPreserves (forget CommRingCat) hc)

/-- Perfect objects over the colimit ring descend to a finite stage, at one universe level. -/
private theorem perfect_descends_filteredColimit (E : DerivedExtendScalars.{uR})
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{uR}) [PreservesColimit R (forget CommRingCat.{uR})]
    (c : Cocone R) (hc : IsColimit c) :
    ∀ (K : DerivedCategory (ModuleCat.{uR} c.pt)), IsPerfect K →
      ∃ (i : I) (Kᵢ : DerivedCategory (ModuleCat.{uR} (R.obj i))),
        IsPerfect Kᵢ ∧ Nonempty (K ≅
          (E (c.ι.app i).hom).functor.obj Kᵢ) :=
  fun K hK => perfect_object_descends.{uI, uR} E R c hc K hK

/-- The composition isomorphism of derived extension of scalars, characterized by its
compatibility with the ordinary scalar tower on complexes. -/
private noncomputable def derivedExtensionScalarsComp (E : DerivedExtendScalars.{uR})
    (hE : ComputesKFlat E)
    {A B C : Type uR} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    (E f).functor ⋙
        (E g).functor ≅
      (E (g.comp f)).functor :=
  Classical.choose (derivedExtensionScalarsComp_exists E hE f g)

/-- The composition isomorphism is compatible with the comparison maps. -/
private theorem derivedExtensionScalarsComp_comparison (E : DerivedExtendScalars.{uR})
    (hE : ComputesKFlat E)
    {A B C : Type uR} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (P : CochainComplex (ModuleCat.{uR} A) ℤ) :
    (E g).functor.map
          ((E f).comparison.app P) ≫
        (E g).comparison.app
          (((ModuleCat.extendScalars.{uR, uR, uR} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        (extensionOfScalarsComplexComp.{uR} f g).inv.app P =
      (derivedExtensionScalarsComp E hE f g).hom.app (DerivedCategory.Q.obj P) ≫
        (E (g.comp f)).comparison.app P :=
  Classical.choose_spec (derivedExtensionScalarsComp_exists E hE f g) P

section HomColimit

open MonoidalCategory

set_option backward.isDefEq.respectTransparency false
/-- Tensor products are unchanged by lifting both module carriers. -/
private def tensorUliftEquiv {A : Type uR} [CommRing A]
    (M N : ModuleCat.{uR} A) :
    ((ModuleCat.uliftFunctor.{uI} A).obj M ⊗[A]
      (ModuleCat.uliftFunctor.{uI} A).obj N) ≃ₗ[A] (M ⊗[A] N) :=
  TensorProduct.congr ULift.moduleEquiv ULift.moduleEquiv

/-- The tensor lift equivalence is natural in its first argument. -/
private lemma tensorUliftEquiv_natural {A : Type uR} [CommRing A]
    {M N : ModuleCat.{uR} A} (f : M ⟶ N) (T : ModuleCat.{uR} A)
    (z : (ModuleCat.uliftFunctor.{uI} A).obj M ⊗[A]
      (ModuleCat.uliftFunctor.{uI} A).obj T) :
    tensorUliftEquiv N T
      (((ModuleCat.uliftFunctor.{uI} A).map f).hom.rTensor
        ((ModuleCat.uliftFunctor.{uI} A).obj T) z) =
      f.hom.rTensor T (tensorUliftEquiv M T z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

/-- In the enlarged universe the forgetful functor preserves the given filtered colimit. -/
private theorem lifted_forget_preservesColimit {A : Type uR} [CommRing A]
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (F : I ⥤ ModuleCat.{max uI uR} A) : PreservesColimit F (forget _) :=
  preservesColimit_of_preserves_colimit_cocone
    (ModuleCat.FilteredColimits.colimitCoconeIsColimit F)
    (Types.TypeMax.colimitCoconeIsColimit (F ⋙ forget _))

/-- Right tensoring by a fixed module, for modules in a universe that need not agree with the
ring's. Mathlib's monoidal structure on `ModuleCat` is available only when the two universes
agree, and only the functor and its left adjointness are needed below, so the functor is built
directly from `LinearMap.rTensor`. -/
private def rTensorFunctor {A : Type uR} [CommRing A] (M : ModuleCat.{max uI uR} A) :
    ModuleCat.{max uI uR} A ⥤ ModuleCat.{max uI uR} A where
  obj N := ModuleCat.of A (N ⊗[A] M)
  map f := ModuleCat.ofHom (f.hom.rTensor M)
  map_id N := by
    ext : 1
    exact TensorProduct.ext' fun _ _ => rfl
  map_comp f g := by
    ext : 1
    exact TensorProduct.ext' fun _ _ => rfl

/-- Right tensoring is a left adjoint, the right adjoint being the internal hom out of the
tensor factor; this is the tensor-hom adjunction, and it needs no agreement of universes. -/
private def rTensorAdj {A : Type uR} [CommRing A] (M : ModuleCat.{max uI uR} A) :
    rTensorFunctor M ⊣ (linearCoyoneda A (ModuleCat.{max uI uR} A)).obj (Opposite.op M) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun N P =>
        { toFun := fun f => ModuleCat.ofHom₂ (TensorProduct.curry f.hom)
          invFun := fun g => ModuleCat.ofHom (TensorProduct.lift g.hom₂)
          left_inv := fun f => by
            ext : 1
            exact TensorProduct.ext' fun _ _ => rfl
          right_inv := fun g => by
            ext n m
            rfl }
      homEquiv_naturality_left_symm := by
        intros
        ext : 1
        exact TensorProduct.ext' fun _ _ => rfl }

private instance rTensorFunctor_isLeftAdjoint {A : Type uR} [CommRing A]
    (M : ModuleCat.{max uI uR} A) : (rTensorFunctor M).IsLeftAdjoint :=
  ⟨_, ⟨rTensorAdj M⟩⟩

/-- Tensoring preserves filtered colimits computed on sets, with no restriction on the index
universe. -/
private def tensorRight_underlying_isColimit
    {A : Type uR} [CommRing A]
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (F : I ⥤ ModuleCat.{uR} A) (c : Cocone F)
    (hc : IsColimit ((forget _).mapCocone c)) (M : ModuleCat.{uR} A) :
    IsColimit (((tensorRight M) ⋙ forget _).mapCocone c) := by
  let U := ModuleCat.uliftFunctor.{uI} A
  have hU : IsColimit ((forget _).mapCocone (U.mapCocone c)) :=
    isColimitOfPreserves uliftFunctor.{uI} hc
  letI : PreservesColimit (F ⋙ U) (forget _) := lifted_forget_preservesColimit _
  letI : HasColimit (F ⋙ U) := ⟨⟨_, ModuleCat.FilteredColimits.colimitCoconeIsColimit _⟩⟩
  letI : ReflectsColimit (F ⋙ U) (forget _) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  have hUM : IsColimit (U.mapCocone c) := isColimitOfReflects (forget _) hU
  have hT := isColimitOfPreserves (rTensorFunctor (U.obj M)) hUM
  letI : PreservesColimit ((F ⋙ U) ⋙ rTensorFunctor (U.obj M)) (forget _) :=
    lifted_forget_preservesColimit _
  have hTf := isColimitOfPreserves (forget _) hT
  apply Nonempty.some
  apply (Types.isColimit_iff_coconeTypesIsColimit _).2
  have h := (Types.isColimit_iff_coconeTypesIsColimit _).1 ⟨hTf⟩
  have h' := h.precompose (G := F ⋙ tensorRight M ⋙ forget _)
    (fun j => (tensorUliftEquiv (F.obj j) M).symm.toEquiv) (by
      intro j k f
      funext z
      apply (tensorUliftEquiv (F.obj k) M).injective
      change tensorUliftEquiv (F.obj k) M
        ((tensorUliftEquiv (F.obj k) M).symm ((F.map f).hom.rTensor M z)) =
        tensorUliftEquiv (F.obj k) M
          ((U.map (F.map f)).hom.rTensor (U.obj M)
            ((tensorUliftEquiv (F.obj j) M).symm z))
      rw [tensorUliftEquiv_natural, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply])
  exact h'.of_equiv (tensorUliftEquiv c.pt M).toEquiv (by
    intro j z
    change (c.ι.app j).hom.rTensor M z = tensorUliftEquiv c.pt M
      ((U.map (c.ι.app j)).hom.rTensor (U.obj M)
        ((tensorUliftEquiv (F.obj j) M).symm z))
    have hn := (tensorUliftEquiv_natural (N := c.pt) (c.ι.app j) M
      ((tensorUliftEquiv (F.obj j) M).symm z)).symm
    rw [LinearEquiv.apply_symm_apply] at hn
    exact hn)

/-- Tensor a fixed complex degreewise with a varying module. -/
private def moduleTensorComplex {A : Type uR} [CommRing A]
    (L : CochainComplex (ModuleCat.{uR} A) ℤ) :
    ModuleCat.{uR} A ⥤ CochainComplex (ModuleCat.{uR} A) ℤ where
  obj M := ((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj L
  map f :=
    { f := fun q => f ▷ L.X q
      comm' := fun i j _ => (whisker_exchange f (L.d i j)).symm }
  map_id M := by ext q; simp
  map_comp f g := by ext q; simp

/-- The strict diagram of scalar extensions, restricted to the base ring. -/
private def scalarExtensionDiagram {A : CommRingCat.{uR}}
    (L : CochainComplex (ModuleCat.{uR} A) ℤ) :
    Under A ⥤ CochainComplex (ModuleCat.{uR} A) ℤ :=
  underRingModule A ⋙ moduleTensorComplex L

/-- Degreewise tensoring computes restricted extension of scalars. -/
private def scalarExtensionRestrictionIso {A : CommRingCat.{uR}}
    (L : CochainComplex (ModuleCat.{uR} A) ℤ) (B : Under A) :
    (scalarExtensionDiagram L).obj B ≅
      ((ModuleCat.restrictScalars B.hom.hom).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars B.hom.hom).mapHomologicalComplex (.up ℤ)).obj L) :=
  HomologicalComplex.Hom.isoOfComponents (fun q =>
    (LinearEquiv.refl A (B ⊗[A] L.X q)).toModuleIso) (by intros; rfl)

open scoped ChangeOfRings

/-- The degreewise adjunction on cochain complexes induced by an adjunction `F ⊣ G` of additive
functors between abelian categories descends to the homotopy categories: the homotopy category is
the localization of the category of complexes at the homotopy equivalences, and the degreewise
functors commute with the localization functors. -/
private noncomputable def mapHomotopyCategoryAdj
    {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive] (adj : F ⊣ G) :
    F.mapHomotopyCategory (ComplexShape.up ℤ) ⊣
      G.mapHomotopyCategory (ComplexShape.up ℤ) :=
  letI : CatCommSq (F.mapHomologicalComplex (ComplexShape.up ℤ))
      (HomotopyCategory.quotient A (ComplexShape.up ℤ))
      (HomotopyCategory.quotient B (ComplexShape.up ℤ))
      (F.mapHomotopyCategory (ComplexShape.up ℤ)) :=
    CatCommSq.mk (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).symm
  letI : CatCommSq (G.mapHomologicalComplex (ComplexShape.up ℤ))
      (HomotopyCategory.quotient B (ComplexShape.up ℤ))
      (HomotopyCategory.quotient A (ComplexShape.up ℤ))
      (G.mapHomotopyCategory (ComplexShape.up ℤ)) :=
    CatCommSq.mk (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).symm
  Adjunction.localization (adj.mapHomologicalComplex (ComplexShape.up ℤ))
    (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    (HomotopyCategory.quotient B (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
    (F.mapHomotopyCategory (ComplexShape.up ℤ))
    (G.mapHomotopyCategory (ComplexShape.up ℤ))

/-- The homotopy adjunction agrees with the degreewise adjunction on representatives. -/
private lemma homotopyAdj_symm_map
    {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive] (adj : F ⊣ G)
    (P : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (f : P ⟶ (G.mapHomologicalComplex (.up ℤ)).obj L) :
    ((mapHomotopyCategoryAdj F G adj).homEquiv
      ((HomotopyCategory.quotient _ _).obj P)
      ((HomotopyCategory.quotient _ _).obj L)).symm
      ((HomotopyCategory.quotient _ _).map f) =
    (HomotopyCategory.quotient _ _).map
      (((adj.mapHomologicalComplex (.up ℤ)).homEquiv P L).symm f) := by
  rw [Adjunction.homEquiv_symm_apply]
  dsimp only [mapHomotopyCategoryAdj]
  rw [Adjunction.localization_counit_app]
  simp only [Functor.mapHomotopyCategoryFactors, CategoryTheory.Quotient.lift.isLift,
    Iso.symm_inv, NatIso.ofComponents_hom_app, Iso.refl_hom,
    Adjunction.homEquiv_symm_apply, Functor.map_comp, Functor.mapHomotopyCategory_map]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]

/-- Extension of scalars is additive because it is a left adjoint. -/
private theorem scalarExtend_additive {A B : Type uR} [CommRing A] [CommRing B]
    (f : A →+* B) : (ModuleCat.extendScalars.{uR, uR, uR} f).Additive :=
  CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _ (by
    show PreservesFiniteColimits (ModuleCat.extendScalars.{uR, uR, uR} f)
    infer_instance)
attribute [local instance] scalarExtend_additive

/-- Scalar adjunction identifies the homotopy Hom groups. -/
private def homotopyScalarEquiv {A : CommRingCat.{uR}}
    (P L : CochainComplex (ModuleCat.{uR} A) ℤ) (B : Under A) :
    ((HomotopyCategory.quotient _ _).obj P ⟶
      (HomotopyCategory.quotient _ _).obj ((scalarExtensionDiagram L).obj B)) ≃
    ((HomotopyCategory.quotient _ _).obj
      (((ModuleCat.extendScalars B.hom.hom).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      (HomotopyCategory.quotient _ _).obj
      (((ModuleCat.extendScalars B.hom.hom).mapHomologicalComplex (.up ℤ)).obj L)) :=
  ((Iso.refl _).homCongr ((HomotopyCategory.quotient _ _).mapIso
    (scalarExtensionRestrictionIso L B))).trans
    ((mapHomotopyCategoryAdj
      (ModuleCat.extendScalars B.hom.hom) (ModuleCat.restrictScalars B.hom.hom)
      (ModuleCat.extendRestrictScalarsAdj B.hom.hom)).homEquiv _ _).symm

/-- The adjoint chain map of a map into restricted scalar extension. -/
private def scalarAdjoint {A : CommRingCat.{uR}}
    (P L : CochainComplex (ModuleCat.{uR} A) ℤ) (B : Under A)
    (x : P ⟶ (scalarExtensionDiagram L).obj B) :
    ((ModuleCat.extendScalars B.hom.hom).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((ModuleCat.extendScalars B.hom.hom).mapHomologicalComplex (.up ℤ)).obj L :=
  (((ModuleCat.extendRestrictScalarsAdj B.hom.hom).mapHomologicalComplex
    (.up ℤ)).homEquiv _ _).symm
      (x ≫ (scalarExtensionRestrictionIso L B).hom)

/-- The Hom equivalence sends a chain map to its scalar adjoint. -/
private lemma homotopyScalarEquiv_map {A : CommRingCat.{uR}}
    (P L : CochainComplex (ModuleCat.{uR} A) ℤ) (B : Under A)
    (x : P ⟶ (scalarExtensionDiagram L).obj B) :
    homotopyScalarEquiv P L B ((HomotopyCategory.quotient _ _).map x) =
      (HomotopyCategory.quotient _ _).map (scalarAdjoint P L B x) := by
  simp only [homotopyScalarEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_inv, Category.id_comp, Functor.mapIso_hom]
  rw [← Functor.map_comp]
  exact homotopyAdj_symm_map _ _ (ModuleCat.extendRestrictScalarsAdj B.hom.hom)
    P _ (x ≫ (scalarExtensionRestrictionIso L B).hom)

/-- The scalar adjoint is evaluated on the canonical generators. -/
private lemma scalarAdjoint_one_tmul {A : CommRingCat.{uR}}
    (P L : CochainComplex (ModuleCat.{uR} A) ℤ) (B : Under A)
    (x : P ⟶ (scalarExtensionDiagram L).obj B) (q : ℤ) (p : P.X q) :
    (scalarAdjoint P L B x).f q ((1 : B) ⊗ₜ p) = (x.f q).hom p := by
  dsimp only [scalarAdjoint]
  rw [Adjunction.homEquiv_symm_apply]
  show (((ModuleCat.extendScalars B.hom.hom).map
    ((x ≫ (scalarExtensionRestrictionIso L B).hom).f q) ≫
      (ModuleCat.extendRestrictScalarsAdj B.hom.hom).counit.app _).hom
      ((1 : B) ⊗ₜ p)) = _
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.ExtendScalars.map_tmul]
  exact ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul
    B.hom.hom ((ModuleCat.extendScalars B.hom.hom).obj (L.X q)) ((x.f q).hom p)

/-- The scalar tower isomorphism transported along equality of ring maps. -/
private def scalarTower {A B C : Type uR} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) {k : A →+* C} (h : g.comp f = k) :
    (ModuleCat.extendScalars k).mapHomologicalComplex (.up ℤ) ≅
      (ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ) ⋙
        (ModuleCat.extendScalars g).mapHomologicalComplex (.up ℤ) := by
  subst h
  exact NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp f g) (.up ℤ)

/-- The scalar tower carries canonical generators to iterated generators. -/
private lemma scalarTower_one_tmul {A B C : Type uR} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) {k : A →+* C} (h : g.comp f = k)
    (L : CochainComplex (ModuleCat.{uR} A) ℤ) (q : ℤ) (x : L.X q) :
    ((scalarTower f g h).hom.app L).f q ((1 : C) ⊗ₜ[A,k] x) =
      (1 : C) ⊗ₜ[B,g] ((1 : B) ⊗ₜ[A,f] x) := by
  subst h
  exact ModuleCat.extendScalarsComp_hom_app_one_tmul f g (L.X q) x

/-- The scalar tower intertwines the algebra transition with the scalar unit. -/
private lemma scalarTower_transfer {A : CommRingCat.{uR}}
    (L : CochainComplex (ModuleCat.{uR} A) ℤ) {B C : Under A} (w : B ⟶ C)
    (q : ℤ) (x : (ModuleCat.extendScalars B.hom.hom).obj (L.X q)) :
    ((scalarTower B.hom.hom w.right.hom
      (congrArg CommRingCat.Hom.hom w.w)).hom.app L).f q
      (((scalarExtensionDiagram L).map w).f q x) =
      (1 : C.right) ⊗ₜ[B.right,w.right.hom] x := by
  let : Algebra A B.right := B.hom.hom.toAlgebra
  let : Algebra B.right C.right := w.right.hom.toAlgebra
  let : Algebra A C.right := C.hom.hom.toAlgebra
  induction x using TensorProduct.induction_on with
  | zero =>
    show (((scalarTower B.hom.hom w.right.hom
      (congrArg CommRingCat.Hom.hom w.w)).hom.app L).f q).hom
      ((((scalarExtensionDiagram L).map w).f q).hom 0) = _
    simp only [map_zero, TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
  | tmul b l =>
    have ht : ((scalarExtensionDiagram L).map w).f q (b ⊗ₜ l) =
        w.right.hom b • ((1 : C.right) ⊗ₜ[↑A,C.hom.hom] l) := by
      show w.right.hom b ⊗ₜ[↑A] l = _
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [ht, map_smul, scalarTower_one_tmul]
    show w.right.hom b • ((1 : C.right) ⊗ₜ[B.right,w.right.hom]
      ((1 : B.right) ⊗ₜ[↑A,B.hom.hom] l)) = _
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have he := (TensorProduct.tmul_smul (R := B.right) (show B.right from b) (1 : C.right)
      ((1 : B.right) ⊗ₜ[↑A,B.hom.hom] l)).symm
    simp only [TensorProduct.smul_tmul', Algebra.smul_def,
      RingHom.algebraMap_toAlgebra, mul_one, RingHom.id_apply] at he
    exact he

/-- Taking scalar adjoints commutes with a further extension of scalars. -/
private lemma scalarAdjoint_naturality {A : CommRingCat.{uR}}
    (P L : CochainComplex (ModuleCat.{uR} A) ℤ) {B C : Under A} (w : B ⟶ C)
    (x : P ⟶ (scalarExtensionDiagram L).obj B) :
    (scalarTower B.hom.hom w.right.hom
      (congrArg CommRingCat.Hom.hom w.w)).hom.app P ≫
      ((ModuleCat.extendScalars w.right.hom).mapHomologicalComplex (.up ℤ)).map
        (scalarAdjoint P L B x) =
    scalarAdjoint P L C (x ≫ (scalarExtensionDiagram L).map w) ≫
      (scalarTower B.hom.hom w.right.hom
        (congrArg CommRingCat.Hom.hom w.w)).hom.app L := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.ExtendScalars.hom_ext
  intro p
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
  erw [scalarTower_one_tmul B.hom.hom w.right.hom
    (congrArg CommRingCat.Hom.hom w.w) P q p]
  show (ModuleCat.extendScalars w.right.hom).map ((scalarAdjoint P L B x).f q)
      ((1 : C.right) ⊗ₜ[B.right,w.right.hom] ((1 : B.right) ⊗ₜ p)) = _
  erw [ModuleCat.ExtendScalars.map_tmul, scalarAdjoint_one_tmul,
    scalarAdjoint_one_tmul]
  exact (scalarTower_transfer L w q ((x.f q).hom p)).symm



/-- Localization identifies homotopy Hom from bounded projectives with derived Hom. -/
private def projectiveQHomEquiv {A : Type uR} [CommRing A]
    (P L : CochainComplex (ModuleCat.{uR} A) ℤ) (b : ℤ)
    [P.IsStrictlyLE b] [∀ q, Module.Projective A (P.X q)] :
    ((HomotopyCategory.quotient _ _).obj P ⟶
      (HomotopyCategory.quotient _ _).obj L) ≃
      (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj L) :=
  (Equiv.ofBijective DerivedCategory.Qh.map
    (bounded_projective_Qh_map_bijective P L b inferInstance inferInstance)).trans
    (((DerivedCategory.quotientCompQhIso (ModuleCat.{uR} A)).app P).homCongr
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{uR} A)).app L))

/-- The localization equivalence takes a chain map to its localized map. -/
private lemma projectiveQHomEquiv_map {A : Type uR} [CommRing A]
    (P L : CochainComplex (ModuleCat.{uR} A) ℤ) (b : ℤ)
    [P.IsStrictlyLE b] [∀ q, Module.Projective A (P.X q)] (x : P ⟶ L) :
    projectiveQHomEquiv P L b ((HomotopyCategory.quotient _ _).map x) =
      DerivedCategory.Q.map x := by
  show (DerivedCategory.quotientCompQhIso (ModuleCat.{uR} A)).inv.app P ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map x) ≫
      (DerivedCategory.quotientCompQhIso (ModuleCat.{uR} A)).hom.app L = _
  rw [DerivedCategory.quotientCompQhIso_hom_naturality, Iso.inv_hom_id_app_assoc]

/-- Derived Hom after scalar extension is computed by the strict homotopy Hom diagram. -/
private def derivedScalarHomEquiv {A : CommRingCat.{uR}} (E : DerivedExtendScalars.{uR})
    (hE : ComputesKFlat E)
    (P L : CochainComplex (ModuleCat.{uR} A) ℤ) (b : ℤ)
    [P.IsStrictlyLE b] [∀ q, Module.Projective A (P.X q)] (hL : L.KFlat)
    (B : Under A) :
    ((HomotopyCategory.quotient _ _).obj P ⟶
      (HomotopyCategory.quotient _ _).obj ((scalarExtensionDiagram L).obj B)) ≃
    ((E B.hom.hom).functor.obj
        (DerivedCategory.Q.obj P) ⟶
      (E B.hom.hom).functor.obj
        (DerivedCategory.Q.obj L)) := by
  let D := E B.hom.hom
  let F := (ModuleCat.extendScalars B.hom.hom).mapHomologicalComplex (.up ℤ)
  have : IsIso (D.comparison.app P) := D.comparison_isIso_of_projective P b
  have : IsIso (D.comparison.app L) := hE B.hom.hom L hL
  have : CochainComplex.IsStrictlyLE (F.obj P) b := inferInstance
  have : ∀ q, Module.Projective B.right ((F.obj P).X q) := by
    intro q
    let : Algebra A B.right := B.hom.hom.toAlgebra
    change Module.Projective B.right (B.right ⊗[A] P.X q)
    infer_instance
  exact (homotopyScalarEquiv P L B).trans
    ((projectiveQHomEquiv (F.obj P) (F.obj L) b).trans
      ((asIso (D.comparison.app P)).symm.homCongr
        (asIso (D.comparison.app L)).symm))

/-- The derived Hom comparison has the canonical formula on chain maps. -/
private lemma derivedScalarHomEquiv_map {A : CommRingCat.{uR}} (E : DerivedExtendScalars.{uR})
    (hE : ComputesKFlat E)
    (P L : CochainComplex (ModuleCat.{uR} A) ℤ) (b : ℤ)
    [P.IsStrictlyLE b] [∀ q, Module.Projective A (P.X q)] (hL : L.KFlat)
    (B : Under A) (x : P ⟶ (scalarExtensionDiagram L).obj B) :
    derivedScalarHomEquiv E hE P L b hL B ((HomotopyCategory.quotient _ _).map x) ≫
      (E B.hom.hom).comparison.app L =
    (E B.hom.hom).comparison.app P ≫
      DerivedCategory.Q.map (scalarAdjoint P L B x) := by
  let D := E B.hom.hom
  have : IsIso (D.comparison.app P) := D.comparison_isIso_of_projective P b
  have : IsIso (D.comparison.app L) := hE B.hom.hom L hL
  simp only [derivedScalarHomEquiv, Equiv.trans_apply, homotopyScalarEquiv_map,
    projectiveQHomEquiv_map]
  show (D.comparison.app P ≫ DerivedCategory.Q.map (scalarAdjoint P L B x) ≫
    inv (D.comparison.app L)) ≫ D.comparison.app L = _
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rfl

/-- The Hom comparison is natural for any scalar composition isomorphism compatible with the
canonical comparison. -/
private lemma derivedScalarHomEquiv_naturality_of_comparison {A : CommRingCat.{uR}}
    (E : DerivedExtendScalars.{uR}) (hE : ComputesKFlat E)
    (P L : CochainComplex (ModuleCat.{uR} A) ℤ) (b : ℤ)
    [P.IsStrictlyLE b] [∀ q, Module.Projective A (P.X q)] (hL : L.KFlat)
    {B C : Under A} (w : B ⟶ C)
    (τ : (E B.hom.hom).functor ⋙
      (E w.right.hom).functor ≅
      (E C.hom.hom).functor)
    (hτ : ∀ X : CochainComplex (ModuleCat.{uR} A) ℤ,
      τ.hom.app (DerivedCategory.Q.obj X) ≫
        (E C.hom.hom).comparison.app X ≫
          DerivedCategory.Q.map ((scalarTower B.hom.hom w.right.hom
            (congrArg CommRingCat.Hom.hom w.w)).hom.app X) =
      (E w.right.hom).functor.map
        ((E B.hom.hom).comparison.app X) ≫
        (E w.right.hom).comparison.app
          (((ModuleCat.extendScalars B.hom.hom).mapHomologicalComplex (.up ℤ)).obj X))
    (x : (HomotopyCategory.quotient _ _).obj P ⟶
      (HomotopyCategory.quotient _ _).obj ((scalarExtensionDiagram L).obj B)) :
    derivedScalarHomEquiv E hE P L b hL C
      (x ≫ (HomotopyCategory.quotient _ _).map ((scalarExtensionDiagram L).map w)) =
    τ.inv.app (DerivedCategory.Q.obj P) ≫
      (E w.right.hom).functor.map
        (derivedScalarHomEquiv E hE P L b hL B x) ≫
      τ.hom.app (DerivedCategory.Q.obj L) := by
  let D := E w.right.hom
  let DB := E B.hom.hom
  let DC := E C.hom.hom
  let T := scalarTower B.hom.hom w.right.hom (congrArg CommRingCat.Hom.hom w.w)
  have : IsIso (DC.comparison.app L) := hE C.hom.hom L hL
  obtain ⟨x, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective x
  rw [← (HomotopyCategory.quotient _ _).map_comp]
  have ht : DerivedCategory.Q.map (scalarAdjoint P L C (x ≫ (scalarExtensionDiagram L).map w)) ≫
      DerivedCategory.Q.map (T.hom.app L) =
      DerivedCategory.Q.map (T.hom.app P) ≫
        DerivedCategory.Q.map
          (((ModuleCat.extendScalars w.right.hom).mapHomologicalComplex (.up ℤ)).map
            (scalarAdjoint P L B x)) := by
    rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
    exact congrArg DerivedCategory.Q.map (scalarAdjoint_naturality P L w x).symm
  apply (cancel_mono (DC.comparison.app L ≫ DerivedCategory.Q.map (T.hom.app L))).1
  apply (cancel_epi (τ.hom.app (DerivedCategory.Q.obj P))).1
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% derivedScalarHomEquiv_map E hE P L b hL C
    (x ≫ (scalarExtensionDiagram L).map w)]
  rw [ht, reassoc_of% hτ P, hτ L]
  rw [← D.functor.map_comp_assoc,
    derivedScalarHomEquiv_map E hE P L b hL B x, D.functor.map_comp]
  simp only [Category.assoc]
  congr 1
  exact (D.comparison.naturality (scalarAdjoint P L B x)).symm

/-- The derived composition comparison commutes with the ordinary scalar tower. -/
private lemma scalarTower_comparison (E : DerivedExtendScalars.{uR})
    {A B C : Type uR} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (τ : (E f).functor ⋙
      (E g).functor ≅
      (E (g.comp f)).functor)
    (hτ : ∀ X : CochainComplex (ModuleCat.{uR} A) ℤ,
      (E g).functor.map
          ((E f).comparison.app X) ≫
        (E g).comparison.app
          (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj X) ≫
        (extensionOfScalarsComplexComp f g).inv.app X =
      τ.hom.app (DerivedCategory.Q.obj X) ≫
        (E (g.comp f)).comparison.app X)
    {k : A →+* C} (h : g.comp f = k) (X : CochainComplex (ModuleCat.{uR} A) ℤ) :
    (τ ≪≫ derivedExtensionScalarsCongr E h).hom.app (DerivedCategory.Q.obj X) ≫
      (E k).comparison.app X ≫
        DerivedCategory.Q.map ((scalarTower f g h).hom.app X) =
    (E g).functor.map
        ((E f).comparison.app X) ≫
      (E g).comparison.app
        (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj X) := by
  subst h
  simp only [derivedExtensionScalarsCongr, eqToIso_refl,
    Iso.trans_hom, Iso.refl_hom, Category.comp_id]
  have hh := (hτ X) =≫ (extensionOfScalarsComplexComp f g).hom.app X
  simp only [Category.assoc, Iso.inv_hom_id_app] at hh
  erw [Category.comp_id] at hh
  exact hh.symm

/-- Conjugation by a natural isomorphism commutes with transport of source and target. -/
private lemma homCongr_conjugate_naturality
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (τ : F ⋙ G ≅ H)
    {X Y X' Y' : C} (eX : X ≅ X') (eY : Y ≅ Y') (x : F.obj X ⟶ F.obj Y) :
    (H.mapIso eX).homCongr (H.mapIso eY)
      (τ.inv.app X ≫ G.map x ≫ τ.hom.app Y) =
      τ.inv.app X' ≫ G.map ((F.mapIso eX).homCongr (F.mapIso eY) x) ≫
        τ.hom.app Y' := by
  simp only [Iso.homCongr_apply, Functor.mapIso_inv, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [τ.inv.naturality_assoc, ← τ.hom.naturality]
  rfl

/-- Transport the scalar Hom comparison to chosen derived representatives. -/
private def derivedScalarHomEquivOfIso {A : CommRingCat.{uR}} (E : DerivedExtendScalars.{uR})
    (hE : ComputesKFlat E)
    (P L : CochainComplex (ModuleCat.{uR} A) ℤ) (b : ℤ)
    [P.IsStrictlyLE b] [∀ q, Module.Projective A (P.X q)] (hL : L.KFlat)
    {K N : DerivedCategory (ModuleCat.{uR} A)}
    (eP : DerivedCategory.Q.obj P ≅ K) (eL : DerivedCategory.Q.obj L ≅ N)
    (B : Under A) :
    ((HomotopyCategory.quotient _ _).obj P ⟶
      (HomotopyCategory.quotient _ _).obj ((scalarExtensionDiagram L).obj B)) ≃
    ((E B.hom.hom).functor.obj K ⟶
      (E B.hom.hom).functor.obj N) :=
  (derivedScalarHomEquiv E hE P L b hL B).trans
    (((E B.hom.hom).functor.mapIso eP).homCongr
      ((E B.hom.hom).functor.mapIso eL))

/-- The transported scalar Hom comparison has the same canonical transition formula. -/
private lemma derivedScalarHomEquivOfIso_naturality {A : CommRingCat.{uR}}
    (E : DerivedExtendScalars.{uR}) (hE : ComputesKFlat E)
    (P L : CochainComplex (ModuleCat.{uR} A) ℤ) (b : ℤ)
    [P.IsStrictlyLE b] [∀ q, Module.Projective A (P.X q)] (hL : L.KFlat)
    {K N : DerivedCategory (ModuleCat.{uR} A)}
    (eP : DerivedCategory.Q.obj P ≅ K) (eL : DerivedCategory.Q.obj L ≅ N)
    {B C : Under A} (w : B ⟶ C)
    (τ : (E B.hom.hom).functor ⋙
      (E w.right.hom).functor ≅
      (E C.hom.hom).functor)
    (hτ : ∀ X : CochainComplex (ModuleCat.{uR} A) ℤ,
      τ.hom.app (DerivedCategory.Q.obj X) ≫
        (E C.hom.hom).comparison.app X ≫
          DerivedCategory.Q.map ((scalarTower B.hom.hom w.right.hom
            (congrArg CommRingCat.Hom.hom w.w)).hom.app X) =
      (E w.right.hom).functor.map
        ((E B.hom.hom).comparison.app X) ≫
        (E w.right.hom).comparison.app
          (((ModuleCat.extendScalars B.hom.hom).mapHomologicalComplex (.up ℤ)).obj X))
    (x : (HomotopyCategory.quotient _ _).obj P ⟶
      (HomotopyCategory.quotient _ _).obj ((scalarExtensionDiagram L).obj B)) :
    derivedScalarHomEquivOfIso E hE P L b hL eP eL C
      (x ≫ (HomotopyCategory.quotient _ _).map ((scalarExtensionDiagram L).map w)) =
    τ.inv.app K ≫
      (E w.right.hom).functor.map
        (derivedScalarHomEquivOfIso E hE P L b hL eP eL B x) ≫
      τ.hom.app N := by
  dsimp only [derivedScalarHomEquivOfIso, Equiv.trans_apply]
  rw [derivedScalarHomEquiv_naturality_of_comparison E hE P L b hL w τ hτ]
  exact homCongr_conjugate_naturality _ _ _ τ eP eL _

/-- The strict scalar-extension diagram is a colimit on underlying sets in each degree. -/
private def scalarExtensionDiagram_isColimit
    {A : CommRingCat.{uR}} {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (F : I ⥤ Under A) (c : Cocone F)
    (hc : IsColimit ((underRingModule A ⋙ forget _).mapCocone c))
    (L : CochainComplex (ModuleCat.{uR} A) ℤ) (q : ℤ) :
    IsColimit ((forget _).mapCocone ((HomologicalComplex.eval _ _ q).mapCocone
      ((scalarExtensionDiagram L).mapCocone c))) :=
  tensorRight_underlying_isColimit (F ⋙ underRingModule A)
    ((underRingModule A).mapCocone c) hc (L.X q)

/-- The general form of [stacks 0BC7], for an arbitrary total derived extension-of-scalars datum
`E` along every homomorphism of commutative rings in `Type uR`: let `R : I ⥤ CommRingCat` be a
filtered system of commutative rings whose colimit is computed on underlying sets, and let `c` be
a colimit cocone. Writing `E f` for derived extension of scalars along a ring homomorphism `f`,
the following two statements hold.

First, every perfect object `K` of the derived category of `c.pt`-modules descends to a finite
stage: there are an index `i` and a perfect object `Kᵢ` over `R.obj i` with
`K ≅ (E (c.ι.app i)).functor.obj Kᵢ`.

Second, morphisms out of a perfect complex commute with the filtered colimit. Fix a stage `i₀` and
objects `K₀`, `L₀` over `R.obj i₀` with `K₀` perfect. Then derived extension of scalars carries a
composition isomorphism `comp` compatible with the scalar-extension tower on complexes, and the
morphisms `(E (c.ι.app i₀)).functor.obj K₀ ⟶ (E (c.ι.app i₀)).functor.obj L₀` over the colimit ring
form the filtered colimit, over the stages `j` above `i₀`, of the morphisms
`(E (R.map j.hom)).functor.obj K₀ ⟶ (E (R.map j.hom)).functor.obj L₀` over those stages, with the
transition maps and the maps to the colimit given by derived extension of scalars conjugated by
`comp`.

The source statement, for the canonical datum
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars` of [stacks 064H], is
`StacksDraft.Perfect.perfectComplexes_filteredColimit`. -/
public theorem perfectComplexes_filteredColimit_of_datum
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{uR}) [PreservesColimit R (forget CommRingCat.{uR})]
    (c : Cocone R) (hc : IsColimit c) (E : DerivedExtendScalars.{uR}) :
    let D := fun {i j : I} (f : i ⟶ j) ↦ E (R.map f).hom
    let Dlim := fun (i : I) ↦ E (c.ι.app i).hom
    (∀ (K : DerivedCategory (ModuleCat.{uR} c.pt)), IsPerfect K →
        ∃ (i : I) (Kᵢ : DerivedCategory (ModuleCat.{uR} (R.obj i))),
          IsPerfect Kᵢ ∧ Nonempty (K ≅ (Dlim i).functor.obj Kᵢ)) ∧
      (∀ (i₀ : I) (K₀ L₀ : DerivedCategory (ModuleCat.{uR} (R.obj i₀))),
        IsPerfect K₀ →
        ∃ (comp : ∀ {A B C : Type uR} [CommRing A] [CommRing B] [CommRing C]
            (f : A →+* B) (g : B →+* C),
            (E f).functor ⋙ (E g).functor ≅ (E (g.comp f)).functor),
          (∀ {A B C : Type uR} [CommRing A] [CommRing B] [CommRing C]
              (f : A →+* B) (g : B →+* C)
              (P : CochainComplex (ModuleCat.{uR} A) ℤ),
            (E g).functor.map ((E f).comparison.app P) ≫
                (E g).comparison.app
                  (((ModuleCat.extendScalars.{uR, uR, uR} f).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj P) ≫
                (extensionOfScalarsComplexComp.{uR} f g).inv.app P =
              (comp f g).hom.app (DerivedCategory.Q.obj P) ≫
                (E (g.comp f)).comparison.app P) ∧
        ∃ (H : Under i₀ ⥤ Type (uR + 1))
          (eH : ∀ j : Under i₀,
            H.obj j ≃ ((D j.hom).functor.obj K₀ ⟶ (D j.hom).functor.obj L₀))
          (s : Cocone H)
          (eTarget : s.pt ≃ ((Dlim i₀).functor.obj K₀ ⟶ (Dlim i₀).functor.obj L₀))
          (_hs : IsColimit s),
          (∀ {j k : Under i₀} (w : j ⟶ k) (x : H.obj j),
            let h : (R.map w.right).hom.comp (R.map j.hom).hom = (R.map k.hom).hom :=
              by
                ext x
                calc
                  _ = (R.map (j.hom ≫ w.right)).hom x :=
                    (congrArg (fun q : R.obj i₀ ⟶ R.obj k.right ↦ q.hom x)
                      (R.map_comp j.hom w.right)).symm
                  _ = _ := by rw [w.w]
            let stageComp := comp (R.map j.hom).hom (R.map w.right).hom ≪≫
              derivedExtensionScalarsCongr.{uR} E h
            eH k (H.map w x) =
              stageComp.inv.app K₀ ≫
                (D w.right).functor.map (eH j x) ≫
                stageComp.hom.app L₀) ∧
          (∀ (j : Under i₀)
              (g : (D j.hom).functor.obj K₀ ⟶ (D j.hom).functor.obj L₀),
            let h : (c.ι.app j.right).hom.comp (R.map j.hom).hom = (c.ι.app i₀).hom :=
              congrArg CommRingCat.Hom.hom (c.w j.hom)
            let limitComp := comp (R.map j.hom).hom (c.ι.app j.right).hom ≪≫
              derivedExtensionScalarsCongr.{uR} E h
            eTarget (s.ι.app j ((eH j).symm g)) =
              limitComp.inv.app K₀ ≫ (Dlim j.right).functor.map g ≫
                limitComp.hom.app L₀)) := by
  refine ⟨perfect_descends_filteredColimit E R c hc, ?_⟩
  intro i₀ K₀ L₀ hK
  have hE : ComputesKFlat E := computesKFlat E
  refine ⟨fun f g ↦ derivedExtensionScalarsComp E hE f g, ?_, ?_⟩
  · intro A B C _ _ _ f g P
    exact derivedExtensionScalarsComp_comparison E hE f g P
  · obtain ⟨P, a, b, hPa, hPb, hfin, hproj, ⟨eP⟩⟩ := hK
    let : P.IsStrictlyGE a := hPa
    let : P.IsStrictlyLE b := hPb
    let (q : ℤ) : Module.Finite (R.obj i₀) (P.X q) := hfin q
    let (q : ℤ) : Module.Projective (R.obj i₀) (P.X q) := hproj q
    obtain ⟨L, hL, ⟨eL⟩⟩ := CochainComplex.KFlat.exists_kFlat_representative L₀
    let V := scalarExtensionDiagram L
    let G := Under.post (X := i₀) R ⋙ V
    let d : Cocone G := V.mapCocone (c.underPost i₀)
    let Q := HomotopyCategory.quotient (ModuleCat.{uR} (R.obj i₀)) (.up ℤ)
    let T := Q ⋙ coyoneda.obj (Opposite.op (Q.obj P))
    let H : Under i₀ ⥤ Type (uR + 1) := G ⋙ T ⋙ uliftFunctor.{uR + 1, uR}
    let s : Cocone H := uliftFunctor.{uR + 1, uR}.mapCocone (T.mapCocone d)
    let e := derivedScalarHomEquivOfIso E hE P L b hL eP.symm eL
    let eH := fun j : Under i₀ => Equiv.ulift.trans (e ((Under.post R).obj j))
    let eTarget := Equiv.ulift.trans (e (Under.mk (c.ι.app i₀)))
    have hd (q : ℤ) : IsColimit ((forget _).mapCocone
        ((HomologicalComplex.eval _ _ q).mapCocone d)) :=
      scalarExtensionDiagram_isColimit (Under.post R) (c.underPost i₀)
        (scalarModules_isColimit R c hc i₀) L q
    have hs : IsColimit s :=
      isColimitOfPreserves uliftFunctor (bounded_projective_homotopy_isColimit G d hd P a b)
    have hnat : ∀ {B C : Under (R.obj i₀)} (w : B ⟶ C)
        (x : Q.obj P ⟶ Q.obj (V.obj B)),
        e C (x ≫ Q.map (V.map w)) = _ ≫ (E w.right.hom).functor.map (e B x) ≫ _ :=
      fun w x => derivedScalarHomEquivOfIso_naturality E hE P L b hL eP.symm eL w
        (derivedExtensionScalarsComp E hE _ _ ≪≫ derivedExtensionScalarsCongr E _)
        (fun X => scalarTower_comparison E _ _ _
          (derivedExtensionScalarsComp_comparison E hE _ _) _ X) x
    refine ⟨H, eH, s, eTarget, hs, fun w x => hnat _ x.down, fun j g => ?_⟩
    have hg : e _ ((eH j).symm g).down = g := (eH j).apply_symm_apply g
    have hn := hnat ((c.underPost i₀).ι.app j) ((eH j).symm g).down
    rwa [hg] at hn

/-- **Stacks 0BC7.** Let `R : I ⥤ CommRingCat` be a filtered system of commutative rings whose
colimit is computed on underlying sets, and let `c` be a colimit cocone. Writing `E f` for the
canonical total derived extension of scalars `- ⊗ᴸ_A B` along `f : A →+* B` ([stacks 064H]), the
following two statements hold.

First, every perfect object `K` of the derived category of `c.pt`-modules descends to a finite
stage: there are an index `i` and a perfect object `Kᵢ` over `R.obj i` with
`K ≅ (E (c.ι.app i)).functor.obj Kᵢ`.

Second, morphisms out of a perfect complex commute with the filtered colimit. Fix a stage `i₀` and
objects `K₀`, `L₀` over `R.obj i₀` with `K₀` perfect. Then derived extension of scalars carries a
composition isomorphism `comp` compatible with the scalar-extension tower on complexes, and the
morphisms `(E (c.ι.app i₀)).functor.obj K₀ ⟶ (E (c.ι.app i₀)).functor.obj L₀` over the colimit ring
form the filtered colimit, over the stages `j` above `i₀`, of the morphisms
`(E (R.map j.hom)).functor.obj K₀ ⟶ (E (R.map j.hom)).functor.obj L₀` over those stages, with the
transition maps and the maps to the colimit given by derived extension of scalars conjugated by
`comp`. -/
@[stacks 0BC7]
public theorem perfectComplexes_filteredColimit
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{uR}) [PreservesColimit R (forget CommRingCat.{uR})]
    (c : Cocone R) (hc : IsColimit c) :
    let E := fun {A B : Type uR} [CommRing A] [CommRing B] (f : A →+* B) ↦
      totalDerivedExtensionScalars.{uR, uR, uR} f
    let D := fun {i j : I} (f : i ⟶ j) ↦ E (R.map f).hom
    let Dlim := fun (i : I) ↦ E (c.ι.app i).hom
    (∀ (K : DerivedCategory (ModuleCat.{uR} c.pt)), IsPerfect K →
        ∃ (i : I) (Kᵢ : DerivedCategory (ModuleCat.{uR} (R.obj i))),
          IsPerfect Kᵢ ∧ Nonempty (K ≅ (Dlim i).functor.obj Kᵢ)) ∧
      (∀ (i₀ : I) (K₀ L₀ : DerivedCategory (ModuleCat.{uR} (R.obj i₀))),
        IsPerfect K₀ →
        ∃ (comp : ∀ {A B C : Type uR} [CommRing A] [CommRing B] [CommRing C]
            (f : A →+* B) (g : B →+* C),
            (E f).functor ⋙ (E g).functor ≅ (E (g.comp f)).functor),
          (∀ {A B C : Type uR} [CommRing A] [CommRing B] [CommRing C]
              (f : A →+* B) (g : B →+* C)
              (P : CochainComplex (ModuleCat.{uR} A) ℤ),
            (E g).functor.map ((E f).comparison.app P) ≫
                (E g).comparison.app
                  (((ModuleCat.extendScalars.{uR, uR, uR} f).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj P) ≫
                (extensionOfScalarsComplexComp.{uR} f g).inv.app P =
              (comp f g).hom.app (DerivedCategory.Q.obj P) ≫
                (E (g.comp f)).comparison.app P) ∧
        ∃ (H : Under i₀ ⥤ Type (uR + 1))
          (eH : ∀ j : Under i₀,
            H.obj j ≃ ((D j.hom).functor.obj K₀ ⟶ (D j.hom).functor.obj L₀))
          (s : Cocone H)
          (eTarget : s.pt ≃ ((Dlim i₀).functor.obj K₀ ⟶ (Dlim i₀).functor.obj L₀))
          (_hs : IsColimit s),
          (∀ {j k : Under i₀} (w : j ⟶ k) (x : H.obj j),
            let h : (R.map w.right).hom.comp (R.map j.hom).hom = (R.map k.hom).hom :=
              by
                ext x
                calc
                  _ = (R.map (j.hom ≫ w.right)).hom x :=
                    (congrArg (fun q : R.obj i₀ ⟶ R.obj k.right ↦ q.hom x)
                      (R.map_comp j.hom w.right)).symm
                  _ = _ := by rw [w.w]
            let stageComp := comp (R.map j.hom).hom (R.map w.right).hom ≪≫
              derivedExtensionScalarsCongr.{uR} E h
            eH k (H.map w x) =
              stageComp.inv.app K₀ ≫
                (D w.right).functor.map (eH j x) ≫
                stageComp.hom.app L₀) ∧
          (∀ (j : Under i₀)
              (g : (D j.hom).functor.obj K₀ ⟶ (D j.hom).functor.obj L₀),
            let h : (c.ι.app j.right).hom.comp (R.map j.hom).hom = (c.ι.app i₀).hom :=
              congrArg CommRingCat.Hom.hom (c.w j.hom)
            let limitComp := comp (R.map j.hom).hom (c.ι.app j.right).hom ≪≫
              derivedExtensionScalarsCongr.{uR} E h
            eTarget (s.ι.app j ((eH j).symm g)) =
              limitComp.inv.app K₀ ≫ (Dlim j.right).functor.map g ≫
                limitComp.hom.app L₀)) :=
  perfectComplexes_filteredColimit_of_datum.{uI, uR} R c hc
    (fun f ↦ totalDerivedExtensionScalars.{uR, uR, uR} f)

end HomColimit

end StacksDraft.Perfect

end
