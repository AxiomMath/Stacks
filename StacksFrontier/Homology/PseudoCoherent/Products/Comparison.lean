module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.BifunctorFlip
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Ring.Shrink
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Localization.Adjunction
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.Tactic.TFAE
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.PseudoCoherent.Triangle
public import StacksFrontier.Homology.TensorComplex.ExactFunctor
public import StacksFrontier.RingTheory.Module.FinitePresentation.TensorProductPi
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.TermFunctorExactness

/-!
# Pseudo-coherence and products: the comparison morphisms

The comparison morphisms `K ⊗ᴸ (∏ a, Q a) ⟶ ∏ a, (K ⊗ᴸ Q a)`, `K ⊗ᴸ Q^A ⟶ (K ⊗ᴸ Q)^A` and
`K ⊗ᴸ R^A ⟶ K^A` on the derived category of a small copy of a commutative ring `R`, together
with the first half of the proof of Stacks 0CYB: the comparison for a K-flat representative,
preservation of products by tensoring with a finitely presented module, the comparison for a
pseudo-coherent object, and the reduction of the four-way characterization to its core
implications.

## Main definitions

* `StacksDraft.PseudoCoherence.DerivedTensorProduct`: a derived tensor bifunctor on `D(R)`.
* `StacksDraft.PseudoCoherence.DerivedProducts`: a choice of categorical products in `D(R)`.
* `StacksDraft.PseudoCoherence.tensorProductComparison`, `tensorPowerComparison` and
  `tensorRingPowerComparison`: the comparison morphisms.

## References

* [Stacks Project, Tag 0CYB](https://stacks.math.columbia.edu/tag/0CYB)
-/

@[expose] public section

namespace StacksDraft.PseudoCoherence

/-! ### Tensoring a complex with a module -/

section TensorWithComplexPort

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

set_option backward.isDefEq.respectTransparency false

universe uA

variable {A : Type uA} [CommRing A]

/-- The functor `N ↦ M• ⊗_A N`, using `N` as a complex concentrated in degree zero. -/
noncomputable abbrev tensorWithCochainComplex (M : CochainComplex (ModuleCat.{uA} A) ℤ) :
    CategoryTheory.Functor (ModuleCat.{uA} A) (CochainComplex (ModuleCat.{uA} A) ℤ) :=
  HomologicalComplex.single (ModuleCat.{uA} A) (ComplexShape.up ℤ) 0 ⋙
    (MonoidalCategory.curriedTensor (ModuleCat.{uA} A)).map₂CochainComplex.obj M

/-- The only nonzero summand in degree `n` of `M ⊗ N[0]` is `Mⁿ ⊗ N`. -/
private noncomputable def tensorSingleTermIso (M : CochainComplex (ModuleCat.{uA} A) ℤ)
    (N : ModuleCat.{uA} A) (n : ℤ) :
    M.X n ⊗ N ≅ ((tensorWithCochainComplex M).obj N).X n := by
  let K := (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℤ) 0).obj N
  let F := curriedTensor (ModuleCat A)
  let e := singleObjXSelf (ComplexShape.up ℤ) 0 N
  let j := ιMapBifunctor M K F (ComplexShape.up ℤ) n 0 n (by simp)
  let p : (HomologicalComplex.mapBifunctor M K F (ComplexShape.up ℤ)).X n ⟶ (M.X n ⊗ K.X 0) :=
    mapBifunctorDesc fun a b hab =>
      if h : b = 0 then by
        subst b
        have ha : a = n := by simpa using hab
        subst a
        exact 𝟙 _
      else 0
  have hjp : j ≫ p = 𝟙 _ := by
    dsimp [j, p]
    simp
  have hpj : p ≫ j = 𝟙 _ := by
    apply mapBifunctor.hom_ext
    intro a b hab
    by_cases hb : b = 0
    · subst b
      have ha : a = n := by simpa using hab
      subst a
      simp [j, p]
    · exact ((F.obj (M.X a)).map_isZero
        (isZero_single_obj_X (ComplexShape.up ℤ) 0 N b hb)).eq_of_src _ _
  exact (tensorIso (Iso.refl _) e.symm) ≪≫ ⟨j, p, hjp, hpj⟩

private lemma tensorSingleTermIso_naturality
    (M : CochainComplex (ModuleCat.{uA} A) ℤ) {N P : ModuleCat.{uA} A}
    (g : N ⟶ P) (n : ℤ) :
    (M.X n ◁ g) ≫ (tensorSingleTermIso M P n).hom =
      (tensorSingleTermIso M N n).hom ≫ ((tensorWithCochainComplex M).map g).f n := by
  dsimp [tensorSingleTermIso, tensorWithCochainComplex]
  simp only [id_tensorHom,
    Functor.map₂HomologicalComplex_obj_map, Category.assoc, ι_mapBifunctorMap,
    curriedTensor_obj_obj, id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
    curriedTensor_obj_map, Category.id_comp]
  rw [single_map_f_self]
  simp [whiskerLeft_comp, Category.assoc]

/-- The termwise tensor comparison is natural in the module. -/
private noncomputable def tensorSingleEvalIso (M : CochainComplex (ModuleCat.{uA} A) ℤ) (n : ℤ) :
    tensorLeft (M.X n) ≅ tensorWithCochainComplex M ⋙
      HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n :=
  NatIso.ofComponents (fun N => tensorSingleTermIso M N n)
    (fun g => tensorSingleTermIso_naturality M g n)

end TensorWithComplexPort

section PiDiscretePort

open CategoryTheory CategoryTheory.Limits

section PiPreserves

variable {J A B : Type*} [Category A] [Category B] [HasProducts B]

end PiPreserves

end PiDiscretePort

/-! ### The comparison morphisms -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open scoped ZeroObject

-- We use the standard construction of the derived category of an abelian category, which
-- supplies the triangulated structure and the cohomology functors `Hⁱ`.
attribute [local instance] HasDerivedCategory.standard

universe u v w

section Comparisons

variable (R : Type u) [CommRing R] [Small.{max v w} R]

-- `v` and `w` only ever occur as `max v w`; the two universes are kept separate so that the
-- module universe is visibly independent of the ring's, as in the source statement.
set_option linter.checkUnivs false in
/-- The copy of the coefficient ring in the universe of the modules. -/
abbrev SmallRing := Shrink.{max v w} R

set_option linter.checkUnivs false in
/-- The derived category of modules over the small copy of `R`. -/
abbrev D := DerivedCategory (ModuleCat.{max v w} (SmallRing.{u, v, w} R))

/-- A derived tensor product on `D(R)`, characterized as the total left derived functor of
tensoring cochain complexes, with its exactness and canonical unit isomorphism. -/
structure DerivedTensorProduct where
  /-- The derived tensor bifunctor. -/
  tensor : D.{u, v, w} R ⥤ D.{u, v, w} R ⥤ D.{u, v, w} R
  /-- The comparison to tensoring representative complexes. -/
  comparison : ∀ E : CochainComplex (ModuleCat.{max v w} (SmallRing.{u, v, w} R)) ℤ,
    DerivedCategory.Q ⋙ tensor.obj (DerivedCategory.Q.obj E) ⟶
      tensorLeft E ⋙ DerivedCategory.Q
  /-- Tensoring by the image of a complex is its total left derived functor. -/
  isLeftDerived : ∀ E : CochainComplex (ModuleCat.{max v w} (SmallRing.{u, v, w} R)) ℤ,
    (tensor.obj (DerivedCategory.Q.obj E)).IsLeftDerivedFunctor
      (comparison E) (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
  /-- Tensoring with any derived object commutes with shifts. -/
  commShift : ∀ K : D.{u, v, w} R, (tensor.obj K).CommShift ℤ
  /-- Tensoring with any derived object preserves distinguished triangles. -/
  triangulated : ∀ K : D.{u, v, w} R, letI := commShift K;
    (tensor.obj K).IsTriangulated
  /-- The complex `R[0]` is the right unit. -/
  unitIso : tensor.flip.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{max v w} (SmallRing.{u, v, w} R)) 0).obj
        (ModuleCat.of (SmallRing.{u, v, w} R) (SmallRing.{u, v, w} R))) ≅ Functor.id (D.{u, v, w} R)

/-- A simultaneous choice of categorical products in `D(R)` indexed in `Type (max v w)`. -/
structure DerivedProducts where
  /-- Every chosen product is categorical. -/
  hasProduct : ∀ (A : Type (max v w)) (F : A → D.{u, v, w} R), HasProduct F

variable {R}

/-- The canonical morphism `K ⊗ᴸ (∏ a, Q a) ⟶ ∏ a, (K ⊗ᴸ Q a)`, with both
products taken in the derived category after embedding the modules in degree zero. -/
noncomputable def tensorProductComparison (T : DerivedTensorProduct.{u, v, w} R)
    (P : DerivedProducts.{u, v, w} R) (K : D.{u, v, w} R) (A : Type (max v w))
    (Q : A → ModuleCat.{max v w} (SmallRing.{u, v, w} R)) :
    let S := DerivedCategory.singleFunctor (ModuleCat.{max v w} (SmallRing.{u, v, w} R)) 0
    letI := P.hasProduct A (fun a => S.obj (Q a))
    letI := P.hasProduct A (fun a => (T.tensor.obj K).obj (S.obj (Q a)))
    (T.tensor.obj K).obj (∏ᶜ fun a => S.obj (Q a)) ⟶
      ∏ᶜ fun a => (T.tensor.obj K).obj (S.obj (Q a)) := by
  let S := DerivedCategory.singleFunctor (ModuleCat.{max v w} (SmallRing.{u, v, w} R)) 0
  letI := P.hasProduct A (fun a => S.obj (Q a))
  letI := P.hasProduct A (fun a => (T.tensor.obj K).obj (S.obj (Q a)))
  exact Pi.lift fun a => (T.tensor.obj K).map (Pi.π _ a)

/-- The canonical morphism `K ⊗ᴸ Q^A ⟶ (K ⊗ᴸ Q)^A`. -/
noncomputable def tensorPowerComparison (T : DerivedTensorProduct.{u, v, w} R)
    (P : DerivedProducts.{u, v, w} R) (K : D.{u, v, w} R) (A : Type (max v w))
    (Q : ModuleCat.{max v w} (SmallRing.{u, v, w} R)) :=
  tensorProductComparison T P K A (fun _ => Q)

/-- The canonical morphism `K ⊗ᴸ R^A ⟶ K^A`, with powers taken in the derived
category and using the unit isomorphism componentwise. -/
noncomputable def tensorRingPowerComparison (T : DerivedTensorProduct.{u, v, w} R)
    (P : DerivedProducts.{u, v, w} R) (K : D.{u, v, w} R) (A : Type (max v w)) :
    let S := DerivedCategory.singleFunctor (ModuleCat.{max v w} (SmallRing.{u, v, w} R)) 0
    let R₀ := S.obj (ModuleCat.of (SmallRing.{u, v, w} R) (SmallRing.{u, v, w} R))
    letI := P.hasProduct A (fun _ => R₀)
    letI := P.hasProduct A (fun _ => K)
    (T.tensor.obj K).obj (∏ᶜ fun _ : A => R₀) ⟶ ∏ᶜ fun _ : A => K := by
  let S := DerivedCategory.singleFunctor (ModuleCat.{max v w} (SmallRing.{u, v, w} R)) 0
  let R₀ := S.obj (ModuleCat.of (SmallRing.{u, v, w} R) (SmallRing.{u, v, w} R))
  letI := P.hasProduct A (fun _ => R₀)
  letI := P.hasProduct A (fun _ => K)
  exact Pi.lift fun a =>
    (T.tensor.obj K).map (Pi.π _ a) ≫ T.unitIso.hom.app K

end Comparisons

/-! ### The development -/

/-- **Stacks 064K** at a module universe equal to the ring's: a cochain complex of flat modules
that vanishes above `b` is K-flat. -/
private lemma kFlat_of_flat_of_isStrictlyLE {S : Type v} [CommRing S]
    (E : CochainComplex (ModuleCat.{v} S) ℤ) (b : ℤ) [E.IsStrictlyLE b]
    [∀ n : ℤ, Module.Flat S (E.X n)] : E.KFlat :=
  CochainComplex.KFlat.kFlat_of_flat.{v, v} E b

private lemma isIso_tensorPowerComparison_of_isIso_tensorProductComparison
    (R : Type u) [CommRing R] [Small.{max v w} R]
    (T : DerivedTensorProduct.{u, v, w} R) (P : DerivedProducts.{u, v, w} R) (K : D.{u, v, w} R)
    (h : ∀ (A : Type (max v w)) (Q : A → ModuleCat.{max v w} (SmallRing.{u, v, w} R)),
      IsIso (tensorProductComparison T P K A Q))
    (A : Type (max v w)) (Q : ModuleCat.{max v w} (SmallRing.{u, v, w} R)) :
    IsIso (tensorPowerComparison T P K A Q) :=
  h A (fun _ => Q)

private lemma homologyRange_tensorPowerComparison_of_homologyRange_tensorProductComparison
    (R : Type u) [CommRing R] [Small.{max v w} R]
    (T : DerivedTensorProduct.{u, v, w} R) (P : DerivedProducts.{u, v, w} R)
    (K : D.{u, v, w} R) (m : ℤ)
    (h : ∀ (A : Type (max v w)) (Q : A → ModuleCat.{max v w} (SmallRing.{u, v, w} R)),
      (∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor _ i).map
        (tensorProductComparison T P K A Q))) ∧
      Epi ((DerivedCategory.homologyFunctor _ m).map
        (tensorProductComparison T P K A Q)))
    (A : Type (max v w)) (Q : ModuleCat.{max v w} (SmallRing.{u, v, w} R)) :
    (∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor _ i).map
      (tensorPowerComparison T P K A Q))) ∧
    Epi ((DerivedCategory.homologyFunctor _ m).map
      (tensorPowerComparison T P K A Q)) :=
  h A (fun _ => Q)

private lemma isIso_derivedTensorComparison_of_invertsQuasiIso
    (R : Type u) [CommRing R] [Small.{max v w} R]
    (T : DerivedTensorProduct.{u, v, w} R)
    (E : CochainComplex (ModuleCat.{max v w} (SmallRing.{u, v, w} R)) ℤ)
    (h : (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)).IsInvertedBy
      (tensorLeft E ⋙ DerivedCategory.Q)) :
    IsIso (T.comparison E) := by
  let := T.isLeftDerived E
  exact Functor.isIso_of_isLeftDerivedFunctor_of_inverts
    (T.tensor.obj (DerivedCategory.Q.obj E)) (T.comparison E) h

private noncomputable def signedTensorFlipIso
    (S : Type (v)) [CommRing S]
    (E M : CochainComplex (ModuleCat.{v} S) ℤ) :
    HomologicalComplex.mapBifunctor M E
        (curriedTensor (ModuleCat.{v} S)).flip (ComplexShape.up ℤ) ≅
      E ⊗ M :=
  HomologicalComplex.mapBifunctorFlipIso E M
    (curriedTensor (ModuleCat.{v} S)) (ComplexShape.up ℤ)

private noncomputable def braidingBicomplexIso
    (S : Type (v)) [CommRing S]
    (M E : CochainComplex (ModuleCat.{v} S) ℤ) :
    (((curriedTensor (ModuleCat.{v} S)).flip.mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj M).obj E ≅
    (((curriedTensor (ModuleCat.{v} S)).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj M).obj E := by
  refine HomologicalComplex.Hom.isoOfComponents (fun i => ?_) ?_
  · refine HomologicalComplex.Hom.isoOfComponents
      (fun j => β_ (E.X j) (M.X i)) ?_
    intro j j' h
    simp only [Functor.mapBifunctorHomologicalComplex_obj_obj_X_d]
    exact (BraidedCategory.braiding_naturality_left (E.d j j') (M.X i)).symm
  · intro i i' h
    ext j : 1
    exact (BraidedCategory.braiding_naturality_right (E.X j) (M.d i i')).symm

private noncomputable def braidingTotalIso
    (S : Type (v)) [CommRing S]
    (M E : CochainComplex (ModuleCat.{v} S) ℤ) :
    HomologicalComplex.mapBifunctor M E
        (curriedTensor (ModuleCat.{v} S)).flip (ComplexShape.up ℤ) ≅
      M ⊗ E :=
  HomologicalComplex₂.total.mapIso (braidingBicomplexIso S M E) (ComplexShape.up ℤ)

private noncomputable def tensorCommIso
    (S : Type (v)) [CommRing S]
    (M E : CochainComplex (ModuleCat.{v} S) ℤ) : M ⊗ E ≅ E ⊗ M :=
  (braidingTotalIso S M E).symm ≪≫ signedTensorFlipIso S E M

private lemma kFlat_left_acyclic
    (S : Type (v)) [CommRing S]
    (E : CochainComplex (ModuleCat.{v} S) ℤ) (hE : E.KFlat)
    (M : CochainComplex (ModuleCat.{v} S) ℤ) (hM : M.Acyclic) :
    (E ⊗ M).Acyclic :=
  HomologicalComplex.Acyclic.of_iso (tensorCommIso S M E) (hE M hM)

private lemma kFlat_tleft_preserves_quasiIso
    (S : Type (v)) [CommRing S]
    (E : CochainComplex (ModuleCat.{v} S) ℤ) (hE : E.KFlat) :
    HomotopyCategory.quasiIso (ModuleCat.{v} S) (ComplexShape.up ℤ) ≤
      (HomotopyCategory.quasiIso (ModuleCat.{v} S) (ComplexShape.up ℤ)).inverseImage
        (Tleft E) := by
  obtain ⟨e, h⟩ := main_left E
  let := e
  let := h
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  let P := HomotopyCategory.subcategoryAcyclic (ModuleCat.{v} S)
  have hobj : P ≤ P.inverseImage (Tleft E) := by
    intro X hX
    obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    rw [ObjectProperty.prop_inverseImage_iff]
    change HomotopyCategory.subcategoryAcyclic _
      ((HomotopyCategory.quotient _ _).obj M) at hX
    change HomotopyCategory.subcategoryAcyclic _
      ((HomotopyCategory.quotient _ _).obj ((TleftCochain E).obj M))
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hX ⊢
    exact kFlat_left_acyclic S E hE M hX
  intro X Y f hf
  rw [MorphismProperty.inverseImage_iff,
    ← ObjectProperty.inverseImage_trW_iff (P := P) (F := Tleft E)]
  exact ObjectProperty.trW_monotone hobj _ hf

private lemma kFlat_tensorLeft_inverts_quasiIso
    (S : Type v) [CommRing S]
    (E : CochainComplex (ModuleCat.{v} S) ℤ) (hE : E.KFlat) :
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)).IsInvertedBy
      (tensorLeft E ⋙ DerivedCategory.Q) := by
  intro X Y f hf
  have hh := kFlat_tleft_preserves_quasiIso S E hE
    ((HomotopyCategory.quotient _ _).map f)
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff f).mpr hf)
  change HomotopyCategory.quasiIso _ _
    ((HomotopyCategory.quotient _ _ ⋙ Tleft E).map f) at hh
  unfold Tleft at hh
  rw [descendF_comp_quotient] at hh
  have hq := (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mp hh
  exact Localization.inverts DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _ hq

private lemma isIso_derivedTensorComparison_of_kFlat
    (R : Type u) [CommRing R] [Small.{max v w} R]
    (T : DerivedTensorProduct.{u, v, w} R)
    (E : CochainComplex (ModuleCat.{max v w} (SmallRing.{u, v, w} R)) ℤ)
    (hE : E.KFlat) : IsIso (T.comparison E) :=
  isIso_derivedTensorComparison_of_invertsQuasiIso R T E
    (kFlat_tensorLeft_inverts_quasiIso _ E hE)

private lemma hasProductsOfShape
    (R : Type u) [CommRing R] [Small.{max v w} R]
    (P : DerivedProducts.{u, v, w} R) (A : Type (max v w)) :
    HasProductsOfShape A (D.{u, v, w} R) := by
  refine ⟨fun F => ?_⟩
  let := P.hasProduct A (fun a => F.obj ⟨a⟩)
  rw [← hasLimit_iff_of_iso (Discrete.natIso
    (F := Discrete.functor fun a => F.obj ⟨a⟩) (G := F)
    fun ⟨_⟩ => Iso.refl _)]
  infer_instance

private lemma preservesProducts_singleFunctor
    (R : Type u) [CommRing R] [Small.{max v w} R] (A : Type (max v w)) :
    PreservesLimitsOfShape (Discrete A)
      (DerivedCategory.singleFunctor (ModuleCat.{max v w} (SmallRing.{u, v, w} R)) 0) := by
  classical
  have hQ : PreservesLimitsOfShape (Discrete A)
      (DerivedCategory.Q (C := ModuleCat.{max v w} (SmallRing.{u, v, w} R))) :=
    Stacks.DerivedProducts.preservesLimitsOfShape_Q
  have hsingle : PreservesLimitsOfShape (Discrete A)
      (CochainComplex.singleFunctor (ModuleCat.{max v w} (SmallRing.{u, v, w} R)) 0) := by
    change PreservesLimitsOfShape (Discrete A)
      (HomologicalComplex.single (ModuleCat.{max v w} (SmallRing.{u, v, w} R))
        (ComplexShape.up ℤ) 0)
    infer_instance
  change PreservesLimitsOfShape (Discrete A)
    (CochainComplex.singleFunctor (ModuleCat.{max v w} (SmallRing.{u, v, w} R)) 0 ⋙
      DerivedCategory.Q)
  infer_instance

private lemma piComparison_tensorLeft_eq
    (S : Type v) [CommRing S] (M : ModuleCat.{v} S)
    (A : Type v) (Q : A → ModuleCat.{v} S) :
    piComparison (tensorLeft M) Q =
      (tensorLeft M).map (ModuleCat.piIsoPi Q).hom ≫
        ModuleCat.ofHom (TensorProduct.piRightHom S S M (fun a => Q a)) ≫
          (ModuleCat.piIsoPi (fun a => M ⊗ Q a)).inv := by
  apply Pi.hom_ext
  intro a
  rw [piComparison_comp_π, Category.assoc, Category.assoc,
    show (ModuleCat.piIsoPi (fun a => M ⊗ Q a)).inv ≫
      Pi.π (fun a => (tensorLeft M).obj (Q a)) a =
        ModuleCat.ofHom (LinearMap.proj a) from
          ModuleCat.piIsoPi_inv_kernel_ι (fun a => M ⊗ Q a) a]
  have hproj : ModuleCat.ofHom (TensorProduct.piRightHom S S M (fun a => Q a)) ≫
      ModuleCat.ofHom (LinearMap.proj a) =
      (tensorLeft M).map (ModuleCat.ofHom (LinearMap.proj a)) := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl
  rw [hproj, ← Functor.map_comp, ModuleCat.piIsoPi_hom_ker_subtype]

private lemma isIso_piComparison_tensorLeft_of_finitePresentation
    (S : Type v) [CommRing S] (M : ModuleCat.{v} S)
    [Module.FinitePresentation S M] (A : Type v) (Q : A → ModuleCat.{v} S) :
    IsIso (piComparison (tensorLeft M) Q) := by
  have hf : IsIso (ModuleCat.ofHom (TensorProduct.piRightHom S S M (fun a => Q a))) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    have h := ((Module.FinitePresentation.tfae_piRightHom_bijective S M).out 1 2).mp
      (inferInstance : Module.FinitePresentation S M)
    exact h A (fun a => Q a)
  rw [piComparison_tensorLeft_eq S M A Q]
  infer_instance

private lemma epi_piComparison_tensorLeft_of_finite
    (S : Type v) [CommRing S] (M : ModuleCat.{v} S)
    [Module.Finite S M] (A : Type v) (Q : A → ModuleCat.{v} S) :
    Epi (piComparison (tensorLeft M) Q) := by
  have hf : Epi (ModuleCat.ofHom (TensorProduct.piRightHom S S M (fun a => Q a))) := by
    rw [ModuleCat.epi_iff_surjective]
    have h := ((Module.Finite.tfae_piRightHom_surjective S M).out 1 2).mp
      (inferInstance : Module.Finite S M)
    exact h A (fun a => Q a)
  rw [piComparison_tensorLeft_eq S M A Q]
  have : Epi ((tensorLeft M).map (ModuleCat.piIsoPi Q).hom) := IsIso.epi_of_iso _
  rwa [epi_comp_iff_of_epi, epi_comp_iff_of_isIso]

private lemma preservesProducts_tensorLeft_of_finitePresentation
    (S : Type v) [CommRing S] (M : ModuleCat.{v} S)
    [Module.FinitePresentation S M] (A : Type v) :
    PreservesLimitsOfShape (Discrete A) (tensorLeft M) := by
  let : ∀ Q : A → ModuleCat.{v} S, PreservesLimit (Discrete.functor Q) (tensorLeft M) :=
    fun Q => by
      let := isIso_piComparison_tensorLeft_of_finitePresentation S M A Q
      exact PreservesProduct.of_iso_comparison _ _
  exact preservesLimitsOfShape_of_discrete _

private lemma preservesProducts_tensorWithCochainComplex
    (S : Type v) [CommRing S] (E : CochainComplex (ModuleCat.{v} S) ℤ)
    [∀ n, Module.FinitePresentation S (E.X n)] (A : Type v) :
    PreservesLimitsOfShape (Discrete A) (tensorWithCochainComplex E) := by
  constructor
  intro F
  apply preservesLimit_of_preserves_limit_cone (limit.isLimit F)
  apply HomologicalComplex.isLimitOfEval
  intro n
  have : PreservesLimitsOfShape (Discrete A) (tensorLeft (E.X n)) :=
    preservesProducts_tensorLeft_of_finitePresentation S (E.X n) A
  have : PreservesLimitsOfShape (Discrete A)
      (tensorWithCochainComplex E ⋙
        HomologicalComplex.eval (ModuleCat S) (ComplexShape.up ℤ) n) :=
    preservesLimitsOfShape_of_natIso (tensorSingleEvalIso E n)
  exact isLimitOfPreserves
    (tensorWithCochainComplex E ⋙
      HomologicalComplex.eval (ModuleCat S) (ComplexShape.up ℤ) n) (limit.isLimit F)

private lemma isIso_tensorProductComparison_of_isPseudoCoherent
    (R : Type u) [CommRing R] [Small.{max v w} R]
    (T : DerivedTensorProduct.{u, v, w} R) (P : DerivedProducts.{u, v, w} R)
    (K : D.{u, v, w} R) (hK : IsPseudoCoherent K)
    (A : Type (max v w)) (Q : A → ModuleCat.{max v w} (SmallRing.{u, v, w} R)) :
    IsIso (tensorProductComparison T P K A Q) := by
  obtain ⟨E, hE, ⟨e⟩⟩ := hK
  let S := SmallRing.{u, v, w} R
  let C := ModuleCat.{max v w} S
  let c := CochainComplex.singleFunctor C 0
  let d := DerivedCategory.singleFunctor C 0
  let : ∀ n, Module.Free S (E.X n) := fun n => (hE.finiteFree n).2
  let : ∀ n, Module.Finite S (E.X n) := fun n => (hE.finiteFree n).1
  let : ∀ n, Module.Projective S (E.X n) := fun n => Module.Projective.of_free
  let : ∀ n, Module.FinitePresentation S (E.X n) :=
    fun n => Module.finitePresentation_of_projective S (E.X n)
  let : ∀ n, Module.Flat S (E.X n) := fun n => inferInstance
  obtain ⟨b, hb⟩ := hE.upperBound
  have hflat : E.KFlat := kFlat_of_flat_of_isStrictlyLE E b
  let := isIso_derivedTensorComparison_of_kFlat R T E hflat
  let := hasProductsOfShape R P A
  let : PreservesLimitsOfShape (Discrete A) (DerivedCategory.Q (C := C)) :=
    Stacks.DerivedProducts.preservesLimitsOfShape_Q
  let := preservesProducts_tensorWithCochainComplex S E A
  have hn : d ⋙ T.tensor.obj (DerivedCategory.Q.obj E) ≅
      tensorWithCochainComplex E ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerLeft c (asIso (T.comparison E))
  let : PreservesLimitsOfShape (Discrete A)
      (d ⋙ T.tensor.obj (DerivedCategory.Q.obj E)) :=
    preservesLimitsOfShape_of_natIso hn.symm
  let := preservesProducts_singleFunctor.{u, v, w} R A
  have hc : IsIso (piComparison (d ⋙ T.tensor.obj (DerivedCategory.Q.obj E)) Q) :=
    inferInstance
  rw [Stacks.DerivedProducts.piComparison_comp_eq] at hc
  have hcomp : IsIso (piComparison (T.tensor.obj (DerivedCategory.Q.obj E))
      (fun a => d.obj (Q a))) :=
    IsIso.of_isIso_comp_left ((T.tensor.obj (DerivedCategory.Q.obj E)).map
      (piComparison d Q)) _
  let : PreservesLimit (Discrete.functor (fun a => d.obj (Q a)))
      (T.tensor.obj (DerivedCategory.Q.obj E)) := PreservesProduct.of_iso_comparison _ _
  let : PreservesLimit (Discrete.functor (fun a => d.obj (Q a))) (T.tensor.obj K) :=
    preservesLimit_of_natIso _ (T.tensor.mapIso e)
  change IsIso (piComparison (T.tensor.obj K) (fun a => d.obj (Q a)))
  infer_instance

noncomputable def moduleTensorRingPowerComparison
    (S : Type v) [CommRing S] (A : Type v) :
    tensorRight (ModuleCat.of S (A → S)) ⟶
      piDiscreteFunctor (fun _ : A => 𝟭 (ModuleCat.{v} S)) ⋙ lim where
  app M := Pi.lift (f := fun _ : A => M) (fun a => ModuleCat.ofHom
    ((LinearMap.proj a).comp (TensorProduct.piScalarRightHom S S M A)))
  naturality {M N} f := by
    change (tensorRight (ModuleCat.of S (A → S))).map f ≫
      Pi.lift (f := fun _ : A => N) (fun a => ModuleCat.ofHom
        ((LinearMap.proj a).comp (TensorProduct.piScalarRightHom S S N A))) =
      Pi.lift (f := fun _ : A => M) (fun a => ModuleCat.ofHom
        ((LinearMap.proj a).comp (TensorProduct.piScalarRightHom S S M A))) ≫
          Limits.Pi.map (fun _ : A => f)
    apply Pi.hom_ext
    intro a
    simp only [Category.assoc, Pi.lift_comp_π, Pi.map_π, Pi.lift_comp_π_assoc]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x r
    exact (map_smul f.hom (r a) x).symm

private lemma moduleTensorRingPowerComparison_comp_pi
    (S : Type v) [CommRing S] (A : Type v) (M : ModuleCat.{v} S) (a : A) :
    (moduleTensorRingPowerComparison S A).app M ≫ Pi.π (fun _ : A => M) a =
      ModuleCat.ofHom ((LinearMap.proj a).comp (TensorProduct.piScalarRightHom S S M A)) :=
  Pi.lift_comp_π _ _

private lemma finite_of_epi_moduleTensorRingPowerComparison
    (S : Type v) [CommRing S] (M : ModuleCat.{v} S)
    (h : ∀ A : Type v, Epi ((moduleTensorRingPowerComparison S A).app M)) :
    Module.Finite S M := by
  apply ((Module.Finite.tfae_piRightHom_surjective S M).out 4 1).mp
  intro A x
  obtain ⟨t, ht⟩ := (ModuleCat.epi_iff_surjective _).mp (h A)
    ((ModuleCat.piIsoPi (fun _ : A => M)).inv x)
  refine ⟨t, funext fun a => ?_⟩
  have he := congrArg (fun z => (Pi.π (fun _ : A => M) a) z) ht
  change (((moduleTensorRingPowerComparison S A).app M ≫
    Pi.π (fun _ : A => M) a).hom t) =
      (((ModuleCat.piIsoPi (fun _ : A => M)).inv ≫
        Pi.π (fun _ : A => M) a).hom x) at he
  rwa [moduleTensorRingPowerComparison_comp_pi, ModuleCat.piIsoPi_inv_kernel_ι] at he

private lemma epi_app_homology_of_epi_homologyMap_of_zero_g
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    {F G : C ⥤ D} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [PreservesFiniteColimits F] [PreservesFiniteColimits G]
    (α : F ⟶ G) (L : ShortComplex C) (hL : L.g = 0)
    [Epi (ShortComplex.homologyMap (L.mapNatTrans α))] :
    Epi (α.app L.homology) := by
  let := F.preservesLeftHomology_of_zero_g L hL
  let := F.preservesRightHomology_of_zero_g L hL
  let := G.preservesLeftHomology_of_zero_g L hL
  let := G.preservesRightHomology_of_zero_g L hL
  rw [α.app_homology L]
  infer_instance

private lemma finite_homology_of_epi_tensorRingPowerComparison_of_zero_d
    (S : Type v) [CommRing S] (E : CochainComplex (ModuleCat.{v} S) ℤ)
    (i : ℤ) (hi : E.d i (i + 1) = 0)
    (h : ∀ A : Type v, Epi (ShortComplex.homologyMap
      ((E.sc i).mapNatTrans (moduleTensorRingPowerComparison S A)))) :
    Module.Finite S (E.homology i) := by
  apply finite_of_epi_moduleTensorRingPowerComparison S (E.homology i)
  intro A
  have := h A
  exact epi_app_homology_of_epi_homologyMap_of_zero_g
    (moduleTensorRingPowerComparison S A) (E.sc i) (by
      change E.d i ((ComplexShape.up ℤ).next i) = 0
      rw [ComplexShape.next_eq' _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl)]
      exact hi)

private lemma piComparison_natTrans
    {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (α : F ⟶ G) {A : Type*} (Q : A → C)
    [HasProduct Q] [HasProduct (fun a => F.obj (Q a))]
    [HasProduct (fun a => G.obj (Q a))] :
    piComparison F Q ≫ Limits.Pi.map (fun a => α.app (Q a)) =
      α.app (∏ᶜ Q) ≫ piComparison G Q := by
  apply Pi.hom_ext
  intro a
  simp only [Category.assoc, Pi.map_π, piComparison_comp_π_assoc,
    piComparison_comp_π]
  exact α.naturality (Pi.π Q a)

/-- A natural isomorphism induces an isomorphism on products, compatible with `piComparison`. -/
private lemma isIso_pi_map_and_map_piComparison_comp_of_natIso
    {C D B : Type*} [Category* C] [Category* D] [Category* B]
    {F G : C ⥤ D} (e : F ≅ G) (H : D ⥤ B) {A : Type*} (Q : A → C)
    [HasProduct Q] [HasProduct (fun a => F.obj (Q a))]
    [HasProduct (fun a => G.obj (Q a))] :
    IsIso (Limits.Pi.map (fun a => e.hom.app (Q a))) ∧
      H.map (piComparison F Q) ≫ H.map (Limits.Pi.map (fun a => e.hom.app (Q a))) =
        H.map (e.hom.app (∏ᶜ Q)) ≫ H.map (piComparison G Q) := by
  refine ⟨⟨Limits.Pi.map (fun a => e.inv.app (Q a)), ?_, ?_⟩, ?_⟩
  · apply Pi.hom_ext
    intro a
    simp
  · apply Pi.hom_ext
    intro a
    simp
  · simp only [← Functor.map_comp, piComparison_natTrans]

private lemma isIso_map_piComparison_iff_of_natIso
    {C D B : Type*} [Category* C] [Category* D] [Category* B]
    {F G : C ⥤ D} (e : F ≅ G) (H : D ⥤ B) {A : Type*} (Q : A → C)
    [HasProduct Q] [HasProduct (fun a => F.obj (Q a))]
    [HasProduct (fun a => G.obj (Q a))] :
    IsIso (H.map (piComparison F Q)) ↔ IsIso (H.map (piComparison G Q)) := by
  obtain ⟨hi, h⟩ := isIso_pi_map_and_map_piComparison_comp_of_natIso e H Q
  rw [← isIso_comp_right_iff (H.map (piComparison F Q))
    (H.map (Limits.Pi.map (fun a => e.hom.app (Q a)))), h, isIso_comp_left_iff]

private lemma epi_map_piComparison_iff_of_natIso
    {C D B : Type*} [Category* C] [Category* D] [Category* B]
    {F G : C ⥤ D} (e : F ≅ G) (H : D ⥤ B) {A : Type*} (Q : A → C)
    [HasProduct Q] [HasProduct (fun a => F.obj (Q a))]
    [HasProduct (fun a => G.obj (Q a))] :
    Epi (H.map (piComparison F Q)) ↔ Epi (H.map (piComparison G Q)) := by
  obtain ⟨hi, h⟩ := isIso_pi_map_and_map_piComparison_comp_of_natIso e H Q
  rw [← epi_comp_iff_of_isIso (H.map (piComparison F Q))
    (H.map (Limits.Pi.map (fun a => e.hom.app (Q a)))), h, epi_comp_iff_of_epi]

private lemma isIso_map_iff_of_natIso
    {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (e : F ≅ G) {X Y : C} (f : X ⟶ Y) : IsIso (F.map f) ↔ IsIso (G.map f) := by
  rw [← NatIso.naturality_2 e f, isIso_comp_left_iff, isIso_comp_right_iff]

private lemma homology_tensorProductComparison_iff_of_kFlat
    (R : Type u) [CommRing R] [Small.{max v w} R]
    (T : DerivedTensorProduct.{u, v, w} R) (P : DerivedProducts.{u, v, w} R)
    (E : CochainComplex (ModuleCat.{max v w} (SmallRing.{u, v, w} R)) ℤ)
    (hE : E.KFlat) (A : Type (max v w))
    (Q : A → ModuleCat.{max v w} (SmallRing.{u, v, w} R)) (i : ℤ) :
    (IsIso ((DerivedCategory.homologyFunctor _ i).map
      (tensorProductComparison T P (DerivedCategory.Q.obj E) A Q)) ↔
      IsIso ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) i).map
        (piComparison (tensorWithCochainComplex E) Q))) ∧
    (Epi ((DerivedCategory.homologyFunctor _ i).map
      (tensorProductComparison T P (DerivedCategory.Q.obj E) A Q)) ↔
      Epi ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) i).map
        (piComparison (tensorWithCochainComplex E) Q))) := by
  let C := ModuleCat.{max v w} (SmallRing.{u, v, w} R)
  let c := CochainComplex.singleFunctor C 0
  let d := DerivedCategory.singleFunctor C 0
  let F := T.tensor.obj (DerivedCategory.Q.obj E)
  let G := tensorWithCochainComplex E
  let H := DerivedCategory.homologyFunctor C i
  let := hasProductsOfShape R P A
  let := preservesProducts_singleFunctor.{u, v, w} R A
  let : PreservesLimitsOfShape (Discrete A) (DerivedCategory.Q (C := C)) :=
    Stacks.DerivedProducts.preservesLimitsOfShape_Q
  let := isIso_derivedTensorComparison_of_kFlat R T E hE
  let e : d ⋙ F ≅ G ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerLeft c (asIso (T.comparison E))
  have h₁ : H.map (piComparison (d ⋙ F) Q) =
      H.map (F.map (piComparison d Q)) ≫
        H.map (tensorProductComparison T P (DerivedCategory.Q.obj E) A Q) := by
    rw [Stacks.DerivedProducts.piComparison_comp_eq, Functor.map_comp]
    rfl
  have h₂ : H.map (piComparison (G ⋙ DerivedCategory.Q) Q) =
      H.map (DerivedCategory.Q.map (piComparison G Q)) ≫
        H.map (piComparison DerivedCategory.Q (fun a => G.obj (Q a))) := by
    rw [Stacks.DerivedProducts.piComparison_comp_eq, Functor.map_comp]
  have he := DerivedCategory.homologyFunctorFactors C i
  constructor
  · rw [← isIso_comp_left_iff (H.map (F.map (piComparison d Q))), ← h₁,
      isIso_map_piComparison_iff_of_natIso e H Q, h₂, isIso_comp_right_iff]
    exact isIso_map_iff_of_natIso he (piComparison G Q)
  · rw [← epi_comp_iff_of_epi (H.map (F.map (piComparison d Q))), ← h₁,
      epi_map_piComparison_iff_of_natIso e H Q, h₂, epi_comp_iff_of_isIso]
    exact epi_map_iff_of_natIso he (piComparison G Q)

private lemma tensorRingPowerComparison_eq
    (R : Type u) [CommRing R] [Small.{max v w} R]
    (T : DerivedTensorProduct.{u, v, w} R) (P : DerivedProducts.{u, v, w} R) (K : D.{u, v, w} R)
    (A : Type (max v w)) :
    let : HasProductsOfShape A (D.{u, v, w} R) := hasProductsOfShape R P A
    tensorRingPowerComparison T P K A =
      tensorPowerComparison T P K A (ModuleCat.of (SmallRing.{u, v, w} R) (SmallRing.{u, v, w} R)) ≫
        Limits.Pi.map (fun _ : A => T.unitIso.hom.app K) := by
  let := hasProductsOfShape R P A
  apply Pi.hom_ext
  intro a
  simp [tensorRingPowerComparison, tensorPowerComparison,
    tensorProductComparison, Category.assoc]

private lemma isIso_tensorRingPowerComparison_of_isIso_tensorPowerComparison
    (R : Type u) [CommRing R] [Small.{max v w} R]
    (T : DerivedTensorProduct.{u, v, w} R) (P : DerivedProducts.{u, v, w} R) (K : D.{u, v, w} R)
    (h : ∀ (A : Type (max v w)) (Q : ModuleCat.{max v w} (SmallRing.{u, v, w} R)),
      IsIso (tensorPowerComparison T P K A Q))
    (A : Type (max v w)) : IsIso (tensorRingPowerComparison T P K A) := by
  let := hasProductsOfShape R P A
  rw [tensorRingPowerComparison_eq R T P K A]
  let : IsIso (tensorPowerComparison T P K A
      (ModuleCat.of (SmallRing.{u, v, w} R) (SmallRing.{u, v, w} R))) := h A _
  infer_instance

private lemma homologyRange_tensorRingPowerComparison_iff
    (R : Type u) [CommRing R] [Small.{max v w} R]
    (T : DerivedTensorProduct.{u, v, w} R) (P : DerivedProducts.{u, v, w} R)
    (K : D.{u, v, w} R) (m : ℤ)
    (A : Type (max v w)) :
    ((∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor _ i).map
      (tensorRingPowerComparison T P K A))) ∧
      Epi ((DerivedCategory.homologyFunctor _ m).map
        (tensorRingPowerComparison T P K A))) ↔
    ((∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor _ i).map
      (tensorPowerComparison T P K A
        (ModuleCat.of (SmallRing.{u, v, w} R) (SmallRing.{u, v, w} R))))) ∧
      Epi ((DerivedCategory.homologyFunctor _ m).map
        (tensorPowerComparison T P K A
          (ModuleCat.of (SmallRing.{u, v, w} R) (SmallRing.{u, v, w} R))))) := by
  let := hasProductsOfShape R P A
  rw [tensorRingPowerComparison_eq R T P K A]
  simp only [Functor.map_comp, isIso_comp_right_iff, epi_comp_iff_of_isIso]

private lemma homologyRange_tensorRingPowerComparison_of_homologyRange_tensorPowerComparison
    (R : Type u) [CommRing R] [Small.{max v w} R]
    (T : DerivedTensorProduct.{u, v, w} R) (P : DerivedProducts.{u, v, w} R)
    (K : D.{u, v, w} R) (m : ℤ)
    (h : ∀ (A : Type (max v w)) (Q : ModuleCat.{max v w} (SmallRing.{u, v, w} R)),
      (∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor _ i).map
        (tensorPowerComparison T P K A Q))) ∧
      Epi ((DerivedCategory.homologyFunctor _ m).map
        (tensorPowerComparison T P K A Q)))
    (A : Type (max v w)) :
    (∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor _ i).map
      (tensorRingPowerComparison T P K A))) ∧
    Epi ((DerivedCategory.homologyFunctor _ m).map
      (tensorRingPowerComparison T P K A)) :=
  (homologyRange_tensorRingPowerComparison_iff R T P K m A).mpr (h A _)

private theorem solution_of_core
    (R : Type u) [CommRing R] [Small.{max v w} R]
    (T : DerivedTensorProduct.{u, v, w} R) (P : DerivedProducts.{u, v, w} R)
    (K : DerivedCategory.Minus (ModuleCat.{max v w} (SmallRing.{u, v, w} R))) (m : ℤ)
    (hpc : IsPseudoCoherent K.obj →
      ∀ (A : Type (max v w)) (Q : A → ModuleCat.{max v w} (SmallRing.{u, v, w} R)),
        IsIso (tensorProductComparison T P K.obj A Q))
    (hpc_rev : (∀ A : Type (max v w), IsIso (tensorRingPowerComparison T P K.obj A)) →
      IsPseudoCoherent K.obj)
    (hm : IsPseudoCoherentFrom K.obj m →
      ∀ (A : Type (max v w)) (Q : A → ModuleCat.{max v w} (SmallRing.{u, v, w} R)),
        (∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor _ i).map
          (tensorProductComparison T P K.obj A Q))) ∧
        Epi ((DerivedCategory.homologyFunctor _ m).map
          (tensorProductComparison T P K.obj A Q)))
    (hm_rev : (∀ A : Type (max v w),
      (∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor _ i).map
        (tensorRingPowerComparison T P K.obj A))) ∧
      Epi ((DerivedCategory.homologyFunctor _ m).map
        (tensorRingPowerComparison T P K.obj A))) →
      IsPseudoCoherentFrom K.obj m) :
    List.TFAE [
      IsPseudoCoherent K.obj,
      ∀ (A : Type (max v w)) (Q : A → ModuleCat.{max v w} (SmallRing.{u, v, w} R)),
        IsIso (tensorProductComparison T P K.obj A Q),
      ∀ (A : Type (max v w)) (Q : ModuleCat.{max v w} (SmallRing.{u, v, w} R)),
        IsIso (tensorPowerComparison T P K.obj A Q),
      ∀ A : Type (max v w), IsIso (tensorRingPowerComparison T P K.obj A)] ∧
    List.TFAE [
      IsPseudoCoherentFrom K.obj m,
      ∀ (A : Type (max v w)) (Q : A → ModuleCat.{max v w} (SmallRing.{u, v, w} R)),
        (∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor _ i).map
          (tensorProductComparison T P K.obj A Q))) ∧
        Epi ((DerivedCategory.homologyFunctor _ m).map
          (tensorProductComparison T P K.obj A Q)),
      ∀ (A : Type (max v w)) (Q : ModuleCat.{max v w} (SmallRing.{u, v, w} R)),
        (∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor _ i).map
          (tensorPowerComparison T P K.obj A Q))) ∧
        Epi ((DerivedCategory.homologyFunctor _ m).map
          (tensorPowerComparison T P K.obj A Q)),
      ∀ A : Type (max v w),
        (∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor _ i).map
          (tensorRingPowerComparison T P K.obj A))) ∧
        Epi ((DerivedCategory.homologyFunctor _ m).map
          (tensorRingPowerComparison T P K.obj A))] := by
  constructor
  · tfae_have 1 → 2 := hpc
    tfae_have 2 → 3 :=
      isIso_tensorPowerComparison_of_isIso_tensorProductComparison R T P K.obj
    tfae_have 3 → 4 :=
      isIso_tensorRingPowerComparison_of_isIso_tensorPowerComparison R T P K.obj
    tfae_have 4 → 1 := hpc_rev
    tfae_finish
  · tfae_have 1 → 2 := hm
    tfae_have 2 → 3 :=
      homologyRange_tensorPowerComparison_of_homologyRange_tensorProductComparison
        R T P K.obj m
    tfae_have 3 → 4 :=
      homologyRange_tensorRingPowerComparison_of_homologyRange_tensorPowerComparison
        R T P K.obj m
    tfae_have 4 → 1 := hm_rev
    tfae_finish

end StacksDraft.PseudoCoherence
