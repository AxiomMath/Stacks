module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Module.Amitsur

/-!
# Exactness of the Amitsur complex of a faithfully flat algebra

For a faithfully flat algebra `A` over a commutative ring `R` and an arbitrary `R`-module `M`,
the extended Amitsur cochain complex
`M → A ⊗[R] M → A ⊗[R] A ⊗[R] M → ⋯`
is exact in every degree.

The argument is descent along `R → A` itself. Exactness is a statement about a complex of
`R`-modules which, because `A` is faithfully flat over `R`, may be tested after applying
`A ⊗[R] -`. The base change of the Amitsur complex of `R → A` is, by a chain of canonical
identifications, the Amitsur complex of `A → A ⊗[R] A` with coefficients in `A ⊗[R] M`; and
that algebra map has a section, namely multiplication, so its Amitsur complex is exact by the
split case.

## Main results

* `AlgebraicTopology.amitsurExtendedCochainComplex_acyclic_of_faithfullyFlat`: exactness of the
  extended Amitsur complex in every degree, including the augmentation term.

## Implementation notes

The rings and the coefficient module have independent universes and the Amitsur complex of
`AlgebraicTopology.amitsurExtendedCochainComplex` uses canonical universe lifts internally to
place its terms in one module category, so the chain of comparison isomorphisms has to carry
those lifts along. The three steps are kept separate:

* `baseChangeFunctor R A` is `A ⊗[R] -` as an additive functor `ModuleCat R ⥤ ModuleCat A`,
  and `acyclic_of_baseChangeFunctor_iso` is faithfully flat descent of exactness along it.
* `algebraBaseChange T S` is base change of commutative algebras, used to move the Čech
  conerve of `R → A` to the Čech conerve of `A → A ⊗[R] A`. The comparisons for the Čech
  conerve of an arrow under a colimit-preserving functor, for the augmented conerve, and for
  the extended alternating coface complex under an additive functor, are each stated in the
  generality in which they are proved.
* `coefficientBaseChangeNatIso` is the natural isomorphism of coefficient functors, which is
  the distributivity `A ⊗[R] (B ⊗[R] M) ≃ (A ⊗[R] B) ⊗[A] (A ⊗[R] M)` of scalar extension over
  the tensor product with the coefficient module, transported across the universe lifts.

Several comparisons are stated with their universe lifts and ring instances pinned down by
`letI`, because the two sides carry `Algebra` instances arising in different ways from the same
ring map; `tensorProductAlgEquivOfAlgebraEq` and `tensorProductRingEquivOfAlgebraEq` are the
devices that transport a tensor product along an equality of such instances.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u v w z u₁ u₂ v₁ v₂

namespace AlgebraicTopology

section FaithfullyFlatDescent

/-- Base change of modules along `R → A`, as a functor `ModuleCat R ⥤ ModuleCat A`. -/
private def baseChangeFunctor
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A] :
    ModuleCat R ⥤ ModuleCat A where
  obj X := ModuleCat.of A (TensorProduct R A X)
  map f := ModuleCat.ofHom (f.hom.baseChange A)
  map_id _ := ModuleCat.hom_ext LinearMap.baseChange_id
  map_comp f g := ModuleCat.hom_ext (LinearMap.baseChange_comp (A := A) (f := f.hom) g.hom)

private instance baseChangeFunctor_preservesZeroMorphisms
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A] :
    (baseChangeFunctor R A).PreservesZeroMorphisms where
  map_zero _ _ := ModuleCat.hom_ext LinearMap.baseChange_zero

private instance baseChangeFunctor_additive
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A] :
    (baseChangeFunctor R A).Additive where
  map_add := ModuleCat.hom_ext (LinearMap.baseChange_add _ _)

/-- A cochain complex of modules over a ring is exact once it becomes exact after tensoring
with a faithfully flat algebra. -/
@[sga "4½ Arcata 1.4.2" "more general"]
private theorem acyclic_of_lTensor_exact
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    [Module.FaithfullyFlat R A]
    (K : CochainComplex (ModuleCat.{w} R) ℕ)
    (h : ∀ i, Function.Exact
      (LinearMap.lTensor A (K.sc i).f.hom)
      (LinearMap.lTensor A (K.sc i).g.hom)) : K.Acyclic :=
  fun i => (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
    (K.sc i)).2
      ((Module.FaithfullyFlat.lTensor_exact_iff_exact R A
        (K.sc i).f.hom (K.sc i).g.hom).1 (h i))

/-- A cochain complex of modules over a ring is exact once its base change along a faithfully
flat algebra is exact. -/
@[sga "4½ Arcata 1.4.2" "more general"]
private theorem acyclic_of_baseChangeFunctor_acyclic
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    [Module.FaithfullyFlat R A] (K : CochainComplex (ModuleCat R) ℕ)
    (h : (((baseChangeFunctor R A).mapHomologicalComplex _).obj K).Acyclic) :
    K.Acyclic := by
  apply acyclic_of_lTensor_exact R A K
  intro i
  have hi :=
    (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (h i)
  change Function.Exact ((K.sc i).f.hom.baseChange A)
    ((K.sc i).g.hom.baseChange A) at hi
  simpa only [LinearMap.baseChange_eq_ltensor] using hi

/-- A cochain complex of modules over a ring is exact once its base change along a faithfully
flat algebra is isomorphic to an exact complex. -/
@[sga "4½ Arcata 1.4.2" "more general"]
private theorem acyclic_of_baseChangeFunctor_iso
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    [Module.FaithfullyFlat R A] (K : CochainComplex (ModuleCat R) ℕ)
    (L : CochainComplex (ModuleCat A) ℕ)
    (e : (((baseChangeFunctor R A).mapHomologicalComplex _).obj K) ≅ L)
    (hL : L.Acyclic) : K.Acyclic :=
  acyclic_of_baseChangeFunctor_acyclic R A K (fun i => (hL i).of_iso e.symm)

end FaithfullyFlatDescent

section SplitCase

/-- Multiplication is a section of the base change `A → A ⊗[R] A`. -/
private theorem nonempty_algHom_tensorProduct_self
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A] :
    Nonempty (TensorProduct R A A →ₐ[A] A) :=
  ⟨Algebra.TensorProduct.lmul'' R⟩

/-- Multiplication composed with the inclusion of the left factor is the identity. -/
private theorem lmul_comp_includeLeft
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A] :
    (Algebra.TensorProduct.lmul'' R).comp
      (Algebra.TensorProduct.includeLeft : A →ₐ[A] TensorProduct R A A) =
      AlgHom.id A A := by
  ext

/-- The Amitsur complex of `A → A ⊗[R] A` is exact, because that algebra map has a section. -/
private theorem acyclic_amitsur_tensorProduct_self
    (R : Type u) (A : Type v) (M : Type w)
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] :
    (amitsurExtendedCochainComplex A (TensorProduct R A A)
      (TensorProduct R A M)).Acyclic :=
  amitsurExtendedCochainComplex_acyclic_of_section
    A (TensorProduct R A A) (TensorProduct R A M) (nonempty_algHom_tensorProduct_self R A)

/-- The Amitsur complex of `A → ULift (A ⊗[R] A)` is exact, because that algebra map has a
section. -/
private theorem acyclic_amitsur_ulift_tensorProduct_self
    (R : Type u) (A : Type v) (M : Type w)
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] :
    (amitsurExtendedCochainComplex A
      (ULift.{u} (TensorProduct R A A))
      (TensorProduct R A M)).Acyclic :=
  amitsurExtendedCochainComplex_acyclic_of_section _ _ _
    ⟨(Algebra.TensorProduct.lmul'' R).comp ULift.algEquiv.toAlgHom⟩

end SplitCase

section CechComparison

/-- Distributivity of scalar extension over the tensor product with the coefficient module. -/
private def tensorDistribBaseChange
    (R : Type u) (A : Type v) (B : Type*) (M : Type w)
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup B] [Module R B] [AddCommGroup M] [Module R M] :
    A ⊗[R] (B ⊗[R] M) ≃ₗ[A] (A ⊗[R] B) ⊗[A] (A ⊗[R] M) :=
  TensorProduct.AlgebraTensorModule.distribBaseChange R A B M

private theorem tensorDistribBaseChange_naturality
    (R : Type u) (A : Type v) (B C : Type*) (M : Type w)
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    [AddCommGroup M] [Module R M] (f : B →ₗ[R] C) :
    (LinearMap.baseChange A (f.rTensor M)) ∘ₗ
      (tensorDistribBaseChange R A B M).symm.toLinearMap =
    (tensorDistribBaseChange R A C M).symm.toLinearMap ∘ₗ
      (f.baseChange A).rTensor (A ⊗[R] M) := by
  ext a b
  rfl

/-- Base change of commutative algebras along `T → S`. -/
private def algebraBaseChange
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    CommAlgCat.{u} R ⥤ CommAlgCat.{u} S :=
  (commAlgCatEquivUnder (.of R)).functor ⋙
    CommRingCat.tensorProd (.of R) (.of S) ⋙
      (commAlgCatEquivUnder (.of S)).inverse

private instance algebraBaseChange_preservesColimits
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    CategoryTheory.Limits.PreservesColimits (algebraBaseChange R S) := by
  let : (CommRingCat.tensorProd (.of R) (.of S)).IsLeftAdjoint :=
    Functor.isLeftAdjoint_of_iso
      (CommRingCat.tensorProdIsoPushout (.of R) (.of S)).symm
  dsimp [algebraBaseChange]
  infer_instance

/-- A colimit-preserving functor commutes with wide pushouts. -/
private noncomputable def widePushoutMapIso
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    {B : C} {J : Type*} {objs : J → C} (arrows : ∀ j, B ⟶ objs j)
    [CategoryTheory.Limits.HasWidePushout B objs arrows]
    [CategoryTheory.Limits.HasWidePushout (F.obj B) (fun j => F.obj (objs j))
      (fun j => F.map (arrows j))]
    [CategoryTheory.Limits.PreservesColimitsOfShape
      (CategoryTheory.Limits.WidePushoutShape J) F] :
    F.obj (CategoryTheory.Limits.widePushout B objs arrows) ≅
      CategoryTheory.Limits.widePushout (F.obj B) (fun j => F.obj (objs j))
        (fun j => F.map (arrows j)) := by
  let K := CategoryTheory.Limits.WidePushoutShape.wideSpan B objs arrows
  exact (preservesColimitIso F K).trans
    (CategoryTheory.Limits.HasColimit.isoOfNatIso
      (CategoryTheory.Limits.WidePushoutShape.diagramIsoWideSpan (K ⋙ F)))

private theorem widePushoutMapIso_head
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    {B : C} {J : Type*} {objs : J → C} (arrows : ∀ j, B ⟶ objs j)
    [CategoryTheory.Limits.HasWidePushout B objs arrows]
    [CategoryTheory.Limits.HasWidePushout (F.obj B) (fun j => F.obj (objs j))
      (fun j => F.map (arrows j))]
    [CategoryTheory.Limits.PreservesColimitsOfShape
      (CategoryTheory.Limits.WidePushoutShape J) F] :
    F.map (CategoryTheory.Limits.WidePushout.head arrows) ≫
      (widePushoutMapIso F arrows).hom =
        CategoryTheory.Limits.WidePushout.head (fun j => F.map (arrows j)) := by
  simp [widePushoutMapIso, CategoryTheory.Limits.HasColimit.isoOfNatIso_ι_hom,
    CategoryTheory.Limits.WidePushoutShape.diagramIsoWideSpan]

private theorem widePushoutMapIso_ι
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    {B : C} {J : Type*} {objs : J → C} (arrows : ∀ j, B ⟶ objs j)
    [CategoryTheory.Limits.HasWidePushout B objs arrows]
    [CategoryTheory.Limits.HasWidePushout (F.obj B) (fun j => F.obj (objs j))
      (fun j => F.map (arrows j))]
    [CategoryTheory.Limits.PreservesColimitsOfShape
      (CategoryTheory.Limits.WidePushoutShape J) F]
    (j : J) :
    F.map (CategoryTheory.Limits.WidePushout.ι arrows j) ≫
      (widePushoutMapIso F arrows).hom =
        CategoryTheory.Limits.WidePushout.ι (fun j => F.map (arrows j)) j := by
  simp [widePushoutMapIso, CategoryTheory.Limits.HasColimit.isoOfNatIso_ι_hom,
    CategoryTheory.Limits.WidePushoutShape.diagramIsoWideSpan]

private theorem widePushoutMap_hom_ext
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    {B : C} {J : Type*} {objs : J → C} (arrows : ∀ j, B ⟶ objs j)
    [CategoryTheory.Limits.HasWidePushout B objs arrows]
    [CategoryTheory.Limits.HasWidePushout (F.obj B) (fun j => F.obj (objs j))
      (fun j => F.map (arrows j))]
    [CategoryTheory.Limits.PreservesColimitsOfShape
      (CategoryTheory.Limits.WidePushoutShape J) F]
    {X : D} (g h : F.obj (CategoryTheory.Limits.widePushout B objs arrows) ⟶ X)
    (hι : ∀ j, F.map (CategoryTheory.Limits.WidePushout.ι arrows j) ≫ g =
      F.map (CategoryTheory.Limits.WidePushout.ι arrows j) ≫ h)
    (hhead : F.map (CategoryTheory.Limits.WidePushout.head arrows) ≫ g =
      F.map (CategoryTheory.Limits.WidePushout.head arrows) ≫ h) : g = h := by
  rw [← cancel_epi (widePushoutMapIso F arrows).inv]
  apply CategoryTheory.Limits.WidePushout.hom_ext
  · intro j
    rw [← widePushoutMapIso_ι F arrows j]
    simpa using hι j
  · rw [← widePushoutMapIso_head F arrows]
    simpa using hhead

private instance hasWidePushout_mapArrow
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) (f : Arrow C)
    [∀ n : ℕ, CategoryTheory.Limits.HasWidePushout (F.obj f.left)
      (fun _ : Fin (n + 1) => F.obj f.right) (fun _ => F.map f.hom)] :
    ∀ n : ℕ, CategoryTheory.Limits.HasWidePushout (Arrow.mk (F.map f.hom)).left
      (fun _ : Fin (n + 1) => (Arrow.mk (F.map f.hom)).right)
      (fun _ => (Arrow.mk (F.map f.hom)).hom) := by
  intro n
  change CategoryTheory.Limits.HasWidePushout (F.obj f.left)
    (fun _ : Fin (n + 1) => F.obj f.right) (fun _ => F.map f.hom)
  infer_instance

/-- The inclusion of the `i`-th copy of `f.right` into a term of the Čech conerve of `f`.

This is `CategoryTheory.Limits.WidePushout.ι` with its codomain stated as a term of the Čech
conerve; keeping that one spelling is what lets the comparison isomorphism below be proved by
rewriting. -/
private noncomputable def cechConerveι
    {C : Type u₁} [Category.{v₁} C] (f : Arrow C)
    [∀ n : ℕ, CategoryTheory.Limits.HasWidePushout f.left
      (fun _ : Fin (n + 1) => f.right) (fun _ => f.hom)]
    (n : SimplexCategory) (i : Fin (n.len + 1)) : f.right ⟶ f.cechConerve.obj n :=
  CategoryTheory.Limits.WidePushout.ι (fun _ : Fin (n.len + 1) => f.hom) i

/-- The map from `f.left` to a term of the Čech conerve of `f`, in the same spelling as
`AlgebraicTopology.cechConerveι`. -/
private noncomputable def cechConerveHead
    {C : Type u₁} [Category.{v₁} C] (f : Arrow C)
    [∀ n : ℕ, CategoryTheory.Limits.HasWidePushout f.left
      (fun _ : Fin (n + 1) => f.right) (fun _ => f.hom)]
    (n : SimplexCategory) : f.left ⟶ f.cechConerve.obj n :=
  CategoryTheory.Limits.WidePushout.head (fun _ : Fin (n.len + 1) => f.hom)

private theorem cechConerveι_map
    {C : Type u₁} [Category.{v₁} C] (f : Arrow C)
    [∀ n : ℕ, CategoryTheory.Limits.HasWidePushout f.left
      (fun _ : Fin (n + 1) => f.right) (fun _ => f.hom)]
    {X Y : SimplexCategory} (g : X ⟶ Y) (i : Fin (X.len + 1)) :
    cechConerveι f X i ≫ f.cechConerve.map g = cechConerveι f Y (g.toOrderHom i) :=
  CategoryTheory.Limits.WidePushout.ι_desc _ _ _ _ i

private theorem cechConerveHead_map
    {C : Type u₁} [Category.{v₁} C] (f : Arrow C)
    [∀ n : ℕ, CategoryTheory.Limits.HasWidePushout f.left
      (fun _ : Fin (n + 1) => f.right) (fun _ => f.hom)]
    {X Y : SimplexCategory} (g : X ⟶ Y) :
    cechConerveHead f X ≫ f.cechConerve.map g = cechConerveHead f Y :=
  CategoryTheory.Limits.WidePushout.head_desc _ _ _ _

/-- The component at `n` of the comparison between the image of the Čech conerve and the Čech
conerve of the image. -/
private noncomputable def cechConerveMapIsoApp
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) (f : Arrow C)
    [∀ n : ℕ, CategoryTheory.Limits.HasWidePushout f.left
      (fun _ : Fin (n + 1) => f.right) (fun _ => f.hom)]
    [∀ n : ℕ, CategoryTheory.Limits.HasWidePushout (F.obj f.left)
      (fun _ : Fin (n + 1) => F.obj f.right) (fun _ => F.map f.hom)]
    [∀ n : ℕ, CategoryTheory.Limits.PreservesColimitsOfShape
      (CategoryTheory.Limits.WidePushoutShape (Fin (n + 1))) F]
    (n : SimplexCategory) :
    F.obj (f.cechConerve.obj n) ≅ (Arrow.mk (F.map f.hom)).cechConerve.obj n :=
  widePushoutMapIso F (fun _ : Fin (n.len + 1) => f.hom)

private theorem cechConerveι_cechConerveMapIsoApp
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) (f : Arrow C)
    [∀ n : ℕ, CategoryTheory.Limits.HasWidePushout f.left
      (fun _ : Fin (n + 1) => f.right) (fun _ => f.hom)]
    [∀ n : ℕ, CategoryTheory.Limits.HasWidePushout (F.obj f.left)
      (fun _ : Fin (n + 1) => F.obj f.right) (fun _ => F.map f.hom)]
    [∀ n : ℕ, CategoryTheory.Limits.PreservesColimitsOfShape
      (CategoryTheory.Limits.WidePushoutShape (Fin (n + 1))) F]
    (n : SimplexCategory) (i : Fin (n.len + 1)) :
    F.map (cechConerveι f n i) ≫ (cechConerveMapIsoApp F f n).hom =
      cechConerveι (Arrow.mk (F.map f.hom)) n i :=
  widePushoutMapIso_ι F (fun _ : Fin (n.len + 1) => f.hom) i

private theorem cechConerveHead_cechConerveMapIsoApp
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) (f : Arrow C)
    [∀ n : ℕ, CategoryTheory.Limits.HasWidePushout f.left
      (fun _ : Fin (n + 1) => f.right) (fun _ => f.hom)]
    [∀ n : ℕ, CategoryTheory.Limits.HasWidePushout (F.obj f.left)
      (fun _ : Fin (n + 1) => F.obj f.right) (fun _ => F.map f.hom)]
    [∀ n : ℕ, CategoryTheory.Limits.PreservesColimitsOfShape
      (CategoryTheory.Limits.WidePushoutShape (Fin (n + 1))) F]
    (n : SimplexCategory) :
    F.map (cechConerveHead f n) ≫ (cechConerveMapIsoApp F f n).hom =
      cechConerveHead (Arrow.mk (F.map f.hom)) n :=
  widePushoutMapIso_head F (fun _ : Fin (n.len + 1) => f.hom)

private theorem cechConerveMap_hom_ext
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) (f : Arrow C)
    [∀ n : ℕ, CategoryTheory.Limits.HasWidePushout f.left
      (fun _ : Fin (n + 1) => f.right) (fun _ => f.hom)]
    [∀ n : ℕ, CategoryTheory.Limits.HasWidePushout (F.obj f.left)
      (fun _ : Fin (n + 1) => F.obj f.right) (fun _ => F.map f.hom)]
    [∀ n : ℕ, CategoryTheory.Limits.PreservesColimitsOfShape
      (CategoryTheory.Limits.WidePushoutShape (Fin (n + 1))) F]
    (n : SimplexCategory) {Z : D} (p q : F.obj (f.cechConerve.obj n) ⟶ Z)
    (hι : ∀ i, F.map (cechConerveι f n i) ≫ p = F.map (cechConerveι f n i) ≫ q)
    (hhead : F.map (cechConerveHead f n) ≫ p = F.map (cechConerveHead f n) ≫ q) : p = q :=
  widePushoutMap_hom_ext F (fun _ : Fin (n.len + 1) => f.hom) p q hι hhead

private theorem whiskering_obj_cechConerve_map
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) (f : Arrow C)
    [∀ n : ℕ, CategoryTheory.Limits.HasWidePushout f.left
      (fun _ : Fin (n + 1) => f.right) (fun _ => f.hom)]
    {X Y : SimplexCategory} (g : X ⟶ Y) :
    (((CosimplicialObject.whiskering C D).obj F).obj f.cechConerve).map g =
      F.map (f.cechConerve.map g) :=
  rfl

/-- A colimit-preserving functor carries the Čech conerve of an arrow to the Čech conerve of
its image. -/
private noncomputable def cechConerveMapIso
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) (f : Arrow C)
    [∀ n : ℕ, CategoryTheory.Limits.HasWidePushout f.left
      (fun _ : Fin (n + 1) => f.right) (fun _ => f.hom)]
    [∀ n : ℕ, CategoryTheory.Limits.HasWidePushout (F.obj f.left)
      (fun _ : Fin (n + 1) => F.obj f.right) (fun _ => F.map f.hom)]
    [∀ n : ℕ, CategoryTheory.Limits.PreservesColimitsOfShape
      (CategoryTheory.Limits.WidePushoutShape (Fin (n + 1))) F] :
    ((CosimplicialObject.whiskering C D).obj F).obj f.cechConerve ≅
      (Arrow.mk (F.map f.hom)).cechConerve :=
  NatIso.ofComponents (cechConerveMapIsoApp F f) (by
    intro X Y g
    refine cechConerveMap_hom_ext F f X _ _ (fun i => ?_) ?_
    · rw [whiskering_obj_cechConerve_map, ← Category.assoc, ← F.map_comp, cechConerveι_map,
        ← Category.assoc, cechConerveι_cechConerveMapIsoApp,
        cechConerveι_cechConerveMapIsoApp, cechConerveι_map]
    · rw [whiskering_obj_cechConerve_map, ← Category.assoc, ← F.map_comp, cechConerveHead_map,
        ← Category.assoc, cechConerveHead_cechConerveMapIsoApp,
        cechConerveHead_cechConerveMapIsoApp, cechConerveHead_map])

/-- A colimit-preserving functor carries the augmented Čech conerve of an arrow to the
augmented Čech conerve of its image. -/
private noncomputable def augmentedCechConerveMapIso
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) (f : Arrow C)
    [∀ n : ℕ, CategoryTheory.Limits.HasWidePushout f.left
      (fun _ : Fin (n + 1) => f.right) (fun _ => f.hom)]
    [∀ n : ℕ, CategoryTheory.Limits.HasWidePushout (F.obj f.left)
      (fun _ : Fin (n + 1) => F.obj f.right) (fun _ => F.map f.hom)]
    [∀ n : ℕ, CategoryTheory.Limits.PreservesColimitsOfShape
      (CategoryTheory.Limits.WidePushoutShape (Fin (n + 1))) F] :
    (CosimplicialObject.Augmented.whiskeringObj C D F).obj f.augmentedCechConerve ≅
      (Arrow.mk (F.map f.hom)).augmentedCechConerve := by
  refine Comma.isoMk (Iso.refl _) (cechConerveMapIso F f) ?_
  ext n
  exact (Category.id_comp _).trans
    ((cechConerveHead_cechConerveMapIsoApp F f n).symm.trans
      (congrArg (· ≫ (cechConerveMapIsoApp F f n).hom) (Category.id_comp _).symm))

/-- An isomorphism of augmented cosimplicial objects compatible with maps into their
augmentation objects induces an isomorphism of extended alternating coface complexes. -/
private def extendedAlternatingCofaceMapComplexIso
    {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    (X Y : CosimplicialObject.Augmented C) (e : X ≅ Y)
    (U V : C) (u : U ⟶ X.left) (v : V ⟶ Y.left)
    (e₀ : U ≅ V) (h : e₀.hom ≫ v = u ≫ e.hom.left) :
    extendedAlternatingCofaceMapComplex X U u ≅
      extendedAlternatingCofaceMapComplex Y V v := by
  let e₁ := (AlgebraicTopology.alternatingCofaceMapComplex C).mapIso
    (CategoryTheory.CosimplicialObject.Augmented.drop.mapIso e)
  refine HomologicalComplex.Hom.isoOfComponents
    (fun | 0 => e₀ | i + 1 => HomologicalComplex.Hom.isoApp e₁ i) ?_
  intro i j hij
  rcases i with _ | i <;> rcases j with _ | j
  · simp at hij
  · cases j
    · change e₀.hom ≫ (v ≫ Y.hom.app (.mk 0)) =
        (u ≫ X.hom.app (.mk 0)) ≫ e.hom.right.app (.mk 0)
      rw [reassoc_of% h, CosimplicialObject.Augmented.w_app (η := e.hom) (n := .mk 0),
        Category.assoc]
    · simp [ComplexShape.up_Rel] at hij
  · simp at hij
  · change (e₁.hom.f i) ≫ _ = _ ≫ (e₁.hom.f j)
    exact e₁.hom.comm i j

private theorem alternatingCofaceMapComplex_d
    {C : Type u₁} [Category.{v₁} C] [Preadditive C] (Z : CosimplicialObject C) (n : ℕ) :
    ((alternatingCofaceMapComplex C).obj Z).d n (n + 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • Z.δ i :=
  CochainComplex.of_d (fun m => Z.obj (SimplexCategory.mk m))
    (AlternatingCofaceMapComplex.objD Z) n

/-- An additive functor commutes with the differential of the alternating coface map complex.

Stated at the level of the differentials rather than proved inside
`AlgebraicTopology.mapExtendedAlternatingCofaceMapComplexIso`, because the equation has to be
crossed in term mode: its two sides spell the ambient object differently. -/
private theorem map_alternatingCofaceMapComplex_d
    {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D] (F : C ⥤ D) [F.Additive]
    (Z : CosimplicialObject C) (n : ℕ) :
    ((alternatingCofaceMapComplex D).obj
        (((CosimplicialObject.whiskering C D).obj F).obj Z)).d n (n + 1) =
      F.map (((alternatingCofaceMapComplex C).obj Z).d n (n + 1)) := by
  have hL : ((alternatingCofaceMapComplex D).obj
      (((CosimplicialObject.whiskering C D).obj F).obj Z)).d n (n + 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • F.map (Z.δ i) :=
    alternatingCofaceMapComplex_d _ n
  have hsum : (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • F.map (Z.δ i)) =
      F.map (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • Z.δ i) := by
    rw [F.map_sum]
    exact Finset.sum_congr rfl fun i _ => F.map_zsmul.symm
  exact hL.trans (hsum.trans (congrArg F.map (alternatingCofaceMapComplex_d Z n).symm))

private theorem whiskeringObj_hom_app
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    (X : CosimplicialObject.Augmented C) (n : SimplexCategory) :
    ((CosimplicialObject.Augmented.whiskeringObj C D F).obj X).hom.app n =
      F.map (X.hom.app n) :=
  Category.id_comp _

/-- An additive functor commutes with the extended alternating coface complex. -/
private noncomputable def mapExtendedAlternatingCofaceMapComplexIso
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive]
    (X : CosimplicialObject.Augmented C) (Y : C) (e : Y ⟶ X.left) :
    ((F.mapHomologicalComplex _).obj (extendedAlternatingCofaceMapComplex X Y e)) ≅
        extendedAlternatingCofaceMapComplex
          ((CosimplicialObject.Augmented.whiskeringObj C D F).obj X)
          (F.obj Y) (F.map e) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i => match i with
      | 0 => Iso.refl (F.obj Y)
      | n + 1 => Iso.refl (F.obj (X.right.obj (.mk n)))) ?_
  intro i j hij
  rcases i with _ | i <;> rcases j with _ | j
  · simp at hij
  · cases j
    · exact (Category.id_comp _).trans
        ((congrArg (F.map e ≫ ·) (whiskeringObj_hom_app F X (.mk 0))).trans
          (((F.map_comp e (X.hom.app (.mk 0))).symm).trans (Category.comp_id _).symm))
    · simp [ComplexShape.up_Rel] at hij
  · simp at hij
  · obtain rfl : i + 1 = j := by simpa [ComplexShape.up_Rel] using hij
    exact (Category.id_comp _).trans
      ((map_alternatingCofaceMapComplex_d F X.right i).trans (Category.comp_id _).symm)

end CechComparison

section AlgebraComparison

/-- The base change of the lifted algebra map `R → A` has augmented Čech conerve the image of
the augmented Čech conerve of `R → A`. -/
private noncomputable def baseChangedCechIso
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A] :
    let T := ULift.{v} R
    let S := ULift.{max u v} A
    letI : Algebra T S := ULift.algebra' R S
    (CosimplicialObject.Augmented.whiskeringObj _ _
      (algebraBaseChange T S)).obj
        (algebraMapArrow R A).augmentedCechConerve ≅
      (Arrow.mk ((algebraBaseChange T S).map
        (algebraMapArrow R A).hom)).augmentedCechConerve := by
  dsimp only
  let : Algebra (ULift.{v} R) (ULift.{max u v} A) :=
    ULift.algebra' R (ULift.{max u v} A)
  exact augmentedCechConerveMapIso
    (algebraBaseChange (ULift.{v} R) (ULift.{max u v} A))
    (algebraMapArrow R A)

/-- The base change of the lifted `A` along the lifted `A` is the lifted `A ⊗[R] A`. -/
private def baseChangedAlgebraEquiv
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A] :
    let T := ULift.{v} R
    let S := ULift.{max u v} A
    let B := ULift.{u} A
    let C := ULift.{u} (A ⊗[R] A)
    letI : Algebra T S := ULift.algebra' R S
    letI : Algebra T B := ULift.algebra' R B
    letI : Algebra A C := inferInstance
    letI : Algebra S C := ULift.algebra' A C
    S ⊗[T] B ≃ₐ[S] C := by
  let : Algebra R (ULift.{max u v} A) := inferInstance
  let : Algebra (ULift.{v} R) (ULift.{max u v} A) :=
    ULift.algebra' R (ULift.{max u v} A)
  let : Algebra (ULift.{v} R) (ULift.{u} A) :=
    ULift.algebra' R (ULift.{u} A)
  let : Algebra (ULift.{max u v} A) A := ULift.algebra' A A
  let : IsScalarTower R (ULift.{max u v} A) A :=
    IsScalarTower.of_algebraMap_eq (by intro r; rfl)
  let e : ULift.{u} (A ⊗[R] A) ≃ₐ[ULift.{max u v} A]
      (ULift.{max u v} A) ⊗[ULift.{v} R] (ULift.{u} A) :=
    Algebra.TensorProduct.uliftEquiv R (ULift.{max u v} A) A A
  exact e.symm

/-- The lifted form of `baseChangedAlgebraEquiv`, with the target lifted once more to the
universe in which the Čech conerve lives. -/
private def baseChangedAlgebraEquivLifted
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A] :
    let T := ULift.{v} R
    let S := ULift.{max u v} A
    let B := ULift.{u} A
    let C := ULift.{u} (A ⊗[R] A)
    let D := ULift.{v} C
    letI : Algebra T S := ULift.algebra' R S
    letI : Algebra T B := ULift.algebra' R B
    letI : Module T S := Algebra.toModule
    letI : Module T B := Algebra.toModule
    letI : Algebra A C := inferInstance
    letI : Algebra A D := inferInstance
    letI : Algebra S C := ULift.algebra' A C
    letI : Algebra S D := ULift.algebra' A D
    S ⊗[T] B ≃ₐ[S] D := by
  let : Algebra (ULift.{v} R) (ULift.{max u v} A) :=
    ULift.algebra' R (ULift.{max u v} A)
  let : Algebra (ULift.{v} R) (ULift.{u} A) :=
    ULift.algebra' R (ULift.{u} A)
  let : Module (ULift.{v} R) (ULift.{max u v} A) := Algebra.toModule
  let : Module (ULift.{v} R) (ULift.{u} A) := Algebra.toModule
  let : Algebra (ULift.{max u v} A) (ULift.{u} (A ⊗[R] A)) :=
    ULift.algebra' A (ULift.{u} (A ⊗[R] A))
  exact (baseChangedAlgebraEquiv R A).trans ULift.algEquiv.symm

/-- Transport a tensor product along an equality of algebra structures on the right factor. -/
private def tensorProductAlgEquivOfAlgebraEq
    (T : Type u) (S : Type v) (B : Type w)
    [CommRing T] [CommRing S] [CommRing B] [Algebra T S]
    (a b : Algebra T B) (h : a = b) :
    letI : Algebra T B := a
    letI : Module T B := Algebra.toModule
    let X := S ⊗[T] B
    letI : Algebra T B := b
    letI : Module T B := Algebra.toModule
    let Y := S ⊗[T] B
    X ≃ₐ[S] Y := by
  cases h
  exact AlgEquiv.refl

/-- Transport a tensor product along an equality of algebra structures on the right factor,
as a ring equivalence.

The ring structures on the two tensor products depend only on the module structures, which the
equality identifies, so this transport is available where `tensorProductAlgEquivOfAlgebraEq` is
not: the `Algebra S` instances carried by a `CommAlgCat` object and by
`Algebra.TensorProduct.leftAlgebra` are equal but not definitionally so. -/
private def tensorProductRingEquivOfAlgebraEq
    (T : Type u) (S : Type v) (B : Type w)
    [CommRing T] [CommRing S] [CommRing B] [Algebra T S]
    (a b : Algebra T B) (h : a = b) :
    letI : Algebra T B := a
    letI : Module T B := Algebra.toModule
    let X := S ⊗[T] B
    letI : Algebra T B := b
    letI : Module T B := Algebra.toModule
    let Y := S ⊗[T] B
    X ≃+* Y := by
  cases h
  exact RingEquiv.refl _

private theorem tensorProductRingEquivOfAlgebraEq_tmul
    (T : Type u) (S : Type v) (B : Type w)
    [CommRing T] [CommRing S] [CommRing B] [Algebra T S]
    (a b : Algebra T B) (h : a = b) (s : S) (x : B) :
    letI : Algebra T B := a
    letI : Module T B := Algebra.toModule
    let p := s ⊗ₜ[T] x
    let e := tensorProductRingEquivOfAlgebraEq T S B a b h
    letI : Algebra T B := b
    letI : Module T B := Algebra.toModule
    e p = s ⊗ₜ[T] x := by
  cases h
  rfl

/-- The base change of the lifted algebra map `R → A` is the algebra map
`A → ULift (A ⊗[R] A)`, after the canonical identifications. -/
private def baseChangedArrowIso
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A] :
    let T := ULift.{v} R
    let S := ULift.{max u v} A
    let C := ULift.{u} (A ⊗[R] A)
    letI : Algebra T S := ULift.algebra' R S
    Arrow.mk ((algebraBaseChange T S).map (algebraMapArrow R A).hom) ≅
        algebraMapArrow A C := by
  let : Algebra (ULift.{v} R) (ULift.{max u v} A) :=
    ULift.algebra' R (ULift.{max u v} A)
  let : Algebra (ULift.{v} R) (ULift.{u} A) :=
    ULift.algebra' R (ULift.{u} A)
  let : Algebra (ULift.{max u v} A) (ULift.{u} (A ⊗[R] A)) :=
    ULift.algebra' A (ULift.{u} (A ⊗[R] A))
  let F := algebraBaseChange (ULift.{v} R) (ULift.{max u v} A)
  let f := algebraMapArrow R A
  let X := F.obj f.left
  let Y := F.obj f.right
  let : Algebra (ULift.{max u v} A) X := X.algebra
  let : Algebra (ULift.{max u v} A) Y := Y.algebra
  let e₀ : X ≅ (algebraMapArrow A (ULift.{u} (A ⊗[R] A))).left :=
    @CommAlgCat.isoMk (ULift.{max u v} A) _ X (ULift.{max u v} A)
      X.commRing inferInstance X.algebra inferInstance {
      toRingEquiv := (Algebra.TensorProduct.rid (ULift.{v} R)
        (ULift.{max u v} A) (ULift.{max u v} A)).toRingEquiv
      commutes' := by
        intro s
        simp only [X, F, f, algebraBaseChange, CommRingCat.tensorProd,
          CommRingCat.mkUnder, commAlgCatEquivUnder, algebraMapArrow]
        change ((Algebra.TensorProduct.rid (ULift.{v} R)
          (ULift.{max u v} A) (ULift.{max u v} A) :
            ((ULift.{max u v} A) ⊗[ULift.{v} R] (ULift.{v} R)) →+*
              (ULift.{max u v} A)).comp
                Algebra.TensorProduct.includeLeftRingHom) s = s
        simp }
  have hAlg :
      (CommRingCat.instAlgebraCarrierRight
        (Under.mk (CommRingCat.ofHom
          (algebraMap (ULift.{v} R) (ULift.{u} A)))) :
        Algebra (ULift.{v} R) (ULift.{u} A)) =
          ULift.algebra' R (ULift.{u} A) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  let e := tensorProductAlgEquivOfAlgebraEq
    (ULift.{v} R) (ULift.{max u v} A) (ULift.{u} A)
    (show Algebra (ULift.{v} R) (ULift.{u} A) from CommRingCat.instAlgebraCarrierRight
      (Under.mk (CommRingCat.ofHom
        (algebraMap (ULift.{v} R) (ULift.{u} A)))))
    (ULift.algebra' R (ULift.{u} A)) hAlg
  let e₁ : Y ≅ (algebraMapArrow A (ULift.{u} (A ⊗[R] A))).right :=
    @CommAlgCat.isoMk (ULift.{max u v} A) _ Y
      (ULift.{v} (ULift.{u} (A ⊗[R] A)))
      Y.commRing inferInstance Y.algebra inferInstance {
      toRingEquiv := (e.trans (baseChangedAlgebraEquivLifted R A)).toRingEquiv
      commutes' := by
        intro s
        let : Algebra (ULift.{v} R) (ULift.{u} A) :=
          CommRingCat.instAlgebraCarrierRight
            (Under.mk (CommRingCat.ofHom
              (algebraMap (ULift.{v} R) (ULift.{u} A))))
        let : Module (ULift.{v} R) (ULift.{u} A) := Algebra.toModule
        change (baseChangedAlgebraEquivLifted R A)
          (e (s ⊗ₜ[ULift.{v} R] (1 : ULift.{u} A))) =
            (algebraMap A (ULift.{v} (ULift.{u} (A ⊗[R] A)))) s.down
        exact (e.trans (baseChangedAlgebraEquivLifted R A)).commutes s }
  refine Arrow.isoMk e₀ e₁ ?_
  change e₀.hom ≫ (algebraMapArrow A (ULift.{u} (A ⊗[R] A))).hom = F.map f.hom ≫ e₁.hom
  rw [← cancel_epi e₀.inv]
  simp only [← Category.assoc, e₀.inv_hom_id, Category.id_comp]
  ext

/-- The base change of the augmented Čech conerve of `R → A` is the augmented Čech conerve of
`A → ULift (A ⊗[R] A)`, which is the split one. -/
private noncomputable def baseChangedCechToSplitIso
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A] :
    let T := ULift.{v} R
    let S := ULift.{max u v} A
    let C := ULift.{u} (A ⊗[R] A)
    letI : Algebra T S := ULift.algebra' R S
    (CosimplicialObject.Augmented.whiskeringObj _ _
      (algebraBaseChange T S)).obj (algebraMapArrow R A).augmentedCechConerve ≅
      (algebraMapArrow A C).augmentedCechConerve := by
  let : Algebra (ULift.{v} R) (ULift.{max u v} A) :=
    ULift.algebra' R (ULift.{max u v} A)
  exact (baseChangedCechIso R A).trans
    ((CosimplicialObject.augmentedCechConerve).mapIso (baseChangedArrowIso R A))

/-- The underlying ring of the base change of an algebra is the tensor product. -/
private def algebraBaseChange_obj_ringEquiv
    (T S : Type u) [CommRing T] [CommRing S] [Algebra T S]
    (B : CommAlgCat.{u} T) :
    letI : Algebra T B := B.algebra
    ((algebraBaseChange T S).obj B : Type u) ≃+* S ⊗[T] B := by
  let : Algebra T B := B.algebra
  have hAlg :
      (CommRingCat.instAlgebraCarrierRight
        ((commAlgCatEquivUnder (.of T)).functor.obj B) : Algebra T B) = B.algebra :=
    Algebra.algebra_ext _ _ fun _ => rfl
  exact tensorProductRingEquivOfAlgebraEq T S B
    ((CommRingCat.instAlgebraCarrierRight
      ((commAlgCatEquivUnder (.of T)).functor.obj B) : Algebra T B))
    B.algebra hAlg

/-- The base change of an algebra is the tensor product, as an algebra equivalence. -/
private def algebraBaseChange_obj_algEquiv
    (T S : Type u) [CommRing T] [CommRing S] [Algebra T S]
    (B : CommAlgCat.{u} T) :
    letI : Algebra T B := B.algebra
    let X := (algebraBaseChange T S).obj B
    letI : Algebra S X := X.algebra
    (X : Type u) ≃ₐ[S] S ⊗[T] B := by
  let : Algebra T B := B.algebra
  let X := (algebraBaseChange T S).obj B
  let : Algebra S X := X.algebra
  have hAlg :
      (CommRingCat.instAlgebraCarrierRight
        ((commAlgCatEquivUnder (.of T)).functor.obj B) : Algebra T B) = B.algebra :=
    Algebra.algebra_ext _ _ fun _ => rfl
  exact {
    toRingEquiv := (algebraBaseChange_obj_ringEquiv T S B)
    commutes' := fun s => tensorProductRingEquivOfAlgebraEq_tmul T S B
      ((CommRingCat.instAlgebraCarrierRight
        ((commAlgCatEquivUnder (.of T)).functor.obj B) : Algebra T B))
      B.algebra hAlg s 1 }

private theorem algebraBaseChange_obj_algEquiv_tmul
    (T S : Type u) [CommRing T] [CommRing S] [Algebra T S]
    (B : CommAlgCat.{u} T) (s : S) (b : B) :
    letI : Algebra T B := B.algebra
    let q := s ⊗ₜ[T] b
    let X := (algebraBaseChange T S).obj B
    letI : Algebra S X := X.algebra
    letI : Algebra T B := CommRingCat.instAlgebraCarrierRight
      ((commAlgCatEquivUnder (.of T)).functor.obj B)
    letI : Module T B := Algebra.toModule
    let p := s ⊗ₜ[T] b
    (algebraBaseChange_obj_algEquiv T S B) p = q := by
  let : Algebra T B := B.algebra
  have hAlg :
      (CommRingCat.instAlgebraCarrierRight
        ((commAlgCatEquivUnder (.of T)).functor.obj B) : Algebra T B) = B.algebra :=
    Algebra.algebra_ext _ _ fun _ => rfl
  exact tensorProductRingEquivOfAlgebraEq_tmul T S B _ _ hAlg s b

private theorem algebraBaseChange_obj_algEquiv_symm_tmul
    (T S : Type u) [CommRing T] [CommRing S] [Algebra T S]
    (B : CommAlgCat.{u} T) (s : S) (b : B) :
    letI : Algebra T B := B.algebra
    let q := s ⊗ₜ[T] b
    let X := (algebraBaseChange T S).obj B
    letI : Algebra S X := X.algebra
    letI : Algebra T B := CommRingCat.instAlgebraCarrierRight
      ((commAlgCatEquivUnder (.of T)).functor.obj B)
    letI : Module T B := Algebra.toModule
    let p := s ⊗ₜ[T] b
    (algebraBaseChange_obj_algEquiv T S B).symm q = p :=
  (algebraBaseChange_obj_algEquiv T S B).symm_apply_eq.mpr
    (algebraBaseChange_obj_algEquiv_tmul T S B s b).symm

private theorem algebraBaseChange_map_symm_tmul
    (T S : Type u) [CommRing T] [CommRing S] [Algebra T S]
    (B C : CommAlgCat.{u} T) (f : B ⟶ C) (s : S) (b : B) :
    letI : Algebra T B := B.algebra
    letI : Algebra T C := C.algebra
    let X := (algebraBaseChange T S).obj B
    let Y := (algebraBaseChange T S).obj C
    letI : Algebra S X := X.algebra
    letI : Algebra S Y := Y.algebra
    ((algebraBaseChange T S).map f).hom
      ((algebraBaseChange_obj_algEquiv T S B).symm (s ⊗ₜ[T] b)) =
        (algebraBaseChange_obj_algEquiv T S C).symm (s ⊗ₜ[T] f.hom b) := by
  dsimp only
  simp only [algebraBaseChange_obj_algEquiv_symm_tmul]
  rfl

end AlgebraComparison

section CoefficientComparison

/-- Tensoring with the coefficient module over the lifted base ring agrees with tensoring over
the base ring itself. -/
private def liftedTensorEquiv
    (R : Type u) (M : Type w) [CommRing R]
    [AddCommGroup M] [Module R M]
    (B : CommAlgCat.{z} (ULift.{v} R)) :
    letI : Algebra (ULift.{v} R) B := B.algebra
    letI : Algebra R B := Algebra.compHom B
      (ULift.ringEquiv : ULift.{v} R ≃+* R).symm.toRingHom
    (B ⊗[ULift.{v} R] M) ≃ₗ[R] (B ⊗[R] M) := by
  let : Algebra (ULift.{v} R) B := B.algebra
  let : Algebra R B := Algebra.compHom B
    (ULift.ringEquiv : ULift.{v} R ≃+* R).symm.toRingHom
  exact TensorProduct.equivOfCompatibleSMul R (ULift.{v} R) R B M

/-- Base change along the lifted `A` agrees with base change along `A`. -/
private def liftedBaseChangeEquiv
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    (B : CommAlgCat.{max u v} (ULift.{v} R)) :
    letI : Algebra (ULift.{v} R) B := B.algebra
    letI : Algebra R B := Algebra.compHom B
      (ULift.ringEquiv : ULift.{v} R ≃+* R).symm.toRingHom
    letI : Algebra (ULift.{v} R) A := ULift.algebra' R A
    letI : IsScalarTower (ULift.{v} R) A (ULift.{max u v} A) :=
      IsScalarTower.of_algebraMap_eq (by intro r; rfl)
    letI : SMulCommClass (ULift.{v} R) A (ULift.{max u v} A) := inferInstance
    (ULift.{max u v} A) ⊗[ULift.{v} R] B ≃ₗ[A] A ⊗[R] B := by
  let : Algebra (ULift.{v} R) B := B.algebra
  let : Algebra R B := Algebra.compHom B
    (ULift.ringEquiv : ULift.{v} R ≃+* R).symm.toRingHom
  let : Algebra (ULift.{v} R) A := ULift.algebra' R A
  let : IsScalarTower (ULift.{v} R) A (ULift.{max u v} A) :=
    IsScalarTower.of_algebraMap_eq (by intro r; rfl)
  let : SMulCommClass (ULift.{v} R) A (ULift.{max u v} A) := inferInstance
  exact (TensorProduct.equivOfCompatibleSMul R (ULift.{v} R) A
    (ULift.{max u v} A) B).trans
      (TensorProduct.AlgebraTensorModule.congr
        (ULift.moduleEquiv : ULift.{max u v} A ≃ₗ[A] A)
        (LinearEquiv.refl R B))

private theorem liftedTensor_smulCommClass
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    (B : CommAlgCat.{max u v} (ULift.{v} R)) :
    letI : Algebra (ULift.{v} R) (ULift.{max u v} A) :=
      ULift.algebra' R (ULift.{max u v} A)
    letI : Algebra (ULift.{v} R) B := B.algebra
    SMulCommClass A (ULift.{max u v} A)
      ((ULift.{max u v} A) ⊗[ULift.{v} R] B) := by
  let : Algebra (ULift.{v} R) (ULift.{max u v} A) :=
    ULift.algebra' R (ULift.{max u v} A)
  let : Algebra (ULift.{v} R) B := B.algebra
  exact TensorProduct.smulCommClass_left

/-- Distributivity of scalar extension over the tensor product with the coefficient module, in
the universe-lifted form in which the Amitsur complex is stated. -/
private def coefficientBaseChangeEquiv
    (R : Type u) (A : Type v) (M : Type w)
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M]
    (B : CommAlgCat.{max u v} (ULift.{v} R)) :
    let S := ULift.{max u v} A
    let T := ULift.{v} R
    letI : Algebra T S := ULift.algebra' R S
    letI : Algebra T A := ULift.algebra' R A
    letI : Algebra T B := B.algebra
    letI : Algebra R B := Algebra.compHom B
      (ULift.ringEquiv : T ≃+* R).symm.toRingHom
    A ⊗[R] (B ⊗[T] M) ≃ₗ[A] (S ⊗[T] B) ⊗[S] (A ⊗[R] M) := by
  let : Algebra (ULift.{v} R) (ULift.{max u v} A) :=
    ULift.algebra' R (ULift.{max u v} A)
  let : Algebra (ULift.{v} R) B := B.algebra
  let : Algebra R B := Algebra.compHom B
    (ULift.ringEquiv : ULift.{v} R ≃+* R).symm.toRingHom
  let e₀ := (LinearEquiv.baseChange R A _ _ (liftedTensorEquiv R M B)).trans
    (tensorDistribBaseChange R A B M)
  let e₁ := TensorProduct.AlgebraTensorModule.congr
    (liftedBaseChangeEquiv R A B).symm
    (LinearEquiv.refl A (A ⊗[R] M))
  let : SMulCommClass A (ULift.{max u v} A)
      ((ULift.{max u v} A) ⊗[ULift.{v} R] B) :=
    liftedTensor_smulCommClass R A B
  let : SMulCommClass (ULift.{max u v} A) A
      ((ULift.{max u v} A) ⊗[ULift.{v} R] B) :=
    SMulCommClass.symm _ _ _
  let e₂ := TensorProduct.equivOfCompatibleSMul A
    (ULift.{max u v} A) A
    ((ULift.{max u v} A) ⊗[ULift.{v} R] B) (A ⊗[R] M)
  exact e₀.trans (e₁.trans e₂.symm)

private theorem coefficientBaseChangeEquiv_tmul
    (R : Type u) (A : Type v) (M : Type w)
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M]
    (B : CommAlgCat.{max u v} (ULift.{v} R))
    (a : A) (b : B) (m : M) :
    let S := ULift.{max u v} A
    let T := ULift.{v} R
    letI : Algebra T S := ULift.algebra' R S
    letI : Algebra T B := B.algebra
    letI : Algebra R B := Algebra.compHom B
      (ULift.ringEquiv : T ≃+* R).symm.toRingHom
    (coefficientBaseChangeEquiv R A M B) (a ⊗ₜ[R] (b ⊗ₜ[T] m)) =
        ((ULift.up a : S) ⊗ₜ[T] b) ⊗ₜ[S] (1 ⊗ₜ[R] m) := by
  dsimp only
  let : Algebra (ULift.{v} R) (ULift.{max u v} A) :=
    ULift.algebra' R (ULift.{max u v} A)
  let : Algebra (ULift.{v} R) B := B.algebra
  let : Algebra R B := Algebra.compHom B
    (ULift.ringEquiv : ULift.{v} R ≃+* R).symm.toRingHom
  simp [coefficientBaseChangeEquiv, tensorDistribBaseChange,
    liftedTensorEquiv, liftedBaseChangeEquiv,
    TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
    TensorProduct.equivOfCompatibleSMul,
    TensorProduct.AlgebraTensorModule.congr_tmul,
    TensorProduct.AlgebraTensorModule.congr_symm_tmul]

/-- The component of the comparison of coefficient functors at an algebra. -/
private def coefficientBaseChangeEquivObj
    (R : Type u) (A : Type v) (M : Type w)
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M]
    (B : CommAlgCat.{max u v} (ULift.{v} R)) :
    let S := ULift.{max u v} A
    let T := ULift.{v} R
    letI : Algebra T S := ULift.algebra' R S
    letI : Algebra T B := B.algebra
    letI : Algebra R B := Algebra.compHom B
      (ULift.ringEquiv : T ≃+* R).symm.toRingHom
    let X := (algebraBaseChange T S).obj B
    letI : Algebra S X := X.algebra
    letI : Algebra A X := Algebra.compHom X (algebraMap A S)
    A ⊗[R] (B ⊗[T] M) ≃ₗ[A] X ⊗[S] (A ⊗[R] M) := by
  let : Algebra (ULift.{v} R) (ULift.{max u v} A) :=
    ULift.algebra' R (ULift.{max u v} A)
  let : Algebra (ULift.{v} R) B := B.algebra
  let : Algebra R B := Algebra.compHom B
    (ULift.ringEquiv : ULift.{v} R ≃+* R).symm.toRingHom
  let X := (algebraBaseChange (ULift.{v} R) (ULift.{max u v} A)).obj B
  let : Algebra (ULift.{max u v} A) X := X.algebra
  let : Algebra A X := Algebra.compHom X (algebraMap A (ULift.{max u v} A))
  let e₁ := coefficientBaseChangeEquiv R A M B
  let e₂ := (TensorProduct.AlgebraTensorModule.congr
    (algebraBaseChange_obj_algEquiv (ULift.{v} R) (ULift.{max u v} A) B).symm.toLinearEquiv
    (LinearEquiv.refl (ULift.{max u v} A) (A ⊗[R] M))).restrictScalars A
  exact e₁.trans e₂

private theorem coefficientBaseChangeEquivObj_tmul
    (R : Type u) (A : Type v) (M : Type w)
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M]
    (B : CommAlgCat.{max u v} (ULift.{v} R))
    (a : A) (b : B) (m : M) :
    let S := ULift.{max u v} A
    let T := ULift.{v} R
    letI : Algebra T S := ULift.algebra' R S
    letI : Algebra T B := B.algebra
    letI : Algebra R B := Algebra.compHom B
      (ULift.ringEquiv : T ≃+* R).symm.toRingHom
    let q := a ⊗ₜ[R] (b ⊗ₜ[T] m)
    let X := (algebraBaseChange T S).obj B
    letI : Algebra S X := X.algebra
    letI : Algebra A X := Algebra.compHom X (algebraMap A S)
    let p := ((algebraBaseChange_obj_algEquiv T S B).symm
      ((ULift.up a : S) ⊗ₜ[T] b) ⊗ₜ[S] ((1 : A) ⊗ₜ[R] m))
    (coefficientBaseChangeEquivObj R A M B) q = p := by
  dsimp only
  refine Eq.trans (LinearEquiv.trans_apply _) ?_
  refine Eq.trans (congrArg _ (coefficientBaseChangeEquiv_tmul R A M B a b m)) ?_
  rfl

private theorem coefficientBaseChangeEquivObj_natural
    (R : Type u) (A : Type v) (M : Type w)
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M]
    (B C : CommAlgCat.{max u v} (ULift.{v} R)) (f : B ⟶ C) :
    let S := ULift.{max u v} A
    let T := ULift.{v} R
    letI : Algebra T S := ULift.algebra' R S
    letI : Algebra T A := ULift.algebra' R A
    letI : Algebra T B := B.algebra
    letI : Algebra T C := C.algebra
    letI : Algebra R B := Algebra.compHom B
      (ULift.ringEquiv : T ≃+* R).symm.toRingHom
    letI : Algebra R C := Algebra.compHom C
      (ULift.ringEquiv : T ≃+* R).symm.toRingHom
    let X := (algebraBaseChange T S).obj B
    let Y := (algebraBaseChange T S).obj C
    letI : Algebra S X := X.algebra
    letI : Algebra S Y := Y.algebra
    letI : Algebra A X := Algebra.compHom X (algebraMap A S)
    letI : Algebra A Y := Algebra.compHom Y (algebraMap A S)
    (coefficientBaseChangeEquivObj R A M C).toLinearMap.comp
      ((((ModuleCat.restrictScalars (algebraMap R T)).map
        (ModuleCat.ofHom (f.hom.toLinearMap.rTensor M))).hom).baseChange A) =
        (((((algebraBaseChange T S).map f).hom.toLinearMap).rTensor
          (A ⊗[R] M)).restrictScalars A).comp
            (coefficientBaseChangeEquivObj R A M B).toLinearMap := by
  let : Algebra (ULift.{v} R) (ULift.{max u v} A) :=
    ULift.algebra' R (ULift.{max u v} A)
  let : Algebra (ULift.{v} R) A := ULift.algebra' R A
  let : Algebra (ULift.{v} R) B := B.algebra
  let : Algebra (ULift.{v} R) C := C.algebra
  let : Algebra R B := Algebra.compHom B
    (ULift.ringEquiv : ULift.{v} R ≃+* R).symm.toRingHom
  let : Algebra R C := Algebra.compHom C
    (ULift.ringEquiv : ULift.{v} R ≃+* R).symm.toRingHom
  let X := (algebraBaseChange (ULift.{v} R) (ULift.{max u v} A)).obj B
  let Y := (algebraBaseChange (ULift.{v} R) (ULift.{max u v} A)).obj C
  let : Algebra (ULift.{max u v} A) X := X.algebra
  let : Algebra (ULift.{max u v} A) Y := Y.algebra
  let : Algebra A X := Algebra.compHom X (algebraMap A (ULift.{max u v} A))
  let : Algebra A Y := Algebra.compHom Y (algebraMap A (ULift.{max u v} A))
  let : Module R (Y ⊗[ULift.{max u v} A] (A ⊗[R] M)) :=
    Module.compHom _ (algebraMap R A)
  let : IsScalarTower R A (Y ⊗[ULift.{max u v} A] (A ⊗[R] M)) :=
    ⟨by
      intro r a x
      simp only [Algebra.smul_def]
      exact mul_smul _ _ _⟩
  dsimp only
  let g : A ⊗[R] (B ⊗[ULift.{v} R] M) →ₗ[A] Y ⊗[ULift.{max u v} A] (A ⊗[R] M) :=
    (coefficientBaseChangeEquivObj R A M C).toLinearMap.comp
      ((((ModuleCat.restrictScalars (algebraMap R (ULift.{v} R))).map
        (ModuleCat.ofHom (f.hom.toLinearMap.rTensor M))).hom).baseChange A)
  let h : A ⊗[R] (B ⊗[ULift.{v} R] M) →ₗ[A] Y ⊗[ULift.{max u v} A] (A ⊗[R] M) :=
    (((((algebraBaseChange (ULift.{v} R) (ULift.{max u v} A)).map f).hom.toLinearMap).rTensor
      (A ⊗[R] M)).restrictScalars A).comp
        (coefficientBaseChangeEquivObj R A M B).toLinearMap
  change g = h
  apply TensorProduct.AlgebraTensorModule.ext
  intro a y
  induction y using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.tmul_zero, map_zero]
  | tmul b m =>
    dsimp [g, h]
    change (coefficientBaseChangeEquivObj R A M C)
      (a ⊗ₜ[R] (f.hom b ⊗ₜ[ULift.{v} R] m)) =
      (((algebraBaseChange (ULift.{v} R) (ULift.{max u v} A)).map f).hom
        ((algebraBaseChange_obj_algEquiv (ULift.{v} R) (ULift.{max u v} A) B).symm
          ((ULift.up a : ULift.{max u v} A) ⊗ₜ[ULift.{v} R] b))) ⊗ₜ[ULift.{max u v} A]
            ((1 : A) ⊗ₜ[R] m)
    rw [coefficientBaseChangeEquivObj_tmul, algebraBaseChange_map_symm_tmul]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

/-- The comparison of the two coefficient functors: tensoring with `M` over `R` and then base
changing to `A`, against base changing the algebra and tensoring with `A ⊗[R] M`. -/
private noncomputable def coefficientBaseChangeNatIso
    (R : Type u) (A : Type v) (M : Type w)
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] :
    let T := ULift.{v} R
    let S := ULift.{max u v} A
    letI : Algebra T S := ULift.algebra' R S
    (tensorModuleFunctor T M ⋙ ModuleCat.restrictScalars (algebraMap R T)) ⋙
      baseChangeFunctor R A ≅
        (algebraBaseChange T S ⋙ tensorModuleFunctor S (A ⊗[R] M)) ⋙
          ModuleCat.restrictScalars (algebraMap A S) := by
  let : Algebra (ULift.{v} R) (ULift.{max u v} A) :=
    ULift.algebra' R (ULift.{max u v} A)
  refine NatIso.ofComponents (fun B => ?_) ?_
  · let : Algebra (ULift.{v} R) B := B.algebra
    let : Algebra R B := Algebra.compHom B
      (ULift.ringEquiv : ULift.{v} R ≃+* R).symm.toRingHom
    let X := (algebraBaseChange (ULift.{v} R) (ULift.{max u v} A)).obj B
    let : Algebra (ULift.{max u v} A) X := X.algebra
    let : Algebra A X := Algebra.compHom X (algebraMap A (ULift.{max u v} A))
    let e := coefficientBaseChangeEquivObj R A M B
    change ModuleCat.of A (A ⊗[R] (B ⊗[ULift.{v} R] M)) ≅
      ModuleCat.of A (X ⊗[ULift.{max u v} A] (A ⊗[R] M))
    exact e.toModuleIso
  · intro B C f
    exact ModuleCat.hom_ext (coefficientBaseChangeEquivObj_natural R A M B C f)

/-- An isomorphism of functors induces an isomorphism of the whiskered augmented cosimplicial
objects. -/
private def augmentedWhiskeringObjIsoOfNatIso
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F G : C ⥤ D} (e : F ≅ G) (X : CosimplicialObject.Augmented C) :
    (CosimplicialObject.Augmented.whiskeringObj C D F).obj X ≅
      (CosimplicialObject.Augmented.whiskeringObj C D G).obj X := by
  refine Comma.isoMk (e.app X.left)
    (NatIso.ofComponents (fun n => e.app (X.right.obj n))
      fun f => e.hom.naturality (X.right.map f)) ?_
  ext n
  rw [NatTrans.comp_app, Functor.const_map_app, whiskeringObj_hom_app,
    NatTrans.comp_app, whiskeringObj_hom_app, Functor.id_map]
  exact (e.hom.naturality (X.hom.app n)).symm

/-- The base change of the augmented Amitsur cosimplicial module of `R → A` is that of
`A → ULift (A ⊗[R] A)` with coefficients in `A ⊗[R] M`. -/
private noncomputable def amitsurAugmentationBaseChangeIso
    (R : Type u) (A : Type v) (M : Type w)
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] :
    (CosimplicialObject.Augmented.whiskeringObj _ _ (baseChangeFunctor R A)).obj
      (amitsurAugmentation R A M) ≅
        amitsurAugmentation A (ULift.{u} (A ⊗[R] A)) (A ⊗[R] M) := by
  let : Algebra (ULift.{v} R) (ULift.{max u v} A) :=
    ULift.algebra' R (ULift.{max u v} A)
  let G := tensorModuleFunctor (ULift.{max u v} A) (A ⊗[R] M) ⋙
    ModuleCat.restrictScalars (algebraMap A (ULift.{max u v} A))
  exact (augmentedWhiskeringObjIsoOfNatIso (coefficientBaseChangeNatIso R A M)
    (algebraMapArrow R A).augmentedCechConerve).trans
      ((CosimplicialObject.Augmented.whiskeringObj _ _ G).mapIso
        (baseChangedCechToSplitIso R A))

/-- The base change of the lifted coefficient module is the lift of the base-changed
coefficient module. -/
private def coefficientLiftBaseChangeEquiv
    (R : Type u) (A : Type v) (M : Type w)
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] :
    A ⊗[R] ULift.{max u v} M ≃ₗ[A] ULift.{max u v} (A ⊗[R] M) :=
  (LinearEquiv.baseChange R A _ _
    (ULift.moduleEquiv : ULift.{max u v} M ≃ₗ[R] M)).trans
      (ULift.moduleEquiv : ULift.{max u v} (A ⊗[R] M) ≃ₗ[A] A ⊗[R] M).symm

private theorem coefficientLiftBaseChangeEquiv_tmul
    (R : Type u) (A : Type v) (M : Type w)
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] (a : A) (m : M) :
    (coefficientLiftBaseChangeEquiv R A M) (a ⊗ₜ[R] ULift.up m) =
      ULift.up (a ⊗ₜ[R] m) := by
  simp [coefficientLiftBaseChangeEquiv]

end CoefficientComparison

section BaseChangeIso

/-- The degree-zero compatibility of the base-change comparison: the augmentation term of the
base-changed Amitsur complex matches the augmentation term of the split one. -/
private theorem amitsurAugmentationBaseChange_left_compat
    (R : Type u) (A : Type v) (M : Type w)
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] :
    (coefficientLiftBaseChangeEquiv R A M).toModuleIso.hom ≫
        ((ModuleCat.restrictScalars (algebraMap A (ULift.{max u v} A))).map
          (ModuleCat.ofHom ((ULift.moduleEquiv :
            ULift.{max u v} (A ⊗[R] M) ≃ₗ[ULift.{max u v} A] A ⊗[R] M).trans
              (TensorProduct.lid (ULift.{max u v} A) (A ⊗[R] M)).symm).toLinearMap)) =
      (baseChangeFunctor R A).map
          ((ModuleCat.restrictScalars (algebraMap R (ULift.{v} R))).map
            (ModuleCat.ofHom ((ULift.moduleEquiv :
              ULift.{max u v} M ≃ₗ[ULift.{v} R] M).trans
                (TensorProduct.lid (ULift.{v} R) M).symm).toLinearMap)) ≫
        (amitsurAugmentationBaseChangeIso R A M).hom.left := by
  apply ModuleCat.hom_ext
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    cases m with
    | up m =>
      let T := ULift.{v} R
      let S := ULift.{max u v} A
      let B := (algebraMapArrow R A).augmentedCechConerve.left
      let : Algebra T S := ULift.algebra' R S
      let : Algebra T B := B.algebra
      let : Algebra R B := Algebra.compHom B
        (ULift.ringEquiv : T ≃+* R).symm.toRingHom
      let X := (algebraBaseChange T S).obj B
      let : Algebra S X := X.algebra
      let : Algebra A X := Algebra.compHom X (algebraMap A S)
      have hcoeff :
          (coefficientBaseChangeEquivObj R A M B)
            (a ⊗ₜ[R] (((ULift.moduleEquiv : ULift.{max u v} M ≃ₗ[T] M).trans
              (TensorProduct.lid T M).symm) (ULift.up m))) =
          ((algebraBaseChange_obj_algEquiv T S B).symm
            ((ULift.up a : S) ⊗ₜ[T] (1 : B))) ⊗ₜ[S] ((1 : A) ⊗ₜ[R] m) :=
        coefficientBaseChangeEquivObj_tmul R A M B a (1 : B) m
      have hsrc :
          (algebraBaseChange_obj_algEquiv T S B).symm
            ((ULift.up a : S) ⊗ₜ[T] (1 : B)) = algebraMap S X (ULift.up a) := by
        simpa [Algebra.TensorProduct.includeLeft_apply] using
          (algebraBaseChange_obj_algEquiv T S B).symm.commutes (ULift.up a : S)
      have hz :
          ((baseChangedArrowIso R A).hom.left.hom.toLinearMap)
            ((algebraBaseChange_obj_algEquiv T S B).symm
              ((ULift.up a : S) ⊗ₜ[T] (1 : B))) = (ULift.up a : S) := by
        rw [hsrc]
        exact (baseChangedArrowIso R A).hom.left.hom.commutes (ULift.up a : S)
      change
        (((ULift.moduleEquiv : ULift.{max u v} (A ⊗[R] M) ≃ₗ[S] A ⊗[R] M).trans
          (TensorProduct.lid S (A ⊗[R] M)).symm)
          ((coefficientLiftBaseChangeEquiv R A M) (a ⊗ₜ[R] ULift.up m)) =
        (LinearMap.rTensor (A ⊗[R] M)
          ((baseChangedArrowIso R A).hom.left.hom.toLinearMap))
          ((coefficientBaseChangeEquivObj R A M B)
            (a ⊗ₜ[R] (((ULift.moduleEquiv : ULift.{max u v} M ≃ₗ[T] M).trans
              (TensorProduct.lid T M).symm) (ULift.up m)))))
      refine Eq.trans ?_ (congrArg
        (fun z => (LinearMap.rTensor (A ⊗[R] M)
          ((baseChangedArrowIso R A).hom.left.hom.toLinearMap)) z) hcoeff).symm
      refine Eq.trans ?_ (LinearMap.rTensor_tmul ..).symm
      refine Eq.trans ?_ (congrArg (fun y : S => y ⊗ₜ[S] ((1 : A) ⊗ₜ[R] m)) hz).symm
      refine Eq.trans (congrArg
        (fun z => ((ULift.moduleEquiv : ULift.{max u v} (A ⊗[R] M) ≃ₗ[S] A ⊗[R] M).trans
          (TensorProduct.lid S (A ⊗[R] M)).symm) z)
        (coefficientLiftBaseChangeEquiv_tmul R A M a m)) ?_
      change (1 : S) ⊗ₜ[S] (a ⊗ₜ[R] m) = (ULift.up a : S) ⊗ₜ[S] ((1 : A) ⊗ₜ[R] m)
      calc
        (1 : S) ⊗ₜ[S] (a ⊗ₜ[R] m) =
            1 ⊗ₜ[S] ((ULift.up a : S) • ((1 : A) ⊗ₜ[R] m)) := by
              congr 1
              exact TensorProduct.tmul_eq_smul_one_tmul a m
        _ = (ULift.up a : S) ⊗ₜ[S] ((1 : A) ⊗ₜ[R] m) := by
              rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
              simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- The base change of the extended Amitsur complex of `R → A` with coefficients in `M` is the
extended Amitsur complex of `A → ULift (A ⊗[R] A)` with coefficients in `A ⊗[R] M`. -/
private noncomputable def amitsurExtendedBaseChangeIso
    (R : Type u) (A : Type v) (M : Type w)
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] :
    (((baseChangeFunctor R A).mapHomologicalComplex _).obj
      (amitsurExtendedCochainComplex R A M)) ≅
        amitsurExtendedCochainComplex A (ULift.{u} (A ⊗[R] A)) (A ⊗[R] M) :=
  (mapExtendedAlternatingCofaceMapComplexIso (baseChangeFunctor R A)
    (amitsurAugmentation R A M)
    (ModuleCat.of R (ULift.{max u v} M))
    ((ModuleCat.restrictScalars (algebraMap R (ULift.{v} R))).map
      (ModuleCat.ofHom ((ULift.moduleEquiv :
        ULift.{max u v} M ≃ₗ[ULift.{v} R] M).trans
          (TensorProduct.lid (ULift.{v} R) M).symm).toLinearMap))).trans
    (extendedAlternatingCofaceMapComplexIso
      _ _ (amitsurAugmentationBaseChangeIso R A M) _ _ _ _
      (coefficientLiftBaseChangeEquiv R A M).toModuleIso
      (amitsurAugmentationBaseChange_left_compat R A M))

end BaseChangeIso

/-- **Stacks Lemma 023M**, and **Stacks Lemma 03OA**.  The extended Amitsur cochain complex of a
faithfully flat algebra is exact for every module of coefficients.  Exactness of the extended
complex `M → A ⊗[R] M → A ⊗[R] A ⊗[R] M → ⋯` says both that the unaugmented complex is exact in
positive degrees and that its degree-zero cohomology is `M`, which is the form 03OA states. -/
@[stacks 023M, stacks 03OA, sga "1 VIII 1.7" "affine case"]
theorem amitsurExtendedCochainComplex_acyclic_of_faithfullyFlat
    (R : Type u) (A : Type v) (M : Type w) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module.FaithfullyFlat R A] :
    (amitsurExtendedCochainComplex R A M).Acyclic := by
  apply acyclic_of_baseChangeFunctor_iso R A
    (amitsurExtendedCochainComplex R A M)
    (amitsurExtendedCochainComplex A
      (ULift.{u} (TensorProduct R A A))
      (TensorProduct R A M))
    (amitsurExtendedBaseChangeIso R A M)
    (acyclic_amitsur_ulift_tensorProduct_self R A M)

end AlgebraicTopology

