module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.CofilteredSystem
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedBoundedCohomologicalDimension
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.InverseLimit
public import StacksFrontier.CategoryTheory.Functor.Derived.Computing
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.DoubleResolution
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.RlimBasic
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.Double
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
import Mathlib.CategoryTheory.Functor.Derived.RightDerivedTriangulated
import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# The derived inverse limit of inverse systems of abelian groups

The inverse-limit functor on inverse systems of abelian groups indexed by the natural numbers has
a right derived functor on the unbounded derived category. Its value on a system is represented by
the two-term product complex with differential `Rlim.delta`, so the higher derived limits vanish
above degree one, the ordinary limit is the kernel of that differential and the first derived
limit is its cokernel. Mittag--Leffler systems are right acyclic, every complex has a
right-acyclic replacement, and on a termwise right-acyclic complex the derived limit is computed
by taking inverse limits termwise. The chosen derived functor carries the canonical shift
compatibility, preserves distinguished triangles, and has a natural `R⁰lim ≅ lim` comparison.

The two immediate consequences of that package are also here: a short exact sequence of systems
gives the six-term exact sequence of `lim` and `R¹lim`, and for an inverse system of four-term
complexes whose two negative-degree terms and whose degree `-1` cohomology system have vanishing
`R¹lim`, degree-zero cohomology commutes with the inverse limit.

## Main definitions

There are no new definitions; the two-term product presentation is
`StacksFrontier.Homology.DerivedCategory.InverseSystem.RlimBasic`.

## Main results

* `Rlim.lim_hasRightDerivedFunctor_and_computations`: existence and computation of the derived
  inverse-limit functor (Tag 07KW), with `Rlim.lim_hasRightDerivedFunctor` its bare existence
  statement (Tag 08U4) and `Rlim.firstDerivedLimit_iso_cokernel_of_isRightDerivedFunctor` the
  cokernel description of `R¹lim` for an arbitrary right-derived inverse-limit functor.
* `Rlim.exists_sixTerm_exact_sequence_lim_rightDerived_one`: the six-term exact sequence
  `0 ⟶ lim A ⟶ lim B ⟶ lim C ⟶ R¹lim A ⟶ R¹lim B ⟶ R¹lim C ⟶ 0` of a short exact sequence of
  inverse systems, with its canonical connecting morphism (Tag 0H31).
* `Rlim.comparisonHomologyLimit_isIso_of_isZero_rightDerivedLim`: degree-zero cohomology commutes
  with the inverse limit of a system of four-term complexes under vanishing of `R¹lim` (Tag 0918).

## Implementation notes

An inverse system is a functor `ℕᵒᵖ ⥤ Ab`. Saying that a derived object is represented by a
complex is expressed by an isomorphism with its image under the localization functor to the
derived category. Existence on the bounded below derived category comes from the adapted class of
Mittag--Leffler systems (Stacks 05T8); the passage to the unbounded derived category is Stacks
07K7, whose hypothesis of vanishing in some degree is supplied by the two-term product model in
degree two. The six displayed objects of the six-term sequence are encoded by a
`ComposableArrows` of length five, whose `Exact` predicate gives exactness at the four interior
objects, monicity of the first map and epicity of the last map expressing the two endpoint zeroes.
Vanishing of `R¹lim` is always stated relative to an arbitrary right-derived inverse-limit
functor, so that no statement depends on a chosen construction.

## References

* [Stacks Project, Tag 07KW](https://stacks.math.columbia.edu/tag/07KW)
* [Stacks Project, Tag 08U4](https://stacks.math.columbia.edu/tag/08U4)
* [Stacks Project, Tag 0H31](https://stacks.math.columbia.edu/tag/0H31)
* [Stacks Project, Tag 0918](https://stacks.math.columbia.edu/tag/0918)
-/


section

set_option maxRecDepth 4096

@[expose] public section

open CategoryTheory Limits DerivedCategory Opposite

namespace Rlim

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- A nonempty Mittag--Leffler tower of sets has a compatible family. Restricting to
eventual ranges turns the transition maps into surjections, so recursive choice applies. -/
private theorem nonempty_sections_of_mittagLeffler_tower
    (F : ℕᵒᵖ ⥤ Type u) [∀ n : ℕᵒᵖ, Nonempty (F.obj n)]
    (hF : F.IsMittagLeffler) : F.sections.Nonempty := by
  let E := F.toEventualRanges
  let : ∀ n : ℕᵒᵖ, Nonempty (E.obj n) :=
    fun n => F.toEventualRanges_nonempty hF n
  have hsurj (n : ℕ) :
      Function.Surjective (E.map (homOfLE (Nat.le_succ n)).op) :=
    F.surjective_toEventualRanges hF _
  let x : ∀ n : ℕ, E.obj (op n) := Nat.rec
    (Classical.choice (inferInstance : Nonempty (E.obj (op 0))))
    (fun n a => Classical.choose (hsurj n a))
  have hx (n : ℕ) :
      E.map (homOfLE (Nat.le_succ n)).op (x (n + 1)) = x n :=
    Classical.choose_spec (hsurj n (x n))
  have hcompat (m n : ℕ) (hmn : m ≤ n) :
      E.map (homOfLE hmn).op (x n) = x m := by
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have hsplit : (homOfLE (Nat.le_succ_of_le hmn)).op =
          (homOfLE (Nat.le_succ n)).op ≫ (homOfLE hmn).op := by
        apply Subsingleton.elim
      rw [hsplit, Functor.map_comp, ConcreteCategory.comp_apply, hx, ih]
  let s : E.sections := ⟨fun n => x n.unop, by
    intro i j f
    have hij : j.unop ≤ i.unop := leOfHom f.unop
    have hf : f = (homOfLE hij).op := Subsingleton.elim _ _
    rw [hf]
    exact hcompat j.unop i.unop hij⟩
  exact ⟨(F.toEventualRangesSectionsEquiv s).val,
    (F.toEventualRangesSectionsEquiv s).property⟩

noncomputable local instance : HasDerivedCategory Ab.{u} := HasDerivedCategory.standard _

noncomputable local instance : HasDerivedCategory Rlim.InvSystemAb.{u} :=
  HasDerivedCategory.standard _

noncomputable local instance : (lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The two-term complex of products associated to a tower. -/
private noncomputable abbrev deltaComplex (A : Rlim.InvSystemAb.{u}) : CochainComplex Ab.{u} ℤ :=
  HomologicalComplex.double (Rlim.delta A)
    (show (ComplexShape.up ℤ).Rel 0 1 by rfl)

/-- The explicit two-term complex supplies the product model data required by 07KW. -/
private theorem deltaComplex_model_data (A : Rlim.InvSystemAb.{u}) :
    ∃ (e₀ : (deltaComplex A).X 0 ≅ Rlim.product A)
      (e₁ : (deltaComplex A).X 1 ≅ Rlim.product A),
      (∀ i : ℤ, i ≠ 0 → i ≠ 1 → IsZero ((deltaComplex A).X i)) ∧
      e₀.inv ≫ (deltaComplex A).d 0 1 ≫ e₁.hom = Rlim.delta A := by
  let h : (ComplexShape.up ℤ).Rel 0 1 := by rfl
  refine ⟨HomologicalComplex.doubleXIso₀ (Rlim.delta A) h,
    HomologicalComplex.doubleXIso₁ (Rlim.delta A) h (by norm_num), ?_, ?_⟩
  · intro i h₀ h₁
    exact HomologicalComplex.isZero_double_X (Rlim.delta A) h i h₀ h₁
  · unfold deltaComplex
    rw [HomologicalComplex.double_d (Rlim.delta A) h (by norm_num)]
    simp

/-- The explicit product complex has no cohomology above degree one. -/
private theorem deltaComplex_higher_vanishes (A : Rlim.InvSystemAb.{u}) (p : ℤ) (hp : 1 < p) :
    IsZero ((deltaComplex A).homology p) := by
  obtain ⟨_, _, hvan, _⟩ := deltaComplex_model_data A
  have hX : IsZero ((deltaComplex A).X p) := hvan p (by omega) (by omega)
  exact (deltaComplex A).sc p |>.isZero_homology_of_isZero_X₂ hX

/-- The coordinatewise Rlim.product map associated to a map of towers.

This is reducible, and exposed: consumers in other modules meet this map as the differential of
the product complex `(productFunctor.mapHomologicalComplex _).obj L` and need the body to see the
two agree. -/
public noncomputable abbrev prodMap {A B : Rlim.InvSystemAb.{u}} (f : A ⟶ B) :
    Rlim.product A ⟶ Rlim.product B :=
  CategoryTheory.Limits.Pi.map (fun n : ℕ ↦ f.app (op n))

/-- The product map of an identity is the identity.

This is Mathlib's `CategoryTheory.Limits.Pi.map_id` for the family of components of a natural
transformation; the two coincide only once the expected type is known, since Mathlib states it
for a bare family of morphisms. -/
private theorem prodMap_id (A : Rlim.InvSystemAb.{u}) : prodMap (𝟙 A) = 𝟙 (Rlim.product A) :=
  CategoryTheory.Limits.Pi.map_id

/-- The product map of a composite is the composite of the product maps.

This is Mathlib's `CategoryTheory.Limits.Pi.map_comp_map`, oriented for the components of a
natural transformation. -/
private theorem prodMap_comp {A B C : Rlim.InvSystemAb.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    prodMap (f ≫ g) = prodMap f ≫ prodMap g :=
  (CategoryTheory.Limits.Pi.map_comp_map _ _).symm

/-- The coordinatewise product map associated to a map of towers. -/
noncomputable abbrev productMap {A B : Rlim.InvSystemAb.{u}} (f : A ⟶ B) :
    Rlim.product A ⟶ Rlim.product B :=
  CategoryTheory.Limits.Pi.map (fun n : ℕ ↦ f.app (op n))

/-- The product map of an identity is the identity.

This is Mathlib's `CategoryTheory.Limits.Pi.map_id` for the family of components of a natural
transformation; the two coincide only once the expected type is known, since Mathlib states it
for a bare family of morphisms. -/
private theorem productMap_id (A : Rlim.InvSystemAb.{u}) : productMap (𝟙 A) = 𝟙 (Rlim.product A) :=
  CategoryTheory.Limits.Pi.map_id

/-- The product map of a composite is the composite of the product maps.

This is Mathlib's `CategoryTheory.Limits.Pi.map_comp_map`, oriented for the components of a
natural transformation. -/
private theorem productMap_comp {A B C : Rlim.InvSystemAb.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    productMap (f ≫ g) = productMap f ≫ productMap g :=
  (CategoryTheory.Limits.Pi.map_comp_map _ _).symm

/-- The product of the entries, regarded as a functor on towers. -/
public noncomputable def productFunctor : Rlim.InvSystemAb.{u} ⥤ Ab.{u} where
  obj := Rlim.product.{u}
  map := fun f => CategoryTheory.Limits.Pi.map (fun n : ℕ ↦ f.app (op n))
  map_id := fun _ => CategoryTheory.Limits.Pi.map_id
  map_comp := fun _ _ => (CategoryTheory.Limits.Pi.map_comp_map _ _).symm

public noncomputable instance : productFunctor.{u}.Additive where
  map_add := by
    intro X Y f g
    apply Pi.hom_ext
    intro n
    simp [productFunctor, Preadditive.add_comp, Preadditive.comp_add]

private lemma shift_comp_π (A : Rlim.InvSystemAb.{u}) (n : ℕ) :
    Rlim.shift A ≫ Pi.π (fun n : ℕ ↦ A.obj (op n)) n =
      Pi.π (fun n : ℕ ↦ A.obj (op n)) (n + 1) ≫
        A.map (homOfLE (Nat.le_succ n)).op := by
  exact Pi.lift_comp_π _ n

/-- The shift commutes with maps of inverse systems. -/
theorem prodMap_shiftMap {A B : Rlim.InvSystemAb.{u}} (f : A ⟶ B) :
    prodMap f ≫ Rlim.shift B = Rlim.shift A ≫ prodMap f := by
  apply Pi.hom_ext
  intro n
  calc
    (prodMap f ≫ Rlim.shift B) ≫ Pi.π (fun n : ℕ ↦ B.obj (op n)) n
        = (prodMap f ≫ Pi.π (fun n : ℕ ↦ B.obj (op n)) (n + 1)) ≫
            B.map (homOfLE (Nat.le_succ n)).op := by
              rw [Category.assoc, shift_comp_π, ← Category.assoc]
    _ = (Pi.π (fun n : ℕ ↦ A.obj (op n)) (n + 1) ≫ f.app (op (n + 1))) ≫
          B.map (homOfLE (Nat.le_succ n)).op := by rw [Pi.map_π]
    _ = (Pi.π (fun n : ℕ ↦ A.obj (op n)) (n + 1) ≫
          A.map (homOfLE (Nat.le_succ n)).op) ≫ f.app (op n) := by
            simp only [Category.assoc, ← f.naturality (homOfLE (Nat.le_succ n)).op]
    _ = (Rlim.shift A ≫ Pi.π (fun n : ℕ ↦ A.obj (op n)) n) ≫ f.app (op n) := by
          rw [shift_comp_π]
    _ = (Rlim.shift A ≫ prodMap f) ≫ Pi.π (fun n : ℕ ↦ B.obj (op n)) n := by
          simp only [Category.assoc, Pi.map_π]

/-- The Rlim.product difference map is natural in the inverse system. -/
public theorem prodMap_deltaMap {A B : Rlim.InvSystemAb.{u}} (f : A ⟶ B) :
    prodMap f ≫ Rlim.delta B = Rlim.delta A ≫ prodMap f := by
  simp only [Rlim.delta, Preadditive.comp_sub, Preadditive.sub_comp,
    Category.comp_id, Category.id_comp, prodMap_shiftMap]

/-- The shift commutes with maps of inverse systems. -/
theorem productMap_shift {A B : Rlim.InvSystemAb.{u}} (f : A ⟶ B) :
    productMap f ≫ Rlim.shift B = Rlim.shift A ≫ productMap f :=
  prodMap_shiftMap f

/-- The product difference map is natural in the inverse system. -/
theorem productMap_delta {A B : Rlim.InvSystemAb.{u}} (f : A ⟶ B) :
    productMap f ≫ Rlim.delta B = Rlim.delta A ≫ productMap f :=
  prodMap_deltaMap f

/-- The product difference maps form an endomorphism of the product functor. -/
noncomputable def deltaNatTrans : productFunctor ⟶ productFunctor where
  app := Rlim.delta
  naturality := fun _ _ f => productMap_delta f

/-- A map of towers induces a map of their two-term product complexes. -/
private noncomputable def deltaComplexMap {A B : Rlim.InvSystemAb.{u}} (f : A ⟶ B) :
    deltaComplex A ⟶ deltaComplex B := by
  let h : (ComplexShape.up ℤ).Rel 0 1 := by rfl
  let e₀ := HomologicalComplex.doubleXIso₀ (Rlim.delta B) h
  let e₁ := HomologicalComplex.doubleXIso₁ (Rlim.delta B) h (by norm_num)
  change HomologicalComplex.double (Rlim.delta A) h ⟶
    HomologicalComplex.double (Rlim.delta B) h
  refine HomologicalComplex.mkHomFromDouble h (by norm_num)
    (productMap f ≫ e₀.inv) (productMap f ≫ e₁.inv) ?_ ?_
  · rw [HomologicalComplex.double_d (Rlim.delta B) h (by norm_num)]
    simpa [e₀, e₁, Category.assoc] using
      congrArg (fun t => t ≫ e₁.inv) (productMap_delta f)
  · intro k hk
    rw [HomologicalComplex.double_d_eq_zero₀ (Rlim.delta B) h 1 k (by norm_num)]
    simp

private lemma deltaComplexMap_f_zero {A B : Rlim.InvSystemAb.{u}} (f : A ⟶ B) :
    (deltaComplexMap f).f 0 ≫
        (HomologicalComplex.doubleXIso₀ (Rlim.delta B)
          (show (ComplexShape.up ℤ).Rel 0 1 by rfl)).hom =
      (HomologicalComplex.doubleXIso₀ (Rlim.delta A)
          (show (ComplexShape.up ℤ).Rel 0 1 by rfl)).hom ≫ productMap f := by
  dsimp [deltaComplexMap]
  simp [Category.assoc]

private lemma deltaComplexMap_f_one {A B : Rlim.InvSystemAb.{u}} (f : A ⟶ B) :
    (deltaComplexMap f).f 1 ≫
        (HomologicalComplex.doubleXIso₁ (Rlim.delta B)
          (show (ComplexShape.up ℤ).Rel 0 1 by rfl) (by norm_num)).hom =
      (HomologicalComplex.doubleXIso₁ (Rlim.delta A)
          (show (ComplexShape.up ℤ).Rel 0 1 by rfl) (by norm_num)).hom ≫ productMap f := by
  dsimp [deltaComplexMap]
  simp [Category.assoc]

/-- The two-term product construction is functorial in the tower. -/
private noncomputable def deltaComplexFunctor : Rlim.InvSystemAb.{u} ⥤ CochainComplex Ab.{u} ℤ where
  obj := deltaComplex
  map := fun f => deltaComplexMap f
  map_id := by
    intro A
    apply HomologicalComplex.from_double_hom_ext
    · rw [← cancel_mono (HomologicalComplex.doubleXIso₀ (Rlim.delta A)
        (show (ComplexShape.up ℤ).Rel 0 1 by rfl)).hom]
      simp [deltaComplexMap_f_zero, productMap_id]
    · rw [← cancel_mono (HomologicalComplex.doubleXIso₁ (Rlim.delta A)
        (show (ComplexShape.up ℤ).Rel 0 1 by rfl) (by norm_num)).hom]
      simp [deltaComplexMap_f_one, productMap_id]
  map_comp := by
    intro A B C f g
    apply HomologicalComplex.from_double_hom_ext
    · rw [← cancel_mono (HomologicalComplex.doubleXIso₀ (Rlim.delta C)
        (show (ComplexShape.up ℤ).Rel 0 1 by rfl)).hom]
      simp only [HomologicalComplex.comp_f, Category.assoc]
      rw [deltaComplexMap_f_zero (f ≫ g), deltaComplexMap_f_zero g,
        productMap_comp]
      simpa only [Category.assoc] using
        (congrArg (fun t => t ≫ productMap g) (deltaComplexMap_f_zero f)).symm
    · rw [← cancel_mono (HomologicalComplex.doubleXIso₁ (Rlim.delta C)
        (show (ComplexShape.up ℤ).Rel 0 1 by rfl) (by norm_num)).hom]
      simp only [HomologicalComplex.comp_f, Category.assoc]
      rw [deltaComplexMap_f_one (f ≫ g), deltaComplexMap_f_one g,
        productMap_comp]
      simpa only [Category.assoc] using
        (congrArg (fun t => t ≫ productMap g) (deltaComplexMap_f_one f)).symm

/-- The inclusion of the inverse limit in the Rlim.product is natural in the tower. -/
public theorem limitToProd_naturality {A B : Rlim.InvSystemAb.{u}} (f : A ⟶ B) :
    Rlim.limitToProduct A ≫ prodMap f = lim.map f ≫ Rlim.limitToProduct B := by
  apply Pi.hom_ext
  intro n
  calc
    (Rlim.limitToProduct A ≫ prodMap f) ≫ Pi.π (fun n : ℕ ↦ B.obj (op n)) n
        = Rlim.limitToProduct A ≫
            (Pi.π (fun n : ℕ ↦ A.obj (op n)) n ≫ f.app (op n)) := by
              rw [Category.assoc, Pi.map_π]
    _ = limit.π A (op n) ≫ f.app (op n) := by
          rw [← Category.assoc, Rlim.limitToProduct_comp_π]
    _ = lim.map f ≫ limit.π B (op n) := by
          rw [← limMap_eq, limMap_π]
    _ = (lim.map f ≫ Rlim.limitToProduct B) ≫ Pi.π (fun n : ℕ ↦ B.obj (op n)) n := by
          rw [Category.assoc, Rlim.limitToProduct_comp_π]

/-- The inclusion of the limit in the Rlim.product is a natural transformation. -/
public noncomputable def limitToProdNatTrans :
    (lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}) ⟶ productFunctor where
  app := Rlim.limitToProduct
  naturality := fun _ _ f => (limitToProd_naturality f).symm

/-- The inclusion of the inverse limit in the product is natural in the tower. -/
theorem limitToProduct_naturality {A B : Rlim.InvSystemAb.{u}} (f : A ⟶ B) :
    Rlim.limitToProduct A ≫ productMap f = lim.map f ≫ Rlim.limitToProduct B :=
  limitToProd_naturality f

/-- The inclusion of the limit in the product is a natural transformation. -/
noncomputable def limitToProductNatTrans :
    (lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}) ⟶ productFunctor where
  app := Rlim.limitToProduct
  naturality := fun _ _ f => (limitToProduct_naturality f).symm

/-- The `n`th coordinate of a product object. -/
private noncomputable def prodCoord (A : Rlim.InvSystemAb.{u}) (x : Rlim.product A) (n : ℕ) :
    A.obj (op n) :=
  Pi.π (fun n : ℕ ↦ A.obj (op n)) n x

/-- The coordinates of the difference map. -/
private lemma prodCoord_delta (A : Rlim.InvSystemAb.{u}) (x : Rlim.product A) (n : ℕ) :
    prodCoord A (Rlim.delta A x) n = prodCoord A x n -
      A.map (homOfLE (Nat.le_succ n)).op (prodCoord A x (n + 1)) := by
  have h : Rlim.delta A ≫ Pi.π (fun n : ℕ => A.obj (op n)) n =
      Pi.π (fun n : ℕ => A.obj (op n)) n -
        Pi.π (fun n : ℕ => A.obj (op n)) (n + 1) ≫
          A.map (homOfLE (Nat.le_succ n)).op := by
    simp [Rlim.delta, Rlim.shift]
  exact ConcreteCategory.congr_hom h x

/-- The affine tower whose compatible families solve `(1 - Rlim.shift)x = y`. -/
private noncomputable abbrev affineTower (A : Rlim.InvSystemAb.{u}) (y : Rlim.product A) :
    ℕᵒᵖ ⥤ Type u :=
  Functor.ofOpSequence (X := fun n : ℕ => (A.obj (op n) : Type u)) (fun n =>
    TypeCat.ofHom (fun x : A.obj (op (n + 1)) =>
      A.map (homOfLE (Nat.le_succ n)).op x + prodCoord A y n))

private lemma affineTower_map_succ (A : Rlim.InvSystemAb.{u}) (y : Rlim.product A)
    (n : ℕ) (x : A.obj (op (n + 1))) :
    (affineTower A y).map (homOfLE (Nat.le_succ n)).op x =
      A.map (homOfLE (Nat.le_succ n)).op x + prodCoord A y n := by
  change (Functor.ofOpSequence (X := fun n : ℕ => (A.obj (op n) : Type u))
    (fun n => TypeCat.ofHom (fun x : A.obj (op (n + 1)) =>
      A.map (homOfLE (Nat.le_succ n)).op x + prodCoord A y n))).map
      (homOfLE (Nat.le_succ n)).op x = _
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  exact TypeCat.ofHom_apply _ x

private lemma affineTower_map_eq_add (A : Rlim.InvSystemAb.{u}) (y : Rlim.product A)
    (m n : ℕ) (hmn : m ≤ n) :
    ∃ c : A.obj (op m), ∀ x : A.obj (op n),
      (affineTower A y).map (homOfLE hmn).op x =
        A.map (homOfLE hmn).op x + c := by
  induction n, hmn using Nat.le_induction with
  | base =>
    refine ⟨0, ?_⟩
    intro x
    have hId : (homOfLE (Nat.le_refl m)).op = 𝟙 (op m) := Subsingleton.elim _ _
    rw [hId, CategoryTheory.Functor.map_id (affineTower A y) (op m),
      CategoryTheory.Functor.map_id A (op m)]
    simpa only [add_zero] using
      (CategoryTheory.types_id_apply ((affineTower A y).obj (op m)) x).trans
        (CategoryTheory.id_apply x).symm
  | succ n hmn ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨A.map (homOfLE hmn).op (prodCoord A y n) + c, ?_⟩
    intro x
    have hsplit : (homOfLE (Nat.le_succ_of_le hmn)).op =
        (homOfLE (Nat.le_succ n)).op ≫ (homOfLE hmn).op :=
      Subsingleton.elim _ _
    rw [hsplit, Functor.map_comp, Functor.map_comp]
    change (affineTower A y).map (homOfLE hmn).op
        ((affineTower A y).map (homOfLE (Nat.le_succ n)).op x) = _
    rw [affineTower_map_succ, hc, map_add]
    simp only [CategoryTheory.comp_apply]
    abel

private lemma affineTower_map_eq_add_hom (A : Rlim.InvSystemAb.{u}) (y : Rlim.product A)
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ∃ c : A.obj j, ∀ x : A.obj i,
      (affineTower A y).map f x = A.map f x + c := by
  have hij : j.unop ≤ i.unop := leOfHom f.unop
  obtain ⟨c, hc⟩ := affineTower_map_eq_add A y j.unop i.unop hij
  refine ⟨c, ?_⟩
  intro x
  have hf : f = (homOfLE hij).op := Subsingleton.elim _ _
  simpa only [hf] using hc x

private lemma affineTower_isMittagLeffler (A : Rlim.InvSystemAb.{u}) (y : Rlim.product A)
    (hA : (A ⋙ forget Ab.{u}).IsMittagLeffler) :
    (affineTower A y).IsMittagLeffler := by
  apply ((affineTower A y).isMittagLeffler_iff_subset_range_comp).2
  intro j
  obtain ⟨i, f, hf⟩ :=
    ((A ⋙ forget Ab.{u}).isMittagLeffler_iff_subset_range_comp).1 hA j
  refine ⟨i, f, ?_⟩
  intro k g z hz
  obtain ⟨x, rfl⟩ := hz
  let xa : A.obj i := x
  obtain ⟨cf, hcf⟩ := affineTower_map_eq_add_hom A y f
  obtain ⟨cg, hcg⟩ := affineTower_map_eq_add_hom A y g
  obtain ⟨t, ht⟩ := hf g ⟨xa - cg, rfl⟩
  change A.map (g ≫ f) t = A.map f (xa - cg) at ht
  refine ⟨t, ?_⟩
  rw [Functor.map_comp]
  change (affineTower A y).map f ((affineTower A y).map g t) = _
  have hm : A.map f (A.map g t) = A.map f (xa - cg) := by
    rw [← CategoryTheory.comp_apply, ← A.map_comp]
    exact ht
  conv_rhs => rw [hcf x]
  rw [hcg, hcf, map_add, hm, map_sub]
  abel

/-- A tuple annihilated by `1 - Rlim.shift` is a cone over the tower. -/
private lemma coordinates_compatible_of_delta_eq_zero (A : Rlim.InvSystemAb.{u})
    (x : Rlim.product A) (hx : Rlim.delta A x = 0) {i j : ℕᵒᵖ} (f : i ⟶ j) :
    A.map f (prodCoord A x i.unop) = prodCoord A x j.unop := by
  let F : ℕ → Ab.{u} := fun n ↦ A.obj (op n)
  have hsucc (n : ℕ) :
      A.map (homOfLE (Nat.le_succ n)).op (prodCoord A x (n + 1)) = prodCoord A x n := by
    have hn : prodCoord A (Rlim.delta A x) n = 0 := by
      rw [hx]
      exact map_zero _
    rw [prodCoord_delta] at hn
    exact (sub_eq_zero.mp hn).symm
  have hle (m n : ℕ) (h : m ≤ n) :
      A.map (homOfLE h).op (prodCoord A x n) = prodCoord A x m := by
    induction n, h using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      have hsplit : (homOfLE (Nat.le_succ_of_le hn)).op =
          (homOfLE (Nat.le_succ n)).op ≫ (homOfLE hn).op := by
        apply Subsingleton.elim
      rw [hsplit, Functor.map_comp, ConcreteCategory.comp_apply, hsucc, ih]
  have hij : j.unop ≤ i.unop := leOfHom f.unop
  have hf : f = (homOfLE hij).op := by
    apply Subsingleton.elim
  rw [hf]
  exact hle j.unop i.unop hij

/-- The homomorphism from `ℤ` which sends `1` to a chosen element. -/
private lemma uliftInt_hom_ext {B : Ab.{u}}
    {f g : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ B} (h : f 1 = g 1) : f = g := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  have hx : x = x.down • (1 : ULift.{u} ℤ) := by
    apply ULift.ext
    simp
  change f x = g x
  rw [hx, map_zsmul, map_zsmul, h]

private noncomputable def scalarMap (B : Ab.{u}) (b : B) : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ B :=
  AddCommGrpCat.ofHom
    (zmultiplesHom B b |>.comp AddEquiv.ulift.toAddMonoidHom)

private lemma scalarMap_apply (B : Ab.{u}) (b : B) (z : ULift.{u} ℤ) :
    scalarMap B b z = z.down • b := rfl

private lemma scalarMap_one (B : Ab.{u}) (b : B) : scalarMap B b 1 = b := by
  rw [scalarMap_apply]
  exact one_zsmul b

attribute [local simp] scalarMap_one

/-- A sequence with `xs n - xs (n + 1)|ₙ = y n` gives a preimage of `y` under `1 - Rlim.shift`. -/
private theorem exists_delta_preimage_of_coords (A : Rlim.InvSystemAb.{u}) (y : Rlim.product A)
    (xs : ∀ n : ℕ, A.obj (op n))
    (h : ∀ n : ℕ, xs n - A.map (homOfLE (Nat.le_succ n)).op (xs (n + 1)) = prodCoord A y n) :
    ∃ x, Rlim.delta A x = y := by
  let g : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ Rlim.product A :=
    Pi.lift (fun n => scalarMap (A.obj (op n)) (xs n))
  have hg (n : ℕ) : prodCoord A (g 1) n = xs n := by
    have hn := congrArg (fun f : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ A.obj (op n) => f 1)
      (Pi.lift_comp_π (fun n => scalarMap (A.obj (op n)) (xs n)) n)
    change prodCoord A (g 1) n = scalarMap _ (xs n) 1 at hn
    exact hn.trans (scalarMap_one _ _)
  refine ⟨g 1, ?_⟩
  have hδ (n : ℕ) : prodCoord A (Rlim.delta A (g 1)) n = prodCoord A y n := by
    rw [prodCoord_delta, hg n, hg (n + 1)]
    exact h n
  have hmap : g ≫ Rlim.delta A = scalarMap (Rlim.product A) y := by
    apply Pi.hom_ext
    intro n
    apply uliftInt_hom_ext
    change prodCoord A (Rlim.delta A (g 1)) n = prodCoord A (scalarMap _ y 1) n
    rw [scalarMap_one]
    exact hδ n
  have hval := congrArg (fun k : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ Rlim.product A => k 1) hmap
  simpa [ConcreteCategory.comp_apply, scalarMap, AddEquiv.ulift] using hval

/-- A Mittag--Leffler tower has a surjective product difference map. -/
private theorem deltaMap_surjective_of_mittagLeffler (A : Rlim.InvSystemAb.{u})
    (hA : (A ⋙ forget Ab.{u}).IsMittagLeffler) :
    Function.Surjective (Rlim.delta A) := by
  intro y
  let F := affineTower A y
  have hne (i : ℕᵒᵖ) : Nonempty (F.obj i) := by
    change Nonempty (A.obj i)
    exact ⟨0⟩
  let : ∀ i : ℕᵒᵖ, Nonempty (F.obj i) := hne
  obtain ⟨s, hs⟩ := nonempty_sections_of_mittagLeffler_tower F
    (affineTower_isMittagLeffler A y hA)
  let xs : ∀ n : ℕ, A.obj (op n) := fun n => s (op n)
  refine exists_delta_preimage_of_coords A y xs fun n => ?_
  have h := hs (homOfLE (Nat.le_succ n)).op
  change (affineTower A y).map (homOfLE (Nat.le_succ n)).op (xs (n + 1)) = xs n at h
  rw [affineTower_map_succ] at h
  rw [← h]
  abel

/-- Surjective successor maps make the product difference map surjective. -/
private theorem deltaMap_surjective_of_surjective_successors (A : Rlim.InvSystemAb.{u})
    (h : ∀ n : ℕ, Function.Surjective (A.map (homOfLE (Nat.le_succ n)).op)) :
    Function.Surjective (Rlim.delta A) := by
  intro y
  let xs : ∀ n : ℕ, A.obj (op n) := Nat.rec 0
    (fun n a => Classical.choose (h n (a - prodCoord A y n)))
  refine exists_delta_preimage_of_coords A y xs fun n => ?_
  rw [Classical.choose_spec (h n (xs n - prodCoord A y n))]
  simp

/-- An element of the product killed by `1 - Rlim.shift` determines a cone on the tower. -/
private noncomputable def deltaKernelCone (A : Rlim.InvSystemAb.{u}) (x : Rlim.product A)
    (hx : Rlim.delta A x = 0) : Cone A where
  pt := AddCommGrpCat.of (ULift.{u} ℤ)
  π :=
    { app := fun i => scalarMap (A.obj i) (prodCoord A x i.unop)
      naturality := by
        intro i j f
        change (𝟙 (AddCommGrpCat.of (ULift.{u} ℤ))) ≫ scalarMap (A.obj j)
            (prodCoord A x j.unop) =
          scalarMap (A.obj i) (prodCoord A x i.unop) ≫ A.map f
        apply uliftInt_hom_ext
        simp [scalarMap, coordinates_compatible_of_delta_eq_zero A x hx f] }

/-- Every element of the kernel of the difference map comes from the inverse limit. -/
private lemma delta_kernel_lifts (A : Rlim.InvSystemAb.{u}) (x : Rlim.product A)
    (hx : Rlim.delta A x = 0) : ∃ y : ↑(limit A), Rlim.limitToProduct A y = x := by
  let c : Cone A := deltaKernelCone A x hx
  let g : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ limit A := limit.lift A c
  have hprod : g ≫ Rlim.limitToProduct A = scalarMap (Rlim.product A) x := by
    apply Pi.hom_ext
    intro n
    change (g ≫ Rlim.limitToProduct A) ≫ Pi.π (fun n : ℕ ↦ A.obj (op n)) n =
      scalarMap (Rlim.product A) x ≫ Pi.π (fun n : ℕ ↦ A.obj (op n)) n
    rw [Category.assoc, Rlim.limitToProduct_comp_π]
    change (limit.lift A c ≫ limit.π A (op n)) =
      scalarMap (Rlim.product A) x ≫ Pi.π (fun n : ℕ ↦ A.obj (op n)) n
    rw [limit.lift_π]
    apply uliftInt_hom_ext
    change scalarMap _ (prodCoord A x n) 1 = prodCoord A (scalarMap _ x 1) n
    rw [scalarMap_one, scalarMap_one]
  refine ⟨g 1, ?_⟩
  have hval := congrArg (fun k : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ Rlim.product A => k 1) hprod
  simpa [ConcreteCategory.comp_apply, scalarMap, AddEquiv.ulift, prodCoord] using hval

/-- The natural composite from limits through products and `1 - Rlim.shift` is zero. -/
public theorem limitToProdNatTrans_comp_deltaNatTrans :
    limitToProdNatTrans ≫ deltaNatTrans = 0 := by
  apply NatTrans.ext
  funext A
  exact Rlim.limitToProduct_comp_delta A

/-- The natural composite from limits through products and `1 - Rlim.shift` is zero. -/
theorem limitToProductNatTrans_comp_deltaNatTrans :
    limitToProductNatTrans ≫ deltaNatTrans = 0 := by
  apply NatTrans.ext
  funext A
  exact Rlim.limitToProduct_comp_delta A

/-- The natural limit-product-difference short complex of functors. -/
private noncomputable def deltaFunctorShortComplex :
    ShortComplex (Rlim.InvSystemAb.{u} ⥤ Ab.{u}) :=
  ShortComplex.mk limitToProductNatTrans deltaNatTrans
    limitToProductNatTrans_comp_deltaNatTrans

/-- The canonical limit-product-difference short complex. -/
private noncomputable def deltaShortComplex (A : Rlim.InvSystemAb.{u}) : ShortComplex Ab.{u} :=
  ShortComplex.mk (Rlim.limitToProduct A) (Rlim.delta A) (Rlim.limitToProduct_comp_delta A)

/-- Evaluating the natural short complex recovers the towerwise one. -/
private theorem deltaFunctorShortComplex_eval (A : Rlim.InvSystemAb.{u}) :
    deltaFunctorShortComplex.map ((evaluation Rlim.InvSystemAb.{u} Ab.{u}).obj A) =
      deltaShortComplex A := by
  rfl

/-- The canonical limit map identifies the kernel of `1 - Rlim.shift`. -/
private theorem deltaShortComplex_exact (A : Rlim.InvSystemAb.{u}) :
    (deltaShortComplex A).Exact := by
  rw [(deltaShortComplex A).ab_exact_iff_function_exact]
  intro x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := delta_kernel_lifts A x hx
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    have h := congrArg (fun f : limit A ⟶ Rlim.product A => f y) (Rlim.limitToProduct_comp_delta A)
    simp at h ⊢

/-- If the difference map is epi, the limit-product-difference sequence is short exact. -/
private theorem deltaShortComplex_shortExact_of_surjective (A : Rlim.InvSystemAb.{u})
    (hδ : Function.Surjective (Rlim.delta A)) : (deltaShortComplex A).ShortExact := by
  let : Mono (deltaShortComplex A).f := Rlim.limitToProduct_mono A
  let : Epi (deltaShortComplex A).g :=
    (AddCommGrpCat.epi_iff_surjective _).2 hδ
  exact ⟨deltaShortComplex_exact A⟩

/-- When `1 - Rlim.shift` is onto, it is the cokernel of the inverse-limit inclusion. -/
private noncomputable def deltaMap_isCokernel_of_surjective (A : Rlim.InvSystemAb.{u})
    (hδ : Function.Surjective (Rlim.delta A)) :
    IsColimit (CokernelCofork.ofπ (Rlim.delta A) (Rlim.limitToProduct_comp_delta A)) :=
  (deltaShortComplex_shortExact_of_surjective A hδ).gIsCokernel

/-- The canonical limit-product-difference sequence is short exact for a tower of surjections.
-/
private theorem deltaShortComplex_shortExact_of_surjective_successors (A : Rlim.InvSystemAb.{u})
    (h : ∀ n : ℕ, Function.Surjective (A.map (homOfLE (Nat.le_succ n)).op)) :
    (deltaShortComplex A).ShortExact :=
  deltaShortComplex_shortExact_of_surjective A
    (deltaMap_surjective_of_surjective_successors A h)

/-- A Mittag--Leffler tower has a short exact limit-product-difference sequence. -/
private theorem deltaShortComplex_shortExact_of_mittagLeffler (A : Rlim.InvSystemAb.{u})
    (hA : (A ⋙ forget Ab.{u}).IsMittagLeffler) :
    (deltaShortComplex A).ShortExact :=
  deltaShortComplex_shortExact_of_surjective A
    (deltaMap_surjective_of_mittagLeffler A hA)

/-- Degree-one cohomology of a two-term presentation of `Rlim.delta` vanishes iff it is onto. -/
private theorem isZero_homology_one_iff_surjective_delta (A : Rlim.InvSystemAb.{u})
    (K : CochainComplex Ab.{u} ℤ) (e₀ : K.X 0 ≅ Rlim.product A) (e₁ : K.X 1 ≅ Rlim.product A)
    (hvan : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → IsZero (K.X i))
    (hδ : e₀.inv ≫ K.d 0 1 ≫ e₁.hom = Rlim.delta A) :
    IsZero (K.homology 1) ↔ Function.Surjective (Rlim.delta A) := by
  have hprev : (ComplexShape.up ℤ).prev 1 = 0 := by simp
  have hnext : (ComplexShape.up ℤ).next 1 = 2 := by simp
  have hSg : (K.sc' 0 1 2).g = 0 := (hvan 2 (by norm_num) (by norm_num)).eq_of_tgt _ _
  have hf : Epi (K.d 0 1) ↔ Epi (K.sc' 0 1 2).f := by
    constructor <;> intro h <;> convert h using 1 <;> simp [HomologicalComplex.sc']
  have hδepi : Epi (Rlim.delta A) ↔ Epi (K.d 0 1) := by
    rw [← hδ]
    exact ⟨fun h => (epi_comp_iff_of_isIso _ e₁.hom).1 (epi_of_epi e₀.inv _),
      fun _ => inferInstance⟩
  rw [← K.exactAt_iff_isZero_homology 1, K.exactAt_iff' 0 1 2 hprev hnext,
    (K.sc' 0 1 2).exact_iff_epi hSg, ← hf, ← hδepi, AddCommGrpCat.epi_iff_surjective]

/-- Surjectivity of the product difference map kills degree-one cohomology of its complex. -/
private theorem deltaComplex_h1_zero_of_surjective (A : Rlim.InvSystemAb.{u})
    (hδ : Function.Surjective (Rlim.delta A)) :
    IsZero ((deltaComplex A).homology 1) := by
  obtain ⟨e₀, e₁, hvan, hd⟩ := deltaComplex_model_data A
  exact (isZero_homology_one_iff_surjective_delta A _ e₀ e₁ hvan hd).2 hδ

/-- In particular, a tower of surjections has no degree-one cohomology in the product model.
-/
private theorem deltaComplex_h1_zero_of_surjective_successors (A : Rlim.InvSystemAb.{u})
    (h : ∀ n : ℕ, Function.Surjective (A.map (homOfLE (Nat.le_succ n)).op)) :
    IsZero ((deltaComplex A).homology 1) :=
  deltaComplex_h1_zero_of_surjective A (deltaMap_surjective_of_surjective_successors A h)

/-- The two-term product model has zero first cohomology for a Mittag--Leffler tower. -/
private theorem deltaComplex_h1_zero_of_mittagLeffler (A : Rlim.InvSystemAb.{u})
    (hA : (A ⋙ forget Ab.{u}).IsMittagLeffler) :
    IsZero ((deltaComplex A).homology 1) :=
  deltaComplex_h1_zero_of_surjective A (deltaMap_surjective_of_mittagLeffler A hA)

/-- Degree-one cohomology of the two-term model vanishes precisely when `1 - Rlim.shift` is onto.
-/
private theorem deltaComplex_h1_zero_iff_surjective (A : Rlim.InvSystemAb.{u}) :
    IsZero ((deltaComplex A).homology 1) ↔ Function.Surjective (Rlim.delta A) := by
  obtain ⟨e₀, e₁, hvan, hd⟩ := deltaComplex_model_data A
  exact isZero_homology_one_iff_surjective_delta A _ e₀ e₁ hvan hd

/-- Vanishing of the cohomology of a model complex transfers to the derived object. -/
private theorem isZero_derived_homology_of_model
    (RF : DerivedCategory Rlim.InvSystemAb.{u} ⥤ DerivedCategory Ab.{u}) (A : Rlim.InvSystemAb.{u})
    (K : CochainComplex Ab.{u} ℤ)
    (eRF : RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A) ≅
      DerivedCategory.Q.obj K) (p : ℤ) (h : IsZero (K.homology p)) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{u} p).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A))) :=
  ((Iso.isZero_iff ((DerivedCategory.homologyFunctorFactors Ab.{u} p).app K)).2 h).of_iso
    ((DerivedCategory.homologyFunctor Ab.{u} p).mapIso eRF)

/-- A derived object represented by the product complex has no cohomology above degree one. -/
private theorem derived_higher_vanishes_of_deltaComplex_model
    (RF : DerivedCategory Rlim.InvSystemAb.{u} ⥤ DerivedCategory Ab.{u}) (A : Rlim.InvSystemAb.{u})
    (eRF : RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A) ≅
      DerivedCategory.Q.obj (deltaComplex A)) (p : ℤ) (hp : 1 < p) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{u} p).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A))) :=
  isZero_derived_homology_of_model RF A _ eRF p (deltaComplex_higher_vanishes A p hp)

/-- Any two-term product model has no derived cohomology above degree one. -/
private theorem derived_higher_vanishes_of_model
    (RF : DerivedCategory Rlim.InvSystemAb.{u} ⥤ DerivedCategory Ab.{u}) (A : Rlim.InvSystemAb.{u})
    (K : CochainComplex Ab.{u} ℤ)
    (hvan : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → IsZero (K.X i))
    (hmodel : Nonempty (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A) ≅
      DerivedCategory.Q.obj K)) (p : ℤ) (hp : 1 < p) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{u} p).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A))) := by
  obtain ⟨eRF⟩ := hmodel
  exact isZero_derived_homology_of_model RF A K eRF p
    (K.sc p |>.isZero_homology_of_isZero_X₂ (hvan p (by omega) (by omega)))

/-- For a tower of surjections, the two-term model gives vanishing of the first derived limit. -/
private theorem derived_h1_zero_of_surjective_successors_of_deltaComplex_model
    (RF : DerivedCategory Rlim.InvSystemAb.{u} ⥤ DerivedCategory Ab.{u}) (A : Rlim.InvSystemAb.{u})
    (eRF : RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A) ≅
      DerivedCategory.Q.obj (deltaComplex A))
    (h : ∀ n : ℕ, Function.Surjective (A.map (homOfLE (Nat.le_succ n)).op)) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{u} 1).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A))) :=
  isZero_derived_homology_of_model RF A _ eRF 1 (deltaComplex_h1_zero_of_surjective_successors A h)

/-- The two-term model gives first-derived-limit vanishing for Mittag--Leffler towers. -/
private theorem derived_h1_zero_of_mittagLeffler_of_deltaComplex_model
    (RF : DerivedCategory Rlim.InvSystemAb.{u} ⥤ DerivedCategory Ab.{u}) (A : Rlim.InvSystemAb.{u})
    (eRF : RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A) ≅
      DerivedCategory.Q.obj (deltaComplex A))
    (hA : (A ⋙ forget Ab.{u}).IsMittagLeffler) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{u} 1).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A))) :=
  isZero_derived_homology_of_model RF A _ eRF 1 (deltaComplex_h1_zero_of_mittagLeffler A hA)

/-- Surjectivity of the difference map kills degree-one cohomology in any two-term model. -/
private lemma derived_h1_zero_of_deltaMap_surjective_of_model
    (RF : DerivedCategory Rlim.InvSystemAb.{u} ⥤ DerivedCategory Ab.{u}) (A : Rlim.InvSystemAb.{u})
    (K : CochainComplex Ab.{u} ℤ)
    (e₀ : K.X 0 ≅ Rlim.product A) (e₁ : K.X 1 ≅ Rlim.product A)
    (hvan : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → IsZero (K.X i))
    (hδ : e₀.inv ≫ K.d 0 1 ≫ e₁.hom = Rlim.delta A)
    (eRF : RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A) ≅
      DerivedCategory.Q.obj K)
    (hsurj : Function.Surjective (Rlim.delta A)) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{u} 1).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A))) :=
  isZero_derived_homology_of_model RF A K eRF 1
    ((isZero_homology_one_iff_surjective_delta A K e₀ e₁ hvan hδ).2 hsurj)

/-- In any two-term product model, the Mittag--Leffler condition kills the first derived
limit.
-/
private theorem derived_h1_zero_of_mittagLeffler_of_model
    (RF : DerivedCategory Rlim.InvSystemAb.{u} ⥤ DerivedCategory Ab.{u}) (A : Rlim.InvSystemAb.{u})
    (K : CochainComplex Ab.{u} ℤ)
    (e₀ : K.X 0 ≅ Rlim.product A) (e₁ : K.X 1 ≅ Rlim.product A)
    (hvan : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → IsZero (K.X i))
    (hδ : e₀.inv ≫ K.d 0 1 ≫ e₁.hom = Rlim.delta A)
    (hmodel : Nonempty (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A) ≅
      DerivedCategory.Q.obj K))
    (hA : (A ⋙ forget Ab.{u}).IsMittagLeffler) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{u} 1).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A))) := by
  obtain ⟨eRF⟩ := hmodel
  exact derived_h1_zero_of_deltaMap_surjective_of_model RF A K e₀ e₁ hvan hδ eRF
    (deltaMap_surjective_of_mittagLeffler A hA)

/-- An invertible derived-functor unit gives the stated termwise limit model. -/
private theorem termwise_limit_model_of_isIso_unit
    (RF : DerivedCategory Rlim.InvSystemAb.{u} ⥤ DerivedCategory Ab.{u})
    (α : (lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (K : CochainComplex Rlim.InvSystemAb.{u} ℤ)
    [IsIso (α.app ((HomotopyCategory.quotient Rlim.InvSystemAb.{u}
      (ComplexShape.up ℤ)).obj K))] :
    Nonempty (RF.obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)) := by
  let qIn : DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient Rlim.InvSystemAb.{u} (ComplexShape.up ℤ)).obj K) ≅
      DerivedCategory.Q.obj K :=
    (DerivedCategory.quotientCompQhIso Rlim.InvSystemAb.{u}).app K
  let qOut₀ : ((lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).mapHomotopyCategory
      (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient Rlim.InvSystemAb.{u} (ComplexShape.up ℤ)).obj K) ≅
      (HomotopyCategory.quotient Ab.{u} (ComplexShape.up ℤ)).obj
        (((lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) :=
    (Functor.mapHomotopyCategoryFactors (lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u})
      (ComplexShape.up ℤ)).app K
  let qOut : DerivedCategory.Qh.obj
      (((lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient Rlim.InvSystemAb.{u} (ComplexShape.up ℤ)).obj K)) ≅
      DerivedCategory.Q.obj
        (((lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) :=
    DerivedCategory.Qh.mapIso qOut₀ ≪≫
      (DerivedCategory.quotientCompQhIso Ab.{u}).app _
  exact ⟨(RF.mapIso qIn).symm ≪≫
    (asIso (α.app ((HomotopyCategory.quotient Rlim.InvSystemAb.{u}
      (ComplexShape.up ℤ)).obj K))).symm ≪≫ qOut⟩

/-- The two-term derived-limit model turns vanishing of degree-one cohomology into
surjectivity of `1 - Rlim.shift`. -/
private lemma deltaMap_surjective_of_h1_vanishes
    (RF : DerivedCategory Rlim.InvSystemAb.{u} ⥤ DerivedCategory Ab.{u}) (A : Rlim.InvSystemAb.{u})
    (hR : IsZero ((DerivedCategory.homologyFunctor Ab.{u} 1).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A))))
    (K : CochainComplex Ab.{u} ℤ) (eRF : RF.obj
      ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A) ≅ DerivedCategory.Q.obj K)
    (e₀ : K.X 0 ≅ Rlim.product A) (e₁ : K.X 1 ≅ Rlim.product A)
    (hvan : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → IsZero (K.X i))
    (hδ : e₀.inv ≫ K.d 0 1 ≫ e₁.hom = Rlim.delta A) :
    Function.Surjective (Rlim.delta A) := by
  refine (isZero_homology_one_iff_surjective_delta A K e₀ e₁ hvan hδ).1 ?_
  have hQ : IsZero ((DerivedCategory.homologyFunctor Ab.{u} 1).obj
      (DerivedCategory.Q.obj K)) :=
    hR.of_iso ((DerivedCategory.homologyFunctor Ab.{u} 1).mapIso eRF.symm)
  exact (Iso.isZero_iff ((DerivedCategory.homologyFunctorFactors Ab.{u} 1).app K)).1 hQ

/-- **Bridge for 07KW and 07KX.** If the degree-one derived inverse limit vanishes, the
two-term product model identifies the cokernel of `1 - Rlim.shift` with zero, giving the
  canonical
short exact sequence `0 → lim A → ∏ Aₙ →[1-Rlim.shift] ∏ Aₙ → 0`. -/
private theorem limit_product_delta_shortExact_of_h1_zero
    (RF : DerivedCategory Rlim.InvSystemAb.{u} ⥤ DerivedCategory Ab.{u}) (A : Rlim.InvSystemAb.{u})
    (hR : IsZero ((DerivedCategory.homologyFunctor Ab.{u} 1).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A))))
    (K : CochainComplex Ab.{u} ℤ) (e₀ : K.X 0 ≅ Rlim.product A) (e₁ : K.X 1 ≅ Rlim.product A)
    (hvan : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → IsZero (K.X i))
    (hδ : e₀.inv ≫ K.d 0 1 ≫ e₁.hom = Rlim.delta A)
    (hmodel : Nonempty (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A) ≅
      DerivedCategory.Q.obj K)) : (deltaShortComplex A).ShortExact := by
  obtain ⟨eRF⟩ := hmodel
  exact deltaShortComplex_shortExact_of_surjective A
    (deltaMap_surjective_of_h1_vanishes RF A hR K eRF e₀ e₁ hvan hδ)

/-- If the outgoing differential vanishes, homology is the incoming cokernel. -/
private noncomputable def homologyIsoCokernelOfDNextEqZero
    {C : Type*} [Category* C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex C c) (i j k : ι) (hi : c.prev j = i)
    (hk : c.next j = k) (h : K.d j k = 0) : K.homology j ≅ cokernel (K.d i j) :=
  K.homologyIsoSc' i j k hi hk ≪≫
    (ShortComplex.LeftHomologyData.ofHasCokernel (K.sc' i j k) h).homologyIso

/-- The degree-one homology of a two-term presentation is its specified cokernel. -/
private noncomputable def homologyOneIsoCokernelOfModel
    {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex C ℤ) {X Y : C} (f : X ⟶ Y)
    (e₀ : K.X 0 ≅ X) (e₁ : K.X 1 ≅ Y) (h₂ : IsZero (K.X 2))
    (hd : e₀.inv ≫ K.d 0 1 ≫ e₁.hom = f) : K.homology 1 ≅ cokernel f :=
  homologyIsoCokernelOfDNextEqZero K 0 1 2 (by simp) (by simp)
      (h₂.eq_of_tgt _ _) ≪≫
    cokernel.mapIso (K.d 0 1) f e₀ e₁ (by
      rw [← hd]
      simp)

/-- Any derived object with the product model has the prescribed first cohomology. -/
private theorem derived_h1_iso_cokernel_of_model
    (RF : DerivedCategory Rlim.InvSystemAb.{u} ⥤ DerivedCategory Ab.{u})
    (A : Rlim.InvSystemAb.{u}) (K : CochainComplex Ab.{u} ℤ)
    (e₀ : K.X 0 ≅ Rlim.product A) (e₁ : K.X 1 ≅ Rlim.product A)
    (hvan : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → IsZero (K.X i))
    (hd : e₀.inv ≫ K.d 0 1 ≫ e₁.hom = Rlim.delta A)
    (hmodel : Nonempty (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A) ≅
      DerivedCategory.Q.obj K)) :
    Nonempty (((DerivedCategory.homologyFunctor Ab.{u} 1).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A))) ≅
        cokernel (Rlim.delta A)) := by
  obtain ⟨e⟩ := hmodel
  exact ⟨(DerivedCategory.homologyFunctor Ab.{u} 1).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors Ab.{u} 1).app K ≪≫
    homologyOneIsoCokernelOfModel K (Rlim.delta A) e₀ e₁
      (hvan 2 (by norm_num) (by norm_num)) hd⟩

/-- Uniqueness of right derived functors transports the cokernel computation. -/
private theorem derived_h1_iso_cokernel_of_rightDerivedUnique
    (RF RF' : DerivedCategory Rlim.InvSystemAb.{u} ⥤ DerivedCategory Ab.{u})
    (α : (lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (α' : (lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF')
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso Rlim.InvSystemAb.{u} (ComplexShape.up
      ℤ))]
    [RF'.IsRightDerivedFunctor α' (HomotopyCategory.quasiIso Rlim.InvSystemAb.{u} (ComplexShape.up
      ℤ))]
    (A : Rlim.InvSystemAb.{u})
    (h : Nonempty (((DerivedCategory.homologyFunctor Ab.{u} 1).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A))) ≅
        cokernel (Rlim.delta A))) :
    Nonempty (((DerivedCategory.homologyFunctor Ab.{u} 1).obj
      (RF'.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A))) ≅
        cokernel (Rlim.delta A)) := by
  obtain ⟨e⟩ := h
  exact ⟨(DerivedCategory.homologyFunctor Ab.{u} 1).mapIso
    ((Functor.rightDerivedUnique RF' RF α' α
      (HomotopyCategory.quasiIso Rlim.InvSystemAb.{u} (ComplexShape.up ℤ))).app
        ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A)) ≪≫ e⟩

/-- The tower of initial products of a family of abelian groups. -/
def prefixProductTower (G : ℕ → Ab.{u}) (k : ℕ) : Rlim.InvSystemAb.{u} where
  obj n := AddCommGrpCat.of (∀ i : {i : ℕ // i < n.unop + k}, G i.val)
  map {m n} f := AddCommGrpCat.ofHom
    (AddMonoidHom.pi fun i : {i : ℕ // i < n.unop + k} =>
      Pi.evalAddMonoidHom (fun j : {j : ℕ // j < m.unop + k} => G j.val)
        ⟨i.val, lt_of_lt_of_le i.property (Nat.add_le_add_right (leOfHom f.unop) k)⟩)

/-- A transition map restricts a tuple to a shorter initial interval. -/
lemma prefixProductTower_map_apply (G : ℕ → Ab.{u}) (k : ℕ)
    {m n : ℕᵒᵖ} (f : m ⟶ n) (x : (prefixProductTower G k).obj m)
    (i : {i : ℕ // i < n.unop + k}) :
    (prefixProductTower G k).map f x i =
      x ⟨i.val, lt_of_lt_of_le i.property (Nat.add_le_add_right (leOfHom f.unop) k)⟩ := rfl

/-- A tuple on a shorter interval extends by zero, so the projection is surjective. -/
theorem prefixProductTower_map_surjective (G : ℕ → Ab.{u}) (k : ℕ)
    {m n : ℕᵒᵖ} (f : m ⟶ n) : Function.Surjective ((prefixProductTower G k).map f) := by
  intro x
  refine ⟨fun i => if hi : i.val < n.unop + k then x ⟨i.val, hi⟩ else 0, ?_⟩
  funext i
  simp only [prefixProductTower_map_apply, dite_eq_left i.property]

/-- The initial-product tower is Mittag--Leffler. -/
theorem prefixProductTower_isMittagLeffler (G : ℕ → Ab.{u}) (k : ℕ) :
    (prefixProductTower G k ⋙ forget Ab.{u}).IsMittagLeffler :=
  (prefixProductTower G k ⋙ forget Ab.{u}).isMittagLeffler_of_surjective
    (fun {_ _} f => prefixProductTower_map_surjective G k f)

/-- The diagonal transition maps embed a tower in its initial-product tower. -/
def toPrefixProductTower (A : Rlim.InvSystemAb.{u}) :
    A ⟶ prefixProductTower (fun n => A.obj (op n)) 1 where
  app n := AddCommGrpCat.ofHom
    (AddMonoidHom.pi fun i : {i : ℕ // i < n.unop + 1} =>
      (A.map (homOfLE (Nat.le_of_lt_succ i.property)).op).hom)
  naturality {m n} f := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    funext i
    change (A.map (homOfLE (Nat.le_of_lt_succ i.property)).op) (A.map f x) =
      A.map (homOfLE (Nat.le_of_lt_succ
        (lt_of_lt_of_le i.property (Nat.add_le_add_right (leOfHom f.unop) 1)))).op x
    rw [← ConcreteCategory.comp_apply, ← A.map_comp]
    rfl

lemma toPrefixProductTower_app_apply (A : Rlim.InvSystemAb.{u}) (n : ℕᵒᵖ)
    (x : A.obj n) (i : {i : ℕ // i < n.unop + 1}) :
    (toPrefixProductTower A).app n x i =
      A.map (homOfLE (Nat.le_of_lt_succ i.property)).op x := rfl

/-- The last coordinate of the diagonal embedding is the original element. -/
lemma toPrefixProductTower_app_last (A : Rlim.InvSystemAb.{u}) (n : ℕᵒᵖ)
    (x : A.obj n) :
    (toPrefixProductTower A).app n x ⟨n.unop, Nat.lt_succ_self _⟩ = x := by
  rw [toPrefixProductTower_app_apply]
  have h : (homOfLE (Nat.le_of_lt_succ (Nat.lt_succ_self n.unop))).op = 𝟙 n :=
    Subsingleton.elim _ _
  rw [h, A.map_id]
  rfl

/-- The diagonal embedding is injective at each stage. -/
private theorem toPrefixProductTower_app_mono (A : Rlim.InvSystemAb.{u}) (n : ℕᵒᵖ) :
    Mono ((toPrefixProductTower A).app n) := by
  apply (AddCommGrpCat.mono_iff_injective _).mpr
  intro x y h
  have hlast := congrFun h ⟨n.unop, Nat.lt_succ_self _⟩
  simpa only [toPrefixProductTower_app_last] using hlast

/-- The source construction gives a monomorphism into a Mittag--Leffler tower. -/
theorem exists_mono_mittagLeffler (A : Rlim.InvSystemAb.{u}) :
    ∃ (B : Rlim.InvSystemAb.{u}) (i : A ⟶ B) (_ : Mono i),
      (B ⋙ forget Ab.{u}).IsMittagLeffler := by
  refine ⟨prefixProductTower (fun n => A.obj (op n)) 1, toPrefixProductTower A, ?_,
    prefixProductTower_isMittagLeffler _ _⟩
  have := toPrefixProductTower_app_mono A
  exact NatTrans.mono_of_mono_app _

/-- The finite difference map in the two-step Mittag--Leffler resolution. -/
private def prefixDifference (A : Rlim.InvSystemAb.{u}) :
    prefixProductTower (fun n => A.obj (op n)) 1 ⟶
      prefixProductTower (fun n => A.obj (op n)) 0 where
  app n := AddCommGrpCat.ofHom (AddMonoidHom.pi
    fun i : {i : ℕ // i < n.unop + 0} =>
      Pi.evalAddMonoidHom (fun j : {j : ℕ // j < n.unop + 1} => A.obj (op j.val))
          ⟨i.val, by omega⟩ -
        (A.map (homOfLE (Nat.le_succ i.val)).op).hom.comp
          (Pi.evalAddMonoidHom (fun j : {j : ℕ // j < n.unop + 1} => A.obj (op j.val))
            ⟨i.val + 1, by omega⟩))
  naturality {m n} f := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    rfl

private lemma prefixDifference_app_apply (A : Rlim.InvSystemAb.{u}) (n : ℕᵒᵖ)
    (x : (prefixProductTower (fun n => A.obj (op n)) 1).obj n)
    (i : {i : ℕ // i < n.unop + 0}) :
    (prefixDifference A).app n x i = x ⟨i.val, by omega⟩ -
      A.map (homOfLE (Nat.le_succ i.val)).op (x ⟨i.val + 1, by omega⟩) := rfl

/-- The composite of the diagonal transition map and the finite difference map is zero. -/
private theorem toPrefixProductTower_comp_prefixDifference (A : Rlim.InvSystemAb.{u}) :
    toPrefixProductTower A ≫ prefixDifference A = 0 := by
  apply NatTrans.ext
  funext n
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  funext i
  change (prefixDifference A).app n ((toPrefixProductTower A).app n x) i = 0
  rw [prefixDifference_app_apply, toPrefixProductTower_app_apply,
    toPrefixProductTower_app_apply, sub_eq_zero]
  rw [← ConcreteCategory.comp_apply, ← A.map_comp]
  rfl

/-- Finite backward recursion solves the difference equations with final value zero. -/
private theorem prefixDifference_app_surjective (A : Rlim.InvSystemAb.{u}) (n : ℕᵒᵖ) :
    Function.Surjective ((prefixDifference A).app n) := by
  intro y
  let x : ∀ i : Fin (n.unop + 1), A.obj (op i.val) :=
    Fin.reverseInduction (motive := fun i : Fin (n.unop + 1) => A.obj (op i.val))
      0 (fun i z => y ⟨i.val, i.isLt⟩ + A.map (homOfLE (Nat.le_succ i.val)).op z)
  refine ⟨fun i => x ⟨i.val, i.property⟩, ?_⟩
  funext i
  rw [prefixDifference_app_apply, sub_eq_iff_eq_add]
  exact Fin.reverseInduction_castSucc ⟨i.val, by simpa using i.property⟩

/-- A tuple in the kernel is determined by its final coordinate. -/
private theorem prefixDifference_kernel_lifts (A : Rlim.InvSystemAb.{u}) (n : ℕᵒᵖ)
    (x : (prefixProductTower (fun n => A.obj (op n)) 1).obj n)
    (hx : (prefixDifference A).app n x = 0) :
    ∃ a : A.obj n, (toPrefixProductTower A).app n a = x := by
  let a : A.obj n := x ⟨n.unop, Nat.lt_succ_self _⟩
  have hall : ∀ j : Fin (n.unop + 1),
      A.map (homOfLE (Nat.le_of_lt_succ j.isLt)).op a = x ⟨j.val, j.isLt⟩ := by
    intro j
    refine Fin.reverseInduction ?_ ?_ j
    · have h : (homOfLE (Nat.le_of_lt_succ (Fin.last n.unop).isLt)).op = 𝟙 n :=
        Subsingleton.elim _ _
      rw [h, A.map_id]
      rfl
    · intro i ih
      have hc := congrFun hx ⟨i.val, i.isLt⟩
      change x ⟨i.val, _⟩ -
        A.map (homOfLE (Nat.le_succ i.val)).op (x ⟨i.val + 1, _⟩) = 0 at hc
      have hf : (homOfLE (Nat.le_of_lt_succ i.castSucc.isLt)).op =
          (homOfLE (Nat.le_of_lt_succ i.succ.isLt)).op ≫
            (homOfLE (Nat.le_succ i.val)).op := Subsingleton.elim _ _
      rw [hf, A.map_comp, ConcreteCategory.comp_apply, ih]
      exact (sub_eq_zero.mp hc).symm
  refine ⟨a, ?_⟩
  funext i
  rw [toPrefixProductTower_app_apply]
  exact hall ⟨i.val, i.property⟩

/-- Exactness in a functor category is detected by evaluations. -/
private theorem shortComplex_exact_of_evaluation
    {J C : Type*} [Category* J] [Category* C] [Abelian C]
    (S : ShortComplex (J ⥤ C))
    (h : ∀ j : J, (S.map ((evaluation J C).obj j)).Exact) : S.Exact := by
  apply S.exact_iff_isZero_homology.mpr
  apply (IsZero.iff_id_eq_zero _).mpr
  apply NatTrans.ext
  funext j
  have hz : IsZero (S.homology.obj j) :=
    (((S.map ((evaluation J C).obj j)).exact_iff_isZero_homology).mp (h j)).of_iso
      (S.mapHomologyIso ((evaluation J C).obj j)).symm
  exact hz.eq_of_src _ _

/-- The finite-product construction is a short exact resolution by Mittag--Leffler towers. -/
private theorem prefixProductTower_shortExact (A : Rlim.InvSystemAb.{u}) :
    (ShortComplex.mk (toPrefixProductTower A) (prefixDifference A)
      (toPrefixProductTower_comp_prefixDifference A)).ShortExact := by
  let S := ShortComplex.mk (toPrefixProductTower A) (prefixDifference A)
    (toPrefixProductTower_comp_prefixDifference A)
  have hepi (n : ℕᵒᵖ) : Epi ((prefixDifference A).app n) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr (prefixDifference_app_surjective A n)
  let := toPrefixProductTower_app_mono A
  let := hepi
  have : Mono S.f := NatTrans.mono_of_mono_app _
  have : Epi S.g := NatTrans.epi_of_epi_app _
  refine ⟨shortComplex_exact_of_evaluation S ?_⟩
  intro n
  apply (S.map ((evaluation ℕᵒᵖ Ab.{u}).obj n)).ab_exact_iff.mpr
  exact prefixDifference_kernel_lifts A n

/-- Evaluation at a coordinate of an initial product. -/
private def prefixEvaluation (G : ℕ → Ab.{u}) (k : ℕ) (n : ℕᵒᵖ)
    (i : {i : ℕ // i < n.unop + k}) :
    (prefixProductTower G k).obj n ⟶ G i.val :=
  AddCommGrpCat.ofHom (Pi.evalAddMonoidHom (fun j : {j : ℕ // j < n.unop + k} => G j.val) i)

/-- Restriction of the full product to the initial products. -/
private noncomputable def prefixProductCone (G : ℕ → Ab.{u}) (k : ℕ) :
    Cone (prefixProductTower G k) where
  pt := ∏ᶜ G
  π :=
    { app := fun n => AddCommGrpCat.ofHom
        (AddMonoidHom.pi fun i : {i : ℕ // i < n.unop + k} => (Pi.π G i.val).hom)
      naturality := by
        intro m n f
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro x
        rfl }

private lemma prefixProductCone_π_eval (G : ℕ → Ab.{u}) (k : ℕ) (n : ℕᵒᵖ)
    (i : {i : ℕ // i < n.unop + k}) :
    (prefixProductCone G k).π.app n ≫ prefixEvaluation G k n i = Pi.π G i.val := by
  apply AddCommGrpCat.hom_ext
  rfl

/-- A coordinate of a cone is unchanged by passing to a later stage. -/
private lemma prefixProductCone_coordinate (G : ℕ → Ab.{u}) (k : ℕ)
    (s : Cone (prefixProductTower G k)) {m n : ℕᵒᵖ} (f : m ⟶ n)
    (x : s.pt) (i : {i : ℕ // i < n.unop + k}) :
    s.π.app n x i = s.π.app m x
      ⟨i.val, lt_of_lt_of_le i.property (Nat.add_le_add_right (leOfHom f.unop) k)⟩ := by
  have h := ConcreteCategory.congr_hom (s.w f) x
  exact (congrFun h i).symm

/-- The limit of the tower of initial products is the full product. -/
private noncomputable def prefixProductConeIsLimit (G : ℕ → Ab.{u}) (k : ℕ) :
    IsLimit (prefixProductCone G k) where
  lift s := Pi.lift (fun i => s.π.app (op (i + 1)) ≫
    prefixEvaluation G k (op (i + 1)) ⟨i, by dsimp; omega⟩)
  fac s n := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    funext i
    change Pi.π G i.val ((Pi.lift (fun j => s.π.app (op (j + 1)) ≫
      prefixEvaluation G k (op (j + 1)) ⟨j, by dsimp; omega⟩)) x) = s.π.app n x i
    rw [← ConcreteCategory.comp_apply, Pi.lift_comp_π]
    change s.π.app (op (i.val + 1)) x ⟨i.val, _⟩ = s.π.app n x i
    let m := max (i.val + 1) n.unop
    rw [prefixProductCone_coordinate G k s
        (homOfLE (show i.val + 1 ≤ m from le_max_left _ _)).op,
      prefixProductCone_coordinate G k s
        (homOfLE (show n.unop ≤ m from le_max_right _ _)).op]
  uniq s f hf := by
    apply Pi.hom_ext
    intro i
    have h := congrArg (fun t => t ≫
      prefixEvaluation G k (op (i + 1)) ⟨i, by dsimp; omega⟩) (hf (op (i + 1)))
    rw [Pi.lift_comp_π]
    rw [Category.assoc, prefixProductCone_π_eval] at h
    exact h

/-- Canonical identification of the limit of initial products with the full product. -/
private noncomputable def prefixProductLimitIso (G : ℕ → Ab.{u}) (k : ℕ) :
    limit (prefixProductTower G k) ≅ ∏ᶜ G :=
  limit.isoLimitCone ⟨prefixProductCone G k, prefixProductConeIsLimit G k⟩

private lemma prefixProductLimitIso_inv_π (G : ℕ → Ab.{u}) (k : ℕ) (n : ℕᵒᵖ) :
    (prefixProductLimitIso G k).inv ≫ limit.π (prefixProductTower G k) n =
      (prefixProductCone G k).π.app n :=
  limit.isoLimitCone_inv_π _ _

private lemma prefixProductLimitIso_hom_π (G : ℕ → Ab.{u}) (k : ℕ) (i : ℕ) :
    (prefixProductLimitIso G k).hom ≫ Pi.π G i =
      limit.π (prefixProductTower G k) (op (i + 1)) ≫
        prefixEvaluation G k (op (i + 1)) ⟨i, by dsimp; omega⟩ := by
  rw [← cancel_epi (prefixProductLimitIso G k).inv]
  rw [Iso.inv_hom_id_assoc, ← Category.assoc, prefixProductLimitIso_inv_π,
    prefixProductCone_π_eval]

/-- Taking inverse limits of the finite difference resolution gives `1 - Rlim.shift`. -/
private theorem prefixDifference_limit_eq_delta (A : Rlim.InvSystemAb.{u}) :
    (prefixProductLimitIso (fun n => A.obj (op n)) 1).inv ≫
      lim.map (prefixDifference A) ≫
        (prefixProductLimitIso (fun n => A.obj (op n)) 0).hom = Rlim.delta A := by
  apply Pi.hom_ext
  intro i
  have hL : lim.map (prefixDifference A) ≫
        limit.π (prefixProductTower (fun n => A.obj (op n)) 0) (op (i + 1)) =
      limit.π (prefixProductTower (fun n => A.obj (op n)) 1) (op (i + 1)) ≫
        (prefixDifference A).app (op (i + 1)) := by
    rw [← limMap_eq, limMap_π]
  simp only [Category.assoc, prefixProductLimitIso_hom_π, reassoc_of% hL,
    reassoc_of% (prefixProductLimitIso_inv_π (fun n => A.obj (op n)) 1 (op (i + 1)))]
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  change prodCoord A x i -
      A.map (homOfLE (Nat.le_succ i)).op (prodCoord A x (i + 1)) =
    prodCoord A (Rlim.delta A x) i
  exact (prodCoord_delta A x i).symm

/-- Mittag--Leffler towers satisfy the exactness hypothesis for an adapted class. -/
theorem mittagLeffler_shortExact_map_lim
    (S : ShortComplex Rlim.InvSystemAb.{u}) (hS : S.ShortExact)
    (h₁ : (S.X₁ ⋙ forget Ab).IsMittagLeffler)
    (h₂ : (S.X₂ ⋙ forget Ab).IsMittagLeffler) :
    (S.X₃ ⋙ forget Ab).IsMittagLeffler ∧
      (S.map (lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u})).ShortExact := by
  exact ⟨Ab.isMittagLeffler_X₃_of_shortExact S hS h₂,
    Ab.shortExact_lim_of_isMittagLeffler S hS h₁⟩

/-- The adapted class of Mittag--Leffler towers gives pointwise derived limits on the
bounded below category, with invertible comparison on that class. -/
private theorem lim_hasPointwiseRightDerivedFunctor_and_mittagLeffler_acyclic :
    let F : Rlim.InvSystemAb.{u} ⥤ Ab.{u} := lim
    ∃ h : (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasPointwiseRightDerivedFunctor
        (HomotopyCategory.Plus.quasiIso Rlim.InvSystemAb.{u}),
      letI := h
      ∀ A : Rlim.InvSystemAb.{u}, (A ⋙ forget Ab).IsMittagLeffler → F.rightAcyclic A := by
  let F : Rlim.InvSystemAb.{u} ⥤ Ab.{u} := lim
  let I : ObjectProperty Rlim.InvSystemAb.{u} := fun A => (A ⋙ forget Ab).IsMittagLeffler
  exact F.hasPointwiseRightDerivedFunctor_and_le_rightAcyclic I
    (fun A => by
      obtain ⟨B, i, hi, hB⟩ := exists_mono_mittagLeffler A
      exact ⟨B, hB, i, hi⟩)
    mittagLeffler_shortExact_map_lim

private theorem plus_quasiIso_isSaturatedMultiplicative
    (C : Type*) [Category* C] [Abelian C] :
    (HomotopyCategory.Plus.quasiIso C).IsSaturatedMultiplicative := by
  refine { toIsMultiplicative := inferInstance, mem_of_comp_mem_comp := ?_ }
  intro X Y Z T f g h hfg hgh n
  let H := HomotopyCategory.Plus.ι C ⋙ HomotopyCategory.homologyFunctor C _ n
  have h₁ : IsIso (H.map f ≫ H.map g) := by
    rw [← H.map_comp]
    exact hfg n
  have h₂ : IsIso (H.map g ≫ H.map h) := by
    rw [← H.map_comp]
    exact hgh n
  have : Mono (H.map g) := mono_of_mono _ (H.map h)
  have : Epi (H.map g) := epi_of_epi (H.map f) _
  exact isIso_of_mono_of_epi (H.map g)

/-- A genuine resolving subcategory supplies essential constancy, not just a Kan colimit. -/
private theorem computesRightDerived_of_derivability
    {C : Type*} {H : Type*} [Category* C] [Category* H]
    (G : C ⥤ H) (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
    (hW : W.IsSaturatedMultiplicative) (P : ObjectProperty C)
    (hΦ : (LocalizerMorphism.ofEq (F := P.ι)
      (W₁ := W.inverseImage P.ι) rfl).IsRightDerivabilityStructure)
    (hG : (LocalizerMorphism.ofEq (F := P.ι)
      (W₁ := W.inverseImage P.ι) rfl).Derives G)
    (X : C) (hX : P X) : Functor.ComputesRightDerived G W X := by
  let Φ := LocalizerMorphism.ofEq (F := P.ι) (W₁ := W.inverseImage P.ι) rfl
  let : Φ.IsRightDerivabilityStructure := hΦ
  let (Y : C) : IsFiltered (StacksDerivedShift.RightFractionCat W Y) :=
    Stacks.DerivedFunctor.Computing.isFiltered_rightCat W Y
  apply (Stacks.DerivedFunctor.Computing.rightDerived_everywhereDefined_and_computes G W hW
    {Y | P Y} ?_ ?_).2 X hX
  · intro Y
    let R : Φ.RightResolution Y := Classical.arbitrary _
    exact ⟨R.X₁.obj, R.w, R.hw, R.X₁.property⟩
  · intro Y Z f hf hY hZ
    exact hG (ObjectProperty.homMk f : (⟨Y, hY⟩ : P.FullSubcategory) ⟶ ⟨Z, hZ⟩) hf

private theorem isMittagLeffler_of_isZero (A : Rlim.InvSystemAb.{u}) (hA : IsZero A) :
    (A ⋙ forget Ab).IsMittagLeffler := by
  apply Functor.isMittagLeffler_of_surjective
  intro i j f
  have hsub : Subsingleton (A.obj j) := AddCommGrpCat.subsingleton_of_isZero
    (((evaluation ℕᵒᵖ Ab.{u}).obj j).map_isZero hA)
  change Function.Surjective (A.map f)
  exact fun y => ⟨0, hsub.elim _ _⟩

/-- Mittag--Leffler towers compute the source derived limit: the resolving subcategory
makes the resolution ind-object essentially constant, including all covariant Hom tests. -/
private theorem lim_computesRightDerived_of_mittagLeffler
    (A : Rlim.InvSystemAb.{u}) (hA : (A ⋙ forget Ab).IsMittagLeffler) :
    Functor.ComputesRightDerived
      ((lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
      (HomotopyCategory.Plus.quasiIso Rlim.InvSystemAb.{u})
      ((HomotopyCategory.Plus.singleFunctor Rlim.InvSystemAb.{u} 0).obj A) := by
  let F : Rlim.InvSystemAb.{u} ⥤ Ab.{u} := lim
  let I : ObjectProperty Rlim.InvSystemAb.{u} := fun A => (A ⋙ forget Ab).IsMittagLeffler
  let P : ObjectProperty (HomotopyCategory.Plus Rlim.InvSystemAb.{u}) :=
    fun X => ∀ n, I (X.obj.as.X n)
  let W := HomotopyCategory.Plus.quasiIso Rlim.InvSystemAb.{u}
  have : W.HasLeftCalculusOfFractions := by
    dsimp [W]
    rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]
    infer_instance
  obtain ⟨hΦ, hderive⟩ := F.isRightDerivabilityStructure_and_derives_of_adapted I
    (fun A => by
      obtain ⟨B, i, hi, hB⟩ := exists_mono_mittagLeffler A
      exact ⟨B, hB, i, hi⟩)
    mittagLeffler_shortExact_map_lim
  apply computesRightDerived_of_derivability _ W
    (plus_quasiIso_isSaturatedMultiplicative Rlim.InvSystemAb.{u}) P hΦ hderive
  intro n
  change I (((HomologicalComplex.single Rlim.InvSystemAb.{u} (ComplexShape.up ℤ) 0).obj A).X n)
  by_cases hn : n = 0
  · subst n
    simpa only [HomologicalComplex.single_obj_X_self] using hA
  · exact isMittagLeffler_of_isZero _
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)

/-- Bounded below derived limits are exact and computed on complexes of right acyclic
towers; Mittag--Leffler towers belong to this class. -/
private theorem lim_hasPointwiseRightDerivedFunctor_and_computations :
    let F : Rlim.InvSystemAb.{u} ⥤ Ab.{u} := lim
    ∃ h : (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasPointwiseRightDerivedFunctor
        (HomotopyCategory.Plus.quasiIso Rlim.InvSystemAb.{u}),
      letI := h
      (∀ A : Rlim.InvSystemAb.{u}, (A ⋙ forget Ab).IsMittagLeffler → F.rightAcyclic A) ∧
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerived
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso
          Rlim.InvSystemAb.{u})).IsTriangulated ∧
      ∀ X : HomotopyCategory.Plus Rlim.InvSystemAb.{u},
        (∀ n : ℤ, F.rightAcyclic (X.obj.as.X n)) →
        IsIso (((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
          DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso Rlim.InvSystemAb.{u})).app X) :=
            by
  let F : Rlim.InvSystemAb.{u} ⥤ Ab.{u} := lim
  obtain ⟨hRF, hML⟩ := lim_hasPointwiseRightDerivedFunctor_and_mittagLeffler_acyclic.{u}
  let := hRF
  let : HasDerivedCategory Ab.{u}ᵒᵖ := HasDerivedCategory.standard _
  let : HasDerivedCategory Rlim.InvSystemAb.{u}ᵒᵖ := HasDerivedCategory.standard _
  obtain ⟨h, htri, hcomp⟩ :=
    (Functor.hasDerivedFunctors_of_enough_acyclic_objects F).1 (fun A => by
      obtain ⟨B, i, hi, hB⟩ := exists_mono_mittagLeffler A
      refine ⟨B, i, hi, ?_⟩
      exact lim_computesRightDerived_of_mittagLeffler B hB)
  exact ⟨h, hML, htri, hcomp⟩

/-- The finite-product resolution of a tower. -/
private noncomputable abbrev prefixResolution (A : Rlim.InvSystemAb.{u}) :
    CochainComplex Rlim.InvSystemAb.{u} ℤ :=
  HomologicalComplex.double (prefixDifference A)
    (show (ComplexShape.up ℤ).Rel 0 1 by rfl)

/-- The augmentation of the finite-product resolution. -/
private noncomputable abbrev prefixResolutionUnit (A : Rlim.InvSystemAb.{u}) :
    (CochainComplex.singleFunctor Rlim.InvSystemAb.{u} 0).obj A ⟶ prefixResolution A :=
  Stacks.DoubleResolution.shortExactResolutionUnit
    (ShortComplex.mk (toPrefixProductTower A) (prefixDifference A)
      (toPrefixProductTower_comp_prefixDifference A))

private theorem prefixResolutionUnit_quasiIso (A : Rlim.InvSystemAb.{u}) :
    QuasiIso (prefixResolutionUnit A) :=
  Stacks.DoubleResolution.shortExactResolutionUnit_quasiIso _ (prefixProductTower_shortExact A)

private lemma isoDoubleOfSupport_hom_f_zero
    {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
    (K : CochainComplex C ℤ) {X Y : C} (f : X ⟶ Y)
    (e₀ : K.X 0 ≅ X) (e₁ : K.X 1 ≅ Y)
    (hz : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → IsZero (K.X i))
    (hd : e₀.inv ≫ K.d 0 1 ≫ e₁.hom = f) :
    (Stacks.DoubleResolution.isoDoubleOfSupport K f e₀ e₁ hz hd).hom.f 0 ≫
      (HomologicalComplex.doubleXIso₀ f (by rfl)).hom = e₀.hom := by
  simp [Stacks.DoubleResolution.isoDoubleOfSupport]

private lemma isoDoubleOfSupport_hom_f_one
    {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
    (K : CochainComplex C ℤ) {X Y : C} (f : X ⟶ Y)
    (e₀ : K.X 0 ≅ X) (e₁ : K.X 1 ≅ Y)
    (hz : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → IsZero (K.X i))
    (hd : e₀.inv ≫ K.d 0 1 ≫ e₁.hom = f) :
    (Stacks.DoubleResolution.isoDoubleOfSupport K f e₀ e₁ hz hd).hom.f 1 ≫
      (HomologicalComplex.doubleXIso₁ f (by rfl) (by norm_num)).hom = e₁.hom := by
  simp [Stacks.DoubleResolution.isoDoubleOfSupport]

/-- Taking limits of the finite-product resolution gives the product difference complex.
-/
private noncomputable def prefixResolutionLimitIso (A : Rlim.InvSystemAb.{u}) :
    (((lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (prefixResolution A)) ≅ deltaComplex A := by
  let F : Rlim.InvSystemAb.{u} ⥤ Ab.{u} := lim
  refine Stacks.DoubleResolution.isoDoubleOfSupport _ (Rlim.delta A)
    (F.mapIso (HomologicalComplex.doubleXIso₀ (prefixDifference A) (by rfl)) ≪≫
      prefixProductLimitIso (fun n => A.obj (op n)) 1)
    (F.mapIso (HomologicalComplex.doubleXIso₁ (prefixDifference A) (by rfl) (by norm_num)) ≪≫
      prefixProductLimitIso (fun n => A.obj (op n)) 0) ?_ ?_
  · intro i h₀ h₁
    exact F.map_isZero (HomologicalComplex.isZero_double_X _ _ i h₀ h₁)
  · change (prefixProductLimitIso _ 1).inv ≫ F.map _ ≫ F.map _ ≫
        (F.map _ ≫ (prefixProductLimitIso _ 0).hom) = _
    simp only [← Functor.map_comp_assoc]
    rw [HomologicalComplex.double_d _ _ (by norm_num)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    exact prefixDifference_limit_eq_delta A

private theorem prefixResolution_terms_mittagLeffler (A : Rlim.InvSystemAb.{u}) (i : ℤ) :
    ((prefixResolution A).X i ⋙ forget Ab).IsMittagLeffler := by
  classical
  by_cases h₀ : i = 0
  · subst i
    simpa [prefixResolution, HomologicalComplex.double] using
      prefixProductTower_isMittagLeffler (fun n => A.obj (op n)) 1
  · by_cases h₁ : i = 1
    · subst i
      simpa [prefixResolution, HomologicalComplex.double] using
        prefixProductTower_isMittagLeffler (fun n => A.obj (op n)) 0
    · exact isMittagLeffler_of_isZero _
        (HomologicalComplex.isZero_double_X (prefixDifference A)
          (show (ComplexShape.up ℤ).Rel 0 1 by rfl) i h₀ h₁)

private theorem prefixResolution_isStrictlyGE (A : Rlim.InvSystemAb.{u}) :
    (prefixResolution A).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact HomologicalComplex.isZero_double_X _ _ i (by omega) (by omega)

/-- Bounded below derived limits have the two-term product model. -/
private theorem derivedPlus_deltaComplex_model
    (RF : DerivedCategory.Plus Rlim.InvSystemAb.{u} ⥤ DerivedCategory.Plus Ab.{u})
    (α : (lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ RF)
    (hcompute : ∀ X : HomotopyCategory.Plus Rlim.InvSystemAb.{u},
      (∀ i : ℤ, (X.obj.as.X i ⋙ forget Ab).IsMittagLeffler) → IsIso (α.app X))
    (A : Rlim.InvSystemAb.{u}) :
    Nonempty (DerivedCategory.Plus.ι.obj
        (RF.obj ((DerivedCategory.Plus.singleFunctor Rlim.InvSystemAb.{u} 0).obj A)) ≅
      DerivedCategory.Q.obj (deltaComplex A)) := by
  let K : HomotopyCategory.Plus Rlim.InvSystemAb.{u} :=
    ⟨(HomotopyCategory.quotient _ _).obj (prefixResolution A),
      (HomotopyCategory.plus_quotient_obj_iff _).2 ⟨0, prefixResolution_isStrictlyGE A⟩⟩
  let a : (HomotopyCategory.Plus.singleFunctor Rlim.InvSystemAb.{u} 0).obj A ⟶ K :=
    ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map (prefixResolutionUnit A))
  have : QuasiIso (prefixResolutionUnit A) := prefixResolutionUnit_quasiIso A
  have ha : IsIso (DerivedCategory.Plus.Qh.map a) := by
    suffices IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map a)) from
      isIso_of_reflects_iso _ DerivedCategory.Plus.ι
    change IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ _).map (prefixResolutionUnit A)))
    exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso Rlim.InvSystemAb.{u})
      (prefixResolutionUnit A)).2 inferInstance
  have : IsIso (α.app K) := hcompute K (prefixResolution_terms_mittagLeffler A)
  let eIn : DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.singleFunctor Rlim.InvSystemAb.{u} 0).obj A) ≅
      (DerivedCategory.Plus.singleFunctor Rlim.InvSystemAb.{u} 0).obj A :=
    DerivedCategory.Plus.ι.preimageIso
      ((DerivedCategory.singleFunctorIsoCompQh Rlim.InvSystemAb.{u} 0).app A).symm
  let eOut : DerivedCategory.Plus.ι.obj
        (((lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).mapHomotopyCategoryPlus ⋙
          DerivedCategory.Plus.Qh).obj K) ≅
      DerivedCategory.Q.obj (((lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (prefixResolution A)) :=
    DerivedCategory.Qh.mapIso
      ((Functor.mapHomotopyCategoryFactors (lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u})
        (ComplexShape.up ℤ)).app (prefixResolution A)) ≪≫
      (DerivedCategory.quotientCompQhIso Ab.{u}).app _
  exact ⟨DerivedCategory.Plus.ι.mapIso
      (RF.mapIso (eIn.symm ≪≫ asIso (DerivedCategory.Plus.Qh.map a))) ≪≫
    (DerivedCategory.Plus.ι.mapIso (asIso (α.app K))).symm ≪≫ eOut ≪≫
      DerivedCategory.Q.mapIso (prefixResolutionLimitIso A)⟩

/-- The unbounded derived functor has the same two-term computation whenever its comparison
is invertible on complexes of Mittag--Leffler towers. -/
private theorem derived_deltaComplex_model
    (RF : DerivedCategory Rlim.InvSystemAb.{u} ⥤ DerivedCategory Ab.{u})
    (α : (lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (hcompute : ∀ K : CochainComplex Rlim.InvSystemAb.{u} ℤ,
      (∀ i : ℤ, (K.X i ⋙ forget Ab).IsMittagLeffler) →
        IsIso (α.app ((HomotopyCategory.quotient _ _).obj K)))
    (A : Rlim.InvSystemAb.{u}) :
    Nonempty (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A) ≅
      DerivedCategory.Q.obj (deltaComplex A)) := by
  have : QuasiIso (prefixResolutionUnit A) := prefixResolutionUnit_quasiIso A
  have : IsIso (α.app ((HomotopyCategory.quotient _ _).obj (prefixResolution A))) :=
    hcompute _ (prefixResolution_terms_mittagLeffler A)
  obtain ⟨e⟩ := termwise_limit_model_of_isIso_unit RF α (prefixResolution A)
  exact ⟨RF.mapIso (asIso (DerivedCategory.Q.map (prefixResolutionUnit A))) ≪≫
    e ≪≫ DerivedCategory.Q.mapIso (prefixResolutionLimitIso A)⟩

/-- Surjectivity of the product difference makes the finite-product resolution remain
  exact
after taking inverse limits. -/
private theorem prefixProductTower_map_lim_shortExact (A : Rlim.InvSystemAb.{u})
    (hδ : Function.Surjective (Rlim.delta A)) :
    ((ShortComplex.mk (toPrefixProductTower A) (prefixDifference A)
      (toPrefixProductTower_comp_prefixDifference A)).map
        (lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u})).ShortExact := by
  let S := ShortComplex.mk (toPrefixProductTower A) (prefixDifference A)
    (toPrefixProductTower_comp_prefixDifference A)
  have hS := prefixProductTower_shortExact A
  have : Mono S.f := hS.mono_f
  have hδ' : Epi (Rlim.delta A) := (AddCommGrpCat.epi_iff_surjective _).2 hδ
  have hcomp : Epi ((prefixProductLimitIso (fun n => A.obj (op n)) 1).inv ≫
      lim.map (prefixDifference A) ≫ (prefixProductLimitIso (fun n => A.obj (op n)) 0).hom) := by
    rw [prefixDifference_limit_eq_delta]
    exact hδ'
  have : Epi (lim.map S.g) := by
    exact (epi_comp_iff_of_isIso _
      (prefixProductLimitIso (fun n => A.obj (op n)) 0).hom).1
        (epi_of_epi (prefixProductLimitIso (fun n => A.obj (op n)) 1).inv _)
  exact {
    exact := hS.exact.map_of_mono_of_preservesKernel _ inferInstance inferInstance
    mono_f := by change Mono (lim.map S.f); infer_instance
    epi_g := by change Epi (lim.map S.g); infer_instance }

/-- The bounded below comparison is invertible on every tower with surjective difference map. -/
private theorem rightAcyclic_of_delta_surjective
    [((lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).HasPointwiseRightDerivedFunctor
        (HomotopyCategory.Plus.quasiIso Rlim.InvSystemAb.{u})]
    (hcompute : ∀ X : HomotopyCategory.Plus Rlim.InvSystemAb.{u},
      (∀ i : ℤ, (X.obj.as.X i ⋙ forget Ab).IsMittagLeffler) →
        IsIso ((((lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).mapHomotopyCategoryPlus ⋙
          DerivedCategory.Plus.Qh).totalRightDerivedUnit DerivedCategory.Plus.Qh
            (HomotopyCategory.Plus.quasiIso Rlim.InvSystemAb.{u})).app X))
    (A : Rlim.InvSystemAb.{u}) (hδ : Function.Surjective (Rlim.delta A)) :
    (lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).rightAcyclic A := by
  let F : Rlim.InvSystemAb.{u} ⥤ Ab.{u} := lim
  let G := F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh
  let RF := G.totalRightDerived DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso Rlim.InvSystemAb.{u})
  let α := G.totalRightDerivedUnit DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso Rlim.InvSystemAb.{u})
  let K : HomotopyCategory.Plus Rlim.InvSystemAb.{u} :=
    ⟨(HomotopyCategory.quotient _ _).obj (prefixResolution A),
      (HomotopyCategory.plus_quotient_obj_iff _).2 ⟨0, prefixResolution_isStrictlyGE A⟩⟩
  let a : (HomotopyCategory.Plus.singleFunctor Rlim.InvSystemAb.{u} 0).obj A ⟶ K :=
    ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map (prefixResolutionUnit A))
  have : QuasiIso (prefixResolutionUnit A) := prefixResolutionUnit_quasiIso A
  have : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (prefixResolutionUnit A)) :=
    Stacks.DoubleResolution.map_shortExactResolutionUnit_quasiIso F _
      (prefixProductTower_map_lim_shortExact A hδ)
  have : IsIso (G.map a) := by
    suffices IsIso (DerivedCategory.Plus.ι.map (G.map a)) from
      isIso_of_reflects_iso _ DerivedCategory.Plus.ι
    change IsIso (DerivedCategory.Qh.map
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.quotient _ _).map (prefixResolutionUnit A))))
    exact (NatIso.isIso_map_iff
      (Functor.isoWhiskerRight (Functor.mapHomotopyCategoryFactors F (ComplexShape.up ℤ))
          DerivedCategory.Qh ≪≫
        Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
          (DerivedCategory.quotientCompQhIso Ab.{u})) (prefixResolutionUnit A)).2
      (show IsIso (DerivedCategory.Q.map
        ((F.mapHomologicalComplex _).map (prefixResolutionUnit A))) from inferInstance)
  have : IsIso (α.app K) := hcompute K (prefixResolution_terms_mittagLeffler A)
  have : IsIso (α.app ((HomotopyCategory.Plus.singleFunctor Rlim.InvSystemAb.{u} 0).obj A) ≫
      (DerivedCategory.Plus.Qh ⋙ RF).map a) := by
    rw [← α.naturality a]
    infer_instance
  have : IsIso (DerivedCategory.Plus.Qh.map a) := by
    suffices IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map a)) from
      isIso_of_reflects_iso _ DerivedCategory.Plus.ι
    change IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ _).map (prefixResolutionUnit A)))
    exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso Rlim.InvSystemAb.{u})
      (prefixResolutionUnit A)).2 inferInstance
  have : IsIso ((DerivedCategory.Plus.Qh ⋙ RF).map a) := by
    change IsIso (RF.map (DerivedCategory.Plus.Qh.map a))
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((DerivedCategory.Plus.Qh ⋙ RF).map a)

/-- Applying an additive functor to a one-term complex commutes with localization. -/
private noncomputable def mapHomotopySingleIso
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive] (n : ℤ) :
    HomotopyCategory.singleFunctor C n ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ≅ F ⋙ DerivedCategory.singleFunctor D n :=
  Functor.isoWhiskerLeft (CochainComplex.singleFunctor C n)
    (Functor.isoWhiskerRight (Functor.mapHomotopyCategoryFactors F (ComplexShape.up ℤ))
        DerivedCategory.Qh ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.quotientCompQhIso D)) ≪≫
    Functor.isoWhiskerRight (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n)
      DerivedCategory.Q

/-- A right acyclic tower has zero first cohomology in the product complex. -/
private theorem delta_surjective_of_rightAcyclic
    [((lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).HasPointwiseRightDerivedFunctor
        (HomotopyCategory.Plus.quasiIso Rlim.InvSystemAb.{u})]
    (hcompute : ∀ X : HomotopyCategory.Plus Rlim.InvSystemAb.{u},
      (∀ i : ℤ, (X.obj.as.X i ⋙ forget Ab).IsMittagLeffler) →
        IsIso ((((lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).mapHomotopyCategoryPlus ⋙
          DerivedCategory.Plus.Qh).totalRightDerivedUnit DerivedCategory.Plus.Qh
            (HomotopyCategory.Plus.quasiIso Rlim.InvSystemAb.{u})).app X))
    (A : Rlim.InvSystemAb.{u}) (hA : (lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).rightAcyclic A) :
    Function.Surjective (Rlim.delta A) := by
  let F : Rlim.InvSystemAb.{u} ⥤ Ab.{u} := lim
  let G := F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh
  let RF := G.totalRightDerived DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso Rlim.InvSystemAb.{u})
  let α := G.totalRightDerivedUnit DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso Rlim.InvSystemAb.{u})
  have : IsIso (α.app ((HomotopyCategory.Plus.singleFunctor Rlim.InvSystemAb.{u} 0).obj A)) := hA
  obtain ⟨e⟩ := derivedPlus_deltaComplex_model RF α hcompute A
  let eIn : DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.singleFunctor Rlim.InvSystemAb.{u} 0).obj A) ≅
      (DerivedCategory.Plus.singleFunctor Rlim.InvSystemAb.{u} 0).obj A :=
    DerivedCategory.Plus.ι.preimageIso
      ((DerivedCategory.singleFunctorIsoCompQh Rlim.InvSystemAb.{u} 0).app A).symm
  let e' : DerivedCategory.Q.obj (deltaComplex A) ≅
      (DerivedCategory.singleFunctor Ab.{u} 0).obj (F.obj A) :=
    e.symm ≪≫ DerivedCategory.Plus.ι.mapIso (RF.mapIso eIn.symm) ≪≫
      (DerivedCategory.Plus.ι.mapIso (asIso (α.app _))).symm ≪≫
        (mapHomotopySingleIso F 0).app A
  apply (deltaComplex_h1_zero_iff_surjective A).1
  exact (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0
    (F.obj A) 1 (by norm_num)).of_iso
      (((DerivedCategory.homologyFunctorFactors Ab.{u} 1).app (deltaComplex A)).symm ≪≫
        (DerivedCategory.homologyFunctor Ab.{u} 1).mapIso e' ≪≫
        (DerivedCategory.homologyFunctorFactors Ab.{u} 1).app _)

/-- The degree-zero unit of derived inverse limit is an isomorphism, since inverse limit
preserves the kernel in the finite-product resolution. -/
private theorem isIso_homology_zero_unit
    (RF : DerivedCategory Rlim.InvSystemAb.{u} ⥤ DerivedCategory Ab.{u})
    (α : (lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (hcompute : ∀ K : CochainComplex Rlim.InvSystemAb.{u} ℤ,
      (∀ i : ℤ, (K.X i ⋙ forget Ab).IsMittagLeffler) →
        IsIso (α.app ((HomotopyCategory.quotient _ _).obj K)))
    (A : Rlim.InvSystemAb.{u}) :
    IsIso ((DerivedCategory.homologyFunctor Ab.{u} 0).map
      (α.app ((HomotopyCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A))) := by
  let F : Rlim.InvSystemAb.{u} ⥤ Ab.{u} := lim
  let H := DerivedCategory.homologyFunctor Ab.{u} 0
  let a := (HomotopyCategory.quotient _ _).map (prefixResolutionUnit A)
  let S := ShortComplex.mk (toPrefixProductTower A) (prefixDifference A)
    (toPrefixProductTower_comp_prefixDifference A)
  have hS := prefixProductTower_shortExact A
  have : Mono S.f := hS.mono_f
  have : QuasiIsoAt ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (prefixResolutionUnit A)) 0 :=
    Stacks.DoubleResolution.map_shortExactResolutionUnit_quasiIsoAt_zero F S
      (hS.exact.map_of_mono_of_preservesKernel F inferInstance inferInstance)
  have : IsIso (((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙ H).map a) := by
    exact (NatIso.isIso_map_iff
      (Functor.isoWhiskerRight
        (Functor.isoWhiskerRight (Functor.mapHomotopyCategoryFactors F (ComplexShape.up ℤ))
            DerivedCategory.Qh ≪≫
          Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
            (DerivedCategory.quotientCompQhIso Ab.{u})) H ≪≫
        Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
          (DerivedCategory.homologyFunctorFactors Ab.{u} 0)) (prefixResolutionUnit A)).2
      ((quasiIsoAt_iff_isIso_homologyMap _ 0).1 inferInstance)
  have : IsIso (H.map (DerivedCategory.Qh.map
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map a))) :=
    inferInstanceAs (IsIso (((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙
      H).map a))
  have : IsIso (α.app ((HomotopyCategory.quotient _ _).obj (prefixResolution A))) :=
    hcompute _ (prefixResolution_terms_mittagLeffler A)
  have : QuasiIso (prefixResolutionUnit A) := prefixResolutionUnit_quasiIso A
  have : IsIso (DerivedCategory.Qh.map a) :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso Rlim.InvSystemAb.{u})
      (prefixResolutionUnit A)).2 inferInstance
  have : IsIso (H.map (α.app ((HomotopyCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A)) ≫
      H.map (RF.map (DerivedCategory.Qh.map a))) := by
    have hw := congrArg H.map (α.naturality a)
    simp only [Functor.comp_map, Functor.map_comp,
      HomotopyCategory.quotient_obj_singleFunctors_obj] at hw
    rw [← hw]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (H.map (RF.map (DerivedCategory.Qh.map a)))

private theorem lim_iso_derived_homology_zero
    (RF : DerivedCategory Rlim.InvSystemAb.{u} ⥤ DerivedCategory Ab.{u})
    (α : (lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (hcompute : ∀ K : CochainComplex Rlim.InvSystemAb.{u} ℤ,
      (∀ i : ℤ, (K.X i ⋙ forget Ab).IsMittagLeffler) →
        IsIso (α.app ((HomotopyCategory.quotient _ _).obj K))) :
    Nonempty ((lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}) ≅
      DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0 ⋙ RF ⋙
        DerivedCategory.homologyFunctor Ab.{u} 0) := by
  let F : Rlim.InvSystemAb.{u} ⥤ Ab.{u} := lim
  let H := DerivedCategory.homologyFunctor Ab.{u} 0
  let β := Functor.whiskerRight
    (Functor.whiskerLeft (HomotopyCategory.singleFunctor Rlim.InvSystemAb.{u} 0) α) H
  have hβ (A : Rlim.InvSystemAb.{u}) : IsIso (β.app A) :=
    isIso_homology_zero_unit RF α hcompute A
  let eβ := NatIso.ofComponents (fun A => @asIso _ _ _ _ (β.app A) (hβ A))
    (fun f => β.naturality f)
  let e : HomotopyCategory.singleFunctor Rlim.InvSystemAb.{u} 0 ⋙
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⋙ H ≅ F :=
    Functor.isoWhiskerRight (mapHomotopySingleIso F 0) H ≪≫
      Functor.isoWhiskerLeft F (DerivedCategory.singleFunctorCompHomologyFunctorIso Ab.{u} 0) ≪≫
        F.rightUnitor
  exact ⟨e.symm ≪≫ eβ ≪≫
    Functor.isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQh Rlim.InvSystemAb.{u} 0).symm (RF
      ⋙ H)⟩

/-- An additive natural transformation invertible on two objects is invertible on their
biproduct. -/
private theorem isIso_app_biprod
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) (X Y : C)
    [IsIso (α.app X)] [IsIso (α.app Y)] : IsIso (α.app (X ⊞ Y)) := by
  have : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  have : PreservesBinaryBiproducts G := preservesBinaryBiproducts_of_preservesBiproducts G
  have h : α.app (X ⊞ Y) = (F.mapBiprod X Y).hom ≫
      biprod.map (α.app X) (α.app Y) ≫ (G.mapBiprod X Y).inv := by
    rw [← cancel_mono (G.mapBiprod X Y).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply biprod.hom_ext
    · simp only [Category.assoc, Functor.mapBiprod_hom, biprod.lift_fst,
        biprod.map_fst, biprod.lift_fst_assoc]
      exact (α.naturality biprod.fst).symm
    · simp only [Category.assoc, Functor.mapBiprod_hom, biprod.lift_snd,
        biprod.map_snd, biprod.lift_snd_assoc]
      exact (α.naturality biprod.snd).symm
  rw [h]
  exact ((F.mapBiprod X Y) ≪≫ biprod.mapIso (asIso (α.app X)) (asIso (α.app Y)) ≪≫
    (G.mapBiprod X Y).symm).isIso_hom

/-- **Stacks 07KW.** The inverse-limit functor on inverse systems of abelian groups has a right
derived functor on the unbounded derived category. Higher derived limits vanish above degree one;
the derived limit of a system is represented by the two-term product complex with differential
`(x_n) ↦ (x_n - f_{n+1}(x_{n+1}))`; Mittag--Leffler systems have vanishing first derived limit;
every complex has a quasi-isomorphic complex of right-acyclic terms; and on such a complex the
derived limit is represented by the termwise inverse-limit complex. Its shift structure and
natural degree-zero comparison give an exact functor on the derived categories. The ordinary
limit is the kernel of the product differential, its first derived limit is the cokernel, and
the latter identification holds for any right-derived functor. -/
@[stacks 07KW]
public theorem lim_hasRightDerivedFunctor_and_computations :
    let F : Rlim.InvSystemAb.{u} ⥤ Ab.{u} := lim
    let P := Rlim.product.{u}
    let δ := Rlim.delta.{u}
    ∃ (RF : DerivedCategory Rlim.InvSystemAb.{u} ⥤ DerivedCategory Ab.{u})
      (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
        DerivedCategory.Qh ⋙ RF),
      RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso Rlim.InvSystemAb.{u} (ComplexShape.up
        ℤ)) ∧
      (∀ (A : Rlim.InvSystemAb.{u}) (p : ℤ), 1 < p →
        IsZero ((DerivedCategory.homologyFunctor Ab.{u} p).obj
          (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A)))) ∧
      (∀ A : Rlim.InvSystemAb.{u}, ∃ (K : CochainComplex Ab.{u} ℤ)
          (e₀ : K.X 0 ≅ P A) (e₁ : K.X 1 ≅ P A),
        (∀ i : ℤ, i ≠ 0 → i ≠ 1 → IsZero (K.X i)) ∧
        e₀.inv ≫ K.d 0 1 ≫ e₁.hom = δ A ∧
        Nonempty (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A) ≅
          DerivedCategory.Q.obj K)) ∧
      (∀ A : Rlim.InvSystemAb.{u}, (A ⋙ forget Ab).IsMittagLeffler →
        IsZero ((DerivedCategory.homologyFunctor Ab.{u} 1).obj
          (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A)))) ∧
      (∀ K : CochainComplex Rlim.InvSystemAb.{u} ℤ,
        ∃ (L : CochainComplex Rlim.InvSystemAb.{u} ℤ) (f : K ⟶ L) (_ : QuasiIso f),
          ∀ p : ℤ, IsZero ((DerivedCategory.homologyFunctor Ab.{u} 1).obj
            (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj (L.X p))))) ∧
      (∀ K : CochainComplex Rlim.InvSystemAb.{u} ℤ,
        (∀ p : ℤ, IsZero ((DerivedCategory.homologyFunctor Ab.{u} 1).obj
          (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj (K.X p))))) →
        Nonempty (RF.obj (DerivedCategory.Q.obj K) ≅
          DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) ∧
      (∀ A : Rlim.InvSystemAb.{u},
        ∃ e : limit A ≅ kernel (δ A),
          ∀ n : ℕ, e.hom ≫ kernel.ι (δ A) ≫
            Pi.π (fun n : ℕ ↦ A.obj (Opposite.op n)) n =
              limit.π A (Opposite.op n)) ∧
      (∀ A : Rlim.InvSystemAb.{u},
        Nonempty (((DerivedCategory.homologyFunctor Ab.{u} 1).obj
          (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A))) ≅
            cokernel (δ A))) ∧
      (∀ A : Rlim.InvSystemAb.{u},
        IsZero ((DerivedCategory.homologyFunctor Ab.{u} 1).obj
          (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A))) →
        ∃ w : Rlim.limitToProduct A ≫ δ A = 0,
          (ShortComplex.mk (Rlim.limitToProduct A) (δ A) w).ShortExact) ∧
      (∀ (RF' : DerivedCategory Rlim.InvSystemAb.{u} ⥤ DerivedCategory Ab.{u})
        (α' : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
          DerivedCategory.Qh ⋙ RF'),
        RF'.IsRightDerivedFunctor α'
          (HomotopyCategory.quasiIso Rlim.InvSystemAb.{u} (ComplexShape.up ℤ)) →
        ∀ A : Rlim.InvSystemAb.{u},
          Nonempty (((DerivedCategory.homologyFunctor Ab.{u} 1).obj
            (RF'.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A))) ≅
              cokernel (δ A))) ∧
      ∃ (commShift : RF.CommShift ℤ),
        letI : RF.CommShift ℤ := commShift
        NatTrans.CommShift α ℤ ∧ RF.IsTriangulated ∧
          Nonempty (F ≅ DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0 ⋙ RF ⋙
            DerivedCategory.homologyFunctor Ab.{u} 0) := by
  classical
  dsimp only
  obtain ⟨hRFplus, hML, htriPlus, hcomputePlus⟩ :=
    lim_hasPointwiseRightDerivedFunctor_and_computations.{u}
  let := hRFplus
  have hmono (A : Rlim.InvSystemAb.{u}) :
      ∃ (B : Rlim.InvSystemAb.{u}) (i : A ⟶ B) (_ : Mono i),
        (lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).rightAcyclic B := by
    obtain ⟨B, i, hi, hB⟩ := exists_mono_mittagLeffler A
    exact ⟨B, i, hi, hML B hB⟩
  let F : Rlim.InvSystemAb.{u} ⥤ Ab.{u} := lim
  let RFplus := (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerived
    DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso Rlim.InvSystemAb.{u})
  let αplus := (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
    DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso Rlim.InvSystemAb.{u})
  have hmodelPlus := derivedPlus_deltaComplex_model RFplus αplus
    (fun X hX => hcomputePlus X (fun i => hML _ (hX i)))
  have htwo (A : Rlim.InvSystemAb.{u}) :
      IsZero ((DerivedCategory.Plus.homologyFunctor Ab.{u} (2 : ℕ)).obj
        (RFplus.obj ((DerivedCategory.Plus.singleFunctor Rlim.InvSystemAb.{u} 0).obj A))) := by
    obtain ⟨e⟩ := hmodelPlus A
    exact (deltaComplex_higher_vanishes A 2 (by norm_num)).of_iso
      ((DerivedCategory.homologyFunctor Ab.{u} 2).mapIso e ≪≫
        (DerivedCategory.homologyFunctorFactors Ab.{u} 2).app (deltaComplex A))
  obtain ⟨hRF, hreplace, hcompute⟩ :=
    Functor.hasRightDerivedFunctor_of_isZero_rightDerived F RFplus αplus F.rightAcyclic
      (fun A => (Functor.computesRightDerived_iff_isIso_unit_of_enough_source_acyclic_objects
        F (fun A => by
          obtain ⟨B, i, hi, hB⟩ := exists_mono_mittagLeffler A
          exact ⟨B, i, hi, lim_computesRightDerived_of_mittagLeffler B hB⟩)
        RFplus αplus ((HomotopyCategory.Plus.singleFunctor _ 0).obj A)).symm) hmono 2 htwo
  let := hRF
  let RF := (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
    DerivedCategory.Qh (HomotopyCategory.quasiIso Rlim.InvSystemAb.{u} (ComplexShape.up ℤ))
  let α := (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit
    DerivedCategory.Qh (HomotopyCategory.quasiIso Rlim.InvSystemAb.{u} (ComplexShape.up ℤ))
  have hcomp := (hcompute RF α).1
  have hmodel := derived_deltaComplex_model RF α
    (fun K hK => hcomp K (fun i => hML _ (hK i)))
  have hcomputeML (K : CochainComplex Rlim.InvSystemAb.{u} ℤ)
      (hK : ∀ i : ℤ, (K.X i ⋙ forget Ab).IsMittagLeffler) :
      IsIso (α.app ((HomotopyCategory.quotient _ _).obj K)) :=
    hcomp K (fun i => hML _ (hK i))
  have hcomputePlusML (X : HomotopyCategory.Plus Rlim.InvSystemAb.{u})
      (hX : ∀ i : ℤ, (X.obj.as.X i ⋙ forget Ab).IsMittagLeffler) :
      IsIso (αplus.app X) := hcomputePlus X (fun i => hML _ (hX i))
  have h₁iff (A : Rlim.InvSystemAb.{u}) :
      IsZero ((DerivedCategory.homologyFunctor Ab.{u} 1).obj
        (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A))) ↔
      Function.Surjective (Rlim.delta A) := by
    obtain ⟨e⟩ := hmodel A
    exact (Iso.isZero_iff ((DerivedCategory.homologyFunctor Ab.{u} 1).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors Ab.{u} 1).app (deltaComplex A))).trans
        (deltaComplex_h1_zero_iff_surjective A)
  have hac (A : Rlim.InvSystemAb.{u}) :
      IsZero ((DerivedCategory.homologyFunctor Ab.{u} 1).obj
        (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A))) ↔ F.rightAcyclic A
          :=
    (h₁iff A).trans ⟨rightAcyclic_of_delta_surjective hcomputePlusML A,
      delta_surjective_of_rightAcyclic hcomputePlusML A⟩
  have hcoker (A : Rlim.InvSystemAb.{u}) :
      Nonempty (((DerivedCategory.homologyFunctor Ab.{u} 1).obj
        (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A))) ≅ cokernel
          (Rlim.delta A)) := by
    obtain ⟨e₀, e₁, hz, hd⟩ := deltaComplex_model_data A
    exact derived_h1_iso_cokernel_of_model RF A _ e₀ e₁ hz hd (hmodel A)
  let commShift := Functor.IsRightDerivedFunctor.commShift RF α
    (HomotopyCategory.quasiIso Rlim.InvSystemAb.{u} (ComplexShape.up ℤ)) ℤ
  let : RF.CommShift ℤ := commShift
  have hαshift : NatTrans.CommShift α ℤ := inferInstance
  have htri : RF.IsTriangulated := by
    have : RFplus.IsTriangulated := htriPlus
    apply StacksDraft.RightDerivedBoundedDimension.isTriangulated_of_acyclic_replacements
      F RF α F.rightAcyclic ?_ ?_ hreplace hcomp
    · intro X Y e hX
      exact (NatTrans.isIso_app_iff_of_iso αplus
        ((HomotopyCategory.Plus.singleFunctor Rlim.InvSystemAb.{u} 0).mapIso e)).1 hX
    · intro X Y hX hY
      let β := Functor.whiskerLeft (HomotopyCategory.Plus.singleFunctor Rlim.InvSystemAb.{u} 0)
        αplus
      have : IsIso (β.app X) := hX
      have : IsIso (β.app Y) := hY
      exact isIso_app_biprod β X Y
  refine ⟨RF, α, inferInstance, ?_, ?_, ?_, ?_, ?_,
    Rlim.limit_kernel_iso, hcoker, ?_, ?_, ?_⟩
  · intro A p hp
    exact derived_higher_vanishes_of_deltaComplex_model RF A (hmodel A).some p hp
  · intro A
    obtain ⟨e₀, e₁, hz, hd⟩ := deltaComplex_model_data A
    exact ⟨deltaComplex A, e₀, e₁, hz, hd, hmodel A⟩
  · intro A hA
    exact (h₁iff A).2 (deltaMap_surjective_of_mittagLeffler A hA)
  · intro K
    obtain ⟨L, f, hf, hL⟩ := hreplace K
    exact ⟨L, f, hf, fun i => (hac (L.X i)).2 (hL i)⟩
  · intro K hK
    have := hcomp K (fun i => (hac (K.X i)).1 (hK i))
    exact termwise_limit_model_of_isIso_unit RF α K
  · intro A hA
    exact ⟨Rlim.limitToProduct_comp_delta A,
      deltaShortComplex_shortExact_of_surjective A ((h₁iff A).1 hA)⟩
  · intro RF' α' hRF' A
    let := hRF'
    exact derived_h1_iso_cokernel_of_rightDerivedUnique RF RF' α α' A (hcoker A)
  · exact ⟨commShift, hαshift, htri, lim_iso_derived_homology_zero RF α hcomputeML⟩

end Rlim

end

end


section

set_option maxRecDepth 4096

@[expose] public noncomputable section

open CategoryTheory Limits DerivedCategory

namespace Rlim

universe u

noncomputable local instance : HasDerivedCategory Ab.{u} := HasDerivedCategory.standard _

noncomputable local instance : HasDerivedCategory Rlim.InvSystemAb.{u} :=
  HasDerivedCategory.standard _

noncomputable local instance : (lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Every right-derived inverse-limit functor has the same first cohomology, namely the
cokernel of `1 - Rlim.shift`. -/
public theorem firstDerivedLimit_iso_cokernel_of_isRightDerivedFunctor
    (RF : DerivedCategory Rlim.InvSystemAb.{u} ⥤ DerivedCategory Ab.{u})
    (α : (lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (hRF : RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso Rlim.InvSystemAb.{u} (ComplexShape.up ℤ)))
    (A : Rlim.InvSystemAb.{u}) :
    Nonempty (((DerivedCategory.homologyFunctor Ab.{u} 1).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A))) ≅
        Rlim.firstDerivedLimit A) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hAny, _⟩ :=
    lim_hasRightDerivedFunctor_and_computations.{u}
  exact hAny RF α hRF A

/-- **Stacks 08U4.** The inverse-limit functor on inverse systems of abelian groups has a
right derived functor from `D(Ab(N))` to `D(Ab)`. -/
@[stacks 08U4]
public theorem lim_hasRightDerivedFunctor :
    let F : Rlim.InvSystemAb ⥤ Ab.{0} := lim
    ∃ (RF : DerivedCategory Rlim.InvSystemAb ⥤ DerivedCategory Ab.{0})
      (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
        DerivedCategory.Qh ⋙ RF),
      RF.IsRightDerivedFunctor α
        (HomotopyCategory.quasiIso Rlim.InvSystemAb (ComplexShape.up ℤ)) := by
  obtain ⟨RF, α, hRF, _⟩ := Rlim.lim_hasRightDerivedFunctor_and_computations
  exact ⟨RF, α, hRF⟩

end Rlim

end

end


section

@[expose] public noncomputable section

open CategoryTheory Limits DerivedCategory

namespace Rlim


universe u

noncomputable local instance : HasDerivedCategory Ab.{u} := HasDerivedCategory.standard _

noncomputable local instance : HasDerivedCategory Rlim.InvSystemAb.{u} :=
  HasDerivedCategory.standard _

noncomputable local instance : (lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).Additive :=
  Functor.additive_of_preserves_binary_products _

set_option linter.tacticCheckInstances false in
/-- **Stacks 0H31.** A short exact sequence of inverse systems of abelian groups induces
the exact sequence
`0 ⟶ lim A ⟶ lim B ⟶ lim C ⟶ R¹lim A ⟶ R¹lim B ⟶ R¹lim C ⟶ 0`.
The maps other than the connecting morphism are the functorial maps of `lim` and `R¹lim`.
The connecting morphism is canonically obtained from the distinguished triangle of the short
exact sequence and is natural in morphisms of short exact sequences. -/
@[stacks 0H31]
public theorem exists_sixTerm_exact_sequence_lim_rightDerived_one
    {S : ShortComplex Rlim.InvSystemAb.{u}} (hS : S.ShortExact) :
    let F : Rlim.InvSystemAb.{u} ⥤ Ab.{u} := lim
    ∃ (RF : DerivedCategory Rlim.InvSystemAb.{u} ⥤ DerivedCategory Ab.{u})
      (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
        DerivedCategory.Qh ⋙ RF) (commShift : RF.CommShift ℤ),
      letI : RF.CommShift ℤ := commShift
      RF.IsRightDerivedFunctor α
          (HomotopyCategory.quasiIso Rlim.InvSystemAb.{u} (ComplexShape.up ℤ)) ∧
        RF.IsTriangulated ∧
        let R (n : ℤ) : Rlim.InvSystemAb.{u} ⥤ Ab.{u} :=
          DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0 ⋙ RF ⋙
            DerivedCategory.homologyFunctor Ab.{u} n
        ∃ e : F ≅ R 0,
          let δ : ∀ {T : ShortComplex Rlim.InvSystemAb.{u}}, T.ShortExact →
              (F.obj T.X₃ ⟶ (R 1).obj T.X₁) := fun {T} (hT : T.ShortExact) ↦ by
            change F.obj T.X₃ ⟶
              (DerivedCategory.homologyFunctor Ab.{u} 1).obj
                (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj T.X₁))
            exact e.hom.app T.X₃ ≫
              DerivedCategory.HomologySequence.δ
                (RF.mapTriangle.obj hT.singleTriangle) 0 1 rfl
          (ComposableArrows.mk₅ (F.map S.f) (F.map S.g) (δ hS)
              ((R 1).map S.f) ((R 1).map S.g)).Exact ∧
            Mono (F.map S.f) ∧ Epi ((R 1).map S.g) ∧
            ∀ {T₁ T₂ : ShortComplex Rlim.InvSystemAb.{u}}
              (h₁ : T₁.ShortExact) (h₂ : T₂.ShortExact) (f : T₁ ⟶ T₂),
              δ h₁ ≫ (R 1).map f.τ₁ = F.map f.τ₃ ≫ δ h₂ := by
  dsimp only
  obtain ⟨RF, α, hRF, hvanish, _, _, _, _, _, _, _, _, commShift, hlast⟩ :=
    lim_hasRightDerivedFunctor_and_computations.{u}
  let : RF.CommShift ℤ := commShift
  have htri : RF.IsTriangulated := hlast.2.1
  let e := Classical.choice hlast.2.2
  let R (n : ℤ) : Rlim.InvSystemAb.{u} ⥤ Ab.{u} :=
    DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0 ⋙ RF ⋙
      DerivedCategory.homologyFunctor Ab.{u} n
  let δ : ∀ {T : ShortComplex Rlim.InvSystemAb.{u}}, T.ShortExact →
      (lim.obj T.X₃ ⟶ (R 1).obj T.X₁) := fun {T} hT ↦
    e.hom.app T.X₃ ≫ DerivedCategory.HomologySequence.δ
      (RF.mapTriangle.obj hT.singleTriangle) 0 1 rfl
  refine ⟨RF, α, commShift, hRF, htri, e, ?_, ?_, ?_, ?_⟩
  · let T := RF.mapTriangle.obj hS.singleTriangle
    have hT : T ∈ distTriang (DerivedCategory Ab.{u}) :=
      RF.map_distinguished _ hS.singleTriangle_distinguished
    have hE :=
      (DerivedCategory.homologyFunctor Ab.{u} 0).homologySequenceComposableArrows₅_exact
        T hT 0 1 rfl
    let dS : (R 0).obj S.X₃ ⟶ (R 1).obj S.X₁ :=
      DerivedCategory.HomologySequence.δ (RF.mapTriangle.obj hS.singleTriangle) 0 1 rfl
    change (ComposableArrows.mk₅ ((R 0).map S.f) ((R 0).map S.g)
      dS
      ((R 1).map S.f) ((R 1).map S.g)).Exact at hE
    let E := ComposableArrows.mk₅ ((R 0).map S.f) ((R 0).map S.g)
      dS
      ((R 1).map S.f) ((R 1).map S.g)
    let D := ComposableArrows.mk₅ (lim.map S.f) (lim.map S.g) (δ hS)
      ((R 1).map S.f) ((R 1).map S.g)
    let i : E ≅ D := ComposableArrows.isoMk₅
      (e.symm.app S.X₁) (e.symm.app S.X₂) (e.symm.app S.X₃)
      (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by change (R 0).map S.f ≫ e.inv.app S.X₂ = e.inv.app S.X₁ ≫ lim.map S.f
          exact e.inv.naturality S.f)
      (by change (R 0).map S.g ≫ e.inv.app S.X₃ = e.inv.app S.X₂ ≫ lim.map S.g
          exact e.inv.naturality S.g)
      (by change dS ≫ 𝟙 _ = e.inv.app S.X₃ ≫ (e.hom.app S.X₃ ≫ dS)
          simpa only [Category.comp_id] using
            (e.inv_hom_id_app_assoc S.X₃ dS).symm)
      (by change (R 1).map S.f ≫ 𝟙 _ = 𝟙 _ ≫ (R 1).map S.f
          simp)
      (by change (R 1).map S.g ≫ 𝟙 _ = 𝟙 _ ≫ (R 1).map S.g
          simp)
    exact ComposableArrows.exact_of_iso i hE
  · have := hS.mono_f
    exact (lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).map_mono S.f
  · let T := RF.mapTriangle.obj hS.singleTriangle
    have hT : T ∈ distTriang (DerivedCategory Ab.{u}) :=
      RF.map_distinguished _ hS.singleTriangle_distinguished
    apply ((DerivedCategory.homologyFunctor Ab.{u} 0).homologySequence_epi_shift_map_mor₂_iff
      T hT 1 2 rfl).2
    exact (hvanish S.X₁ 2 (by omega)).eq_of_tgt _ _
  · intro T₁ T₂ h₁ h₂' f
    let d₁ : (R 0).obj T₁.X₃ ⟶ (R 1).obj T₁.X₁ :=
      DerivedCategory.HomologySequence.δ
        (RF.mapTriangle.obj h₁.singleTriangle) 0 1 rfl
    let d₂ : (R 0).obj T₂.X₃ ⟶ (R 1).obj T₂.X₁ :=
      DerivedCategory.HomologySequence.δ
        (RF.mapTriangle.obj h₂'.singleTriangle) 0 1 rfl
    have hn := ((DerivedCategory.homologyFunctor Ab.{u} 0).homologySequenceδ_naturality
      (RF.mapTriangle.map (ShortComplex.ShortExact.singleTriangle.map h₁ h₂' f)) 0 1 rfl).symm
    change d₁ ≫ (R 1).map f.τ₁ = (R 0).map f.τ₃ ≫ d₂ at hn
    change (e.hom.app T₁.X₃ ≫ d₁) ≫ (R 1).map f.τ₁ =
      lim.map f.τ₃ ≫ e.hom.app T₂.X₃ ≫ d₂
    calc
      _ = e.hom.app T₁.X₃ ≫ (d₁ ≫ (R 1).map f.τ₁) := Category.assoc _ _ _
      _ = e.hom.app T₁.X₃ ≫ ((R 0).map f.τ₃ ≫ d₂) :=
        congrArg (fun k ↦ e.hom.app T₁.X₃ ≫ k) hn
      _ = lim.map f.τ₃ ≫ e.hom.app T₂.X₃ ≫ d₂ :=
        (e.hom.naturality_assoc f.τ₃ d₂).symm

end Rlim

end

end


section

@[expose] public noncomputable section

open CategoryTheory Limits DerivedCategory

namespace Rlim

set_option backward.isDefEq.respectTransparency.types false

noncomputable local instance : HasDerivedCategory Ab.{0} := HasDerivedCategory.standard _

noncomputable local instance : HasDerivedCategory Rlim.InvSystemAb :=
  HasDerivedCategory.standard _

noncomputable local instance : (lim : Rlim.InvSystemAb ⥤ Ab.{0}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The three middle terms of the four-term system, viewed as one short complex
in the abelian category of inverse systems. -/
private noncomputable def systemShortComplex
    {A B C : Rlim.InvSystemAb} (f : A ⟶ B) (g : B ⟶ C)
    (h : ∀ i, f.app i ≫ g.app i = 0) :
    ShortComplex Rlim.InvSystemAb :=
  ShortComplex.mk f g (by
    apply NatTrans.ext
    funext i
    exact h i)

private lemma systemShortComplex_map_lim
    {A B C : Rlim.InvSystemAb} (f : A ⟶ B) (g : B ⟶ C)
    (h : ∀ i, f.app i ≫ g.app i = 0) :
    (systemShortComplex f g h).map
      (lim : Rlim.InvSystemAb ⥤ Ab.{0}) =
      limitShortComplexOfInvSystem f g h := by
  rfl

private lemma systemShortComplex_pointwise
    {A B C : Rlim.InvSystemAb} (f : A ⟶ B) (g : B ⟶ C)
    (h : ∀ i, f.app i ≫ g.app i = 0) :
    (ShortComplex.FunctorEquivalence.functor ℕᵒᵖ Ab.{0}).obj
      (systemShortComplex f g h) = invSystemShortComplexFunctor f g h := by
  rfl

private noncomputable def systemShortComplex_homologyIso
    (S : ShortComplex Rlim.InvSystemAb) :
    S.homology ≅
      (ShortComplex.FunctorEquivalence.functor ℕᵒᵖ Ab.{0}).obj S ⋙
        ShortComplex.homologyFunctor Ab.{0} := by
  refine NatIso.ofComponents (fun i => ?_) ?_
  · exact (S.mapHomologyIso ((evaluation ℕᵒᵖ Ab.{0}).obj i)).symm
  · intro i j φ
    apply (cancel_mono (S.mapHomologyIso ((evaluation ℕᵒᵖ Ab.{0}).obj j)).hom).1
    calc
      (S.homology.map φ ≫
          (S.mapHomologyIso ((evaluation ℕᵒᵖ Ab.{0}).obj j)).inv) ≫
          (S.mapHomologyIso ((evaluation ℕᵒᵖ Ab.{0}).obj j)).hom =
          S.homology.map φ := by simp
      _ = (S.mapHomologyIso ((evaluation ℕᵒᵖ Ab.{0}).obj i)).inv ≫
          ShortComplex.homologyMap (S.mapNatTrans ((evaluation ℕᵒᵖ Ab.{0}).map φ)) ≫
            (S.mapHomologyIso ((evaluation ℕᵒᵖ Ab.{0}).obj j)).hom :=
        NatTrans.app_homology ((evaluation ℕᵒᵖ Ab.{0}).map φ) S

/-- Vanishing of the first derived limit of a system does not depend on the right derived
functor. -/
private lemma isZero_R1_iff_of_isRightDerivedFunctor
    (RF RF' : DerivedCategory Rlim.InvSystemAb ⥤ DerivedCategory Ab.{0})
    (α : (lim : Rlim.InvSystemAb ⥤ Ab.{0}).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (α' : (lim : Rlim.InvSystemAb ⥤ Ab.{0}).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF')
    (hRF : RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso Rlim.InvSystemAb (ComplexShape.up ℤ)))
    (hRF' : RF'.IsRightDerivedFunctor α'
      (HomotopyCategory.quasiIso Rlim.InvSystemAb (ComplexShape.up ℤ)))
    (A : Rlim.InvSystemAb) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{0} 1).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb 0).obj A))) ↔
    IsZero ((DerivedCategory.homologyFunctor Ab.{0} 1).obj
      (RF'.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb 0).obj A))) := by
  let : RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso Rlim.InvSystemAb (ComplexShape.up ℤ)) := hRF
  let : RF'.IsRightDerivedFunctor α'
      (HomotopyCategory.quasiIso Rlim.InvSystemAb (ComplexShape.up ℤ)) := hRF'
  exact Iso.isZero_iff ((DerivedCategory.homologyFunctor Ab.{0} 1).mapIso
    ((Functor.rightDerivedUnique RF RF' α α'
      (HomotopyCategory.quasiIso Rlim.InvSystemAb (ComplexShape.up ℤ))).app
        ((DerivedCategory.singleFunctor Rlim.InvSystemAb 0).obj A)))

/-- A short exact sequence of inverse systems remains right exact under inverse limit when
the first derived limit of its kernel vanishes. -/
private lemma epi_limMap_of_shortExact_of_isZero_R1
    (RF : DerivedCategory Rlim.InvSystemAb ⥤ DerivedCategory Ab.{0})
    (α : (lim : Rlim.InvSystemAb ⥤ Ab.{0}).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (hRF : RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso Rlim.InvSystemAb (ComplexShape.up ℤ)))
    {S : ShortComplex Rlim.InvSystemAb} (hS : S.ShortExact)
    (hZ : IsZero ((DerivedCategory.homologyFunctor Ab.{0} 1).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb 0).obj S.X₁)))) :
    Epi ((lim : Rlim.InvSystemAb ⥤ Ab.{0}).map S.g) := by
  obtain ⟨RF', α', commShift, hRF', _, e₀, hex, _, _, _⟩ :=
    Rlim.exists_sixTerm_exact_sequence_lim_rightDerived_one hS
  have hZ' := (isZero_R1_iff_of_isRightDerivedFunctor RF RF' α α' hRF hRF' _).1 hZ
  have hδ : (hex.sc 1).g = 0 := hZ'.eq_of_tgt _ _
  exact ((hex.sc 1).exact_iff_epi hδ).1 (hex.exact 1)

/-- The first derived inverse limit of the middle system vanishes when it vanishes on both
ends of a short exact sequence. -/
private lemma isZero_R1_middle_of_shortExact
    (RF : DerivedCategory Rlim.InvSystemAb ⥤ DerivedCategory Ab.{0})
    (α : (lim : Rlim.InvSystemAb ⥤ Ab.{0}).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (hRF : RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso Rlim.InvSystemAb (ComplexShape.up ℤ)))
    {S : ShortComplex Rlim.InvSystemAb} (hS : S.ShortExact)
    (h₁ : IsZero ((DerivedCategory.homologyFunctor Ab.{0} 1).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb 0).obj S.X₁))))
    (h₃ : IsZero ((DerivedCategory.homologyFunctor Ab.{0} 1).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb 0).obj S.X₃)))) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{0} 1).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb 0).obj S.X₂))) := by
  obtain ⟨RF', α', commShift, hRF', _, e₀, hex, _, _, _⟩ :=
    Rlim.exists_sixTerm_exact_sequence_lim_rightDerived_one hS
  refine (isZero_R1_iff_of_isRightDerivedFunctor RF RF' α α' hRF hRF' _).2
    ((hex.exact 3).isZero_of_both_isZero ?_ ?_)
  · exact (isZero_R1_iff_of_isRightDerivedFunctor RF RF' α α' hRF hRF' _).1 h₁
  · exact (isZero_R1_iff_of_isRightDerivedFunctor RF RF' α α' hRF hRF' _).1 h₃

/-- The first derived inverse limit of a quotient vanishes when it vanishes on its source:
inverse systems indexed by `ℕ` have no higher derived limits. -/
private lemma isZero_R1_quotient_of_shortExact
    (RF : DerivedCategory Rlim.InvSystemAb ⥤ DerivedCategory Ab.{0})
    (α : (lim : Rlim.InvSystemAb ⥤ Ab.{0}).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (hRF : RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso Rlim.InvSystemAb (ComplexShape.up ℤ)))
    {S : ShortComplex Rlim.InvSystemAb} (hS : S.ShortExact)
    (h₂ : IsZero ((DerivedCategory.homologyFunctor Ab.{0} 1).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb 0).obj S.X₂)))) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{0} 1).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb 0).obj S.X₃))) := by
  obtain ⟨RF', α', commShift, hRF', _, e₀, hex, _, hepi, _⟩ :=
    Rlim.exists_sixTerm_exact_sequence_lim_rightDerived_one hS
  refine (isZero_R1_iff_of_isRightDerivedFunctor RF RF' α α' hRF hRF' _).2 (IsZero.of_epi
    ((DerivedCategory.singleFunctor Rlim.InvSystemAb 0 ⋙ RF' ⋙
      DerivedCategory.homologyFunctor Ab.{0} 1).map S.g) ?_)
  exact (isZero_R1_iff_of_isRightDerivedFunctor RF RF' α α' hRF hRF' _).1 h₂

/-- A morphism killed by `p` stays killed after factoring through the coimage. -/
private lemma factorThruCoimage_comp_eq_zero {X Y Z : Rlim.InvSystemAb} (f : X ⟶ Y) (p : Y ⟶ Z)
    (w : f ≫ p = 0) : Abelian.factorThruCoimage f ≫ p = 0 := by
  apply (cancel_epi (Abelian.coimage.π f)).1
  rw [← Category.assoc, Abelian.coimage.fac, w, comp_zero]

/-- The kernel injection and the coimage projection form a short exact sequence. -/
private lemma shortExact_kernel_coimage {X Y : Rlim.InvSystemAb} (f : X ⟶ Y) :
    (ShortComplex.mk (kernel.ι f) (Abelian.coimage.π f) (cokernel.condition _)).ShortExact := by
  refine { exact := ?_, mono_f := inferInstance, epi_g := inferInstance }
  exact ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)

/-- The coimage injection and any cokernel projection form a short exact sequence. -/
private lemma shortExact_coimage_cokernel
    {X Y Z : Rlim.InvSystemAb} (f : X ⟶ Y) (p : Y ⟶ Z)
    (w : f ≫ p = 0)
    (hp : IsColimit (CokernelCofork.ofπ p w)) :
    (ShortComplex.mk (Abelian.factorThruCoimage f) p
      (factorThruCoimage_comp_eq_zero f p w)).ShortExact := by
  let S₀ := ShortComplex.mk f p w
  let S₁ := ShortComplex.mk (Abelian.factorThruCoimage f) p
    (factorThruCoimage_comp_eq_zero f p w)
  let φ : S₀ ⟶ S₁ :=
    { τ₁ := Abelian.coimage.π f
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [S₀, S₁]
      comm₂₃ := by simp [S₀, S₁] }
  have hex₀ : S₀.Exact := ShortComplex.exact_of_g_is_cokernel _ hp
  have hex₁ : S₁.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hex₀
  exact { exact := hex₁, mono_f := inferInstance, epi_g := epi_of_isColimit_cofork hp }

/-- The cokernel of a morphism is preserved by inverse limit if its source and kernel have
vanishing first derived limits. -/
private lemma preservesCokernel_of_isZero_R1_kernel_and_source
    (RF : DerivedCategory Rlim.InvSystemAb ⥤ DerivedCategory Ab.{0})
    (α : (lim : Rlim.InvSystemAb ⥤ Ab.{0}).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (hRF : RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso Rlim.InvSystemAb (ComplexShape.up ℤ)))
    {X Y : Rlim.InvSystemAb} (f : X ⟶ Y)
    (hK : IsZero ((DerivedCategory.homologyFunctor Ab.{0} 1).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb 0).obj (kernel f)))))
    (hX : IsZero ((DerivedCategory.homologyFunctor Ab.{0} 1).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb 0).obj X)))) :
    PreservesColimit (parallelPair f 0) (lim : Rlim.InvSystemAb ⥤ Ab.{0}) := by
  let F : Rlim.InvSystemAb ⥤ Ab.{0} := lim
  have hepi₁ : Epi (F.map (Abelian.coimage.π f)) :=
    epi_limMap_of_shortExact_of_isZero_R1 RF α hRF (shortExact_kernel_coimage f) hK
  have hQ : IsZero ((DerivedCategory.homologyFunctor Ab.{0} 1).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb 0).obj
        (Abelian.coimage f)))) :=
    isZero_R1_quotient_of_shortExact RF α hRF (shortExact_kernel_coimage f) hX
  let S₂ : ShortComplex Rlim.InvSystemAb :=
    ShortComplex.mk (Abelian.factorThruCoimage f) (cokernel.π f)
      (factorThruCoimage_comp_eq_zero f _ (cokernel.condition f))
  have hS₂ : S₂.ShortExact :=
    shortExact_coimage_cokernel f (cokernel.π f) (cokernel.condition f)
      (cokernelIsCokernel f)
  have hepi₂ : Epi (F.map (cokernel.π f)) :=
    epi_limMap_of_shortExact_of_isZero_R1 RF α hRF hS₂ hQ
  have hex₂ : (S₂.map F).Exact :=
    ShortComplex.exact_of_f_is_kernel _
      (KernelFork.mapIsLimit _ hS₂.fIsKernel F)
  let S₀ : ShortComplex Rlim.InvSystemAb :=
    ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  let φ : S₀.map F ⟶ S₂.map F :=
    { τ₁ := F.map (Abelian.coimage.π f)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        dsimp [S₀, S₂]
        simp only [Category.comp_id, ← F.map_comp, Abelian.coimage.fac]
      comm₂₃ := by simp [S₀, S₂] }
  have hex₀ : (S₀.map F).Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hex₂
  have hcok : IsColimit (CokernelCofork.ofπ (F.map (cokernel.π f)) (by
      rw [← F.map_comp, cokernel.condition, F.map_zero])) :=
    (ShortComplex.exact_and_epi_g_iff_g_is_cokernel (S₀.map F)).1 ⟨hex₀, hepi₂⟩ |>.some
  exact preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
    ((CokernelCofork.isColimitMapCoconeEquiv _ F).2 hcok)

/-- Vanishing of first derived limits on the first term and on homology implies
vanishing on the cycles of a short complex. -/
private lemma isZero_R1_cycles_of_isZero_R1_first_and_homology
    (RF : DerivedCategory Rlim.InvSystemAb ⥤ DerivedCategory Ab.{0})
    (α : (lim : Rlim.InvSystemAb ⥤ Ab.{0}).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (hRF : RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso Rlim.InvSystemAb (ComplexShape.up ℤ)))
    (S : ShortComplex Rlim.InvSystemAb)
    (h₁ : IsZero ((DerivedCategory.homologyFunctor Ab.{0} 1).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb 0).obj S.X₁))))
    (hH : IsZero ((DerivedCategory.homologyFunctor Ab.{0} 1).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb 0).obj S.homology)))) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{0} 1).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb 0).obj S.cycles))) := by
  have hQ := isZero_R1_quotient_of_shortExact RF α hRF (shortExact_kernel_coimage S.toCycles) h₁
  exact isZero_R1_middle_of_shortExact RF α hRF
    (shortExact_coimage_cokernel S.toCycles S.homologyπ S.toCycles_comp_homologyπ
      S.homologyIsCokernel) hQ hH

/-- **Stacks 0918.** Let
`A⁻² ⟶ A⁻¹ ⟶ A⁰ ⟶ A¹` be an inverse system of four-term complexes of
abelian groups. If `R¹ lim` vanishes on `A⁻²`, on `A⁻¹`, and on the inverse system of
degree `-1` cohomologies, then the canonical morphism from the degree-zero cohomology of the
termwise inverse limit to the inverse limit of the degree-zero cohomologies is an isomorphism. -/
@[stacks 0918]
public theorem comparisonHomologyLimit_isIso_of_isZero_rightDerivedLim
    (A_neg2 A_neg1 A_0 A_1 : Rlim.InvSystemAb)
    (d_neg2 : A_neg2 ⟶ A_neg1) (d_neg1 : A_neg1 ⟶ A_0) (d_0 : A_0 ⟶ A_1)
    (h_neg1 : ∀ i, d_neg2.app i ≫ d_neg1.app i = 0)
    (h_0 : ∀ i, d_neg1.app i ≫ d_0.app i = 0)
    (RF : DerivedCategory Rlim.InvSystemAb ⥤ DerivedCategory Ab.{0})
    (α : (lim : Rlim.InvSystemAb ⥤ Ab.{0}).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (hRF : RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso Rlim.InvSystemAb (ComplexShape.up ℤ)))
    (hA_neg2 : IsZero ((DerivedCategory.homologyFunctor Ab.{0} 1).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb 0).obj A_neg2))))
    (hA_neg1 : IsZero ((DerivedCategory.homologyFunctor Ab.{0} 1).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb 0).obj A_neg1))))
    (hH_neg1 : IsZero ((DerivedCategory.homologyFunctor Ab.{0} 1).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb 0).obj
        (homologyInvSystem d_neg2 d_neg1 h_neg1))))) :
    IsIso (comparisonHomologyLimit d_neg1 d_0 h_0) := by
  let R₁ : Rlim.InvSystemAb ⥤ Ab.{0} :=
    DerivedCategory.singleFunctor Rlim.InvSystemAb 0 ⋙ RF ⋙
      DerivedCategory.homologyFunctor Ab.{0} 1
  let F : Rlim.InvSystemAb ⥤ Ab.{0} := lim
  let Sneg := systemShortComplex d_neg2 d_neg1 h_neg1
  have hHom : IsZero (R₁.obj Sneg.homology) := by
    apply IsZero.of_iso hH_neg1
    exact R₁.mapIso (systemShortComplex_homologyIso Sneg)
  have hCycles : IsZero (R₁.obj Sneg.cycles) :=
    isZero_R1_cycles_of_isZero_R1_first_and_homology RF α hRF Sneg hA_neg2 hHom
  have hKer : IsZero (R₁.obj (kernel d_neg1)) := by
    apply IsZero.of_iso hCycles
    exact (R₁.mapIso Sneg.cyclesIsoKernel).symm
  let S₀ := systemShortComplex d_neg1 d_0 h_0
  have hKer₀ : IsZero (R₁.obj (kernel S₀.f)) := by
    simpa only [S₀, systemShortComplex] using hKer
  have hKer' : IsZero (R₁.obj (kernel S₀.toCycles)) := by
    apply IsZero.of_iso hKer₀
    simpa only [S₀.toCycles_i] using
      (R₁.mapIso (kernelCompMono S₀.toCycles S₀.iCycles)).symm
  have hPres : PreservesColimit (parallelPair S₀.toCycles 0) F :=
    preservesCokernel_of_isZero_R1_kernel_and_source RF α hRF S₀.toCycles hKer' hA_neg1
  have hPresF : PreservesColimit (parallelPair S₀.f 0) F :=
    preservesCokernel_of_isZero_R1_kernel_and_source RF α hRF S₀.f hKer₀ hA_neg1
  let : (ShortComplex.LeftHomologyData.canonical S₀).IsPreservedBy F :=
    ⟨inferInstance, by
      change PreservesColimit (parallelPair S₀.toCycles 0) F
      exact hPres⟩
  let : F.PreservesLeftHomologyOf S₀ :=
    Functor.PreservesLeftHomologyOf.mk' F (ShortComplex.LeftHomologyData.canonical S₀)
  let : (ShortComplex.RightHomologyData.canonical S₀).IsPreservedBy F :=
    ⟨hPresF, inferInstance⟩
  let : F.PreservesRightHomologyOf S₀ :=
    Functor.PreservesRightHomologyOf.mk' F (ShortComplex.RightHomologyData.canonical S₀)
  let e := S₀.mapHomologyIso F
  let κ : S₀.homology ≅ homologyInvSystem d_neg1 d_0 h_0 :=
    systemShortComplex_homologyIso S₀
  have hcomp : comparisonHomologyLimit d_neg1 d_0 h_0 =
      e.hom ≫ F.map κ.hom := by
    apply limit.hom_ext
    intro i
    simp only [comparisonHomologyLimit]
    erw [Category.assoc, limMap_π]
    have hnat : limit.π S₀.homology i =
        e.inv ≫ ShortComplex.homologyMap (S₀.mapNatTrans (lim.π i)) ≫
          (S₀.mapHomologyIso ((evaluation ℕᵒᵖ Ab.{0}).obj i)).hom :=
      by simpa only [lim.π_app] using (NatTrans.app_homology (lim.π i) S₀)
    have hκ : κ.hom.app i =
        (S₀.mapHomologyIso ((evaluation ℕᵒᵖ Ab.{0}).obj i)).inv := rfl
    rw [hnat, hκ]
    simp only [← Category.assoc]
    erw [e.hom_inv_id, Category.id_comp]
    erw [Category.assoc,
      (S₀.mapHomologyIso ((evaluation ℕᵒᵖ Ab.{0}).obj i)).hom_inv_id,
      Category.comp_id]
    exact limit.lift_π _ i
  have hIsoCandidate : IsIso (e.hom ≫ F.map κ.hom) := by
    change IsIso (e.hom ≫ (F.mapIso κ).hom)
    infer_instance
  exact hcomp.symm ▸ hIsoCandidate

end Rlim

end

end
