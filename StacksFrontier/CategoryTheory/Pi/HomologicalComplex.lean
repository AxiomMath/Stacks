module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Homotopy
public import StacksFrontier.CategoryTheory.Pi.Preadditive

/-!
# Complexes in a product of preadditive categories

A complex in a product `∀ i, A i` of preadditive categories is the same thing as a family of
complexes, one in each factor: both the objects and the differentials of a complex in the
product are given index by index, and the two conditions on a complex — that the differential
vanish off the shape and that consecutive differentials compose to zero — are conditions in each
factor separately. So

  `HomologicalComplex (∀ i, A i) c ≌ ∀ i, HomologicalComplex (A i) c`,

for an arbitrary index type and an arbitrary complex shape.

## Main definitions

All names are in the namespace `CategoryTheory.Pi`.

* `evalHomologicalComplex`: evaluation at an index read on complexes, that is
  `CategoryTheory.Functor.mapHomologicalComplex` of `CategoryTheory.Pi.eval`, which is additive
  by `eval_additive`.
* `homologicalComplexFunctor`: reading a complex in the product index by index, as one functor
  to the product of the categories of complexes.
* `homologicalComplexInverse`: assembling a family of complexes, one in each factor, into a
  complex in the product.
* `homologicalComplexEquivalence`: **the equivalence**.
* `homotopyPi`: a family of homotopies, one in each factor, assembled into a homotopy in the
  product.

## Implementation notes

The equivalence is obtained from fullness, faithfulness and essential surjectivity rather than
by exhibiting unit and counit: a product of categories *is* the category of families, so the
assembly `CategoryTheory.Pi.homologicalComplexInverse` is a reindexing of the data and not a
universal property, and reading it back index by index returns the family it was built from on
the nose. Essential surjectivity is therefore `Iso.refl`, and fullness and faithfulness say that
a family of maps of complexes assembles to one map of complexes in the product, uniquely.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Pi

universe w t v u

variable {I : Type w} {A : I → Type u} [∀ i, Category.{v} (A i)] [∀ i, Preadditive (A i)]
variable {ι : Type t} (c : ComplexShape ι)

/-- Evaluation at an index, read on complexes: a complex in a product of preadditive categories
has an underlying complex in each factor. -/
def evalHomologicalComplex (i : I) :
    HomologicalComplex (∀ i, A i) c ⥤ HomologicalComplex (A i) c :=
  (Pi.eval A i).mapHomologicalComplex c

/-- **Reading a complex in a product index by index**, as one functor to the product of the
categories of complexes in the factors. -/
def homologicalComplexFunctor :
    HomologicalComplex (∀ i, A i) c ⥤ ∀ i, HomologicalComplex (A i) c :=
  Functor.pi' fun i => evalHomologicalComplex c i

/-- The objects of the complex read off at an index are the components of the objects. -/
@[simp]
theorem homologicalComplexFunctor_obj_X (K : HomologicalComplex (∀ i, A i) c) (i : I) (n : ι) :
    (((homologicalComplexFunctor c).obj K) i).X n = K.X n i := rfl

/-- The differentials of the complex read off at an index are the components of the
differentials. -/
@[simp]
theorem homologicalComplexFunctor_obj_d (K : HomologicalComplex (∀ i, A i) c) (i : I)
    (n m : ι) : (((homologicalComplexFunctor c).obj K) i).d n m = K.d n m i := rfl

/-- The components of a map of complexes read off at an index are the components of the map. -/
@[simp]
theorem homologicalComplexFunctor_map_f {K L : HomologicalComplex (∀ i, A i) c} (φ : K ⟶ L)
    (i : I) (n : ι) : (((homologicalComplexFunctor c).map φ) i).f n = φ.f n i := rfl

/-- **Assembling a family of complexes into a complex in the product.** The objects and the
differentials are given index by index, and both conditions on a complex hold index by index. -/
def homologicalComplexInverse :
    (∀ i, HomologicalComplex (A i) c) ⥤ HomologicalComplex (∀ i, A i) c where
  obj K :=
    { X := fun n i => (K i).X n
      d := fun n m i => (K i).d n m
      shape := fun n m h => funext fun i => (K i).shape n m h
      d_comp_d' := fun n m p hnm hmp => funext fun i => (K i).d_comp_d' n m p hnm hmp }
  map φ :=
    { f := fun n i => (φ i).f n
      comm' := fun n m h => funext fun i => (φ i).comm' n m h }

/-- The objects of an assembled complex are the families of the objects of the factors. -/
@[simp]
theorem homologicalComplexInverse_obj_X (K : ∀ i, HomologicalComplex (A i) c) (n : ι) :
    ((homologicalComplexInverse c).obj K).X n = fun i => (K i).X n := rfl

/-- The differentials of an assembled complex are the families of the differentials of the
factors. -/
@[simp]
theorem homologicalComplexInverse_obj_d (K : ∀ i, HomologicalComplex (A i) c) (n m : ι) :
    ((homologicalComplexInverse c).obj K).d n m = fun i => (K i).d n m := rfl

/-- The components of an assembled map of complexes are the families of the components of the
maps in the factors. -/
@[simp]
theorem homologicalComplexInverse_map_f {K L : ∀ i, HomologicalComplex (A i) c} (φ : K ⟶ L)
    (n : ι) : ((homologicalComplexInverse c).map φ).f n = fun i => (φ i).f n := rfl

/-- Reading the assembly of a family of complexes index by index returns the family. -/
theorem homologicalComplexFunctor_obj_inverse_obj (K : ∀ i, HomologicalComplex (A i) c) :
    (homologicalComplexFunctor c).obj ((homologicalComplexInverse c).obj K) = K := rfl

/-- Reading a complex index by index is faithful. -/
instance homologicalComplexFunctor_faithful :
    (homologicalComplexFunctor (A := A) c).Faithful where
  map_injective {_ _} {_ _} h := by
    ext n i
    exact congrArg (fun t => HomologicalComplex.Hom.f t n) (congrFun h i)

/-- Reading a complex index by index is full. -/
instance homologicalComplexFunctor_full : (homologicalComplexFunctor (A := A) c).Full where
  map_surjective {_ _} φ :=
    ⟨{ f := fun n i => (φ i).f n
       comm' := fun n m h => funext fun i => (φ i).comm' n m h }, rfl⟩

/-- Reading a complex index by index is essentially surjective. -/
instance homologicalComplexFunctor_essSurj :
    (homologicalComplexFunctor (A := A) c).EssSurj where
  mem_essImage K := ⟨(homologicalComplexInverse c).obj K, ⟨Iso.refl K⟩⟩

/-- Reading a complex index by index is an equivalence. -/
instance homologicalComplexFunctor_isEquivalence :
    (homologicalComplexFunctor (A := A) c).IsEquivalence where

/-- **A complex in a product of preadditive categories is a family of complexes.** Reading a
complex index by index is an equivalence

  `HomologicalComplex (∀ i, A i) c ≌ ∀ i, HomologicalComplex (A i) c`,

for an arbitrary index type and an arbitrary complex shape. -/
def homologicalComplexEquivalence :
    HomologicalComplex (∀ i, A i) c ≌ ∀ i, HomologicalComplex (A i) c :=
  (homologicalComplexFunctor c).asEquivalence

/-- **A family of homotopies assembles into a homotopy in the product.** A homotopy between two
maps of complexes in a product of preadditive categories is a family of maps of the underlying
objects together with two conditions; the maps are given index by index and both conditions hold
index by index, exactly as for a map of complexes. -/
def homotopyPi {K L : HomologicalComplex (∀ i, A i) c} {f g : K ⟶ L}
    (H : ∀ i, Homotopy ((evalHomologicalComplex c i).map f)
      ((evalHomologicalComplex c i).map g)) :
    Homotopy f g where
  hom p q := fun i => (H i).hom p q
  zero p q h := funext fun i => (H i).zero p q h
  comm n := funext fun i => (H i).comm n

/-- The functor of `CategoryTheory.Pi.homologicalComplexEquivalence` is
`CategoryTheory.Pi.homologicalComplexFunctor`. -/
@[simp]
theorem homologicalComplexEquivalence_functor :
    (homologicalComplexEquivalence (A := A) c).functor = homologicalComplexFunctor c := rfl

end CategoryTheory.Pi

end
