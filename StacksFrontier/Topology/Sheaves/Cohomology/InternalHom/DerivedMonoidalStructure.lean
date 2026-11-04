module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedCategory
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.MonoidalStructure

/-!
# Symmetric monoidal derived category of a ringed space

For a ringed space `(X, O_X)` the unbounded derived category `D(O_X)` is symmetric monoidal.
Its tensor product is the derived tensor product, its unit is the structure sheaf in degree
zero, and its associativity and commutativity constraints are those of complexes, read on
K-flat representatives through the comparison isomorphism.

## Main definitions

* `CategoryTheory.ObjectProperty.liftCoreMonoidal`: a monoidal functor whose image lies in a
  full monoidal subcategory is monoidal as a functor into that subcategory.
* `Stacks.Cohomology.MonoidalDerived.SymmetricMonoidalDerivedCategory` records a symmetric
  monoidal structure on `D(O_X)`, the comparison identifying its tensor product with the total
  tensor product of K-flat complexes, the identification of its unit, and the compatibility of
  that comparison with the associator and the braiding.
* `Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory` and
  `Stacks.Cohomology.MonoidalDerived.derivedCategorySymmetricCategory` expose the monoidal and
  symmetric structures separately from the bundled statement.

## Main results

* `Stacks.Cohomology.MonoidalDerived.symmetricMonoidalDerivedCategory` constructs this
  structure for every ringed space.
* `CochainComplex.KFlatMonoidal.braiding_derivedTensorIso` and
  `CochainComplex.KFlatMonoidal.associator_derivedTensorIso`: for a monoidal abelian category
  with K-flat resolutions, the comparison isomorphism of the localized monoidal structure on
  `D(A)` carries the associator and the braiding of `Comp(A)` to those of `D(A)`.
* `CochainComplex.KFlatMonoidal.rightUnitor_derivedTensorIso` and
  `CochainComplex.KFlatMonoidal.leftUnitor_derivedTensorIso`: that comparison, together with
  `CochainComplex.KFlatMonoidal.derivedUnitIso`, carries the two unitors of `Comp(A)` to those
  of `D(A)`.  Both rest on `CochainComplex.KFlatMonoidal.epsilon_kFlatQRestriction`, which
  identifies the unit constraint of the restriction of `DerivedCategory.Q` with
  `derivedUnitIso` just as `mu_kFlatQRestriction` identifies its tensorator with
  `derivedTensorIso`.

## Implementation notes

The monoidal and symmetric structures, the comparison and the unit isomorphism are Tag 0FPT at
the ringed site of opens of `X`, instantiated exactly as Tag 0FP8 instantiates Tag 0FPQ in
`StacksFrontier/Topology/Sheaves/Cohomology/InternalHom/MonoidalStructure.lean`.  What is new is
the clause "with the usual associativity and commutativity constraints", which Tag 0FPT does
not record: there the constraints hold by construction but are not stated as equations, so
nothing could be cited for them.

They are supplied here by exhibiting the comparison as the tensorator of a braided monoidal
functor.  The K-flat complexes are a full monoidal subcategory of `Comp(A)` -- they contain the
unit and are closed under the tensor product, which `CochainComplex.KFlatMonoidal` proves from
the right unitor and the associator -- and `CochainComplex.KFlatMonoidal.toKFlatObjects` sends
them to the K-flat objects of `K(A)`.  That functor is braided monoidal, its tensorator being
the comparison of the first localization, and its composite with `kFlatQ` is therefore a
braided monoidal functor from the K-flat complexes to `D(A)`.  Transporting along
`CochainComplex.KFlatMonoidal.derivedQIso` turns it into a braided monoidal structure on the
restriction of `DerivedCategory.Q` whose tensorator is `derivedTensorIso`.  The two clauses are
then the associativity axiom and the braiding axiom of that functor, so no coherence diagram is
verified here either.

K-flatness of a tensor product is not a hypothesis of the associativity clause:
`CochainComplex.KFlatMonoidal.kFlat_tensor` supplies it.

Two naming points.  `CochainComplex.KFlatMonoidal` already contains a `KFlat` for complexes of
modules over a ring, so K-flatness for a bifunctor is spelled out in full here.  The generic
half of the file is stated in `CochainComplex.KFlatMonoidal`, the namespace of the construction
it extends, rather than in the ringed space namespace, since it uses nothing about sheaves of
modules.

## References

* [Stacks Project, Tag 0FPB](https://stacks.math.columbia.edu/tag/0FPB)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Localization
open AlgebraicGeometry

universe w v u d

namespace CategoryTheory.ObjectProperty

variable {C : Type*} {D : Type*} [Category* C] [Category* D]
  [MonoidalCategory C] [MonoidalCategory D]
  (P : ObjectProperty D) [P.IsMonoidal] (F : C ⥤ D) (h : ∀ X, P (F.obj X))

section
variable [F.Monoidal]

/-- A monoidal functor taking values in a full monoidal subcategory is monoidal as a functor
into that subcategory: the unit and the tensorator are those of `F`, and every axiom is the
corresponding axiom of `F`, the structure of a full monoidal subcategory being that of the
ambient category. -/
def liftCoreMonoidal : (P.lift F h).CoreMonoidal where
  εIso := P.isoMk (Functor.Monoidal.εIso F)
  μIso X Y := P.isoMk (Functor.Monoidal.μIso F X Y)
  μIso_hom_natural_left f X' := by apply P.hom_ext; simp
  μIso_hom_natural_right X' f := by apply P.hom_ext; simp
  associativity X Y Z := by apply P.hom_ext; simp
  left_unitality X := by apply P.hom_ext; simp
  right_unitality X := by apply P.hom_ext; simp

/-- The lift of a monoidal functor into a full monoidal subcategory is monoidal, with the
structure `liftCoreMonoidal`. -/
instance liftMonoidal : (P.lift F h).Monoidal := (liftCoreMonoidal P F h).toMonoidal

/-- The tensorator of the lift is that of `F`. -/
@[simp] lemma lift_mu_hom (X Y : C) :
    (Functor.LaxMonoidal.μ (P.lift F h) X Y).hom = Functor.LaxMonoidal.μ F X Y := rfl

end

omit [MonoidalCategory C] [MonoidalCategory D] [P.IsMonoidal] in
/-- An isomorphism of a full subcategory is the underlying isomorphism. -/
@[simp] lemma isoMk_hom_hom {X Y : P.FullSubcategory} (e : X.obj ≅ Y.obj) :
    (P.isoMk e).hom.hom = e.hom := rfl

/-- A braided monoidal functor taking values in a full monoidal subcategory is braided as a
functor into that subcategory. -/
instance liftLaxBraided [BraidedCategory C] [BraidedCategory D] [F.Braided] :
    (P.lift F h).LaxBraided where
  braided X Y := P.hom_ext (Functor.LaxBraided.braided (F := F) X Y)

end CategoryTheory.ObjectProperty

namespace CochainComplex.KFlatMonoidal

open CochainComplex.KFlatBifunctor

variable (A : Type u) [Category.{v} A] [Abelian A] [MonoidalCategory A]
  [(curriedTensor A).Additive] [∀ X : A, ((curriedTensor A).obj X).Additive]
  [∀ X₁ X₂ : GradedObject ℤ A, GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

attribute [local instance] homotopyMonoidal homotopyBraided homotopySymmetric

/-! ### The K-flat complexes are a full monoidal subcategory of `Comp(A)` -/

/-- The unit of `Comp(A)` is K-flat. -/
instance kFlatComplexes_containsUnit :
    (kFlatComplexes (curriedTensor A)).ContainsUnit where
  prop_unit := kFlat_tensorUnit A

/-- The K-flat complexes are stable under the tensor product of `Comp(A)`. -/
instance kFlatComplexes_tensorLE :
    (kFlatComplexes (curriedTensor A)).TensorLE
      (kFlatComplexes (curriedTensor A)) (kFlatComplexes (curriedTensor A)) where
  prop_tensor _ _ hX hY := kFlat_tensor A hX hY

/-- The K-flat complexes are a monoidal object property, hence a full monoidal subcategory of
`Comp(A)`. -/
instance kFlatComplexes_isMonoidal : (kFlatComplexes (curriedTensor A)).IsMonoidal where

section
variable [SymmetricCategory (CochainComplex A ℤ)]

/-- `Comp(A)` to `K(A)` is monoidal, read at `K(A)` rather than at the type synonym carrying
the localized structure. -/
instance quotientMonoidal :
    (HomotopyCategory.quotient A (ComplexShape.up ℤ)).Monoidal :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    (Iso.refl (homotopyUnit A))).Monoidal

/-- `Comp(A)` to `K(A)` is braided. -/
instance quotientBraided :
    (HomotopyCategory.quotient A (ComplexShape.up ℤ)).Braided :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    (Iso.refl (homotopyUnit A))).Braided

/-- The K-flat complexes, sent to the K-flat objects of `K(A)`.  K-flatness of an object of
`K(A)` is K-flatness of the underlying complex, so no condition is checked. -/
def toKFlatObjects :
    (kFlatComplexes (curriedTensor A)).FullSubcategory ⥤
      (kFlatObjects (curriedTensor A)).FullSubcategory :=
  (kFlatObjects (curriedTensor A)).lift
    ((kFlatComplexes (curriedTensor A)).ι ⋙
      HomotopyCategory.quotient A (ComplexShape.up ℤ)) (fun X => X.property)

/-- `toKFlatObjects` is monoidal, with the structure of the quotient functor `Comp(A) ⥤ K(A)`. -/
instance toKFlatObjectsMonoidal : (toKFlatObjects A).Monoidal :=
  ObjectProperty.liftMonoidal _ _ _

/-- `toKFlatObjects` is lax braided, as the quotient functor `Comp(A) ⥤ K(A)` is braided. -/
instance toKFlatObjectsLaxBraided : (toKFlatObjects A).LaxBraided :=
  ObjectProperty.liftLaxBraided _ _ _

/-- The tensorator of `toKFlatObjects` is the comparison `homotopyMu` of the first
localization. -/
@[simp] lemma mu_toKFlatObjects_hom
    (K L : (kFlatComplexes (curriedTensor A)).FullSubcategory) :
    (Functor.LaxMonoidal.μ (toKFlatObjects A) K L).hom =
      (homotopyMu A K.obj L.obj).hom := by
  have h1 : (Functor.LaxMonoidal.μ (toKFlatObjects A) K L).hom =
      Functor.LaxMonoidal.μ ((kFlatComplexes (curriedTensor A)).ι ⋙
        HomotopyCategory.quotient A (ComplexShape.up ℤ)) K L := rfl
  rw [h1, Functor.LaxMonoidal.comp_μ, ObjectProperty.ι_μ,
    CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

/-- The unit constraint of `toKFlatObjects` is the identity.  The unit of `K(A)` is the image
of the unit of `Comp(A)` -- the first localization is taken at `Iso.refl (homotopyUnit A)` --
and both inclusions of a full monoidal subcategory are strictly unital, so nothing is left to
compare.  This is the unit counterpart of `mu_toKFlatObjects_hom` and is proved the same
way. -/
@[simp] lemma epsilon_toKFlatObjects_hom :
    (Functor.LaxMonoidal.ε (toKFlatObjects A)).hom = 𝟙 _ := by
  have h1 : (Functor.LaxMonoidal.ε (toKFlatObjects A)).hom =
      Functor.LaxMonoidal.ε ((kFlatComplexes (curriedTensor A)).ι ⋙
        HomotopyCategory.quotient A (ComplexShape.up ℤ)) := rfl
  rw [h1, Functor.LaxMonoidal.comp_ε, ObjectProperty.ι_ε,
    CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

/-- `epsilon_toKFlatObjects_hom` read in the full subcategory of K-flat objects. -/
@[simp] lemma epsilon_toKFlatObjects :
    Functor.LaxMonoidal.ε (toKFlatObjects A) = 𝟙 _ :=
  (kFlatObjects (curriedTensor A)).hom_ext (epsilon_toKFlatObjects_hom A)

/-! ### The K-flat complexes map to `D(A)` by a braided monoidal functor -/

section
variable [HasDerivedCategory.{w} A]
  (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) P ∧ QuasiIso f)

/-- The K-flat complexes to `D(A)`, through the K-flat objects of `K(A)`. -/
def kFlatToDerivedFunctor :
    (kFlatComplexes (curriedTensor A)).FullSubcategory ⥤ DerivedCategory A :=
  toKFlatObjects A ⋙ kFlatQ (curriedTensor A)

/-- `DerivedCategory.Q` restricted to the K-flat complexes. -/
def kFlatQRestriction :
    (kFlatComplexes (curriedTensor A)).FullSubcategory ⥤ DerivedCategory A :=
  (kFlatComplexes (curriedTensor A)).ι ⋙ DerivedCategory.Q

/-- The two routes from a K-flat complex to `D(A)` agree: passing through the homotopy
category is `derivedQIso`, naturally in the complex. -/
def kFlatToDerivedFunctorIso : kFlatToDerivedFunctor A ≅ kFlatQRestriction A :=
  NatIso.ofComponents (fun K => derivedQIso A K.obj)
    (fun _ => (DerivedCategory.quotientCompQhIso A).hom.naturality _)

/-- The localization of the K-flat objects of `K(A)` at the quasi-isomorphisms is monoidal. -/
@[instance_reducible]
def kFlatQMonoidal :
    letI := derivedMonoidal A hres
    (kFlatQ (curriedTensor A)).Monoidal :=
  letI := kFlatQ_isLocalization (curriedTensor A) hres
  letI := derivedMonoidal A hres
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor A))
    (kFlatQuasiIso (curriedTensor A))
    (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _)))).Monoidal

/-- That localization is braided as well. -/
@[instance_reducible]
def kFlatQLaxBraided :
    letI := derivedMonoidal A hres
    letI := derivedSymmetric A hres
    letI := kFlatQMonoidal A hres
    (kFlatQ (curriedTensor A)).LaxBraided :=
  letI := kFlatQ_isLocalization (curriedTensor A) hres
  letI := derivedMonoidal A hres
  letI := derivedSymmetric A hres
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor A))
    (kFlatQuasiIso (curriedTensor A))
    (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _)))).LaxBraided

/-- The composite of the two localizations is monoidal. -/
@[instance_reducible]
def kFlatToDerivedMonoidal :
    letI := derivedMonoidal A hres
    (kFlatToDerivedFunctor A).Monoidal :=
  letI := derivedMonoidal A hres
  letI := kFlatQMonoidal A hres
  inferInstanceAs (toKFlatObjects A ⋙ kFlatQ (curriedTensor A)).Monoidal

/-- The composite of the two localizations is braided. -/
@[instance_reducible]
def kFlatToDerivedLaxBraided :
    letI := derivedMonoidal A hres
    letI := derivedSymmetric A hres
    letI := kFlatToDerivedMonoidal A hres
    (kFlatToDerivedFunctor A).LaxBraided :=
  letI := derivedMonoidal A hres
  letI := derivedSymmetric A hres
  letI := kFlatQMonoidal A hres
  letI := kFlatQLaxBraided A hres
  inferInstanceAs (toKFlatObjects A ⋙ kFlatQ (curriedTensor A)).LaxBraided

/-- **`DerivedCategory.Q` is monoidal on the K-flat complexes**, by transport of the composite
of the two localizations along `kFlatToDerivedFunctorIso`. -/
@[instance_reducible]
def kFlatQRestrictionMonoidal :
    letI := derivedMonoidal A hres
    (kFlatQRestriction A).Monoidal :=
  letI := derivedMonoidal A hres
  letI := kFlatToDerivedMonoidal A hres
  Functor.Monoidal.transport (kFlatToDerivedFunctorIso A)

/-- **`DerivedCategory.Q` is braided on the K-flat complexes.**  A transported monoidal
structure makes the transporting isomorphism monoidal, which is what carries the braiding
across. -/
@[instance_reducible]
def kFlatQRestrictionLaxBraided :
    letI := derivedMonoidal A hres
    letI := derivedSymmetric A hres
    letI := kFlatQRestrictionMonoidal A hres
    (kFlatQRestriction A).LaxBraided :=
  letI := derivedMonoidal A hres
  letI := derivedSymmetric A hres
  letI := kFlatToDerivedMonoidal A hres
  letI := kFlatToDerivedLaxBraided A hres
  letI := Functor.Monoidal.transport (kFlatToDerivedFunctorIso A)
  letI : NatTrans.IsMonoidal (kFlatToDerivedFunctorIso A).hom := by
    constructor
    · rfl
    · intro K L
      rw [Functor.Monoidal.transport_μ (kFlatToDerivedFunctorIso A)]
      simp
      rfl
  Functor.LaxBraided.ofNatIso (kFlatToDerivedFunctorIso A)

/-- The tensorator of the restriction of `DerivedCategory.Q` to the K-flat complexes is the
comparison isomorphism `derivedTensorIso`.  Both are the comparison of the second localization
followed by the image of the comparison of the first; the two spellings differ only by the
tensorator of the inclusion of the K-flat complexes, which is an identity.

Everything here is in term mode on purpose.  A K-flat object of `K(A)` is written
`⟨Q(K), hK⟩` with `hK` a K-flatness proof for the complex `K`, and that is type-correct only
after unfolding `HomotopyCategory.quotient`, which `rw` and `simp` will not do when they build
a motive; so no rewriting tactic can act on these goals at all. -/
lemma mu_kFlatQRestriction {K L : CochainComplex A ℤ}
    (hK : _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) K)
    (hL : _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) L) :
    letI := derivedMonoidal A hres
    letI := kFlatQRestrictionMonoidal A hres
    Functor.LaxMonoidal.μ (kFlatQRestriction A) ⟨K, hK⟩ ⟨L, hL⟩ =
      (derivedTensorIso A hres hK hL).hom := by
  let := derivedMonoidal A hres
  let := kFlatQMonoidal A hres
  let := kFlatToDerivedMonoidal A hres
  let := kFlatQRestrictionMonoidal A hres
  have hmap : DerivedCategory.Qh.map
        (Functor.LaxMonoidal.μ (toKFlatObjects A) ⟨K, hK⟩ ⟨L, hL⟩).hom =
      DerivedCategory.Qh.map (homotopyMu A K L).hom :=
    congrArg _ (mu_toKFlatObjects_hom A ⟨K, hK⟩ ⟨L, hL⟩)
  exact (congrArg (fun m =>
      ((derivedQIso A K).inv ⊗ₘ (derivedQIso A L).inv) ≫
        (Functor.LaxMonoidal.μ (kFlatQ (curriedTensor A))
              ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩
              ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L, hL⟩ ≫ m) ≫
          (derivedQIso A (K ⊗ L)).hom) hmap).trans
    (congrArg _ (Category.assoc _ _ _))

/-- The unit constraint of the composite of the two localizations is the identity: both are
taken at an identity unit isomorphism, and `epsilon_toKFlatObjects` makes the inner one an
identity too. -/
lemma epsilon_kFlatToDerivedFunctor :
    letI := derivedMonoidal A hres
    letI := kFlatToDerivedMonoidal A hres
    Functor.LaxMonoidal.ε (kFlatToDerivedFunctor A) = 𝟙 _ := by
  let := derivedMonoidal A hres
  let := kFlatQMonoidal A hres
  let := kFlatToDerivedMonoidal A hres
  change Functor.LaxMonoidal.ε (kFlatQ (curriedTensor A)) ≫
    (kFlatQ (curriedTensor A)).map (Functor.LaxMonoidal.ε (toKFlatObjects A)) = 𝟙 _
  rw [epsilon_toKFlatObjects]
  exact (congrArg _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)

/-- **The unit constraint of the restriction of `DerivedCategory.Q` to the K-flat complexes is
`derivedUnitIso`.**  This is the unit counterpart of `mu_kFlatQRestriction`: the monoidal
structure on the restriction is transported along `kFlatToDerivedFunctorIso`, so its unit is
the unit of the composite of the two localizations followed by that isomorphism at the unit
complex; the former is an identity by `epsilon_kFlatToDerivedFunctor` and the latter is
`derivedUnitIso` by construction.

Term mode, for the reason given on `mu_kFlatQRestriction`: the goals mention the unit of the
full subcategory of K-flat complexes, which is type-correct only after unfolding
`HomotopyCategory.quotient` and `DerivedCategory.quotientCompQhIso`, and no rewriting tactic
will unfold those while building a motive. -/
lemma epsilon_kFlatQRestriction :
    letI := derivedMonoidal A hres
    letI := kFlatQRestrictionMonoidal A hres
    Functor.LaxMonoidal.ε (kFlatQRestriction A) = (derivedUnitIso A hres).hom := by
  let := derivedMonoidal A hres
  let := kFlatToDerivedMonoidal A hres
  let := kFlatQRestrictionMonoidal A hres
  rw [Functor.Monoidal.transport_ε (kFlatToDerivedFunctorIso A),
    epsilon_kFlatToDerivedFunctor A hres]
  exact Category.id_comp _

/-- **The right unit constraint of `D(A)` is the one of `Comp(A)`**: the comparison
isomorphism on K-flat complexes and the unit isomorphism carry the right unitor of `Comp(A)`
to the right unitor of `D(A)`.  This is the right unitality axiom of `kFlatQRestriction`,
whose unit and tensorator are `derivedUnitIso` and `derivedTensorIso`. -/
theorem rightUnitor_derivedTensorIso {K : CochainComplex A ℤ}
    (hK : _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) K) :
    letI := derivedMonoidal A hres
    (ρ_ ((DerivedCategory.Q (C := A)).obj K)).hom =
      (DerivedCategory.Q (C := A)).obj K ◁ (derivedUnitIso A hres).hom ≫
        (derivedTensorIso A hres hK (kFlat_tensorUnit A)).hom ≫
          (DerivedCategory.Q (C := A)).map (ρ_ K).hom := by
  let := derivedMonoidal A hres
  let := kFlatQRestrictionMonoidal A hres
  rw [← epsilon_kFlatQRestriction A hres,
    ← mu_kFlatQRestriction A hres hK (kFlat_tensorUnit A)]
  exact Functor.LaxMonoidal.right_unitality (kFlatQRestriction A) ⟨K, hK⟩

/-- **The left unit constraint of `D(A)` is the one of `Comp(A)`.**  The mirror of
`rightUnitor_derivedTensorIso`, and the left unitality axiom of the same functor; it needs no
braiding, the two unitality axioms being independent fields of a lax monoidal functor. -/
theorem leftUnitor_derivedTensorIso {K : CochainComplex A ℤ}
    (hK : _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) K) :
    letI := derivedMonoidal A hres
    (λ_ ((DerivedCategory.Q (C := A)).obj K)).hom =
      (derivedUnitIso A hres).hom ▷ (DerivedCategory.Q (C := A)).obj K ≫
        (derivedTensorIso A hres (kFlat_tensorUnit A) hK).hom ≫
          (DerivedCategory.Q (C := A)).map (λ_ K).hom := by
  let := derivedMonoidal A hres
  let := kFlatQRestrictionMonoidal A hres
  rw [← epsilon_kFlatQRestriction A hres,
    ← mu_kFlatQRestriction A hres (kFlat_tensorUnit A) hK]
  exact Functor.LaxMonoidal.left_unitality (kFlatQRestriction A) ⟨K, hK⟩

/-- **The commutativity constraint of `D(A)` is the one of `Comp(A)`**: the comparison
isomorphism on K-flat complexes carries the braiding of `Comp(A)` to the braiding of `D(A)`.
For complexes of modules the former is the Koszul symmetry. -/
theorem braiding_derivedTensorIso {K L : CochainComplex A ℤ}
    (hK : _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) K)
    (hL : _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) L) :
    letI := derivedMonoidal A hres
    letI := derivedSymmetric A hres
    (derivedTensorIso A hres hK hL).hom ≫
        (DerivedCategory.Q (C := A)).map (β_ K L).hom =
      (β_ ((DerivedCategory.Q (C := A)).obj K)
          ((DerivedCategory.Q (C := A)).obj L)).hom ≫
        (derivedTensorIso A hres hL hK).hom := by
  let := derivedMonoidal A hres
  let := derivedSymmetric A hres
  let := kFlatQRestrictionMonoidal A hres
  let := kFlatQRestrictionLaxBraided A hres
  rw [← mu_kFlatQRestriction A hres hK hL, ← mu_kFlatQRestriction A hres hL hK]
  exact Functor.LaxBraided.braided (F := kFlatQRestriction A) ⟨K, hK⟩ ⟨L, hL⟩

/-- **The associativity constraint of `D(A)` is the one of `Comp(A)`**: the comparison
isomorphism on K-flat complexes carries the associator of `Comp(A)` to the associator of
`D(A)`. -/
theorem associator_derivedTensorIso {K L N : CochainComplex A ℤ}
    (hK : _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) K)
    (hL : _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) L)
    (hN : _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) N) :
    letI := derivedMonoidal A hres
    ((derivedTensorIso A hres hK hL).hom ▷ (DerivedCategory.Q (C := A)).obj N) ≫
        (derivedTensorIso A hres (kFlat_tensor A hK hL) hN).hom ≫
        (DerivedCategory.Q (C := A)).map (α_ K L N).hom =
      (α_ ((DerivedCategory.Q (C := A)).obj K) ((DerivedCategory.Q (C := A)).obj L)
          ((DerivedCategory.Q (C := A)).obj N)).hom ≫
        ((DerivedCategory.Q (C := A)).obj K ◁ (derivedTensorIso A hres hL hN).hom) ≫
        (derivedTensorIso A hres hK (kFlat_tensor A hL hN)).hom := by
  let := derivedMonoidal A hres
  let := kFlatQRestrictionMonoidal A hres
  rw [← mu_kFlatQRestriction A hres hK hL, ← mu_kFlatQRestriction A hres hL hN,
    ← mu_kFlatQRestriction A hres (kFlat_tensor A hK hL) hN,
    ← mu_kFlatQRestriction A hres hK (kFlat_tensor A hL hN)]
  exact Functor.LaxMonoidal.associativity (kFlatQRestriction A)
    ⟨K, hK⟩ ⟨L, hL⟩ ⟨N, hN⟩

end

end

end CochainComplex.KFlatMonoidal

namespace Stacks.Cohomology.MonoidalDerived

open Stacks.SheafOfModules.DerivedMonoidal

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Mod R)]

/- The monoidal structures on `Mod(O)` and `Comp(Mod(O))` with both site universes pinned at
the single universe `u` of the site, of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Monoidal/DerivedCategory.lean`, back in scope.  This
is the configuration of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Monoidal/DerivedTensorConstraints.lean`. -/
attribute [local instance] Stacks.SheafOfModules.DerivedMonoidal.monoidalCategoryMod
  Stacks.SheafOfModules.DerivedMonoidal.symmetricCategoryMod
  Stacks.SheafOfModules.DerivedMonoidal.monoidalPreadditiveMod
  Stacks.SheafOfModules.DerivedMonoidal.monoidalClosedMod
  Stacks.SheafOfModules.DerivedMonoidal.hasTensorMod
  Stacks.SheafOfModules.DerivedMonoidal.monoidalComplexes

/-! ### The two constraint clauses -/

/-- The commutativity constraint of `D(Mod(O))` is the one of complexes: on K-flat complexes
the comparison carries the Koszul symmetry of Tag 0FNG to the braiding of `D(Mod(O))`. -/
abbrev BraidingComparison [Monoidal R] [Symmetric R] (cmp : Comparison R) : Prop :=
  ∀ (K L : Complexes R) (hK : KFlat R K) (hL : KFlat R L),
    (cmp K L hK hL).hom ≫ (DerivedCategory.Q (C := Mod R)).map (β_ K L).hom =
      (β_ ((DerivedCategory.Q (C := Mod R)).obj K)
          ((DerivedCategory.Q (C := Mod R)).obj L)).hom ≫ (cmp L K hL hK).hom

/-- The associativity constraint of `D(Mod(O))` is the one of complexes: on K-flat complexes
the comparison carries the associator of total tensor products to that of `D(Mod(O))`. -/
abbrev AssociatorComparison [Monoidal R] (cmp : Comparison R) : Prop :=
  ∀ (K L N : Complexes R) (hK : KFlat R K) (hL : KFlat R L) (hN : KFlat R N),
    ((cmp K L hK hL).hom ▷ (DerivedCategory.Q (C := Mod R)).obj N) ≫
        (cmp (K ⊗ L) N
          (CochainComplex.KFlatMonoidal.kFlat_tensor (Mod R) hK hL) hN).hom ≫
        (DerivedCategory.Q (C := Mod R)).map (α_ K L N).hom =
      (α_ ((DerivedCategory.Q (C := Mod R)).obj K) ((DerivedCategory.Q (C := Mod R)).obj L)
          ((DerivedCategory.Q (C := Mod R)).obj N)).hom ≫
        ((DerivedCategory.Q (C := Mod R)).obj K ◁ (cmp L N hL hN).hom) ≫
        (cmp K (L ⊗ N) hK
          (CochainComplex.KFlatMonoidal.kFlat_tensor (Mod R) hL hN)).hom

/-! ### The statement -/

/-- A symmetric monoidal structure on the derived category of modules on a ringed site, whose
tensor product is the derived tensor product -- on K-flat complexes the total tensor product --
whose unit is the structure sheaf in degree zero, and whose associativity and commutativity
constraints are those of complexes. -/
public structure SymmetricMonoidalDerivedCategory where
  /-- The monoidal structure on `D(Mod(O))`. -/
  monoidal : Monoidal R
  /-- The symmetric braiding on `D(Mod(O))`. -/
  symmetric : Symmetric R
  /-- The isomorphism between the tensor product in `D(Mod(O))` of the images of two K-flat
  complexes and the image of their total tensor product. -/
  comparison : Comparison R
  /-- The isomorphism between the tensor unit of `D(Mod(O))` and the structure sheaf in degree
  zero. -/
  unitIso : UnitIso R
  /-- The comparison carries the braiding of complexes to the braiding of `D(Mod(O))`. -/
  braiding_comparison : BraidingComparison R comparison
  /-- The comparison carries the associator of complexes to the associator of `D(Mod(O))`. -/
  associator_comparison : AssociatorComparison R comparison

/-! ### The construction -/

/-- **The derived category of modules on a ringed site is a symmetric monoidal category**, with
tensor product the derived tensor product, unit the structure sheaf in degree zero, and the
usual associativity and commutativity constraints.  The first four clauses are Tag 0FPT; the
last two are what this file adds. -/
def symmetricMonoidalDerivedSite : SymmetricMonoidalDerivedCategory R where
  monoidal := (symmetricMonoidalDerived R).monoidal
  symmetric := (symmetricMonoidalDerived R).symmetric
  comparison := (symmetricMonoidalDerived R).comparison
  unitIso := (symmetricMonoidalDerived R).unitIso
  braiding_comparison _ _ hK hL :=
    CochainComplex.KFlatMonoidal.braiding_derivedTensorIso (Mod R)
      (exists_kFlat_resolution R) hK hL
  associator_comparison _ _ _ hK hL hN :=
    CochainComplex.KFlatMonoidal.associator_derivedTensorIso (Mod R)
      (exists_kFlat_resolution R) hK hL hN

/-! ### The ringed space -/

open AlgebraicGeometry in
/-- **The derived category of modules on a ringed space is a symmetric monoidal category**, with
tensor product the derived tensor product, unit the structure sheaf in degree zero, and the
usual associativity and commutativity constraints.  This is the ringed site statement at the
site of opens of `X`, exactly as Tag 0FP8 is Tag 0FPQ there. -/
@[stacks 0FPB]
public def symmetricMonoidalDerivedCategory (X : RingedSpace.{u, u})
    [HasDerivedCategory.{d} (Mod X.sheaf)] :
    SymmetricMonoidalDerivedCategory X.sheaf :=
  symmetricMonoidalDerivedSite X.sheaf

open AlgebraicGeometry in
/-- The monoidal structure on the derived category of modules on a ringed space, with the
derived tensor product. -/
@[instance_reducible]
def derivedCategoryMonoidalCategory (X : RingedSpace.{u, u})
    [HasDerivedCategory.{d} (Mod X.sheaf)] :
    MonoidalCategory (DerivedModules X.sheaf) :=
  (symmetricMonoidalDerivedCategory X).monoidal

open AlgebraicGeometry in
/-- The commutativity constraint on the derived category of modules on a ringed space. -/
@[instance_reducible]
def derivedCategorySymmetricCategory (X : RingedSpace.{u, u})
    [HasDerivedCategory.{d} (Mod X.sheaf)] :
    letI := derivedCategoryMonoidalCategory X
    SymmetricCategory (DerivedModules X.sheaf) :=
  (symmetricMonoidalDerivedCategory X).symmetric

end Stacks.Cohomology.MonoidalDerived

end
