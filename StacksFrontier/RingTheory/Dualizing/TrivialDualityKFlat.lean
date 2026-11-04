module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleRlimTensorLimit
public import StacksFrontier.Homology.KFlat.LargeUniverse
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.Tor.DerivedChangeOfRings
public import StacksFrontier.Homology.Tor.DerivedTensorLargeUniverse
public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.Conservative
public import StacksFrontier.RingTheory.Dualizing.TrivialDuality
public import StacksFrontier.RingTheory.Dualizing.TrivialDuality.BaseChange

/-!
# The comparison of Stacks 0BZE on K-flat complexes

Let `f : R → A` be a homomorphism of commutative rings. Stacks 0BZE asserts, for `A` perfect as
an `R`-module, that derived coextension of scalars `RHom_R(A, -) : D(R) ⥤ D(A)` of Stacks 0A70 is
isomorphic to the derived tensor product `- ⊗ᴸ_R RHom_R(A, R)` of Stacks 06Y6. This file
constructs the comparison morphism between the two functors on the K-flat complexes, proves it
natural in chain maps between them, and reduces the assertion to the invertibility of that one
morphism.

The comparison is built without any K-injective resolution and without a chain-level tensor--Hom
map. For a K-flat complex `K`, tensoring with `K` preserves quasi-isomorphisms, so the derived
counit `RHom_R(A, R) ⟶ R` of Stacks 0A70 may be tensored with `K` by writing it as a chain-level
right fraction and tensoring numerator and denominator; the resulting map
`Tot(K ⊗_R res RHom_R(A, R)) ⟶ K` in `D(R)` is `Stacks0BZE.tensorCounit`. Composed with the three
structural comparisons of the derived change-of-rings bundle it gives
`Stacks0BZE.restrictedComparison`, a map out of the restriction to `R` of `K ⊗ᴸ_R RHom_R(A, R)`,
and its transpose under the adjunction of Stacks 0A70 is `Stacks0BZE.comparison`, a morphism in
`D(A)`.

## Main definitions

* `Stacks0BZE.tensorCounit`: the derived counit of Stacks 0A70 tensored with a K-flat complex.
* `Stacks0BZE.restrictedComparison`: the comparison of Stacks 0BZE, read in `D(R)`.
* `Stacks0BZE.comparison`: the comparison of Stacks 0BZE in `D(A)`.
* `Stacks0BZE.cardIsoOfIsos`, `Stacks0BZE.cardIso`: the descent of a comparison on K-flat
  complexes to an isomorphism of functors on `D(R)`.

## Main results

* `Stacks0BZE.tensorCounit_naturality`, `Stacks0BZE.restrictedComparison_naturality`,
  `Stacks0BZE.comparison_naturality`: all three comparisons are natural in chain maps between
  K-flat complexes.
* `Stacks0BZE.restrictScalars_comparison_comp_counit`: the defining property of the comparison,
  namely that restricting it to `R` and following with the counit of Stacks 0A70 returns
  `Stacks0BZE.restrictedComparison`.
* `Stacks0BZE.isIso_comparison_of_restrictScalars`: invertibility of the comparison may be
  checked after restriction of scalars, which is conservative on derived categories.
* `Stacks0BZE.card_of_kFlatComparison` and `Stacks0BZE.card_of_isIso_comparison`: the statement
  of Stacks 0BZE follows from a natural family of isomorphisms on the K-flat complexes, and in
  particular from invertibility of `Stacks0BZE.comparison`.

## Implementation notes

The descent from the K-flat complexes to all of `D(R)` is
`ModuleSystemRlimTensor.natIsoOfResolutions`: the K-flat complexes resolve every cochain complex
and `DerivedCategory.Q` is a localization with a calculus of fractions, so a family of
isomorphisms on a resolving class that is natural in chain maps between its members determines an
isomorphism of functors.

Invertibility of `Stacks0BZE.comparison`, the hypothesis of
`Stacks0BZE.card_of_isIso_comparison`, is not proved here. By
`Stacks0BZE.isIso_comparison_of_restrictScalars` and
`Stacks0BZE.restrictScalars_comparison_comp_counit` that invertibility is a statement in `D(R)`
about `Stacks0BZE.restrictedComparison`, where
`Dualizing.derivedHomRestrictScalarsInternalHomIsoCanonical` identifies the restriction of
derived coextension with the derived internal Hom out of the algebra, and the perfectness
hypothesis is meant to enter through the derived tensor--Hom diagonal of Stacks 0ATK.

Note also that the perfectness hypothesis of the statement below lives at module universe `u`,
the ring's own, whereas the two functors it compares live at module universe `max v u`; a
universe transport of perfectness is therefore part of any proof that uses it.

## References

* [The Stacks Project, Tag 0BZE](https://stacks.math.columbia.edu/tag/0BZE)
* [The Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [The Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
* [The Stacks Project, Tag 0ATK](https://stacks.math.columbia.edu/tag/0ATK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks0BZE

variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)

/-- The free module of rank one on the lifted carrier, in degree zero. -/
def unitComplex (R : Type u) [CommRing R] : CochainComplex (ModuleCat.{max v u} R) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat.{max v u} R) 0).obj
    (ModuleCat.of R (ULift.{max v u} R))

/-- The object `R₀` of `D(R)`: the free module of rank one on the lifted carrier, in degree
zero. -/
def unitObject (R : Type u) [CommRing R] : DerivedCategory (ModuleCat.{max v u} R) :=
  (DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
    (ModuleCat.of R (ULift.{max v u} R))

/-- `R₀` is the class of `unitComplex`. -/
def unitObjectIso (R : Type u) [CommRing R] :
    unitObject.{u, v} R ≅ DerivedCategory.Q.obj (unitComplex.{u, v} R) :=
  (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max v u} R) 0).app _

/-- The chosen complex of `A`-modules representing `RHom_R(A, R)`. -/
def dualComplex : CochainComplex (ModuleCat.{max v u} A) ℤ :=
  ((DerivedCategory.Qh (C := ModuleCat.{max v u} A)).objPreimage
    ((Dualizing.derivedHom.{u, v} f).obj (unitObject.{u, v} R))).as

/-- Its class in `D(A)` is `RHom_R(A, R)`. -/
def dualComplexIso :
    DerivedCategory.Q.obj (dualComplex.{u, v} f) ≅
      (Dualizing.derivedHom.{u, v} f).obj (unitObject.{u, v} R) :=
  (DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} A)).symm.app
      (dualComplex.{u, v} f) ≪≫
    DerivedCategory.Qh.objObjPreimageIso _

/-- The canonical derived change-of-rings bundle for the dual complex. -/
def bundle :
    CochainComplex.DerivedTensor.DerivedTensorChangeOfRings f (dualComplex.{u, v} f) :=
  CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f (dualComplex.{u, v} f)

/-- The restriction of scalars functor on derived categories. -/
abbrev resDerived : DerivedCategory (ModuleCat.{max v u} A) ⥤
    DerivedCategory (ModuleCat.{max v u} R) :=
  (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory

/-- The derived counit of Stacks 0A70 at `R₀`, read on chain-level representatives:
`Q(res RHom_R(A, R)) ⟶ Q(R[0])`. -/
def dualCounit :
    DerivedCategory.Q.obj
        ((CochainComplex.restrictScalarsLarge.{v} f).obj (dualComplex.{u, v} f)) ⟶
      DerivedCategory.Q.obj (unitComplex.{u, v} R) :=
  ((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategoryFactors.app
      (dualComplex.{u, v} f)).inv ≫
    (resDerived f).map (dualComplexIso.{u, v} f).hom ≫
    (Dualizing.derivedHomAdjunction.{u, u, v} f).counit.app (unitObject.{u, v} R) ≫
    (unitObjectIso.{u, v} R).hom

/-- A chain-level right fraction for `Stacks0BZE.dualCounit`. -/
structure Fraction where
  /-- The source complex of the fraction. -/
  source : CochainComplex (ModuleCat.{max v u} R) ℤ
  /-- The denominator, a quasi-isomorphism onto the restricted dual complex. -/
  den : source ⟶ (CochainComplex.restrictScalarsLarge.{v} f).obj (dualComplex.{u, v} f)
  /-- The denominator becomes invertible in the derived category. -/
  den_isIso : IsIso (DerivedCategory.Q.map den)
  /-- The numerator. -/
  num : source ⟶ unitComplex.{u, v} R
  /-- The fraction computes the counit. -/
  fac : dualCounit.{u, v} f =
    inv (DerivedCategory.Q.map den) ≫ DerivedCategory.Q.map num

/-- Every morphism of the derived category is a right fraction. -/
def fraction : Fraction.{u, v} f :=
  have h := DerivedCategory.right_fac (dualCounit.{u, v} f)
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec.choose_spec⟩

/-- The total tensor-product bifunctor on cochain complexes of `R`-modules, at a module
universe above the ring's. -/
def tensorBifunctor (R : Type u) [CommRing R] :
    CochainComplex (ModuleCat.{max v u} R) ℤ ⥤
      CochainComplex (ModuleCat.{max v u} R) ℤ ⥤
        CochainComplex (ModuleCat.{max v u} R) ℤ :=
  letI : MonoidalCategoryStruct (ModuleCat.{max v u} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{u, max v u}
  letI : MonoidalCategory (ModuleCat.{max v u} R) :=
    ModuleCat.liftedModuleMonoidal.{u, max v u}
  (curriedTensor (ModuleCat.{max v u} R)).map₂CochainComplex

/-- The right unitor of the total tensor product of cochain complexes. -/
def unitorIso (K : CochainComplex (ModuleCat.{max v u} R) ℤ) :
    ((tensorBifunctor.{u, v} R).obj K).obj (unitComplex.{u, v} R) ≅ K :=
  letI : MonoidalCategoryStruct (ModuleCat.{max v u} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{u, max v u}
  letI : MonoidalCategory (ModuleCat.{max v u} R) :=
    ModuleCat.liftedModuleMonoidal.{u, max v u}
  MonoidalCategoryStruct.rightUnitor K

/-- The right unitor `Stacks0BZE.unitorIso` is natural in the cochain complex. -/
lemma unitorIso_naturality {K L : CochainComplex (ModuleCat.{max v u} R) ℤ} (a : K ⟶ L) :
    ((tensorBifunctor.{u, v} R).map a).app (unitComplex.{u, v} R) ≫ (unitorIso.{u, v} L).hom =
      (unitorIso.{u, v} K).hom ≫ a :=
  let : MonoidalCategoryStruct (ModuleCat.{max v u} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{u, max v u}
  let : MonoidalCategory (ModuleCat.{max v u} R) :=
    ModuleCat.liftedModuleMonoidal.{u, max v u}
  MonoidalCategory.rightUnitor_naturality a

/-- The complex of `R`-modules underlying the chosen representative of `RHom_R(A, R)`. -/
abbrev dualRestricted : CochainComplex (ModuleCat.{max v u} R) ℤ :=
  (CochainComplex.restrictScalarsLarge.{v} f).obj (dualComplex.{u, v} f)

/-- The denominator of `Stacks0BZE.fraction` is a quasi-isomorphism. -/
lemma quasiIso_fraction_den : QuasiIso (fraction.{u, v} f).den := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact (fraction.{u, v} f).den_isIso

/-- Tensored with a K-flat complex, the denominator of `Stacks0BZE.fraction` becomes an isomorphism
in the derived category. -/
lemma isIso_tensor_fraction_den {K : CochainComplex (ModuleCat.{max v u} R) ℤ}
    (hK : CochainComplex.KFlat.{u, max v u} K) :
    IsIso (DerivedCategory.Q.map
      (((tensorBifunctor.{u, v} R).obj K).map (fraction.{u, v} f).den)) := by
  rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
  have := quasiIso_fraction_den.{u, v} f
  exact CochainComplex.DerivedTensor.quasiIso_tleft_map_of_kFlat.{u, max v u} K hK
    (fraction.{u, v} f).den

/-- The denominator of the fraction, tensored with a K-flat complex, as an isomorphism. -/
def tensorDenIso {K : CochainComplex (ModuleCat.{max v u} R) ℤ}
    (hK : CochainComplex.KFlat.{u, max v u} K) :
    DerivedCategory.Q.obj
        (((tensorBifunctor.{u, v} R).obj K).obj (fraction.{u, v} f).source) ≅
      DerivedCategory.Q.obj
        (((tensorBifunctor.{u, v} R).obj K).obj (dualRestricted.{u, v} f)) :=
  @asIso _ _ _ _ _ (isIso_tensor_fraction_den.{u, v} f hK)

/-- The forward map of `Stacks0BZE.tensorDenIso` is the class of the tensored denominator. -/
lemma tensorDenIso_hom {K : CochainComplex (ModuleCat.{max v u} R) ℤ}
    (hK : CochainComplex.KFlat.{u, max v u} K) :
    (tensorDenIso.{u, v} f hK).hom =
      DerivedCategory.Q.map
        (((tensorBifunctor.{u, v} R).obj K).map (fraction.{u, v} f).den) :=
  rfl

/-- Tensoring the derived counit `RHom_R(A, R) ⟶ R` of Stacks 0A70 with a K-flat complex `K`:
the map `Tot(K ⊗_R res RHom_R(A, R)) ⟶ K` in `D(R)`, computed from a chain-level fraction. -/
def tensorCounit (K : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hK : CochainComplex.KFlat.{u, max v u} K) :
    DerivedCategory.Q.obj
        (((tensorBifunctor.{u, v} R).obj K).obj (dualRestricted.{u, v} f)) ⟶
      DerivedCategory.Q.obj K :=
  (tensorDenIso.{u, v} f hK).inv ≫
    DerivedCategory.Q.map (((tensorBifunctor.{u, v} R).obj K).map (fraction.{u, v} f).num) ≫
    DerivedCategory.Q.map (unitorIso.{u, v} K).hom

/-- `Stacks0BZE.tensorCounit` is the inverse of the tensored denominator, followed by the tensored
numerator and the right unitor. -/
lemma tensorCounit_eq (K : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hK : CochainComplex.KFlat.{u, max v u} K) :
    tensorCounit.{u, v} f K hK = (tensorDenIso.{u, v} f hK).inv ≫
      DerivedCategory.Q.map (((tensorBifunctor.{u, v} R).obj K).map (fraction.{u, v} f).num) ≫
      DerivedCategory.Q.map (unitorIso.{u, v} K).hom :=
  rfl

/-- `Stacks0BZE.tensorCounit` is natural in chain maps between K-flat complexes. -/
theorem tensorCounit_naturality {K L : CochainComplex (ModuleCat.{max v u} R) ℤ}
    (hK : CochainComplex.KFlat.{u, max v u} K) (hL : CochainComplex.KFlat.{u, max v u} L)
    (a : K ⟶ L) :
    DerivedCategory.Q.map (((tensorBifunctor.{u, v} R).map a).app (dualRestricted.{u, v} f)) ≫
        tensorCounit.{u, v} f L hL =
      tensorCounit.{u, v} f K hK ≫ DerivedCategory.Q.map a := by
  have hden : (tensorDenIso.{u, v} f hK).hom ≫
        DerivedCategory.Q.map
          (((tensorBifunctor.{u, v} R).map a).app (dualRestricted.{u, v} f)) =
      DerivedCategory.Q.map
          (((tensorBifunctor.{u, v} R).map a).app (fraction.{u, v} f).source) ≫
        (tensorDenIso.{u, v} f hL).hom := by
    rw [tensorDenIso_hom, tensorDenIso_hom, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg DerivedCategory.Q.map
      (((tensorBifunctor.{u, v} R).map a).naturality (fraction.{u, v} f).den)
  have hnum : DerivedCategory.Q.map
        (((tensorBifunctor.{u, v} R).map a).app (fraction.{u, v} f).source) ≫
      DerivedCategory.Q.map (((tensorBifunctor.{u, v} R).obj L).map (fraction.{u, v} f).num) =
      DerivedCategory.Q.map (((tensorBifunctor.{u, v} R).obj K).map (fraction.{u, v} f).num) ≫
      DerivedCategory.Q.map
        (((tensorBifunctor.{u, v} R).map a).app (unitComplex.{u, v} R)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg DerivedCategory.Q.map
      (((tensorBifunctor.{u, v} R).map a).naturality (fraction.{u, v} f).num).symm
  have hunit : DerivedCategory.Q.map
        (((tensorBifunctor.{u, v} R).map a).app (unitComplex.{u, v} R)) ≫
      DerivedCategory.Q.map (unitorIso.{u, v} L).hom =
      DerivedCategory.Q.map (unitorIso.{u, v} K).hom ≫ DerivedCategory.Q.map a := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg DerivedCategory.Q.map (unitorIso_naturality.{u, v} a)
  rw [← cancel_epi (tensorDenIso.{u, v} f hK).hom, tensorCounit_eq, tensorCounit_eq,
    ← Category.assoc, hden]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, hnum, Category.assoc, hunit]

/-- On morphisms, `CochainComplex.tensorRightLarge M` agrees with `Stacks0BZE.tensorBifunctor`
evaluated at `M`. -/
lemma tensorRightLarge_map_eq (M : CochainComplex (ModuleCat.{max v u} R) ℤ)
    {K L : CochainComplex (ModuleCat.{max v u} R) ℤ} (a : K ⟶ L) :
    (CochainComplex.tensorRightLarge.{u, max v u} M).map a =
      ((tensorBifunctor.{u, v} R).map a).app M :=
  rfl

/-- The three structural comparisons of the bundle, composed: a natural transformation
`Q ⋙ (- ⊗ᴸ_R RHom_R(A,R)) ⋙ res ⟶ Tot(- ⊗_R res RHom_R(A,R)) ⋙ Q`. -/
def underlyingNatTrans :
    DerivedCategory.Q ⋙ ((bundle.{u, v} f).F ⋙ resDerived f) ⟶
      CochainComplex.tensorRightLarge.{u, max v u} (dualRestricted.{u, v} f) ⋙
        DerivedCategory.Q :=
  Functor.whiskerRight (bundle.{u, v} f).alphaF (resDerived f) ≫
    Functor.whiskerLeft (bundle.{u, v} f).directTensor
      (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategoryFactors.hom ≫
    Functor.whiskerRight (bundle.{u, v} f).directTensorUnderlying.hom DerivedCategory.Q

/-- The comparison `K ⊗ᴸ_R RHom_R(A, R) ⟶ K` in `D(R)`, that is, the restriction to `R` of the
comparison of Stacks 0BZE, written on a K-flat representative. -/
def restrictedComparison (K : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hK : CochainComplex.KFlat.{u, max v u} K) :
    (resDerived f).obj ((bundle.{u, v} f).F.obj (DerivedCategory.Q.obj K)) ⟶
      DerivedCategory.Q.obj K :=
  (underlyingNatTrans.{u, v} f).app K ≫ tensorCounit.{u, v} f K hK

/-- `Stacks0BZE.restrictedComparison` is `Stacks0BZE.underlyingNatTrans` followed by
`Stacks0BZE.tensorCounit`. -/
lemma restrictedComparison_eq (K : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hK : CochainComplex.KFlat.{u, max v u} K) :
    restrictedComparison.{u, v} f K hK =
      (underlyingNatTrans.{u, v} f).app K ≫ tensorCounit.{u, v} f K hK :=
  rfl

/-- `Stacks0BZE.restrictedComparison` is natural in chain maps between K-flat complexes. -/
theorem restrictedComparison_naturality {K L : CochainComplex (ModuleCat.{max v u} R) ℤ}
    (hK : CochainComplex.KFlat.{u, max v u} K) (hL : CochainComplex.KFlat.{u, max v u} L)
    (a : K ⟶ L) :
    (resDerived f).map ((bundle.{u, v} f).F.map (DerivedCategory.Q.map a)) ≫
        restrictedComparison.{u, v} f L hL =
      restrictedComparison.{u, v} f K hK ≫ DerivedCategory.Q.map a := by
  have hnu : (resDerived f).map ((bundle.{u, v} f).F.map (DerivedCategory.Q.map a)) ≫
        (underlyingNatTrans.{u, v} f).app L =
      (underlyingNatTrans.{u, v} f).app K ≫
        DerivedCategory.Q.map
          (((tensorBifunctor.{u, v} R).map a).app (dualRestricted.{u, v} f)) :=
    (underlyingNatTrans.{u, v} f).naturality a
  have htc := tensorCounit_naturality.{u, v} f hK hL a
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ tensorCounit.{u, v} f L hL) hnu).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z => (underlyingNatTrans.{u, v} f).app K ≫ z) htc).trans
          (Category.assoc _ _ _).symm)))

/-- **The comparison of Stacks 0BZE.** For a K-flat complex `K` of `R`-modules, a map
`K ⊗ᴸ_R RHom_R(A, R) ⟶ RHom_R(A, K)` in `D(A)`: the transpose, under the adjunction of
Stacks 0A70, of `Stacks0BZE.restrictedComparison`. -/
def comparison (K : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hK : CochainComplex.KFlat.{u, max v u} K) :
    (bundle.{u, v} f).F.obj (DerivedCategory.Q.obj K) ⟶
      (Dualizing.derivedHom.{u, v} f).obj (DerivedCategory.Q.obj K) :=
  (Dualizing.derivedHomAdjunction.{u, u, v} f).homEquiv _ _
    (restrictedComparison.{u, v} f K hK)

/-- `Stacks0BZE.comparison` is natural in chain maps between K-flat complexes. -/
theorem comparison_naturality {K L : CochainComplex (ModuleCat.{max v u} R) ℤ}
    (hK : CochainComplex.KFlat.{u, max v u} K) (hL : CochainComplex.KFlat.{u, max v u} L)
    (a : K ⟶ L) :
    comparison.{u, v} f K hK ≫
        (Dualizing.derivedHom.{u, v} f).map (DerivedCategory.Q.map a) =
      (bundle.{u, v} f).F.map (DerivedCategory.Q.map a) ≫ comparison.{u, v} f L hL := by
  rw [comparison, comparison, ← Adjunction.homEquiv_naturality_right,
    ← Adjunction.homEquiv_naturality_left]
  exact congrArg _ (restrictedComparison_naturality.{u, v} f hK hL a).symm

/-- `Stacks0BZE.comparison` is the adjoint transpose of `Stacks0BZE.restrictedComparison`. -/
lemma comparison_eq (K : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hK : CochainComplex.KFlat.{u, max v u} K) :
    comparison.{u, v} f K hK = (Dualizing.derivedHomAdjunction.{u, u, v} f).homEquiv _ _
      (restrictedComparison.{u, v} f K hK) :=
  rfl

/-- The defining property of `Stacks0BZE.comparison`: restricted to `R` and followed by the
counit of Stacks 0A70, it is `Stacks0BZE.restrictedComparison`. -/
theorem restrictScalars_comparison_comp_counit (K : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hK : CochainComplex.KFlat.{u, max v u} K) :
    (resDerived f).map (comparison.{u, v} f K hK) ≫
        (Dualizing.derivedHomAdjunction.{u, u, v} f).counit.app (DerivedCategory.Q.obj K) =
      restrictedComparison.{u, v} f K hK :=
  ((Dualizing.derivedHomAdjunction.{u, u, v} f).homEquiv_counit
      (g := comparison.{u, v} f K hK)).symm.trans
    (((Dualizing.derivedHomAdjunction.{u, u, v} f).homEquiv
      ((bundle.{u, v} f).F.obj (DerivedCategory.Q.obj K))
      (DerivedCategory.Q.obj K)).symm_apply_apply
      (restrictedComparison.{u, v} f K hK))

/-- Invertibility of `Stacks0BZE.comparison` may be checked after restriction of scalars:
restriction induces a conservative functor on derived categories. -/
theorem isIso_comparison_of_restrictScalars (K : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hK : CochainComplex.KFlat.{u, max v u} K)
    (h : IsIso ((resDerived f).map (comparison.{u, v} f K hK))) :
    IsIso (comparison.{u, v} f K hK) :=
  have := h
  isIso_of_reflects_iso (comparison.{u, v} f K hK)
    (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory

/-- A family of isomorphisms realizing `Stacks0BZE.comparison` on the K-flat complexes descends
to an isomorphism of functors on all of `D(R)`: the K-flat complexes resolve, so a comparison
natural in chain maps between them determines one on the localization. -/
def cardIsoOfIsos
    (e : ∀ (K : CochainComplex (ModuleCat.{max v u} R) ℤ),
      CochainComplex.KFlat.{u, max v u} K →
        ((bundle.{u, v} f).F.obj (DerivedCategory.Q.obj K) ≅
          (Dualizing.derivedHom.{u, v} f).obj (DerivedCategory.Q.obj K)))
    (he : ∀ K hK, comparison.{u, v} f K hK = (e K hK).hom) :
    Dualizing.derivedHom.{u, v} f ≅ (bundle.{u, v} f).F :=
  ModuleSystemRlimTensor.natIsoOfResolutions
    (B := ModuleCat.{max v u} R) (fun K => CochainComplex.KFlat K)
    (fun K => by
      obtain ⟨P, s, hP, _, hs, _⟩ := CochainComplex.KFlat.exists_kFlat_resolution K
      exact ⟨P, s, hP, hs⟩)
    _ _ (fun K hK => (e K hK).symm)
    (fun K L hK hL g => by
      have h := comparison_naturality.{u, v} f hK hL g
      simp only [Iso.symm_hom]
      rw [← cancel_epi (e K hK).hom, Iso.hom_inv_id_assoc, ← he K hK, ← Category.assoc, h,
        he L hL, Category.assoc, Iso.hom_inv_id, Category.comp_id])

/-- Given invertibility of `Stacks0BZE.comparison` at every K-flat complex, the comparison
descends to an isomorphism of functors on all of `D(R)`. -/
def cardIso
    (hiso : ∀ (K : CochainComplex (ModuleCat.{max v u} R) ℤ)
      (hK : CochainComplex.KFlat.{u, max v u} K), IsIso (comparison.{u, v} f K hK)) :
    Dualizing.derivedHom.{u, v} f ≅ (bundle.{u, v} f).F :=
  cardIsoOfIsos.{u, v} f
    (fun K hK => letI := hiso K hK; asIso (comparison.{u, v} f K hK))
    (fun _ _ => rfl)

/-- **Stacks 0BZE, from any natural family of isomorphisms on the K-flat complexes.** The
family is not required to realize `Stacks0BZE.comparison`. -/
theorem card_of_kFlatComparison
    (hperfect : letI := f.toAlgebra
      StacksDraft.Perfect.IsPerfectModule (R := R) A)
    (hcomp : ∃ e : ∀ K : CochainComplex (ModuleCat.{max v u} R) ℤ,
        CochainComplex.KFlat.{u, max v u} K →
          ((Dualizing.derivedHom.{u, v} f).obj (DerivedCategory.Q.obj K) ≅
            (bundle.{u, v} f).F.obj (DerivedCategory.Q.obj K)),
      ∀ K L (hK : CochainComplex.KFlat.{u, max v u} K)
        (hL : CochainComplex.KFlat.{u, max v u} L) (g : K ⟶ L),
        (Dualizing.derivedHom.{u, v} f).map (DerivedCategory.Q.map g) ≫ (e L hL).hom =
          (e K hK).hom ≫ (bundle.{u, v} f).F.map (DerivedCategory.Q.map g)) :
    letI : MonoidalCategoryStruct (ModuleCat.{max v u} R) :=
      ModuleCat.liftedModuleMonoidalStruct.{u, max v u}
    letI : MonoidalCategory (ModuleCat.{max v u} R) :=
      ModuleCat.liftedModuleMonoidal.{u, max v u}
    let R₀ := (DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
      (MonoidalCategoryStruct.tensorUnit (ModuleCat.{max v u} R))
    Nonempty (Dualizing.derivedHom.{u, v} f ≅
      (CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f
        ((DerivedCategory.Qh (C := ModuleCat.{max v u} A)).objPreimage
          ((Dualizing.derivedHom.{u, v} f).obj R₀)).as).F) := by
  intro R₀
  have := hperfect
  obtain ⟨e, he⟩ := hcomp
  exact ⟨ModuleSystemRlimTensor.natIsoOfResolutions
    (B := ModuleCat.{max v u} R) (fun K => CochainComplex.KFlat K)
    (fun K => by
      obtain ⟨P, s, hP, _, hs, _⟩ := CochainComplex.KFlat.exists_kFlat_resolution K
      exact ⟨P, s, hP, hs⟩)
    _ _ e he⟩

/-- **Stacks 0BZE, from invertibility of the comparison on K-flat complexes.** If
`Stacks0BZE.comparison` is invertible at every K-flat complex, then derived coextension of
scalars along `f` is isomorphic, as a functor, to the derived tensor product with
`RHom_R(A, R)`. -/
theorem card_of_isIso_comparison
    (hperfect : letI := f.toAlgebra
      StacksDraft.Perfect.IsPerfectModule (R := R) A)
    (hiso : ∀ (K : CochainComplex (ModuleCat.{max v u} R) ℤ)
      (hK : CochainComplex.KFlat.{u, max v u} K), IsIso (comparison.{u, v} f K hK)) :
    letI : MonoidalCategoryStruct (ModuleCat.{max v u} R) :=
      ModuleCat.liftedModuleMonoidalStruct.{u, max v u}
    letI : MonoidalCategory (ModuleCat.{max v u} R) :=
      ModuleCat.liftedModuleMonoidal.{u, max v u}
    let R₀ := (DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
      (MonoidalCategoryStruct.tensorUnit (ModuleCat.{max v u} R))
    Nonempty (Dualizing.derivedHom.{u, v} f ≅
      (CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f
        ((DerivedCategory.Qh (C := ModuleCat.{max v u} A)).objPreimage
          ((Dualizing.derivedHom.{u, v} f).obj R₀)).as).F) := by
  intro R₀
  have := hperfect
  exact ⟨cardIso.{u, v} f hiso⟩


end Stacks0BZE
end
