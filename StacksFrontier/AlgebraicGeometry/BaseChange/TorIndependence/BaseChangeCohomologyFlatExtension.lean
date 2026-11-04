module

public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsSelfIso
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeCohomologyFunctor
public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeCohomologySingleDegree
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMap
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsSingleDegree
public import StacksFrontier.Homology.Tor.TorFlatBaseChangeSecond
import all StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMap

/-!
# A flat extension of the algebra passes through base-change cohomology

Let `R → A` and `R → R'` be homomorphisms of commutative rings and let `A → A₂` be a *flat*
homomorphism — a localization, for instance. For `K` an object of `D(A)` there is an isomorphism
of `A₂`-modules, called (L) below,

`A₂ ⊗_A H^n(K|_R ⊗ᴸ_R R')  ≅  H^n(((K ⊗ᴸ_A A₂)|_R) ⊗ᴸ_R R')`,

natural in `K`: extending the algebra by a flat map commutes, on cohomology, with derived base
change along an arbitrary `R → R'`. The `A`-module structure on `H^n(K|_R ⊗ᴸ_R R')` is the one
`RingTheory.TorIndependence.baseChangeCohomology` records, coming from the `A`-linearity of
`D(A)`. The comparison is obtained from the unit of the derived change-of-rings adjunction of
[stacks 0GMT], and it is equivariant for the right tensor factor `R'`, which with its
`A₂`-linearity is linearity over all of `A₂ ⊗_R R'`.

## Main definitions

* `RingTheory.TorIndependence.mapDerivedCategoryCompIso`: a composition isomorphism for
  `CategoryTheory.Functor.mapDerivedCategory`.
* `RingTheory.TorIndependence.derivedBaseChangeRestrictIso`: the derived base change of an
  `A₂`-complex read over `A` is its derived base change read over `A₂`.
* `RingTheory.TorIndependence.baseChangeCohomologyRestrictNatTrans`: the same statement on
  cohomology, as `A`-modules.
* `RingTheory.TorIndependence.localizedBaseChangeCohomologyFunctor` and
  `RingTheory.TorIndependence.baseChangeCohomologyExtendFunctor`: the two sides of the
  displayed formula, as functors `D(A) ⥤ ModuleCat A₂`.
* `RingTheory.TorIndependence.localizedBaseChangeCohomologyComparison`: the comparison between
  them, obtained from the unit of the derived change-of-rings adjunction of [stacks 0GMT] by
  the adjunction between extension and restriction of scalars along `A → A₂`.

## Main results

* `RingTheory.TorIndependence.isIso_localizedBaseChangeCohomologyComparison` and
  `RingTheory.TorIndependence.localizedBaseChangeCohomologyIso`: the comparison is invertible at
  every object of `D(A)`.
* `RingTheory.TorIndependence.isIso_localizedBaseChangeCohomologyComparison_app_single`
  and its shifted form `…_app_shift_regularModule`: the generator case, where the comparison is
  the flat base change of `Tor` in its second variable.
* `RingTheory.TorIndependence.derivedBaseChange_unit_single_regular`: at the regular module in
  degree `d` the unit of the derived change-of-rings adjunction, read on derived base changes, is
  the derived base change of the structure map `A → A₂` in that degree.
* `RingTheory.TorIndependence.isHomological_baseChangeCohomologyFunctor` and
  `RingTheory.TorIndependence.preservesColimitsOfShape_baseChangeCohomologyFunctor`: the
  `A ⊗_R R'`-valued base-change cohomology is homological and preserves direct sums.
* `RingTheory.TorIndependence.isHomological_of_restrictScalars` and
  `RingTheory.TorIndependence.preservesColimitsOfShape_of_restrictScalars`: a functor into
  modules is homological, resp. preserves direct sums, as soon as it is after a restriction of
  scalars.
* `RingTheory.TorIndependence.isHomological_comp_of_exact`: a homological functor followed by an
  exact functor is homological.
* `RingTheory.TorIndependence.localizedBaseChangeCohomologyComparison_app_includeRight_smul`
  and the two steps it is assembled from,
  `RingTheory.TorIndependence.baseChangeCohomologyRestrictMap_includeRight_smul` and
  `RingTheory.TorIndependence.baseChangeCohomologyUnitNatTrans_app_includeRight_smul`: the
  comparison is equivariant for the right tensor factor `R'`, which with its `A₂`-linearity is
  linearity over all of `A₂ ⊗_R R'`.

## Implementation notes

Both sides of (L) are `A₂`-valued rather than `A₂ ⊗_R R'`-valued: the `A₂`-module structure on the
right-hand side is the one the left tensor factor of `A₂ ⊗_R R'` supplies, and the comparison is
the transpose of an `A`-linear map under `ModuleCat.extendRestrictScalarsAdj`, which needs no
flatness of `A ⊗_R R' → A₂ ⊗_R R'`. The equivariance for `R'` is stated on elements: the right
tensor factor acts on `A₂ ⊗_A (H^n(K|_R ⊗ᴸ_R R')|_A)` through the second factor, which is not a
`Module` instance on that carrier.

The model of the derived category is a binder `[HasDerivedCategory.{u} (ModuleCat.{u} ·)]` for
each of the four rings, not `HasDerivedCategory.standard`. The morphism universe `u` is the one at
which the regular module is a compact generator and at which `ModuleCat.{u}` has the coproducts
`StacksDraft.HomologicalDevissage.isIso_of_isIso_app_shift_regularModule` uses.

## References

* [The Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [The Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [The Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
* [The Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Functor
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct ChangeOfRings

universe u w

namespace RingTheory.TorIndependence

/-! ### A composition isomorphism for `mapDerivedCategory` -/

section CompIso

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]
  (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (H : C₁ ⥤ C₃)
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- A natural isomorphism `F ⋙ G ≅ H` between exact functors of abelian categories, read on
derived categories. -/
def mapDerivedCategoryCompIso (e : F ⋙ G ≅ H) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ G.mapDerivedCategory))
    (DerivedCategory.Q ⋙ H.mapDerivedCategory) _ _
    (Functor.isoWhiskerRight F.mapDerivedCategoryFactors G.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        G.mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ))
        DerivedCategory.Q ≪≫ H.mapDerivedCategoryFactors.symm)

end CompIso

/-! ### The derived base change of a complex read over an intermediate ring -/

section Restrict

variable {R A A₂ R' : Type u} [CommRing R] [CommRing A] [CommRing A₂] [CommRing R']
  [Algebra R A] [Algebra A A₂] [Algebra R A₂] [IsScalarTower R A A₂] [Algebra R R']
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w} (ModuleCat.{u} A₂)] [HasDerivedCategory.{w} (ModuleCat.{u} R')]

/-- Restriction of scalars along a tower `R → A → A₂`, read on derived categories. -/
def restrictScalarsTowerDerivedIso :
    (ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars.{u} (algebraMap R A)).mapDerivedCategory ≅
      (ModuleCat.restrictScalars.{u} (algebraMap R A₂)).mapDerivedCategory :=
  mapDerivedCategoryCompIso _ _ _
    (ModuleCat.restrictScalarsComp'.{u} (algebraMap R A) (algebraMap A A₂) (algebraMap R A₂)
      (IsScalarTower.algebraMap_eq R A A₂)).symm

/-- **The derived base change of an `A₂`-complex read over `A` is its derived base change read
over `A₂`.** -/
def derivedBaseChangeRestrictIso :
    (ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory ⋙
        derivedBaseChangeFunctor (R := R) (A := A) (R' := R') ≅
      derivedBaseChangeFunctor (R := R) (A := A₂) (R' := R') :=
  Functor.isoWhiskerRight (restrictScalarsTowerDerivedIso (R := R) (A := A) (A₂ := A₂))
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).functor

end Restrict

/-! ### Reflecting exactness and direct sums along a restriction of scalars -/

section Reflect

/-- A short complex of modules exact after a restriction of scalars is exact. -/
theorem shortComplex_exact_of_restrictScalars {S T : Type u} [Ring S] [Ring T] (f : S →+* T)
    (C : ShortComplex (ModuleCat.{u} T))
    (h : (C.map (ModuleCat.restrictScalars.{u} f)).Exact) : C.Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  rw [ShortComplex.moduleCat_exact_iff] at h
  exact h

variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **A functor into modules is homological as soon as it is after a restriction of scalars.** -/
theorem isHomological_of_restrictScalars {S T : Type u} [Ring S] [Ring T] (f : S →+* T)
    (F : D ⥤ ModuleCat.{u} T)
    [(F ⋙ ModuleCat.restrictScalars.{u} f).IsHomological] : F.IsHomological := by
  have hz : F.PreservesZeroMorphisms := by
    refine ⟨fun {X Y} => (ModuleCat.restrictScalars.{u} f).map_injective ?_⟩
    have h0 := (F ⋙ ModuleCat.restrictScalars.{u} f).map_zero X Y
    rw [Functor.comp_map] at h0
    rw [h0, Functor.map_zero]
  refine ⟨fun T' hT' => shortComplex_exact_of_restrictScalars f _ ?_⟩
  exact (F ⋙ ModuleCat.restrictScalars.{u} f).map_distinguished_exact T' hT'

omit [Preadditive D] [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] in
/-- **A functor into modules preserves direct sums as soon as it does after a restriction of
scalars.** -/
theorem preservesColimitsOfShape_of_restrictScalars {S T : Type u} [Ring S] [Ring T]
    (f : S →+* T) {J : Type u} (F : D ⥤ ModuleCat.{u} T)
    [PreservesColimitsOfShape (Discrete J) (F ⋙ ModuleCat.restrictScalars.{u} f)] :
    PreservesColimitsOfShape (Discrete J) F := by
  have : ReflectsColimitsOfShape (Discrete J) (ModuleCat.restrictScalars.{u} f) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves F (ModuleCat.restrictScalars.{u} f)

end Reflect

/-! ### The cohomology functor over the base, and the tensor-product functor -/

section Over

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w} (ModuleCat.{u} R')]

/-- The right tensor inclusion `R' → A ⊗_R R'`, as a ring homomorphism. -/
abbrev includeRightRingHom (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] : R' →+* A ⊗[R] R' :=
  (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := R')).toRingHom

/-- The left tensor inclusion `A → A ⊗_R R'`, as a ring homomorphism. -/
abbrev includeLeftRingHom (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] : A →+* A ⊗[R] R' :=
  (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := A) (B := R')).toRingHom

/-- **The `A ⊗_R R'`-valued cohomology functor, read over `R'`, is the cohomology of the derived
base change.** The two are the same object with the same maps: only the action is forgotten. -/
def baseChangeCohomologyFunctorRestrictIso (n : ℤ) :
    baseChangeCohomologyFunctor (R := R) (A := A) (R' := R') n ⋙
        ModuleCat.restrictScalars.{u} (includeRightRingHom R A R') ≅
      derivedBaseChangeFunctor (R := R) (A := A) (R' := R') ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} R') n :=
  NatIso.ofComponents
    (fun K => (AddEquiv.toLinearEquiv
      (M := (ModuleCat.restrictScalars.{u} (includeRightRingHom R A R')).obj
        (baseChangeCohomology (R := R) (R' := R') K n))
      (M₂ := baseChangeCohomologyOverBase (R := R) (R' := R') K n)
      (AddEquiv.refl _)
      (fun r x => baseChangeCohomology_includeRight_smul (R := R) (R' := R') K n r x)).toModuleIso)
    (fun φ => by
      refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
      rfl)

/-- **The `A ⊗_R R'`-valued cohomology of a derived base change is a homological functor.** -/
theorem isHomological_baseChangeCohomologyFunctor (n : ℤ) :
    (baseChangeCohomologyFunctor (R := R) (A := A) (R' := R') n).IsHomological := by
  have h := isHomological_derivedBaseChangeHomology (R := R) (A := A) (R' := R') n
  have : (baseChangeCohomologyFunctor (R := R) (A := A) (R' := R') n ⋙
      ModuleCat.restrictScalars.{u} (includeRightRingHom R A R')).IsHomological :=
    Functor.IsHomological.of_iso (baseChangeCohomologyFunctorRestrictIso n).symm
  exact isHomological_of_restrictScalars (includeRightRingHom R A R') _

end Over

section OverColimits

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  [HasDerivedCategory.{u} (ModuleCat.{u} R)] [HasDerivedCategory.{u} (ModuleCat.{u} A)]
  [HasDerivedCategory.{u} (ModuleCat.{u} R')]

/-- **The `A ⊗_R R'`-valued cohomology of a derived base change preserves direct sums.** -/
theorem preservesColimitsOfShape_baseChangeCohomologyFunctor (J : Type u) (n : ℤ) :
    PreservesColimitsOfShape (Discrete J)
      (baseChangeCohomologyFunctor (R := R) (A := A) (R' := R') n) := by
  have h := preservesColimitsOfShape_derivedBaseChangeHomology (R := R) (A := A) (R' := R') J n
  have : PreservesColimitsOfShape (Discrete J)
      (baseChangeCohomologyFunctor (R := R) (A := A) (R' := R') n ⋙
        ModuleCat.restrictScalars.{u} (includeRightRingHom R A R')) :=
    (preservesColimitsOfShape_iff_of_natIso
      (baseChangeCohomologyFunctorRestrictIso (R := R) (A := A) (R' := R') n)).2 h
  exact preservesColimitsOfShape_of_restrictScalars (includeRightRingHom R A R') _

end OverColimits

/-! ### The base-change cohomology of an `A₂`-complex, read over `A` -/

section Comparison

variable {R A A₂ R' : Type u} [CommRing R] [CommRing A] [CommRing A₂] [CommRing R']
  [Algebra R A] [Algebra A A₂] [Algebra R A₂] [IsScalarTower R A A₂] [Algebra R R']
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w} (ModuleCat.{u} A₂)] [HasDerivedCategory.{w} (ModuleCat.{u} R')]

/-- The comparison of the base-change cohomology of an `A₂`-complex read over `A` with its
base-change cohomology read over `A₂`, as a morphism of `R'`-modules. -/
def baseChangeCohomologyRestrictMap (n : ℤ) (L : DerivedCategory (ModuleCat.{u} A₂)) :
    baseChangeCohomologyOverBase (R := R) (R' := R')
        ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory.obj L) n ⟶
      baseChangeCohomologyOverBase (R := R) (R' := R') L n :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
    ((derivedBaseChangeRestrictIso (R := R) (A := A) (A₂ := A₂) (R' := R')).hom.app L)

/-- The comparison `baseChangeCohomologyRestrictMap` of the base-change cohomology of an
`A₂`-complex read over `A` and over `A₂` is an isomorphism. -/
instance isIso_baseChangeCohomologyRestrictMap (n : ℤ)
    (L : DerivedCategory (ModuleCat.{u} A₂)) :
    IsIso (baseChangeCohomologyRestrictMap (R := R) (A := A) (A₂ := A₂) (R' := R') n L) :=
  inferInstanceAs (IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
    ((derivedBaseChangeRestrictIso (R := R) (A := A) (A₂ := A₂) (R' := R')).hom.app L)))

/-- A functor carries an equality of composites to an equality of composites. -/
private theorem map_comp_eq_map_comp {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z W : C} {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X ⟶ W} {g' : W ⟶ Z} (e : f ≫ g = f' ≫ g') :
    F.map f ≫ F.map g = F.map f' ≫ F.map g' := by
  rw [← F.map_comp, ← F.map_comp, e]

/-- The comparison is natural in the `A₂`-complex. -/
theorem baseChangeCohomologyRestrictMap_naturality (n : ℤ)
    {L L' : DerivedCategory (ModuleCat.{u} A₂)} (φ : L ⟶ L') :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
          ((derivedBaseChangeFunctor (R := R) (A := A) (R' := R')).map
            ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory.map φ)) ≫
        baseChangeCohomologyRestrictMap (R := R) (A := A) n L' =
      baseChangeCohomologyRestrictMap (R := R) (A := A) n L ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
          ((derivedBaseChangeFunctor (R := R) (A := A₂) (R' := R')).map φ) := by
  exact map_comp_eq_map_comp (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n)
    ((derivedBaseChangeRestrictIso (R := R) (A := A) (A₂ := A₂) (R' := R')).hom.naturality φ)

/-- **The comparison carries the action of `A` on the left to the action of `A₂` on the left.**
Scalar multiplication by `a : A` on an `A₂`-complex read over `A` is scalar multiplication by
`algebraMap a` on the complex itself. -/
theorem baseChangeCohomologyRestrictMap_includeLeft_smul (n : ℤ)
    (L : DerivedCategory (ModuleCat.{u} A₂)) (a : A)
    (x : baseChangeCohomology (R := R) (R' := R')
      ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory.obj L) n) :
    (baseChangeCohomologyRestrictMap (R := R) (A := A) n L).hom
        (show baseChangeCohomologyOverBase (R := R) (R' := R')
            ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory.obj L) n from
          (Algebra.TensorProduct.includeLeft (R := R) (S := R) a : A ⊗[R] R') • x) =
      (Algebra.TensorProduct.includeLeft (R := R) (S := R) (algebraMap A A₂ a) :
            A₂ ⊗[R] R') •
        (show baseChangeCohomology (R := R) (R' := R') L n from
          (baseChangeCohomologyRestrictMap (R := R) (A := A) n L).hom
            (show baseChangeCohomologyOverBase (R := R) (R' := R')
              ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory.obj L) n
              from x)) := by
  have hs := exactFunctor_scalar (ModuleCat.restrictScalars.{u} (algebraMap A A₂))
    (algebraMap A A₂ a) a (fun M => by ext m; rfl) L
  have hnat := baseChangeCohomologyRestrictMap_naturality (R := R) (A := A) (A₂ := A₂)
    (R' := R') n (algebraMap A A₂ a • 𝟙 L)
  rw [hs] at hnat
  rw [baseChangeCohomology_includeLeft_smul, baseChangeCohomology_includeLeft_smul]
  exact congrArg (fun ξ => ModuleCat.Hom.hom ξ
    (show baseChangeCohomologyOverBase (R := R) (R' := R')
      ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory.obj L) n
      from x)) hnat

/-- **The comparison carries the action of `R'` on the right to the action of `R'` on the
right.** -/
theorem baseChangeCohomologyRestrictMap_includeRight_smul (n : ℤ)
    (L : DerivedCategory (ModuleCat.{u} A₂)) (r : R')
    (x : baseChangeCohomology (R := R) (R' := R')
      ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory.obj L) n) :
    (baseChangeCohomologyRestrictMap (R := R) (A := A) n L).hom
        (show baseChangeCohomologyOverBase (R := R) (R' := R')
            ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory.obj L) n from
          (Algebra.TensorProduct.includeRight r : A ⊗[R] R') • x) =
      (Algebra.TensorProduct.includeRight r : A₂ ⊗[R] R') •
        (show baseChangeCohomology (R := R) (R' := R') L n from
          (baseChangeCohomologyRestrictMap (R := R) (A := A) n L).hom
            (show baseChangeCohomologyOverBase (R := R) (R' := R')
              ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory.obj L) n
              from x)) := by
  rw [baseChangeCohomology_includeRight_smul, baseChangeCohomology_includeRight_smul]
  exact (baseChangeCohomologyRestrictMap (R := R) (A := A) (A₂ := A₂) (R' := R') n L).hom.map_smul
    r (show baseChangeCohomologyOverBase (R := R) (R' := R')
      ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory.obj L) n from x)

/-- **The comparison carries scalar multiplication on the complex to the action of `A₂` on the
left.** For `x : A₂`, the action of `x` on the base-change cohomology of `L|_A` is only the one
the functor supplies — the module structure there is over `A ⊗_R R'`, which does not see `A₂` —
while on the base-change cohomology of `L` it is the action of the left tensor factor of
`A₂ ⊗_R R'`. The comparison carries the first to the second. -/
theorem baseChangeCohomologyRestrictMap_smul (n : ℤ)
    (L : DerivedCategory (ModuleCat.{u} A₂)) (x : A₂)
    (m : baseChangeCohomology (R := R) (R' := R')
      ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory.obj L) n) :
    (baseChangeCohomologyRestrictMap (R := R) (A := A) n L).hom
        (show baseChangeCohomologyOverBase (R := R) (R' := R')
            ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory.obj L) n from
          ((((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory ⋙
                derivedBaseChangeFunctor (R := R) (A := A) (R' := R')) ⋙
              DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map (x • 𝟙 L)).hom m) =
      (Algebra.TensorProduct.includeLeft (R := R) (S := R) x : A₂ ⊗[R] R') •
        (show baseChangeCohomology (R := R) (R' := R') L n from
          (baseChangeCohomologyRestrictMap (R := R) (A := A) n L).hom
            (show baseChangeCohomologyOverBase (R := R) (R' := R')
              ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory.obj L) n
              from m)) := by
  have hnat := baseChangeCohomologyRestrictMap_naturality (R := R) (A := A) (A₂ := A₂)
    (R' := R') n (x • 𝟙 L)
  rw [baseChangeCohomology_includeLeft_smul]
  exact ConcreteCategory.congr_hom hnat m

/-- **The base-change cohomology of an `A₂`-complex, read over `A`, maps to its base-change
cohomology over `A₂` with the `A`-action restricted along `A → A₂`.** Both sides are read as
`A`-modules through the left tensor inclusion, and the map is the identity on underlying groups
up to the comparison of the two readings over `R`. -/
def baseChangeCohomologyRestrictNatTrans (n : ℤ) :
    (ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory ⋙
        baseChangeCohomologyFunctor (R := R) (A := A) (R' := R') n ⋙
          ModuleCat.restrictScalars.{u} (includeLeftRingHom R A R') ⟶
      baseChangeCohomologyFunctor (R := R) (A := A₂) (R' := R') n ⋙
        ModuleCat.restrictScalars.{u} (includeLeftRingHom R A₂ R') ⋙
          ModuleCat.restrictScalars.{u} (algebraMap A A₂) where
  app L :=
    ModuleCat.ofHom
      (X := (ModuleCat.restrictScalars.{u} (includeLeftRingHom R A R')).obj
        (baseChangeCohomology (R := R) (R' := R')
          ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory.obj L) n))
      (Y := (ModuleCat.restrictScalars.{u} (algebraMap A A₂)).obj
        ((ModuleCat.restrictScalars.{u} (includeLeftRingHom R A₂ R')).obj
          (baseChangeCohomology (R := R) (R' := R') L n)))
      { toFun := fun x =>
          (baseChangeCohomologyRestrictMap (R := R) (A := A) (A₂ := A₂) (R' := R') n L).hom x
        map_add' := fun x y =>
          (baseChangeCohomologyRestrictMap (R := R) (A := A) (A₂ := A₂) (R' := R') n L).hom.map_add
            x y
        map_smul' := fun a x =>
          baseChangeCohomologyRestrictMap_includeLeft_smul
            (R := R) (A := A) (A₂ := A₂) (R' := R') n L a x }
  naturality {L L'} φ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
    exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp
      (baseChangeCohomologyRestrictMap_naturality (R := R) (A := A) (A₂ := A₂) (R' := R') n φ)) m

end Comparison

/-! ### Postcomposing a homological functor with an exact functor -/

section PostCompose

variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {A₃ B₃ : Type*} [Category A₃] [Abelian A₃] [Category B₃] [Abelian B₃]

/-- A homological functor followed by an exact functor is homological. -/
theorem isHomological_comp_of_exact (F : D ⥤ A₃) [F.IsHomological] (G : A₃ ⥤ B₃) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] : (F ⋙ G).IsHomological := by
  have : G.PreservesHomology := {}
  exact ⟨fun T hT => (F.map_distinguished_exact T hT).map G⟩

end PostCompose

/-! ### The comparison is invertible at the regular module in a single degree -/

section SingleRegular

variable {A : Type u} [CommRing A]

/-- The regular module in degree `d` is a complex of projectives. -/
instance projective_single_regular_X (d i : ℤ) :
    Projective (((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) d).obj
      (ModuleCat.of A A)).X i) := by
  by_cases hi : i = d
  · exact Projective.of_iso
      (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) d (ModuleCat.of A A) i hi).symm
      inferInstance
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) d (ModuleCat.of A A) i
      hi).projective

variable {A₂ : Type u} [CommRing A₂] [Algebra A A₂]
  [HasDerivedCategory.{u} (ModuleCat.{u} A)] [HasDerivedCategory.{u} (ModuleCat.{u} A₂)]

/-- **The comparison of derived with termwise extension of scalars is invertible at the regular
module in degree `d`.** -/
instance isIso_comparison_single_regular (d : ℤ) :
    IsIso ((totalDerivedExtensionScalars.{u, u, u, u, u} (algebraMap A A₂)).comparison.app
      ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) d).obj
        (ModuleCat.of A A))) :=
  (totalDerivedExtensionScalars.{u, u, u, u, u}
    (algebraMap A A₂)).comparison_isIso_of_projective _ d

/-- **Derived extension of scalars carries the regular module in degree `d` to the regular
module in degree `d`.** -/
def singleRegularExtendIso (d : ℤ) :
    (totalDerivedExtensionScalars.{u, u, u, u, u} (algebraMap A A₂)).functor.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) d).obj (ModuleCat.of A A)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A₂) d).obj (ModuleCat.of A₂ A₂) :=
  singleExtendIso (algebraMap A A₂)
      (totalDerivedExtensionScalars.{u, u, u, u, u} (algebraMap A A₂)).functor
      (totalDerivedExtensionScalars.{u, u, u, u, u} (algebraMap A A₂)).comparison d
      (ModuleCat.of A A) (isIso_comparison_single_regular (A := A) (A₂ := A₂) d) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} A₂) d).mapIso
      (ModuleCat.extendScalarsSelfIso (algebraMap A A₂))

/-- The two factors of `singleRegularExtendIso`. -/
theorem singleRegularExtendIso_hom (d : ℤ) :
    (singleRegularExtendIso (A := A) (A₂ := A₂) d).hom =
      (singleExtendIso (algebraMap A A₂)
          (totalDerivedExtensionScalars.{u, u, u, u, u} (algebraMap A A₂)).functor
          (totalDerivedExtensionScalars.{u, u, u, u, u} (algebraMap A A₂)).comparison d
          (ModuleCat.of A A) (isIso_comparison_single_regular (A := A) (A₂ := A₂) d)).hom ≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} A₂) d).map
          (ModuleCat.extendScalarsTranspose (algebraMap A A₂)
            (ModuleCat.structureHom (algebraMap A A₂))) :=
  rfl

end SingleRegular

/-! ### The two functors of (L), and the comparison between them -/

section Main

variable {R A A₂ R' : Type u} [CommRing R] [CommRing A] [CommRing A₂] [CommRing R']
  [Algebra R A] [Algebra A A₂] [Algebra R A₂] [IsScalarTower R A A₂] [Algebra R R']
  [HasDerivedCategory.{u} (ModuleCat.{u} R)] [HasDerivedCategory.{u} (ModuleCat.{u} A)]
  [HasDerivedCategory.{u} (ModuleCat.{u} A₂)] [HasDerivedCategory.{u} (ModuleCat.{u} R')]

/-- `K ↦ A₂ ⊗_A H^n(K|_R ⊗ᴸ_R R')`, the left-hand side of (L). The `A`-module structure on the
base-change cohomology is the one the left tensor factor of `A ⊗_R R'` provides. -/
def localizedBaseChangeCohomologyFunctor (n : ℤ) :
    DerivedCategory (ModuleCat.{u} A) ⥤ ModuleCat.{u} A₂ :=
  baseChangeCohomologyFunctor (R := R) (A := A) (R' := R') n ⋙
    ModuleCat.restrictScalars.{u} (includeLeftRingHom R A R') ⋙
      ModuleCat.extendScalars.{u, u, u} (algebraMap A A₂)

/-- `K ↦ H^n(((K ⊗ᴸ_A A₂)|_R) ⊗ᴸ_R R')`, the right-hand side of (L), read as an `A₂`-module
through the left tensor factor of `A₂ ⊗_R R'`. -/
def baseChangeCohomologyExtendFunctor (n : ℤ) :
    DerivedCategory (ModuleCat.{u} A) ⥤ ModuleCat.{u} A₂ :=
  (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).functor ⋙
    baseChangeCohomologyFunctor (R := R) (A := A₂) (R' := R') n ⋙
      ModuleCat.restrictScalars.{u} (includeLeftRingHom R A₂ R')

/-- The derived change-of-rings adjunction of [stacks 0GMT] at the model computed by K-flat
resolutions: derived extension of scalars along `A → A₂` is left adjoint to derived restriction
of scalars. -/
def derivedExtendRestrictAdjunction :
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).functor ⊣
      (ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory :=
  @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u, u, u}
    A A₂ _ _ (algebraMap A A₂) _ _
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).functor
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).comparison
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).isLeftDerived

/-- The `A`-linear comparison underlying (L): the unit `K ⟶ (K ⊗ᴸ_A A₂)|_A` of the derived
change-of-rings adjunction, read through base-change cohomology and then identified with the
base-change cohomology taken over `A₂`. -/
def baseChangeCohomologyUnitNatTrans (n : ℤ) :
    baseChangeCohomologyFunctor (R := R) (A := A) (R' := R') n ⋙
        ModuleCat.restrictScalars.{u} (includeLeftRingHom R A R') ⟶
      baseChangeCohomologyExtendFunctor (R := R) (A := A) (A₂ := A₂) (R' := R') n ⋙
        ModuleCat.restrictScalars.{u} (algebraMap A A₂) :=
  Functor.whiskerRight (derivedExtendRestrictAdjunction (A := A) (A₂ := A₂)).unit
      (baseChangeCohomologyFunctor (R := R) (A := A) (R' := R') n ⋙
        ModuleCat.restrictScalars.{u} (includeLeftRingHom R A R')) ≫
    Functor.whiskerLeft (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).functor
      (baseChangeCohomologyRestrictNatTrans (R := R) (A := A) (A₂ := A₂) (R' := R') n)

/-- **The comparison of (L).** The `A₂`-linear map
`A₂ ⊗_A H^n(K|_R ⊗ᴸ_R R') ⟶ H^n(((K ⊗ᴸ_A A₂)|_R) ⊗ᴸ_R R')`, natural in `K`, obtained from
`RingTheory.TorIndependence.baseChangeCohomologyUnitNatTrans` by the adjunction between
extension and restriction of scalars along `A → A₂`. -/
def localizedBaseChangeCohomologyComparison (n : ℤ) :
    localizedBaseChangeCohomologyFunctor (R := R) (A := A) (A₂ := A₂) (R' := R') n ⟶
      baseChangeCohomologyExtendFunctor (R := R) (A := A) (A₂ := A₂) (R' := R') n :=
  Functor.whiskerRight (baseChangeCohomologyUnitNatTrans (R := R) (A := A) (A₂ := A₂) (R' := R') n)
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A A₂)) ≫
    Functor.whiskerLeft
      (baseChangeCohomologyExtendFunctor (R := R) (A := A) (A₂ := A₂) (R' := R') n)
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap A A₂)).counit

/-! ### The hypotheses of the dévissage -/

omit [Algebra R A₂] [IsScalarTower R A A₂] [HasDerivedCategory.{u} (ModuleCat.{u} A₂)] in
/-- If `A → A₂` is flat, then `K ↦ A₂ ⊗_A H^n(K|_R ⊗ᴸ_R R')` is a homological functor. -/
theorem isHomological_localizedBaseChangeCohomologyFunctor
    (hflat : (algebraMap A A₂).Flat) (n : ℤ) :
    (localizedBaseChangeCohomologyFunctor (R := R) (A := A) (A₂ := A₂) (R' := R')
      n).IsHomological := by
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  have := isHomological_baseChangeCohomologyFunctor (R := R) (A := A) (R' := R') n
  exact isHomological_comp_of_exact (baseChangeCohomologyFunctor (R := R) (A := A) (R' := R') n)
    (ModuleCat.restrictScalars.{u} (includeLeftRingHom R A R') ⋙
      ModuleCat.extendScalars.{u, u, u} (algebraMap A A₂))

omit [Algebra R A] [IsScalarTower R A A₂] in
/-- The functor `K ↦ H^n(((K ⊗ᴸ_A A₂)|_R) ⊗ᴸ_R R')` is homological. -/
theorem isHomological_baseChangeCohomologyExtendFunctor (n : ℤ) :
    (baseChangeCohomologyExtendFunctor (R := R) (A := A) (A₂ := A₂) (R' := R')
      n).IsHomological := by
  let := (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).commShift
  let := (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).isTriangulated
  have := isHomological_baseChangeCohomologyFunctor (R := R) (A := A₂) (R' := R') n
  have : (baseChangeCohomologyFunctor (R := R) (A := A₂) (R' := R') n ⋙
      ModuleCat.restrictScalars.{u} (includeLeftRingHom R A₂ R')).IsHomological :=
    isHomological_comp_of_exact _ _
  exact inferInstanceAs
    (((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).functor ⋙
      baseChangeCohomologyFunctor (R := R) (A := A₂) (R' := R') n ⋙
        ModuleCat.restrictScalars.{u} (includeLeftRingHom R A₂ R')).IsHomological)

/-- Restriction of scalars along a ring homomorphism preserves coproducts. -/
private theorem preservesColimitsOfShape_restrictScalars_discrete {S T : Type u} [Ring S]
    [Ring T] (f : S →+* T) (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (ModuleCat.restrictScalars.{u} f) :=
  have : PreservesColimitsOfSize.{u, u} (ModuleCat.restrictScalars.{u} f) :=
    (ModuleCat.restrictCoextendScalarsAdj.{u, u, u} f).leftAdjoint_preservesColimits
  inferInstance

omit [Algebra R A₂] [IsScalarTower R A A₂] [HasDerivedCategory.{u} (ModuleCat.{u} A₂)] in
/-- The functor `K ↦ A₂ ⊗_A H^n(K|_R ⊗ᴸ_R R')` preserves coproducts indexed by `J`. -/
theorem preservesColimitsOfShape_localizedBaseChangeCohomologyFunctor (J : Type u) (n : ℤ) :
    PreservesColimitsOfShape (Discrete J)
      (localizedBaseChangeCohomologyFunctor (R := R) (A := A) (A₂ := A₂) (R' := R') n) := by
  let := preservesColimitsOfShape_baseChangeCohomologyFunctor (R := R) (A := A) (R' := R') J n
  let hext : PreservesColimitsOfSize.{u, u}
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A A₂)) :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (algebraMap A A₂)).leftAdjoint_preservesColimits
  let := preservesColimitsOfShape_restrictScalars_discrete (includeLeftRingHom R A R') J
  let : PreservesColimitsOfShape (Discrete J)
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A A₂)) :=
    hext.preservesColimitsOfShape
  exact inferInstanceAs (PreservesColimitsOfShape (Discrete J)
    (baseChangeCohomologyFunctor (R := R) (A := A) (R' := R') n ⋙
      ModuleCat.restrictScalars.{u} (includeLeftRingHom R A R') ⋙
        ModuleCat.extendScalars.{u, u, u} (algebraMap A A₂)))

omit [Algebra R A] [IsScalarTower R A A₂] in
/-- The functor `K ↦ H^n(((K ⊗ᴸ_A A₂)|_R) ⊗ᴸ_R R')` preserves coproducts indexed by `J`. -/
theorem preservesColimitsOfShape_baseChangeCohomologyExtendFunctor (J : Type u) (n : ℤ) :
    PreservesColimitsOfShape (Discrete J)
      (baseChangeCohomologyExtendFunctor (R := R) (A := A) (A₂ := A₂) (R' := R') n) := by
  let := preservesColimitsOfShape_baseChangeCohomologyFunctor (R := R) (A := A₂) (R' := R') J n
  let hder : PreservesColimitsOfSize.{u, u}
      (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).functor :=
    preservesColimits_totalDerivedExtensionScalars (algebraMap A A₂)
  let : PreservesColimitsOfShape (Discrete J)
      (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).functor :=
    hder.preservesColimitsOfShape
  let := preservesColimitsOfShape_restrictScalars_discrete (includeLeftRingHom R A₂ R') J
  exact inferInstanceAs (PreservesColimitsOfShape (Discrete J)
    ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).functor ⋙
      baseChangeCohomologyFunctor (R := R) (A := A₂) (R' := R') n ⋙
        ModuleCat.restrictScalars.{u} (includeLeftRingHom R A₂ R')))

/-- **The two readings of a module in degree `d` over the two algebras.** For `N` an
`A₂`-module, the derived base change of `N|_A` placed in degree `d` is the derived base change of
`N` placed in degree `d`. -/
def singleDegreeBaseChangeIso (d : ℤ) :
    ModuleCat.restrictScalars.{u} (algebraMap A A₂) ⋙
        DerivedCategory.singleFunctor (ModuleCat.{u} A) d ⋙
          derivedBaseChangeFunctor (R := R) (A := A) (R' := R') ≅
      DerivedCategory.singleFunctor (ModuleCat.{u} A₂) d ⋙
        derivedBaseChangeFunctor (R := R) (A := A₂) (R' := R') :=
  Functor.isoWhiskerRight (singleRestrictDerivedIso (algebraMap A A₂) d)
      (derivedBaseChangeFunctor (R := R) (A := A) (R' := R')) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.singleFunctor (ModuleCat.{u} A₂) d)
      (derivedBaseChangeRestrictIso (R := R) (A := A) (A₂ := A₂) (R' := R'))

/-- The component of `singleDegreeBaseChangeIso` at an `A₂`-module `N` is the base change of the
identification of `N|_A` in degree `d` with the restriction of `N` in degree `d`, followed by
`derivedBaseChangeRestrictIso`. -/
theorem singleDegreeBaseChangeIso_hom_app (d : ℤ) (N : ModuleCat.{u} A₂) :
    (singleDegreeBaseChangeIso (R := R) (A := A) (A₂ := A₂) (R' := R') d).hom.app N =
      (derivedBaseChangeFunctor (R := R) (A := A) (R' := R')).map
          ((singleRestrictDerivedIso (algebraMap A A₂) d).hom.app N) ≫
        (derivedBaseChangeRestrictIso (R := R) (A := A) (A₂ := A₂) (R' := R')).hom.app
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A₂) d).obj N) :=
  rfl

/-- **The unit of the derived change-of-rings adjunction at the regular module in degree `d`,
read on derived base changes.** It is the derived base change of the structure map `A → A₂`,
placed in degree `d`. -/
theorem derivedBaseChange_unit_single_regular (d : ℤ) :
    (derivedBaseChangeFunctor (R := R) (A := A) (R' := R')).map
          ((derivedExtendRestrictAdjunction (A := A) (A₂ := A₂)).unit.app
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) d).obj (ModuleCat.of A A))) ≫
        (derivedBaseChangeRestrictIso (R := R) (A := A) (A₂ := A₂) (R' := R')).hom.app
            ((totalDerivedExtensionScalars.{u, u, u, u, u} (algebraMap A A₂)).functor.obj
              ((DerivedCategory.singleFunctor (ModuleCat.{u} A) d).obj (ModuleCat.of A A))) ≫
          (derivedBaseChangeFunctor (R := R) (A := A₂) (R' := R')).map
            (singleRegularExtendIso (A := A) (A₂ := A₂) d).hom =
      (derivedBaseChangeFunctor (R := R) (A := A) (R' := R')).map
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) d).map
            (ModuleCat.structureHom (algebraMap A A₂))) ≫
        (singleDegreeBaseChangeIso (R := R) (A := A) (A₂ := A₂) (R' := R') d).hom.app
          (ModuleCat.of A₂ A₂) := by
  have hB := @derivedExtensionScalarsAdjunction_unit_app.{u, u, u, u, u}
    A A₂ _ _ (algebraMap A A₂) _ _
    (totalDerivedExtensionScalars.{u, u, u, u, u} (algebraMap A A₂)).functor
    (totalDerivedExtensionScalars.{u, u, u, u, u} (algebraMap A A₂)).comparison
    (totalDerivedExtensionScalars.{u, u, u, u, u} (algebraMap A A₂)).isLeftDerived
  have hinner : (DerivedCategory.singleFunctor (ModuleCat.{u} A) d).map
          (ModuleCat.structureHom (algebraMap A A₂)) ≫
        (singleRestrictDerivedIso (algebraMap A A₂) d).hom.app (ModuleCat.of A₂ A₂) =
      (derivedExtendRestrictAdjunction (A := A) (A₂ := A₂)).unit.app
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) d).obj (ModuleCat.of A A)) ≫
        (ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory.map
          (singleRegularExtendIso (A := A) (A₂ := A₂) d).hom := by
    have hkey := unit_app_single_eq (algebraMap A A₂)
      (totalDerivedExtensionScalars.{u, u, u, u, u} (algebraMap A A₂)).functor
      (totalDerivedExtensionScalars.{u, u, u, u, u} (algebraMap A A₂)).comparison d
      (ModuleCat.of A A) (derivedExtendRestrictAdjunction (A := A) (A₂ := A₂)) hB
      (isIso_comparison_single_regular (A := A) (A₂ := A₂) d)
    have hnatsrd := (singleRestrictDerivedIso (algebraMap A A₂) d).hom.naturality
      (ModuleCat.extendScalarsTranspose (algebraMap A A₂)
        (ModuleCat.structureHom (algebraMap A A₂)))
    dsimp only [Functor.comp_map, Functor.comp_obj] at hnatsrd
    rw [← ModuleCat.unit_comp_restrictScalars_map_extendScalarsTranspose (algebraMap A A₂)
      (ModuleCat.structureHom (algebraMap A A₂)), CategoryTheory.Functor.map_comp,
      Category.assoc, hnatsrd, ← Category.assoc, ← hkey, singleRegularExtendIso_hom,
      CategoryTheory.Functor.map_comp]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [singleDegreeBaseChangeIso_hom_app]
  conv_rhs => rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hinner,
    CategoryTheory.Functor.map_comp, Category.assoc]
  congr 1
  have hnat := (derivedBaseChangeRestrictIso (R := R) (A := A) (A₂ := A₂) (R' := R')).hom.naturality
    (singleRegularExtendIso (A := A) (A₂ := A₂) d).hom
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnat
  exact hnat.symm

/-! ### The comparison at an object is a transpose -/

/-- **The comparison of (L) at an object is a transpose.** It is the transpose, under extension
and restriction of scalars along `A → A₂`, of the `A`-linear map
`RingTheory.TorIndependence.baseChangeCohomologyUnitNatTrans`. -/
theorem localizedBaseChangeCohomologyComparison_app_eq_transpose (n : ℤ)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (localizedBaseChangeCohomologyComparison (R := R) (A := A) (A₂ := A₂) (R' := R') n).app K =
      ModuleCat.extendScalarsTranspose (algebraMap A A₂)
        ((baseChangeCohomologyUnitNatTrans (R := R) (A := A) (A₂ := A₂) (R' := R') n).app K) :=
  rfl

/-! ### (L) is equivariant for the right tensor factor -/

/-- **The `A`-linear map underlying (L) is `R'`-equivariant.** The action of the right tensor
factor `R'` of `A ⊗_R R'` on the source is carried to the action of the right tensor factor `R'`
of `A₂ ⊗_R R'` on the target. -/
theorem baseChangeCohomologyUnitNatTrans_app_includeRight_smul (n : ℤ)
    (K : DerivedCategory (ModuleCat.{u} A)) (r : R')
    (m : baseChangeCohomology (R := R) (R' := R') K n) :
    ((baseChangeCohomologyUnitNatTrans (R := R) (A := A) (A₂ := A₂) (R' := R') n).app K).hom
        (show (ModuleCat.restrictScalars.{u} (includeLeftRingHom R A R')).obj
            (baseChangeCohomology (R := R) (R' := R') K n) from
          (Algebra.TensorProduct.includeRight r : A ⊗[R] R') • m) =
      (Algebra.TensorProduct.includeRight r : A₂ ⊗[R] R') •
        (show baseChangeCohomology (R := R) (R' := R')
            ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).functor.obj K) n from
          ((baseChangeCohomologyUnitNatTrans (R := R) (A := A) (A₂ := A₂) (R' := R') n).app
              K).hom
            (show (ModuleCat.restrictScalars.{u} (includeLeftRingHom R A R')).obj
              (baseChangeCohomology (R := R) (R' := R') K n) from m)) := by
  set L := (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).functor.obj K with hL
  set v := baseChangeCohomologyMap (R := R) (R' := R') n
    ((derivedExtendRestrictAdjunction (A := A) (A₂ := A₂)).unit.app K) with hv
  have hcomp : ∀ z : baseChangeCohomology (R := R) (R' := R') K n,
      ((baseChangeCohomologyUnitNatTrans (R := R) (A := A) (A₂ := A₂) (R' := R') n).app K).hom
          (show (ModuleCat.restrictScalars.{u} (includeLeftRingHom R A R')).obj
            (baseChangeCohomology (R := R) (R' := R') K n) from z) =
        (baseChangeCohomologyRestrictMap (R := R) (A := A) (A₂ := A₂) (R' := R') n L).hom
          (show baseChangeCohomologyOverBase (R := R) (R' := R')
            ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory.obj L) n from
            v.hom z) := fun _ => rfl
  rw [hcomp, hcomp, v.hom.map_smul (Algebra.TensorProduct.includeRight r : A ⊗[R] R') m]
  exact baseChangeCohomologyRestrictMap_includeRight_smul (R := R) (A := A) (A₂ := A₂)
    (R' := R') n L r (v.hom m)

/-- **(L) is equivariant for the right tensor factor.** On the generators `x • (1 ⊗ m)` of its
source, the comparison of (L) carries the action of `R'` through `A ⊗_R R'` to the action of `R'`
through `A₂ ⊗_R R'`. -/
theorem localizedBaseChangeCohomologyComparison_app_includeRight_smul (n : ℤ)
    (K : DerivedCategory (ModuleCat.{u} A)) (x : A₂) (r : R')
    (m : baseChangeCohomology (R := R) (R' := R') K n) :
    ((localizedBaseChangeCohomologyComparison (R := R) (A := A) (A₂ := A₂) (R' := R')
            n).app K).hom
        (x • (show (ModuleCat.extendScalars.{u, u, u} (algebraMap A A₂)).obj
            ((ModuleCat.restrictScalars.{u} (includeLeftRingHom R A R')).obj
              (baseChangeCohomology (R := R) (R' := R') K n)) from
          (1 : A₂) ⊗ₜ[A, algebraMap A A₂]
            (show (ModuleCat.restrictScalars.{u} (includeLeftRingHom R A R')).obj
              (baseChangeCohomology (R := R) (R' := R') K n) from
              (Algebra.TensorProduct.includeRight r : A ⊗[R] R') • m))) =
      (Algebra.TensorProduct.includeRight r : A₂ ⊗[R] R') •
        (show baseChangeCohomology (R := R) (R' := R')
            ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).functor.obj K) n from
          ((localizedBaseChangeCohomologyComparison (R := R) (A := A) (A₂ := A₂) (R' := R')
                n).app K).hom
            (x • (show (ModuleCat.extendScalars.{u, u, u} (algebraMap A A₂)).obj
                ((ModuleCat.restrictScalars.{u} (includeLeftRingHom R A R')).obj
                  (baseChangeCohomology (R := R) (R' := R') K n)) from
              (1 : A₂) ⊗ₜ[A, algebraMap A A₂]
                (show (ModuleCat.restrictScalars.{u} (includeLeftRingHom R A R')).obj
                  (baseChangeCohomology (R := R) (R' := R') K n) from m)))) := by
  have hgen : ∀ z : (ModuleCat.restrictScalars.{u} (includeLeftRingHom R A R')).obj
        (baseChangeCohomology (R := R) (R' := R') K n),
      ((localizedBaseChangeCohomologyComparison (R := R) (A := A) (A₂ := A₂) (R' := R')
              n).app K).hom
          (x • (show (ModuleCat.extendScalars.{u, u, u} (algebraMap A A₂)).obj
              ((ModuleCat.restrictScalars.{u} (includeLeftRingHom R A R')).obj
                (baseChangeCohomology (R := R) (R' := R') K n)) from
            (1 : A₂) ⊗ₜ[A, algebraMap A A₂] z)) =
        (Algebra.TensorProduct.includeLeft (R := R) (S := R) x : A₂ ⊗[R] R') •
          (show baseChangeCohomology (R := R) (R' := R')
              ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).functor.obj K) n from
            ((baseChangeCohomologyUnitNatTrans (R := R) (A := A) (A₂ := A₂) (R' := R')
                n).app K).hom z) := by
    intro z
    exact ModuleCat.extendScalarsTranspose_smul_one_tmul (algebraMap A A₂)
      ((baseChangeCohomologyUnitNatTrans (R := R) (A := A) (A₂ := A₂) (R' := R') n).app K) x z
  rw [hgen, hgen, baseChangeCohomologyUnitNatTrans_app_includeRight_smul, smul_smul, smul_smul,
    mul_comm]

/-! ### Above the degree of the module -/

omit [Algebra R A₂] [IsScalarTower R A A₂] [HasDerivedCategory.{u} (ModuleCat.{u} A₂)] in
/-- **Above the degree of the module the left-hand side of (L) vanishes.** -/
theorem isZero_localizedBaseChangeCohomologyFunctor_single (d n : ℤ) (hdn : d < n) :
    IsZero ((localizedBaseChangeCohomologyFunctor (R := R) (A := A) (A₂ := A₂) (R' := R') n).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) d).obj (ModuleCat.of A A))) := by
  show IsZero ((ModuleCat.extendScalars.{u, u, u} (algebraMap A A₂)).obj
    ((ModuleCat.restrictScalars.{u} (includeLeftRingHom R A R')).obj
      (baseChangeCohomology (R := R) (R' := R')
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) d).obj (ModuleCat.of A A)) n)))
  refine CategoryTheory.Functor.map_isZero _ (CategoryTheory.Functor.map_isZero _ ?_)
  rw [ModuleCat.isZero_iff_subsingleton]
  have h0 := isZero_baseChangeCohomologyOverBase_single_of_lt (R := R) (A := A) (R' := R') d n hdn
    (ModuleCat.of A A)
  rw [ModuleCat.isZero_iff_subsingleton] at h0
  exact h0

omit [Algebra R A] [IsScalarTower R A A₂] in
/-- **Above the degree of the module the right-hand side of (L) vanishes.** -/
theorem isZero_baseChangeCohomologyExtendFunctor_single (d n : ℤ) (hdn : d < n) :
    IsZero ((baseChangeCohomologyExtendFunctor (R := R) (A := A) (A₂ := A₂) (R' := R') n).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) d).obj (ModuleCat.of A A))) := by
  show IsZero ((ModuleCat.restrictScalars.{u} (includeLeftRingHom R A₂ R')).obj
    (baseChangeCohomology (R := R) (R' := R')
      ((totalDerivedExtensionScalars.{u, u, u, u, u} (algebraMap A A₂)).functor.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) d).obj (ModuleCat.of A A))) n))
  refine CategoryTheory.Functor.map_isZero _ ?_
  rw [ModuleCat.isZero_iff_subsingleton]
  have h0 : IsZero (baseChangeCohomologyOverBase (R := R) (R' := R')
      ((totalDerivedExtensionScalars.{u, u, u, u, u} (algebraMap A A₂)).functor.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) d).obj (ModuleCat.of A A))) n) := by
    refine IsZero.of_iso (isZero_baseChangeCohomologyOverBase_single_of_lt
      (R := R) (A := A₂) (R' := R') d n hdn (ModuleCat.of A₂ A₂)) ?_
    exact (derivedBaseChangeFunctor (R := R) (A := A₂) (R' := R') ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).mapIso
        (singleRegularExtendIso (A := A) (A₂ := A₂) d)
  rw [ModuleCat.isZero_iff_subsingleton] at h0
  exact h0

/-- **The comparison of (L) is invertible at the regular module in a degree below `n`**, both
sides being zero there. -/
theorem isIso_localizedBaseChangeCohomologyComparison_app_single_of_lt (d n : ℤ) (hdn : d < n) :
    IsIso ((localizedBaseChangeCohomologyComparison (R := R) (A := A) (A₂ := A₂) (R' := R')
      n).app ((DerivedCategory.singleFunctor (ModuleCat.{u} A) d).obj (ModuleCat.of A A))) := by
  have hX := isZero_localizedBaseChangeCohomologyFunctor_single
    (R := R) (A := A) (A₂ := A₂) (R' := R') d n hdn
  have hY := isZero_baseChangeCohomologyExtendFunctor_single
    (R := R) (A := A) (A₂ := A₂) (R' := R') d n hdn
  exact ⟨hY.to_ _, hX.eq_of_src _ _, hY.eq_of_src _ _⟩

/-! ### The two sides at the regular module, identified with `Tor` -/

/-- The tower identification `(A₂|_A)|_R ≅ A₂|_R`, landing on `A₂` as an `R`-module. -/
def towerBaseIso :
    (ModuleCat.restrictScalars.{u, u, u} (algebraMap R A)).obj
        ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).obj (ModuleCat.of A₂ A₂)) ≅
      ModuleCat.of R A₂ :=
  (ModuleCat.restrictScalarsComp'App (algebraMap R A) (algebraMap A A₂) (algebraMap R A₂)
      (IsScalarTower.algebraMap_eq R A A₂) (ModuleCat.of A₂ A₂)).symm ≪≫
    baseModuleIso (R := R) (R' := A₂)

omit [HasDerivedCategory.{u} (ModuleCat.{u} R)] [HasDerivedCategory.{u} (ModuleCat.{u} A)]
  [HasDerivedCategory.{u} (ModuleCat.{u} A₂)] in
/-- The structure map `A → A₂`, read over `R` through the two identifications. -/
theorem structureHom_comp_towerBaseIso :
    (ModuleCat.restrictScalars.{u, u, u} (algebraMap R A)).map
          (ModuleCat.structureHom (algebraMap A A₂)) ≫
        (towerBaseIso (R := R) (A := A) (A₂ := A₂)).hom =
      (baseModuleIso (R := R) (R' := A)).hom ≫
        ModuleCat.ofHom (IsScalarTower.toAlgHom R A A₂).toLinearMap := by
  ext a
  rfl

omit [HasDerivedCategory.{u} (ModuleCat.{u} R)] [HasDerivedCategory.{u} (ModuleCat.{u} A)] in
/-- Multiplication by `a` on `A`, read over `R`. -/
theorem smul_comp_baseModuleIso (a : A) :
    (ModuleCat.restrictScalars.{u, u, u} (algebraMap R A)).map (a • 𝟙 (ModuleCat.of A A)) ≫
        (baseModuleIso (R := R) (R' := A)).hom =
      (baseModuleIso (R := R) (R' := A)).hom ≫
        ModuleCat.ofHom (TorChangeOfRings.mulLinear R A a) := by
  ext x
  rfl

omit [HasDerivedCategory.{u} (ModuleCat.{u} R)] [HasDerivedCategory.{u} (ModuleCat.{u} A)]
  [HasDerivedCategory.{u} (ModuleCat.{u} A₂)] in
/-- Multiplication by `a₂` on `A₂`, read over `R` through the tower. -/
theorem smul_comp_towerBaseIso (a₂ : A₂) :
    (ModuleCat.restrictScalars.{u, u, u} (algebraMap R A)).map
          ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).map
            (a₂ • 𝟙 (ModuleCat.of A₂ A₂))) ≫
        (towerBaseIso (R := R) (A := A) (A₂ := A₂)).hom =
      (towerBaseIso (R := R) (A := A) (A₂ := A₂)).hom ≫
        ModuleCat.ofHom (TorChangeOfRings.mulLinear R A₂ a₂) := by
  ext x
  rfl

/-- **The left-hand side of (L) at the regular module in degree `d` is `A₂ ⊗_A Tor`.** This is
the `A`-linear identification of its source with `Tor_i^R(R', A)`. -/
def generatorSourceHom (d n : ℤ) (i : ℕ) (h : n + (i : ℤ) = d) :
    (ModuleCat.restrictScalars.{u} (includeLeftRingHom R A R')).obj
        (baseChangeCohomology (R := R) (R' := R')
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) d).obj (ModuleCat.of A A)) n) ⟶
      torModule R A R' i :=
  ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars.{u} (includeLeftRingHom R A R')).obj
      (baseChangeCohomology (R := R) (R' := R')
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) d).obj (ModuleCat.of A A)) n))
    (Y := torModule R A R' i)
    { toFun := fun x =>
        (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
            (baseModuleIso (R := R) (R' := A)).hom).hom
          (((baseChangeCohomologySingleDegreeIsoTor (R := R) (A := A) (R' := R') d n i h).hom.app
            (ModuleCat.of A A)).hom x)
      map_add' := fun x y =>
        (congrArg (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
              (baseModuleIso (R := R) (R' := A)).hom).hom
            (_root_.map_add (((baseChangeCohomologySingleDegreeIsoTor (R := R) (A := A) (R' := R')
              d n i h).hom.app (ModuleCat.of A A)).hom) x y)).trans
          (_root_.map_add (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
            (baseModuleIso (R := R) (R' := A)).hom).hom _ _)
      map_smul' := fun a x => by
        have h1 := baseChangeCohomologySingleDegreeIsoTor_includeLeft_smul
          (R := R) (A := A) (R' := R') d n i h (ModuleCat.of A A) a x
        have h3 : ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
                ((ModuleCat.restrictScalars.{u, u, u} (algebraMap R A)).map
                  (a • 𝟙 (ModuleCat.of A A))) ≫
              ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
                (baseModuleIso (R := R) (R' := A)).hom =
            ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
                (baseModuleIso (R := R) (R' := A)).hom ≫
              ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
                (ModuleCat.ofHom (TorChangeOfRings.mulLinear R A a)) := by
          rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
            smul_comp_baseModuleIso]
        have h2 := torModule_smul R A R' i a
          ((((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
              (baseModuleIso (R := R) (R' := A)).hom).hom
            (((baseChangeCohomologySingleDegreeIsoTor (R := R) (A := A) (R' := R') d n i
              h).hom.app (ModuleCat.of A A)).hom x))
        exact ((congrArg _ h1).trans (congrArg (fun φ => ModuleCat.Hom.hom φ
          (((baseChangeCohomologySingleDegreeIsoTor (R := R) (A := A) (R' := R') d n i h).hom.app
            (ModuleCat.of A A)).hom x)) h3)).trans h2.symm }

/-- The identification `generatorSourceHom` of the base-change cohomology of the regular
`A`-module in degree `d` with `Tor_i^R(R', A)` is an isomorphism. -/
instance isIso_generatorSourceHom (d n : ℤ) (i : ℕ) (h : n + (i : ℤ) = d) :
    IsIso (generatorSourceHom (R := R) (A := A) (R' := R') d n i h) := by
  have b1 : Function.Bijective
      (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
        (baseModuleIso (R := R) (R' := A)).hom).hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have b2 : Function.Bijective
      ((baseChangeCohomologySingleDegreeIsoTor (R := R) (A := A) (R' := R') d n i h).hom.app
        (ModuleCat.of A A)).hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  exact (ConcreteCategory.isIso_iff_bijective _).mpr (b1.comp b2)

/-- The second half of the identification of the right-hand side of (L) at the regular module in
degree `d`: from the base-change cohomology of the regular `A₂`-module in degree `d` to
`Tor_i^R(R', A₂)`, as `A₂`-modules. -/
def generatorTargetHom₀ (d n : ℤ) (i : ℕ) (h : n + (i : ℤ) = d) :
    (ModuleCat.restrictScalars.{u} (includeLeftRingHom R A₂ R')).obj
        (baseChangeCohomology (R := R) (R' := R')
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A₂) d).obj (ModuleCat.of A₂ A₂)) n) ⟶
      torModule R A₂ R' i :=
  ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars.{u} (includeLeftRingHom R A₂ R')).obj
      (baseChangeCohomology (R := R) (R' := R')
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A₂) d).obj (ModuleCat.of A₂ A₂)) n))
    (Y := torModule R A₂ R' i)
    { toFun := fun y =>
        (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
            (towerBaseIso (R := R) (A := A) (A₂ := A₂)).hom).hom
          (((baseChangeCohomologySingleDegreeIsoTor (R := R) (A := A) (R' := R') d n i h).hom.app
              ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).obj (ModuleCat.of A₂ A₂))).hom
            (((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
              ((singleDegreeBaseChangeIso (R := R) (A := A) (A₂ := A₂) (R' := R') d).inv.app
                (ModuleCat.of A₂ A₂))).hom y))
      map_add' := fun x y =>
        (congrArg (fun z => (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
              (towerBaseIso (R := R) (A := A) (A₂ := A₂)).hom).hom
            (((baseChangeCohomologySingleDegreeIsoTor (R := R) (A := A) (R' := R') d n i
                h).hom.app
              ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).obj
                (ModuleCat.of A₂ A₂))).hom z))
            (_root_.map_add (((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
              ((singleDegreeBaseChangeIso (R := R) (A := A) (A₂ := A₂) (R' := R') d).inv.app
                (ModuleCat.of A₂ A₂))).hom) x y)).trans
          ((congrArg (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
                (towerBaseIso (R := R) (A := A) (A₂ := A₂)).hom).hom
              (_root_.map_add (((baseChangeCohomologySingleDegreeIsoTor (R := R) (A := A) (R' := R')
                d n i h).hom.app ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).obj
                  (ModuleCat.of A₂ A₂))).hom) _ _)).trans
            (_root_.map_add (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
              (towerBaseIso (R := R) (A := A) (A₂ := A₂)).hom).hom _ _))
      map_smul' := fun a₂ y => by
        have hs : (DerivedCategory.singleFunctor (ModuleCat.{u} A₂) d).map
              (a₂ • 𝟙 (ModuleCat.of A₂ A₂)) =
            a₂ • 𝟙 ((DerivedCategory.singleFunctor (ModuleCat.{u} A₂) d).obj
              (ModuleCat.of A₂ A₂)) := by
          rw [Functor.map_smul, CategoryTheory.Functor.map_id]
        have h1 := baseChangeCohomology_includeLeft_smul (R := R) (R' := R')
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A₂) d).obj (ModuleCat.of A₂ A₂)) n a₂ y
        have hnatL := (singleDegreeBaseChangeIso (R := R) (A := A) (A₂ := A₂)
          (R' := R') d).inv.naturality (a₂ • 𝟙 (ModuleCat.of A₂ A₂))
        dsimp only [Functor.comp_map, Functor.comp_obj] at hnatL
        rw [hs] at hnatL
        have hL := congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map hnatL
        rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at hL
        have hnatB := (baseChangeCohomologySingleDegreeIsoTor
          (R := R) (A := A) (R' := R') d n i h).hom.naturality
            ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).map
              (a₂ • 𝟙 (ModuleCat.of A₂ A₂)))
        dsimp only [Functor.comp_map, Functor.comp_obj] at hnatB
        have h3 : ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
                ((ModuleCat.restrictScalars.{u, u, u} (algebraMap R A)).map
                  ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).map
                    (a₂ • 𝟙 (ModuleCat.of A₂ A₂)))) ≫
              ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
                (towerBaseIso (R := R) (A := A) (A₂ := A₂)).hom =
            ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
                (towerBaseIso (R := R) (A := A) (A₂ := A₂)).hom ≫
              ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
                (ModuleCat.ofHom (TorChangeOfRings.mulLinear R A₂ a₂)) := by
          rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
            smul_comp_towerBaseIso]
        have f1 := DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hL) y
        have f2 := DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hnatB)
          (((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
            ((singleDegreeBaseChangeIso (R := R) (A := A) (A₂ := A₂) (R' := R') d).inv.app
              (ModuleCat.of A₂ A₂))).hom y)
        have f3 := congrArg (fun φ => ModuleCat.Hom.hom φ
          (((baseChangeCohomologySingleDegreeIsoTor (R := R) (A := A) (R' := R') d n i h).hom.app
              ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).obj (ModuleCat.of A₂ A₂))).hom
            (((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
              ((singleDegreeBaseChangeIso (R := R) (A := A) (A₂ := A₂) (R' := R') d).inv.app
                (ModuleCat.of A₂ A₂))).hom y))) h3
        have f4 := torModule_smul R A₂ R' i a₂
          ((((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
              (towerBaseIso (R := R) (A := A) (A₂ := A₂)).hom).hom
            (((baseChangeCohomologySingleDegreeIsoTor (R := R) (A := A) (R' := R') d n i h).hom.app
                ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).obj (ModuleCat.of A₂ A₂))).hom
              (((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
                ((singleDegreeBaseChangeIso (R := R) (A := A) (A₂ := A₂) (R' := R') d).inv.app
                  (ModuleCat.of A₂ A₂))).hom y)))
        exact (congrArg (fun z => (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
              (towerBaseIso (R := R) (A := A) (A₂ := A₂)).hom).hom
            (((baseChangeCohomologySingleDegreeIsoTor (R := R) (A := A) (R' := R')
                d n i h).hom.app ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).obj
                  (ModuleCat.of A₂ A₂))).hom z))
            ((congrArg (((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
              ((singleDegreeBaseChangeIso (R := R) (A := A) (A₂ := A₂) (R' := R') d).inv.app
                (ModuleCat.of A₂ A₂))).hom) h1).trans f1)).trans
          (((congrArg (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
              (towerBaseIso (R := R) (A := A) (A₂ := A₂)).hom).hom f2).trans f3).trans f4.symm) }

/-- The identification `generatorTargetHom₀` of the base-change cohomology of the regular
`A₂`-module in degree `d` with `Tor_i^R(R', A₂)` is an isomorphism. -/
instance isIso_generatorTargetHom₀ (d n : ℤ) (i : ℕ) (h : n + (i : ℤ) = d) :
    IsIso (generatorTargetHom₀ (R := R) (A := A) (A₂ := A₂) (R' := R') d n i h) := by
  have b1 : Function.Bijective
      (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
        (towerBaseIso (R := R) (A := A) (A₂ := A₂)).hom).hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have b2 : Function.Bijective
      ((baseChangeCohomologySingleDegreeIsoTor (R := R) (A := A) (R' := R') d n i h).hom.app
        ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).obj (ModuleCat.of A₂ A₂))).hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have b3 : Function.Bijective
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
        ((singleDegreeBaseChangeIso (R := R) (A := A) (A₂ := A₂) (R' := R') d).inv.app
          (ModuleCat.of A₂ A₂))).hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  exact (ConcreteCategory.isIso_iff_bijective _).mpr (b1.comp (b2.comp b3))

/-- **The right-hand side of (L) at the regular module in degree `d` is `Tor_i^R(R', A₂)`**, as
`A₂`-modules. -/
def generatorTargetHom (d n : ℤ) (i : ℕ) (h : n + (i : ℤ) = d) :
    (ModuleCat.restrictScalars.{u} (includeLeftRingHom R A₂ R')).obj
        (baseChangeCohomology (R := R) (R' := R')
          ((totalDerivedExtensionScalars.{u, u, u, u, u} (algebraMap A A₂)).functor.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) d).obj (ModuleCat.of A A))) n) ⟶
      torModule R A₂ R' i :=
  (ModuleCat.restrictScalars.{u} (includeLeftRingHom R A₂ R')).map
      (baseChangeCohomologyMap (R := R) (A := A₂) (R' := R') n
        (singleRegularExtendIso (A := A) (A₂ := A₂) d).hom) ≫
    generatorTargetHom₀ (R := R) (A := A) (A₂ := A₂) (R' := R') d n i h

/-- The identification `generatorTargetHom` of the base-change cohomology of `A ⊗ᴸ_A A₂` in
degree `d` with `Tor_i^R(R', A₂)` is an isomorphism. -/
instance isIso_generatorTargetHom (d n : ℤ) (i : ℕ) (h : n + (i : ℤ) = d) :
    IsIso (generatorTargetHom (R := R) (A := A) (A₂ := A₂) (R' := R') d n i h) := by
  have hm : IsIso (baseChangeCohomologyMap (R := R) (A := A₂) (R' := R') n
      (singleRegularExtendIso (A := A) (A₂ := A₂) d).hom) :=
    inferInstanceAs (IsIso ((baseChangeCohomologyFunctor (R := R) (A := A₂) (R' := R') n).map
      (singleRegularExtendIso (A := A) (A₂ := A₂) d).hom))
  dsimp only [generatorTargetHom]
  infer_instance

/-! ### The generator case -/

/-- **The comparison of (L) at the regular module in degree `d` is the comparison of `Tor`.**
Under the two identifications of its source and target with `Tor`, the `A`-linear map underlying
the comparison is `Tor_i^R(R', ·)` applied to the structure map `A → A₂`. -/
theorem generator_square (d n : ℤ) (i : ℕ) (h : n + (i : ℤ) = d) :
    (baseChangeCohomologyUnitNatTrans (R := R) (A := A) (A₂ := A₂) (R' := R') n).app
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) d).obj (ModuleCat.of A A)) ≫
        (ModuleCat.restrictScalars.{u} (algebraMap A A₂)).map
          (generatorTargetHom (R := R) (A := A) (A₂ := A₂) (R' := R') d n i h) =
      generatorSourceHom (R := R) (A := A) (R' := R') d n i h ≫
        torModuleMap (R := R) (A := A) (A₂ := A₂) (R' := R') i := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  have hψ := congrArg (fun φ => φ ≫
      (singleDegreeBaseChangeIso (R := R) (A := A) (A₂ := A₂) (R' := R') d).inv.app
        (ModuleCat.of A₂ A₂))
    (derivedBaseChange_unit_single_regular (R := R) (A := A) (A₂ := A₂) (R' := R') d)
  simp only [Functor.comp_obj, Category.assoc, Iso.hom_inv_id_app, Category.comp_id] at hψ
  have hH := congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map hψ
  simp only [CategoryTheory.Functor.map_comp] at hH
  have hHx := ConcreteCategory.congr_hom hH x
  have hnatB := (baseChangeCohomologySingleDegreeIsoTor
    (R := R) (A := A) (R' := R') d n i h).hom.naturality
      (ModuleCat.structureHom (algebraMap A A₂))
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnatB
  have hnatBx := ConcreteCategory.congr_hom hnatB x
  have hsq := map_comp_eq_map_comp ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R'))
    (structureHom_comp_towerBaseIso (R := R) (A := A) (A₂ := A₂))
  have hsqx := ConcreteCategory.congr_hom hsq
    (((baseChangeCohomologySingleDegreeIsoTor (R := R) (A := A) (R' := R') d n i h).hom.app
      (ModuleCat.of A A)).hom x)
  exact ((congrArg (fun z => (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
            (towerBaseIso (R := R) (A := A) (A₂ := A₂)).hom).hom
          (((baseChangeCohomologySingleDegreeIsoTor (R := R) (A := A) (R' := R') d n i h).hom.app
            ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).obj
              (ModuleCat.of A₂ A₂))).hom z)) hHx).trans
      (congrArg (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
        (towerBaseIso (R := R) (A := A) (A₂ := A₂)).hom).hom hnatBx)).trans hsqx

/-- **The comparison of (L) is invertible at the regular module in every degree.** -/
theorem isIso_localizedBaseChangeCohomologyComparison_app_single
    (hflat : (algebraMap A A₂).Flat) (d n : ℤ) :
    IsIso ((localizedBaseChangeCohomologyComparison (R := R) (A := A) (A₂ := A₂) (R' := R')
      n).app ((DerivedCategory.singleFunctor (ModuleCat.{u} A) d).obj (ModuleCat.of A A))) := by
  rcases lt_or_ge d n with hdn | hdn
  · exact isIso_localizedBaseChangeCohomologyComparison_app_single_of_lt
      (R := R) (A := A) (A₂ := A₂) (R' := R') d n hdn
  · obtain ⟨i, hi⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hdn)
    have h : n + (i : ℤ) = d := by omega
    rw [localizedBaseChangeCohomologyComparison_app_eq_transpose]
    exact ModuleCat.isIso_extendScalarsTranspose_of_iso (algebraMap A A₂) _
      (torModuleMap (R := R) (A := A) (A₂ := A₂) (R' := R') i)
      (@asIso _ _ _ _ (generatorSourceHom (R := R) (A := A) (R' := R') d n i h)
        (isIso_generatorSourceHom (R := R) (A := A) (R' := R') d n i h))
      (@asIso _ _ _ _ (generatorTargetHom (R := R) (A := A) (A₂ := A₂) (R' := R') d n i h)
        (isIso_generatorTargetHom (R := R) (A := A) (A₂ := A₂) (R' := R') d n i h))
      (generator_square (R := R) (A := A) (A₂ := A₂) (R' := R') d n i h)
      (isIso_torModuleFlatBaseChange hflat i)

/-- **The generator case of (L).** The comparison of (L) is invertible at every shift of the
compact generator `A[0]` of `D(A)`. -/
theorem isIso_localizedBaseChangeCohomologyComparison_app_shift_regularModule
    (hflat : (algebraMap A A₂).Flat) (n m : ℤ) :
    IsIso ((localizedBaseChangeCohomologyComparison (R := R) (A := A) (A₂ := A₂) (R' := R')
        n).app
      (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))⟦m⟧)) :=
  (NatTrans.isIso_app_iff_of_iso
      (localizedBaseChangeCohomologyComparison (R := R) (A := A) (A₂ := A₂) (R' := R') n)
      (DerivedCategory.singleShiftIso (ModuleCat.of A A) m)).mpr
    (isIso_localizedBaseChangeCohomologyComparison_app_single hflat (-m) n)

/-! ### (L) -/

/-- **(L), the dévissage form.** Let `R → A` be a homomorphism of commutative rings, let
`A → A₂` be flat — a localization, for instance — and let `R → R'` be an arbitrary homomorphism
of commutative rings. Then the comparison

`A₂ ⊗_A H^n(K|_R ⊗ᴸ_R R')  ⟶  H^n(((K ⊗ᴸ_A A₂)|_R) ⊗ᴸ_R R')`

is an isomorphism for every `K` in `D(A)`, naturally in `K`. -/
theorem isIso_localizedBaseChangeCohomologyComparison
    (hflat : (algebraMap A A₂).Flat) (n : ℤ) :
    IsIso (localizedBaseChangeCohomologyComparison (R := R) (A := A) (A₂ := A₂) (R' := R') n) := by
  let := isHomological_localizedBaseChangeCohomologyFunctor (R := R) (A := A) (A₂ := A₂)
    (R' := R') hflat n
  let := isHomological_baseChangeCohomologyExtendFunctor (R := R) (A := A) (A₂ := A₂)
    (R' := R') n
  let : ∀ J : Type u, PreservesColimitsOfShape (Discrete J)
      (localizedBaseChangeCohomologyFunctor (R := R) (A := A) (A₂ := A₂) (R' := R') n) :=
    fun J => preservesColimitsOfShape_localizedBaseChangeCohomologyFunctor
      (R := R) (A := A) (A₂ := A₂) (R' := R') J n
  let : ∀ J : Type u, PreservesColimitsOfShape (Discrete J)
      (baseChangeCohomologyExtendFunctor (R := R) (A := A) (A₂ := A₂) (R' := R') n) :=
    fun J => preservesColimitsOfShape_baseChangeCohomologyExtendFunctor
      (R := R) (A := A) (A₂ := A₂) (R' := R') J n
  exact StacksDraft.HomologicalDevissage.isIso_of_isIso_app_shift_regularModule _
    (isIso_localizedBaseChangeCohomologyComparison_app_shift_regularModule
      (R := R) (A := A) (A₂ := A₂) (R' := R') hflat n)

/-- **(L) at an object.** `A₂ ⊗_A H^n(K|_R ⊗ᴸ_R R') ≅ H^n(((K ⊗ᴸ_A A₂)|_R) ⊗ᴸ_R R')` as
`A₂`-modules, for `A → A₂` flat. -/
def localizedBaseChangeCohomologyIso (hflat : (algebraMap A A₂).Flat) (n : ℤ)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap A A₂)).obj
        ((ModuleCat.restrictScalars.{u} (includeLeftRingHom R A R')).obj
          (baseChangeCohomology (R := R) (R' := R') K n)) ≅
      (ModuleCat.restrictScalars.{u} (includeLeftRingHom R A₂ R')).obj
        (baseChangeCohomology (R := R) (R' := R')
          ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).functor.obj K) n) :=
  letI := isIso_localizedBaseChangeCohomologyComparison (R := R) (A := A) (A₂ := A₂) (R' := R')
    hflat n
  (asIso (localizedBaseChangeCohomologyComparison (R := R) (A := A) (A₂ := A₂) (R' := R')
    n)).app K

end Main

end RingTheory.TorIndependence

end
