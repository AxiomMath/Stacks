module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksFrontier.Algebra.Homology.MapTotalComplex
public import StacksFrontier.Homology.DerivedCategory.Monoidal.Basic
public import StacksFrontier.Homology.HomComplex.DerivedAdjunction
public import StacksFrontier.Homology.KFlat.ScalarBaseChange
public import StacksFrontier.Homology.Tor.DerivedTensor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The canonical derived tensor product in an independent module universe

Let `A` be a commutative ring in a universe `u`. The derived tensor product of
`StacksFrontier.Homology.Tor.DerivedTensor` is built on the monoidal structure of `ModuleCat A`,
which forces the modules to live in the universe of `A` itself. This file removes that
restriction: the canonical derived tensor product of `ULift.{v} A`-modules is transported along
the equivalence `D(ModuleCat.{max u v} (ULift.{v} A)) ≌ D(ModuleCat.{max u v} A)` of
`StacksDraft.DerivedHom.derivedScalarEquivalence`, yielding a derived tensor product on
`D(ModuleCat.{max u v} A)` for a module universe `max u v` independent of `u`.

The transported bifunctor is packaged as a term of
`CochainComplex.DerivedTensor.DerivedTensorProductGeneral`, which records the comparison with
ordinary total tensor products of K-flat representatives together with exactness in each
variable; the transported monoidal structure is recorded separately, with isomorphisms
identifying its tensor bifunctor with that bifunctor and its unit with `A` in degree zero.

## Main definitions

* `CochainComplex.DerivedTensor.canonicalDerivedTensorFunctorGeneral`: the derived tensor
  bifunctor on `D(ModuleCat.{max u v} A)`.
* `CochainComplex.DerivedTensor.canonicalDerivedTensorProductGeneral`: that bifunctor together
  with its K-flat comparison and exactness, as a `DerivedTensorProductGeneral`.
* `CochainComplex.DerivedTensor.canonicalDerivedMonoidalStructure`: the transported monoidal
  structure on `D(ModuleCat.{max u v} A)`.
* `CochainComplex.DerivedTensor.canonicalDerivedMonoidalTensorIso` and
  `CochainComplex.DerivedTensor.canonicalDerivedMonoidalUnitIso`: its tensor bifunctor is the
  one above, and its unit is `A[0]`.
* `CochainComplex.DerivedTensor.derivedTensor_comparison`: the same K-flat comparison for the
  tensor bifunctor of `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`.
* `CochainComplex.DerivedTensor.mapBifunctorIso`: totalization of the bicomplex built from a
  pair of complexes respects a natural isomorphism of the bifunctors.

## Main results

* `CochainComplex.DerivedTensor.isKFlat_restrictScalars_of_ringEquiv`: K-flatness is preserved by
  restriction of scalars along a ring isomorphism, in the universe-independent sense.
* `CochainComplex.DerivedTensor.scalarEquivalenceTensorComplexIso`: the scalar equivalence
  carries the total tensor product of the restricted complexes to the total tensor product of
  the originals.

## Implementation notes

Restriction of scalars along a ring isomorphism is an equivalence, hence preserves coproducts,
so it commutes with totalization of a bicomplex by
`HomologicalComplex₂.TotalMap.totalIso`. That is the only input needed to compare the total
tensor product formed over `A` with the one formed over `ULift.{v} A`.

The monoidal structure is obtained by `CategoryTheory.Monoidal.transport`, so it is a datum
rather than an instance; every statement mentioning it binds it explicitly.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CochainComplex.DerivedTensor

/-- Uncurrying the currying of a bifunctor does not change its action on morphisms. -/
public theorem uncurry_curry_map
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C × D ⥤ E) {X Y : C × D} (f : X ⟶ Y) :
    (Functor.uncurry.obj (Functor.curry.obj F)).map f = F.map f := by
  show F.map (CategoryTheory.Prod.mkHom f.1 (𝟙 X.2)) ≫
    F.map (CategoryTheory.Prod.mkHom (𝟙 Y.1) f.2) = F.map f
  rw [← F.map_comp]
  congr 1
  ext <;> simp

/-- Two commuting squares sharing an edge glue to a commuting rectangle. Stated over an
abstract category so that it applies by `exact` at default transparency, where a `rw` through
`Category.assoc` cannot see that the two spellings of the shared object agree. -/
public theorem glue_comp_squares {C : Type*} [Category C] {X Y Z V W U : C}
    {p : X ⟶ Y} {q : Y ⟶ Z} {r : Z ⟶ V}
    {q' : X ⟶ W} {m : W ⟶ Z} {r' : W ⟶ U} {s : U ⟶ V}
    (h₁ : p ≫ q = q' ≫ m) (h₂ : m ≫ r = r' ≫ s) :
    p ≫ q ≫ r = (q' ≫ r') ≫ s := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

/-- `CochainComplex.DerivedTensor.glue_comp_squares` with the resulting rectangle
re-associated to the right. -/
public theorem glue_comp_squares_assoc {C : Type*} [Category C] {X Y Z V W U : C}
    {p : X ⟶ Y} {q : Y ⟶ Z} {r : Z ⟶ V}
    {q' : X ⟶ W} {m : W ⟶ Z} {r' : W ⟶ U} {s : U ⟶ V}
    (h₁ : p ≫ q = q' ≫ m) (h₂ : m ≫ r = r' ≫ s) :
    p ≫ q ≫ r = q' ≫ r' ≫ s :=
  (glue_comp_squares h₁ h₂).trans (Category.assoc _ _ _)

/-- Four commuting squares paste to a commuting square.  Stated over an arbitrary category so
that it applies by unification alone. -/
public theorem comp_square_four {C : Type*} [Category C]
    {A₀ A₁ A₂ A₃ A₄ B₀ B₁ B₂ B₃ B₄ : C}
    {m₀ : A₀ ⟶ B₀} {m₁ : A₁ ⟶ B₁} {m₂ : A₂ ⟶ B₂} {m₃ : A₃ ⟶ B₃} {m₄ : A₄ ⟶ B₄}
    {a₁ : A₀ ⟶ A₁} {a₂ : A₁ ⟶ A₂} {a₃ : A₂ ⟶ A₃} {a₄ : A₃ ⟶ A₄}
    {b₁ : B₀ ⟶ B₁} {b₂ : B₁ ⟶ B₂} {b₃ : B₂ ⟶ B₃} {b₄ : B₃ ⟶ B₄}
    (h₁ : m₀ ≫ b₁ = a₁ ≫ m₁) (h₂ : m₁ ≫ b₂ = a₂ ≫ m₂) (h₃ : m₂ ≫ b₃ = a₃ ≫ m₃)
    (h₄ : m₃ ≫ b₄ = a₄ ≫ m₄) :
    m₀ ≫ (b₁ ≫ ((b₂ ≫ b₃) ≫ b₄)) = (a₁ ≫ ((a₂ ≫ a₃) ≫ a₄)) ≫ m₄ := by
  simp only [Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, h₄]

/-- A natural isomorphism of bifunctors induces an isomorphism of the bicomplexes that the
two bifunctors build from one pair of complexes. -/
public def mapBifunctorHomologicalComplexIso
    {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
    [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
    {F G : C₁ ⥤ C₂ ⥤ D}
    [F.PreservesZeroMorphisms] [∀ X, (F.obj X).PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] [∀ X, (G.obj X).PreservesZeroMorphisms]
    (e : F ≅ G) (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ) :
    ((F.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L ≅
      ((G.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => HomologicalComplex.Hom.isoOfComponents
      (fun j => (e.app (K.X i)).app (L.X j))
      (fun j j' _ => ((e.hom.app (K.X i)).naturality (L.d j j')).symm))
    (fun i i' _ => by
      ext j
      exact (congr_app (e.hom.naturality (K.d i i')) (L.X j)).symm)

/-- Totalization respects a natural isomorphism of bifunctors. -/
public def mapBifunctorIso
    {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
    [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
    {F G : C₁ ⥤ C₂ ⥤ D}
    [F.PreservesZeroMorphisms] [∀ X, (F.obj X).PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] [∀ X, (G.obj X).PreservesZeroMorphisms]
    (e : F ≅ G) (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ)
    [HomologicalComplex.HasMapBifunctor K L F (.up ℤ)]
    [HomologicalComplex.HasMapBifunctor K L G (.up ℤ)] :
    HomologicalComplex.mapBifunctor K L F (.up ℤ) ≅
      HomologicalComplex.mapBifunctor K L G (.up ℤ) :=
  HomologicalComplex₂.total.mapIso (mapBifunctorHomologicalComplexIso e K L) (.up ℤ)

/-- The isomorphism induced by a natural isomorphism of bifunctors acts on the antidiagonal
summand `K^i ⊗ L^j` by the component of that isomorphism. -/
public theorem ι_mapBifunctorIso_hom
    {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
    [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
    {F G : C₁ ⥤ C₂ ⥤ D}
    [F.PreservesZeroMorphisms] [∀ X, (F.obj X).PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] [∀ X, (G.obj X).PreservesZeroMorphisms]
    (e : F ≅ G) (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ)
    [HomologicalComplex.HasMapBifunctor K L F (.up ℤ)]
    [HomologicalComplex.HasMapBifunctor K L G (.up ℤ)]
    (i j n : ℤ) (h : i + j = n) :
    HomologicalComplex.ιMapBifunctor K L F (.up ℤ) i j n h ≫
        (mapBifunctorIso e K L).hom.f n =
      (e.hom.app (K.X i)).app (L.X j) ≫
        HomologicalComplex.ιMapBifunctor K L G (.up ℤ) i j n h :=
  HomologicalComplex₂.ιTotal_map _ _
    (mapBifunctorHomologicalComplexIso e K L).hom (.up ℤ) i j n h

/-- The isomorphism induced by a natural isomorphism of bifunctors is natural in both
complexes. -/
public theorem mapBifunctorIso_hom_naturality
    {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
    [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
    {F G : C₁ ⥤ C₂ ⥤ D}
    [F.PreservesZeroMorphisms] [∀ X, (F.obj X).PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] [∀ X, (G.obj X).PreservesZeroMorphisms]
    (e : F ≅ G) {K K' : CochainComplex C₁ ℤ}
    {L L' : CochainComplex C₂ ℤ} (f : K ⟶ K') (g : L ⟶ L')
    [HomologicalComplex.HasMapBifunctor K L F (.up ℤ)]
    [HomologicalComplex.HasMapBifunctor K L G (.up ℤ)]
    [HomologicalComplex.HasMapBifunctor K' L' F (.up ℤ)]
    [HomologicalComplex.HasMapBifunctor K' L' G (.up ℤ)] :
    HomologicalComplex.mapBifunctorMap f g F (.up ℤ) ≫
        (mapBifunctorIso e K' L').hom =
      (mapBifunctorIso e K L).hom ≫
        HomologicalComplex.mapBifunctorMap f g G (.up ℤ) := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  simp only [HomologicalComplex.comp_f, HomologicalComplex.ι_mapBifunctorMap_assoc,
    ι_mapBifunctorIso_hom, reassoc_of% ι_mapBifunctorIso_hom,
    HomologicalComplex.ι_mapBifunctorMap]
  simp [← NatTrans.naturality_assoc]

/-- The universe-independent K-flatness predicate agrees with K-flatness against the lifted
monoidal structure on `ModuleCat`. -/
public theorem isKFlat_iff_kFlat
    {A : Type u} [CommRing A]
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    IsKFlat.{u, v} K ↔ K.KFlat := Iff.rfl

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- The identity map of a module, as a semilinear equivalence from its restriction of scalars
along a ring isomorphism. -/
public def restrictScalarsLinearEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) (M : ModuleCat.{max u v} S) :
    LinearEquiv (σ' := (e.symm : S →+* R)) (e : R →+* S)
      ((ModuleCat.restrictScalars e.toRingHom).obj M) M where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restriction of scalars along a ring isomorphism commutes with the tensor product of two
modules. -/
public def restrictScalarsTensorIso
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) (M N : ModuleCat.{max u v} S) :
    ModuleCat.of R (TensorProduct R
      ((ModuleCat.restrictScalars e.toRingHom).obj M)
      ((ModuleCat.restrictScalars e.toRingHom).obj N)) ≅
    (ModuleCat.restrictScalars e.toRingHom).obj
      (ModuleCat.of S (TensorProduct S M N)) := by
  let t := TensorProduct.congr (restrictScalarsLinearEquiv e M)
    (restrictScalarsLinearEquiv e N)
  letI : Module R (TensorProduct S M N) :=
    Module.compHom (TensorProduct S M N) e.toRingHom
  apply LinearEquiv.toModuleIso
  exact { __ := t.toAddEquiv, map_smul' := t.map_smul' }

/-- The comparison of `CochainComplex.DerivedTensor.restrictScalarsTensorIso`, as an isomorphism
of bifunctors. -/
public def restrictScalarsTensorNatIso
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) :
    (ModuleCat.restrictScalars.{max u v, u, v} e.toRingHom).prod
        (ModuleCat.restrictScalars.{max u v, u, v} e.toRingHom) ⋙
      CategoryTheory.Functor.uncurry.obj (moduleTensor.{u, v} R) ≅
    CategoryTheory.Functor.uncurry.obj (moduleTensor.{v, u} S) ⋙
      ModuleCat.restrictScalars.{max u v, u, v} e.toRingHom :=
  NatIso.ofComponents (fun X => restrictScalarsTensorIso e X.1 X.2) (by
    intro X Y f
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl)

/-- Tensoring on the left, read through restriction of scalars along a ring isomorphism,
preserves zero morphisms. -/
public theorem restrictScalars_tensorLeft_preservesZero
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) :
    (CategoryTheory.Functor.curry.obj
      ((ModuleCat.restrictScalars.{max u v, u, v} e.toRingHom).prod
        (ModuleCat.restrictScalars.{max u v, u, v} e.toRingHom) ⋙
        CategoryTheory.Functor.uncurry.obj
          (moduleTensor.{u, v} R))).PreservesZeroMorphisms := by
  constructor
  intro M N
  apply NatTrans.ext
  funext P
  simp
  rfl

/-- The bicomplex of termwise tensor products of two complexes of modules, whose total complex
is `CochainComplex.DerivedTensor.tensorComplex`. -/
@[ega "III 7.6.4"]
public abbrev tensorBicomplex
    (R : Type u) [CommRing R]
    (K L : CochainComplex (ModuleCat.{max u v} R) ℤ) :=
  (((moduleTensor.{u, v} R).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L

/-- Restriction of scalars along a ring isomorphism commutes with the tensor bicomplex. -/
public def restrictScalarsTensorBicomplexIso
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) (K L : CochainComplex (ModuleCat.{max u v} S) ℤ) :
    tensorBicomplex R
      (((ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex (.up ℤ)).obj K)
      (((ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex (.up ℤ)).obj L) ≅
    HomologicalComplex₂.TotalMap.mapBicomplex (ModuleCat.restrictScalars e.toRingHom)
      (tensorBicomplex S K L) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => HomologicalComplex.Hom.isoOfComponents
      (fun q => restrictScalarsTensorIso e (K.X p) (L.X q))
      (by
        intro q q' _
        apply ModuleCat.hom_ext
        apply TensorProduct.ext
        ext x y
        rfl))
    (by
      intro p p' _
      apply HomologicalComplex.hom_ext
      intro q
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      ext x y
      rfl)

/-- Restriction of scalars along a ring isomorphism commutes with the total tensor product of
two complexes. -/
public def restrictScalarsTensorComplexIso
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) (K L : CochainComplex (ModuleCat.{max u v} S) ℤ) :
    tensorComplex
      (((ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex (.up ℤ)).obj K)
      (((ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex (.up ℤ)).obj L) ≅
    ((ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex (.up ℤ)).obj
      (tensorComplex K L) := by
  let E := ModuleCat.restrictScalars.{max u v, u, v} e.toRingHom
  let _ : E.IsEquivalence := inferInstance
  exact HomologicalComplex₂.total.mapIso (restrictScalarsTensorBicomplexIso e K L) (.up ℤ) ≪≫
    HomologicalComplex₂.TotalMap.totalIso (c₁₂ := .up ℤ) E (tensorBicomplex S K L)

/-- A pair of morphisms of complexes, acting on the tensor bicomplex. -/
public abbrev tensorBicomplexMap
    {R : Type u} [CommRing R]
    {K K' L L' : CochainComplex (ModuleCat.{max u v} R) ℤ}
    (f : K ⟶ K') (g : L ⟶ L') :
    tensorBicomplex R K L ⟶ tensorBicomplex R K' L' :=
  (((moduleTensor.{u, v} R).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).map f).app L ≫
  (((moduleTensor.{u, v} R).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K').map g

/-- The bicomplex comparison is natural in both complexes. -/
public theorem restrictScalarsTensorBicomplexIso_naturality
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S)
    {K K' L L' : CochainComplex (ModuleCat.{max u v} S) ℤ}
    (f : K ⟶ K') (g : L ⟶ L') :
    let E := ModuleCat.restrictScalars.{max u v, u, v} e.toRingHom
    let EC := E.mapHomologicalComplex (.up ℤ)
    tensorBicomplexMap (EC.map f) (EC.map g) ≫
        (restrictScalarsTensorBicomplexIso e K' L').hom =
      (restrictScalarsTensorBicomplexIso e K L).hom ≫
        ((EC.mapHomologicalComplex (.up ℤ)).map (tensorBicomplexMap f g)) := by
  dsimp only
  let α := restrictScalarsTensorNatIso e
  apply HomologicalComplex.hom_ext
  intro p
  apply HomologicalComplex.hom_ext
  intro q
  convert (α.hom.naturality (CategoryTheory.Prod.mkHom (f.f p) (g.f q))) using 1 <;> rfl

/-- The total complex comparison is natural in both complexes. -/
public theorem restrictScalarsTensorComplexIso_naturality
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S)
    {K K' L L' : CochainComplex (ModuleCat.{max u v} S) ℤ}
    (f : K ⟶ K') (g : L ⟶ L') :
    let E := ModuleCat.restrictScalars.{max u v, u, v} e.toRingHom
    let EC := E.mapHomologicalComplex (.up ℤ)
    HomologicalComplex.mapBifunctorMap (EC.map f) (EC.map g) (moduleTensor R) (.up ℤ) ≫
      (restrictScalarsTensorComplexIso e K' L').hom =
    (restrictScalarsTensorComplexIso e K L).hom ≫
      EC.map (HomologicalComplex.mapBifunctorMap f g (moduleTensor S) (.up ℤ)) := by
  dsimp only
  let E := ModuleCat.restrictScalars.{max u v, u, v} e.toRingHom
  let EC := E.mapHomologicalComplex (.up ℤ)
  let _ : E.IsEquivalence := inferInstance
  let b := restrictScalarsTensorBicomplexIso e K L
  let b' := restrictScalarsTensorBicomplexIso e K' L'
  let t := HomologicalComplex₂.TotalMap.totalIso (c₁₂ := .up ℤ) E (tensorBicomplex S K L)
  let t' := HomologicalComplex₂.TotalMap.totalIso (c₁₂ := .up ℤ) E (tensorBicomplex S K' L')
  show HomologicalComplex₂.total.map (tensorBicomplexMap (EC.map f) (EC.map g))
      (.up ℤ) ≫ (HomologicalComplex₂.total.map b'.hom (.up ℤ) ≫ t'.hom) =
    (HomologicalComplex₂.total.map b.hom (.up ℤ) ≫ t.hom) ≫
      EC.map (HomologicalComplex₂.total.map (tensorBicomplexMap f g) (.up ℤ))
  rw [← Category.assoc, ← HomologicalComplex₂.total.map_comp,
    restrictScalarsTensorBicomplexIso_naturality, HomologicalComplex₂.total.map_comp,
    Category.assoc, ← HomologicalComplex₂.TotalMap.totalIso_naturality (c₁₂ := .up ℤ) E
    (tensorBicomplex S K L) (tensorBicomplexMap f g)]
  dsimp only [b, t, EC, E]
  simp only [Category.assoc]

/-- A pair of isomorphisms of complexes induces an isomorphism of their total tensor
products. -/
public def tensorComplex_mapIso
    (R : Type u) [CommRing R]
    {K K' L L' : CochainComplex (ModuleCat.{max u v} R) ℤ}
    (f : K ≅ K') (g : L ≅ L') :
    tensorComplex K L ≅ tensorComplex K' L' := by
  let B := (moduleTensor.{u, v} R).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)
  exact HomologicalComplex₂.total.mapIso
    (((B.mapIso f).app L) ≪≫ ((B.obj K').mapIso g)) (.up ℤ)

/-- The forward direction of `CochainComplex.DerivedTensor.tensorComplex_mapIso` is the map of
total tensor products induced by the two isomorphisms. -/
public theorem tensorComplex_mapIso_hom
    (R : Type u) [CommRing R]
    {K K' L L' : CochainComplex (ModuleCat.{max u v} R) ℤ}
    (f : K ≅ K') (g : L ≅ L') :
    (tensorComplex_mapIso R f g).hom =
      HomologicalComplex.mapBifunctorMap f.hom g.hom (moduleTensor R) (.up ℤ) := by
  rfl

/-- **K-flatness is preserved by restriction of scalars along a ring isomorphism.** -/
public theorem isKFlat_restrictScalars_of_ringEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) (K : CochainComplex (ModuleCat.{max u v} S) ℤ)
    (hK : K.KFlat) :
    CochainComplex.KFlat
      (((ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex (.up ℤ)).obj K) := by
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, v, max u v} e
  let i := (ModuleCat.extendRestrictScalarsAdj.{v, v, u}
    e.symm.toRingHom).leftAdjointUniq E.toAdjunction
  let j := (NatIso.mapHomologicalComplex i (.up ℤ)).app K
  have h' := CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{v, u, max u v}
    e.symm.toRingHom K hK
  intro M hM
  let B := (moduleTensor.{u, v} R).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)
  let t := HomologicalComplex₂.total.mapIso ((B.obj M).mapIso j) (.up ℤ)
  exact HomologicalComplex.Acyclic.of_iso t (h' M hM)

/-- The scalar equivalence carries the localization of the restricted complex to the
localization of the complex itself. -/
public def scalarEquivalenceQObjIso
    (A : Type u) [CommRing A]
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    let E := StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A
    let E₀ := StacksDraft.DerivedHom.uliftModuleEquivalence.{u, max u v, v} A
    E.functor.obj (DerivedCategory.Q.obj ((E₀.inverse.mapHomologicalComplex (.up ℤ)).obj K)) ≅
      DerivedCategory.Q.obj K := by
  let E₀ := StacksDraft.DerivedHom.uliftModuleEquivalence.{u, max u v, v} A
  exact (E₀.functor.mapDerivedCategoryFactors).app
      ((E₀.inverse.mapHomologicalComplex (.up ℤ)).obj K) ≪≫
    DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex E₀.counitIso (.up ℤ)).app K)

/-- The comparison of `CochainComplex.DerivedTensor.scalarEquivalenceQObjIso` is natural. -/
public theorem scalarEquivalenceQObjIso_naturality
    (A : Type u) [CommRing A]
    {K L : CochainComplex (ModuleCat.{max u v} A) ℤ} (f : K ⟶ L) :
    let E := StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A
    let E₀ := StacksDraft.DerivedHom.uliftModuleEquivalence.{u, max u v, v} A
    E.functor.map (DerivedCategory.Q.map ((E₀.inverse.mapHomologicalComplex (.up ℤ)).map f)) ≫
        (scalarEquivalenceQObjIso A L).hom =
      (scalarEquivalenceQObjIso A K).hom ≫ DerivedCategory.Q.map f := by
  intro _ E₀
  -- Both composites are spelled through the factorisation `F ≅ G` below, so that every
  -- intermediate object is named by the same functor on both sides; associativity and the
  -- naturality squares then compose as terms, with no unfolding of the scalar equivalence.
  let EC₀ := E₀.inverse.mapHomologicalComplex (ComplexShape.up ℤ)
  let EC := E₀.functor.mapHomologicalComplex (ComplexShape.up ℤ)
  let c := NatIso.mapHomologicalComplex E₀.counitIso (ComplexShape.up ℤ)
  let α := E₀.functor.mapDerivedCategoryFactors
  let F := DerivedCategory.Q ⋙ E₀.functor.mapDerivedCategory
  let G := EC ⋙ DerivedCategory.Q
  let h : EC₀.obj K ⟶ EC₀.obj L := EC₀.map f
  let aK : F.obj (EC₀.obj K) ⟶ G.obj (EC₀.obj K) := α.hom.app (EC₀.obj K)
  let aL : F.obj (EC₀.obj L) ⟶ G.obj (EC₀.obj L) := α.hom.app (EC₀.obj L)
  let cK : G.obj (EC₀.obj K) ⟶ DerivedCategory.Q.obj K := DerivedCategory.Q.map (c.app K).hom
  let cL : G.obj (EC₀.obj L) ⟶ DerivedCategory.Q.obj L := DerivedCategory.Q.map (c.app L).hom
  have hc : EC.map h ≫ (c.app L).hom = (c.app K).hom ≫ f := c.hom.naturality f
  have hcQ : G.map h ≫ cL = cK ≫ DerivedCategory.Q.map f :=
    (DerivedCategory.Q.map_commSq ⟨hc⟩).w
  have key : F.map h ≫ (aL ≫ cL) = (aK ≫ cK) ≫ DerivedCategory.Q.map f :=
    glue_comp_squares (α.hom.naturality h) hcQ
  exact key

/-- The inverse of `CochainComplex.DerivedTensor.scalarEquivalenceQObjIso` is natural. -/
public theorem scalarEquivalenceQObjIso_inv_naturality
    (A : Type u) [CommRing A]
    {K L : CochainComplex (ModuleCat.{max u v} A) ℤ} (f : K ⟶ L) :
    let E := StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A
    let E₀ := StacksDraft.DerivedHom.uliftModuleEquivalence.{u, max u v, v} A
    DerivedCategory.Q.map f ≫ (scalarEquivalenceQObjIso A L).inv =
      (scalarEquivalenceQObjIso A K).inv ≫
        E.functor.map (DerivedCategory.Q.map
          ((E₀.inverse.mapHomologicalComplex (.up ℤ)).map f)) := by
  have h := scalarEquivalenceQObjIso_naturality A f
  apply (cancel_mono (scalarEquivalenceQObjIso A L).hom).mp
  simp only [Category.assoc]
  rw [h]
  simp

/-- The scalar equivalence carries the total tensor product of the restricted complexes to the
total tensor product of the complexes themselves. -/
public def scalarEquivalenceTensorComplexIso
    (A : Type u) [CommRing A]
    (K L : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    let E := StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A
    let E₀ := StacksDraft.DerivedHom.uliftModuleEquivalence.{u, max u v, v} A
    let K₀ := (E₀.inverse.mapHomologicalComplex (.up ℤ)).obj K
    let L₀ := (E₀.inverse.mapHomologicalComplex (.up ℤ)).obj L
    E.functor.obj (DerivedCategory.Q.obj (tensorComplex K₀ L₀)) ≅
      DerivedCategory.Q.obj (tensorComplex K L) := by
  let e := (ULift.ringEquiv.{u, v} (R := A)).symm
  let E := StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A
  exact E.functor.mapIso
      (DerivedCategory.Q.mapIso (restrictScalarsTensorComplexIso e.symm K L)) ≪≫
    scalarEquivalenceQObjIso A (tensorComplex K L)

/-- The comparison of `CochainComplex.DerivedTensor.scalarEquivalenceTensorComplexIso` is
natural in both complexes. -/
public theorem scalarEquivalenceTensorComplexIso_naturality
    (A : Type u) [CommRing A]
    {K K' L L' : CochainComplex (ModuleCat.{max u v} A) ℤ}
    (f : K ⟶ K') (g : L ⟶ L') :
    let E := StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A
    let E₀ := StacksDraft.DerivedHom.uliftModuleEquivalence.{u, max u v, v} A
    let s := HomologicalComplex.mapBifunctorMap
      ((E₀.inverse.mapHomologicalComplex (.up ℤ)).map f)
      ((E₀.inverse.mapHomologicalComplex (.up ℤ)).map g)
      (moduleTensor (ULift.{v} A)) (.up ℤ)
    let t := HomologicalComplex.mapBifunctorMap f g (moduleTensor A) (.up ℤ)
    E.functor.map (DerivedCategory.Q.map s) ≫
        (scalarEquivalenceTensorComplexIso A K' L').hom =
      (scalarEquivalenceTensorComplexIso A K L).hom ≫ DerivedCategory.Q.map t := by
  intro E E₀ s t
  -- The comparison is the transported restriction-of-scalars comparison of total tensor
  -- products followed by `scalarEquivalenceQObjIso`; both factors are natural, and the two
  -- naturality squares are pasted as terms. The type ascriptions on `r`, `r'`, `qKL` and
  -- `qK'L'` put every intermediate object in the spelling `s` and `t` already use.
  let e := (ULift.ringEquiv.{u, v} (R := A)).symm
  let EC₀ := E₀.inverse.mapHomologicalComplex (ComplexShape.up ℤ)
  let r : tensorComplex (EC₀.obj K) (EC₀.obj L) ⟶ EC₀.obj (tensorComplex K L) :=
    (restrictScalarsTensorComplexIso e.symm K L).hom
  let r' : tensorComplex (EC₀.obj K') (EC₀.obj L') ⟶ EC₀.obj (tensorComplex K' L') :=
    (restrictScalarsTensorComplexIso e.symm K' L').hom
  let qKL : E.functor.obj (DerivedCategory.Q.obj (EC₀.obj (tensorComplex K L))) ⟶
      DerivedCategory.Q.obj (tensorComplex K L) :=
    (scalarEquivalenceQObjIso.{u, v} A (tensorComplex K L)).hom
  let qK'L' : E.functor.obj (DerivedCategory.Q.obj (EC₀.obj (tensorComplex K' L'))) ⟶
      DerivedCategory.Q.obj (tensorComplex K' L') :=
    (scalarEquivalenceQObjIso.{u, v} A (tensorComplex K' L')).hom
  have hr : s ≫ r' = r ≫ EC₀.map t :=
    restrictScalarsTensorComplexIso_naturality e.symm f g
  have hq : E.functor.map (DerivedCategory.Q.map (EC₀.map t)) ≫ qK'L' =
      qKL ≫ DerivedCategory.Q.map t := scalarEquivalenceQObjIso_naturality A t
  have hQ : DerivedCategory.Q.map s ≫ DerivedCategory.Q.map r' =
      DerivedCategory.Q.map r ≫ DerivedCategory.Q.map (EC₀.map t) :=
    (DerivedCategory.Q.map_commSq ⟨hr⟩).w
  have hE : E.functor.map (DerivedCategory.Q.map s) ≫
        E.functor.map (DerivedCategory.Q.map r') =
      E.functor.map (DerivedCategory.Q.map r) ≫
        E.functor.map (DerivedCategory.Q.map (EC₀.map t)) :=
    (E.functor.map_commSq ⟨hQ⟩).w
  have key : E.functor.map (DerivedCategory.Q.map s) ≫
        (E.functor.map (DerivedCategory.Q.map r') ≫ qK'L') =
      (E.functor.map (DerivedCategory.Q.map r) ≫ qKL) ≫ DerivedCategory.Q.map t :=
    glue_comp_squares hE hq
  exact key

/-- **K-flat representatives compute the derived tensor product of the canonical tensor--Hom
adjunction** `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing` on the derived category of
`A`-modules in an independent module universe. Only the second representative has to be
K-flat, since the model isomorphism it is compared with asks for no more. -/
public def derivedTensor_comparison
    (A : Type u) [CommRing A]
    (K L : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hL : L.KFlat) :
    let d := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing A
    d.tensor.obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (tensorComplex K L) := by
  let E₀ := StacksDraft.DerivedHom.uliftModuleEquivalence.{u, max u v, v} A
  let K₀ := (E₀.inverse.mapHomologicalComplex (.up ℤ)).obj K
  let L₀ := (E₀.inverse.mapHomologicalComplex (.up ℤ)).obj L
  let e := (ULift.ringEquiv.{u, v} (R := A)).symm
  have hL₀ : CochainComplex.KFlat L₀ := isKFlat_restrictScalars_of_ringEquiv e.symm L hL
  exact (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing A).tensor.mapIso
      ((scalarEquivalenceQObjIso.{u, v} A K).symm.prod
        (scalarEquivalenceQObjIso.{u, v} A L).symm) ≪≫
    StacksDraft.DerivedHom.derivedTensorModelIso (R := A) K₀ L₀ hL₀ ≪≫
    scalarEquivalenceTensorComplexIso.{u, v} A K L

/-- **The canonical derived tensor product of `A`-modules in an independent module universe.**
It is the canonical derived tensor product over `ULift.{v} A`, transported along the scalar
equivalence. -/
public def canonicalDerivedTensorFunctorGeneral
    (A : Type u) [CommRing A] :
    DerivedCategory (ModuleCat.{max u v} A) ⥤
      DerivedCategory (ModuleCat.{max u v} A) ⥤
        DerivedCategory (ModuleCat.{max u v} A) :=
  let E := StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A
  Functor.curry.obj (E.inverse.prod E.inverse ⋙
    Functor.uncurry.obj (canonicalDerivedTensorProduct (ULift.{v} A)).tensor ⋙ E.functor)

/-- The transported derived tensor product, computed on localizations of complexes. -/
public def tensorFunctorModelIso
    (A : Type u) [CommRing A]
    (K L : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    let E := StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A
    let E₀ := StacksDraft.DerivedHom.uliftModuleEquivalence.{u, max u v, v} A
    let K₀ := (E₀.inverse.mapHomologicalComplex (.up ℤ)).obj K
    let L₀ := (E₀.inverse.mapHomologicalComplex (.up ℤ)).obj L
    let T := canonicalDerivedTensorProduct (ULift.{v} A)
    ((canonicalDerivedTensorFunctorGeneral.{u, v} A).obj (DerivedCategory.Q.obj K)).obj
        (DerivedCategory.Q.obj L) ≅
      E.functor.obj
        ((T.tensor.obj (DerivedCategory.Q.obj K₀)).obj (DerivedCategory.Q.obj L₀)) := by
  let E := StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A
  let E₀ := StacksDraft.DerivedHom.uliftModuleEquivalence.{u, max u v, v} A
  let K₀ := (E₀.inverse.mapHomologicalComplex (.up ℤ)).obj K
  let L₀ := (E₀.inverse.mapHomologicalComplex (.up ℤ)).obj L
  let T := canonicalDerivedTensorProduct (ULift.{v} A)
  let B := Functor.uncurry.obj (canonicalDerivedTensorFunctorGeneral.{u, v} A)
  exact B.mapIso ((scalarEquivalenceQObjIso.{u, v} A K).symm.prod
      (scalarEquivalenceQObjIso.{u, v} A L).symm) ≪≫
    E.functor.mapIso ((Functor.uncurry.obj T.tensor).mapIso
      ((E.unitIso.app (DerivedCategory.Q.obj K₀)).symm.prod
        (E.unitIso.app (DerivedCategory.Q.obj L₀)).symm))

/-- The comparison of `CochainComplex.DerivedTensor.tensorFunctorModelIso` is natural in both
complexes. -/
public theorem tensorFunctorModelIso_naturality
    (A : Type u) [CommRing A]
    {K K' L L' : CochainComplex (ModuleCat.{max u v} A) ℤ}
    (f : K ⟶ K') (g : L ⟶ L') :
    let E := StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A
    let E₀ := StacksDraft.DerivedHom.uliftModuleEquivalence.{u, max u v, v} A
    let T := canonicalDerivedTensorProduct (ULift.{v} A)
    let B := Functor.uncurry.obj (canonicalDerivedTensorFunctorGeneral.{u, v} A)
    let D := Functor.uncurry.obj T.tensor
    B.map (CategoryTheory.Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) ≫
        (tensorFunctorModelIso A K' L').hom =
      (tensorFunctorModelIso A K L).hom ≫
        E.functor.map (D.map (CategoryTheory.Prod.mkHom
          (DerivedCategory.Q.map ((E₀.inverse.mapHomologicalComplex (.up ℤ)).map f))
          (DerivedCategory.Q.map ((E₀.inverse.mapHomologicalComplex (.up ℤ)).map g)))) := by
  intro E E₀ T B D
  -- Name the five morphisms of the two pasted naturality squares: `p` and `w` are the maps
  -- being transported, `c`/`c'` the comparison of localizations, `u`/`u'` the unit of the
  -- scalar equivalence, and `m`/`v` the same map read on either side of that equivalence.
  let EC₀ := E₀.inverse.mapHomologicalComplex (ComplexShape.up ℤ)
  let K₀ := EC₀.obj K
  let K₀' := EC₀.obj K'
  let L₀ := EC₀.obj L
  let L₀' := EC₀.obj L'
  let f₀ : DerivedCategory.Q.obj K₀ ⟶ DerivedCategory.Q.obj K₀' :=
    DerivedCategory.Q.map (EC₀.map f)
  let g₀ : DerivedCategory.Q.obj L₀ ⟶ DerivedCategory.Q.obj L₀' :=
    DerivedCategory.Q.map (EC₀.map g)
  let cK := scalarEquivalenceQObjIso.{u, v} A K
  let cK' := scalarEquivalenceQObjIso.{u, v} A K'
  let cL := scalarEquivalenceQObjIso.{u, v} A L
  let cL' := scalarEquivalenceQObjIso.{u, v} A L'
  let p := CategoryTheory.Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)
  let c := (cK.symm.prod cL.symm).hom
  let c' := (cK'.symm.prod cL'.symm).hom
  let m := CategoryTheory.Prod.mkHom (E.functor.map f₀) (E.functor.map g₀)
  let v := CategoryTheory.Prod.mkHom
    (E.inverse.map (E.functor.map f₀)) (E.inverse.map (E.functor.map g₀))
  let u := ((E.unitIso.app (DerivedCategory.Q.obj K₀)).symm.prod
    (E.unitIso.app (DerivedCategory.Q.obj L₀)).symm).hom
  let u' := ((E.unitIso.app (DerivedCategory.Q.obj K₀')).symm.prod
    (E.unitIso.app (DerivedCategory.Q.obj L₀')).symm).hom
  let w := CategoryTheory.Prod.mkHom f₀ g₀
  have hp : p ≫ c' = c ≫ m := CategoryTheory.Prod.hom_ext
    (scalarEquivalenceQObjIso_inv_naturality A f) (scalarEquivalenceQObjIso_inv_naturality A g)
  have hu : v ≫ u' = u ≫ w := CategoryTheory.Prod.hom_ext
    (E.unitIso.symm.hom.naturality f₀) (E.unitIso.symm.hom.naturality g₀)
  have hB : B.map m = E.functor.map (D.map v) := by
    unfold B canonicalDerivedTensorFunctorGeneral
    rw [uncurry_curry_map]
    rfl
  have hDu : D.map v ≫ D.map u' = D.map u ≫ D.map w :=
    (D.map_commSq ⟨hu⟩).w
  have hEu : E.functor.map (D.map v) ≫ E.functor.map (D.map u') =
      E.functor.map (D.map u) ≫ E.functor.map (D.map w) :=
    (E.functor.map_commSq ⟨hDu⟩).w
  have hBp : B.map p ≫ B.map c' = B.map c ≫ E.functor.map (D.map v) :=
    (B.map_commSq ⟨hp⟩).w.trans (B.map c ≫= hB)
  have key : B.map p ≫ (B.map c' ≫ E.functor.map (D.map u')) =
      (B.map c ≫ E.functor.map (D.map u)) ≫ E.functor.map (D.map w) :=
    glue_comp_squares hBp hEu
  exact key

/-- K-flat representatives compute
`CochainComplex.DerivedTensor.canonicalDerivedTensorFunctorGeneral`. -/
public def tensorFunctorComparison
    (A : Type u) [CommRing A]
    (K L : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hK : K.KFlat) (hL : L.KFlat) :
    ((canonicalDerivedTensorFunctorGeneral.{u, v} A).obj (DerivedCategory.Q.obj K)).obj
        (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (tensorComplex K L) := by
  let E₀ := StacksDraft.DerivedHom.uliftModuleEquivalence.{u, max u v, v} A
  let E := StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A
  let K₀ := (E₀.inverse.mapHomologicalComplex (.up ℤ)).obj K
  let L₀ := (E₀.inverse.mapHomologicalComplex (.up ℤ)).obj L
  let e := (ULift.ringEquiv.{u, v} (R := A)).symm
  have hK₀ : CochainComplex.KFlat K₀ := isKFlat_restrictScalars_of_ringEquiv e.symm K hK
  have hL₀ : CochainComplex.KFlat L₀ := isKFlat_restrictScalars_of_ringEquiv e.symm L hL
  exact tensorFunctorModelIso A K L ≪≫
    E.functor.mapIso ((canonicalDerivedTensorProduct (ULift.{v} A)).comparison K₀ L₀ hK₀ hL₀) ≪≫
    scalarEquivalenceTensorComplexIso.{u, v} A K L

/-- The monoidal tensor product of complexes is the total tensor product. -/
public theorem tensorHom_eq_mapBifunctorMap
    (R : Type u) [CommRing R]
    {K K' L L' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : K ⟶ K') (g : L ⟶ L') :
    HomologicalComplex.tensorHom f g =
      HomologicalComplex.mapBifunctorMap f g (moduleTensor R) (.up ℤ) := rfl

/-- The comparison of `CochainComplex.DerivedTensor.tensorFunctorComparison` is natural in both
representatives. -/
public theorem tensorFunctorComparison_naturality
    (A : Type u) [CommRing A]
    {K K' L L' : CochainComplex (ModuleCat.{max u v} A) ℤ}
    (f : K ⟶ K') (g : L ⟶ L')
    (hK : K.KFlat) (hK' : K'.KFlat) (hL : L.KFlat) (hL' : L'.KFlat) :
    ((canonicalDerivedTensorFunctorGeneral.{u, v} A).map (DerivedCategory.Q.map f)).app
          (DerivedCategory.Q.obj L) ≫
        ((canonicalDerivedTensorFunctorGeneral.{u, v} A).obj
          (DerivedCategory.Q.obj K')).map (DerivedCategory.Q.map g) ≫
        (tensorFunctorComparison A K' L' hK' hL').hom =
      (tensorFunctorComparison A K L hK hL).hom ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap f g (moduleTensor A) (.up ℤ)) := by
  -- `tensorFunctorComparison` is the composite of three comparisons, each natural: the model
  -- isomorphism, the K-flat comparison over `ULift A` transported along `E`, and the comparison
  -- of total tensor products. The proof pastes their three naturality squares as terms.
  let E := StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A
  let E₀ := StacksDraft.DerivedHom.uliftModuleEquivalence.{u, max u v, v} A
  let e := (ULift.ringEquiv.{u, v} (R := A)).symm
  let EC₀ := E₀.inverse.mapHomologicalComplex (ComplexShape.up ℤ)
  let K₀ := EC₀.obj K
  let K₀' := EC₀.obj K'
  let L₀ := EC₀.obj L
  let L₀' := EC₀.obj L'
  let f₀ : K₀ ⟶ K₀' := EC₀.map f
  let g₀ : L₀ ⟶ L₀' := EC₀.map g
  have hk₀ : CochainComplex.KFlat K₀ := isKFlat_restrictScalars_of_ringEquiv e.symm K hK
  have hk₀' : CochainComplex.KFlat K₀' := isKFlat_restrictScalars_of_ringEquiv e.symm K' hK'
  have hl₀ : CochainComplex.KFlat L₀ := isKFlat_restrictScalars_of_ringEquiv e.symm L hL
  have hl₀' : CochainComplex.KFlat L₀' := isKFlat_restrictScalars_of_ringEquiv e.symm L' hL'
  let T := canonicalDerivedTensorProduct (ULift.{v} A)
  let B := Functor.uncurry.obj (canonicalDerivedTensorFunctorGeneral.{u, v} A)
  let D := Functor.uncurry.obj T.tensor
  let p := CategoryTheory.Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)
  let w := CategoryTheory.Prod.mkHom (DerivedCategory.Q.map f₀) (DerivedCategory.Q.map g₀)
  let s := HomologicalComplex.mapBifunctorMap f₀ g₀
    (moduleTensor (ULift.{v} A)) (ComplexShape.up ℤ)
  let t := HomologicalComplex.mapBifunctorMap f g (moduleTensor A) (ComplexShape.up ℤ)
  let M := (tensorFunctorModelIso A K L).hom
  let M' := (tensorFunctorModelIso A K' L').hom
  let Ec := E.functor.map (T.comparison K₀ L₀ hk₀ hl₀).hom
  let Ec' := E.functor.map (T.comparison K₀' L₀' hk₀' hl₀').hom
  let S := (scalarEquivalenceTensorComplexIso.{u, v} A K L).hom
  let S' := (scalarEquivalenceTensorComplexIso.{u, v} A K' L').hom
  let Ew := E.functor.map (D.map w)
  let Es := E.functor.map (DerivedCategory.Q.map s)
  have hpair :
      ((canonicalDerivedTensorFunctorGeneral.{u, v} A).map (DerivedCategory.Q.map f)).app
          (DerivedCategory.Q.obj L) ≫
        ((canonicalDerivedTensorFunctorGeneral.{u, v} A).obj
          (DerivedCategory.Q.obj K')).map (DerivedCategory.Q.map g) = B.map p := rfl
  have hmodel : B.map p ≫ M' = M ≫ Ew := tensorFunctorModelIso_naturality A f g
  have hsource0 :
      (T.tensor.map (DerivedCategory.Q.map f₀)).app (DerivedCategory.Q.obj L₀) ≫
        ((T.tensor.obj (DerivedCategory.Q.obj K₀')).map (DerivedCategory.Q.map g₀) ≫
          (T.comparison K₀' L₀' hk₀' hl₀').hom) =
      (T.comparison K₀ L₀ hk₀ hl₀).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap f₀ g₀
          (moduleTensor (ULift.{v} A)) (ComplexShape.up ℤ)) := by
    have h := T.comparison_naturality f₀ g₀ hk₀ hk₀' hl₀ hl₀'
    simp only [tensorHom_eq_mapBifunctorMap] at h
    exact h
  have hsourceD : D.map w ≫ (T.comparison K₀' L₀' hk₀' hl₀').hom =
      (T.comparison K₀ L₀ hk₀ hl₀).hom ≫ DerivedCategory.Q.map s :=
    (Category.assoc _ _ _).trans hsource0
  have hsourceE : Ew ≫ Ec' = Ec ≫ Es :=
    (E.functor.map_commSq ⟨hsourceD⟩).w
  have htensor : Es ≫ S' = S ≫ DerivedCategory.Q.map t :=
    scalarEquivalenceTensorComplexIso_naturality A f g
  have inner : Ew ≫ (Ec' ≫ S') = (Ec ≫ S) ≫ DerivedCategory.Q.map t :=
    glue_comp_squares hsourceE htensor
  have key : B.map p ≫ (M' ≫ (Ec' ≫ S')) =
      (M ≫ (Ec ≫ S)) ≫ DerivedCategory.Q.map t :=
    glue_comp_squares hmodel inner
  exact ((Category.assoc _ _ _).symm.trans (hpair =≫ _)).trans key

/-- The comparison of `CochainComplex.DerivedTensor.derivedTensor_comparison` is natural in both
representatives. -/
public theorem derivedTensor_comparison_naturality
    (A : Type u) [CommRing A]
    {K K' L L' : CochainComplex (ModuleCat.{max u v} A) ℤ}
    (f : K ⟶ K') (g : L ⟶ L') (hL : L.KFlat) (hL' : L'.KFlat) :
    (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.map
          (DerivedCategory.Q.map f, DerivedCategory.Q.map g) ≫
        (derivedTensor_comparison.{u, v} A K' L' hL').hom =
      (derivedTensor_comparison.{u, v} A K L hL).hom ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap f g (moduleTensor A) (.up ℤ)) := by
  -- `derivedTensor_comparison` is the composite of four comparisons, each natural: the
  -- identification of the two representatives through the scalar equivalence, the bifunctor
  -- comparison `derivedTensorULiftIso`, the K-flat comparison over `ULift A` transported along
  -- the scalar equivalence, and the comparison of total tensor products.  The four naturality
  -- squares are pasted as terms.
  let d := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v, max u v + 1} A
  let E := StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A
  let E₀ := StacksDraft.DerivedHom.uliftModuleEquivalence.{u, max u v, v} A
  let e := (ULift.ringEquiv.{u, v} (R := A)).symm
  let EC₀ := E₀.inverse.mapHomologicalComplex (ComplexShape.up ℤ)
  let dU := StacksDraft.DerivedHom.derivedHomAdjunctionULift.{u, v, max u v + 1} (R := A)
  have hl₀ : CochainComplex.KFlat (EC₀.obj L) := isKFlat_restrictScalars_of_ringEquiv e.symm L hL
  have hl₀' : CochainComplex.KFlat (EC₀.obj L') :=
    isKFlat_restrictScalars_of_ringEquiv e.symm L' hL'
  let f₀ : EC₀.obj K ⟶ EC₀.obj K' := EC₀.map f
  let g₀ : EC₀.obj L ⟶ EC₀.obj L' := EC₀.map g
  let sK := (scalarEquivalenceQObjIso.{u, v} A K).inv
  let sK' := (scalarEquivalenceQObjIso.{u, v} A K').inv
  let sL := (scalarEquivalenceQObjIso.{u, v} A L).inv
  let sL' := (scalarEquivalenceQObjIso.{u, v} A L').inv
  let U := (StacksDraft.DerivedHom.derivedTensorULiftIso.{u, v, max u v + 1} A).hom.app
    (DerivedCategory.Q.obj (EC₀.obj K), DerivedCategory.Q.obj (EC₀.obj L))
  let U' := (StacksDraft.DerivedHom.derivedTensorULiftIso.{u, v, max u v + 1} A).hom.app
    (DerivedCategory.Q.obj (EC₀.obj K'), DerivedCategory.Q.obj (EC₀.obj L'))
  let C := E.functor.map (dU.tensorIso (EC₀.obj K) (EC₀.obj L) hl₀).hom
  let C' := E.functor.map (dU.tensorIso (EC₀.obj K') (EC₀.obj L') hl₀').hom
  let S := (scalarEquivalenceTensorComplexIso.{u, v} A K L).hom
  let S' := (scalarEquivalenceTensorComplexIso.{u, v} A K' L').hom
  let p₀ : (E.functor.obj (DerivedCategory.Q.obj (EC₀.obj K)),
      E.functor.obj (DerivedCategory.Q.obj (EC₀.obj L))) ⟶
      (E.functor.obj (DerivedCategory.Q.obj (EC₀.obj K')),
        E.functor.obj (DerivedCategory.Q.obj (EC₀.obj L'))) :=
    CategoryTheory.Prod.mkHom (E.functor.map (DerivedCategory.Q.map f₀))
      (E.functor.map (DerivedCategory.Q.map g₀))
  have h₁ : d.tensor.map
        (CategoryTheory.Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) ≫
        d.tensor.map (CategoryTheory.Prod.mkHom sK' sL') =
      d.tensor.map (CategoryTheory.Prod.mkHom sK sL) ≫ d.tensor.map p₀ := by
    exact (d.tensor.map_commSq ⟨Prod.ext (scalarEquivalenceQObjIso_inv_naturality A f)
      (scalarEquivalenceQObjIso_inv_naturality A g)⟩).w
  have h₂ : d.tensor.map p₀ ≫ U' = U ≫ E.functor.map (dU.tensor.map
      (CategoryTheory.Prod.mkHom (DerivedCategory.Q.map f₀) (DerivedCategory.Q.map g₀))) :=
    (StacksDraft.DerivedHom.derivedTensorULiftIso.{u, v, max u v + 1} A).hom.naturality
      (CategoryTheory.Prod.mkHom (DerivedCategory.Q.map f₀) (DerivedCategory.Q.map g₀))
  have h₃₀ := dU.tensorIso_naturality f₀ g₀ hl₀ hl₀'
  simp only at h₃₀
  have h₃ := (E.functor.map_commSq ⟨h₃₀⟩).w
  have h₄ : E.functor.map (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap f₀ g₀
        (moduleTensor (ULift.{v} A)) (.up ℤ))) ≫ S' =
      S ≫ DerivedCategory.Q.map
        (HomologicalComplex.mapBifunctorMap f g (moduleTensor A) (.up ℤ)) :=
    scalarEquivalenceTensorComplexIso_naturality A f g
  exact comp_square_four h₁ h₂ h₃ h₄

/-- Tensoring on the right with a fixed object, expressed through the scalar equivalence. -/
public def tensorFunctorRightIso
    (A : Type u) [CommRing A]
    (K : DerivedCategory (ModuleCat.{max u v} A)) :
    let E := StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A
    let T := canonicalDerivedTensorProduct (ULift.{v} A)
    (canonicalDerivedTensorFunctorGeneral.{u, v} A).obj K ≅
      E.inverse ⋙ T.tensor.obj (E.inverse.obj K) ⋙ E.functor := by
  refine NatIso.ofComponents (fun _ => Iso.refl _) ?_
  intro X Y f
  simp [canonicalDerivedTensorFunctorGeneral]

/-- Tensoring on the left with a fixed object, expressed through the scalar equivalence. -/
public def tensorFunctorLeftIso
    (A : Type u) [CommRing A]
    (L : DerivedCategory (ModuleCat.{max u v} A)) :
    let E := StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A
    let T := canonicalDerivedTensorProduct (ULift.{v} A)
    (canonicalDerivedTensorFunctorGeneral.{u, v} A).flip.obj L ≅
      E.inverse ⋙ T.tensor.flip.obj (E.inverse.obj L) ⋙ E.functor := by
  refine NatIso.ofComponents (fun _ => Iso.refl _) ?_
  intro X Y f
  simp [canonicalDerivedTensorFunctorGeneral]

/-- The scalar equivalence commutes with the shifts. -/
public instance derivedScalarEquivalence_functor_commShift
    (A : Type u) [CommRing A] :
    (StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v,
      max u v + 1} A).functor.CommShift ℤ := by
  change ((StacksDraft.DerivedHom.uliftModuleEquivalence.{u, max u v,
    v} A).functor.mapDerivedCategory).CommShift ℤ
  infer_instance

/-- The scalar equivalence is exact. -/
public instance derivedScalarEquivalence_functor_isTriangulated
    (A : Type u) [CommRing A] :
    (StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v,
      max u v + 1} A).functor.IsTriangulated := by
  change ((StacksDraft.DerivedHom.uliftModuleEquivalence.{u, max u v,
    v} A).functor.mapDerivedCategory).IsTriangulated
  infer_instance

/-- The inverse of the scalar equivalence commutes with the shifts. -/
public instance derivedScalarEquivalence_inverse_commShift
    (A : Type u) [CommRing A] :
    (StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A).inverse.CommShift ℤ :=
  (StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A).commShiftInverse ℤ

/-- The scalar equivalence commutes with the shifts as an equivalence. -/
public instance derivedScalarEquivalence_commShift
    (A : Type u) [CommRing A] :
    (StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A).CommShift ℤ :=
  (StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A).commShift_of_functor ℤ

/-- The inverse of the scalar equivalence is exact. -/
public instance derivedScalarEquivalence_inverse_isTriangulated
    (A : Type u) [CommRing A] :
    (StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v,
      max u v + 1} A).inverse.IsTriangulated :=
  (StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v,
    max u v + 1} A).toAdjunction.isTriangulated_rightAdjoint

/-- Tensoring on the right with a fixed object commutes with the shifts. -/
public instance canonicalDerivedTensorFunctorGeneral_right_commShift
    (A : Type u) [CommRing A]
    (K : DerivedCategory (ModuleCat.{max u v} A)) :
    ((canonicalDerivedTensorFunctorGeneral.{u, v} A).obj K).CommShift ℤ := by
  let E := StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A
  let T := canonicalDerivedTensorProduct (ULift.{v} A)
  letI := T.commShift_right (E.inverse.obj K)
  letI : (E.inverse ⋙ T.tensor.obj (E.inverse.obj K) ⋙ E.functor).CommShift ℤ := inferInstance
  exact Functor.CommShift.ofIso (tensorFunctorRightIso A K).symm ℤ

/-- Tensoring on the right with a fixed object is exact. -/
public instance canonicalDerivedTensorFunctorGeneral_right_isTriangulated
    (A : Type u) [CommRing A]
    (K : DerivedCategory (ModuleCat.{max u v} A)) :
    ((canonicalDerivedTensorFunctorGeneral.{u, v} A).obj K).IsTriangulated := by
  let E := StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A
  let T := canonicalDerivedTensorProduct (ULift.{v} A)
  let _ := T.commShift_right (E.inverse.obj K)
  let _ := T.exact_right (E.inverse.obj K)
  let _ : (E.inverse ⋙ T.tensor.obj (E.inverse.obj K) ⋙ E.functor).CommShift ℤ := inferInstance
  let _ : (E.inverse ⋙ T.tensor.obj (E.inverse.obj K) ⋙ E.functor).IsTriangulated :=
    inferInstance
  let i := (tensorFunctorRightIso A K).symm
  let _ := Functor.CommShift.ofIso_compatibility i ℤ
  exact Functor.isTriangulated_of_iso i

/-- Tensoring on the left with a fixed object commutes with the shifts. -/
public instance canonicalDerivedTensorFunctorGeneral_left_commShift
    (A : Type u) [CommRing A]
    (L : DerivedCategory (ModuleCat.{max u v} A)) :
    ((canonicalDerivedTensorFunctorGeneral.{u, v} A).flip.obj L).CommShift ℤ := by
  let E := StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A
  let T := canonicalDerivedTensorProduct (ULift.{v} A)
  letI := T.commShift_left (E.inverse.obj L)
  letI : (E.inverse ⋙ T.tensor.flip.obj (E.inverse.obj L) ⋙ E.functor).CommShift ℤ :=
    inferInstance
  exact Functor.CommShift.ofIso (tensorFunctorLeftIso A L).symm ℤ

/-- Tensoring on the left with a fixed object is exact. -/
public instance canonicalDerivedTensorFunctorGeneral_left_isTriangulated
    (A : Type u) [CommRing A]
    (L : DerivedCategory (ModuleCat.{max u v} A)) :
    ((canonicalDerivedTensorFunctorGeneral.{u, v} A).flip.obj L).IsTriangulated := by
  let E := StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A
  let T := canonicalDerivedTensorProduct (ULift.{v} A)
  let _ := T.commShift_left (E.inverse.obj L)
  let _ := T.exact_left (E.inverse.obj L)
  let _ : (E.inverse ⋙ T.tensor.flip.obj (E.inverse.obj L) ⋙ E.functor).CommShift ℤ :=
    inferInstance
  let _ : (E.inverse ⋙ T.tensor.flip.obj (E.inverse.obj L) ⋙ E.functor).IsTriangulated :=
    inferInstance
  let i := (tensorFunctorLeftIso A L).symm
  let _ := Functor.CommShift.ofIso_compatibility i ℤ
  exact Functor.isTriangulated_of_iso i

/-- **The canonical derived tensor product of `A`-modules in an independent module universe**,
with its K-flat comparison and its exactness in each variable. -/
public def canonicalDerivedTensorProductGeneral
    (A : Type u) [CommRing A] :
    DerivedTensorProductGeneral.{u, v} A where
  tensor := canonicalDerivedTensorFunctorGeneral.{u, v} A
  comparison := tensorFunctorComparison A
  comparison_naturality := tensorFunctorComparison_naturality A
  commShift_left := by intro L; infer_instance
  commShift_right := by intro K; infer_instance
  exact_left := by intro L; infer_instance
  exact_right := by intro K; infer_instance

/-- **The monoidal structure on the derived category of `A`-modules in an independent module
universe**, transported from the one over `ULift.{v} A` along the scalar equivalence. -/
@[instance_reducible]
public def canonicalDerivedMonoidalStructure
    (A : Type u) [CommRing A] :
    MonoidalCategory (DerivedCategory (ModuleCat.{max u v} A)) := by
  letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
    (ULift.{v} A)).choose
  exact CategoryTheory.Monoidal.transport
    (StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A)

/-- The tensor bifunctor of the transported monoidal structure is the derived tensor product
of `CochainComplex.DerivedTensor.canonicalDerivedTensorFunctorGeneral`. -/
public def canonicalDerivedMonoidalTensorIso
    (A : Type u) [CommRing A] :
    letI := canonicalDerivedMonoidalStructure.{u, v} A
    MonoidalCategory.curriedTensor (DerivedCategory (ModuleCat.{max u v} A)) ≅
      canonicalDerivedTensorFunctorGeneral.{u, v} A := by
  let E := StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A
  letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
    (ULift.{v} A)).choose
  letI : MonoidalCategoryStruct (DerivedCategory (ModuleCat.{max u v} A)) :=
    CategoryTheory.Monoidal.transportStruct E
  letI : MonoidalCategory (DerivedCategory (ModuleCat.{max u v} A)) :=
    CategoryTheory.Monoidal.transport E
  let e := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
    (ULift.{v} A)).choose_spec.choose_spec.choose
  let t : MonoidalCategory.curriedTensor (DerivedCategory (ModuleCat.{max u v} A)) ≅
      Functor.curry.obj (E.inverse.prod E.inverse ⋙
        Functor.uncurry.obj (MonoidalCategory.curriedTensor _) ⋙ E.functor) := by
    refine NatIso.ofComponents (fun U => NatIso.ofComponents (fun Y => Iso.refl _) ?_) ?_
    · intro X Y f
      simpa [MonoidalCategory.curriedTensor] using
        CategoryTheory.Monoidal.transportStruct_whiskerLeft E U X Y f
    · intro X Y f
      ext Z
      simpa [MonoidalCategory.curriedTensor] using
        CategoryTheory.Monoidal.transportStruct_whiskerRight E f Z
  exact t ≪≫ Functor.curry.mapIso
    (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (E.inverse.prod E.inverse) (Functor.uncurry.mapIso e))
      E.functor)

/-- The unit of the symmetric monoidal derived category of [stacks 0FNQ] is the ring in
degree zero. -/
public def monoidalUnitIsoSingleFunctorObj
    (R : Type u) [CommRing R] :
    letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory R).choose
    𝟙_ (DerivedCategory (ModuleCat.{u} R)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R) := by
  letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory R).choose
  let T := canonicalSymmetricDerivedTensorProduct R
  let e := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
    R).choose_spec.choose_spec.choose
  exact (T.tensorProduct.rightUnitor.app (𝟙_ _)).symm ≪≫ ((e.app (𝟙_ _)).app _).symm ≪≫ λ_ _

/-- The unit of the transported monoidal structure is `A`, placed in degree zero, viewed as a
module in the larger universe. -/
public def canonicalDerivedMonoidalUnitIso
    (A : Type u) [CommRing A] :
    letI := canonicalDerivedMonoidalStructure.{u, v} A
    𝟙_ (DerivedCategory (ModuleCat.{max u v} A)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
        (ModuleCat.of A (ULift.{v} A)) := by
  let E := StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A
  letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
    (ULift.{v} A)).choose
  change E.functor.obj (𝟙_ (DerivedCategory (ModuleCat.{max u v} (ULift.{v} A)))) ≅ _
  exact E.functor.mapIso (monoidalUnitIsoSingleFunctorObj (ULift.{v} A)) ≪≫
    ((StacksDraft.DerivedHom.uliftModuleEquivalence.{u, max u v,
      v} A).functor.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).mapIso (Iso.refl _)

end CochainComplex.DerivedTensor

end
