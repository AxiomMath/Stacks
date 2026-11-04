module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.Combinatorics.Quiver.ReflQuiver
import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.RebaseBaseChange
import StacksFrontier.RingTheory.Flat.Lazard
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public noncomputable section

/-!
# Change of rings for Tor

For commutative `R`-algebras `A` and `B`, `Tor_i^R(A, B)` carries a canonical
`A ⊗[R] B`-module structure. A commutative diagram of algebra maps induces a map on Tor
which is semilinear over the induced map of tensor-product algebras. These maps are functorial
in the diagram, and their scalar extensions give the comparisons used in base change.

## Main definitions

* `TorChangeOfRings.tensorProductMap`: the map of tensor-product algebras induced by a
  commutative ring diagram.
* `TorChangeOfRings.System`: an all-degree system of tensor-product actions and
  change-of-rings maps.
* `TorChangeOfRings.canonicalSystem`: a canonical system from an existence witness.
* `TorChangeOfRings.changeMap`: the semilinear change-of-rings map from such a witness.
* `TorChangeOfRings.extensionMap`: its linear extension to the target tensor-product algebra.
* `TorChangeOfRings.moduleStructure`: the canonical `A ⊗[R] B`-module structure on
  `Tor_i^R(A, B)`.

## Main results

* `TorChangeOfRings.canonicalSystem_nonempty`: a canonical system exists.
* `TorChangeOfRings.System.IsCanonical.action_tmul`: the action is characterized on pure
  tensors.
* `TorChangeOfRings.System.IsCanonical.map_id` and
  `TorChangeOfRings.System.IsCanonical.map_comp`: change-of-rings maps are functorial.
* `TorChangeOfRings.System.IsCanonical.extension_one_tmul`: the scalar-extended map is
  characterized on generators.
* `TorChangeOfRings.System.IsCanonical.map_resolution`: the change map agrees with the
  chain map between projective-resolution models of Tor.
* `TorChangeOfRings.System.IsCanonical.resolution_comparison_exists`: compatible chain
  comparisons exist for every pair of projective resolutions.
* `TorChangeOfRings.System.IsCanonical.flat_baseChange`: the canonical flat base-change
  comparison is an isomorphism.
* `TorChangeOfRings.System.IsCanonical.flat_algebra_extension`: independently extending
  both algebras by flat maps over a fixed base gives an isomorphism on Tor.
* `TorChangeOfRings.isIso_extensionMap_of_flat_algebra`: the same statement for the chosen
  canonical system.

## Implementation notes

The canonical construction and all its coherence are packaged as one data-valued object. Its
existence is stated separately, and definitions selecting it take an explicit existence witness.
This keeps the module structures used by identity, composition, and scalar extension definitionally
the same. The map after extension of scalars is obtained from semilinearity by the standard
extension/restriction-of-scalars adjunction. The resolution comparison identifies the map with
the homology map of any lift of the algebra diagram to projective resolutions; its chain map
sends `a ⊗ p` to `fA a ⊗ ψ p` in every degree.

Multiplication in the two algebras induces commuting actions on Tor, and the comparison map is
induced on homology by a lift between projective resolutions. Linearity of derived functors
follows by lifting sums and scalar multiples to projective resolutions and using uniqueness up to
homotopy. Filtered-colimit comparisons use projective resolutions in categories of module
diagrams. The flat module comparison follows from Lazard's theorem
(`flat_iff_directLimit_free_finite`, Tag 058G) and its finite free calculation.

## References

* [Stacks, Tag 00M7](https://stacks.math.columbia.edu/tag/00M7)
* [Stacks, Tag 058G](https://stacks.math.columbia.edu/tag/058G)
-/


open CategoryTheory

open scoped TensorProduct

universe u v

namespace TorChangeOfRings

/-- The `i`-th Tor module of two `R`-modules, using Mathlib's categorical Tor functor. -/
public abbrev torObj (R : Type u) [CommRing R] (i : ℕ) (M N : Type u)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] : Type u :=
  ((CategoryTheory.Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R M)).obj
    (ModuleCat.of R N)

/-- The homomorphism between tensor-product algebras induced by a commutative diagram of
algebra maps. -/
public def tensorProductMap (R R' A B A' B' : Type u)
    [CommRing R] [CommRing R'] [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra R R'] [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra R B']
    [Algebra R' A'] [Algebra R' B'] [IsScalarTower R R' A'] [IsScalarTower R R' B']
    (fA : A →ₐ[R] A') (fB : B →ₐ[R] B') : (A ⊗[R] B) →+* (A' ⊗[R'] B') :=
  (Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeLeft : A' →ₐ[R'] A' ⊗[R'] B').restrictScalars R |>.comp fA)
    ((Algebra.TensorProduct.includeRight : B' →ₐ[R'] A' ⊗[R'] B').restrictScalars R |>.comp fB)
    fun _ _ ↦ Commute.all _ _).toRingHom

/-- Multiplication by an element of an algebra, regarded as a linear endomorphism over the
base ring. -/
public def mulLinear (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (a : A) :
    A →ₗ[R] A where
  toFun x := a * x
  map_add' x y := mul_add a x y
  map_smul' r x := by simp [Algebra.smul_def, mul_left_comm]

/-- Homology commutes with restriction of scalars. The homology isomorphism is the one
induced by the exact restriction-of-scalars functor on the short complex in degree `i`. -/
public noncomputable def homologyRestrictIso (R R' : Type u) [CommRing R] [CommRing R']
    [Algebra R R'] (K : ChainComplex (ModuleCat.{u} R') ℕ) (i : ℕ) :
    (((ModuleCat.restrictScalars (algebraMap R R')).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj K).homology i ≅
      (ModuleCat.restrictScalars (algebraMap R R')).obj (K.homology i) :=
  ((K.sc' (ComplexShape.down ℕ |>.prev i) i (ComplexShape.down ℕ |>.next i)).mapHomologyIso
    (ModuleCat.restrictScalars (algebraMap R R')))

/-- An all-degree system of tensor-product actions and change-of-rings maps for Tor. -/
public structure System where
  action : ∀ (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℕ), Module (A ⊗[R] B) (torObj R i A B)
  action_tower : ∀ (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℕ),
    letI := action R A B i
    IsScalarTower R (A ⊗[R] B) (torObj R i A B)
  map : ∀ (R R' A B A' B' : Type u)
    [CommRing R] [CommRing R'] [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra R R'] [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra R B']
    [Algebra R' A'] [Algebra R' B'] [IsScalarTower R R' A'] [IsScalarTower R R' B']
    (i : ℕ) (fA : A →ₐ[R] A') (fB : B →ₐ[R] B'),
    letI := action R A B i
    letI := action R' A' B' i
    torObj R i A B →ₛₗ[tensorProductMap R R' A B A' B' fA fB] torObj R' i A' B'

/-- The scalar extension of a system's semilinear change-of-rings map. -/
public def System.extensionMap (S : System) (R R' A B A' B' : Type u)
    [CommRing R] [CommRing R'] [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra R R'] [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra R B']
    [Algebra R' A'] [Algebra R' B'] [IsScalarTower R R' A'] [IsScalarTower R R' B']
    (i : ℕ) (fA : A →ₐ[R] A') (fB : B →ₐ[R] B') :
    letI := S.action R A B i
    letI := S.action R' A' B' i
    (ModuleCat.extendScalars (tensorProductMap R R' A B A' B' fA fB)).obj
        (ModuleCat.of (A ⊗[R] B) (torObj R i A B)) ⟶
      ModuleCat.of (A' ⊗[R'] B') (torObj R' i A' B') := by
  letI := S.action R A B i
  letI := S.action R' A' B' i
  refine ((ModuleCat.extendRestrictScalarsAdj
    (tensorProductMap R R' A B A' B' fA fB)).homEquiv
      (ModuleCat.of (A ⊗[R] B) (torObj R i A B))
      (ModuleCat.of (A' ⊗[R'] B') (torObj R' i A' B'))).symm ?_
  exact ModuleCat.homEquiv.symm
    { toFun := S.map R R' A B A' B' i fA fB
      map_add' := (S.map R R' A B A' B' i fA fB).map_add
      map_smul' := (S.map R R' A B A' B' i fA fB).map_smul' }

/-- Coherence conditions characterizing a functorial change-of-rings system. -/
public structure System.IsCanonical (S : System) : Prop where
  action_tmul : ∀ (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℕ),
    letI := S.action R A B i
    ∀ (a : A) (b : B) (x : torObj R i A B),
      (a ⊗ₜ[R] b) • x =
        (((CategoryTheory.Tor (ModuleCat.{u} R) i).map (ModuleCat.ofHom (mulLinear R A a))).app
            (ModuleCat.of R B) ≫
          ((CategoryTheory.Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R A)).map
            (ModuleCat.ofHom (mulLinear R B b))) x
  map_id : ∀ (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℕ) (x : torObj R i A B),
    S.map R R A B A B i (AlgHom.id R A) (AlgHom.id R B) x = x
  map_comp : ∀ (R R' R'' A B A' B' A'' B'' : Type u)
    [CommRing R] [CommRing R'] [CommRing R'']
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [CommRing A''] [CommRing B'']
    [Algebra R R'] [Algebra R' R''] [Algebra R R''] [IsScalarTower R R' R'']
    [Algebra R A] [Algebra R B]
    [Algebra R A'] [Algebra R B'] [Algebra R' A'] [Algebra R' B']
    [IsScalarTower R R' A'] [IsScalarTower R R' B']
    [Algebra R A''] [Algebra R B''] [Algebra R' A''] [Algebra R' B'']
    [Algebra R'' A''] [Algebra R'' B'']
    [IsScalarTower R R' A''] [IsScalarTower R R' B'']
    [IsScalarTower R R'' A''] [IsScalarTower R R'' B'']
    [IsScalarTower R' R'' A''] [IsScalarTower R' R'' B'']
    (i : ℕ) (fA : A →ₐ[R] A') (fB : B →ₐ[R] B')
    (gA : A' →ₐ[R'] A'') (gB : B' →ₐ[R'] B'') (x : torObj R i A B),
    S.map R R'' A B A'' B'' i
        ((gA.restrictScalars R).comp fA) ((gB.restrictScalars R).comp fB) x =
      S.map R' R'' A' B' A'' B'' i gA gB (S.map R R' A B A' B' i fA fB x)
  resolution_comparison_exists : ∀ (R R' A B A' B' : Type u)
    [CommRing R] [CommRing R'] [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra R R'] [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra R B']
    [Algebra R' A'] [Algebra R' B'] [IsScalarTower R R' A'] [IsScalarTower R R' B']
    (fA : A →ₐ[R] A') (fB : B →ₐ[R] B')
    (P : ProjectiveResolution (ModuleCat.of R B))
    (Q : ProjectiveResolution (ModuleCat.of R' B')),
    ∃ (ψ : P.complex ⟶
      ((ModuleCat.restrictScalars (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj Q.complex)
      (φ : (((MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).obj
        (ModuleCat.of R A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex ⟶
        ((ModuleCat.restrictScalars (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj
          ((((MonoidalCategory.tensoringLeft (ModuleCat.{u} R')).obj
            (ModuleCat.of R' A')).mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex)),
      (∀ p : P.complex.X 0,
        (Q.π.f 0) (ψ.f 0 p) = fB ((P.π.f 0) p)) ∧
      (∀ (j : ℕ) (a : A) (p : P.complex.X j),
        φ.f j (a ⊗ₜ[R] p) = fA a ⊗ₜ[R'] (show Q.complex.X j from ψ.f j p))
  map_resolution : ∀ (R R' A B A' B' : Type u)
    [CommRing R] [CommRing R'] [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra R R'] [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra R B']
    [Algebra R' A'] [Algebra R' B'] [IsScalarTower R R' A'] [IsScalarTower R R' B']
    (i : ℕ) (fA : A →ₐ[R] A') (fB : B →ₐ[R] B')
    (P : ProjectiveResolution (ModuleCat.of R B))
    (Q : ProjectiveResolution (ModuleCat.of R' B'))
    (ψ : P.complex ⟶
      ((ModuleCat.restrictScalars (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj Q.complex)
    (φ : (((MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).obj
        (ModuleCat.of R A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex ⟶
      ((ModuleCat.restrictScalars (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj
        ((((MonoidalCategory.tensoringLeft (ModuleCat.{u} R')).obj
          (ModuleCat.of R' A')).mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex))
    (_hψ : ∀ p : P.complex.X 0,
      (Q.π.f 0) (ψ.f 0 p) = fB ((P.π.f 0) p))
    (_hφ : ∀ (j : ℕ) (a : A) (p : P.complex.X j),
      φ.f j (a ⊗ₜ[R] p) = fA a ⊗ₜ[R'] (show Q.complex.X j from ψ.f j p))
    (x : torObj R i A B),
    let F := (MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R A)
    let F' := (MonoidalCategory.tensoringLeft (ModuleCat.{u} R')).obj (ModuleCat.of R' A')
    (Q.isoLeftDerivedObj F' i).hom (S.map R R' A B A' B' i fA fB x) =
      (homologyRestrictIso R R' ((F'.mapHomologicalComplex
        (ComplexShape.down ℕ)).obj Q.complex) i).hom
        (((HomologicalComplex.homologyFunctor _ _ i).map φ)
          ((P.isoLeftDerivedObj F i).hom x))
  extension_one_tmul : ∀ (R R' A B A' B' : Type u)
    [CommRing R] [CommRing R'] [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra R R'] [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra R B']
    [Algebra R' A'] [Algebra R' B'] [IsScalarTower R R' A'] [IsScalarTower R R' B']
    (i : ℕ) (fA : A →ₐ[R] A') (fB : B →ₐ[R] B') (x : torObj R i A B),
    letI := S.action R A B i
    letI := S.action R' A' B' i
    S.extensionMap R R' A B A' B' i fA fB
        ((1 : A' ⊗[R'] B') ⊗ₜ[A ⊗[R] B] x) = S.map R R' A B A' B' i fA fB x
  flat_baseChange : ∀ (R R' A B : Type u)
    [CommRing R] [CommRing R'] [CommRing A] [CommRing B]
    [Algebra R R'] [Algebra R A] [Algebra R B] [Module.Flat R R'] (i : ℕ),
    IsIso (S.extensionMap R R' A B (R' ⊗[R] A) (R' ⊗[R] B) i
      (Algebra.TensorProduct.includeRight : A →ₐ[R] R' ⊗[R] A)
      (Algebra.TensorProduct.includeRight : B →ₐ[R] R' ⊗[R] B))
  flat_algebra_extension : ∀ (R A B A' B' : Type u)
    [CommRing R] [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra R B']
    (fA : A →ₐ[R] A') (fB : B →ₐ[R] B')
    (_hA : RingHom.Flat fA.toRingHom) (_hB : RingHom.Flat fB.toRingHom) (i : ℕ),
    IsIso (S.extensionMap R R A B A' B' i fA fB)

end TorChangeOfRings

-- The construction of the canonical system: tensor-product actions, the change-of-rings maps
-- built from lifts between projective resolutions, and the flat comparisons.
section

open CategoryTheory.Limits

open scoped ChangeOfRings

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private lemma projectiveResolutions_additive (C : Type*) [Category* C] [Abelian C]
    [HasProjectiveResolutions C] : (projectiveResolutions C).Additive where
  map_add {X Y} f g := by
    dsimp only [projectiveResolutions]
    rw [← Functor.map_add]
    apply HomotopyCategory.eq_of_homotopy
    apply ProjectiveResolution.liftHomotopy (f + g)
    · exact ProjectiveResolution.lift_commutes _ _ _
    · simp [Preadditive.add_comp, Preadditive.comp_add]

/-- Taking projective resolutions is an `R`-linear functor to the homotopy category. -/
lemma projectiveResolutions_linear (R : Type*) [Semiring R]
    (C : Type*) [Category* C] [Abelian C] [HasProjectiveResolutions C]
    [CategoryTheory.Linear R C] : (projectiveResolutions C).Linear R where
  map_smul {X Y} f r := by
    dsimp only [projectiveResolutions]
    rw [← Functor.map_smul]
    apply HomotopyCategory.eq_of_homotopy
    apply ProjectiveResolution.liftHomotopy (r • f)
    · exact ProjectiveResolution.lift_commutes _ _ _
    · ext
      simp [CategoryTheory.Linear.smul_comp, CategoryTheory.Linear.comp_smul]

/-- A homology functor of homological complexes is `R`-linear. -/
lemma homologyFunctor_linear (R : Type*) [Semiring R]
    (C : Type*) [Category* C] [Abelian C] [CategoryTheory.Linear R C]
    {ι : Type*} (c : ComplexShape ι) (i : ι) :
    (HomologicalComplex.homologyFunctor C c i).Linear R where
  map_smul f r :=
    ShortComplex.homologyMap_smul ((HomologicalComplex.shortComplexFunctor C c i).map f) r

private lemma leftDerived_additive {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasProjectiveResolutions C] (F : C ⥤ D) [F.Additive]
    (i : ℕ) : (F.leftDerived i).Additive := by
  let := projectiveResolutions_additive C
  dsimp [Functor.leftDerived, Functor.leftDerivedToHomotopyCategory]
  infer_instance

/-- The left derived functors of an `R`-linear functor are `R`-linear. -/
lemma leftDerived_linear (R : Type*) [Semiring R]
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasProjectiveResolutions C] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
    (F : C ⥤ D) [F.Additive] [F.Linear R] (i : ℕ) : (F.leftDerived i).Linear R := by
  let := projectiveResolutions_linear R C
  let := homologyFunctor_linear R D (ComplexShape.down ℕ) i
  let : (HomotopyCategory.homologyFunctor D (ComplexShape.down ℕ) i).Linear R := by
    let := Functor.linear_of_iso (R := R)
      (HomotopyCategory.homologyFunctorFactors D (ComplexShape.down ℕ) i).symm
    exact Functor.linear_of_full_essSurj_comp (HomotopyCategory.quotient D _) _
  dsimp [Functor.leftDerived, Functor.leftDerivedToHomotopyCategory]
  infer_instance

private lemma leftDerived_app_add {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasProjectiveResolutions C]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α β : F ⟶ G) (i : ℕ) (X : C) :
    (NatTrans.leftDerived (α + β) i).app X =
      (NatTrans.leftDerived α i).app X + (NatTrans.leftDerived β i).app X := by
  let P := projectiveResolution X
  rw [P.leftDerived_app_eq (α + β), P.leftDerived_app_eq α, P.leftDerived_app_eq β]
  have h : (NatTrans.mapHomologicalComplex (α + β) (ComplexShape.down ℕ)).app P.complex =
      (NatTrans.mapHomologicalComplex α _).app P.complex +
        (NatTrans.mapHomologicalComplex β _).app P.complex := rfl
  rw [h, Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

/-- Taking left derived functors of a natural transformation commutes with scalars. -/
lemma leftDerived_app_smul (R : Type*) [Semiring R]
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasProjectiveResolutions C] [CategoryTheory.Linear R D]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) (r : R) (i : ℕ) (X : C) :
    (NatTrans.leftDerived (r • α) i).app X = r • (NatTrans.leftDerived α i).app X := by
  let := homologyFunctor_linear R D (ComplexShape.down ℕ) i
  let P := projectiveResolution X
  rw [P.leftDerived_app_eq (r • α), P.leftDerived_app_eq α]
  have h : (NatTrans.mapHomologicalComplex (r • α) (ComplexShape.down ℕ)).app P.complex =
      r • (NatTrans.mapHomologicalComplex α _).app P.complex := rfl
  rw [h, Functor.map_smul, CategoryTheory.Linear.smul_comp, CategoryTheory.Linear.comp_smul]

private lemma tor_additive (R : Type u) [CommRing R] (i : ℕ) :
    (Tor (ModuleCat.{u} R) i).Additive where
  map_add {X Y} f g := by
    apply NatTrans.ext
    funext B
    show (NatTrans.leftDerived ((MonoidalCategory.tensoringLeft _).map (f + g)) i).app B = _
    rw [Functor.map_add, leftDerived_app_add]
    rfl

/-- `Tor i` on `R`-modules is an `R`-linear functor. -/
lemma tor_linear (R : Type u) [CommRing R] (i : ℕ) :
    (Tor (ModuleCat.{u} R) i).Linear R where
  map_smul f r := by
    apply NatTrans.ext
    funext B
    show (NatTrans.leftDerived ((MonoidalCategory.tensoringLeft _).map (r • f)) i).app B = _
    have h : (MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).map (r • f) =
        r • (MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).map f := by
      apply NatTrans.ext
      funext N
      apply MonoidalLinear.smul_whiskerRight
    rw [h, leftDerived_app_smul]
    rfl

private def functorEndAlgHom (R : Type u) [CommRing R]
    {C : Type*} [Category* C] [Preadditive C] [CategoryTheory.Linear R C]
    (F : C ⥤ ModuleCat.{u} R)
    [F.Additive] [F.Linear R] (X : C) : End X →ₐ[R] Module.End R (F.obj X) where
  toFun f := (F.map f).hom
  map_zero' := congrArg ModuleCat.Hom.hom (F.map_zero X X)
  map_one' := congrArg ModuleCat.Hom.hom (F.map_id X)
  map_add' f g := congrArg ModuleCat.Hom.hom (F.map_add (f := f) (g := g))
  map_mul' f g := congrArg ModuleCat.Hom.hom (F.map_comp g f)
  commutes' r := by
    change (F.map (r • 𝟙 X)).hom = r • LinearMap.id
    rw [F.map_smul, F.map_id]
    rfl

private def mulEndAlgHom (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    A →ₐ[R] End (ModuleCat.of R A) where
  toFun a := ModuleCat.ofHom (TorChangeOfRings.mulLinear R A a)
  map_zero' := by apply ModuleCat.hom_ext; ext; simp [TorChangeOfRings.mulLinear]
  map_one' := by apply ModuleCat.hom_ext; ext; simp [TorChangeOfRings.mulLinear]
  map_add' a b := by
    apply ModuleCat.hom_ext
    ext x
    change (a + b) * x = a * x + b * x
    exact add_mul a b x
  map_mul' a b := by apply ModuleCat.hom_ext; ext; simp [TorChangeOfRings.mulLinear, mul_assoc,
    End.mul_def]
  commutes' r := by
    apply ModuleCat.hom_ext
    ext x
    change algebraMap R A r * x = r • x
    exact (Algebra.smul_def r x).symm

private def torLeftAction (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℕ) :
    A →ₐ[R] Module.End R (TorChangeOfRings.torObj R i A B) := by
  letI := tor_additive R i
  letI := tor_linear R i
  letI : ((evaluation (ModuleCat.{u} R) (ModuleCat.{u} R)).obj
      (ModuleCat.of R B)).Linear R := ⟨fun _ _ => rfl⟩
  let F := Tor (ModuleCat.{u} R) i ⋙ (evaluation _ _).obj (ModuleCat.of R B)
  exact (functorEndAlgHom R F (ModuleCat.of R A)).comp (mulEndAlgHom R A)

private def torRightAction (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℕ) :
    B →ₐ[R] Module.End R (TorChangeOfRings.torObj R i A B) := by
  let F := (MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R A)
  letI := leftDerived_additive F i
  letI := leftDerived_linear R F i
  exact (functorEndAlgHom R (F.leftDerived i) (ModuleCat.of R B)).comp (mulEndAlgHom R B)

private lemma torActions_commute (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℕ) (a : A) (b : B) :
    Commute (torLeftAction R A B i a) (torRightAction R A B i b) :=
  LinearMap.ext fun x => (congrArg (fun f : End (((Tor (ModuleCat.{u} R) i).obj
    (ModuleCat.of R A)).obj (ModuleCat.of R B)) => f.asHom x)
    (((Tor (ModuleCat.{u} R) i).map
      (ModuleCat.ofHom (TorChangeOfRings.mulLinear R A a))).naturality
        (ModuleCat.ofHom (TorChangeOfRings.mulLinear R B b))))

private def torTensorAction (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℕ) :
    A ⊗[R] B →ₐ[R] Module.End R (TorChangeOfRings.torObj R i A B) :=
  Algebra.TensorProduct.lift (torLeftAction R A B i) (torRightAction R A B i)
    (torActions_commute R A B i)

@[instance_reducible] private def torModule (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℕ) :
    Module (A ⊗[R] B) (TorChangeOfRings.torObj R i A B) :=
  Module.compHom _ (torTensorAction R A B i).toRingHom

private lemma torModule_isScalarTower (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℕ) :
    let := torModule R A B i
    IsScalarTower R (A ⊗[R] B) (TorChangeOfRings.torObj R i A B) := by
  let := torModule R A B i
  refine ⟨fun r t x => ?_⟩
  show (torTensorAction R A B i (r • t)) x = r • (torTensorAction R A B i t) x
  rw [map_smul]
  rfl

private lemma torModule_tmul (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℕ) (a : A) (b : B)
    (x : TorChangeOfRings.torObj R i A B) :
    letI := torModule R A B i
    (a ⊗ₜ[R] b) • x =
      (((Tor (ModuleCat.{u} R) i).map (ModuleCat.ofHom (TorChangeOfRings.mulLinear R A a))).app
          (ModuleCat.of R B) ≫
        ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R A)).map
          (ModuleCat.ofHom (TorChangeOfRings.mulLinear R B b))) x := by
  show (torTensorAction R A B i (a ⊗ₜ[R] b)) x = _
  rw [torTensorAction, Algebra.TensorProduct.lift_tmul]
  exact congrArg (fun f : Module.End R (TorChangeOfRings.torObj R i A B) => f x)
    (torActions_commute R A B i a b).eq

private lemma exists_chainMap_lift {C : Type*} [Category* C] [Abelian C]
    (P Q : ChainComplex C ℕ) [∀ n, Projective (P.X n)] {Y : C}
    (q : Q.X 0 ⟶ Y) [Epi q] (hq : Q.d 1 0 ≫ q = 0)
    (h₀ : (ShortComplex.mk (Q.d 1 0) q hq).Exact)
    (hQ : ∀ n, (ShortComplex.mk (Q.d (n + 2) (n + 1)) (Q.d (n + 1) n)
      (Q.d_comp_d _ _ _)).Exact)
    (f : P.X 0 ⟶ Y) (hf : P.d 1 0 ≫ f = 0) :
    ∃ ψ : P ⟶ Q, ψ.f 0 ≫ q = f := by
  let ψ₀ := Projective.factorThru f q
  have hψ₀ : ψ₀ ≫ q = f := Projective.factorThru_comp _ _
  let ψ₁ := h₀.liftFromProjective (P.d 1 0 ≫ ψ₀) (by simp [hψ₀, hf])
  have hψ₁ : ψ₁ ≫ Q.d 1 0 = P.d 1 0 ≫ ψ₀ := h₀.liftFromProjective_comp _ _
  let ψ : P ⟶ Q := ChainComplex.mkHom P Q ψ₀ ψ₁ hψ₁ fun n ⟨g, g', w⟩ =>
    ⟨(hQ n).liftFromProjective (P.d (n + 2) (n + 1) ≫ g') (by simp [w]),
      (hQ n).liftFromProjective_comp _ _⟩
  exact ⟨ψ, hψ₀⟩

private lemma nonempty_homotopy_zero_of_augmentation {C : Type*} [Category* C] [Abelian C]
    {P Q : ChainComplex C ℕ} [∀ n, Projective (P.X n)] {Y : C}
    (q : Q.X 0 ⟶ Y) (hq : Q.d 1 0 ≫ q = 0)
    (h₀ : (ShortComplex.mk (Q.d 1 0) q hq).Exact)
    (hQ : ∀ n, (ShortComplex.mk (Q.d (n + 2) (n + 1)) (Q.d (n + 1) n)
      (Q.d_comp_d _ _ _)).Exact)
    (f : P ⟶ Q) (hf : f.f 0 ≫ q = 0) : Nonempty (Homotopy f 0) := by
  let s₀ := h₀.liftFromProjective (f.f 0) hf
  have hs₀ : s₀ ≫ Q.d 1 0 = f.f 0 := h₀.liftFromProjective_comp _ _
  let s₁ := (hQ 0).liftFromProjective (f.f 1 - P.d 1 0 ≫ s₀)
    (by simp [Preadditive.sub_comp, hs₀])
  have hs₁ : s₁ ≫ Q.d 2 1 = f.f 1 - P.d 1 0 ≫ s₀ :=
    (hQ 0).liftFromProjective_comp _ _
  refine ⟨Homotopy.mkInductive f s₀ hs₀.symm s₁ (by rw [hs₁]; abel) ?_⟩
  rintro n ⟨g, g', w⟩
  have hz : (f.f (n + 2) - P.d (n + 2) (n + 1) ≫ g') ≫ Q.d (n + 2) (n + 1) = 0 := by
    simp [Preadditive.sub_comp, w]
  refine ⟨(hQ (n + 1)).liftFromProjective _ hz, ?_⟩
  rw [(hQ (n + 1)).liftFromProjective_comp]
  abel

private lemma nonempty_homotopy_of_augmentation {C : Type*} [Category* C] [Abelian C]
    {P Q : ChainComplex C ℕ} [∀ n, Projective (P.X n)] {Y : C}
    (q : Q.X 0 ⟶ Y) (hq : Q.d 1 0 ≫ q = 0)
    (h₀ : (ShortComplex.mk (Q.d 1 0) q hq).Exact)
    (hQ : ∀ n, (ShortComplex.mk (Q.d (n + 2) (n + 1)) (Q.d (n + 1) n)
      (Q.d_comp_d _ _ _)).Exact)
    (f g : P ⟶ Q) (hfg : f.f 0 ≫ q = g.f 0 ≫ q) : Nonempty (Homotopy f g) := by
  obtain ⟨h⟩ := nonempty_homotopy_zero_of_augmentation q hq h₀ hQ (f - g)
    (by simpa using sub_eq_zero.mpr hfg)
  exact ⟨Homotopy.equivSubZero.invFun h⟩

private def tensorRestrictScalars {R S : Type u} [CommRing R] [CommRing S]
    (ρ : R →+* S) {M : ModuleCat.{u} R} {M' : ModuleCat.{u} S}
    (f : M →ₛₗ[ρ] M') :
    ModuleCat.restrictScalars ρ ⋙ (MonoidalCategory.tensoringLeft _).obj M ⟶
      (MonoidalCategory.tensoringLeft _).obj M' ⋙ ModuleCat.restrictScalars ρ where
  app N := ModuleCat.semilinearMapAddEquiv ρ _ _
    (TensorProduct.map f ((ModuleCat.semilinearMapAddEquiv ρ _ _).symm (𝟙 _)))
  naturality {N N'} g := by
    apply ModuleCat.hom_ext
    exact TensorProduct.ext' fun _ _ => rfl

private def tensorComplexMap {R S : Type u} [CommRing R] [CommRing S]
    (ρ : R →+* S) {M : ModuleCat.{u} R} {M' : ModuleCat.{u} S}
    (f : M →ₛₗ[ρ] M') {P : ChainComplex (ModuleCat.{u} R) ℕ}
    {Q : ChainComplex (ModuleCat.{u} S) ℕ}
    (ψ : P ⟶ ((ModuleCat.restrictScalars ρ).mapHomologicalComplex _).obj Q) :
    (((MonoidalCategory.tensoringLeft _).obj M).mapHomologicalComplex _).obj P ⟶
      ((ModuleCat.restrictScalars ρ).mapHomologicalComplex _).obj
        ((((MonoidalCategory.tensoringLeft _).obj M').mapHomologicalComplex _).obj Q) :=
  (((MonoidalCategory.tensoringLeft _).obj M).mapHomologicalComplex _).map ψ ≫
    (NatTrans.mapHomologicalComplex (tensorRestrictScalars ρ f) _).app Q

private lemma tensorComplexMap_tmul {R S : Type u} [CommRing R] [CommRing S]
    (ρ : R →+* S) {M : ModuleCat.{u} R} {M' : ModuleCat.{u} S}
    (f : M →ₛₗ[ρ] M') {P : ChainComplex (ModuleCat.{u} R) ℕ}
    {Q : ChainComplex (ModuleCat.{u} S) ℕ}
    (ψ : P ⟶ ((ModuleCat.restrictScalars ρ).mapHomologicalComplex _).obj Q)
    (j : ℕ) (m : M) (p : P.X j) :
    (tensorComplexMap ρ f ψ).f j (m ⊗ₜ[R] p) =
      f m ⊗ₜ[S] (show Q.X j from ψ.f j p) := rfl

private def tensorComplexMap_homotopy {R S : Type u} [CommRing R] [CommRing S]
    (ρ : R →+* S) {M : ModuleCat.{u} R} {M' : ModuleCat.{u} S}
    (f : M →ₛₗ[ρ] M') {P : ChainComplex (ModuleCat.{u} R) ℕ}
    {Q : ChainComplex (ModuleCat.{u} S) ℕ}
    {ψ ψ' : P ⟶ ((ModuleCat.restrictScalars ρ).mapHomologicalComplex _).obj Q}
    (h : Homotopy ψ ψ') :
    Homotopy (tensorComplexMap ρ f ψ) (tensorComplexMap ρ f ψ') :=
  ((((MonoidalCategory.tensoringLeft _).obj M).mapHomotopy h)).compRight
    ((NatTrans.mapHomologicalComplex (tensorRestrictScalars ρ f) _).app Q)

private def algHomSemilinear {R S A B : Type u} [CommRing R] [CommRing S]
    [CommRing A] [CommRing B] [Algebra R S] [Algebra R A] [Algebra R B]
    [Algebra S B] [IsScalarTower R S B] (f : A →ₐ[R] B) :
    A →ₛₗ[algebraMap R S] B where
  toFun := f
  map_add' := f.map_add
  map_smul' r a := by
    rw [map_smul]
    exact (IsScalarTower.algebraMap_smul S r (f a)).symm

private lemma resolution_lift_exists {R S : Type u} [CommRing R] [CommRing S]
    (ρ : R →+* S) {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (f : M →ₛₗ[ρ] N) (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    ∃ ψ : P.complex ⟶ ((ModuleCat.restrictScalars ρ).mapHomologicalComplex _).obj Q.complex,
      ∀ p : P.complex.X 0, Q.π.f 0 (ψ.f 0 p) = f (P.π.f 0 p) := by
  let F := ModuleCat.restrictScalars ρ
  let f' := ModuleCat.semilinearMapAddEquiv ρ M N f
  obtain ⟨ψ, hψ⟩ := exists_chainMap_lift P.complex
    ((F.mapHomologicalComplex _).obj Q.complex) (F.map (Q.π.f 0))
    (by
      show F.map (Q.complex.d 1 0) ≫ F.map (Q.π.f 0) = 0
      rw [← F.map_comp, Q.complex_d_comp_π_f_zero, F.map_zero])
    (Q.exact₀.map F) (fun n => (Q.exact_succ n).map F)
    (P.π.f 0 ≫ f') (by simp)
  exact ⟨ψ, fun p => congrArg (fun g : P.complex.X 0 ⟶ F.obj N => g p) hψ⟩

private lemma resolution_lift_homotopy {R S : Type u} [CommRing R] [CommRing S]
    (ρ : R →+* S) {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
    (ψ ψ' : P.complex ⟶ ((ModuleCat.restrictScalars ρ).mapHomologicalComplex _).obj Q.complex)
    (hψ : ∀ p : P.complex.X 0, Q.π.f 0 (ψ.f 0 p) = Q.π.f 0 (ψ'.f 0 p)) :
    Nonempty (Homotopy ψ ψ') := by
  let F := ModuleCat.restrictScalars ρ
  exact nonempty_homotopy_of_augmentation (F.map (Q.π.f 0))
    (by
      show F.map (Q.complex.d 1 0) ≫ F.map (Q.π.f 0) = 0
      rw [← F.map_comp, Q.complex_d_comp_π_f_zero, F.map_zero])
    (Q.exact₀.map F) (fun n => (Q.exact_succ n).map F) ψ ψ'
    (ModuleCat.hom_ext (LinearMap.ext hψ))

/-- Chain maps out of a tensored complex are determined by their values on pure tensors. -/
private lemma tensorComplex_hom_ext {R : Type u} [CommRing R] {M : ModuleCat.{u} R}
    {P K : ChainComplex (ModuleCat.{u} R) ℕ}
    {f g : (((MonoidalCategory.tensoringLeft _).obj M).mapHomologicalComplex _).obj P ⟶ K}
    (h : ∀ j (m : M) (p : P.X j), f.f j (m ⊗ₜ[R] p) = g.f j (m ⊗ₜ[R] p)) : f = g := by
  apply HomologicalComplex.Hom.ext
  funext j
  apply ModuleCat.hom_ext
  exact TensorProduct.ext' (h j)

private lemma tensorComplexMap_eq_of_tmul {R S : Type u} [CommRing R] [CommRing S]
    (ρ : R →+* S) {M : ModuleCat.{u} R} {M' : ModuleCat.{u} S}
    (f : M →ₛₗ[ρ] M') {P : ChainComplex (ModuleCat.{u} R) ℕ}
    {Q : ChainComplex (ModuleCat.{u} S) ℕ}
    (ψ : P ⟶ ((ModuleCat.restrictScalars ρ).mapHomologicalComplex _).obj Q)
    (φ : (((MonoidalCategory.tensoringLeft _).obj M).mapHomologicalComplex _).obj P ⟶
      ((ModuleCat.restrictScalars ρ).mapHomologicalComplex _).obj
        ((((MonoidalCategory.tensoringLeft _).obj M').mapHomologicalComplex _).obj Q))
    (hφ : ∀ j (m : M) (p : P.X j), φ.f j (m ⊗ₜ[R] p) =
      f m ⊗ₜ[S] (show Q.X j from ψ.f j p)) : φ = tensorComplexMap ρ f ψ :=
  tensorComplex_hom_ext hφ

private def torMapOfLift {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {M N : ModuleCat.{u} R} {M' N' : ModuleCat.{u} S}
    (f : M →ₛₗ[algebraMap R S] M') (P : ProjectiveResolution N) (Q : ProjectiveResolution N')
    (ψ : P.complex ⟶ ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex _).obj
      Q.complex) (i : ℕ) :
    ((Tor (ModuleCat.{u} R) i).obj M).obj N →ₛₗ[algebraMap R S]
      ((Tor (ModuleCat.{u} S) i).obj M').obj N' :=
  (ModuleCat.semilinearMapAddEquiv (algebraMap R S) _ _).symm
    ((P.isoLeftDerivedObj ((MonoidalCategory.tensoringLeft _).obj M) i).hom ≫
      (HomologicalComplex.homologyFunctor _ _ i).map
        (tensorComplexMap (algebraMap R S) f ψ) ≫
      (TorChangeOfRings.homologyRestrictIso R S
        ((((MonoidalCategory.tensoringLeft _).obj M').mapHomologicalComplex _).obj Q.complex) i).hom
          ≫
      (ModuleCat.restrictScalars (algebraMap R S)).map
        (Q.isoLeftDerivedObj ((MonoidalCategory.tensoringLeft _).obj M') i).inv)

private lemma torMapOfLift_resolution {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {M N : ModuleCat.{u} R} {M' N' : ModuleCat.{u} S}
    (f : M →ₛₗ[algebraMap R S] M') (P : ProjectiveResolution N) (Q : ProjectiveResolution N')
    (ψ : P.complex ⟶ ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex _).obj
      Q.complex) (i : ℕ) (x : ((Tor (ModuleCat.{u} R) i).obj M).obj N) :
    (Q.isoLeftDerivedObj ((MonoidalCategory.tensoringLeft _).obj M') i).hom
        (torMapOfLift f P Q ψ i x) =
      (TorChangeOfRings.homologyRestrictIso R S
        ((((MonoidalCategory.tensoringLeft _).obj M').mapHomologicalComplex _).obj Q.complex) i).hom
          (((HomologicalComplex.homologyFunctor _ _ i).map
            (tensorComplexMap (algebraMap R S) f ψ))
              ((P.isoLeftDerivedObj ((MonoidalCategory.tensoringLeft _).obj M) i).hom x)) :=
  CategoryTheory.Iso.inv_hom_id_apply
    (Q.isoLeftDerivedObj ((MonoidalCategory.tensoringLeft _).obj M') i) _

private lemma torMapOfLift_eq_of_homotopy {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {M N : ModuleCat.{u} R} {M' N' : ModuleCat.{u} S}
    (f : M →ₛₗ[algebraMap R S] M') (P : ProjectiveResolution N) (Q : ProjectiveResolution N')
    {ψ ψ' : P.complex ⟶ ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex _).obj
      Q.complex} (h : Homotopy ψ ψ') (i : ℕ) :
    torMapOfLift f P Q ψ i = torMapOfLift f P Q ψ' i := by
  have hh := Homotopy.homologyMap_eq (tensorComplexMap_homotopy (algebraMap R S) f h) i
  dsimp only [torMapOfLift, HomologicalComplex.homologyFunctor_map]
  rw [hh]

private lemma torMapOfLift_eq_of_augmentation {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] {M N : ModuleCat.{u} R} {M' N' : ModuleCat.{u} S}
    (f : M →ₛₗ[algebraMap R S] M') (P : ProjectiveResolution N) (Q : ProjectiveResolution N')
    {ψ ψ' : P.complex ⟶ ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex _).obj
      Q.complex}
    (hψ : ∀ p : P.complex.X 0, Q.π.f 0 (ψ.f 0 p) = Q.π.f 0 (ψ'.f 0 p)) (i : ℕ) :
    torMapOfLift f P Q ψ i = torMapOfLift f P Q ψ' i := by
  obtain ⟨h⟩ := resolution_lift_homotopy (algebraMap R S) P Q ψ ψ' hψ
  exact torMapOfLift_eq_of_homotopy f P Q h i

private lemma tensorComplexMap_precomp {R S : Type u} [CommRing R] [CommRing S]
    (ρ : R →+* S) {M : ModuleCat.{u} R} {M' : ModuleCat.{u} S}
    (f : M →ₛₗ[ρ] M') {P₀ P : ChainComplex (ModuleCat.{u} R) ℕ}
    {Q : ChainComplex (ModuleCat.{u} S) ℕ} (α : P₀ ⟶ P)
    (ψ : P ⟶ ((ModuleCat.restrictScalars ρ).mapHomologicalComplex _).obj Q) :
    tensorComplexMap ρ f (α ≫ ψ) =
      (((MonoidalCategory.tensoringLeft _).obj M).mapHomologicalComplex _).map α ≫
        tensorComplexMap ρ f ψ := by
  simp only [tensorComplexMap, Functor.map_comp, Category.assoc]

private lemma tensorComplexMap_postcomp {R S : Type u} [CommRing R] [CommRing S]
    (ρ : R →+* S) {M : ModuleCat.{u} R} {M' : ModuleCat.{u} S}
    (f : M →ₛₗ[ρ] M') {P : ChainComplex (ModuleCat.{u} R) ℕ}
    {Q Q' : ChainComplex (ModuleCat.{u} S) ℕ}
    (ψ : P ⟶ ((ModuleCat.restrictScalars ρ).mapHomologicalComplex _).obj Q) (β : Q ⟶ Q') :
    tensorComplexMap ρ f
        (ψ ≫ ((ModuleCat.restrictScalars ρ).mapHomologicalComplex _).map β) =
      tensorComplexMap ρ f ψ ≫
        ((ModuleCat.restrictScalars ρ).mapHomologicalComplex _).map
          ((((MonoidalCategory.tensoringLeft _).obj M').mapHomologicalComplex _).map β) :=
  tensorComplex_hom_ext fun _ _ _ => rfl

private lemma homologyRestrictIso_naturality {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] {K L : ChainComplex (ModuleCat.{u} S) ℕ} (φ : K ⟶ L) (i : ℕ) :
    (HomologicalComplex.homologyFunctor _ _ i).map
        (((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex _).map φ) ≫
        (TorChangeOfRings.homologyRestrictIso R S L i).hom =
      (TorChangeOfRings.homologyRestrictIso R S K i).hom ≫
        (ModuleCat.restrictScalars (algebraMap R S)).map
          ((HomologicalComplex.homologyFunctor _ _ i).map φ) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ i).map φ)
    (ModuleCat.restrictScalars (algebraMap R S))

private lemma torMapOfLift_precomp {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {M N : ModuleCat.{u} R} {M' N' : ModuleCat.{u} S}
    (f : M →ₛₗ[algebraMap R S] M') (P₀ P : ProjectiveResolution N) (Q : ProjectiveResolution N')
    (α : P₀.complex ⟶ P.complex) (hα : α.f 0 ≫ P.π.f 0 = P₀.π.f 0)
    (ψ : P.complex ⟶ ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex _).obj
      Q.complex) (i : ℕ) :
    torMapOfLift f P₀ Q (α ≫ ψ) i = torMapOfLift f P Q ψ i := by
  have h := ProjectiveResolution.isoLeftDerivedObj_hom_naturality (𝟙 N) P₀ P α
    (by simpa using hα) ((MonoidalCategory.tensoringLeft _).obj M) i
  rw [(((MonoidalCategory.tensoringLeft _).obj M).leftDerived i).map_id N,
    Category.id_comp] at h
  dsimp only [Functor.comp_map] at h
  simp only [torMapOfLift, tensorComplexMap_precomp, Functor.map_comp]
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, ← h]
  simp only [Category.assoc]

private lemma torMapOfLift_postcomp {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {M N : ModuleCat.{u} R} {M' N' : ModuleCat.{u} S}
    (f : M →ₛₗ[algebraMap R S] M') (P : ProjectiveResolution N) (Q Q' : ProjectiveResolution N')
    (ψ : P.complex ⟶ ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex _).obj
      Q.complex) (β : Q.complex ⟶ Q'.complex) (hβ : β.f 0 ≫ Q'.π.f 0 = Q.π.f 0) (i : ℕ) :
    torMapOfLift f P Q'
      (ψ ≫ ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex _).map β) i =
        torMapOfLift f P Q ψ i := by
  have h := ProjectiveResolution.isoLeftDerivedObj_inv_naturality (𝟙 N') Q Q' β
    (by simpa using hβ) ((MonoidalCategory.tensoringLeft _).obj M') i
  rw [(((MonoidalCategory.tensoringLeft _).obj M').leftDerived i).map_id N',
    Category.comp_id] at h
  dsimp only [Functor.comp_map] at h
  simp only [torMapOfLift, tensorComplexMap_postcomp, Functor.map_comp, Category.assoc]
  have hη := homologyRestrictIso_naturality (R := R)
    ((((MonoidalCategory.tensoringLeft _).obj M').mapHomologicalComplex _).map β) i
  rw [reassoc_of% hη, ← Functor.map_comp, ← h]

private def torMap {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {M N : ModuleCat.{u} R} {M' N' : ModuleCat.{u} S}
    (f : M →ₛₗ[algebraMap R S] M') (g : N →ₛₗ[algebraMap R S] N') (i : ℕ) :
    ((Tor (ModuleCat.{u} R) i).obj M).obj N →ₛₗ[algebraMap R S]
      ((Tor (ModuleCat.{u} S) i).obj M').obj N' :=
  torMapOfLift f (projectiveResolution N) (projectiveResolution N')
    (Classical.choose (resolution_lift_exists (algebraMap R S) g
      (projectiveResolution N) (projectiveResolution N'))) i

private lemma torMap_eq_of_lift {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {M N : ModuleCat.{u} R} {M' N' : ModuleCat.{u} S}
    (f : M →ₛₗ[algebraMap R S] M') (g : N →ₛₗ[algebraMap R S] N')
    (P : ProjectiveResolution N) (Q : ProjectiveResolution N')
    (ψ : P.complex ⟶ ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex _).obj
      Q.complex)
    (hψ : ∀ p : P.complex.X 0, Q.π.f 0 (ψ.f 0 p) = g (P.π.f 0 p)) (i : ℕ) :
    torMap f g i = torMapOfLift f P Q ψ i := by
  let P₀ := projectiveResolution N
  let Q₀ := projectiveResolution N'
  let α := ProjectiveResolution.lift (𝟙 N) P₀ P
  let β := ProjectiveResolution.lift (𝟙 N') Q Q₀
  have hα : α.f 0 ≫ P.π.f 0 = P₀.π.f 0 :=
    (ProjectiveResolution.lift_commutes_zero (𝟙 N) P₀ P).trans (Category.comp_id _)
  have hβ : β.f 0 ≫ Q₀.π.f 0 = Q.π.f 0 :=
    (ProjectiveResolution.lift_commutes_zero (𝟙 N') Q Q₀).trans (Category.comp_id _)
  let χ := (α ≫ ψ) ≫
    ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex _).map β
  have hχ (p : P₀.complex.X 0) : Q₀.π.f 0 (χ.f 0 p) = g (P₀.π.f 0 p) := by
    have hαp := congrArg (fun t : P₀.complex.X 0 ⟶ N => t p) hα
    have hβp := congrArg (fun t : Q.complex.X 0 ⟶ N' => t (ψ.f 0 (α.f 0 p))) hβ
    exact hβp.trans ((hψ _).trans (congrArg g hαp))
  calc
    torMap f g i = torMapOfLift f P₀ Q₀ χ i := by
      apply torMapOfLift_eq_of_augmentation
      intro p
      exact (Classical.choose_spec (resolution_lift_exists (algebraMap R S) g P₀ Q₀) p).trans
        (hχ p).symm
    _ = torMapOfLift f P₀ Q (α ≫ ψ) i := torMapOfLift_postcomp f P₀ Q Q₀ _ β hβ i
    _ = torMapOfLift f P Q ψ i := torMapOfLift_precomp f P₀ P Q α hα ψ i

private lemma resolution_comparison_exists
    (R R' A B A' B' : Type u)
    [CommRing R] [CommRing R'] [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra R R'] [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra R B']
    [Algebra R' A'] [Algebra R' B'] [IsScalarTower R R' A'] [IsScalarTower R R' B']
    (fA : A →ₐ[R] A') (fB : B →ₐ[R] B')
    (P : ProjectiveResolution (ModuleCat.of R B))
    (Q : ProjectiveResolution (ModuleCat.of R' B')) :
    ∃ (ψ : P.complex ⟶
      ((ModuleCat.restrictScalars (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj Q.complex)
      (φ : (((MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).obj
        (ModuleCat.of R A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex ⟶
        ((ModuleCat.restrictScalars (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj
          ((((MonoidalCategory.tensoringLeft (ModuleCat.{u} R')).obj
            (ModuleCat.of R' A')).mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex)),
      (∀ p : P.complex.X 0,
        (Q.π.f 0) (ψ.f 0 p) = fB ((P.π.f 0) p)) ∧
      (∀ (j : ℕ) (a : A) (p : P.complex.X j),
        φ.f j (a ⊗ₜ[R] p) = fA a ⊗ₜ[R'] (show Q.complex.X j from ψ.f j p)) := by
  obtain ⟨ψ, hψ⟩ := resolution_lift_exists (algebraMap R R') (algHomSemilinear fB) P Q
  exact ⟨ψ, tensorComplexMap (algebraMap R R') (algHomSemilinear fA) ψ,
    hψ, fun _ _ _ => rfl⟩

private lemma leftDerived_app_comp_iso_hom {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasProjectiveResolutions C]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) {X : C}
    (P : ProjectiveResolution X) (i : ℕ) :
    (NatTrans.leftDerived α i).app X ≫ (P.isoLeftDerivedObj G i).hom =
      (P.isoLeftDerivedObj F i).hom ≫
        (HomologicalComplex.homologyFunctor _ _ i).map
          ((NatTrans.mapHomologicalComplex α _).app P.complex) := by
  rw [P.leftDerived_app_eq α]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private lemma iso_inv_comp_leftDerived_app {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasProjectiveResolutions C]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) {X : C}
    (P : ProjectiveResolution X) (i : ℕ) :
    (P.isoLeftDerivedObj F i).inv ≫ (NatTrans.leftDerived α i).app X =
      (HomologicalComplex.homologyFunctor _ _ i).map
          ((NatTrans.mapHomologicalComplex α _).app P.complex) ≫
        (P.isoLeftDerivedObj G i).inv := by
  rw [P.leftDerived_app_eq α, Iso.inv_hom_id_assoc]

private lemma torMapOfLift_naturality_left {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] {M N : ModuleCat.{u} R} {M' N' : ModuleCat.{u} S}
    (f : M →ₛₗ[algebraMap R S] M') (P : ProjectiveResolution N) (Q : ProjectiveResolution N')
    (ψ : P.complex ⟶ ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex _).obj
      Q.complex) (a : M ⟶ M) (a' : M' ⟶ M') (hf : ∀ m, f (a m) = a' (f m)) (i : ℕ) :
    ((Tor (ModuleCat.{u} R) i).map a).app N ≫
        ModuleCat.semilinearMapAddEquiv (algebraMap R S) _ _ (torMapOfLift f P Q ψ i) =
      ModuleCat.semilinearMapAddEquiv (algebraMap R S) _ _ (torMapOfLift f P Q ψ i) ≫
        (ModuleCat.restrictScalars (algebraMap R S)).map (((Tor (ModuleCat.{u} S) i).map a').app N')
          := by
  let τ := (MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).map a
  let τ' := (MonoidalCategory.tensoringLeft (ModuleCat.{u} S)).map a'
  let κ := (NatTrans.mapHomologicalComplex τ (ComplexShape.down ℕ)).app P.complex
  let κ' := (NatTrans.mapHomologicalComplex τ' (ComplexShape.down ℕ)).app Q.complex
  have hκ : κ ≫ tensorComplexMap (algebraMap R S) f ψ =
      tensorComplexMap (algebraMap R S) f ψ ≫
        ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex _).map κ' := by
    exact tensorComplex_hom_ext fun j m p =>
      congrArg (fun z : M' => z ⊗ₜ[S] (show Q.complex.X j from ψ.f j p)) (hf m)
  have hκH := congrArg ((HomologicalComplex.homologyFunctor _ _ i).map) hκ
  simp only [Functor.map_comp] at hκH
  have hη := homologyRestrictIso_naturality (R := R) κ' i
  have ha := leftDerived_app_comp_iso_hom τ P i
  have ha' := iso_inv_comp_leftDerived_app τ' Q i
  show (NatTrans.leftDerived τ i).app N ≫ _ = _ ≫
    (ModuleCat.restrictScalars (algebraMap R S)).map ((NatTrans.leftDerived τ' i).app N')
  simp only [torMapOfLift, AddEquiv.apply_symm_apply, Category.assoc]
  rw [reassoc_of% ha, reassoc_of% hκH, reassoc_of% hη]
  rw [← Functor.map_comp, ← ha', Functor.map_comp]

private lemma torMapOfLift_naturality_right {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] {M N : ModuleCat.{u} R} {M' N' : ModuleCat.{u} S}
    (f : M →ₛₗ[algebraMap R S] M') (g : N →ₛₗ[algebraMap R S] N')
    (P : ProjectiveResolution N) (Q : ProjectiveResolution N')
    (ψ : P.complex ⟶ ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex _).obj
      Q.complex) (hψ : ∀ p, Q.π.f 0 (ψ.f 0 p) = g (P.π.f 0 p))
    (a : N ⟶ N) (a' : N' ⟶ N') (hg : ∀ n, g (a n) = a' (g n)) (i : ℕ) :
    ((Tor (ModuleCat.{u} R) i).obj M).map a ≫
        ModuleCat.semilinearMapAddEquiv (algebraMap R S) _ _ (torMapOfLift f P Q ψ i) =
      ModuleCat.semilinearMapAddEquiv (algebraMap R S) _ _ (torMapOfLift f P Q ψ i) ≫
        (ModuleCat.restrictScalars (algebraMap R S)).map (((Tor (ModuleCat.{u} S) i).obj M').map a')
          := by
  let α := ProjectiveResolution.lift a P P
  let β := ProjectiveResolution.lift a' Q Q
  let F := (MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).obj M
  let F' := (MonoidalCategory.tensoringLeft (ModuleCat.{u} S)).obj M'
  have hα : α.f 0 ≫ P.π.f 0 = P.π.f 0 ≫ a := ProjectiveResolution.lift_commutes_zero a P P
  have hβ : β.f 0 ≫ Q.π.f 0 = Q.π.f 0 ≫ a' := ProjectiveResolution.lift_commutes_zero a' Q Q
  have hψ' : ∀ p, Q.π.f 0 ((α ≫ ψ).f 0 p) = Q.π.f 0
      ((ψ ≫ ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex _).map β).f 0 p) :=
        by
    intro p
    have hαp := congrArg (fun t : P.complex.X 0 ⟶ N => t p) hα
    have hβp := congrArg (fun t : Q.complex.X 0 ⟶ N' => t (ψ.f 0 p)) hβ
    exact (hψ _).trans ((congrArg g hαp).trans
      ((hg _).trans ((congrArg (fun z => a' z) (hψ p).symm).trans hβp.symm)))
  obtain ⟨hH⟩ := resolution_lift_homotopy (algebraMap R S) P Q _ _ hψ'
  have hκH := Homotopy.homologyMap_eq (tensorComplexMap_homotopy (algebraMap R S) f hH) i
  change (HomologicalComplex.homologyFunctor _ _ i).map _ =
    (HomologicalComplex.homologyFunctor _ _ i).map _ at hκH
  rw [tensorComplexMap_precomp, tensorComplexMap_postcomp, Functor.map_comp,
    Functor.map_comp] at hκH
  have hη := homologyRestrictIso_naturality (R := R) ((F'.mapHomologicalComplex _).map β) i
  have ha := ProjectiveResolution.isoLeftDerivedObj_hom_naturality a P P α hα F i
  have ha' := ProjectiveResolution.isoLeftDerivedObj_inv_naturality a' Q Q β hβ F' i
  dsimp only [Functor.comp_map] at ha ha'
  show (F.leftDerived i).map a ≫ _ = _ ≫
    (ModuleCat.restrictScalars (algebraMap R S)).map ((F'.leftDerived i).map a')
  simp only [torMapOfLift, AddEquiv.apply_symm_apply, Category.assoc]
  rw [reassoc_of% ha, reassoc_of% hκH, reassoc_of% hη]
  rw [← Functor.map_comp, ← ha', Functor.map_comp]

section AlgebraMaps

variable (R S A B A' B' : Type u)
  [CommRing R] [CommRing S] [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra R B']
  [Algebra S A'] [Algebra S B'] [IsScalarTower R S A'] [IsScalarTower R S B']
  (fA : A →ₐ[R] A') (fB : B →ₐ[R] B')

private abbrev algebraTorMap (i : ℕ) : TorChangeOfRings.torObj R i A B →ₛₗ[algebraMap R S]
    TorChangeOfRings.torObj S i A' B' :=
  torMap (M := ModuleCat.of R A) (N := ModuleCat.of R B)
    (M' := ModuleCat.of S A') (N' := ModuleCat.of S B')
    (algHomSemilinear fA) (algHomSemilinear fB) i

private lemma algebraTorMap_mul_left (i : ℕ) (a : A) (x : TorChangeOfRings.torObj R i A B) :
    algebraTorMap R S A B A' B' fA fB i (torLeftAction R A B i a x) =
      torLeftAction S A' B' i (fA a) (algebraTorMap R S A B A' B' fA fB i x) := by
  let P := projectiveResolution (ModuleCat.of R B)
  let Q := projectiveResolution (ModuleCat.of S B')
  let ψ := Classical.choose (resolution_lift_exists (algebraMap R S) (algHomSemilinear fB) P Q)
  have h := torMapOfLift_naturality_left (algHomSemilinear fA) P Q ψ
    (ModuleCat.ofHom (TorChangeOfRings.mulLinear R A a))
    (ModuleCat.ofHom (TorChangeOfRings.mulLinear S A' (fA a)))
    (fun m => fA.map_mul a m) i
  exact ConcreteCategory.congr_hom h x

private lemma algebraTorMap_mul_right (i : ℕ) (b : B) (x : TorChangeOfRings.torObj R i A B) :
    algebraTorMap R S A B A' B' fA fB i (torRightAction R A B i b x) =
      torRightAction S A' B' i (fB b) (algebraTorMap R S A B A' B' fA fB i x) := by
  let P := projectiveResolution (ModuleCat.of R B)
  let Q := projectiveResolution (ModuleCat.of S B')
  let ψ := Classical.choose (resolution_lift_exists (algebraMap R S) (algHomSemilinear fB) P Q)
  have hψ := Classical.choose_spec (resolution_lift_exists (algebraMap R S) (algHomSemilinear fB) P
    Q)
  have h := torMapOfLift_naturality_right (M := ModuleCat.of R A) (M' := ModuleCat.of S A')
    (algHomSemilinear fA) (algHomSemilinear fB) P Q ψ hψ
    (ModuleCat.ofHom (TorChangeOfRings.mulLinear R B b))
    (ModuleCat.ofHom (TorChangeOfRings.mulLinear S B' (fB b)))
    (fun n => fB.map_mul b n) i
  exact ConcreteCategory.congr_hom h x

private lemma algebraTorMap_smul (i : ℕ) (t : A ⊗[R] B) (x : TorChangeOfRings.torObj R i A B) :
    let := torModule R A B i
    let := torModule S A' B' i
    algebraTorMap R S A B A' B' fA fB i (t • x) =
      TorChangeOfRings.tensorProductMap R S A B A' B' fA fB t •
        algebraTorMap R S A B A' B' fA fB i x := by
  let := torModule R A B i
  let := torModule S A' B' i
  induction t using TensorProduct.induction_on with
  | zero => simp only [zero_smul, map_zero]
  | add t t' ht ht' => simp only [add_smul, map_add, ht, ht']
  | tmul a b =>
    have ht : TorChangeOfRings.tensorProductMap R S A B A' B' fA fB (a ⊗ₜ[R] b) =
        fA a ⊗ₜ[S] fB b := by
      simp [TorChangeOfRings.tensorProductMap]
    rw [ht]
    show algebraTorMap R S A B A' B' fA fB i
        ((torLeftAction R A B i a) ((torRightAction R A B i b) x)) =
      torLeftAction S A' B' i (fA a)
        (torRightAction S A' B' i (fB b) (algebraTorMap R S A B A' B' fA fB i x))
    rw [algebraTorMap_mul_left, algebraTorMap_mul_right]

private def tensorLinearTorMap (i : ℕ) :
    letI := torModule R A B i
    letI := torModule S A' B' i
    TorChangeOfRings.torObj R i A B →ₛₗ[TorChangeOfRings.tensorProductMap R S A B A' B' fA fB]
      TorChangeOfRings.torObj S i A' B' := by
  letI := torModule R A B i
  letI := torModule S A' B' i
  exact
    { toFun := algebraTorMap R S A B A' B' fA fB i
      map_add' := (algebraTorMap R S A B A' B' fA fB i).map_add
      map_smul' := algebraTorMap_smul R S A B A' B' fA fB i }

end AlgebraMaps

private def torSystem : TorChangeOfRings.System where
  action := torModule
  action_tower := torModule_isScalarTower
  map R S A B A' B' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i fA fB :=
    tensorLinearTorMap R S A B A' B' fA fB i

private lemma extensionMap_one_tmul (S : TorChangeOfRings.System) : ∀ (R R' A B A' B' : Type u)
    [CommRing R] [CommRing R'] [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra R R'] [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra R B']
    [Algebra R' A'] [Algebra R' B'] [IsScalarTower R R' A'] [IsScalarTower R R' B']
    (i : ℕ) (fA : A →ₐ[R] A') (fB : B →ₐ[R] B') (x : TorChangeOfRings.torObj R i A B),
    let := S.action R A B i
    let := S.action R' A' B' i
    S.extensionMap R R' A B A' B' i fA fB
        ((1 : A' ⊗[R'] B') ⊗ₜ[A ⊗[R] B] x) = S.map R R' A B A' B' i fA fB x
 := by
  intro R R' A B A' B' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i fA fB x
  let := S.action R A B i
  let := S.action R' A' B' i
  show (1 : A' ⊗[R'] B') • S.map R R' A B A' B' i fA fB x = _
  exact one_smul _ _

private lemma homologyRestrictIso_self (R : Type u) [CommRing R]
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) :
    (TorChangeOfRings.homologyRestrictIso R R K i).hom = 𝟙 (K.homology i) := by
  show ((K.sc i).homologyData.left.map (𝟭 (ModuleCat.{u} R))).homologyIso.hom = _
  let h := (K.sc i).homologyData.left
  have hc : (h.map (𝟭 (ModuleCat.{u} R))).cyclesIso.hom = h.cyclesIso.hom := by
    rw [← cancel_mono h.i]
    exact (h.map (𝟭 (ModuleCat.{u} R))).cyclesIso_hom_comp_i.trans
      h.cyclesIso_hom_comp_i.symm
  rw [← cancel_epi (K.sc i).homologyπ,
    ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
  show (h.map (𝟭 (ModuleCat.{u} R))).cyclesIso.hom ≫ h.π = _
  rw [hc, ← h.homologyπ_comp_homologyIso_hom]
  simp only [ShortComplex.map_id, ShortComplex.LeftHomologyData.homologyIso,
    ShortComplex.leftHomologyIso, ShortComplex.LeftHomologyData.leftHomologyIso,
    Iso.symm_self_id, Iso.refl_hom, Category.comp_id, ShortComplex.LeftHomologyData.map_H,
    Functor.id_obj, h]
  exact (Category.comp_id _).symm

private lemma torMap_id (R : Type u) [CommRing R] (M N : ModuleCat.{u} R)
    (i : ℕ) (x : ((Tor (ModuleCat.{u} R) i).obj M).obj N) :
    torMap (LinearMap.id : M →ₗ[R] M) (LinearMap.id : N →ₗ[R] N) i x = x := by
  let P := projectiveResolution N
  let F := (MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).obj M
  have hm := torMap_eq_of_lift (M := M) (M' := M)
    (LinearMap.id : M →ₗ[R] M) (LinearMap.id : N →ₗ[R] N)
    P P (𝟙 P.complex) (fun _ => rfl) i
  have hφ : tensorComplexMap (algebraMap R R) (M := M) (M' := M)
      (LinearMap.id : M →ₗ[R] M) (𝟙 P.complex) =
      𝟙 ((F.mapHomologicalComplex _).obj P.complex) :=
    tensorComplex_hom_ext fun _ _ _ => rfl
  rw [hm]
  simp only [torMapOfLift, hφ, homologyRestrictIso_self]
  rw [(HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) i).map_id]
  simp only [Category.id_comp]
  exact Iso.hom_inv_id_apply (P.isoLeftDerivedObj F i) x

private lemma torSystem_map_id (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℕ) (x : TorChangeOfRings.torObj R i A B) :
    torSystem.map R R A B A B i (AlgHom.id R A) (AlgHom.id R B) x = x :=
  torMap_id R (ModuleCat.of R A) (ModuleCat.of R B) i x

private abbrev homologyClass {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{u} R)) (x : S.X₂) (hx : S.g x = 0) : S.homology :=
  S.homologyπ (S.moduleCatCyclesIso.inv ⟨x, hx⟩)

private lemma homologyClass_surjective {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{u} R)) (z : S.homology) :
    ∃ (x : S.X₂) (hx : S.g x = 0), homologyClass S x hx = z := by
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance z
  refine ⟨(S.moduleCatCyclesIso.hom c).val, (S.moduleCatCyclesIso.hom c).property, ?_⟩
  exact congrArg S.homologyπ (Iso.hom_inv_id_apply S.moduleCatCyclesIso c)

private lemma homologyClass_map {R : Type u} [CommRing R]
    {S T : ShortComplex (ModuleCat.{u} R)} (f : S ⟶ T) (x : S.X₂) (hx : S.g x = 0) :
    ShortComplex.homologyMap f (homologyClass S x hx) =
      homologyClass T (f.τ₂ x) (by
        change (f.τ₂ ≫ T.g) x = 0
        rw [f.comm₂₃]
        change f.τ₃ (S.g x) = 0
        rw [hx, map_zero]) := by
  have h := congrArg (fun k : S.cycles ⟶ T.homology => k (S.moduleCatCyclesIso.inv ⟨x, hx⟩))
    (ShortComplex.homologyπ_naturality f)
  change ShortComplex.homologyMap f (homologyClass S x hx) =
    T.homologyπ (ShortComplex.cyclesMap f (S.moduleCatCyclesIso.inv ⟨x, hx⟩)) at h
  rw [h]
  congr 1
  apply (ModuleCat.mono_iff_injective T.iCycles).mp inferInstance
  have h' := congrArg (fun k : S.cycles ⟶ T.X₂ => k (S.moduleCatCyclesIso.inv ⟨x, hx⟩))
    (ShortComplex.cyclesMap_i f)
  simp only [ModuleCat.comp_apply, ShortComplex.moduleCatCyclesIso_inv_iCycles_apply] at h' ⊢
  exact h'

private lemma homologyClass_restrict {R S : Type u} [CommRing R] [CommRing S]
    (ρ : R →+* S) (K : ShortComplex (ModuleCat.{u} S))
    (x : K.X₂) (hx : K.g x = 0) :
    (K.mapHomologyIso (ModuleCat.restrictScalars ρ)).hom
      (homologyClass (K.map (ModuleCat.restrictScalars ρ)) x hx) = homologyClass K x hx := by
  let F := ModuleCat.restrictScalars ρ
  let h := K.moduleCatLeftHomologyData
  rw [h.mapHomologyIso_eq]
  show h.homologyIso.inv ((h.map F).homologyIso.hom ((K.map F).homologyπ _)) = _
  have hh := congrArg (fun k : (K.map F).cycles ⟶ F.obj h.H =>
    k ((K.map F).moduleCatCyclesIso.inv ⟨x, hx⟩))
    ((h.map F).homologyπ_comp_homologyIso_hom)
  change (h.map F).homologyIso.hom ((K.map F).homologyπ _) =
    (h.map F).π ((h.map F).cyclesIso.hom _) at hh
  rw [hh]
  have hc : (h.map F).cyclesIso.hom ((K.map F).moduleCatCyclesIso.inv ⟨x, hx⟩) =
      (⟨x, hx⟩ : LinearMap.ker K.g.hom) := by
    apply (ModuleCat.mono_iff_injective (F.map h.i)).mp inferInstance
    have h' := congrArg (fun k : (K.map F).cycles ⟶ F.obj K.X₂ =>
      k ((K.map F).moduleCatCyclesIso.inv ⟨x, hx⟩)) ((h.map F).cyclesIso_hom_comp_i)
    simp only [ModuleCat.comp_apply] at h'
    change (F.map h.i) ((h.map F).cyclesIso.hom _) =
      (K.map F).iCycles ((K.map F).moduleCatCyclesIso.inv ⟨x, hx⟩) at h'
    have hi := congrArg (fun k : (K.map F).moduleCatLeftHomologyData.K ⟶ (K.map F).X₂ =>
      k ⟨x, hx⟩) (K.map F).moduleCatCyclesIso_inv_iCycles
    exact h'.trans hi
  rw [hc]
  exact (congrArg (fun k : K.moduleCatLeftHomologyData.K ⟶ K.homology => k ⟨x, hx⟩)
    K.moduleCatCyclesIso_inv_π).symm

private abbrev tensorComplex {R : Type u} [CommRing R] (M : ModuleCat.{u} R)
    (P : ChainComplex (ModuleCat.{u} R) ℕ) :=
  (((MonoidalCategory.tensoringLeft _).obj M).mapHomologicalComplex _).obj P

private abbrev torCycleClass {R : Type u} [CommRing R] (M : ModuleCat.{u} R)
    {N : ModuleCat.{u} R} (P : ProjectiveResolution N) (i : ℕ)
    (x : (tensorComplex M P.complex).X i)
    (hx : (tensorComplex M P.complex).d i ((ComplexShape.down ℕ).next i) x = 0) :
    ((Tor (ModuleCat.{u} R) i).obj M).obj N :=
  (P.isoLeftDerivedObj ((MonoidalCategory.tensoringLeft _).obj M) i).inv
    (homologyClass ((tensorComplex M P.complex).sc i) x hx)

private lemma torCycleClass_surjective {R : Type u} [CommRing R] (M : ModuleCat.{u} R)
    {N : ModuleCat.{u} R} (P : ProjectiveResolution N) (i : ℕ)
    (z : ((Tor (ModuleCat.{u} R) i).obj M).obj N) :
    ∃ (x : (tensorComplex M P.complex).X i)
      (hx : (tensorComplex M P.complex).d i ((ComplexShape.down ℕ).next i) x = 0),
      torCycleClass M P i x hx = z := by
  obtain ⟨x, hx, h⟩ := homologyClass_surjective ((tensorComplex M P.complex).sc i)
    ((P.isoLeftDerivedObj ((MonoidalCategory.tensoringLeft _).obj M) i).hom z)
  exact ⟨x, hx, (congrArg (P.isoLeftDerivedObj ((MonoidalCategory.tensoringLeft _).obj M) i).inv
    h).trans
    (Iso.hom_inv_id_apply _ z)⟩

private lemma torMap_cycleClass {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {M N : ModuleCat.{u} R} {M' N' : ModuleCat.{u} S}
    (f : M →ₛₗ[algebraMap R S] M') (g : N →ₛₗ[algebraMap R S] N')
    (P : ProjectiveResolution N) (Q : ProjectiveResolution N')
    (ψ : P.complex ⟶ ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex _).obj
      Q.complex)
    (hψ : ∀ p : P.complex.X 0, Q.π.f 0 (ψ.f 0 p) = g (P.π.f 0 p))
    (i : ℕ) (x : (tensorComplex M P.complex).X i)
    (hx : (tensorComplex M P.complex).d i ((ComplexShape.down ℕ).next i) x = 0) :
    ∃ hx', torMap f g i (torCycleClass M P i x hx) =
      torCycleClass M' Q i ((tensorComplexMap (algebraMap R S) f ψ).f i x) hx' := by
  let φ := tensorComplexMap (algebraMap R S) f ψ
  have hx' : (tensorComplex M' Q.complex).d i ((ComplexShape.down ℕ).next i) (φ.f i x) = 0 := by
    have h := congrArg (fun k : (tensorComplex M P.complex).X i ⟶ _ => k x)
      (φ.comm i ((ComplexShape.down ℕ).next i))
    change _ = φ.f _ ((tensorComplex M P.complex).d _ _ x) at h
    rwa [hx, map_zero] at h
  refine ⟨hx', ?_⟩
  rw [torMap_eq_of_lift f g P Q ψ hψ]
  show (Q.isoLeftDerivedObj ((MonoidalCategory.tensoringLeft _).obj M') i).inv
      ((TorChangeOfRings.homologyRestrictIso R S (tensorComplex M' Q.complex) i).hom
        (ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor _ _ i).map φ)
          ((P.isoLeftDerivedObj ((MonoidalCategory.tensoringLeft _).obj M) i).hom
            ((P.isoLeftDerivedObj ((MonoidalCategory.tensoringLeft _).obj M) i).inv _)))) = _
  rw [Iso.inv_hom_id_apply, homologyClass_map]
  exact congrArg (Q.isoLeftDerivedObj ((MonoidalCategory.tensoringLeft _).obj M') i).inv
    (homologyClass_restrict (algebraMap R S) ((tensorComplex M' Q.complex).sc i) _ hx')

private def chainMapComp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (ρ : R →+* S) (σ : S →+* T) (τ : R →+* T) (hτ : τ = σ.comp ρ)
    {P : ChainComplex (ModuleCat.{u} R) ℕ} {Q : ChainComplex (ModuleCat.{u} S) ℕ}
    {L : ChainComplex (ModuleCat.{u} T) ℕ}
    (ψ : P ⟶ ((ModuleCat.restrictScalars ρ).mapHomologicalComplex _).obj Q)
    (χ : Q ⟶ ((ModuleCat.restrictScalars σ).mapHomologicalComplex _).obj L) :
    P ⟶ ((ModuleCat.restrictScalars τ).mapHomologicalComplex _).obj L where
  f j := ψ.f j ≫ (ModuleCat.restrictScalars ρ).map (χ.f j) ≫
    (ModuleCat.restrictScalarsComp' ρ σ τ hτ).inv.app (L.X j)
  comm' j k _ := by
    apply ModuleCat.hom_ext
    ext x
    change L.d j k (χ.f j (ψ.f j x)) = χ.f k (ψ.f k (P.d j k x))
    have hψ := congrArg (fun f : P.X j ⟶ _ => f x) (ψ.comm j k)
    have hχ := congrArg (fun f : Q.X j ⟶ _ => f (ψ.f j x)) (χ.comm j k)
    exact hχ.trans (congrArg (fun z => χ.f k z) hψ)

private lemma torMap_comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [RingHomCompTriple (algebraMap R S) (algebraMap S T) (algebraMap R T)]
    {M N : ModuleCat.{u} R} {M' N' : ModuleCat.{u} S} {M'' N'' : ModuleCat.{u} T}
    (f : M →ₛₗ[algebraMap R S] M') (g : N →ₛₗ[algebraMap R S] N')
    (f' : M' →ₛₗ[algebraMap S T] M'') (g' : N' →ₛₗ[algebraMap S T] N'')
    (i : ℕ) (z : ((Tor (ModuleCat.{u} R) i).obj M).obj N) :
    torMap (f'.comp f) (g'.comp g) i z = torMap f' g' i (torMap f g i z) := by
  let P := projectiveResolution N
  let Q := projectiveResolution N'
  let L := projectiveResolution N''
  obtain ⟨ψ, hψ⟩ := resolution_lift_exists (algebraMap R S) g P Q
  obtain ⟨χ, hχ⟩ := resolution_lift_exists (algebraMap S T) g' Q L
  let θ := chainMapComp (algebraMap R S) (algebraMap S T) (algebraMap R T)
    (IsScalarTower.algebraMap_eq R S T) ψ χ
  have hθ (p : P.complex.X 0) : L.π.f 0 (θ.f 0 p) = (g'.comp g) (P.π.f 0 p) := by
    show L.π.f 0 (χ.f 0 (ψ.f 0 p)) = g' (g (P.π.f 0 p))
    rw [hχ, hψ]
  obtain ⟨x, hx, rfl⟩ := torCycleClass_surjective M P i z
  obtain ⟨hx', he⟩ := torMap_cycleClass f g P Q ψ hψ i x hx
  obtain ⟨hx'', he'⟩ := torMap_cycleClass f' g' Q L χ hχ i _ hx'
  obtain ⟨hx''', he''⟩ := torMap_cycleClass (f'.comp f) (g'.comp g) P L θ hθ i x hx
  rw [he, he', he'']
  have hφ : (tensorComplexMap (algebraMap R T) (f'.comp f) θ).f i x =
      (tensorComplexMap (algebraMap S T) f' χ).f i
        ((tensorComplexMap (algebraMap R S) f ψ).f i x) := by
    have hh : ∀ x : (tensorComplex M P.complex).X i,
        (tensorComplexMap (algebraMap R T) (f'.comp f) θ).f i x =
          (tensorComplexMap (algebraMap S T) f' χ).f i
            ((tensorComplexMap (algebraMap R S) f ψ).f i x) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add y y' hy hy' => simp only [map_add, hy, hy']
      | tmul m p => rfl
    exact hh x
  congr 1

private lemma torSystem_map_comp : ∀ (R R' R'' A B A' B' A'' B'' : Type u)
    [CommRing R] [CommRing R'] [CommRing R'']
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [CommRing A''] [CommRing B'']
    [Algebra R R'] [Algebra R' R''] [Algebra R R''] [IsScalarTower R R' R'']
    [Algebra R A] [Algebra R B]
    [Algebra R A'] [Algebra R B'] [Algebra R' A'] [Algebra R' B']
    [IsScalarTower R R' A'] [IsScalarTower R R' B']
    [Algebra R A''] [Algebra R B''] [Algebra R' A''] [Algebra R' B'']
    [Algebra R'' A''] [Algebra R'' B'']
    [IsScalarTower R R' A''] [IsScalarTower R R' B'']
    [IsScalarTower R R'' A''] [IsScalarTower R R'' B'']
    [IsScalarTower R' R'' A''] [IsScalarTower R' R'' B'']
    (i : ℕ) (fA : A →ₐ[R] A') (fB : B →ₐ[R] B')
    (gA : A' →ₐ[R'] A'') (gB : B' →ₐ[R'] B'') (x : TorChangeOfRings.torObj R i A B),
    torSystem.map R R'' A B A'' B'' i
        ((gA.restrictScalars R).comp fA) ((gB.restrictScalars R).comp fB) x =
      torSystem.map R' R'' A' B' A'' B'' i gA gB (torSystem.map R R' A B A' B' i fA fB x) := by
  intro R S T A B A' B' A'' B'' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i
    f g f' g' x
  let : RingHomCompTriple (algebraMap R S) (algebraMap S T) (algebraMap R T) :=
    ⟨(IsScalarTower.algebraMap_eq R S T).symm⟩
  exact torMap_comp (M := ModuleCat.of R A) (N := ModuleCat.of R B)
    (M' := ModuleCat.of S A') (N' := ModuleCat.of S B')
    (M'' := ModuleCat.of T A'') (N'' := ModuleCat.of T B'')
    (algHomSemilinear f) (algHomSemilinear g) (algHomSemilinear f') (algHomSemilinear g') i x

private lemma extendScalars_preservesProjectives {R S : Type u} [CommRing R] [CommRing S]
    (ρ : R →+* S) : (ModuleCat.extendScalars.{u,u,u} ρ).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (ModuleCat.extendRestrictScalarsAdj ρ)

private def tensorComplexBaseChangeIso {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (M : ModuleCat.{u} R) (P : ChainComplex (ModuleCat.{u} R) ℕ) :
    ((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex _).obj (tensorComplex M P) ≅
      tensorComplex ((ModuleCat.extendScalars (algebraMap R S)).obj M)
        (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex _).obj P) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun j =>
    (Functor.Monoidal.μIso (ModuleCat.extendScalars (algebraMap R S)) M (P.X j)).symm) ?_
  intro j k _
  exact Functor.OplaxMonoidal.δ_natural_right _ M (P.d j k)

private def flatTorBaseChangeIso {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] (M N : ModuleCat.{u} R) (i : ℕ) :
    (ModuleCat.extendScalars (algebraMap R S)).obj (((Tor (ModuleCat.{u} R) i).obj M).obj N) ≅
      ((Tor (ModuleCat.{u} S) i).obj ((ModuleCat.extendScalars (algebraMap R S)).obj M)).obj
        ((ModuleCat.extendScalars (algebraMap R S)).obj N) := by
  let F := ModuleCat.extendScalars.{u,u,u} (algebraMap R S)
  let := extendScalars_preservesProjectives (algebraMap R S)
  let : PreservesFiniteLimits F :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat (RingHom.flat_algebraMap_iff.mpr
      inferInstance)
  let : F.Additive := Functor.additive_of_preserves_binary_products F
  let P := projectiveResolution N
  let Q := F.mapProjectiveResolution P
  exact F.mapIso (P.isoLeftDerivedObj ((MonoidalCategory.tensoringLeft _).obj M) i) ≪≫
    (((tensorComplex M P.complex).sc i).mapHomologyIso F).symm ≪≫
    HomologicalComplex.homologyMapIso (tensorComplexBaseChangeIso M P.complex) i ≪≫
    (Q.isoLeftDerivedObj ((MonoidalCategory.tensoringLeft _).obj (F.obj M)) i).symm

private lemma homologyClass_extend {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] (K : ShortComplex (ModuleCat.{u} R))
    (x : K.X₂) (hx : K.g x = 0) :
    let F := ModuleCat.extendScalars.{u,u,u} (algebraMap R S)
    let : PreservesFiniteLimits F := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
    ∃ hx', (K.mapHomologyIso F).inv ((1 : S) ⊗ₜ[R, algebraMap R S] homologyClass K x hx) =
      homologyClass (K.map F) ((1 : S) ⊗ₜ[R, algebraMap R S] x) hx' := by
  let F := ModuleCat.extendScalars.{u,u,u} (algebraMap R S)
  let : PreservesFiniteLimits F := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have hx' : (K.map F).g ((1 : S) ⊗ₜ[R, algebraMap R S] x) = 0 := by
    show (1 : S) ⊗ₜ[R, algebraMap R S] K.g x = 0
    rw [hx, TensorProduct.tmul_zero]
  refine ⟨hx', ?_⟩
  let h := K.moduleCatLeftHomologyData
  let y : F.obj h.K := (1 : S) ⊗ₜ[R, algebraMap R S] (⟨x, hx⟩ : LinearMap.ker K.g.hom)
  have hc : (K.map F).moduleCatCyclesIso.inv ⟨(1 : S) ⊗ₜ[R, algebraMap R S] x, hx'⟩ =
      (h.map F).cyclesIso.inv y := by
    apply (ModuleCat.mono_iff_injective (K.map F).iCycles).mp inferInstance
    have h₁ := congrArg (fun k : (K.map F).moduleCatLeftHomologyData.K ⟶ (K.map F).X₂ =>
      k ⟨(1 : S) ⊗ₜ[R, algebraMap R S] x, hx'⟩) (K.map F).moduleCatCyclesIso_inv_iCycles
    have h₂ := congrArg (fun k : (h.map F).K ⟶ (K.map F).X₂ => k y)
      (h.map F).cyclesIso_inv_comp_iCycles
    exact h₁.trans h₂.symm
  apply (ModuleCat.mono_iff_injective (K.mapHomologyIso F).hom).mp inferInstance
  rw [Iso.inv_hom_id_apply]
  show (1 : S) ⊗ₜ[R, algebraMap R S] homologyClass K x hx =
    (K.mapHomologyIso F).hom ((K.map F).homologyπ _)
  rw [hc, h.mapHomologyIso_eq]
  have hh := congrArg (fun k : (K.map F).cycles ⟶ F.obj h.H => k ((h.map F).cyclesIso.inv y))
    (h.map F).homologyπ_comp_homologyIso_hom
  change (h.map F).homologyIso.hom ((K.map F).homologyπ _) =
    (h.map F).π ((h.map F).cyclesIso.hom ((h.map F).cyclesIso.inv y)) at hh
  rw [Iso.inv_hom_id_apply] at hh
  show _ = (F.map h.homologyIso.inv) ((h.map F).homologyIso.hom ((K.map F).homologyπ _))
  rw [hh]
  show (1 : S) ⊗ₜ[R, algebraMap R S] homologyClass K x hx =
    (1 : S) ⊗ₜ[R, algebraMap R S] (h.homologyIso.inv (h.π ⟨x, hx⟩))
  exact congrArg (fun z : K.homology => (1 : S) ⊗ₜ[R, algebraMap R S] z)
    (congrArg (fun k : h.K ⟶ K.homology => k ⟨x, hx⟩) K.moduleCatCyclesIso_inv_π)

private def baseChangeUnit {R S : Type u} [CommRing R] [CommRing S]
    (ρ : R →+* S) (M : ModuleCat.{u} R) :
    M →ₛₗ[ρ] (ModuleCat.extendScalars ρ).obj M :=
  (ModuleCat.semilinearMapAddEquiv ρ _ _).symm ((ModuleCat.extendRestrictScalarsAdj ρ).unit.app M)

private lemma flatTorBaseChangeIso_one_tmul {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] (M N : ModuleCat.{u} R) (i : ℕ)
    (z : ((Tor (ModuleCat.{u} R) i).obj M).obj N) :
    (flatTorBaseChangeIso M N i).hom ((1 : S) ⊗ₜ[R, algebraMap R S] z) =
      torMap (baseChangeUnit (algebraMap R S) M) (baseChangeUnit (algebraMap R S) N) i z := by
  let F := ModuleCat.extendScalars.{u,u,u} (algebraMap R S)
  let := extendScalars_preservesProjectives (algebraMap R S)
  let : PreservesFiniteLimits F := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let : F.Additive := Functor.additive_of_preserves_binary_products F
  let P := projectiveResolution N
  let Q := F.mapProjectiveResolution P
  let ψ : P.complex ⟶ ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex _).obj
      Q.complex := (NatTrans.mapHomologicalComplex
        (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).unit _).app P.complex
  have hψ (p : P.complex.X 0) : Q.π.f 0 (ψ.f 0 p) =
      baseChangeUnit (algebraMap R S) N (P.π.f 0 p) := by
    rfl
  obtain ⟨x, hx, rfl⟩ := torCycleClass_surjective M P i z
  obtain ⟨hx', hm⟩ := torMap_cycleClass (baseChangeUnit (algebraMap R S) M)
    (baseChangeUnit (algebraMap R S) N) P Q ψ hψ i x hx
  rw [hm]
  obtain ⟨hx'', he⟩ := homologyClass_extend (S := S) ((tensorComplex M P.complex).sc i) x hx
  show (Q.isoLeftDerivedObj ((MonoidalCategory.tensoringLeft _).obj (F.obj M)) i).inv
      (ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor _ _ i).map
        (tensorComplexBaseChangeIso M P.complex).hom)
        ((((tensorComplex M P.complex).sc i).mapHomologyIso F).inv
          ((1 : S) ⊗ₜ[R, algebraMap R S]
            ((P.isoLeftDerivedObj ((MonoidalCategory.tensoringLeft _).obj M) i).hom
              ((P.isoLeftDerivedObj ((MonoidalCategory.tensoringLeft _).obj M) i).inv _))))) = _
  rw [Iso.inv_hom_id_apply, he]
  erw [homologyClass_map]
  have hc : (tensorComplexBaseChangeIso M P.complex).hom.f i
      ((1 : S) ⊗ₜ[R, algebraMap R S] x) =
      (tensorComplexMap (algebraMap R S) (baseChangeUnit (algebraMap R S) M) ψ).f i x := by
    have hh : ∀ y : (tensorComplex M P.complex).X i,
        (tensorComplexBaseChangeIso M P.complex).hom.f i
            ((1 : S) ⊗ₜ[R, algebraMap R S] y) =
          (tensorComplexMap (algebraMap R S) (baseChangeUnit (algebraMap R S) M) ψ).f i y := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | add y y' hy hy' => simp only [TensorProduct.tmul_add, map_add, hy, hy']
      | tmul m p => rfl
    exact hh x
  congr 1
  show homologyClass ((tensorComplex (F.obj M) Q.complex).sc i) _ _ = _
  congr 1

private lemma torSystem_isCanonical
    (hflat : ∀ (R R' A B : Type u)
    [CommRing R] [CommRing R'] [CommRing A] [CommRing B]
    [Algebra R R'] [Algebra R A] [Algebra R B] [Module.Flat R R'] (i : ℕ),
    IsIso (torSystem.extensionMap R R' A B (R' ⊗[R] A) (R' ⊗[R] B) i
      (Algebra.TensorProduct.includeRight : A →ₐ[R] R' ⊗[R] A)
      (Algebra.TensorProduct.includeRight : B →ₐ[R] R' ⊗[R] B)))
    (hflatAlg : ∀ (R A B A' B' : Type u)
    [CommRing R] [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra R B']
    (fA : A →ₐ[R] A') (fB : B →ₐ[R] B')
    (_hA : RingHom.Flat fA.toRingHom) (_hB : RingHom.Flat fB.toRingHom) (i : ℕ),
    IsIso (torSystem.extensionMap R R A B A' B' i fA fB)) : torSystem.{u}.IsCanonical := by
  refine ⟨torModule_tmul, torSystem_map_id, torSystem_map_comp, resolution_comparison_exists,
    ?_, extensionMap_one_tmul torSystem, hflat, hflatAlg⟩
  intro R S A B A' B' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i fA fB P Q ψ φ hψ hφ x
  have h := torMap_eq_of_lift (M := ModuleCat.of R A) (M' := ModuleCat.of S A')
    (algHomSemilinear fA) (algHomSemilinear fB) P Q ψ hψ i
  have he := tensorComplexMap_eq_of_tmul (algebraMap R S) (algHomSemilinear fA) ψ φ hφ
  have ht := torMapOfLift_resolution (M := ModuleCat.of R A) (M' := ModuleCat.of S A')
    (algHomSemilinear fA) P Q ψ i x
  rw [← h] at ht
  subst φ
  exact ht

private lemma isIso_torBaseChange {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] (M N : ModuleCat.{u} R) (i : ℕ) :
    IsIso (((ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).homEquiv
      (((Tor (ModuleCat.{u} R) i).obj M).obj N)
      (((Tor (ModuleCat.{u} S) i).obj ((ModuleCat.extendScalars (algebraMap R S)).obj M)).obj
        ((ModuleCat.extendScalars (algebraMap R S)).obj N))).symm
      (ModuleCat.semilinearMapAddEquiv (algebraMap R S) _ _
        (torMap (baseChangeUnit (algebraMap R S) M) (baseChangeUnit (algebraMap R S) N) i))) := by
  have he : ((ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).homEquiv
      (((Tor (ModuleCat.{u} R) i).obj M).obj N)
      (((Tor (ModuleCat.{u} S) i).obj ((ModuleCat.extendScalars (algebraMap R S)).obj M)).obj
        ((ModuleCat.extendScalars (algebraMap R S)).obj N))).symm
      (ModuleCat.semilinearMapAddEquiv (algebraMap R S) _ _
        (torMap (baseChangeUnit (algebraMap R S) M) (baseChangeUnit (algebraMap R S) N) i)) =
      (flatTorBaseChangeIso M N i).hom := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    show (1 : S) • torMap (baseChangeUnit (algebraMap R S) M)
      (baseChangeUnit (algebraMap R S) N) i x = _
    rw [one_smul]
    exact (flatTorBaseChangeIso_one_tmul M N i x).symm
  rw [he]
  infer_instance

private alias isBaseChange_of_pushout := Stacks.RelativeProj.isBaseChange_of_isPushout

private abbrev tensorProductBaseChangeEquiv (R S A B : Type u)
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B] :
    ((S ⊗[R] A) ⊗[S] (S ⊗[R] B)) ≃ₐ[S] S ⊗[R] (A ⊗[R] B) :=
  (Algebra.TensorProduct.cancelBaseChange R S S (S ⊗[R] A) B).trans
    (Algebra.TensorProduct.assoc R R S S A B)

private lemma tensorProductBaseChangeEquiv_map (R S A B : Type u)
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B] (x : A ⊗[R] B) :
    tensorProductBaseChangeEquiv R S A B
      (TorChangeOfRings.tensorProductMap R S A B (S ⊗[R] A) (S ⊗[R] B)
        Algebra.TensorProduct.includeRight Algebra.TensorProduct.includeRight x) =
      (1 : S) ⊗ₜ[R] x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
  | tmul a b =>
    simp [TorChangeOfRings.tensorProductMap, tensorProductBaseChangeEquiv,
      Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.TensorProduct.assoc_tmul]

private lemma tensorProductMap_isBaseChange (R S A B : Type u)
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B]
    (f : (A ⊗[R] B) →ₗ[R] ((S ⊗[R] A) ⊗[S] (S ⊗[R] B)))
    (hf : ∀ x, f x = TorChangeOfRings.tensorProductMap R S A B (S ⊗[R] A) (S ⊗[R] B)
      Algebra.TensorProduct.includeRight Algebra.TensorProduct.includeRight x) : IsBaseChange S f :=
        by
  apply IsBaseChange.of_equiv (tensorProductBaseChangeEquiv R S A B).symm.toLinearEquiv
  intro x
  apply (tensorProductBaseChangeEquiv R S A B).injective
  show (tensorProductBaseChangeEquiv R S A B)
    ((tensorProductBaseChangeEquiv R S A B).symm _) = _
  rw [AlgEquiv.apply_symm_apply, hf, tensorProductBaseChangeEquiv_map]

private noncomputable def baseChangeTensorIso {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars (algebraMap R S)).obj M ≅ ModuleCat.of S (S ⊗[R] M) := by
  let e : (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) ≃ₗ[R] S :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro r s
        change algebraMap R S r * (show S from s) = r • (show S from s)
        exact (Algebra.smul_def r (show S from s)).symm }
  let eR := TensorProduct.congr e (LinearEquiv.refl R M)
  let eS : (ModuleCat.extendScalars (algebraMap R S)).obj M ≃ₗ[S] S ⊗[R] M :=
    { __ := eR.toAddEquiv
      map_smul' := by
        intro s x
        change eR (s • x) = s • eR x
        induction x using TensorProduct.induction_on with
        | zero => simp only [smul_zero, map_zero]
        | add x y hx hy => simp only [smul_add, map_add, hx, hy]
        | tmul a m => rfl }
  exact eS.toModuleIso
private lemma baseChangeTensorIso_tmul {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (M : ModuleCat.{u} R) (s : S) (m : M) :
    (baseChangeTensorIso M).hom (s ⊗ₜ[R, algebraMap R S] m) = s ⊗ₜ[R] m := rfl

private lemma torMap_comp_eq_self {R : Type u} [CommRing R] {M N M' N' : ModuleCat.{u} R}
    (f : M →ₗ[R] M') (f' : M' →ₗ[R] M) (g : N →ₗ[R] N') (g' : N' →ₗ[R] N)
    (hf : f'.comp f = LinearMap.id) (hg : g'.comp g = LinearMap.id)
    (i : ℕ) (x : ((Tor (ModuleCat.{u} R) i).obj M).obj N) :
    torMap f' g' i (torMap f g i x) = x := by
  let : RingHomCompTriple (algebraMap R R) (algebraMap R R) (algebraMap R R) := ⟨rfl⟩
  rw [← torMap_comp, hf, hg, torMap_id]

private def torMapIso {R : Type u} [CommRing R] {M N M' N' : ModuleCat.{u} R}
    (f : M ≅ M') (g : N ≅ N') (i : ℕ) :
    ((Tor (ModuleCat.{u} R) i).obj M).obj N ≅ ((Tor (ModuleCat.{u} R) i).obj M').obj N' where
  hom := ModuleCat.ofHom (torMap f.hom.hom g.hom.hom i)
  inv := ModuleCat.ofHom (torMap f.inv.hom g.inv.hom i)
  hom_inv_id := by
    apply ModuleCat.hom_ext
    ext x
    exact torMap_comp_eq_self _ _ _ _ (congrArg ModuleCat.Hom.hom f.hom_inv_id)
      (congrArg ModuleCat.Hom.hom g.hom_inv_id) i x
  inv_hom_id := by
    apply ModuleCat.hom_ext
    ext x
    exact torMap_comp_eq_self _ _ _ _ (congrArg ModuleCat.Hom.hom f.inv_hom_id)
      (congrArg ModuleCat.Hom.hom g.inv_hom_id) i x

private abbrev flatTorTensorIso {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] (M N : ModuleCat.{u} R) (i : ℕ) :
    ModuleCat.of S (S ⊗[R] ((Tor (ModuleCat.{u} R) i).obj M).obj N) ≅
      ((Tor (ModuleCat.{u} S) i).obj (ModuleCat.of S (S ⊗[R] M))).obj
        (ModuleCat.of S (S ⊗[R] N)) :=
  (baseChangeTensorIso (((Tor (ModuleCat.{u} R) i).obj M).obj N)).symm ≪≫
    flatTorBaseChangeIso M N i ≪≫ torMapIso (baseChangeTensorIso M) (baseChangeTensorIso N) i

private def tensorUnit {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (M : ModuleCat.{u} R) : M →ₛₗ[algebraMap R S] ModuleCat.of S (S ⊗[R] M) :=
  (baseChangeTensorIso M).hom.hom.comp (baseChangeUnit (algebraMap R S) M)

private lemma flatTorTensorIso_one_tmul {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] (M N : ModuleCat.{u} R) (i : ℕ)
    (x : ((Tor (ModuleCat.{u} R) i).obj M).obj N) :
    (flatTorTensorIso (S := S) M N i).hom ((1 : S) ⊗ₜ[R] x) =
      torMap (tensorUnit M) (tensorUnit N) i x := by
  let : RingHomCompTriple (algebraMap R S) (algebraMap S S) (algebraMap R S) := ⟨rfl⟩
  show torMap (baseChangeTensorIso M).hom.hom (baseChangeTensorIso N).hom.hom i
    ((flatTorBaseChangeIso M N i).hom ((1 : S) ⊗ₜ[R, algebraMap R S] x)) = _
  rw [flatTorBaseChangeIso_one_tmul, ← torMap_comp]
  rfl

private lemma bijective_of_pushout
    {R S C D M N : Type*} [CommRing R] [CommRing S] [CommRing C] [CommRing D]
    [Algebra R S] [Algebra R C] [Algebra R D] [Algebra S D] [Algebra C D]
    [IsScalarTower R S D] [IsScalarTower R C D] [Algebra.IsPushout R S C D]
    [AddCommGroup M] [Module R M] [Module C M] [IsScalarTower R C M]
    [AddCommGroup N] [Module S N] [Module D N] [IsScalarTower S D N]
    (f : D ⊗[C] M →ₗ[D] N) (e : S ⊗[R] M ≃ₗ[S] N)
    (he : ∀ x, f (1 ⊗ₜ[C] x) = e (1 ⊗ₜ[R] x)) : Function.Bijective f := by
  let c := Algebra.IsPushout.cancelBaseChange R S C D M
  have hf (x : S ⊗[R] M) : f (c.symm x) = e x := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s m =>
      rw [Algebra.IsPushout.cancelBaseChange_symm_tmul]
      calc
        f (algebraMap S D s ⊗ₜ[C] m) =
            algebraMap S D s • f (1 ⊗ₜ[C] m) := by
          rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        _ = s • e (1 ⊗ₜ[R] m) := by rw [he, IsScalarTower.algebraMap_smul]
        _ = e (s ⊗ₜ[R] m) := by
          rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have h : (f : D ⊗[C] M → N) = e ∘ c := by
    funext x
    simpa using hf (c x)
  rw [h]
  exact e.bijective.comp c.bijective

/-- A map out of an extension of scalars is invertible if it is bijective after precomposing
with the tensor-product description of the extension. -/
private lemma isIso_of_bijective_comp_baseChangeTensorIso {C D T T' : Type u} [CommRing C]
    [CommRing D] [Algebra C D] [AddCommGroup T] [Module C T] [AddCommGroup T'] [Module D T']
    (f : (ModuleCat.extendScalars (algebraMap C D)).obj (ModuleCat.of C T) ⟶ ModuleCat.of D T')
    (hf : Function.Bijective
      (f.hom.comp (baseChangeTensorIso (S := D) (ModuleCat.of C T)).inv.hom)) : IsIso f :=
  (ConcreteCategory.isIso_iff_bijective f).mpr
    ((Function.Bijective.of_comp_iff f.hom
      (baseChangeTensorIso (S := D) (ModuleCat.of C T)).toLinearEquiv.symm.bijective).mp hf)

private lemma torSystem_flat_baseChange (R S A B : Type u)
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B] [Module.Flat R S] (i : ℕ) :
    IsIso (torSystem.extensionMap R S A B (S ⊗[R] A) (S ⊗[R] B) i
      Algebra.TensorProduct.includeRight Algebra.TensorProduct.includeRight) := by
  let C := A ⊗[R] B
  let D := (S ⊗[R] A) ⊗[S] (S ⊗[R] B)
  let θ : C →ₐ[R] D :=
    { __ := TorChangeOfRings.tensorProductMap R S A B (S ⊗[R] A) (S ⊗[R] B)
        Algebra.TensorProduct.includeRight Algebra.TensorProduct.includeRight
      commutes' := by
        intro r
        show (Algebra.TensorProduct.lift _ _ _) ((algebraMap R C) r) = _
        exact (Algebra.TensorProduct.lift _ _ _).commutes r }
  let : Algebra C D := θ.toAlgebra
  let : IsScalarTower R C D := IsScalarTower.of_algebraMap_eq fun r => (θ.commutes r).symm
  let : Algebra.IsPushout R S C D := ⟨tensorProductMap_isBaseChange R S A B
    (IsScalarTower.toAlgHom R C D).toLinearMap (fun _ => rfl)⟩
  let := torModule R A B i
  let := torModule S (S ⊗[R] A) (S ⊗[R] B) i
  let := torModule_isScalarTower R A B i
  let := torModule_isScalarTower S (S ⊗[R] A) (S ⊗[R] B) i
  let f := torSystem.extensionMap R S A B (S ⊗[R] A) (S ⊗[R] B) i
    Algebra.TensorProduct.includeRight Algebra.TensorProduct.includeRight
  let e := baseChangeTensorIso (S := D) (ModuleCat.of C (TorChangeOfRings.torObj R i A B))
  have hf : Function.Bijective (f.hom.comp e.inv.hom) := by
    apply bijective_of_pushout (R := R) (S := S) _
      (flatTorTensorIso (S := S) (ModuleCat.of R A) (ModuleCat.of R B) i).toLinearEquiv
    intro x
    show f ((1 : D) ⊗ₜ[C, θ.toRingHom] x) = _
    rw [extensionMap_one_tmul]
    exact (flatTorTensorIso_one_tmul (S := S) (ModuleCat.of R A)
      (ModuleCat.of R B) i x).symm
  exact isIso_of_bijective_comp_baseChangeTensorIso f hf

private lemma diagram_enoughProjectives (J : Type u) [SmallCategory J]
    (R : Type u) [Ring R] : EnoughProjectives (J ⥤ ModuleCat.{u} R) := by
  let : ∀ j : J, (evaluationLeftAdjoint (ModuleCat.{u} R) j).PreservesProjectiveObjects :=
    fun j => Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (evaluationAdjunctionRight (ModuleCat.{u} R) j)
  refine ⟨fun F => ?_⟩
  let P (j : J) := (evaluationLeftAdjoint (ModuleCat.{u} R) j).obj (Projective.over (F.obj j))
  let π (j : J) : P j ⟶ F :=
    ((evaluationAdjunctionRight (ModuleCat.{u} R) j).homEquiv _ _).symm (Projective.π (F.obj j))
  let e : (∐ P) ⟶ F := Sigma.desc π
  have he (j : J) : Epi (e.app j) := by
    have h : Sigma.ι (fun _ : j ⟶ j => Projective.over (F.obj j)) (𝟙 j) ≫
        (Sigma.ι P j).app j ≫ e.app j = Projective.π (F.obj j) := by
      rw [← NatTrans.comp_app, Sigma.ι_desc]
      show ((evaluationAdjunctionRight (ModuleCat.{u} R) j).homEquiv _ _)
        (((evaluationAdjunctionRight (ModuleCat.{u} R) j).homEquiv _ _).symm _) = _
      exact Equiv.apply_symm_apply _ _
    have : Epi (Sigma.ι (fun _ : j ⟶ j => Projective.over (F.obj j)) (𝟙 j) ≫
        (Sigma.ι P j).app j ≫ e.app j) := h.symm ▸ inferInstance
    exact epi_of_epi (Sigma.ι (fun _ : j ⟶ j => Projective.over (F.obj j)) (𝟙 j) ≫
      (Sigma.ι P j).app j) (e.app j)
  have : Epi e := NatTrans.epi_of_epi_app e
  exact ⟨⟨∐ P, e⟩⟩

private lemma evaluation_preservesProjectives (J : Type u) [SmallCategory J]
    (R : Type u) [Ring R] (j : J) :
    ((evaluation J (ModuleCat.{u} R)).obj j).PreservesProjectiveObjects := by
  let : (evaluationRightAdjoint (ModuleCat.{u} R) j).PreservesEpimorphisms := by
    refine ⟨fun {X Y} f _ => ?_⟩
    let : ∀ k : J, Epi (((evaluationRightAdjoint (ModuleCat.{u} R) j).map f).app k) :=
      fun k => by
        show Epi (Limits.Pi.map (fun _ : k ⟶ j => f))
        apply (ModuleCat.epi_iff_surjective _).mpr
        intro y
        let hf := (ModuleCat.epi_iff_surjective f).mp inferInstance
        choose x hx using fun a : k ⟶ j => hf (Limits.Pi.π (fun _ : k ⟶ j => Y) a y)
        refine ⟨(ModuleCat.piIsoPi (fun _ : k ⟶ j => X)).inv x, ?_⟩
        apply (ModuleCat.piIsoPi (fun _ : k ⟶ j => Y)).toLinearEquiv.injective
        funext a
        show ((ModuleCat.piIsoPi (fun _ : k ⟶ j => Y)).hom
          ((Limits.Pi.map (fun _ : k ⟶ j => f))
            ((ModuleCat.piIsoPi (fun _ : k ⟶ j => X)).inv x))) a =
          ((ModuleCat.piIsoPi (fun _ : k ⟶ j => Y)).hom y) a
        rw [ModuleCat.piIsoPi_hom_ker_subtype_apply,
          ModuleCat.piIsoPi_hom_ker_subtype_apply]
        have hv := congrArg (fun h : (∏ᶜ (fun _ : k ⟶ j => X)) ⟶ Y =>
          h ((ModuleCat.piIsoPi (fun _ : k ⟶ j => X)).inv x))
          (Limits.Pi.map_π (fun _ : k ⟶ j => f) a)
        change _ = f (Limits.Pi.π (fun _ : k ⟶ j => X) a
          ((ModuleCat.piIsoPi (fun _ : k ⟶ j => X)).inv x)) at hv
        rw [ModuleCat.piIsoPi_inv_kernel_ι_apply] at hv
        exact hv.trans (hx a)
    exact NatTrans.epi_of_epi_app _
  exact Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (evaluationAdjunctionLeft _ j)

private def leftDerivedDiagramIso {J : Type u} [SmallCategory J]
    {R S : Type u} [Ring R] [Ring S]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]
    (D : J ⥤ ModuleCat.{u} R) (P : ProjectiveResolution D) (i : ℕ) :
    D ⋙ F.leftDerived i ≅
      ((((Functor.whiskeringRight J (ModuleCat.{u} R) (ModuleCat.{u} S)).obj
        F).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex).homology i := by
  let : ∀ j : J, ((evaluation J (ModuleCat.{u} R)).obj j).PreservesProjectiveObjects :=
    evaluation_preservesProjectives J R
  let W := (Functor.whiskeringRight J (ModuleCat.{u} R) (ModuleCat.{u} S)).obj F
  let K := (W.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let Q (j : J) := ((evaluation J (ModuleCat.{u} R)).obj j).mapProjectiveResolution P
  refine NatIso.ofComponents (fun j =>
    (Q j).isoLeftDerivedObj F i ≪≫ (K.sc i).mapHomologyIso ((evaluation _ _).obj j)) ?_
  intro j k g
  have h := ProjectiveResolution.isoLeftDerivedObj_hom_naturality (D.map g) (Q j) (Q k)
    (P.complex.asFunctor.map g) (by exact (P.π.f 0).naturality g) F i
  have h' := NatTrans.app_homology ((evaluation J (ModuleCat.{u} S)).map g) (K.sc i)
  change (F.leftDerived i).map (D.map g) ≫
    ((Q k).isoLeftDerivedObj F i).hom ≫
      ((K.sc i).mapHomologyIso ((evaluation J (ModuleCat.{u} S)).obj k)).hom =
    (((Q j).isoLeftDerivedObj F i).hom ≫
      ((K.sc i).mapHomologyIso ((evaluation J (ModuleCat.{u} S)).obj j)).hom) ≫
        (K.homology i).map g
  change (K.homology i).map g = _ at h'
  rw [← Category.assoc, h, Category.assoc]
  rw [h']
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rfl

private lemma colim_preservesProjectives {J : Type u} [SmallCategory J]
    (R : Type u) [Ring R] :
    (colim : (J ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms colimConstAdj

private def leftDerivedColimitIso {J : Type u} [SmallCategory J] [IsFiltered J]
    {R S : Type u} [Ring R] [Ring S]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive] [PreservesColimitsOfShape J F]
    (D : J ⥤ ModuleCat.{u} R) (P : ProjectiveResolution D) (i : ℕ) :
    (F.leftDerived i).obj (colimit D) ≅
      colimit (((((Functor.whiskeringRight J (ModuleCat.{u} R)
        (ModuleCat.{u} S)).obj F).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex).homology i) := by
  let C : (J ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R := colim
  let C' : (J ⥤ ModuleCat.{u} S) ⥤ ModuleCat.{u} S := colim
  let := colim_preservesProjectives (J := J) R
  let Q := C.mapProjectiveResolution P
  let W := (Functor.whiskeringRight J (ModuleCat.{u} R) (ModuleCat.{u} S)).obj F
  let K := (W.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let e : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex ≅
      (C'.mapHomologicalComplex (ComplexShape.down ℕ)).obj K :=
    HomologicalComplex.Hom.isoOfComponents (fun n => preservesColimitIso F (P.complex.X n))
      (fun n m _ => ((preservesColimitNatIso F).hom.naturality (P.complex.d n m)).symm)
  exact Q.isoLeftDerivedObj F i ≪≫ HomologicalComplex.homologyMapIso e i ≪≫
    (K.sc i).mapHomologyIso C'

private def evaluationToColimit {J : Type u} [SmallCategory J]
    (R : Type u) [Ring R] (j : J) :
    (evaluation J (ModuleCat.{u} R)).obj j ⟶ colim where
  app D := colimit.ι D j
  naturality _ _ f := (colimit.ι_map f j).symm

private lemma leftDerivedColimitIso_ι {J : Type u} [SmallCategory J] [IsFiltered J]
    {R S : Type u} [Ring R] [Ring S]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive] [PreservesColimitsOfShape J F]
    (D : J ⥤ ModuleCat.{u} R) (P : ProjectiveResolution D) (i : ℕ) (j : J) :
    (F.leftDerived i).map (colimit.ι D j) ≫ (leftDerivedColimitIso F D P i).hom =
      (leftDerivedDiagramIso F D P i).hom.app j ≫ colimit.ι _ j := by
  let C : (J ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R := colim
  let C' : (J ⥤ ModuleCat.{u} S) ⥤ ModuleCat.{u} S := colim
  let := colim_preservesProjectives (J := J) R
  let := evaluation_preservesProjectives J R j
  let Q := C.mapProjectiveResolution P
  let Qj := ((evaluation J (ModuleCat.{u} R)).obj j).mapProjectiveResolution P
  let W := (Functor.whiskeringRight J (ModuleCat.{u} R) (ModuleCat.{u} S)).obj F
  let K := (W.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let e : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex ≅
      (C'.mapHomologicalComplex (ComplexShape.down ℕ)).obj K :=
    HomologicalComplex.Hom.isoOfComponents (fun n => preservesColimitIso F (P.complex.X n))
      (fun n m _ => ((preservesColimitNatIso F).hom.naturality (P.complex.d n m)).symm)
  let ψ := (NatTrans.mapHomologicalComplex (evaluationToColimit R j) _).app P.complex
  let κ := (NatTrans.mapHomologicalComplex (evaluationToColimit S j) _).app K
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} S) (ComplexShape.down ℕ) i
  have he : (F.mapHomologicalComplex _).map ψ ≫ e.hom = κ := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact ι_preservesColimitIso_hom F (P.complex.X n) j
  have hh := ProjectiveResolution.isoLeftDerivedObj_hom_naturality (colimit.ι D j) Qj Q ψ
    (by exact (colimit.ι_map (P.π.f 0) j)) F i
  have ht := NatTrans.app_homology (evaluationToColimit S j) (K.sc i)
  have ht' : ((K.sc i).mapHomologyIso ((evaluation J (ModuleCat.{u} S)).obj j)).hom ≫
      colimit.ι (K.homology i) j = H.map κ ≫ ((K.sc i).mapHomologyIso C').hom := by
    show ((K.sc i).mapHomologyIso ((evaluation J (ModuleCat.{u} S)).obj j)).hom ≫
      (evaluationToColimit S j).app (K.sc i).homology = _
    rw [ht, Iso.hom_inv_id_assoc]
    rfl
  show (F.leftDerived i).map (colimit.ι D j) ≫
    (Q.isoLeftDerivedObj F i).hom ≫ H.map e.hom ≫ ((K.sc i).mapHomologyIso C').hom =
    ((Qj.isoLeftDerivedObj F i).hom ≫
      ((K.sc i).mapHomologyIso ((evaluation J (ModuleCat.{u} S)).obj j)).hom) ≫
        colimit.ι (K.homology i) j
  rw [← Category.assoc, ← Category.assoc, hh]
  simp only [Category.assoc]
  show (Qj.isoLeftDerivedObj F i).hom ≫ H.map ((F.mapHomologicalComplex _).map ψ) ≫
    H.map e.hom ≫ ((K.sc i).mapHomologyIso C').hom = _
  rw [← Functor.map_comp_assoc, he, ht']

private lemma leftDerived_preservesFilteredColimitsOfShape
    (J : Type u) [SmallCategory J] [IsFiltered J]
    {R S : Type u} [Ring R] [Ring S]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive] [PreservesColimitsOfShape J F]
    (i : ℕ) : PreservesColimitsOfShape J (F.leftDerived i) := by
  let := diagram_enoughProjectives J R
  refine ⟨fun {D} => ?_⟩
  let P := projectiveResolution D
  let e := leftDerivedDiagramIso F D P i
  let e' := leftDerivedColimitIso F D P i
  have h : colimit.post D (F.leftDerived i) = (colim.mapIso e ≪≫ e'.symm).hom := by
    apply (cancel_mono e'.hom).mp
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply colimit.hom_ext
    intro j
    rw [colimit.ι_post_assoc, Functor.mapIso_hom, colimit.ι_map]
    exact leftDerivedColimitIso_ι F D P i j
  have : IsIso (colimit.post D (F.leftDerived i)) := h ▸ inferInstance
  exact preservesColimit_of_isIso_post (F.leftDerived i) D

private def diagramComplex {J : Type u} [SmallCategory J]
    {R : Type u} [Ring R] (D : J ⥤ ChainComplex (ModuleCat.{u} R) ℕ) :
    ChainComplex (J ⥤ ModuleCat.{u} R) ℕ where
  X n := D ⋙ HomologicalComplex.eval _ _ n
  d n m := { app j := (D.obj j).d n m
             naturality j k f := (D.map f).comm n m }
  shape n m h := by
    apply NatTrans.ext
    funext j
    exact (D.obj j).shape n m h
  d_comp_d' n m k _ _ := by
    apply NatTrans.ext
    funext j
    exact (D.obj j).d_comp_d n m k

private def homologyDiagramIso {J : Type u} [SmallCategory J]
    {R : Type u} [Ring R] (K : ChainComplex (J ⥤ ModuleCat.{u} R) ℕ) (i : ℕ) :
    K.asFunctor ⋙ HomologicalComplex.homologyFunctor _ _ i ≅ K.homology i :=
  NatIso.ofComponents (fun j => (K.sc i).mapHomologyIso ((evaluation _ _).obj j)) (by
    intro j k g
    have h := NatTrans.app_homology ((evaluation J (ModuleCat.{u} R)).map g) (K.sc i)
    change (K.homology i).map g = _ at h
    change ShortComplex.homologyMap ((K.sc i).mapNatTrans
      ((evaluation J (ModuleCat.{u} R)).map g)) ≫ _ = _
    rw [h, Iso.hom_inv_id_assoc])

private lemma homology_preservesFilteredColimitsOfShape
    (J : Type u) [SmallCategory J] [IsFiltered J]
    (R : Type u) [Ring R] (i : ℕ) :
    PreservesColimitsOfShape J
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) i) := by
  let C : (J ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R := colim
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) i
  refine ⟨fun {D} => ?_⟩
  let K := diagramComplex D
  let c : Cocone D :=
    { pt := (C.mapHomologicalComplex _).obj K
      ι := { app j := (NatTrans.mapHomologicalComplex (evaluationToColimit R j) _).app K
             naturality j k f := by
               apply HomologicalComplex.Hom.ext
               funext n
               exact colimit.w (K.X n) f } }
  have hc : IsColimit c := HomologicalComplex.isColimitOfEval D c
    (fun n => colimit.isColimit (K.X n))
  have he : D = K.asFunctor := by rfl
  let e : D ⋙ H ≅ K.homology i := (eqToIso (by rw [he])) ≪≫ homologyDiagramIso K i
  let e' := (K.sc i).mapHomologyIso C
  have h : IsColimit (H.mapCocone c) := by
    let s := (Cocone.precompose e.hom).obj (colimit.cocone (K.homology i))
    have hs : IsColimit s := (IsColimit.precomposeHomEquiv e _).symm (colimit.isColimit _)
    let ec : H.mapCocone c ≅ s := Cocone.ext e' (by
      intro j
      have ht := NatTrans.app_homology (evaluationToColimit R j) (K.sc i)
      show (H.map ((NatTrans.mapHomologicalComplex (evaluationToColimit R j) _).app K)) ≫
        ((K.sc i).mapHomologyIso C).hom =
        ((K.sc i).mapHomologyIso ((evaluation J (ModuleCat.{u} R)).obj j)).hom ≫
          (evaluationToColimit R j).app (K.sc i).homology
      rw [ht, Iso.hom_inv_id_assoc]
      rfl)
    exact IsColimit.ofIsoColimit hs ec.symm
  exact preservesColimit_of_preserves_colimit_cocone hc h

private def tensorComplexFunctor {R : Type u} [CommRing R]
    (P : ChainComplex (ModuleCat.{u} R) ℕ) :
    ModuleCat.{u} R ⥤ ChainComplex (ModuleCat.{u} R) ℕ where
  obj M := tensorComplex M P
  map f := (NatTrans.mapHomologicalComplex
    ((MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).map f) _).app P
  map_id M := by
    apply HomologicalComplex.Hom.ext
    funext j
    exact ((MonoidalCategory.tensoringRight (ModuleCat.{u} R)).obj (P.X j)).map_id M
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext j
    exact ((MonoidalCategory.tensoringRight (ModuleCat.{u} R)).obj (P.X j)).map_comp f g

private def torLeftIso {R : Type u} [CommRing R] (N : ModuleCat.{u} R)
    (P : ProjectiveResolution N) (i : ℕ) :
    (Tor (ModuleCat.{u} R) i).flip.obj N ≅
      tensorComplexFunctor P.complex ⋙ HomologicalComplex.homologyFunctor _ _ i :=
  NatIso.ofComponents (fun M => P.isoLeftDerivedObj
    ((MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).obj M) i)
      (fun f => leftDerived_app_comp_iso_hom
        ((MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).map f) P i)

private lemma tor_preservesFilteredColimits_left (R : Type u) [CommRing R]
    (N : ModuleCat.{u} R) (i : ℕ) :
    PreservesFilteredColimitsOfSize.{u, u} ((Tor (ModuleCat.{u} R) i).flip.obj N) := by
  refine ⟨fun J _ _ => ?_⟩
  let P := projectiveResolution N
  let : PreservesColimitsOfShape J (tensorComplexFunctor P.complex) := by
    apply HomologicalComplex.preservesColimitsOfShape_of_eval
    intro n
    show PreservesColimitsOfShape J (MonoidalCategory.tensorRight (P.complex.X n))
    infer_instance
  let := homology_preservesFilteredColimitsOfShape J R i
  exact preservesColimitsOfShape_of_natIso (torLeftIso N P i).symm

@[sga "7 VIII 1.3" "special case"]
private lemma tor_preservesFilteredColimits_right (R : Type u) [CommRing R]
    (M : ModuleCat.{u} R) (i : ℕ) :
    PreservesFilteredColimitsOfSize.{u, u} ((Tor (ModuleCat.{u} R) i).obj M) :=
  ⟨fun J _ _ => leftDerived_preservesFilteredColimitsOfShape J
    ((MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).obj M) i⟩

private abbrev spanHom {B : Type u} [CommRing B] (M : ModuleCat.{u} B) (m : M) :
    ModuleCat.of B B ⟶ M := ModuleCat.ofHom (LinearMap.toSpanSingleton B M m)

private def functorTensorMap {B : Type u} [CommRing B]
    (F : ModuleCat.{u} B ⥤ AddCommGrpCat.{u}) [F.Additive]
    [Module B (F.obj (ModuleCat.of B B))]
    (hF : ∀ (b : B) (x : F.obj (ModuleCat.of B B)),
      F.map (spanHom (ModuleCat.of B B) b) x = b • x) (M : ModuleCat.{u} B) :
    M ⊗[B] F.obj (ModuleCat.of B B) →+ F.obj M := by
  let f : M →+ F.obj (ModuleCat.of B B) →+ F.obj M :=
    { toFun := fun m => (F.map (spanHom M m)).hom
      map_zero' := by
        have hz : spanHom M 0 = 0 := by ext; simp [spanHom]
        rw [hz, F.map_zero]
        rfl
      map_add' := by
        intro m n
        have ha : spanHom M (m + n) = spanHom M m + spanHom M n := by
          apply ModuleCat.hom_ext
          exact LinearMap.ext fun b => smul_add b m n
        rw [ha, F.map_add]
        rfl }
  refine TensorProduct.liftAddHom f ?_
  intro b m x
  have he : spanHom M (b • m) = spanHom (ModuleCat.of B B) b ≫ spanHom M m := by
    apply ModuleCat.hom_ext
    exact LinearMap.ext fun a => smul_smul a b m
  change F.map (spanHom M (b • m)) x = F.map (spanHom M m) (b • x)
  rw [he, F.map_comp]
  change F.map (spanHom M m) (F.map (spanHom (ModuleCat.of B B) b) x) = _
  rw [hF]

private lemma functorTensorMap_tmul {B : Type u} [CommRing B]
    (F : ModuleCat.{u} B ⥤ AddCommGrpCat.{u}) [F.Additive]
    [Module B (F.obj (ModuleCat.of B B))]
    (hF : ∀ (b : B) (x : F.obj (ModuleCat.of B B)),
      F.map (spanHom (ModuleCat.of B B) b) x = b • x) (M : ModuleCat.{u} B)
    (m : M) (x : F.obj (ModuleCat.of B B)) :
    functorTensorMap F hF M (m ⊗ₜ[B] x) = F.map (spanHom M m) x := rfl

private def functorTensorNatTrans {B : Type u} [CommRing B]
    (F : ModuleCat.{u} B ⥤ AddCommGrpCat.{u}) [F.Additive]
    [Module B (F.obj (ModuleCat.of B B))]
    (hF : ∀ (b : B) (x : F.obj (ModuleCat.of B B)),
      F.map (spanHom (ModuleCat.of B B) b) x = b • x) :
    MonoidalCategory.tensorRight (ModuleCat.of B (F.obj (ModuleCat.of B B))) ⋙
      forget₂ (ModuleCat.{u} B) AddCommGrpCat ⟶ F where
  app M := AddCommGrpCat.ofHom (functorTensorMap F hF M)
  naturality M N f := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul m t =>
      change functorTensorMap F hF N (f m ⊗ₜ[B] t) =
        F.map f (functorTensorMap F hF M (m ⊗ₜ[B] t))
      rw [functorTensorMap_tmul, functorTensorMap_tmul]
      have he : spanHom N (f m) = spanHom M m ≫ f := by
        apply ModuleCat.hom_ext
        exact LinearMap.ext fun b => (f.hom.map_smul b m).symm
      rw [he, F.map_comp]
      rfl

private lemma addCommGrp_sum_apply {ι : Type*} {M N : AddCommGrpCat.{u}}
    (s : Finset ι) (f : ι → (M ⟶ N)) (x : M) :
    (∑ j ∈ s, f j) x = ∑ j ∈ s, f j x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, AddCommGrpCat.hom_add_apply, ih]

private lemma functorTensorMap_bijective_of_finite_free {B : Type u} [CommRing B]
    (F : ModuleCat.{u} B ⥤ AddCommGrpCat.{u}) [F.Additive]
    [Module B (F.obj (ModuleCat.of B B))]
    (hF : ∀ (b : B) (x : F.obj (ModuleCat.of B B)),
      F.map (spanHom (ModuleCat.of B B) b) x = b • x)
    (M : ModuleCat.{u} B) [Module.Free B M] [Module.Finite B M] :
    Function.Bijective (functorTensorMap F hF M) := by
  let b := Module.Free.chooseBasis B M
  let := Fintype.ofFinite (Module.Free.ChooseBasisIndex B M)
  let g (x : F.obj M) : M ⊗[B] F.obj (ModuleCat.of B B) :=
    ∑ j, b j ⊗ₜ[B] (F.map (ModuleCat.ofHom (b.coord j))) x
  have hgadd (x y : F.obj M) : g (x + y) = g x + g y := by
    simp [g, TensorProduct.tmul_add, Finset.sum_add_distrib]
  have hsum : (∑ j, (ModuleCat.ofHom (b.coord j) ≫ spanHom M (b j))) = 𝟙 M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp,
      LinearMap.comp_apply, ModuleCat.hom_ofHom]
    exact b.sum_repr m
  have hr (x : F.obj M) : functorTensorMap F hF M (g x) = x := by
    calc
      functorTensorMap F hF M (g x) =
          ∑ j, (F.map (ModuleCat.ofHom (b.coord j) ≫ spanHom M (b j))) x := by
        simp [g, functorTensorMap_tmul, F.map_comp]
      _ = (F.map (∑ j, ModuleCat.ofHom (b.coord j) ≫ spanHom M (b j))) x := by
        rw [F.map_sum, addCommGrp_sum_apply]
      _ = x := by rw [hsum, F.map_id]; rfl
  have hl (z : M ⊗[B] F.obj (ModuleCat.of B B)) : g (functorTensorMap F hF M z) = z := by
    induction z using TensorProduct.induction_on with
    | zero => simp [g]
    | add x y hx hy => rw [map_add, hgadd, hx, hy]
    | tmul m t =>
      rw [functorTensorMap_tmul]
      show (∑ j, b j ⊗ₜ[B]
        (F.map (ModuleCat.ofHom (b.coord j))) (F.map (spanHom M m) t)) = m ⊗ₜ[B] t
      have he (j : Module.Free.ChooseBasisIndex B M) :
          spanHom M m ≫ ModuleCat.ofHom (b.coord j) =
            spanHom (ModuleCat.of B B) (b.coord j m) := by
        apply ModuleCat.hom_ext
        exact LinearMap.ext fun a => (b.coord j).map_smul a m
      calc
        (∑ j, b j ⊗ₜ[B] (F.map (ModuleCat.ofHom (b.coord j)))
            (F.map (spanHom M m) t)) =
            ∑ j, b j ⊗ₜ[B] ((b.coord j m) • t) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [← AddCommGrpCat.comp_apply, ← F.map_comp, he, hF]
        _ = (∑ j, (b.coord j m) • b j) ⊗ₜ[B] t := by
          simp only [TensorProduct.tmul_smul, TensorProduct.sum_tmul, TensorProduct.smul_tmul']
        _ = m ⊗ₜ[B] t := congrArg (fun m : M => m ⊗ₜ[B] t) (b.sum_repr m)
  exact ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩

private lemma functorTensorMap_bijective_of_flat {B : Type u} [CommRing B]
    (F : ModuleCat.{u} B ⥤ AddCommGrpCat.{u}) [F.Additive]
    [PreservesFilteredColimitsOfSize.{u, u} F]
    [Module B (F.obj (ModuleCat.of B B))]
    (hF : ∀ (b : B) (x : F.obj (ModuleCat.of B B)),
      F.map (spanHom (ModuleCat.of B B) b) x = b • x)
    (M : ModuleCat.{u} B) [Module.Flat B M] :
    Function.Bijective (functorTensorMap F hF M) := by
  obtain ⟨J, _, _, _, _, G, _, _, f, _, hfree, hfinite, ⟨e⟩⟩ :=
    (flat_iff_directLimit_free_finite (R := B) M).mp inferInstance
  let := hfree
  let := hfinite
  let D := ModuleCat.directLimitDiagram G f
  let α := functorTensorNatTrans F hF
  let : ∀ j, IsIso ((D.whiskerLeft α).app j) := fun j => by
    let : Module.Free B (D.obj j) := hfree j
    let : Module.Finite B (D.obj j) := hfinite j
    exact (ConcreteCategory.isIso_iff_bijective _).mpr
      (functorTensorMap_bijective_of_finite_free F hF (D.obj j))
  have hα : IsIso (D.whiskerLeft α) := (NatTrans.isIso_iff_isIso_app _).mpr (fun _ => inferInstance)
  let := hα
  have h := isIso_app_coconePt_of_preservesColimit D α
    (ModuleCat.directLimitCocone G f) (ModuleCat.directLimitIsColimit G f)
  let : IsIso (α.app (ModuleCat.of B (Module.DirectLimit G f))) := h
  let E := e.toModuleIso
  let T := MonoidalCategory.tensorRight (ModuleCat.of B (F.obj (ModuleCat.of B B))) ⋙
    forget₂ (ModuleCat.{u} B) AddCommGrpCat
  have he : α.app M = T.map E.inv ≫ α.app (ModuleCat.of B (Module.DirectLimit G f)) ≫
      F.map E.hom := by
    rw [← α.naturality]
    show α.app M = T.map E.inv ≫ T.map E.hom ≫ α.app M
    rw [← T.map_comp_assoc, E.inv_hom_id, T.map_id, Category.id_comp]
  apply (ConcreteCategory.isIso_iff_bijective (α.app M)).mp
  rw [he]
  infer_instance

private lemma torMap_sameRing {R : Type u} [CommRing R]
    {M N M' N' : ModuleCat.{u} R} (f : M ⟶ M') (g : N ⟶ N') (i : ℕ) :
    ModuleCat.ofHom (torMap f.hom g.hom i) =
      ((Tor (ModuleCat.{u} R) i).map f).app N ≫
        ((Tor (ModuleCat.{u} R) i).obj M').map g := by
  let P := projectiveResolution N
  let Q := projectiveResolution N'
  let F := (MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).obj M
  let F' := (MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).obj M'
  let α := (MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).map f
  let ψ := ProjectiveResolution.lift g P Q
  have hψ : ∀ p : P.complex.X 0, Q.π.f 0 (ψ.f 0 p) = g.hom (P.π.f 0 p) := by
    intro p
    exact congrArg (fun h : P.complex.X 0 ⟶ _ => h p)
      (ProjectiveResolution.lift_commutes_zero g P Q)
  have hφ : tensorComplexMap (algebraMap R R) f.hom ψ =
      (NatTrans.mapHomologicalComplex α _).app P.complex ≫
        (F'.mapHomologicalComplex _).map ψ :=
    tensorComplex_hom_ext fun _ _ _ => rfl
  rw [torMap_eq_of_lift f.hom g.hom P Q ψ hψ i]
  show ModuleCat.ofHom (torMapOfLift f.hom P Q ψ i) =
    (NatTrans.leftDerived α i).app N ≫ (F'.leftDerived i).map g
  rw [P.leftDerived_app_eq α, F'.leftDerived_map_eq i g ψ
    (ProjectiveResolution.lift_commutes g P Q)]
  simp only [Category.assoc]
  show (P.isoLeftDerivedObj F i).hom ≫
      (HomologicalComplex.homologyFunctor _ _ i).map
        (tensorComplexMap (algebraMap R R) f.hom ψ) ≫
      (TorChangeOfRings.homologyRestrictIso R R (tensorComplex M' Q.complex) i).hom ≫
      (Q.isoLeftDerivedObj F' i).inv = _
  rw [hφ, homologyRestrictIso_self]
  simp only [F, F', Functor.comp_map, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_assoc]
  congr 3

private lemma bijective_of_pushout_of_tmul
    {R S C D M N : Type*} [CommRing R] [CommRing S] [CommRing C] [CommRing D]
    [Algebra R S] [Algebra R C] [Algebra R D] [Algebra S D] [Algebra C D]
    [IsScalarTower R S D] [IsScalarTower R C D] [Algebra.IsPushout R S C D]
    [AddCommGroup M] [Module R M] [Module C M] [IsScalarTower R C M]
    [AddCommGroup N] (f : D ⊗[C] M →+ N) (e : S ⊗[R] M →+ N)
    (he : Function.Bijective e)
    (h : ∀ s m, f (algebraMap S D s ⊗ₜ[C] m) = e (s ⊗ₜ[R] m)) :
    Function.Bijective f := by
  let c := Algebra.IsPushout.cancelBaseChange R S C D M
  have hf (x : S ⊗[R] M) : f (c.symm x) = e x := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s m =>
      rw [Algebra.IsPushout.cancelBaseChange_symm_tmul]
      exact h s m
  have hfe : (f : D ⊗[C] M → N) = e ∘ c := by
    funext x
    simpa using hf (c x)
  rw [hfe]
  exact he.comp c.bijective

@[instance_reducible] private def functorModule {B : Type u} [CommRing B]
    (F : ModuleCat.{u} B ⥤ AddCommGrpCat.{u}) [F.Additive] :
    Module B (F.obj (ModuleCat.of B B)) where
  smul b x := F.map (spanHom (ModuleCat.of B B) b) x
  one_smul x := by
    have h : spanHom (ModuleCat.of B B) 1 = 𝟙 _ := by
      apply ModuleCat.hom_ext
      exact LinearMap.ext fun b => mul_one b
    change F.map (spanHom (ModuleCat.of B B) 1) x = x
    rw [h, F.map_id]
    rfl
  mul_smul b c x := by
    have h : spanHom (ModuleCat.of B B) (b * c) =
        spanHom (ModuleCat.of B B) c ≫ spanHom (ModuleCat.of B B) b := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      change a * (b * c) = (a * c) * b
      simp only [mul_assoc, mul_comm b c]
    change F.map (spanHom (ModuleCat.of B B) (b * c)) x =
      F.map (spanHom (ModuleCat.of B B) b) (F.map (spanHom (ModuleCat.of B B) c) x)
    rw [h, F.map_comp]
    rfl
  smul_add b x y := (F.map (spanHom (ModuleCat.of B B) b)).hom.map_add x y
  smul_zero b := (F.map (spanHom (ModuleCat.of B B) b)).hom.map_zero
  add_smul b c x := by
    have h : spanHom (ModuleCat.of B B) (b + c) =
        spanHom (ModuleCat.of B B) b + spanHom (ModuleCat.of B B) c := by
      apply ModuleCat.hom_ext
      exact LinearMap.ext fun a => mul_add a b c
    change F.map (spanHom (ModuleCat.of B B) (b + c)) x =
      F.map (spanHom (ModuleCat.of B B) b) x + F.map (spanHom (ModuleCat.of B B) c) x
    rw [h, F.map_add]
    rfl
  zero_smul x := by
    have h : spanHom (ModuleCat.of B B) 0 = 0 := by
      apply ModuleCat.hom_ext
      exact LinearMap.ext fun a => mul_zero a
    change F.map (spanHom (ModuleCat.of B B) 0) x = 0
    rw [h, F.map_zero]
    rfl

private lemma functorModule_smul {B : Type u} [CommRing B]
    (F : ModuleCat.{u} B ⥤ AddCommGrpCat.{u}) [F.Additive]
    (b : B) (x : F.obj (ModuleCat.of B B)) :
    letI := functorModule F
    b • x = F.map (spanHom (ModuleCat.of B B) b) x := rfl


private lemma bijective_of_flat_functor {A A' C D T T' : Type u}
    [CommRing A] [CommRing A'] [CommRing C] [CommRing D]
    [Algebra A A'] [Algebra A C] [Algebra A D] [Algebra A' D] [Algebra C D]
    [IsScalarTower A A' D] [IsScalarTower A C D] [Algebra.IsPushout A A' C D] [Module.Flat A A']
    [AddCommGroup T] [Module C T] [AddCommGroup T']
    (G : ModuleCat.{u} A ⥤ AddCommGrpCat.{u}) [G.Additive]
    [PreservesFilteredColimitsOfSize.{u, u} G]
    (α : T ≃+ G.obj (ModuleCat.of A A)) (β : T' ≃+ G.obj (ModuleCat.of A A'))
    (hα : ∀ (a : A) (x : T), α (algebraMap A C a • x) =
      G.map (spanHom (ModuleCat.of A A) a) (α x))
    (f : D ⊗[C] T →+ T')
    (hf : ∀ (s : A') (x : T), β (f (algebraMap A' D s ⊗ₜ[C] x)) =
      G.map (spanHom (ModuleCat.of A A') s) (α x)) :
    Function.Bijective f := by
  let : Module A T := Module.compHom T (algebraMap A C)
  have : IsScalarTower A C T := ⟨fun a c x => by
    show (a • c) • x = algebraMap A C a • (c • x)
    rw [Algebra.smul_def, mul_smul]⟩
  let := functorModule G
  let αl : T ≃ₗ[A] G.obj (ModuleCat.of A A) :=
    { α with map_smul' := fun a x => hα a x }
  let g := functorTensorMap G (functorModule_smul G) (ModuleCat.of A A')
  have hg : Function.Bijective g :=
    functorTensorMap_bijective_of_flat G (functorModule_smul G) (ModuleCat.of A A')
  let e : A' ⊗[A] T →+ T' := β.symm.toAddMonoidHom.comp
    (g.comp (LinearEquiv.lTensor A' αl).toLinearMap.toAddMonoidHom)
  have he : Function.Bijective e :=
    β.symm.bijective.comp (hg.comp (LinearEquiv.lTensor A' αl).bijective)
  refine bijective_of_pushout_of_tmul (R := A) (S := A') f e he fun s x => ?_
  apply β.injective
  show β (f _) = β (β.symm (g (s ⊗ₜ[A] α x)))
  rw [hf, AddEquiv.apply_symm_apply]
  rfl

private def restrictIso (R A X : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup X] [Module R X] [Module A X] [IsScalarTower R A X] :
    ModuleCat.of R X ≅ (ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A X) :=
  let e : X ≃ₗ[R] (ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A X) :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        exact (algebraMap_smul A r x).symm }
  e.toModuleIso

private lemma restrictIso_apply (R A X : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup X] [Module R X] [Module A X] [IsScalarTower R A X] (x : X) :
    (restrictIso R A X).hom x = (show X from x) := rfl

private lemma tor_flip_additive (R : Type u) [CommRing R] (N : ModuleCat.{u} R) (i : ℕ) :
    ((Tor (ModuleCat.{u} R) i).flip.obj N).Additive where
  map_add {X Y} f g := by
    let := tor_additive R i
    show ((Tor (ModuleCat.{u} R) i).map (f + g)).app N = _
    rw [Functor.map_add]
    rfl

private lemma restrictScalars_preservesFilteredColimits {R S : Type u} [CommRing R] [CommRing S]
    (ρ : R →+* S) : PreservesFilteredColimitsOfSize.{u, u} (ModuleCat.restrictScalars.{u} ρ) :=
  ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩

private lemma mulLinear_one_eq_id (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    ModuleCat.ofHom (TorChangeOfRings.mulLinear R A 1) = 𝟙 (ModuleCat.of R A) := by
  apply ModuleCat.hom_ext
  exact LinearMap.ext fun x => one_mul x

private lemma torModule_tmul_one (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℕ) (a : A) (x : TorChangeOfRings.torObj R i A B) :
    letI := torModule R A B i
    (a ⊗ₜ[R] (1 : B)) • x =
      ((Tor (ModuleCat.{u} R) i).flip.obj (ModuleCat.of R B)).map
        (ModuleCat.ofHom (TorChangeOfRings.mulLinear R A a)) x := by
  rw [torModule_tmul, mulLinear_one_eq_id, CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

private lemma mulLinear_comp_restrictIso (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (a : A) : ModuleCat.ofHom (TorChangeOfRings.mulLinear R A a) ≫ (restrictIso R A A).hom =
      (restrictIso R A A).hom ≫
        (ModuleCat.restrictScalars (algebraMap R A)).map (spanHom (ModuleCat.of A A) a) := by
  apply ModuleCat.hom_ext
  exact LinearMap.ext fun y => mul_comm a y

private lemma torSystem_isIso_extensionMap_left (R A A' B : Type u)
    [CommRing R] [CommRing A] [CommRing A'] [CommRing B]
    [Algebra R A] [Algebra R A'] [Algebra R B]
    (fA : A →ₐ[R] A') (hA : RingHom.Flat fA.toRingHom) (i : ℕ) :
    IsIso (torSystem.extensionMap R R A B A' B i fA (AlgHom.id R B)) := by
  let : Algebra A A' := fA.toRingHom.toAlgebra
  let : Module.Flat A A' := hA
  let : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq fun r => (fA.commutes r).symm
  let C := A ⊗[R] B
  let D := A' ⊗[R] B
  let θ : C →+* D := TorChangeOfRings.tensorProductMap R R A B A' B fA (AlgHom.id R B)
  let : Algebra C D := θ.toAlgebra
  let : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq fun a => by
    simp [RingHom.algebraMap_toAlgebra, θ, C, D, TorChangeOfRings.tensorProductMap]
  have : Algebra.IsPushout A A' C D := by
    apply Algebra.IsPushout.tensorProduct_tensorProduct
    ext b
    simp [RingHom.algebraMap_toAlgebra, θ, C, D, TorChangeOfRings.tensorProductMap]
  let := torModule R A B i
  let := torModule R A' B i
  let := tor_additive R i
  let := tor_flip_additive R (ModuleCat.of R B) i
  let := tor_preservesFilteredColimits_left R (ModuleCat.of R B) i
  let := restrictScalars_preservesFilteredColimits (algebraMap R A)
  let F := (Tor (ModuleCat.{u} R) i).flip.obj (ModuleCat.of R B)
  let G := ModuleCat.restrictScalars.{u} (algebraMap R A) ⋙ F ⋙
    forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  let α : TorChangeOfRings.torObj R i A B ≃+ G.obj (ModuleCat.of A A) :=
    (F.mapIso (restrictIso R A A)).toLinearEquiv.toAddEquiv
  let β : TorChangeOfRings.torObj R i A' B ≃+ G.obj (ModuleCat.of A A') :=
    (F.mapIso (restrictIso R A A')).toLinearEquiv.toAddEquiv
  let f := torSystem.extensionMap R R A B A' B i fA (AlgHom.id R B)
  let e := baseChangeTensorIso (S := D) (ModuleCat.of C (TorChangeOfRings.torObj R i A B))
  have hf : Function.Bijective (f.hom.comp e.inv.hom) := by
    refine bijective_of_flat_functor (A := A) (A' := A') (C := C) (D := D) G α β ?_
      (f.hom.comp e.inv.hom).toAddMonoidHom ?_
    · intro a x
      have ha : algebraMap A C a = a ⊗ₜ[R] (1 : B) := rfl
      rw [ha, torModule_tmul_one]
      show (F.map (ModuleCat.ofHom (TorChangeOfRings.mulLinear R A a)) ≫
        F.map (restrictIso R A A).hom) x =
        (F.map (restrictIso R A A).hom ≫ F.map ((ModuleCat.restrictScalars (algebraMap R A)).map
          (spanHom (ModuleCat.of A A) a))) x
      rw [← F.map_comp, ← F.map_comp, mulLinear_comp_restrictIso]
    · intro s x
      have h1 : (f.hom.comp e.inv.hom) (algebraMap A' D s ⊗ₜ[C] x) =
          (s ⊗ₜ[R] (1 : B)) • torSystem.map R R A B A' B i fA (AlgHom.id R B) x := by
        show f ((algebraMap A' D s) ⊗ₜ[C, θ] x) = _
        rw [show (algebraMap A' D s) ⊗ₜ[C, θ] x =
            (algebraMap A' D s) • ((1 : D) ⊗ₜ[C, θ] x) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul]
        rw [extensionMap_one_tmul]
        rfl
      have h2 : torSystem.map R R A B A' B i fA (AlgHom.id R B) x =
          F.map (ModuleCat.ofHom (fA.toLinearMap)) x := by
        have h := torMap_sameRing (ModuleCat.ofHom (fA.toLinearMap)) (𝟙 (ModuleCat.of R B)) i
        rw [CategoryTheory.Functor.map_id, Category.comp_id] at h
        exact ConcreteCategory.congr_hom h x
      have hm : ModuleCat.ofHom fA.toLinearMap ≫ ModuleCat.ofHom (TorChangeOfRings.mulLinear R A' s)
        ≫
          (restrictIso R A A').hom = (restrictIso R A A).hom ≫
            (ModuleCat.restrictScalars (algebraMap R A)).map (spanHom (ModuleCat.of A A') s) := by
        apply ModuleCat.hom_ext
        exact LinearMap.ext fun y => mul_comm s (fA y)
      show β ((f.hom.comp e.inv.hom) (algebraMap A' D s ⊗ₜ[C] x)) =
        (F.map (restrictIso R A A).hom ≫
        F.map ((ModuleCat.restrictScalars (algebraMap R A)).map (spanHom (ModuleCat.of A A') s))) x
      rw [h1, h2, torModule_tmul_one, ← F.map_comp, ← hm, F.map_comp, F.map_comp]
      rfl
  exact isIso_of_bijective_comp_baseChangeTensorIso f hf

private lemma torModule_one_tmul (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℕ) (b : B) (x : TorChangeOfRings.torObj R i A B) :
    letI := torModule R A B i
    ((1 : A) ⊗ₜ[R] b) • x =
      ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R A)).map
        (ModuleCat.ofHom (TorChangeOfRings.mulLinear R B b)) x := by
  rw [torModule_tmul, mulLinear_one_eq_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp]

private lemma tor_obj_additive (R : Type u) [CommRing R] (M : ModuleCat.{u} R) (i : ℕ) :
    ((Tor (ModuleCat.{u} R) i).obj M).Additive :=
  leftDerived_additive ((MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).obj M) i

private lemma torSystem_isIso_extensionMap_right (R A B B' : Type u)
    [CommRing R] [CommRing A] [CommRing B] [CommRing B']
    [Algebra R A] [Algebra R B] [Algebra R B']
    (fB : B →ₐ[R] B') (hB : RingHom.Flat fB.toRingHom) (i : ℕ) :
    IsIso (torSystem.extensionMap R R A B A B' i (AlgHom.id R A) fB) := by
  let : Algebra B B' := fB.toRingHom.toAlgebra
  let : Module.Flat B B' := hB
  have : IsScalarTower R B B' := IsScalarTower.of_algebraMap_eq fun r => (fB.commutes r).symm
  let C := A ⊗[R] B
  let D := A ⊗[R] B'
  let θ : C →+* D := TorChangeOfRings.tensorProductMap R R A B A B' (AlgHom.id R A) fB
  let : Algebra C D := θ.toAlgebra
  let : Algebra B C := Algebra.TensorProduct.rightAlgebra
  let : Algebra B' D := Algebra.TensorProduct.rightAlgebra
  let : Algebra B D := ((algebraMap B' D).comp (algebraMap B B')).toAlgebra
  have : IsScalarTower B C D := IsScalarTower.of_algebraMap_eq fun b => by
    simp [RingHom.algebraMap_toAlgebra, θ, C, D, TorChangeOfRings.tensorProductMap]
  have : IsScalarTower B B' D := IsScalarTower.of_algebraMap_eq fun b => by
    simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower R C D := IsScalarTower.of_algebraMap_eq fun r => by
    simp [RingHom.algebraMap_toAlgebra, θ, C, D, TorChangeOfRings.tensorProductMap]
  have : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq fun r => by
    simp [RingHom.algebraMap_toAlgebra, D]
  have : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq fun a => by
    simp [RingHom.algebraMap_toAlgebra, θ, C, D, TorChangeOfRings.tensorProductMap]
  have : Algebra.IsPushout B B' C D := by
    have h2 : Algebra.IsPushout R B' A D := TensorProduct.isPushout'
    exact (Algebra.IsPushout.comp_iff R B A C (T := B') (T' := D)).mp h2
  let := torModule R A B i
  let := torModule R A B' i
  let := tor_obj_additive R (ModuleCat.of R A) i
  let := tor_preservesFilteredColimits_right R (ModuleCat.of R A) i
  let := restrictScalars_preservesFilteredColimits (algebraMap R B)
  let F := (Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R A)
  let G := ModuleCat.restrictScalars.{u} (algebraMap R B) ⋙ F ⋙
    forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  let α : TorChangeOfRings.torObj R i A B ≃+ G.obj (ModuleCat.of B B) :=
    (F.mapIso (restrictIso R B B)).toLinearEquiv.toAddEquiv
  let β : TorChangeOfRings.torObj R i A B' ≃+ G.obj (ModuleCat.of B B') :=
    (F.mapIso (restrictIso R B B')).toLinearEquiv.toAddEquiv
  let f := torSystem.extensionMap R R A B A B' i (AlgHom.id R A) fB
  let e := baseChangeTensorIso (S := D) (ModuleCat.of C (TorChangeOfRings.torObj R i A B))
  have hf : Function.Bijective (f.hom.comp e.inv.hom) := by
    refine bijective_of_flat_functor (A := B) (A' := B') (C := C) (D := D) G α β ?_
      (f.hom.comp e.inv.hom).toAddMonoidHom ?_
    · intro b x
      have hb : algebraMap B C b = (1 : A) ⊗ₜ[R] b := rfl
      rw [hb, torModule_one_tmul]
      show (F.map (ModuleCat.ofHom (TorChangeOfRings.mulLinear R B b)) ≫
        F.map (restrictIso R B B).hom) x =
        (F.map (restrictIso R B B).hom ≫ F.map ((ModuleCat.restrictScalars (algebraMap R B)).map
          (spanHom (ModuleCat.of B B) b))) x
      rw [← F.map_comp, ← F.map_comp, mulLinear_comp_restrictIso]
    · intro s x
      have h1 : (f.hom.comp e.inv.hom) (algebraMap B' D s ⊗ₜ[C] x) =
          ((1 : A) ⊗ₜ[R] s) • torSystem.map R R A B A B' i (AlgHom.id R A) fB x := by
        show f ((algebraMap B' D s) ⊗ₜ[C, θ] x) = _
        rw [show (algebraMap B' D s) ⊗ₜ[C, θ] x =
            (algebraMap B' D s) • ((1 : D) ⊗ₜ[C, θ] x) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul]
        rw [extensionMap_one_tmul]
        rfl
      have h2 : torSystem.map R R A B A B' i (AlgHom.id R A) fB x =
          F.map (ModuleCat.ofHom (fB.toLinearMap)) x := by
        have h := torMap_sameRing (𝟙 (ModuleCat.of R A)) (ModuleCat.ofHom (fB.toLinearMap)) i
        rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at h
        exact ConcreteCategory.congr_hom h x
      have hm : ModuleCat.ofHom fB.toLinearMap ≫
          ModuleCat.ofHom (TorChangeOfRings.mulLinear R B' s) ≫
          (restrictIso R B B').hom = (restrictIso R B B).hom ≫
            (ModuleCat.restrictScalars (algebraMap R B)).map (spanHom (ModuleCat.of B B') s) := by
        apply ModuleCat.hom_ext
        exact LinearMap.ext fun y => mul_comm s (fB y)
      show β ((f.hom.comp e.inv.hom) (algebraMap B' D s ⊗ₜ[C] x)) =
        (F.map (restrictIso R B B).hom ≫
        F.map ((ModuleCat.restrictScalars (algebraMap R B)).map
          (spanHom (ModuleCat.of B B') s))) x
      rw [h1, h2, torModule_one_tmul, ← F.map_comp, ← hm, F.map_comp, F.map_comp]
      rfl
  exact isIso_of_bijective_comp_baseChangeTensorIso f hf
private def semilinearExtension {C D T T' : Type u} [CommRing C] [CommRing D]
    [AddCommGroup T] [Module C T] [AddCommGroup T'] [Module D T'] (θ : C →+* D)
    (g : T →ₛₗ[θ] T') :
    (ModuleCat.extendScalars θ).obj (ModuleCat.of C T) ⟶ ModuleCat.of D T' :=
  ((ModuleCat.extendRestrictScalarsAdj θ).homEquiv (ModuleCat.of C T) (ModuleCat.of D T')).symm
    (ModuleCat.homEquiv.symm
      { toFun := g
        map_add' := g.map_add
        map_smul' := g.map_smul' })

private lemma semilinearExtension_one_tmul {C D T T' : Type u} [CommRing C] [CommRing D]
    [AddCommGroup T] [Module C T] [AddCommGroup T'] [Module D T'] (θ : C →+* D)
    (g : T →ₛₗ[θ] T') (x : T) :
    semilinearExtension θ g ((1 : D) ⊗ₜ[C, θ] x) = g x := by
  show (1 : D) • g x = _
  exact one_smul _ _

private lemma isIso_semilinearExtension_comp {C C' C'' T T' T'' : Type u}
    [CommRing C] [CommRing C'] [CommRing C'']
    [AddCommGroup T] [Module C T] [AddCommGroup T'] [Module C' T']
    [AddCommGroup T''] [Module C'' T'']
    (θ₁ : C →+* C') (θ₂ : C' →+* C'') (θ : C →+* C'') (hθ : θ = θ₂.comp θ₁)
    (g₁ : T →ₛₗ[θ₁] T') (g₂ : T' →ₛₗ[θ₂] T'') (g : T →ₛₗ[θ] T'')
    (hg : ∀ x, g x = g₂ (g₁ x))
    (h₁ : IsIso (semilinearExtension θ₁ g₁)) (h₂ : IsIso (semilinearExtension θ₂ g₂)) :
    IsIso (semilinearExtension θ g) := by
  subst hθ
  have he : semilinearExtension (θ₂.comp θ₁) g =
      (ModuleCat.extendScalarsComp θ₁ θ₂).hom.app (ModuleCat.of C T) ≫
        (ModuleCat.extendScalars θ₂).map (semilinearExtension θ₁ g₁) ≫
          semilinearExtension θ₂ g₂ := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    rw [semilinearExtension_one_tmul, hg]
    show _ = semilinearExtension θ₂ g₂ ((ModuleCat.extendScalars θ₂).map
      (semilinearExtension θ₁ g₁)
      ((ModuleCat.extendScalarsComp θ₁ θ₂).hom.app (ModuleCat.of C T) ((1 : C'') ⊗ₜ x)))
    rw [ModuleCat.extendScalarsComp_hom_app_one_tmul, ModuleCat.ExtendScalars.map_tmul,
      semilinearExtension_one_tmul, semilinearExtension_one_tmul]
  rw [he]
  infer_instance

private lemma torSystem_extensionMap_eq (R A B A' B' : Type u)
    [CommRing R] [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra R B'] (i : ℕ)
    (fA : A →ₐ[R] A') (fB : B →ₐ[R] B') :
    letI := torModule R A B i
    letI := torModule R A' B' i
    torSystem.extensionMap R R A B A' B' i fA fB =
      semilinearExtension _ (torSystem.map R R A B A' B' i fA fB) := rfl

private lemma torSystem_flat_algebra_extension (R A B A' B' : Type u)
    [CommRing R] [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra R B']
    (fA : A →ₐ[R] A') (fB : B →ₐ[R] B')
    (hA : RingHom.Flat fA.toRingHom) (hB : RingHom.Flat fB.toRingHom) (i : ℕ) :
    IsIso (torSystem.extensionMap R R A B A' B' i fA fB) := by
  let := torModule R A B i
  let := torModule R A' B i
  let := torModule R A' B' i
  have h₁ := torSystem_isIso_extensionMap_left R A A' B fA hA i
  have h₂ := torSystem_isIso_extensionMap_right R A' B B' fB hB i
  rw [torSystem_extensionMap_eq] at h₁ h₂ ⊢
  refine isIso_semilinearExtension_comp _ _ _ ?_ (torSystem.map R R A B A' B i fA (AlgHom.id R B))
    (torSystem.map R R A' B A' B' i (AlgHom.id R A') fB) _ (fun x => ?_) h₁ h₂
  · apply RingHom.ext
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b => simp [TorChangeOfRings.tensorProductMap]
  · have h := torSystem_map_comp R R R A B A' B A' B' i fA (AlgHom.id R B) (AlgHom.id R A') fB x
    have hA' : ((AlgHom.id R A').restrictScalars R).comp fA = fA := AlgHom.ext fun _ => rfl
    have hB' : (fB.restrictScalars R).comp (AlgHom.id R B) = fB := AlgHom.ext fun _ => rfl
    rw [hA', hB'] at h
    exact h

end

namespace TorChangeOfRings

/-- The canonical tensor-product actions and functorial change-of-rings maps on Tor, together
with their coherence, flat base-change, and flat algebra-extension comparisons. -/
@[ega "IV 11.2.1" "special case"]
public theorem canonicalSystem_nonempty : Nonempty { S : System // S.IsCanonical } :=
  ⟨⟨torSystem, torSystem_isCanonical torSystem_flat_baseChange
    torSystem_flat_algebra_extension⟩⟩

/-- A choice of the canonical tensor-product actions and functorial change-of-rings maps
on Tor, given a proof that such a system exists. -/
public def canonicalSystem (h : Nonempty { S : System // S.IsCanonical }) :
    { S : System // S.IsCanonical } :=
  Classical.choice h

/-- The coherence laws of the canonical change-of-rings system. -/
public abbrev canonicalLaws (h : Nonempty { S : System // S.IsCanonical }) :
    (canonicalSystem h).1.IsCanonical := (canonicalSystem h).2

/-- The canonical `A ⊗[R] B`-module structure on `Tor_i^R(A,B)`. -/
public abbrev moduleStructure (h : Nonempty { S : System // S.IsCanonical })
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℕ) : Module (A ⊗[R] B) (torObj R i A B) :=
  (canonicalSystem h).1.action R A B i

/-- The canonical tensor-product action extends the original `R`-module structure on Tor. -/
public instance moduleStructure_isScalarTower (h : Nonempty { S : System // S.IsCanonical })
    (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (i : ℕ) :
    letI := moduleStructure h R A B i
    IsScalarTower R (A ⊗[R] B) (torObj R i A B) :=
  (canonicalSystem h).1.action_tower R A B i

/-- The canonical change-of-rings map, semilinear over the induced map of tensor-product
algebras. -/
public def changeMap (h : Nonempty { S : System // S.IsCanonical })
    (R R' A B A' B' : Type u)
    [CommRing R] [CommRing R'] [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra R R'] [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra R B']
    [Algebra R' A'] [Algebra R' B'] [IsScalarTower R R' A'] [IsScalarTower R R' B']
    (i : ℕ) (fA : A →ₐ[R] A') (fB : B →ₐ[R] B') :
    letI := moduleStructure h R A B i
    letI := moduleStructure h R' A' B' i
    torObj R i A B →ₛₗ[tensorProductMap R R' A B A' B' fA fB] torObj R' i A' B' :=
  (canonicalSystem h).1.map R R' A B A' B' i fA fB

/-- The canonical change-of-rings map after extension of scalars to the target
tensor-product algebra. -/
public def extensionMap (h : Nonempty { S : System // S.IsCanonical })
    (R R' A B A' B' : Type u)
    [CommRing R] [CommRing R'] [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra R R'] [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra R B']
    [Algebra R' A'] [Algebra R' B'] [IsScalarTower R R' A'] [IsScalarTower R R' B']
    (i : ℕ) (fA : A →ₐ[R] A') (fB : B →ₐ[R] B') :
    letI := moduleStructure h R A B i
    letI := moduleStructure h R' A' B' i
    (ModuleCat.extendScalars (tensorProductMap R R' A B A' B' fA fB)).obj
        (ModuleCat.of (A ⊗[R] B) (torObj R i A B)) ⟶
      ModuleCat.of (A' ⊗[R'] B') (torObj R' i A' B') :=
  (canonicalSystem h).1.extensionMap R R' A B A' B' i fA fB

/-- The canonical Tor comparison is invertible when both algebras are independently extended
by flat maps over a fixed base ring. -/
public theorem isIso_extensionMap_of_flat_algebra
    (h : Nonempty { S : System // S.IsCanonical })
    (R A B A' B' : Type u)
    [CommRing R] [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra R B']
    (fA : A →ₐ[R] A') (fB : B →ₐ[R] B')
    (hA : RingHom.Flat fA.toRingHom) (hB : RingHom.Flat fB.toRingHom) (i : ℕ) :
    IsIso (extensionMap h R R A B A' B' i fA fB) :=
  (canonicalLaws h).flat_algebra_extension R A B A' B' fA fB hA hB i

end TorChangeOfRings

end
