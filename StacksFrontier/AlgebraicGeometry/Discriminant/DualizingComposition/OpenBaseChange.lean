module

public import StacksFrontier.AlgebraicGeometry.Different.DualizingModulesQuasi.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingBaseChange.Independence
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingComposition.Trace

/-!
# The trace map across an open base change

Let `A → R → B → C` be rings with `R → B` flat and a ring epimorphism, as happens when `B` is
the target of a finite-open factorization with intermediate algebra `R`. Then the relative
dualizing module of `C` over `B` is computed from a finite-open factorization of `C` over `R`
by base change, and composing with a functional on `R` gives a map to the relative dualizing
module of `C` over `A`. This is the second of the two halves out of which the composition map
for relative dualizing modules is built.

## Main definitions

* `Stacks.Discriminant.dualizingModule.traceAfterOpenBaseChange` is that map.
* `Stacks.Discriminant.dualizingModule.traceAfterOpenBaseChangeComp` reads it as a map linear in
  the functional on `R` over `A`, followed by a `C`-linear map out of its target.
* `Stacks.Discriminant.dualizingModule.compatibleTensorLift` lifts a compatible ring map to the
  scalar extension, which is how a factorization of `C` over `R` is compared with one over `B`.
* `Stacks.Discriminant.dualizingModule.dualMapOfFlatEpi` turns an `A`-linear functional into an
  `S`-linear one under the flat-epimorphism hypothesis.

## Main results

* `Stacks.Discriminant.dualizingModule.traceAfterOpenBaseChange_tmul_of_compatible` computes the
  map on the pure tensors coming from a compatible pair of factorizations.
* `Stacks.Discriminant.dualizingModule.traceAfterOpenBaseChange_naturality`: the map is
  independent of the finite-open factorization of `C` over `R`.
* `Stacks.Discriminant.dualizingModule.openBaseChange_induction` is the induction principle
  that reduces a statement about the dualizing module over `B` to those pure tensors.

## Implementation notes

The scalar extension `B ⊗[R] C` is identified with `C` because `R → B` is a ring epimorphism;
the resulting isomorphism is used both to retarget a factorization of `C` over `B` and to
transport the module structures. Flatness of `B` over `R` is what makes the dualizing module
over `B` the base change of the one over `R`, which is where the lift along the base change
comes from.

## References

* [Stacks Project, Tag 0BT4](https://stacks.math.columbia.edu/tag/0BT4)
-/

@[expose] public section

open scoped TensorProduct

universe u v w x y z x'

namespace Stacks.Discriminant

namespace dualizingModule

attribute [local instance] algebraDualModule

/-- The identification `B ⊗[R] C ≃ₐ[B] C` along a ring epimorphism sends `1 ⊗ₜ c` to `c`. -/
private lemma tensorEpiLmulEquiv_one_tmul
    {R : Type*} {B : Type*} {C : Type*}
    [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra B C] [Algebra R C] [IsScalarTower R B C]
    (hepi : Algebra.IsEpi R B) (c : C) :
    tensorEpiLmulEquiv hepi (1 ⊗ₜ[R] c) = c := by
  rw [tensorEpiLmulEquiv_tmul, map_one, one_mul]

/-- Restricting a `C`-module along the identification `B ⊗[R] C ≃ₐ[B] C` makes it a scalar tower
over `C` and `B ⊗[R] C`. -/
private lemma isScalarTower_tensorEpi_compHom
    {R : Type*} {B : Type*} {C : Type*}
    [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra B C] [Algebra R C] [IsScalarTower R B C]
    (hepi : Algebra.IsEpi R B) (Z : Type*) [AddCommMonoid Z] [Module C Z] :
    letI : Algebra C (B ⊗[R] C) := Algebra.TensorProduct.rightAlgebra
    letI : Module (B ⊗[R] C) Z := Module.compHom Z (tensorEpiLmulEquiv hepi).toRingHom
    IsScalarTower C (B ⊗[R] C) Z := by
  let : Algebra C (B ⊗[R] C) := Algebra.TensorProduct.rightAlgebra
  let : Module (B ⊗[R] C) Z := Module.compHom Z (tensorEpiLmulEquiv hepi).toRingHom
  exact .of_algebraMap_smul fun c m =>
    congrArg (· • m) (tensorEpiLmulEquiv_one_tmul hepi c)

/-- A `C`-linear map out of `M` assembled from an additive map `r` that is semilinear along a
function `σ : C → T`, a `T`-linear comparison `cmp`, and a `T`-linear map `tr`, in the situation
where the `T`-action on the target restricts along `σ` to its `C`-action.

Taking the three ingredients separately makes the `C`-linearity of the composite a consequence of
`hr` and `hσ`, each of which is a statement about one ingredient.  Assembling the composite first
and proving its linearity afterwards would instead require the elaborator to compare the two
scalar actions on the target through the whole composite. -/
def linearMapOfSemilinearComp
    {C : Type*} {T : Type*} {M : Type*} {N : Type*} {P : Type*} {Z : Type*}
    [Semiring C] [Semiring T] [AddCommMonoid M] [Module C M] [AddCommMonoid N] [Module T N]
    [AddCommMonoid P] [Module T P] [AddCommMonoid Z] [Module T Z] [Module C Z]
    (σ : C → T) (r : M →+ N) (cmp : N ≃ₗ[T] P) (tr : P →ₗ[T] Z)
    (hr : ∀ (c : C) (m : M), r (c • m) = σ c • r m)
    (hσ : ∀ (c : C) (z : Z), σ c • z = c • z) :
    M →ₗ[C] Z where
  toFun m := tr (cmp (r m))
  map_add' m n := by simp only [map_add]
  map_smul' c m := by simp only [RingHom.id_apply, hr, map_smul, hσ]

/-- The value of `linearMapOfSemilinearComp` is the composite of its three ingredients. -/
lemma linearMapOfSemilinearComp_apply
    {C : Type*} {T : Type*} {M : Type*} {N : Type*} {P : Type*} {Z : Type*}
    [Semiring C] [Semiring T] [AddCommMonoid M] [Module C M] [AddCommMonoid N] [Module T N]
    [AddCommMonoid P] [Module T P] [AddCommMonoid Z] [Module T Z] [Module C Z]
    (σ : C → T) (r : M →+ N) (cmp : N ≃ₗ[T] P) (tr : P →ₗ[T] Z)
    (hr : ∀ (c : C) (m : M), r (c • m) = σ c • r m)
    (hσ : ∀ (c : C) (z : Z), σ c • z = c • z) (m : M) :
    linearMapOfSemilinearComp σ r cmp tr hr hσ m = tr (cmp (r m)) :=
  rfl

/-- The trace map on relative dualizing modules for a composite `A → R → B → C` in which
`R → B` is a flat ring epimorphism: the dualizing module of `C` over `B` maps to the dualizing
module of `C` over `A`. -/
noncomputable def traceAfterOpenBaseChange
    {A : Type u} {R : Type v} {B : Type w} {C : Type x}
    [CommRing A] [CommRing R] [CommRing B] [CommRing C]
    [Algebra A R] [Algebra R B] [Algebra B C] [Algebra R C]
    [IsScalarTower R B C] [Algebra A C] [IsScalarTower A R C]
    [Module.Finite A R] [IsNoetherianRing R] [IsNoetherianRing B]
    [Module.Flat R B] (hepi : Algebra.IsEpi R B)
    (K : FiniteOpenFactorization.{v, x, y} R C)
    (G : FiniteOpenFactorization.{w, x, z} B C)
    (f : Module.Dual A R) :
    dualizingModule G →ₗ[C]
      dualizingModule (restrictBaseFactorization (A := A) K) := by
  let T := B ⊗[R] C
  letI : Algebra C T := Algebra.TensorProduct.rightAlgebra
  let e : T ≃ₐ[B] C := tensorEpiLmulEquiv hepi
  let Kb := FiniteOpenFactorization.baseChange K B
  let Gt := retargetFactorization G e.symm
  let Z := dualizingModule (restrictBaseFactorization (A := A) K)
  let N := dualizingModule Kb
  letI : Module C N := Module.compHom _ (algebraMap C T)
  letI : IsScalarTower C T N := IsScalarTower.of_compHom C T N
  let hbc := dualizingModule_isBaseChange_of_flat K B
  letI : Module T Z := Module.compHom _ e.toRingHom
  letI : IsScalarTower C T Z := IsScalarTower.of_algebraMap_smul (fun c m => by
    change e (1 ⊗ₜ[R] c) • m = c • m
    rw [tensorEpiLmulEquiv_one_tmul])
  let tr := hbc.lift (finiteTrace K f)
  refine linearMapOfSemilinearComp (fun c => e.symm c) (retargetDualizingMap G e.symm)
    (dualizingModuleEquiv Gt Kb) tr (retargetDualizingMap_smul G e.symm) ?_
  intro c z
  change e (e.symm c) • z = c • z
  rw [e.apply_symm_apply]

/-- The trace map after an open base change is additive in the functional on the finite
base extension. -/
lemma traceAfterOpenBaseChange_add
    {A : Type u} {R : Type v} {B : Type w} {C : Type x}
    [CommRing A] [CommRing R] [CommRing B] [CommRing C]
    [Algebra A R] [Algebra R B] [Algebra B C] [Algebra R C]
    [IsScalarTower R B C] [Algebra A C] [IsScalarTower A R C]
    [Module.Finite A R] [IsNoetherianRing R] [IsNoetherianRing B]
    [Module.Flat R B] (hepi : Algebra.IsEpi R B)
    (K : FiniteOpenFactorization.{v, x, y} R C)
    (G : FiniteOpenFactorization.{w, x, z} B C)
    (f g : Module.Dual A R) :
    traceAfterOpenBaseChange hepi K G (f + g) =
      traceAfterOpenBaseChange hepi K G f + traceAfterOpenBaseChange hepi K G g := by
  refine LinearMap.ext fun m => ?_
  simp only [traceAfterOpenBaseChange, linearMapOfSemilinearComp_apply, finiteTrace_add,
    isBaseChange_lift_add, LinearMap.add_apply]

/-- The trace map after an open base change is linear in the functional on the finite base
extension. -/
lemma traceAfterOpenBaseChange_smul
    {A : Type u} {R : Type v} {B : Type w} {C : Type x}
    [CommRing A] [CommRing R] [CommRing B] [CommRing C]
    [Algebra A R] [Algebra R B] [Algebra B C] [Algebra R C]
    [IsScalarTower R B C] [Algebra A C] [IsScalarTower A R C]
    [Module.Finite A R] [IsNoetherianRing R] [IsNoetherianRing B]
    [Module.Flat R B] (hepi : Algebra.IsEpi R B)
    (K : FiniteOpenFactorization.{v, x, y} R C)
    (G : FiniteOpenFactorization.{w, x, z} B C)
    (r : R) (f : Module.Dual A R) :
    traceAfterOpenBaseChange hepi K G (r • f) =
      algebraMap R C r • traceAfterOpenBaseChange hepi K G f := by
  refine LinearMap.ext fun m => ?_
  simp only [traceAfterOpenBaseChange, linearMapOfSemilinearComp_apply, finiteTrace_smul,
    isBaseChange_lift_smul, LinearMap.smul_apply]

/-- The trace map after an open base change, read as an `R`-linear map in the functional and
followed by a `C`-linear map `t` out of the relative dualizing module of `C` over `A`.

The target `Z` of `t` is arbitrary, carrying actions of `C` and of `R` that agree through
`algebraMap R C`, which is the hypothesis `ht`.  Assembling the linear map here, where `R` is a
type variable, is what keeps it usable: a consumer that instead builds it in a context where `R`
is the intermediate algebra of a factorization has to compare the two sides of
`traceAfterOpenBaseChange_add` with `R` substituted, and unfolding the resulting composite of
base changes and localization isomorphisms is enormous. -/
noncomputable def traceAfterOpenBaseChangeComp
    {A : Type u} {R : Type v} {B : Type w} {C : Type x} {Z : Type x'}
    [CommRing A] [CommRing R] [CommRing B] [CommRing C]
    [Algebra A R] [Algebra R B] [Algebra B C] [Algebra R C]
    [IsScalarTower R B C] [Algebra A C] [IsScalarTower A R C]
    [Module.Finite A R] [IsNoetherianRing R] [IsNoetherianRing B]
    [Module.Flat R B] (hepi : Algebra.IsEpi R B)
    (K : FiniteOpenFactorization.{v, x, y} R C)
    (G : FiniteOpenFactorization.{w, x, z} B C)
    [AddCommGroup Z] [Module C Z] [Module R Z] [SMulCommClass C R Z]
    (t : dualizingModule (restrictBaseFactorization (A := A) K) →ₗ[C] Z)
    (ht : ∀ (r : R) (z : Z), algebraMap R C r • z = r • z) :
    Module.Dual A R →ₗ[R] (dualizingModule G →ₗ[C] Z) where
  toFun f := t.comp (traceAfterOpenBaseChange hepi K G f)
  map_add' f g := by
    rw [traceAfterOpenBaseChange_add, LinearMap.comp_add]
  map_smul' r f := by
    rw [RingHom.id_apply, traceAfterOpenBaseChange_smul]
    refine LinearMap.ext fun m => ?_
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul] using ht r _

/-- The value of `traceAfterOpenBaseChangeComp` is the trace map followed by `t`. -/
lemma traceAfterOpenBaseChangeComp_apply
    {A : Type u} {R : Type v} {B : Type w} {C : Type x} {Z : Type x'}
    [CommRing A] [CommRing R] [CommRing B] [CommRing C]
    [Algebra A R] [Algebra R B] [Algebra B C] [Algebra R C]
    [IsScalarTower R B C] [Algebra A C] [IsScalarTower A R C]
    [Module.Finite A R] [IsNoetherianRing R] [IsNoetherianRing B]
    [Module.Flat R B] (hepi : Algebra.IsEpi R B)
    (K : FiniteOpenFactorization.{v, x, y} R C)
    (G : FiniteOpenFactorization.{w, x, z} B C)
    [AddCommGroup Z] [Module C Z] [Module R Z] [SMulCommClass C R Z]
    (t : dualizingModule (restrictBaseFactorization (A := A) K) →ₗ[C] Z)
    (ht : ∀ (r : R) (z : Z), algebraMap R C r • z = r • z)
    (f : Module.Dual A R) (m : dualizingModule G) :
    traceAfterOpenBaseChangeComp hepi K G t ht f m =
      t (traceAfterOpenBaseChange hepi K G f m) :=
  rfl

/-- Additivity of the trace map after an open base change, read off at one element of the
relative dualizing module. -/
lemma traceAfterOpenBaseChange_add_apply
    {A : Type u} {R : Type v} {B : Type w} {C : Type x}
    [CommRing A] [CommRing R] [CommRing B] [CommRing C]
    [Algebra A R] [Algebra R B] [Algebra B C] [Algebra R C]
    [IsScalarTower R B C] [Algebra A C] [IsScalarTower A R C]
    [Module.Finite A R] [IsNoetherianRing R] [IsNoetherianRing B]
    [Module.Flat R B] (hepi : Algebra.IsEpi R B)
    (K : FiniteOpenFactorization.{v, x, y} R C)
    (G : FiniteOpenFactorization.{w, x, z} B C)
    (f g : Module.Dual A R) (m : dualizingModule G) :
    traceAfterOpenBaseChange hepi K G (f + g) m =
      traceAfterOpenBaseChange hepi K G f m + traceAfterOpenBaseChange hepi K G g m := by
  rw [traceAfterOpenBaseChange_add, LinearMap.add_apply]

/-- Linearity of the trace map after an open base change, read off at one element of the
relative dualizing module. -/
lemma traceAfterOpenBaseChange_smul_apply
    {A : Type u} {R : Type v} {B : Type w} {C : Type x}
    [CommRing A] [CommRing R] [CommRing B] [CommRing C]
    [Algebra A R] [Algebra R B] [Algebra B C] [Algebra R C]
    [IsScalarTower R B C] [Algebra A C] [IsScalarTower A R C]
    [Module.Finite A R] [IsNoetherianRing R] [IsNoetherianRing B]
    [Module.Flat R B] (hepi : Algebra.IsEpi R B)
    (K : FiniteOpenFactorization.{v, x, y} R C)
    (G : FiniteOpenFactorization.{w, x, z} B C)
    (r : R) (f : Module.Dual A R) (m : dualizingModule G) :
    traceAfterOpenBaseChange hepi K G (r • f) m =
      algebraMap R C r • traceAfterOpenBaseChange hepi K G f m := by
  rw [traceAfterOpenBaseChange_smul, LinearMap.smul_apply]

/-- The trace map after an open base change does not depend on the chosen finite-open
factorization of `C` over `R`. -/
lemma traceAfterOpenBaseChange_naturality
    {A : Type u} {R : Type v} {B : Type w} {C : Type x}
    [CommRing A] [CommRing R] [CommRing B] [CommRing C]
    [Algebra A R] [Algebra R B] [Algebra B C] [Algebra R C]
    [IsScalarTower R B C] [Algebra A C] [IsScalarTower A R C]
    [Module.Finite A R] [IsNoetherianRing A] [IsNoetherianRing R] [IsNoetherianRing B]
    [Module.Flat R B] (hepi : Algebra.IsEpi R B)
    (K : FiniteOpenFactorization.{v, x, y} R C)
    (L : FiniteOpenFactorization.{v, x, z} R C)
    (G : FiniteOpenFactorization.{w, x, x'} B C)
    (f : Module.Dual A R) (m : dualizingModule G) :
    traceAfterOpenBaseChange hepi L G f m =
      dualizingModuleEquiv (restrictBaseFactorization (A := A) K)
        (restrictBaseFactorization (A := A) L)
        (traceAfterOpenBaseChange hepi K G f m) := by
  let T := B ⊗[R] C
  let : Algebra C T := Algebra.TensorProduct.rightAlgebra
  let e : T ≃ₐ[B] C := tensorEpiLmulEquiv hepi
  let : Algebra T C := e.toRingHom.toAlgebra
  let Kb := FiniteOpenFactorization.baseChange K B
  let Lb := FiniteOpenFactorization.baseChange L B
  let Gt := retargetFactorization G e.symm
  let JK := restrictBaseFactorization (A := A) K
  let JL := restrictBaseFactorization (A := A) L
  let ZK := dualizingModule JK
  let ZL := dualizingModule JL
  let NK := dualizingModule Kb
  let NL := dualizingModule Lb
  let : Module C NK := Module.compHom _ (algebraMap C T)
  let : Module C NL := Module.compHom _ (algebraMap C T)
  let : IsScalarTower C T NK := IsScalarTower.of_compHom C T NK
  let : IsScalarTower C T NL := IsScalarTower.of_compHom C T NL
  let : Module T ZK := Module.compHom _ e.toRingHom
  let : Module T ZL := Module.compHom _ e.toRingHom
  let : IsScalarTower T C ZK := IsScalarTower.of_compHom T C ZK
  let : IsScalarTower T C ZL := IsScalarTower.of_compHom T C ZL
  let : IsScalarTower C T ZK := isScalarTower_tensorEpi_compHom hepi ZK
  let : IsScalarTower C T ZL := isScalarTower_tensorEpi_compHom hepi ZL
  let hK := dualizingModule_isBaseChange_of_flat K B
  let hL := dualizingModule_isBaseChange_of_flat L B
  let tK := hK.lift (finiteTrace K f)
  let tL := hL.lift (finiteTrace L f)
  let eKL := dualizingModuleEquiv Kb Lb
  let eJ := dualizingModuleEquiv JK JL
  have ht : tL.comp eKL.toLinearMap = (eJ.toLinearMap.restrictScalars T).comp tK := by
    apply hK.algHom_ext
    intro n
    change tL (eKL (dualizingModule.baseChange K B n)) = eJ (tK _)
    rw [dualizingModule.baseChange_congr K L B, IsBaseChange.lift_eq, IsBaseChange.lift_eq]
    exact finiteTrace_naturality K L f n
  let n := retargetDualizingMap G e.symm m
  have hc := congrArg (fun φ : NK →ₗ[T] ZL => φ (dualizingModuleEquiv Gt Kb n)) ht
  have he := congrArg (fun φ : dualizingModule Gt ≃ₗ[T] NL => φ n)
    (dualizingModuleEquiv_trans Gt Kb Lb)
  change tL (dualizingModuleEquiv Gt Lb n) = eJ (tK _)
  exact he ▸ hc

/-- A ring map `S → T` over `R → B` that is `R`-linear lifts to an algebra map
`B ⊗[R] S → T` over `B`. -/
def compatibleTensorLift
    {R : Type u} {B : Type v} {S : Type w} {T : Type x}
    [CommRing R] [CommRing B] [CommRing S] [CommRing T]
    [Algebra R B] [Algebra R S] [Algebra B T]
    (j : S →+* T)
    (hj : ∀ r, j (algebraMap R S r) = algebraMap B T (algebraMap R B r)) :
    B ⊗[R] S →ₐ[B] T := by
  letI : Algebra R T := ((algebraMap B T).comp (algebraMap R B)).toAlgebra
  letI : IsScalarTower R B T := IsScalarTower.of_algebraMap_eq' rfl
  let j' : S →ₐ[R] T := { j with commutes' := hj }
  let l := Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R B T) j'
    (fun _ _ => Commute.all _ _)
  exact { l.toRingHom with commutes' := fun b => by simp [l] }

/-- The lift of a compatible ring map to the scalar extension multiplies out a pure
tensor. -/
lemma compatibleTensorLift_tmul
    {R : Type u} {B : Type v} {S : Type w} {T : Type x}
    [CommRing R] [CommRing B] [CommRing S] [CommRing T]
    [Algebra R B] [Algebra R S] [Algebra B T]
    (j : S →+* T)
    (hj : ∀ r, j (algebraMap R S r) = algebraMap B T (algebraMap R B r))
    (b : B) (s : S) :
    compatibleTensorLift j hj (b ⊗ₜ[R] s) = algebraMap B T b * j s := by
  simp [compatibleTensorLift]

/-- The lift is surjective as soon as the image of the original map spans the target over
`B`. -/
lemma compatibleTensorLift_surjective
    {R : Type u} {B : Type v} {S : Type w} {T : Type x}
    [CommRing R] [CommRing B] [CommRing S] [CommRing T]
    [Algebra R B] [Algebra R S] [Algebra B T]
    (j : S →+* T)
    (hj : ∀ r, j (algebraMap R S r) = algebraMap B T (algebraMap R B r))
    (hspan : Submodule.span B (Set.range j) = ⊤) :
    Function.Surjective (compatibleTensorLift j hj) := by
  suffices (compatibleTensorLift j hj).toLinearMap.range = ⊤ from
    (LinearMap.range_eq_top (f := (compatibleTensorLift j hj).toLinearMap)).mp this
  apply top_unique
  rw [← hspan, Submodule.span_le]
  rintro _ ⟨s, rfl⟩
  exact ⟨1 ⊗ₜ[R] s, by simp [compatibleTensorLift_tmul]⟩

/-- A functional on `T` restricting along a compatible map to the scalar extension of a
functional on `S` is the base change of the latter. -/
lemma baseChangeDual_eq_comp_compatibleTensorLift
    {R : Type u} {B : Type v} {S : Type w} {T : Type x}
    [CommRing R] [CommRing B] [CommRing S] [CommRing T]
    [Algebra R B] [Algebra R S] [Algebra B T]
    (j : S →+* T)
    (hj : ∀ r, j (algebraMap R S r) = algebraMap B T (algebraMap R B r))
    (g : Module.Dual B T) (g' : Module.Dual R S)
    (hg : ∀ t, g (j t) = algebraMap R B (g' t)) :
    g'.baseChange B = g.comp (compatibleTensorLift j hj).toLinearMap := by
  refine TensorProduct.AlgebraTensorModule.ext fun b s => ?_
  simp only [Module.Dual.baseChange_apply_tmul, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, compatibleTensorLift_tmul]
  rw [← Algebra.smul_def, map_smul, hg, Algebra.smul_def, smul_eq_mul, mul_comm]

/-- On a pure tensor whose functional descends along a compatible map of intermediate
algebras, the trace map after an open base change composes the two functionals. -/
lemma traceAfterOpenBaseChange_tmul_of_compatible
    {A : Type u} {R : Type v} {B : Type w} {C : Type x}
    [CommRing A] [CommRing R] [CommRing B] [CommRing C]
    [Algebra A R] [Algebra R B] [Algebra B C] [Algebra R C]
    [IsScalarTower R B C] [Algebra A C] [IsScalarTower A R C]
    [Module.Finite A R] [IsNoetherianRing R] [IsNoetherianRing B]
    [Module.Flat R B] (hepi : Algebra.IsEpi R B)
    (K : FiniteOpenFactorization.{v, x, y} R C)
    (G : FiniteOpenFactorization.{w, x, z} B C)
    (j : K.middle →+* G.middle)
    (hjR : ∀ r, j (algebraMap R K.middle r) =
      algebraMap B G.middle (algebraMap R B r))
    (hjC : ∀ t, algebraMap G.middle C (j t) = algebraMap K.middle C t)
    (hspan : Submodule.span B (Set.range j) = ⊤)
    (f : Module.Dual A R) (g : Module.Dual B G.middle)
    (g' : Module.Dual R K.middle)
    (hg : ∀ t, g (j t) = algebraMap R B (g' t)) (c : C) :
    letI : Algebra A K.middle := ((algebraMap R K.middle).comp (algebraMap A R)).toAlgebra
    letI : IsScalarTower A R K.middle := IsScalarTower.of_algebraMap_eq' rfl
    traceAfterOpenBaseChange hepi K G f (dualizingModule.tmul G g c) =
      dualizingModule.tmul (restrictBaseFactorization K) (dualComp f g') c := by
  let : Algebra A K.middle := ((algebraMap R K.middle).comp (algebraMap A R)).toAlgebra
  let : IsScalarTower A R K.middle := IsScalarTower.of_algebraMap_eq' rfl
  let T := B ⊗[R] C
  let : Algebra C T := Algebra.TensorProduct.rightAlgebra
  let e : T ≃ₐ[B] C := tensorEpiLmulEquiv hepi
  let Kb := FiniteOpenFactorization.baseChange K B
  let Gt := retargetFactorization G e.symm
  let l : Kb.middle →ₐ[B] Gt.middle := compatibleTensorLift j hjR
  have hlT (t : Kb.middle) : algebraMap Gt.middle T (l t) = algebraMap Kb.middle T t := by
    apply e.injective
    change e (e.symm (algebraMap G.middle C (compatibleTensorLift j hjR t))) =
      e (Algebra.TensorProduct.map (AlgHom.id R B) (IsScalarTower.toAlgHom R K.middle C) t)
    rw [e.apply_symm_apply]
    induction t using TensorProduct.inductionOn with
    | add t s ht hs => simp only [map_add, ht, hs]
    | tmul b t =>
      change algebraMap G.middle C (compatibleTensorLift j hjR (b ⊗ₜ[R] t)) =
        tensorEpiLmulEquiv hepi (b ⊗ₜ[R] algebraMap K.middle C t)
      rw [compatibleTensorLift_tmul, map_mul,
        ← IsScalarTower.algebraMap_apply B G.middle C, hjC, tensorEpiLmulEquiv_tmul]
  have hec : e.symm c = 1 ⊗ₜ[R] c :=
    e.symm_apply_eq.mpr (tensorEpiLmulEquiv_one_tmul hepi c).symm
  have hfun : g.comp l.toLinearMap = g'.baseChange B :=
    (baseChangeDual_eq_comp_compatibleTensorLift j hjR g g' hg).symm
  let Z := dualizingModule (restrictBaseFactorization (A := A) K)
  let N := dualizingModule Kb
  let : Module C N := Module.compHom _ (algebraMap C T)
  let : IsScalarTower C T N := IsScalarTower.of_compHom C T N
  let : Module T Z := Module.compHom _ e.toRingHom
  let : IsScalarTower C T Z := isScalarTower_tensorEpi_compHom hepi Z
  let hbc := dualizingModule_isBaseChange_of_flat K B
  change hbc.lift (finiteTrace K f)
    (dualizingModuleEquiv Gt Kb
      (retargetDualizingMap G e.symm (dualizingModule.tmul G g c))) = _
  rw [retargetDualizingMap_tmul, comparison_tmul_of_surjective Kb Gt l
      (compatibleTensorLift_surjective j hjR hspan) hlT,
    hfun, hec, ← dualizingModule.baseChange_tmul,
    IsBaseChange.lift_eq, finiteTrace_tmul]

/-- For a flat ring epimorphism `R → B` and an intermediate algebra `S` embedded in `B`, the
two pure tensors of an element of `S` in `B ⊗[R] S` agree. -/
lemma tmul_one_eq_one_tmul_of_flat_epi
    {R : Type u} {S : Type v} {B : Type w}
    [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
    [Module.Flat R B] (hepi : Algebra.IsEpi R B)
    (hinj : Function.Injective (algebraMap S B)) (s : S) :
    algebraMap S B s ⊗ₜ[R] (1 : S) = (1 : B) ⊗ₜ[R] s := by
  apply Module.Flat.lTensor_preserves_injective_linearMap
    (M := B) (IsScalarTower.toAlgHom R S B).toLinearMap hinj
  simpa only [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom,
    map_one] using! ((Algebra.isEpi_iff_forall_one_tmul_eq R B).mp hepi (algebraMap S B s)).symm

/-- An `R`-linear map to `B` out of an `S`-module is `S`-linear, when `R → B` is a flat ring
epimorphism and `S` embeds in `B`. -/
lemma map_smul_of_flat_epi
    {R : Type u} {S : Type v} {B : Type w} {M : Type x}
    [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [Module.Flat R B] (hepi : Algebra.IsEpi R B)
    (hinj : Function.Injective (algebraMap S B)) (f : M →ₗ[R] B) (s : S) (m : M) :
    f (s • m) = algebraMap S B s * f m := by
  let g : S →ₗ[R] B := f.comp ((LinearMap.toSpanSingleton S M m).restrictScalars R)
  simpa only [LinearMap.liftBaseChange_tmul, g, LinearMap.comp_apply,
    LinearMap.coe_restrictScalars, LinearMap.toSpanSingleton_apply, one_smul, smul_eq_mul,
    one_mul] using
    (congrArg (g.liftBaseChange B) (tmul_one_eq_one_tmul_of_flat_epi hepi hinj s)).symm

/-- An `A`-linear functional on an `S`-module becomes `S`-linear after composing with
`A → S`, under the flat-epimorphism hypothesis. -/
def dualMapOfFlatEpi
    {R : Type u} {S : Type v} {B : Type w} {M : Type x}
    [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [Module.Flat R B] (hepi : Algebra.IsEpi R B)
    (hinj : Function.Injective (algebraMap S B)) (f : Module.Dual R M) :
    Module.Dual S M where
  toFun m := algebraMap R S (f m)
  map_add' m n := by rw [map_add, map_add]
  map_smul' s m := by
    apply hinj
    change algebraMap S B (algebraMap R S (f (s • m))) =
      algebraMap S B (s * algebraMap R S (f m))
    rw [map_mul, ← IsScalarTower.algebraMap_apply R S B,
      ← IsScalarTower.algebraMap_apply R S B]
    exact map_smul_of_flat_epi hepi hinj ((Algebra.linearMap R B).comp f) s m

/-- To prove a property of every element of the relative dualizing module of `C` over `B` it
suffices to treat sums, scalar multiples, and the images of the pure tensors coming from
a finite-open factorization of `C` over `R`. -/
lemma openBaseChange_induction
    {R : Type u} {B : Type v} {C : Type w}
    [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra B C] [Algebra R C] [IsScalarTower R B C]
    [IsNoetherianRing R] [IsNoetherianRing B] [Module.Flat R B]
    (hepi : Algebra.IsEpi R B)
    (K : FiniteOpenFactorization.{u, w, x} R C)
    (G : FiniteOpenFactorization.{v, w, y} B C)
    {P : dualizingModule G → Prop}
    (htmul : ∀ (f : Module.Dual R K.middle) (c : C),
      P (dualizingModuleEquiv
          (retargetFactorization (FiniteOpenFactorization.baseChange K B)
            (tensorEpiLmulEquiv hepi)) G
        (dualizingModule.tmul
          (retargetFactorization (FiniteOpenFactorization.baseChange K B)
            (tensorEpiLmulEquiv hepi)) (f.baseChange B) c)))
    (hadd : ∀ m n, P m → P n → P (m + n))
    (hsmul : ∀ (c : C) m, P m → P (c • m)) (m : dualizingModule G) : P m := by
  let Kb := FiniteOpenFactorization.baseChange K B
  let e : B ⊗[R] C ≃ₐ[B] C := tensorEpiLmulEquiv hepi
  let G₀ := retargetFactorization Kb e
  let T := B ⊗[R] C
  let : Algebra C T := Algebra.TensorProduct.rightAlgebra
  let N := dualizingModule Kb
  let : Module C N := Module.compHom _ (algebraMap C T)
  let : IsScalarTower C T N := IsScalarTower.of_compHom C T N
  let hbc := dualizingModule_isBaseChange_of_flat K B
  obtain ⟨n, rfl⟩ := (dualizingModuleEquiv G₀ G).surjective m
  obtain ⟨n, rfl⟩ := (retargetDualizingMap_bijective Kb e).surjective n
  obtain ⟨n, rfl⟩ := hbc.equiv.surjective n
  induction n using TensorProduct.inductionOn with
  | add m n hm hn => simpa only [map_add] using hadd _ _ hm hn
  | tmul t n =>
    rw [hbc.equiv_tmul, retargetDualizingMap_smul, map_smul]
    apply hsmul
    induction n using dualizingModule.induction_on K with
    | add m n hm hn => simpa only [map_add] using hadd _ _ hm hn
    | tmul f c =>
      have hstep : retargetDualizingMap Kb e
            (dualizingModule.baseChange K B (dualizingModule.tmul K f c)) =
          dualizingModule.tmul G₀ (f.baseChange B) c := by
        rw [dualizingModule.baseChange_tmul]
        exact (retargetDualizingMap_tmul Kb e (f.baseChange B) ((1 : B) ⊗ₜ[R] c)).trans
          (by rw [tensorEpiLmulEquiv_one_tmul hepi c])
      change P (dualizingModuleEquiv G₀ G (retargetDualizingMap Kb e
        (dualizingModule.baseChange K B (dualizingModule.tmul K f c))))
      rw [hstep]
      exact htmul f c

/-- The image of the right inclusion spans a scalar extension over the extended base. -/
lemma span_range_includeRight
    {R : Type u} {B : Type v} {S : Type w}
    [CommRing R] [CommRing B] [CommRing S] [Algebra R B] [Algebra R S] :
    Submodule.span B (Set.range
      (Algebra.TensorProduct.includeRight : S →ₐ[R] B ⊗[R] S)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro t
  induction t using TensorProduct.inductionOn with
  | add t s ht hs => exact Submodule.add_mem _ ht hs
  | tmul b s =>
    rw [← mul_one b, ← smul_eq_mul, ← TensorProduct.smul_tmul']
    exact Submodule.smul_mem _ b (Submodule.subset_span ⟨s, rfl⟩)

/-- Under the flat-epimorphism hypothesis, the right inclusion of an intermediate algebra
into a scalar extension agrees with the left one. -/
lemma includeRight_algebraMap_of_flat_epi
    {R : Type u} {S : Type v} {B : Type w} {L : Type x}
    [CommRing R] [CommRing S] [CommRing B] [CommRing L]
    [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
    [Algebra R L] [Algebra S L] [IsScalarTower R S L]
    [Module.Flat R B] (hepi : Algebra.IsEpi R B)
    (hinj : Function.Injective (algebraMap S B)) (s : S) :
    (1 : B) ⊗ₜ[R] algebraMap S L s = algebraMap S B s ⊗ₜ[R] (1 : L) := by
  simpa only [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom,
    map_one] using! (congrArg ((IsScalarTower.toAlgHom R S L).toLinearMap.lTensor B)
      (tmul_one_eq_one_tmul_of_flat_epi hepi hinj s)).symm

end dualizingModule

end Stacks.Discriminant
