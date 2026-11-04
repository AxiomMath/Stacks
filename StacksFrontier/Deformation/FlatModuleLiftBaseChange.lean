module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.FinitelyPresented.FreeMapAtGenericFibre
public import StacksFrontier.Deformation.ExtBaseChangeVanishing
public import StacksFrontier.Deformation.ToposThickening.CanonicalObstructionBaseChange
public import StacksFrontier.Homology.Tor.DerivedTensorFlatBaseChange

/-!
# The two lifting problems of a flat finite module along a thickening

Let `A' → A` be a surjection of commutative rings with nilpotent kernel whose thickening
`P' → P` is square-zero, let `P' → Q'` be a flat map of flat `A'`-algebras, and let
`P = P' ⊗_{A'} A` and `Q = Q' ⊗_{A'} A` be their base changes. The thickening `Q' → Q` is then
square-zero automatically (`Deformation.sq_ker_algebraMap_tensorProduct_eq_bot_of_tower`).
For a `P`-module `M` which is finite over `P` and flat over `A`, Stacks 0DZ2 compares
the problem of lifting `M` to an `A'`-flat `P'`-module with that of lifting `M ⊗_P Q` to an
`A'`-flat `Q'`-module. This file completes that comparison.

The obstruction class of `M` lives in `Hom_{D(P)}(K, (K ⊗^𝐋_P I/I²)[2])` for `K` the single
complex on `M`. Because the kernel `I` of `P' → P` is the base change of the kernel of `A' → A`
and `M` is `A`-flat, the target of that morphism is again a single complex, so the obstruction
class is an element of `Ext²_P(M, M ⊗_P I)`; the comparison with the obstruction class over `Q`
is then the vanishing criterion for a flat base change of `Ext`.

## Main results

* `Deformation.exists_singleIso_obstructionTarget`: the target of the canonical obstruction
  morphism of a module flat over the base is a single complex. This is the derived tensor
  computation of Stacks 0DZ2, with the kernel identification of Stacks 0DYR.
* `Deformation.sq_ker_algebraMap_tensorProduct_eq_bot_of_tower`: squareness of the thickening
  `P' → P` is inherited by the thickening `Q' → Q` of any `P'`-algebra `Q'`, so only one of the
  two thickenings in Stacks 0DZ2's diagram has to be assumed square-zero.
* `Deformation.exists_flat_lift_iff_exists_flat_lift_baseChange_of_finite`: the comparison with
  the obstruction morphism assumed `J`-power torsion. This is the form the proof below supports;
  the tag Stacks 0DZ2 sits on the stronger statement in
  `StacksFrontier.Deformation.FlatModuleLiftLocalization`, which replaces that assumption by the
  source's local liftability.

## Implementation notes

**What the comparison here assumes, and where the tag lives.** The theorem below assumes that
the obstruction morphism of `M` is killed by a power of every element of `J`, which is the form
its proof uses. The source assumes instead that `M` is locally liftable: for every `g ∈ J'` the
localization `M_g` has an `A'`-flat `(P')_g`-module lift. That hypothesis implies this one, by
base change of the canonical obstruction morphism of Stacks 0DYR(3) at the localization squares
together with the `Ext` base change of Stacks 0A6A — the route the source's proof of Stacks 05EC
takes — and the derivation is carried out in
`StacksFrontier.Deformation.FlatModuleLiftLocalization`, where the tag now sits. The theorem below
is what that one is proved from, and is kept because it is the shape the obstruction calculus
produces.

**Which 0A6A.** Three modules cite Stacks 0A6A. The one used is the `Ext`-tensor circle of
`StacksFrontier.Homology.HomComplex.RHom.HomModuleBaseChange`, through
`Deformation.ExtBaseChange.one_tmul_eq_zero_of_comp_mk₀_unit_eq_zero` and
`StacksDraft.DerivedHom.SingleBaseChange.ext_comp_mk₀_unit_eq_zero`: it carries no tag of its
own, is the Stacks 087Q comparison for a finite module over a Noetherian ring, and turns the
vanishing of a derived base change into `1 ⊗ x = 0` with no torsion hypothesis.
`StacksDraft.Homology.HomComplex.RHom.BaseChange.isIso_derivedHomBaseChange` is avoided because
its attribute is clause-qualified on the Stacks 0E1V side, and
`StacksFrontier.RingTheory.Dualizing.LocalizationCriterion` is avoided because it cites 0A6A only
in prose and proves a dualizing-complex criterion instead.

**The remaining departures from the source, and the dévissage.** Two gaps remain, both
disclosed at the tag.

1. **`M` is assumed finite over `P`.** The source assumes only that `M` is an `A`-flat
   `P`-module. Its proof compares `Ext²_P(M, M ⊗_P I)` with `Ext²_Q(M ⊗_P Q, (M ⊗_P I) ⊗_P Q)`,
   and that base change of `Ext` along the flat map `P → Q` is an isomorphism only for `M`
   finite over `P`; so `Module.Finite P M` is assumed. This is a correction of the source and
   not a deviation from it: the comparison genuinely fails for a non-finite `A`-flat `M`, with
   `Ext` out of an infinite direct sum producing an infinite product that the flat base change
   does not commute with. The counterexample, the identification of the half of the comparison
   that needs no finiteness, and the proof that no weaker coherence condition is available over
   a Noetherian `P` are all in the implementation notes of
   `StacksFrontier.Deformation.FlatModuleLiftLocalization`.
2. **The thickening `P' → P` is assumed square-zero.** The source assumes only that it is
   nilpotent. Writing `I = ker(A' → A)`, the kernel of `P' → P` is `I · P'`, so the hypothesis
   `hzeroP` is exactly `I² · P' = 0`. This is the only remaining deviation in the kernels: the
   kernel of `A' → A` itself is assumed only nilpotent, as in the source, and squareness of the
   second thickening `Q' → Q` is not assumed but derived, by
   `Deformation.sq_ker_algebraMap_tensorProduct_eq_bot_of_tower`.

   The dévissage closing this gap is the one the source leaves as `details omitted`, and it is
   diagnosed in full — what the step needs, and the counterexample to it — in the
   implementation notes of `StacksFrontier.Deformation.FlatModuleLiftLocalization`. In brief:
   `Deformation.squareZero_devissage` would need its `hcomp` for the motive "the comparison
   holds for this thickening", and the backward direction of `hcomp` fails because the
   intermediate `A''`-flat lift `M''` of `M` is produced by an *existence* statement. All of
   0DZ2's hypotheses, local liftability included, transport to the stage `A'' → A`; what the
   second stage then needs is that the obstruction class of the square-zero step `A' → A''` be
   independent of which `A''`-flat `P''`-lift of `M` it is evaluated on, and over
   `A' = k[t]/(t³)`, `P' = k[t, x]/(t³, x²)` the module `M = k` has an `A'`-flat `P'`-lift
   while its `A''`-flat `P''`-lift `P''/(x - t)` has none. Running the dévissage on the
   obstruction side instead does
   not help: `Deformation.exists_flat_lift_iff_canonicalObstructionMap_eq_zero` tolerates a
   nilpotent kernel on `A' → A`, but it takes `hzeroP` as an argument and passes it to
   `Deformation.Obstruction.canonicalObstructionMap`, because the canonical class of Stacks
   0DYR is *defined* only for a square-zero surjection; over a merely nilpotent `P' → P` there
   is no single class to compare, only the tower of classes of the successive square-zero
   quotients, and the same two inputs are what that tower needs.

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
* [Stacks Project, Tag 0DYR](https://stacks.math.columbia.edu/tag/0DYR)
* [Stacks Project, Tag 087Q](https://stacks.math.columbia.edu/tag/087Q)
* [Stacks Project, Tag 05EC](https://stacks.math.columbia.edu/tag/05EC)
* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.DerivedTensor CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

universe u

namespace Deformation

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-! ### The obstruction target of a module flat over the base -/

/-- The square `A' → A`, `A' → P'`, `A → P`, `P' → P` of a base change `P = P' ⊗_{A'} A`
commutes. -/
theorem algebraMap_comp_tensorProduct_comm (A' A P' : Type u) [CommRing A'] [CommRing A]
    [CommRing P'] [Algebra A' A] [Algebra A' P'] :
    (algebraMap A (TensorProduct A' P' A)).comp (algebraMap A' A) =
      (algebraMap P' (TensorProduct A' P' A)).comp (algebraMap A' P') := by
  refine RingHom.ext fun x => ?_
  have h1 : (algebraMap A (TensorProduct A' P' A)).comp (algebraMap A' A) x =
      (1 : P') ⊗ₜ[A'] (algebraMap A' A x) := rfl
  have h2 : (algebraMap P' (TensorProduct A' P' A)).comp (algebraMap A' P') x =
      (algebraMap A' P' x) ⊗ₜ[A'] (1 : A) := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [h1, h2, Algebra.algebraMap_eq_smul_one (R := A') (A := A) x,
    Algebra.algebraMap_eq_smul_one (R := A') (A := P') x, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul']

/-- `P = P' ⊗_{A'} A` is flat over `A` when `P'` is flat over `A'`. -/
theorem flat_base_of_tensorProduct (A' A P' : Type u) [CommRing A'] [CommRing A] [CommRing P']
    [Algebra A' A] [Algebra A' P'] [Module.Flat A' P'] :
    Module.Flat A (TensorProduct A' P' A) :=
  Module.Flat.of_linearEquiv (Algebra.TensorProduct.commRight A' A P').symm.toLinearEquiv

/-- The kernel of `Q' → Q' ⊗_{A'} A` is the extension of the kernel of `P' → P' ⊗_{A'} A`. -/
private theorem ker_algebraMap_tensorProduct_eq_map_of_tower
    (A' A P' Q' : Type u) [CommRing A'] [CommRing A] [CommRing P'] [CommRing Q']
    [Algebra A' A] [Algebra A' P'] [Algebra A' Q'] [Algebra P' Q'] [IsScalarTower A' P' Q']
    [Module.Flat A' P'] [Module.Flat A' Q'] :
    RingHom.ker (algebraMap Q' (TensorProduct A' Q' A)) =
      Ideal.map (algebraMap P' Q') (RingHom.ker (algebraMap P' (TensorProduct A' P' A))) := by
  rw [Algebra.ker_algebraMap_tensorProduct_left A' P' A, Ideal.map_map,
    Algebra.ker_algebraMap_tensorProduct_left A' Q' A, IsScalarTower.algebraMap_eq A' P' Q']

/-- **Squareness of a thickening propagates along the flat horizontal arrows.** If the kernel of
`P' → P' ⊗_{A'} A` has square zero and `Q'` is a `P'`-algebra, then so does the kernel of
`Q' → Q' ⊗_{A'} A`.

Both kernels are the extension of `I = ker(A' → A)`, so the hypothesis says that every element
of `I²` already dies in `P'`, and an element dying in `P'` dies in every `P'`-algebra.
Consequently the Q-side square-zero hypothesis of the obstruction calculus is not an extra
assumption on the diagram of Stacks 0DZ2: of the two thickenings `P' → P` and `Q' → Q` only the
first has to be cut down from the source's nilpotence to square zero. -/
theorem sq_ker_algebraMap_tensorProduct_eq_bot_of_tower
    (A' A P' Q' : Type u) [CommRing A'] [CommRing A] [CommRing P'] [CommRing Q']
    [Algebra A' A] [Algebra A' P'] [Algebra A' Q'] [Algebra P' Q'] [IsScalarTower A' P' Q']
    [Module.Flat A' P'] [Module.Flat A' Q']
    (hzeroP : (RingHom.ker (algebraMap P' (TensorProduct A' P' A))) ^ 2 = ⊥) :
    (RingHom.ker (algebraMap Q' (TensorProduct A' Q' A))) ^ 2 = ⊥ := by
  rw [ker_algebraMap_tensorProduct_eq_map_of_tower A' A P' Q', ← Ideal.map_pow, hzeroP,
    Ideal.map_bot]

/-- **Stacks 0DZ2, the derived tensor computation of the obstruction target.** For `M` a
`P`-module flat over `A`, where `P = P' ⊗_{A'} A`, the target `K ⊗^𝐋_P I/I²` of the canonical
obstruction morphism of Stacks 0DYR is a module placed in degree zero: the kernel `I` of
`P' → P` is the base change of the kernel of `A' → A`, and all higher Tor modules of an
`A`-flat module against a module base-changed from `A` vanish. -/
theorem exists_singleIso_obstructionTarget
    (A' A P' : Type u) [CommRing A'] [CommRing A] [CommRing P']
    [Algebra A' A] [Algebra A' P'] [Module.Flat A' P']
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hsurjP : Function.Surjective (algebraMap P' (TensorProduct A' P' A)))
    (M : Type u) [AddCommGroup M] [Module (TensorProduct A' P' A) M] [Module A M]
    [IsScalarTower A (TensorProduct A' P' A) M] [Module.Flat A M]
    (K : DerivedCategory (ModuleCat.{u} (TensorProduct A' P' A)))
    (eK : K ≅ DerivedCategory.Q.obj ((CochainComplex.singleFunctor
      (ModuleCat.{u} (TensorProduct A' P' A)) 0).obj
        (ModuleCat.of (TensorProduct A' P' A) (ULift.{u} M)))) :
    ∃ (N : Type u) (_ : AddCommGroup N) (_ : Module (TensorProduct A' P' A) N),
      Nonempty ((((canonicalDerivedTensorProductFunctor (TensorProduct A' P' A)).obj K).obj
          (Obstruction.squareZeroKernelObject.{u, u}
            (algebraMap P' (TensorProduct A' P' A)) hsurjP)) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} (TensorProduct A' P' A)) 0).obj
          (ModuleCat.of (TensorProduct A' P' A) (ULift.{u} N))) := by
  have hφ : (algebraMap A (TensorProduct A' P' A)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (flat_base_of_tensorProduct A' A P')
  have hker : RingHom.ker (algebraMap P' (TensorProduct A' P' A)) =
      Ideal.map (algebraMap A' P') (RingHom.ker (algebraMap A' A)) :=
    Algebra.ker_algebraMap_tensorProduct_left A' P' A
  have hbc := Obstruction.isIso_squareZeroKernelBaseChangeMap
    (algebraMap A' A) hsurjA (algebraMap P' (TensorProduct A' P' A)) hsurjP
    (algebraMap A' P') (algebraMap A (TensorProduct A' P' A))
    (algebraMap_comp_tensorProduct_comm A' A P') hker
    (RingHom.flat_algebraMap_iff.mpr (inferInstanceAs (Module.Flat A' P')))
  have hres : Module.Flat A ((ModuleCat.restrictScalars.{u}
      (algebraMap A (TensorProduct A' P' A))).obj
        (ModuleCat.of (TensorProduct A' P' A) (ULift.{u} M))) :=
    Module.Flat.of_linearEquiv
      ({ toFun := ULift.down
         invFun := ULift.up
         left_inv := fun _ => rfl
         right_inv := fun _ => rfl
         map_add' := fun _ _ => rfl
         map_smul' := fun r x =>
           IsScalarTower.algebraMap_smul (TensorProduct A' P' A) r x.down } :
        ((ModuleCat.restrictScalars.{u} (algebraMap A (TensorProduct A' P' A))).obj
          (ModuleCat.of (TensorProduct A' P' A) (ULift.{u} M)) : Type u) ≃ₗ[A] M)
  obtain ⟨eTor⟩ := nonempty_derivedTensor_single_extendScalars_iso_single
    (algebraMap A (TensorProduct A' P' A)) hφ
    (ModuleCat.of (TensorProduct A' P' A) (ULift.{u} M))
    (Obstruction.squareZeroKernelModule.{u, u} (algebraMap A' A) hsurjA)
  refine ⟨((((curriedTensor (ModuleCat.{u} (TensorProduct A' P' A))).obj
      (ModuleCat.of (TensorProduct A' P' A) (ULift.{u} M))).obj
        ((ModuleCat.extendScalars.{u, u, u} (algebraMap A (TensorProduct A' P' A))).obj
          (Obstruction.squareZeroKernelModule.{u, u} (algebraMap A' A) hsurjA)) : Type u)),
    inferInstance, inferInstance, ⟨?_⟩⟩
  refine ((canonicalDerivedTensorProductFunctor (TensorProduct A' P' A)).mapIso eK).app _ ≪≫
    (((canonicalDerivedTensorProductFunctor (TensorProduct A' P' A)).obj
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor
        (ModuleCat.{u} (TensorProduct A' P' A)) 0).obj
          (ModuleCat.of (TensorProduct A' P' A) (ULift.{u} M))))).mapIso ?_) ≪≫
    eTor ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ
      (ModuleCat.{u} (TensorProduct A' P' A)) 0).app _).symm ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} (TensorProduct A' P' A)) 0).mapIso
      (LinearEquiv.toModuleIso (ULift.moduleEquiv (R := TensorProduct A' P' A)).symm)
  exact (DerivedCategory.singleFunctor (ModuleCat.{u} (TensorProduct A' P' A)) 0).mapIso
      (asIso (Obstruction.squareZeroKernelBaseChangeMap
        (algebraMap A' A) hsurjA (algebraMap P' (TensorProduct A' P' A)) hsurjP
        (algebraMap A' P') (algebraMap A (TensorProduct A' P' A))
        (algebraMap_comp_tensorProduct_comm A' A P'))).symm ≪≫
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} (TensorProduct A' P' A)) 0).app _

/-! ### Comparing the two obstruction classes -/

/-- **Stacks 0DZ2, the comparison of the two obstruction classes.** Let `fR : R' → R` and
`fS : S' → S` be surjections with square-zero kernels in a commuting square over `a : R' → S'`
and `algebraMap R S`, with `R` Noetherian, `S` flat over `R` and `ker fS = a(ker fR)·S'`, and
suppose `S` induces an isomorphism `R/I ≅ S/IS` for a finitely generated ideal `I`. If the
canonical obstruction morphism of Stacks 0DYR for `fR` at a bounded-above `K` is killed by a
power of every element of `I`, and both `K` and the target of that morphism are single
complexes on a finite and an arbitrary `R`-module, then it vanishes exactly when the
obstruction morphism of the derived base change of `K` does. -/
theorem canonicalObstructionMap_eq_zero_iff_baseChange
    {R' R S' S : Type u} [CommRing R'] [CommRing R] [CommRing S'] [CommRing S]
    [Algebra R S] [IsNoetherianRing R]
    (fR : R' →+* R) (hfR : Function.Surjective fR) (hzR : (RingHom.ker fR) ^ 2 = ⊥)
    (fS : S' →+* S) (hfS : Function.Surjective fS) (hzS : (RingHom.ker fS) ^ 2 = ⊥)
    (a : R' →+* S') (hcomm : (algebraMap R S).comp fR = fS.comp a)
    (hJker : RingHom.ker fS = Ideal.map a (RingHom.ker fR))
    (ha : a.Flat) (hflat : Module.Flat R S)
    (I : Ideal R) (hI : I.FG)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    {M N : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N]
    {K : DerivedCategory (ModuleCat.{u} R)}
    (hK : (DerivedCategory.TStructure.t (C := ModuleCat.{u} R)).minus K)
    (eK : K ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      (ModuleCat.of R (ULift.{u} M)))
    (eT : (((canonicalDerivedTensorProductFunctor R).obj K).obj
        (Obstruction.squareZeroKernelObject.{u, u} fR hfR)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R (ULift.{u} N)))
    (hloc : ∀ g ∈ I, ∃ k : ℕ, g ^ k •
      (Obstruction.canonicalObstructionMap fR hfR hzR K hK).val = 0) :
    (Obstruction.canonicalObstructionMap fR hfR hzR K hK).val = 0 ↔
      (Obstruction.canonicalObstructionMap fS hfS hzS
        ((derivedExtensionScalarsGeneral.{u, u, u} (algebraMap R S)).functor.obj K)
        ((derivedExtensionScalarsGeneral.{u, u, u}
          (algebraMap R S)).maps_boundedAbove ⟨K, hK⟩)).val = 0 := by
  have hld := (derivedExtensionScalarsGeneral.{u, u, u} (algebraMap R S)).isLeftDerived
  obtain ⟨Θ, hΘ, hΘeq⟩ := Obstruction.exists_isIso_obstructionTargetBaseChange
    fR hfR fS hfS a (algebraMap R S) hcomm hJker ha
    (RingHom.flat_algebraMap_iff.mpr hflat)
    (Obstruction.canonicalObstructionMap fR hfR hzR K hK).2
    (Obstruction.canonicalObstructionMap fS hfS hzS
      ((derivedExtensionScalarsGeneral.{u, u, u} (algebraMap R S)).functor.obj K)
      ((derivedExtensionScalarsGeneral.{u, u, u}
        (algebraMap R S)).maps_boundedAbove ⟨K, hK⟩)).2
  have hmono : Mono (((derivedExtensionScalarsGeneral.{u, u, u}
      (algebraMap R S)).functor.commShiftIso (2 : ℤ)).hom.app
        (((canonicalDerivedTensorProductFunctor R).obj K).obj
          (Obstruction.squareZeroKernelObject.{u, u} fR hfR)) ≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} S)) (2 : ℤ)).map Θ) := by
    have := hΘ
    infer_instance
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← hΘeq, h, Functor.map_zero, Limits.zero_comp]
  · rw [h] at hΘeq
    exact @Deformation.ExtBaseChange.eq_zero_of_map_eq_zero_of_singleIso R S _ _ _ _ hflat
      (derivedExtensionScalarsGeneral.{u, u, u} (algebraMap R S)).functor
      (derivedExtensionScalarsGeneral.{u, u, u} (algebraMap R S)).comparison
      hld _ I hI hquot M N _ _ _ _ _ K _ 2 eK eT _ (zero_of_comp_mono _ hΘeq) hloc

/-- **The comparison of Stacks 0DZ2 with the obstruction morphism assumed power torsion.** Let
`A' → A` be a surjection of commutative rings with nilpotent kernel, let `P'` and `Q'` be flat
`A'`-algebras with `P' → Q'` flat, let `P = P' ⊗_{A'} A` be square-zero thickened by `A' → A`
with `P` Noetherian and `P/J ≅ Q/JQ` for a finitely generated ideal `J`, where `Q = Q' ⊗_{A'} A`,
and let `N` be the base change to `Q` of a `P`-module `M` which is finite over `P` and flat
over `A`. Then `M` has an `A'`-flat lift to a `P'`-module if and only if `N` has an `A'`-flat
lift to a `Q'`-module.

The standing local liftability hypothesis of the source enters as `hloc`, in the form the proof
uses it: the obstruction morphism of `M` is killed by a power of every element of `J`. The tag
Stacks 0DZ2 sits on
`Deformation.exists_flat_lift_iff_exists_flat_lift_baseChange_of_localizationLift`, which
assumes the source's local liftability instead. See the implementation notes. -/
theorem exists_flat_lift_iff_exists_flat_lift_baseChange_of_finite
    (A' A P' Q' : Type u) [CommRing A'] [CommRing A] [CommRing P'] [CommRing Q']
    [Algebra A' A] [Algebra A' P'] [Algebra A' Q'] [Algebra P' Q'] [IsScalarTower A' P' Q']
    [Module.Flat A' P'] [Module.Flat A' Q'] [Module.Flat P' Q']
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (hsurjP : Function.Surjective (algebraMap P' (TensorProduct A' P' A)))
    (hzeroP : (RingHom.ker (algebraMap P' (TensorProduct A' P' A))) ^ 2 = ⊥)
    (hsurjQ : Function.Surjective (algebraMap Q' (TensorProduct A' Q' A)))
    [Algebra (TensorProduct A' P' A) (TensorProduct A' Q' A)]
    [IsNoetherianRing (TensorProduct A' P' A)]
    (hcomm : (algebraMap (TensorProduct A' P' A) (TensorProduct A' Q' A)).comp
        (algebraMap P' (TensorProduct A' P' A)) =
      (algebraMap Q' (TensorProduct A' Q' A)).comp (algebraMap P' Q'))
    (hflatPQ : Module.Flat (TensorProduct A' P' A) (TensorProduct A' Q' A))
    (J : Ideal (TensorProduct A' P' A)) (hJ : J.FG)
    (hquot : Function.Bijective (Ideal.quotientMap
      (J.map (algebraMap (TensorProduct A' P' A) (TensorProduct A' Q' A)))
      (algebraMap (TensorProduct A' P' A) (TensorProduct A' Q' A)) Ideal.le_comap_map))
    (M : Type u) [AddCommGroup M] [Module (TensorProduct A' P' A) M] [Module A M]
    [IsScalarTower A (TensorProduct A' P' A) M] [Module.Flat A M]
    [Module.Finite (TensorProduct A' P' A) M]
    (N : Type u) [AddCommGroup N] [Module (TensorProduct A' Q' A) N] [Module A N]
    [IsScalarTower A (TensorProduct A' Q' A) N] [Module.Flat A N]
    (hN : Nonempty ((ModuleCat.extendScalars.{u, u, u}
        (algebraMap (TensorProduct A' P' A) (TensorProduct A' Q' A))).obj
          (ModuleCat.of (TensorProduct A' P' A) (ULift.{u} M)) ≅
      ModuleCat.of (TensorProduct A' Q' A) (ULift.{u} N)))
    (K : DerivedCategory (ModuleCat.{u} (TensorProduct A' P' A)))
    (hK : (DerivedCategory.TStructure.t
      (C := ModuleCat.{u} (TensorProduct A' P' A))).minus K)
    (eK : K ≅ DerivedCategory.Q.obj ((CochainComplex.singleFunctor
      (ModuleCat.{u} (TensorProduct A' P' A)) 0).obj
        (ModuleCat.of (TensorProduct A' P' A) (ULift.{u} M))))
    (hloc : ∀ g ∈ J, ∃ n : ℕ, g ^ n •
      (Obstruction.canonicalObstructionMap
        (algebraMap P' (TensorProduct A' P' A)) hsurjP hzeroP K hK).val = 0) :
    (∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module P' M') (_ : Module A' M')
        (_ : IsScalarTower A' P' M'), Module.Flat A' M' ∧
        Nonempty ((ModuleCat.extendScalars.{u, u, u}
            (algebraMap P' (TensorProduct A' P' A))).obj (ModuleCat.of P' M') ≅
          ModuleCat.of (TensorProduct A' P' A) (ULift.{u} M))) ↔
      (∃ (N' : Type u) (_ : AddCommGroup N') (_ : Module Q' N') (_ : Module A' N')
        (_ : IsScalarTower A' Q' N'), Module.Flat A' N' ∧
        Nonempty ((ModuleCat.extendScalars.{u, u, u}
            (algebraMap Q' (TensorProduct A' Q' A))).obj (ModuleCat.of Q' N') ≅
          ModuleCat.of (TensorProduct A' Q' A) (ULift.{u} N))) := by
  have hzeroQ : (RingHom.ker (algebraMap Q' (TensorProduct A' Q' A))) ^ 2 = ⊥ :=
    sq_ker_algebraMap_tensorProduct_eq_bot_of_tower A' A P' Q' hzeroP
  have hld := (derivedExtensionScalarsGeneral.{u, u, u}
    (algebraMap (TensorProduct A' P' A) (TensorProduct A' Q' A))).isLeftDerived
  obtain ⟨eMod⟩ := hN
  obtain ⟨N₀, _instN₀, _instN₀mod, ⟨eT⟩⟩ :=
    exists_singleIso_obstructionTarget A' A P' hsurjA hsurjP M K eK
  have hcompIso : IsIso (derivedExtensionScalarsGeneral.{u, u, u}
      (algebraMap (TensorProduct A' P' A) (TensorProduct A' Q' A))).comparison :=
    @StacksDraft.DerivedHom.HomModuleBaseChange.isIso_comparison_of_flat
      (TensorProduct A' P' A) (TensorProduct A' Q' A) _ _ _ hflatPQ _ _ hld
  have eL : (derivedExtensionScalarsGeneral.{u, u, u}
        (algebraMap (TensorProduct A' P' A) (TensorProduct A' Q' A))).functor.obj K ≅
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor
        (ModuleCat.{u} (TensorProduct A' Q' A)) 0).obj
          (ModuleCat.of (TensorProduct A' Q' A) (ULift.{u} N))) :=
    (derivedExtensionScalarsGeneral.{u, u, u}
        (algebraMap (TensorProduct A' P' A) (TensorProduct A' Q' A))).functor.mapIso eK ≪≫
      asIso ((derivedExtensionScalarsGeneral.{u, u, u}
          (algebraMap (TensorProduct A' P' A) (TensorProduct A' Q' A))).comparison.app
        ((CochainComplex.singleFunctor (ModuleCat.{u} (TensorProduct A' P' A)) 0).obj
          (ModuleCat.of (TensorProduct A' P' A) (ULift.{u} M)))) ≪≫
      DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex
          (ModuleCat.extendScalars.{u, u, u}
            (algebraMap (TensorProduct A' P' A) (TensorProduct A' Q' A)))
          (ComplexShape.up ℤ) 0).app
            (ModuleCat.of (TensorProduct A' P' A) (ULift.{u} M))) ≪≫
      DerivedCategory.Q.mapIso
        ((CochainComplex.singleFunctor (ModuleCat.{u} (TensorProduct A' Q' A)) 0).mapIso eMod)
  rw [exists_flat_lift_iff_canonicalObstructionMap_eq_zero A' A P' hsurjA hnilA hsurjP hzeroP
      M K hK eK,
    exists_flat_lift_iff_canonicalObstructionMap_eq_zero A' A Q' hsurjA hnilA hsurjQ hzeroQ
      N _ ((derivedExtensionScalarsGeneral.{u, u, u}
        (algebraMap (TensorProduct A' P' A) (TensorProduct A' Q' A))).maps_boundedAbove
          ⟨K, hK⟩) eL]
  exact canonicalObstructionMap_eq_zero_iff_baseChange
    (algebraMap P' (TensorProduct A' P' A)) hsurjP hzeroP
    (algebraMap Q' (TensorProduct A' Q' A)) hsurjQ hzeroQ (algebraMap P' Q') hcomm
    (ker_algebraMap_tensorProduct_eq_map_of_tower A' A P' Q')
    (RingHom.flat_algebraMap_iff.mpr (inferInstanceAs (Module.Flat P' Q'))) hflatPQ J hJ hquot
    hK (eK ≪≫ ((DerivedCategory.singleFunctorIsoCompQ
      (ModuleCat.{u} (TensorProduct A' P' A)) 0).app _).symm) eT hloc

end Deformation

end
