module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.HomologyColimit
public import StacksFrontier.Homology.Tor.ChangeOfRingsSystem
public import StacksFrontier.Homology.TwoTermComplex.BaseChange
public import StacksCore.Tactic.StacksAttribute

@[expose] public noncomputable section

/-!
# Tor independence

Two algebras `A` and `B` over a commutative ring `R` are *Tor independent* when
`Tor_i^R(A, B) = 0` for all `i > 0`. This file collects the basic theory: the definition and
its elementary reformulations, the behaviour of the canonical change-of-rings comparison on
Tor under flatness, stability of Tor independence under flat base change, the local nature of
Tor independence, and the comparison of derived base changes along a commutative square of
rings.

## Main definitions

* `RingTheory.TorIndependence.TorIndependent`: the predicate that two algebras are Tor
  independent over their base ring.
* `RingTheory.TorIndependence.derivedBaseChangeComparison`: the natural comparison between
  the two derived base changes attached to a commutative square of commutative rings.

## Main results

* `RingTheory.TorIndependence.torIndependent_iff_isZero_tor` and
  `RingTheory.TorIndependence.torIndependent_iff_subsingleton_tor`: in a common universe,
  Tor independence is the vanishing of the ordinary, unlifted Tor modules.
* `RingTheory.TorIndependence.isIso_torExtensionMap_of_flat`: the canonical scalar-extended
  change-of-rings map on Tor is an isomorphism under three flatness hypotheses.
* `RingTheory.TorIndependence.torIndependent_tensorProduct_of_flat`: Tor independence is
  preserved by flat base change.
* `RingTheory.TorIndependence.torIndependent_localizations_tfae`: global Tor independence,
  Tor independence at pairs of primes lying over a common prime, and prime-local vanishing
  over the tensor-product algebra are equivalent.

## Implementation notes

The zero module condition is expressed categorically by `CategoryTheory.Limits.IsZero`, and
Mathlib's `CategoryTheory.Tor` derives the tensor product in its second argument. All rings are
lifted to a common universe because Mathlib's monoidal `ModuleCat` requires the ring and its
modules to live in the same universe; the universe-change comparisons `torRestrictIso` and
`torUliftIso` transport projective resolutions along the relevant ring equivalence and along
`ULift`, and are shared by several of the results below.

The canonical `A ⊗[R] B`-module structure on `Tor_i^R(A, B)` and the change-of-rings
comparisons come from `TorChangeOfRings.canonicalSystem_nonempty` in
`StacksFrontier.Homology.Tor.ChangeOfRingsSystem`. The displayed equalities of the source are
expressed as invertibility of these canonical comparison maps.

For the comparison of derived base changes, restriction of scalars is passed to derived
categories by its exact functor and only extension of scalars is left-derived; the
normalization on ordinary modules is `r' ⊗ m ↦ i(r') ⊗ m`, and the factorization equation
characterizes the derived comparison. Its construction goes through a derivability structure
for the cellular objects of a category of complexes, which is the content of the private
`Resolutions` namespace.

## References

* [The Stacks Project, Tag 0660](https://stacks.math.columbia.edu/tag/0660)
* [The Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [The Stacks Project, Tag 08HW](https://stacks.math.columbia.edu/tag/08HW)
* [The Stacks Project, Tag 0FXF](https://stacks.math.columbia.edu/tag/0FXF)
* [The Stacks Project, Tag 08HX](https://stacks.math.columbia.edu/tag/08HX)
-/


open CategoryTheory

open scoped TensorProduct


namespace RingTheory.TorIndependence


-- Tor independence of algebras, and its universe-change reformulations (Tag 0660).
section

open CategoryTheory Limits

universe uR uA uB

/-- Two `R`-algebras are Tor independent over `R` when their positive-degree
Tor modules over `R` vanish. -/
@[stacks 0660, sga "6 III 1.5" "affine case"]
public def TorIndependent (R : Type uR) (A : Type uA) (B : Type uB)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] : Prop :=
  letI : Algebra (ULift.{max uR uA uB} R)
      (ULift.{max uR uA uB} A) :=
    ULift.algebra' R (ULift.{max uR uA uB} A)
  letI : Algebra (ULift.{max uR uA uB} R)
      (ULift.{max uR uA uB} B) :=
    ULift.algebra' R (ULift.{max uR uA uB} B)
  ∀ p : ℕ, 0 < p →
    IsZero (((Tor (ModuleCat.{max uR uA uB}
      (ULift.{max uR uA uB} R)) p).obj
      (ModuleCat.of (ULift.{max uR uA uB} R)
        (ULift.{max uR uA uB} A))).obj
          (ModuleCat.of (ULift.{max uR uA uB} R)
            (ULift.{max uR uA uB} B)))

noncomputable section UniverseChange

open MonoidalCategory
open scoped TensorProduct

universe u

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Restriction along a ring equivalence is semilinearly the identity. -/
private def restrictEquiv (e : R ≃+* S) (M : ModuleCat.{u} S) :
    LinearEquiv (σ' := (e.symm : S →+* R)) (e : R →+* S)
      ((ModuleCat.restrictScalars e.toRingHom).obj M) M where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Tensor products commute with restriction along a ring equivalence. -/
private def restrictTensorIso (e : R ≃+* S) (M N : ModuleCat.{u} S) :
    (ModuleCat.restrictScalars e.toRingHom).obj M ⊗
      (ModuleCat.restrictScalars e.toRingHom).obj N ≅
    (ModuleCat.restrictScalars e.toRingHom).obj (M ⊗ N) := by
  let t := TensorProduct.congr (restrictEquiv e M) (restrictEquiv e N)
  letI : Module R (M ⊗ N : ModuleCat S) :=
    Module.compHom (M ⊗ N : ModuleCat S) e.toRingHom
  exact LinearEquiv.toModuleIso
    { __ := t.toAddEquiv
      map_smul' := t.map_smul' }

/-- The tensor comparison is natural in the second module. -/
private def restrictTensorNatIso (e : R ≃+* S) (M : ModuleCat.{u} S) :
    ModuleCat.restrictScalars e.toRingHom ⋙
        tensorLeft ((ModuleCat.restrictScalars e.toRingHom).obj M) ≅
      tensorLeft M ⋙ ModuleCat.restrictScalars e.toRingHom :=
  NatIso.ofComponents (restrictTensorIso e M) (by
    intro N N' f
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl)

/-- Transport a projective resolution, compare its tensor complexes, and take homology. -/
@[no_expose] public def torRestrictIso (e : R ≃+* S) (M N : ModuleCat.{u} S) (i : ℕ) :
    ((Tor (ModuleCat R) i).obj ((ModuleCat.restrictScalars e.toRingHom).obj M)).obj
        ((ModuleCat.restrictScalars e.toRingHom).obj N) ≅
      (ModuleCat.restrictScalars e.toRingHom).obj (((Tor (ModuleCat S) i).obj M).obj N) := by
  let F := ModuleCat.restrictScalars e.toRingHom
  let P := projectiveResolution N
  let K := ((tensorLeft M).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  exact ((F.mapProjectiveResolution P).isoLeftDerivedObj (tensorLeft (F.obj M)) i) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) i).mapIso
      ((NatIso.mapHomologicalComplex (restrictTensorNatIso e M) (ComplexShape.down ℕ)).app
        P.complex) ≪≫
    ((K.sc i).mapHomologyIso F) ≪≫
    F.mapIso (P.isoLeftDerivedObj (tensorLeft M) i).symm

/-- `Tor` vanishes after restricting scalars along a ring isomorphism if and only if it vanishes
before. -/
public theorem isZero_tor_restrict_iff (e : R ≃+* S) (M N : ModuleCat.{u} S) (i : ℕ) :
    IsZero (((Tor (ModuleCat R) i).obj
      ((ModuleCat.restrictScalars e.toRingHom).obj M)).obj
        ((ModuleCat.restrictScalars e.toRingHom).obj N)) ↔
    IsZero (((Tor (ModuleCat S) i).obj M).obj N) := by
  rw [(torRestrictIso e M N i).isZero_iff]
  exact ⟨IsZero.of_full_of_faithful_of_isZero _ _,
    (ModuleCat.restrictScalars e.toRingHom).map_isZero⟩

/-- The lifted algebra is the original module with scalars restricted along `ULift.down`. -/
private def uliftRestrictIso (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    letI : Algebra (ULift.{u} R) (ULift.{u} A) := ULift.algebra' R (ULift.{u} A)
    ModuleCat.of (ULift.{u} R) (ULift.{u} A) ≅
      (ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u} R ≃+* R).toRingHom).obj
        (ModuleCat.of R A) := by
  letI : Algebra (ULift.{u} R) (ULift.{u} A) := ULift.algebra' R (ULift.{u} A)
  exact LinearEquiv.toModuleIso
    { toFun := ULift.down
      invFun := ULift.up
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

/-- For rings in a common universe, Tor independence can be checked using the
original rings and modules. This also applies to their localizations. -/
public theorem torIndependent_iff_isZero_tor (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    TorIndependent R A B ↔
      ∀ i : ℕ, 0 < i →
        IsZero (((Tor (ModuleCat R) i).obj (ModuleCat.of R A)).obj (ModuleCat.of R B)) := by
  let : Algebra (ULift.{u} R) (ULift.{u} A) := ULift.algebra' R (ULift.{u} A)
  let : Algebra (ULift.{u} R) (ULift.{u} B) := ULift.algebra' R (ULift.{u} B)
  unfold TorIndependent
  apply forall_congr'
  intro i
  apply imp_congr_right
  intro _
  let F := ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u} R ≃+* R).toRingHom
  let eA := uliftRestrictIso R A
  let eB := uliftRestrictIso R B
  let e := (((Tor (ModuleCat (ULift.{u} R)) i).mapIso eA).app
      (ModuleCat.of (ULift.{u} R) (ULift.{u} B))) ≪≫
    ((Tor (ModuleCat (ULift.{u} R)) i).obj (F.obj (ModuleCat.of R A))).mapIso eB
  exact e.isZero_iff.trans
    (isZero_tor_restrict_iff (R := ULift.{u} R) (S := R) ULift.ringEquiv
      (ModuleCat.of R A) (ModuleCat.of R B) i)

/-- The underlying ordinary Tor modules are subsingletons exactly when the algebras
are Tor independent. -/
public theorem torIndependent_iff_subsingleton_tor (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] :
    TorIndependent R A B ↔ ∀ i : ℕ, 0 < i →
      Subsingleton (((Tor (ModuleCat R) i).obj (ModuleCat.of R A)).obj
        (ModuleCat.of R B)) := by
  simp only [torIndependent_iff_isZero_tor, ModuleCat.isZero_iff_subsingleton]

end UniverseChange

end


-- Tor after flat changes of both algebras (Tag 08HW).
section

open CategoryTheory

open scoped TensorProduct

universe u

/-- Flatness of the map out of a tensor product is symmetric in the two factors. -/
private theorem flat_lift_swap {R S A C : Type*} [CommRing R] [CommRing S] [CommRing A]
    [CommRing C] [Algebra R S] [Algebra R A] [Algebra R C] (f : A →ₐ[R] C) (g : S →ₐ[R] C)
    (h : RingHom.Flat (Algebra.TensorProduct.lift f g (fun _ _ ↦ Commute.all _ _)).toRingHom) :
    RingHom.Flat (Algebra.TensorProduct.lift g f (fun _ _ ↦ Commute.all _ _)).toRingHom := by
  have he : Algebra.TensorProduct.lift g f (fun _ _ ↦ Commute.all _ _) =
      (Algebra.TensorProduct.lift f g (fun _ _ ↦ Commute.all _ _)).comp
        (Algebra.TensorProduct.comm R S A).toAlgHom := by
    apply Algebra.TensorProduct.ext'
    intro s a
    simp [mul_comm]
  rw [he]
  exact (RingHom.Flat.of_bijective (Algebra.TensorProduct.comm R S A).bijective).comp h

set_option backward.isDefEq.respectTransparency false in
-- Elaborating the composite comparison unfolds several nested scalar-extension structures.
/-- The ordinary, unlifted comparison for rings in a common universe. This form is also used
by the localization criterion; the universe-independent statement below transports the diagram
to this setting by canonical ring equivalences. -/
public theorem isIso_torExtensionMap_of_flat_sameUniverse
    (R R' A B A' B' : Type u)
    [CommRing R] [CommRing R'] [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra R R'] [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra R B']
    [Algebra R' A'] [Algebra R' B'] [IsScalarTower R R' A'] [IsScalarTower R R' B']
    (fA : A →ₐ[R] A') (fB : B →ₐ[R] B')
    (hR' : RingHom.Flat (algebraMap R R'))
    (hA' : RingHom.Flat (Algebra.TensorProduct.lift fA
      (IsScalarTower.toAlgHom R R' A') (fun _ _ ↦ Commute.all _ _)).toRingHom)
    (hB' : RingHom.Flat (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom R R' B') fB (fun _ _ ↦ Commute.all _ _)).toRingHom)
    (i : ℕ) :
    IsIso (TorChangeOfRings.extensionMap TorChangeOfRings.canonicalSystem_nonempty
      R R' A B A' B' i fA fB) := by
  -- Factor the diagram through the two scalar extensions.
  let S := TorChangeOfRings.canonicalSystem TorChangeOfRings.canonicalSystem_nonempty
  let A₁ := R' ⊗[R] A
  let B₁ := R' ⊗[R] B
  let a : A →ₐ[R] A₁ := Algebra.TensorProduct.includeRight
  let b : B →ₐ[R] B₁ := Algebra.TensorProduct.includeRight
  let a' : A₁ →ₐ[R'] A' :=
    { __ := Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R R' A') fA
        (fun _ _ ↦ Commute.all _ _)
      commutes' r := by simp [A₁] }
  let b' : B₁ →ₐ[R'] B' :=
    { __ := Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R R' B') fB
        (fun _ _ ↦ Commute.all _ _)
      commutes' r := by simp [B₁] }
  have ha' : a'.toRingHom.Flat := flat_lift_swap fA _ hA'
  have hb' : b'.toRingHom.Flat := hB'
  let := S.1.action R A B i
  let := S.1.action R' A₁ B₁ i
  let := S.1.action R' A' B' i
  let g := TorChangeOfRings.tensorProductMap R R' A B A₁ B₁ a b
  let g' := TorChangeOfRings.tensorProductMap R' R' A₁ B₁ A' B' a' b'
  let e := S.1.extensionMap R R' A B A₁ B₁ i a b
  let e' := S.1.extensionMap R' R' A₁ B₁ A' B' i a' b'
  have : Module.Flat R R' := RingHom.flat_algebraMap_iff.mp hR'
  have : IsIso e := S.2.flat_baseChange R R' A B i
  have : IsIso e' := S.2.flat_algebra_extension R' A₁ B₁ A' B' a' b' ha' hb' i
  have hg : TorChangeOfRings.tensorProductMap R R' A B A' B' fA fB = g'.comp g := by
    ext x <;> simp [g, g', TorChangeOfRings.tensorProductMap, a, b, a', b', A₁, B₁]
  let M := ModuleCat.of (A ⊗[R] B) (TorChangeOfRings.torObj R i A B)
  -- The composite of the two invertible comparisons is the original comparison.
  let E := (ModuleCat.extendScalarsComp g g').hom.app M ≫
    (ModuleCat.extendScalars g').map e ≫ e'
  have hE : IsIso E := by dsimp [E]; infer_instance
  have hfA : (a'.restrictScalars R).comp a = fA := by ext x; simp [a', a, A₁]
  have hfB : (b'.restrictScalars R).comp b = fB := by ext x; simp [b', b, B₁]
  have hmap (x : TorChangeOfRings.torObj R i A B) :
      S.1.map R R' A B A' B' i fA fB x =
        S.1.map R' R' A₁ B₁ A' B' i a' b' (S.1.map R R' A B A₁ B₁ i a b x) := by
    calc
      _ = S.1.map R R' A B A' B' i ((a'.restrictScalars R).comp a)
          ((b'.restrictScalars R).comp b) x :=
        congrArg₂ (fun (fa : A →ₐ[R] A') (fb : B →ₐ[R] B') ↦
          S.1.map R R' A B A' B' i fa fb x) hfA.symm hfB.symm
      _ = _ := S.2.map_comp R R' R' A B A₁ B₁ A' B' i a b a' b' x
  show IsIso (S.1.extensionMap R R' A B A' B' i fA fB)
  generalize hd : S.1.extensionMap R R' A B A' B' i fA fB = d
  have hdgen (x : TorChangeOfRings.torObj R i A B) :=
    S.2.extension_one_tmul R R' A B A' B' i fA fB x
  simp only [hd, hmap] at hdgen
  clear hd
  revert d hdgen
  rw [hg]
  intro d hdgen
  have heq : d = E := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    rw [hdgen]
    dsimp only [E]
    rw [ModuleCat.comp_apply, ModuleCat.extendScalarsComp_hom_app_one_tmul,
      ModuleCat.comp_apply]
    show S.1.map R' R' A₁ B₁ A' B' i a' b' (S.1.map R R' A B A₁ B₁ i a b x) =
      e' ((1 : A' ⊗[R'] B') ⊗ₜ[R' ⊗[R] A ⊗[R'] (R' ⊗[R] B)]
        (e ((1 : A₁ ⊗[R'] B₁) ⊗ₜ[A ⊗[R] B] x)))
    rw [S.2.extension_one_tmul, S.2.extension_one_tmul]
  rw [heq]
  exact hE

universe uR uS uA uB uC uD
attribute [local instance] ULift.algebra'

/-- **Stacks 08HW.** If `R'` is flat over `R`, `A'` is flat over `A ⊗[R] R'`, and
`B'` is flat over `R' ⊗[R] B`, the canonical scalar-extended change-of-rings map on
ordinary Tor is an isomorphism. The diagram is lifted to the maximum of its six independent
universes so that Mathlib's categorical Tor and extension-of-scalars constructions apply. -/
@[stacks 08HW]
public theorem isIso_torExtensionMap_of_flat
    (R : Type uR) (R' : Type uS) (A : Type uA) (B : Type uB)
    (A' : Type uC) (B' : Type uD)
    [CommRing R] [CommRing R'] [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra R R'] [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra R B']
    [Algebra R' A'] [Algebra R' B'] [IsScalarTower R R' A'] [IsScalarTower R R' B']
    (fA : A →ₐ[R] A') (fB : B →ₐ[R] B')
    (hR' : RingHom.Flat (algebraMap R R'))
    (hA' : RingHom.Flat (Algebra.TensorProduct.lift fA
      (IsScalarTower.toAlgHom R R' A') (fun _ _ ↦ Commute.all _ _)).toRingHom)
    (hB' : RingHom.Flat (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom R R' B') fB (fun _ _ ↦ Commute.all _ _)).toRingHom)
    (i : ℕ) :
    IsIso (TorChangeOfRings.extensionMap TorChangeOfRings.canonicalSystem_nonempty
      (ULift.{max uR uS uA uB uC uD} R) (ULift.{max uR uS uA uB uC uD} R')
      (ULift.{max uR uS uA uB uC uD} A) (ULift.{max uR uS uA uB uC uD} B)
      (ULift.{max uR uS uA uB uC uD} A') (ULift.{max uR uS uA uB uC uD} B')
      i fA.ulift fB.ulift) := by
  let RU := ULift.{max uR uS uA uB uC uD} R
  let SU := ULift.{max uR uS uA uB uC uD} R'
  let AU := ULift.{max uR uS uA uB uC uD} A
  let BU := ULift.{max uR uS uA uB uC uD} B
  let CU := ULift.{max uR uS uA uB uC uD} A'
  let DU := ULift.{max uR uS uA uB uC uD} B'
  have hR : RingHom.Flat (algebraMap RU SU) := RingHom.Flat.ulift_iff.mpr hR'
  let eA : ULift.{max uR uS uA uB uC uD} (A ⊗[R] R') ≃ₐ[R] AU ⊗[RU] SU :=
    Algebra.TensorProduct.uliftEquiv R R A R'
  let eB : ULift.{max uR uS uA uB uC uD} (R' ⊗[R] B) ≃ₐ[R] SU ⊗[RU] BU :=
    Algebra.TensorProduct.uliftEquiv R R R' B
  have hA : RingHom.Flat (Algebra.TensorProduct.lift (fA.ulift : AU →ₐ[RU] CU)
      (IsScalarTower.toAlgHom RU SU CU) (fun _ _ ↦ Commute.all _ _)).toRingHom := by
    have he : (Algebra.TensorProduct.lift (fA.ulift : AU →ₐ[RU] CU)
        (IsScalarTower.toAlgHom RU SU CU) (fun _ _ ↦ Commute.all _ _)).toRingHom =
        (Algebra.TensorProduct.lift fA (IsScalarTower.toAlgHom R R' A')
          (fun _ _ ↦ Commute.all _ _)).toRingHom.ulift.comp eA.symm.toRingHom := by
      ext a <;> rfl
    rw [he]
    exact (RingHom.Flat.of_bijective eA.symm.bijective).comp
      (RingHom.Flat.ulift_iff.mpr hA')
  have hB : RingHom.Flat (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom RU SU DU) (fB.ulift : BU →ₐ[RU] DU)
      (fun _ _ ↦ Commute.all _ _)).toRingHom := by
    have he : (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom RU SU DU)
        (fB.ulift : BU →ₐ[RU] DU) (fun _ _ ↦ Commute.all _ _)).toRingHom =
        (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R R' B') fB
          (fun _ _ ↦ Commute.all _ _)).toRingHom.ulift.comp eB.symm.toRingHom := by
      ext r <;> rfl
    rw [he]
    exact (RingHom.Flat.of_bijective eB.symm.bijective).comp
      (RingHom.Flat.ulift_iff.mpr hB')
  exact isIso_torExtensionMap_of_flat_sameUniverse RU SU AU BU CU DU fA.ulift fB.ulift hR hA hB i

end


-- Tor independence after flat base change (Tag 0FXF).
section

open CategoryTheory Limits
open MonoidalCategory
open scoped TensorProduct
open scoped MonoidalCategory

universe uR uS uA uB

attribute [local instance] ULift.algebra'
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

private noncomputable def raiseModules (R : Type uR) [CommRing R] :
    ModuleCat.{uR} R ⥤ ModuleCat.{max uR uA} (ULift.{uA} R) :=
  ModuleCat.uliftFunctor.{uA} R ⋙ ModuleCat.restrictScalars ULift.ringEquiv.toRingHom

private instance {R : Type uR} [CommRing R] : (raiseModules.{uR, uA} R).Additive := by
  unfold raiseModules
  infer_instance

private instance {R : Type uR} [CommRing R] : (raiseModules.{uR, uA} R).Full := by
  unfold raiseModules
  infer_instance

private instance {R : Type uR} [CommRing R] : (raiseModules.{uR, uA} R).Faithful := by
  unfold raiseModules
  infer_instance

private instance {R : Type uR} [CommRing R] :
    (raiseModules.{uR, uA} R).PreservesProjectiveObjects := by
  unfold raiseModules
  infer_instance

private instance {R : Type uR} [CommRing R] :
    PreservesFiniteLimits (raiseModules.{uR, uA} R) := by
  unfold raiseModules
  apply comp_preservesFiniteLimits

private instance {R : Type uR} [CommRing R] :
    PreservesFiniteColimits (raiseModules.{uR, uA} R) := by
  unfold raiseModules
  apply comp_preservesFiniteColimits

private noncomputable def uliftTensorIso {R : Type uR} [CommRing R]
    (M N : ModuleCat.{uR} R) :
    (raiseModules.{uR, uA} R).obj M ⊗ (raiseModules.{uR, uA} R).obj N ≅
      (raiseModules.{uR, uA} R).obj (M ⊗ N) :=
  LinearEquiv.toModuleIso
    (TensorProduct.AlgebraTensorModule.uliftEquiv R (ULift.{uA} R) M N).symm

private noncomputable def uliftTensorNatIso {R : Type uR} [CommRing R]
    (M : ModuleCat.{uR} R) :
    raiseModules.{uR, uA} R ⋙ tensorLeft ((raiseModules.{uR, uA} R).obj M) ≅
      tensorLeft M ⋙ raiseModules.{uR, uA} R :=
  NatIso.ofComponents (uliftTensorIso M) (by
    intro N N' f
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl)

private noncomputable def torUliftIso {R : Type uR} [CommRing R]
    (M N : ModuleCat.{uR} R) (i : ℕ) :
    ((Tor (ModuleCat.{max uR uA} (ULift.{uA} R)) i).obj
      ((raiseModules.{uR, uA} R).obj M)).obj
        ((raiseModules.{uR, uA} R).obj N) ≅
      (raiseModules.{uR, uA} R).obj (((Tor (ModuleCat.{uR} R) i).obj M).obj N) := by
  let F := raiseModules.{uR, uA} R
  let P := projectiveResolution N
  let K := ((tensorLeft M).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  exact ((F.mapProjectiveResolution P).isoLeftDerivedObj (tensorLeft (F.obj M)) i) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat (ULift.{uA} R))
      (ComplexShape.down ℕ) i).mapIso
      ((NatIso.mapHomologicalComplex (uliftTensorNatIso M) (ComplexShape.down ℕ)).app
        P.complex) ≪≫
    ((K.sc i).mapHomologyIso F) ≪≫
    F.mapIso (P.isoLeftDerivedObj (tensorLeft M) i).symm

private theorem isZero_tor_changeUniverse {R : Type uR} [CommRing R]
    (M N : ModuleCat.{uR} R) (S : Type (max uR uA)) [CommRing S]
    (P Q : ModuleCat.{max uR uA} S)
    (e : S ≃+* ULift.{uA} R)
    (eM : P ≅ (ModuleCat.restrictScalars e.toRingHom).obj
      ((raiseModules.{uR, uA} R).obj M))
    (eN : Q ≅ (ModuleCat.restrictScalars e.toRingHom).obj
      ((raiseModules.{uR, uA} R).obj N)) (i : ℕ) :
    IsZero (((Tor (ModuleCat S) i).obj P).obj Q) ↔
      IsZero (((Tor (ModuleCat R) i).obj M).obj N) := by
  let F := raiseModules.{uR, uA} R
  let G := ModuleCat.restrictScalars e.toRingHom
  let et : ((Tor (ModuleCat S) i).obj P).obj Q ≅
      G.obj (((Tor (ModuleCat (ULift.{uA} R)) i).obj (F.obj M)).obj (F.obj N)) :=
    (((Tor (ModuleCat S) i).mapIso eM).app Q) ≪≫
      ((Tor (ModuleCat S) i).obj _).mapIso eN ≪≫
      torRestrictIso e (F.obj M) (F.obj N) i
  rw [et.isZero_iff]
  exact ⟨fun h ↦ IsZero.of_full_of_faithful_of_isZero F _
      ((torUliftIso M N i).isZero_iff.mp (IsZero.of_full_of_faithful_of_isZero G _ h)),
    fun h ↦ G.map_isZero ((torUliftIso M N i).isZero_iff.mpr (F.map_isZero h))⟩

/-- The ring equivalence from a lift of `R` to a lift of a lift of `R`. -/
private noncomputable def uliftUliftRingEquiv (R : Type uR) [CommRing R] :
    ULift.{max uR uS uA} R ≃+* ULift.{uS} (ULift.{max uR uA} R) :=
  (ULift.ringEquiv : ULift.{max uR uS uA} R ≃+* R) |>.trans
    ((ULift.ringEquiv : ULift.{max uR uA} R ≃+* R).symm) |>.trans
      (ULift.ringEquiv : ULift.{uS} (ULift.{max uR uA} R) ≃+* ULift.{max uR uA} R).symm

/-- A lift of `X` is, over `uliftUliftRingEquiv`, the restriction of the raised lift of `X`. -/
private noncomputable def uliftUliftModuleIso (R : Type uR) (X : Type uB)
    [CommRing R] [CommRing X] [Algebra R X] :
    ModuleCat.of (ULift.{max uR uS uA uB} R) (ULift.{max uR uS uA uB} X) ≅
      (ModuleCat.restrictScalars
        (uliftUliftRingEquiv.{uR, uS, max uA uB} R).toRingHom).obj
        ((raiseModules.{max uR uA uB, uS} (ULift.{max uR uA uB} R)).obj
          (ModuleCat.of (ULift.{max uR uA uB} R) (ULift.{max uR uA uB} X))) := by
  let e := uliftUliftRingEquiv.{uR, uS, max uA uB} R
  let : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  let : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv_symm e
  dsimp [raiseModules]
  let l : LinearEquiv (R := ULift.{max uR uS uA uB} R)
      (S := ULift.{uS} (ULift.{max uR uA uB} R)) (σ' := e.symm.toRingHom) e.toRingHom
      (ULift.{max uR uS uA uB} X) (ULift.{uS} (ULift.{max uR uA uB} X)) :=
    { toFun x := ⟨⟨x.down⟩⟩
      invFun x := ⟨x.down.down⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' r x := by cases r; cases x; rfl }
  let l' : ULift.{max uR uS uA uB} X ≃ₗ[ULift.{max uR uS uA uB} R]
      (ModuleCat.restrictScalars e.toRingHom).obj
        ((raiseModules.{max uR uA uB, uS} (ULift.{max uR uA uB} R)).obj
          (ModuleCat.of (ULift.{max uR uA uB} R) (ULift.{max uR uA uB} X))) :=
    { __ := l.toAddEquiv, map_smul' := l.map_smul' }
  exact LinearEquiv.toModuleIso l'

/-- The lift of `includeLeft` and the structure map into `X ⊗[R] R'` is the identity, hence
flat. -/
private theorem flat_lift_includeLeft (R R' X : Type*) [CommRing R] [CommRing R'] [CommRing X]
    [Algebra R R'] [Algebra R X] :
    letI : Algebra R' (X ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
    RingHom.Flat (Algebra.TensorProduct.lift
      (Algebra.TensorProduct.includeLeft : X →ₐ[R] X ⊗[R] R')
      (IsScalarTower.toAlgHom R R' (X ⊗[R] R')) (fun _ _ ↦ Commute.all _ _)).toRingHom := by
  let : Algebra R' (X ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
  have he : Algebra.TensorProduct.lift
      (Algebra.TensorProduct.includeLeft : X →ₐ[R] X ⊗[R] R')
      (IsScalarTower.toAlgHom R R' (X ⊗[R] R')) (fun _ _ ↦ Commute.all _ _) =
      AlgHom.id R (X ⊗[R] R') := by
    refine Algebra.TensorProduct.ext' fun a r => ?_
    rw [Algebra.TensorProduct.lift_tmul]
    show (a ⊗ₜ[R] 1) * (1 ⊗ₜ[R] r) = a ⊗ₜ[R] r
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [he]
  exact RingHom.Flat.id _

/-- **Stacks 0FXF.** Tor independence of two algebras is preserved by extension of scalars along
a flat map of commutative rings. -/
@[stacks 0FXF]
public theorem torIndependent_tensorProduct_of_flat
    (R : Type uR) (R' : Type uS) (A : Type uA) (B : Type uB)
    [CommRing R] [CommRing R'] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra R R']
    (h : TorIndependent R A B)
    (hR' : RingHom.Flat (algebraMap R R')) :
    let _ : Algebra R' (A ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
    let _ : Algebra R' (B ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
    TorIndependent R' (A ⊗[R] R') (B ⊗[R] R') := by
  let : Algebra R' (A ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
  let : Algebra R' (B ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
  show TorIndependent R' (A ⊗[R] R') (B ⊗[R] R')
  let fA : A →ₐ[R] A ⊗[R] R' := Algebra.TensorProduct.includeLeft
  let fB : B →ₐ[R] B ⊗[R] R' := Algebra.TensorProduct.includeLeft
  have hA := flat_lift_includeLeft R R' A
  have hB := flat_lift_swap fB _ (flat_lift_includeLeft R R' B)
  unfold TorIndependent at h ⊢
  intro i hi
  let e := TorChangeOfRings.extensionMap TorChangeOfRings.canonicalSystem_nonempty
    (ULift.{max uR uS uA uB} R) (ULift.{max uR uS uA uB} R')
    (ULift.{max uR uS uA uB} A) (ULift.{max uR uS uA uB} B)
    (ULift.{max uR uS uA uB} (A ⊗[R] R')) (ULift.{max uR uS uA uB} (B ⊗[R] R'))
    i fA.ulift fB.ulift
  have he : IsIso e := isIso_torExtensionMap_of_flat
    R R' A B (A ⊗[R] R') (B ⊗[R] R') fA fB hR' hA hB i
  let R₀ := ULift.{max uR uA uB} R
  let A₀ := ULift.{max uR uA uB} A
  let B₀ := ULift.{max uR uA uB} B
  let M₀ : ModuleCat R₀ := ModuleCat.of R₀ A₀
  let N₀ : ModuleCat R₀ := ModuleCat.of R₀ B₀
  let F₀ := raiseModules.{max uR uA uB, uS} R₀
  let eR₀ := uliftUliftRingEquiv.{uR, uS, max uA uB} R
  let eA₀ := uliftUliftModuleIso.{uR, uS, uB, uA} R A
  let eB₀ := uliftUliftModuleIso.{uR, uS, uA, uB} R B
  have hsourceBase : IsZero (ModuleCat.of (ULift.{max uR uS uA uB} R)
      (TorChangeOfRings.torObj (ULift.{max uR uS uA uB} R) i
        (ULift.{max uR uS uA uB} A) (ULift.{max uR uS uA uB} B))) :=
    (isZero_tor_changeUniverse M₀ N₀ _ _ _ eR₀ eA₀ eB₀ i).mpr (h i hi)
  have hbig := (asIso e).isZero_iff.mp
    ((ModuleCat.extendScalars _).map_isZero (by
      rwa [ModuleCat.isZero_iff_subsingleton] at hsourceBase ⊢))
  let RS := ULift.{max uS uA uB} R'
  let AS := ULift.{max uS uA uB} (A ⊗[R] R')
  let BS := ULift.{max uS uA uB} (B ⊗[R] R')
  let M : ModuleCat RS := ModuleCat.of RS AS
  let N : ModuleCat RS := ModuleCat.of RS BS
  let F := raiseModules.{max uS uA uB, uR} RS
  let eR := uliftUliftRingEquiv.{uS, uR, max uA uB} R'
  let eA := uliftUliftModuleIso.{uS, uR, uB, max uA uS} R' (A ⊗[R] R')
  let eB := uliftUliftModuleIso.{uS, uR, uA, max uB uS} R' (B ⊗[R] R')
  have hbigBase : IsZero (((Tor (ModuleCat (ULift.{max uR uS uA uB} R')) i).obj
      (ModuleCat.of _ (ULift.{max uR uS uA uB} (A ⊗[R] R')))).obj
        (ModuleCat.of _ (ULift.{max uR uS uA uB} (B ⊗[R] R')))) := by
    rwa [ModuleCat.isZero_iff_subsingleton] at hbig ⊢
  exact (isZero_tor_changeUniverse M N _ _ _ eR eA eB i).mp hbigBase

end


-- Tor independence is local (Tag 08HX).
section

open CategoryTheory Limits

open scoped TensorProduct

universe u

private theorem flat_tensorProduct_lift_of_isLocalization
    {R S A C : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing C]
    [Algebra R S] [Algebra R A] [Algebra R C] [Algebra S C] [IsScalarTower R S C]
    (U : Submonoid R) [IsLocalization U S] (f : A →ₐ[R] C)
    (hf : RingHom.Flat f.toRingHom) :
    RingHom.Flat (Algebra.TensorProduct.lift f (IsScalarTower.toAlgHom R S C)
      (fun _ _ ↦ Commute.all _ _)).toRingHom := by
  let g := Algebra.TensorProduct.lift f (IsScalarTower.toAlgHom R S C)
    (fun _ _ ↦ Commute.all _ _)
  let : Algebra A C := f.toRingHom.toAlgebra
  let : Algebra (A ⊗[R] S) C := g.toRingHom.toAlgebra
  let : IsScalarTower A (A ⊗[R] S) C := .of_algebraMap_eq fun a ↦ by
    simp [g, RingHom.algebraMap_toAlgebra]
  exact (Module.flat_iff_of_isLocalization (A ⊗[R] S)
    (Algebra.algebraMapSubmonoid A U) C).mpr hf

private theorem flat_tensorProduct_lift_of_isLocalization_right
    {R S B C : Type*} [CommRing R] [CommRing S] [CommRing B] [CommRing C]
    [Algebra R S] [Algebra R B] [Algebra R C] [Algebra S C] [IsScalarTower R S C]
    (U : Submonoid R) [IsLocalization U S] (f : B →ₐ[R] C)
    (hf : RingHom.Flat f.toRingHom) :
    RingHom.Flat (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S C) f
      (fun _ _ ↦ Commute.all _ _)).toRingHom := by
  exact flat_lift_swap f _ (flat_tensorProduct_lift_of_isLocalization U f hf)

private theorem isIso_torExtensionMap_atPrime
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (r : PrimeSpectrum R) (p : PrimeSpectrum A) (q : PrimeSpectrum B)
    [p.asIdeal.LiesOver r.asIdeal] [q.asIdeal.LiesOver r.asIdeal]
    [Algebra (Localization.AtPrime r.asIdeal) (Localization.AtPrime p.asIdeal)]
    [Algebra (Localization.AtPrime r.asIdeal) (Localization.AtPrime q.asIdeal)]
    [Localization.AtPrime.IsLiesOverAlgebra r.asIdeal p.asIdeal]
    [Localization.AtPrime.IsLiesOverAlgebra r.asIdeal q.asIdeal] (i : ℕ) :
    IsIso (TorChangeOfRings.extensionMap TorChangeOfRings.canonicalSystem_nonempty
      R (Localization.AtPrime r.asIdeal) A B
      (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) i
      (IsScalarTower.toAlgHom R A _) (IsScalarTower.toAlgHom R B _)) := by
  apply isIso_torExtensionMap_of_flat_sameUniverse
  · exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ r.asIdeal.primeCompl)
  · exact flat_tensorProduct_lift_of_isLocalization r.asIdeal.primeCompl _
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ p.asIdeal.primeCompl))
  · exact flat_tensorProduct_lift_of_isLocalization_right r.asIdeal.primeCompl _
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ q.asIdeal.primeCompl))

private theorem subsingleton_localizedModule_of_tensorProduct
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] (U : Submonoid R)
    (f : S →ₐ[R] Localization U) [Subsingleton (S ⊗[R] M)] :
    Subsingleton (LocalizedModule U M) := by
  have : Subsingleton (Localization U ⊗[R] M) := by
    refine (subsingleton_iff_forall_eq 0).mpr fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul s m =>
      have hm : (1 : Localization U) ⊗ₜ[R] m = 0 := by
        simpa using congrArg (TensorProduct.map f.toLinearMap (LinearMap.id : M →ₗ[R] M))
          (Subsingleton.elim (1 ⊗ₜ[R] m : S ⊗[R] M) 0)
      calc
        s ⊗ₜ[R] m = s • ((1 : Localization U) ⊗ₜ[R] m) := by simp [TensorProduct.smul_tmul']
        _ = 0 := by rw [hm, smul_zero]
    | add x y hx hy => simp [hx, hy]
  exact (LocalizedModule.equivTensorProduct U M).injective.subsingleton


/-- **Stacks 08HX.** For `R`-algebras `A` and `B`, the following are equivalent:

1. `A` and `B` are Tor independent over `R`;
2. `A_p` and `B_q` are Tor independent over `R_r` whenever `p` and `q` lie over `r`;
3. every positive-degree Tor module of `A` and `B` vanishes after localization at every
   prime of `A ⊗[R] B`. -/
@[stacks 08HX]
public theorem torIndependent_localizations_tfae
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    List.TFAE [
      TorIndependent R A B,
      (∀ (r : PrimeSpectrum R) (p : PrimeSpectrum A) (q : PrimeSpectrum B)
        (hp : r.asIdeal = p.asIdeal.comap (algebraMap R A))
        (hq : r.asIdeal = q.asIdeal.comap (algebraMap R B)),
        letI : p.asIdeal.LiesOver r.asIdeal := ⟨hp⟩
        letI : q.asIdeal.LiesOver r.asIdeal := ⟨hq⟩
        letI : Algebra (Localization.AtPrime r.asIdeal)
            (Localization.AtPrime p.asIdeal) :=
          Localization.AtPrime.algebraOfLiesOver r.asIdeal p.asIdeal
        letI : Algebra (Localization.AtPrime r.asIdeal)
            (Localization.AtPrime q.asIdeal) :=
          Localization.AtPrime.algebraOfLiesOver r.asIdeal q.asIdeal
        TorIndependent (Localization.AtPrime r.asIdeal)
          (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)),
      (∀ (i : ℕ), 0 < i → ∀ s : PrimeSpectrum (A ⊗[R] B),
        letI := TorChangeOfRings.moduleStructure
          TorChangeOfRings.canonicalSystem_nonempty R A B i
        Subsingleton
          (LocalizedModule s.asIdeal.primeCompl (TorChangeOfRings.torObj R i A B)))] := by
  tfae_have 1 → 2 := by
    intro h r p q hp hq
    let : p.asIdeal.LiesOver r.asIdeal := ⟨hp⟩
    let : q.asIdeal.LiesOver r.asIdeal := ⟨hq⟩
    let : Algebra (Localization.AtPrime r.asIdeal) (Localization.AtPrime p.asIdeal) :=
      Localization.AtPrime.algebraOfLiesOver r.asIdeal p.asIdeal
    let : Algebra (Localization.AtPrime r.asIdeal) (Localization.AtPrime q.asIdeal) :=
      Localization.AtPrime.algebraOfLiesOver r.asIdeal q.asIdeal
    show TorIndependent _ _ _
    rw [torIndependent_iff_subsingleton_tor] at h ⊢
    intro i hi
    let : Subsingleton (TorChangeOfRings.torObj R i A B) := h i hi
    let e := TorChangeOfRings.extensionMap TorChangeOfRings.canonicalSystem_nonempty
      R (Localization.AtPrime r.asIdeal) A B
      (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) i
      (IsScalarTower.toAlgHom R A _) (IsScalarTower.toAlgHom R B _)
    have : IsIso e := isIso_torExtensionMap_atPrime R A B r p q i
    have hz := (asIso e).isZero_iff.mp ((ModuleCat.extendScalars _).map_isZero
      (ModuleCat.isZero_iff_subsingleton.mpr inferInstance))
    have hs := ModuleCat.isZero_iff_subsingleton.mp hz
    exact hs
  tfae_have 2 → 3 := by
    intro h i hi s
    let r := PrimeSpectrum.comap (algebraMap R (A ⊗[R] B)) s
    let p := PrimeSpectrum.comap (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom s
    let q := PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom s
    have hp : r.asIdeal = p.asIdeal.comap (algebraMap R A) := by
      show s.asIdeal.comap _ = (s.asIdeal.comap _).comap _
      rw [Ideal.comap_comap]
      congr 1
    have hq : r.asIdeal = q.asIdeal.comap (algebraMap R B) := by
      show s.asIdeal.comap _ = (s.asIdeal.comap _).comap _
      rw [Ideal.comap_comap]
      congr 1
      ext b
      exact (Algebra.TensorProduct.includeRight.commutes b).symm
    let : p.asIdeal.LiesOver r.asIdeal := ⟨hp⟩
    let : q.asIdeal.LiesOver r.asIdeal := ⟨hq⟩
    let : Algebra (Localization.AtPrime r.asIdeal) (Localization.AtPrime p.asIdeal) :=
      Localization.AtPrime.algebraOfLiesOver r.asIdeal p.asIdeal
    let : Algebra (Localization.AtPrime r.asIdeal) (Localization.AtPrime q.asIdeal) :=
      Localization.AtPrime.algebraOfLiesOver r.asIdeal q.asIdeal
    have hlocal := (torIndependent_iff_subsingleton_tor _ _ _).mp (h r p q hp hq) i hi
    let fA := IsScalarTower.toAlgHom R A (Localization.AtPrime p.asIdeal)
    let fB := IsScalarTower.toAlgHom R B (Localization.AtPrime q.asIdeal)
    let D := Localization.AtPrime p.asIdeal ⊗[Localization.AtPrime r.asIdeal]
      Localization.AtPrime q.asIdeal
    let f := TorChangeOfRings.tensorProductMap R (Localization.AtPrime r.asIdeal) A B
      (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) fA fB
    let : Algebra (A ⊗[R] B) D := f.toAlgebra
    let := TorChangeOfRings.moduleStructure TorChangeOfRings.canonicalSystem_nonempty R A B i
    let e := TorChangeOfRings.extensionMap TorChangeOfRings.canonicalSystem_nonempty
      R (Localization.AtPrime r.asIdeal) A B
      (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) i fA fB
    have : IsIso e := isIso_torExtensionMap_atPrime R A B r p q i
    have : Subsingleton (D ⊗[A ⊗[R] B] TorChangeOfRings.torObj R i A B) :=
      ((ModuleCat.mono_iff_injective e).mp inferInstance).subsingleton
    let gA := Localization.localAlgHom p.asIdeal s.asIdeal
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B) rfl
    let gB := Localization.localAlgHom q.asIdeal s.asIdeal
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) rfl
    let g := (Algebra.TensorProduct.lift gA gB (fun _ _ ↦ Commute.all _ _)).toRingHom.comp
      (IsLocalization.algebraTensorEquiv r.asIdeal.primeCompl
        (Localization.AtPrime r.asIdeal)
        (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)).toRingHom
    have hg : g.comp f = algebraMap (A ⊗[R] B) (Localization.AtPrime s.asIdeal) := by
      apply RingHom.ext
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        have hf : f (a ⊗ₜ[R] b) = fA a ⊗ₜ[Localization.AtPrime r.asIdeal] fB b := by
          simp [f, TorChangeOfRings.tensorProductMap, Algebra.TensorProduct.tmul_mul_tmul]
        rw [RingHom.comp_apply, hf]
        show gA (fA a) * gB (fB b) = _
        simp [gA, gB, fA, fB, Localization.localAlgHom, Localization.localRingHom_to_map,
          ← map_mul, Algebra.TensorProduct.tmul_mul_tmul]
      | add x y hx hy => simp_all only [map_add]
    let g' : D →ₐ[A ⊗[R] B] Localization.AtPrime s.asIdeal :=
      { __ := g, commutes' := fun x ↦ congrArg (fun k : _ →+* _ ↦ k x) hg }
    exact subsingleton_localizedModule_of_tensorProduct s.asIdeal.primeCompl g'
  tfae_have 3 → 1 := by
    intro h
    rw [torIndependent_iff_subsingleton_tor]
    intro i hi
    let := TorChangeOfRings.moduleStructure TorChangeOfRings.canonicalSystem_nonempty R A B i
    exact Module.subsingleton_of_localization_maximal
      (fun P _ ↦ LocalizedModule P.primeCompl (TorChangeOfRings.torObj R i A B))
      (fun P _ ↦ LocalizedModule.mkLinearMap P.primeCompl _)
      (fun P _ ↦ h i hi ⟨P, inferInstance⟩)
  tfae_finish

end


-- Comparison of derived base changes (Tag 065Z).
section

open CategoryTheory

open scoped ChangeOfRings

universe uR uA uRp uAp v w

namespace Resolutions
open CategoryTheory Limits Functor LocalizerMorphism

section
variable {C₁ C₂ D H H' : Type*} [Category* C₁] [Category* C₂]
  [Category* D] [Category* H] [Category* H']
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  (Φ : LocalizerMorphism W₁ W₂) [Φ.IsLeftDerivabilityStructure]
  [Φ.IsLocalizedEquivalence]
  {Q : C₂ ⥤ D} [Q.IsLocalization W₂]
  {F : C₂ ⥤ H} (hF : Φ.Derives F)
  (LF : D ⥤ H) (α : Q ⋙ LF ⟶ F) [LF.IsLeftDerivedFunctor α W₂]

include hF in
private lemma isLeftDerivedFunctor_postcomp (G : H ⥤ H') :
    (LF ⋙ G).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ whiskerRight α G) W₂ := by
  have := LeftDerivedByResolutions.hasPointwiseLeftDerivedFunctor_of_derives Φ F hF
  let w := ((Φ.catCommSq W₁.Q Q).iso).inv
  let E := (RightExtension.mk LF α).compTwoSquare w
  have hE : E.IsPointwiseRightKanExtension :=
    (LF.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor α W₂).compTwoSquare w
  have : E.left.IsLeftDerivedFunctor E.hom W₁ := ⟨hE.isRightKanExtension⟩
  have he : IsIso E.hom := isIso_of_isLeftDerivedFunctor_of_inverts E.left E.hom hF
  let E' := RightExtension.mk (LF ⋙ G) ((Functor.associator _ _ _).inv ≫ whiskerRight α G)
  have he' : IsIso (E'.compTwoSquare w).hom := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    have : IsIso (G.map (E.hom.app X)) := inferInstance
    convert this using 1 <;>
      simp [E, E', RightExtension.compTwoSquare, map_comp]
  exact ⟨(E'.isPointwiseRightKanExtensionOfCompTwoSquare w
    ((E'.compTwoSquare w).isPointwiseRightKanExtensionOfIsIsoOfIsLocalization
      W₁)).isRightKanExtension⟩
end

end Resolutions

namespace Resolutions
open CategoryTheory Limits Functor LocalizerMorphism

open ZeroObject StacksDraft.UnboundedLeftDerivedFunctor in
private lemma isLeftDerivedFunctor_mapHomotopyCategory_postcomp
    {A B H : Type*} [Category* A] [Category* B] [Category* H]
    [Abelian A] [Abelian B] [EnoughProjectives A]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B]
    [HasExactColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F]
    [PreservesColimitsOfShape ℕ F]
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (G : DerivedCategory B ⥤ H) :
    (LF ⋙ G).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ whiskerRight α G)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  let P : ObjectProperty A := fun X => Projective X
  let : P.ContainsZero := ⟨0, isZero_zero A, inferInstance⟩
  have hsum : ∀ X Y : A, P X → P Y → P (X ⊞ Y) := by
    intro X Y hX hY
    change Projective X at hX
    change Projective Y at hY
    let := hX
    let := hY
    exact inferInstance
  have hcover : ∀ X : A, ∃ (Y : A) (_ : P Y) (p : Y ⟶ X), Epi p :=
    fun X => ⟨Projective.over X, inferInstance, Projective.π X, inferInstance⟩
  have hFP : ∀ (a : ℤ) (L : CochainComplex A ℤ), L.IsStrictlyLE a →
      (∀ n, P (L.X n)) → L.Acyclic →
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic := by
    intro a L hL hP hacyc
    let := hL
    have (n : ℤ) : Projective (L.X n) := hP n
    have := CochainComplex.isKProjective_of_projective L a
    let h := F.mapHomotopy (CochainComplex.IsKProjective.homotopyZero (𝟙 L) hacyc)
    intro n
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    apply (IsZero.iff_id_eq_zero _).2
    simpa using h.homologyMap_eq n
  have := hasLeftResolutions_cellularLocalizerMorphism P hsum hcover
  have := isLeftDerivabilityStructure_cellularLocalizerMorphism P inferInstance
  have := LeftDerivedByResolutions.isLocalizedEquivalence_inclusionLocalizerMorphism
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) (cellular P)
  exact isLeftDerivedFunctor_postcomp (cellularLocalizerMorphism P)
    (derives_cellularLocalizerMorphism F P hsum hcover hFP) LF α G

end Resolutions

namespace Resolutions
open CategoryTheory Limits Functor LocalizerMorphism

private lemma kan_postcomp_transfer {C C' D H H' : Type*}
    [Category* C] [Category* C'] [Category* D] [Category* H] [Category* H']
    (q : C' ⥤ C)
    [((whiskeringLeft C' C H).obj q).Full]
    [((whiskeringLeft C' C H).obj q).Faithful]
    [((whiskeringLeft C' C H').obj q).Full]
    [((whiskeringLeft C' C H').obj q).Faithful]
    {L : C ⥤ D} {L' : C' ⥤ D} {F : C ⥤ H} {F' : C' ⥤ H}
    (eL : q ⋙ L ≅ L') (eF : q ⋙ F ≅ F')
    (LF : D ⥤ H) (α : L' ⋙ LF ⟶ F') [LF.IsRightKanExtension α]
    (G : H ⥤ H')
    (h : ∀ (β : L ⋙ LF ⟶ F), LF.IsRightKanExtension β →
      (LF ⋙ G).IsRightKanExtension
        ((Functor.associator _ _ _).inv ≫ whiskerRight β G)) :
    (LF ⋙ G).IsRightKanExtension
      ((Functor.associator _ _ _).inv ≫ whiskerRight α G) := by
  let β := ((whiskeringLeft C' C H).obj q).preimage
    ((Functor.associator _ _ _).inv ≫ whiskerRight eL.hom LF ≫ α ≫ eF.inv)
  have hβ : (Functor.associator _ _ _).hom ≫ whiskerLeft q β =
      whiskerRight eL.hom LF ≫ α ≫ eF.inv := by
    dsimp [β]
    rw [← whiskeringLeft_obj_map, map_preimage]
    simp
  have hb : LF.IsRightKanExtension β := by
    rw [TwoTermComplex.isRightKanExtension_iff_precomp_of_fullyFaithful_whiskeringLeft q LF β, hβ]
    exact (TwoTermComplex.isRightKanExtension_iff_of_iso LF eL eF.symm α).1 inferInstance
  have hx := (TwoTermComplex.isRightKanExtension_iff_precomp_of_fullyFaithful_whiskeringLeft q
    (LF ⋙ G) ((Functor.associator _ _ _).inv ≫ whiskerRight β G)).1 (h β hb)
  apply (TwoTermComplex.isRightKanExtension_iff_of_iso (LF ⋙ G) eL
    ((Functor.associator q F G).symm ≪≫ isoWhiskerRight eF G).symm
    ((Functor.associator _ _ _).inv ≫ whiskerRight α G)).2
  convert hx using 1
  ext X
  have hh := congr_app hβ X
  dsimp at hh ⊢
  simp only [Category.id_comp, Category.comp_id] at hh ⊢
  simp only [hh, map_comp]

end Resolutions

namespace Resolutions
open CategoryTheory Limits Functor LocalizerMorphism

private lemma isLeftDerivedFunctor_mapHomologicalComplex_postcomp
    {A B H : Type*} [Category* A] [Category* B] [Category* H]
    [Abelian A] [Abelian B] [EnoughProjectives A]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B]
    [HasExactColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F]
    [PreservesColimitsOfShape ℕ F]
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Q ⋙ LF ⟶
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [LF.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]
    (G : DerivedCategory B ⥤ H) :
    (LF ⋙ G).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ whiskerRight α G)
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) := by
  have := IsLeftDerivedFunctor.isRightKanExtension LF α
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let eF : q ⋙ (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ≅
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)
  refine ⟨kan_postcomp_transfer q (DerivedCategory.quotientCompQhIso A) eF LF α G ?_⟩
  intro β hβ
  have : LF.IsLeftDerivedFunctor β (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := ⟨hβ⟩
  have := isLeftDerivedFunctor_mapHomotopyCategory_postcomp F LF β G
  exact IsLeftDerivedFunctor.isRightKanExtension (LF ⋙ G) _
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))

end Resolutions

open CategoryTheory Limits Functor
open scoped ChangeOfRings

set_option backward.isDefEq.respectTransparency false in
private noncomputable def underivedComparison
    {R : Type uR} {A : Type uA} {R' : Type uRp} {A' : Type uAp}
    [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    (f : R →+* A) (g : R →+* R') (h : A →+* A') (i : R' →+* A')
    (sq : h.comp f = i.comp g) :
    {τ : ModuleCat.restrictScalars.{max v uR uA uRp uAp} f ⋙ ModuleCat.extendScalars g ⟶
      ModuleCat.extendScalars h ⋙ ModuleCat.restrictScalars i //
      ∀ (M : ModuleCat.{max v uR uA uRp uAp} A) (r' : R') (m : M),
        τ.app M (r' ⊗ₜ[R,g] m) = (i r') ⊗ₜ[A,h] m} := by
  let ah := ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp uAp, uA, uAp} h
  let ag := ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp uAp, uR, uRp} g
  let β := (ModuleCat.restrictScalarsComp.{max v uR uA uRp uAp} f h).inv ≫
    (ModuleCat.restrictScalarsComp' g i (h.comp f) sq).hom
  let τ := (mateEquiv ah ag).symm β
  refine ⟨τ, fun M r' m => ?_⟩
  let : Module R M := Module.compHom M f
  let := g.toAlgebra
  let := h.toAlgebra
  have hone : τ.app M ((1 : R') ⊗ₜ[R,g] m) = (1 : A') ⊗ₜ[A,h] m := by
    have hh := congrArg (fun k => k m) (unit_mateEquiv_symm ah ag β M)
    change (1 : A') ⊗ₜ[A,h] m = τ.app M ((1 : R') ⊗ₜ[R,g] m) at hh
    exact hh.symm
  calc
    τ.app M (r' ⊗ₜ[R,g] m) =
        τ.app M (r' • ((1 : R') ⊗ₜ[R,g] m)) := by
      congr 1
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    _ = r' • τ.app M ((1 : R') ⊗ₜ[R,g] m) := (τ.app M).hom.map_smul r' _
    _ = (i r') ⊗ₜ[A,h] m := by
      rw [hone]
      change (i r') • ((1 : A') ⊗ₜ[A,h] m) = _
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- Let `R → A`, `R → R'`, `A → A'`, and `R' → A'` be a commutative square of
commutative rings. There is a natural comparison
`K ⊗ᴸ_R R' ⟶ K ⊗ᴸ_A A'` in `D(R')`.

The first component of the result is the underived comparison, normalized on pure tensors.
The second is its canonical lift between any chosen models of the two total left-derived
functors; the displayed factorization records canonicity as well as functoriality in `K`. -/
-- The body names `private` helpers, so it must not be exposed to importers.
@[stacks 065Z, no_expose]
public noncomputable def derivedBaseChangeComparison
    {R : Type uR} {A : Type uA} {R' : Type uRp} {A' : Type uAp}
    [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [HasDerivedCategory (ModuleCat.{max v uR uA uRp uAp} R)]
    [HasDerivedCategory (ModuleCat.{max v uR uA uRp uAp} A)]
    [HasDerivedCategory (ModuleCat.{max v uR uA uRp uAp} R')]
    [HasDerivedCategory (ModuleCat.{max v uR uA uRp uAp} A')]
    (f : R →+* A) (g : R →+* R') (h : A →+* A') (i : R' →+* A')
    (sq : h.comp f = i.comp g) :
    let Res_f := ModuleCat.restrictScalars.{max v uR uA uRp uAp} f
    let Res_i := ModuleCat.restrictScalars.{max v uR uA uRp uAp} i
    let Ext_g := ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp uAp} g
    let Ext_h := ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h
    letI : (ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max v uR uA uRp uAp, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp uAp, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max v uR uA uRp uAp} i).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max v uR uA uRp uAp, uRp, uAp} i).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max v uR uA uRp uAp} i).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp uAp, uRp, uAp} i).isRightAdjoint
    let F_R := Res_f ⋙ Ext_g
    let F_A := Ext_h ⋙ Res_i
    let U_g := Ext_g.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q (C := ModuleCat.{max v uR uA uRp uAp} R')
    let U_h := Ext_h.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q (C := ModuleCat.{max v uR uA uRp uAp} A')
    ∀ (L_g : DerivedCategory (ModuleCat.{max v uR uA uRp uAp} R) ⥤
          DerivedCategory (ModuleCat.{max v uR uA uRp uAp} R'))
      (L_h : DerivedCategory (ModuleCat.{max v uR uA uRp uAp} A) ⥤
          DerivedCategory (ModuleCat.{max v uR uA uRp uAp} A'))
      (alpha_g : DerivedCategory.Q (C := ModuleCat.{max v uR uA uRp uAp} R) ⋙ L_g ⟶ U_g)
      (alpha_h : DerivedCategory.Q (C := ModuleCat.{max v uR uA uRp uAp} A) ⋙ L_h ⟶ U_h),
      [L_g.IsLeftDerivedFunctor alpha_g
        (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp uAp} R) (ComplexShape.up ℤ))] →
      [L_h.IsLeftDerivedFunctor alpha_h
        (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp uAp} A) (ComplexShape.up ℤ))] →
      let DRes_f := Res_f.mapDerivedCategory
      let DRes_i := Res_i.mapDerivedCategory
      let beta_R :
          DerivedCategory.Q (C := ModuleCat.{max v uR uA uRp uAp} A) ⋙ (DRes_f ⋙ L_g) ⟶
            F_R.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
              DerivedCategory.Q (C := ModuleCat.{max v uR uA uRp uAp} R') :=
        (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight Res_f.mapDerivedCategoryFactors.hom L_g ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft (Res_f.mapHomologicalComplex (ComplexShape.up ℤ)) alpha_g ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight
            (Functor.mapHomologicalComplexCompIso (Iso.refl F_R)
              (ComplexShape.up ℤ)).hom
            (DerivedCategory.Q (C := ModuleCat.{max v uR uA uRp uAp} R'))
      let beta_A :
          DerivedCategory.Q (C := ModuleCat.{max v uR uA uRp uAp} A) ⋙ (L_h ⋙ DRes_i) ⟶
            F_A.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
              DerivedCategory.Q (C := ModuleCat.{max v uR uA uRp uAp} R') :=
        (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight alpha_h DRes_i ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft (Ext_h.mapHomologicalComplex (ComplexShape.up ℤ))
            Res_i.mapDerivedCategoryFactors.hom ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight
            (Functor.mapHomologicalComplexCompIso (Iso.refl F_A)
              (ComplexShape.up ℤ)).hom
            (DerivedCategory.Q (C := ModuleCat.{max v uR uA uRp uAp} R'))
      Σ' (tau0 : F_R ⟶ F_A),
        {tau : DRes_f ⋙ L_g ⟶ L_h ⋙ DRes_i //
          (∀ (M : ModuleCat.{max v uR uA uRp uAp} A) (r' : R') (m : M),
            tau0.app M (r' ⊗ₜ[R,g] m) = (i r') ⊗ₜ[A,h] m) ∧
          Functor.whiskerLeft (DerivedCategory.Q (C := ModuleCat.{max v uR uA uRp uAp} A)) tau ≫
            beta_A =
            beta_R ≫ Functor.whiskerRight
                (NatTrans.mapHomologicalComplex tau0 (ComplexShape.up ℤ))
                (DerivedCategory.Q (C := ModuleCat.{max v uR uA uRp uAp} R'))} := by
  intro Res_f Res_i Ext_g Ext_h F_R F_A U_g U_h
    L_g L_h alpha_g alpha_h inst_g inst_h DRes_f DRes_i beta_R beta_A
  haveI : Res_f.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{max v uR uA uRp uAp, uR, uA} f).isLeftAdjoint
  haveI : Res_f.IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp uAp, uR, uA} f).isRightAdjoint
  haveI : Res_i.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{max v uR uA uRp uAp, uRp, uAp} i).isLeftAdjoint
  haveI : Res_i.IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp uAp, uRp, uAp} i).isRightAdjoint
  haveI : HasExactColimitsOfShape ℕ (ModuleCat.{max v uR uA uRp uAp} A) :=
    TwoTermComplex.hasExactColimitsOfShape_nat_moduleCat
  haveI : HasExactColimitsOfShape ℕ (ModuleCat.{max v uR uA uRp uAp} A') :=
    TwoTermComplex.hasExactColimitsOfShape_nat_moduleCat
  haveI : Ext_h.IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp uAp, uA, uAp} h).isLeftAdjoint
  let γ : DerivedCategory.Q ⋙ (L_h ⋙ DRes_i) ⟶ U_h ⋙ DRes_i :=
    (Functor.associator _ _ _).inv ≫ whiskerRight alpha_h DRes_i
  haveI : (L_h ⋙ DRes_i).IsLeftDerivedFunctor γ
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp uAp} A) (ComplexShape.up ℤ)) :=
    Resolutions.isLeftDerivedFunctor_mapHomologicalComplex_postcomp Ext_h L_h alpha_h DRes_i
  let eA : U_h ⋙ DRes_i ≅ F_A.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q (C := ModuleCat.{max v uR uA uRp uAp} R') :=
    Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (Ext_h.mapHomologicalComplex (ComplexShape.up ℤ))
        Res_i.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (Functor.mapHomologicalComplexCompIso (Iso.refl F_A)
        (ComplexShape.up ℤ)) _
  have hγ := IsLeftDerivedFunctor.isRightKanExtension (L_h ⋙ DRes_i) γ
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp uAp} A) (ComplexShape.up ℤ))
  have hβ : (L_h ⋙ DRes_i).IsRightKanExtension beta_A := by
    have heq : beta_A = γ ≫ eA.hom := by simp [beta_A, γ, eA, Category.assoc]
    rw [heq]
    exact (isRightKanExtension_iff_of_iso₂ γ (γ ≫ eA.hom) eA
      (Iso.refl _) (by simp)).1 hγ
  haveI : (L_h ⋙ DRes_i).IsLeftDerivedFunctor beta_A
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp uAp} A) (ComplexShape.up ℤ)) := ⟨hβ⟩
  let τ₀ := underivedComparison.{uR, uA, uRp, uAp, v} f g h i sq
  exact ⟨τ₀.val, (L_h ⋙ DRes_i).leftDerivedLift beta_A
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp uAp} A) (ComplexShape.up ℤ))
    (DRes_f ⋙ L_g) (beta_R ≫ whiskerRight
      (NatTrans.mapHomologicalComplex τ₀.val (ComplexShape.up ℤ)) DerivedCategory.Q),
    τ₀.property, Functor.leftDerived_fac _ _ _ _ _⟩

end

end RingTheory.TorIndependence

end
