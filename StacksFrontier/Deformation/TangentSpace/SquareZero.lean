module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Ideal
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.DualNumber
public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Completed.Basic
public import StacksFrontier.Deformation.TangentSpace.Functor
public import StacksFrontier.RingTheory.AdicCompletion.LiftToComplete

/-!
# Square-zero points of a prorepresentable functor

The square-zero points of a prorepresentable functor are computed by
derivations.

## Main definitions

* `SquareZeroPoint` is the value at `k[V]` of
  the functor prorepresented by `S`.
* `Deformation.residueAlgHom_eq_residueHom` identifies the two structural augmentations to
  the chosen residue field.
* `Derivations` is the type of derivations into
  `V`, with its `S`-module structure induced by the residue map.
* `squareZeroExtensionObject` realizes a finite-dimensional `k[V]` as a complete local
  `Λ`-algebra with its augmentation to `k`.

## Main results

* `squareZeroPointsDerivationsEquiv` is the
  canonical identification of square-zero points and derivations.
* `squareZeroPointsDerivationsEquivHom` identifies the actual morphisms of the
  complete-local-algebra category with derivations whenever `A` realizes `k[V]`.
* The accompanying application and naturality lemmas characterize both directions and
  record functoriality in both `V` and `S`.

## Implementation notes

The object denoted `k[V]` in the source is Mathlib's `TrivSqZeroExt k V`. The first
equivalence records maps with the augmentation equation explicitly. The categorical
equivalence applies to any complete local algebra object `A` identified with this
square-zero extension compatibly with residue maps; thus its source is the actual
categorical morphism type. The formulas say that the two maps are `f ↦ f - q` and
`D ↦ q + D`.

## References

* [Stacks Project, Tag 06IC](https://stacks.math.columbia.edu/tag/06IC)
-/

@[expose] public section

namespace Deformation

/-! ### Square-zero points of a prorepresentable functor -/

section
open IsLocalRing CategoryTheory
open scoped RightActions
universe u v w x y


variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

attribute [instance] CompleteLocalAlgCat.commRing CompleteLocalAlgCat.algebra

local instance (V : Type x) [AddCommGroup V] [Module k V] : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

local instance (V : Type x) [AddCommGroup V] [Module k V] : IsCentralScalar k V :=
  Module.isCentralScalar_oppositeOfCommSemiring k V

/-- The canonical augmentation `S → k` determined by the chosen identification of the
residue field with `k`. -/
noncomputable def residueHom (S : CompleteLocalAlgCat.{u, v, w} Λ k) : S →ₐ[Λ] k :=
  S.residueEquiv.toAlgHom.comp (IsScalarTower.toAlgHom Λ S (ResidueField S))

/-- The two structural augmentations of a complete local algebra to its chosen residue field
agree: `Deformation.residueAlgHom`, used for residue-field-valued derivations, and
`Deformation.residueHom`, used for the tangent space. -/
public theorem residueAlgHom_eq_residueHom (S : CompleteLocalAlgCat.{u, v, w} Λ k) :
    residueAlgHom S = residueHom S := by
  ext r
  rfl

/-- A `k[V]`-valued point of the functor prorepresented by `S`: a `Λ`-algebra map
`S → k[V]` whose composite with the augmentation is the residue map `S → k`. -/
abbrev SquareZeroPoint (S : CompleteLocalAlgCat.{u, v, w} Λ k)
    (V : Type x) [AddCommGroup V] [Module k V] :=
  letI : Module Λ V := Module.compHom V (algebraMap Λ k)
  letI : IsScalarTower Λ k V := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  { f : S →ₐ[Λ] TrivSqZeroExt k V //
    (TrivSqZeroExt.fstHom Λ k V).comp f = residueHom S }

/-- The `Λ`-derivations `S → V`, where `S` acts on `V` through its residue map. -/
abbrev Derivations (S : CompleteLocalAlgCat.{u, v, w} Λ k)
    (V : Type x) [AddCommGroup V] [Module k V] :=
  letI : Module Λ V := Module.compHom V (algebraMap Λ k)
  letI : Module S V := Module.compHom V (residueHom S).toRingHom
  Derivation Λ S V

/-- Postcompose a square-zero point with a linear map of its square-zero ideals. -/
def SquareZeroPoint.map (S : CompleteLocalAlgCat.{u, v, w} Λ k)
    {V : Type x} {W : Type y} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (l : V →ₗ[k] W) :
    SquareZeroPoint S V → SquareZeroPoint S W := by
  letI : Module Λ V := Module.compHom V (algebraMap Λ k)
  letI : IsScalarTower Λ k V := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module Λ W := Module.compHom W (algebraMap Λ k)
  letI : IsScalarTower Λ k W := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact fun f ↦
    ⟨(TrivSqZeroExt.map l).restrictScalars Λ |>.comp f.1, by
      ext s
      simpa using AlgHom.congr_fun f.2 s⟩

/-- Precompose a square-zero point by a map compatible with the residue maps. -/
def SquareZeroPoint.precomp
    (S : CompleteLocalAlgCat.{u, v, w} Λ k)
    (T : CompleteLocalAlgCat.{u, y, w} Λ k)
    (g : T →ₐ[Λ] S) (hg : (residueHom S).comp g = residueHom T)
    (V : Type x) [AddCommGroup V] [Module k V] :
    SquareZeroPoint S V → SquareZeroPoint T V := by
  letI : Module Λ V := Module.compHom V (algebraMap Λ k)
  letI : IsScalarTower Λ k V := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact fun f ↦ ⟨f.1.comp g, by
    ext t
    exact (AlgHom.congr_fun f.2 (g t)).trans (AlgHom.congr_fun hg t)⟩

/-- **Stacks Project, Tag 06IC.** Evaluation of the functor prorepresented by `S` on
`k[V]` is canonically equivalent to the type of `Λ`-derivations `S → V`. -/
theorem squareZeroPoint_fst
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) (V : Type x)
    [AddCommGroup V] [Module k V] (f : SquareZeroPoint S V) (s : S) :
    (f.1 s).fst = residueHom S s := by
  exact AlgHom.congr_fun f.2 s

noncomputable def squareZeroPoint_toDerivation
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) (V : Type x)
    [AddCommGroup V] [Module k V] (f : SquareZeroPoint S V) : Derivations S V := by
  letI : Module Λ V := Module.compHom V (algebraMap Λ k)
  letI : IsScalarTower Λ k V := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : IsScalarTower Λ kᵐᵒᵖ V := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module S V := Module.compHom V (residueHom S).toRingHom
  let dlin : S →ₗ[Λ] V :=
    (TrivSqZeroExt.sndHom k V).restrictScalars Λ |>.comp f.1.toLinearMap
  refine
    { toLinearMap := dlin
      map_one_eq_zero' := by
        change (f.1 1).snd = 0
        simp
      leibniz' := fun s t => by
        change (f.1 (s * t)).snd = s •> (f.1 t).snd + t •> (f.1 s).snd
        have hm : f.1 (s * t) = f.1 s * f.1 t := map_mul f.1 s t
        rw [hm, TrivSqZeroExt.snd_mul]
        rw [squareZeroPoint_fst S V f s, squareZeroPoint_fst S V f t]
        change (residueHom S s) •> (f.1 t).snd +
            (f.1 s).snd <• (residueHom S t) =
          s •> (f.1 t).snd + t •> (f.1 s).snd
        rfl }

noncomputable def derivation_toSquareZeroPoint
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) (V : Type x)
    [AddCommGroup V] [Module k V] (D : Derivations S V) : SquareZeroPoint S V := by
  letI : Module Λ V := Module.compHom V (algebraMap Λ k)
  letI : IsScalarTower Λ k V := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module S V := Module.compHom V (residueHom S).toRingHom
  letI : Algebra Λ (TrivSqZeroExt k V) := TrivSqZeroExt.algebra' Λ k V
  refine ⟨{
    toFun := fun s => (residueHom S s, D s)
    map_one' := by apply TrivSqZeroExt.ext <;> simp [D.map_one_eq_zero]
    map_mul' := fun s t => by
      apply TrivSqZeroExt.ext
      · change residueHom S (s * t) = residueHom S s * residueHom S t
        exact map_mul (residueHom S) s t
      · change D (s * t) =
          (residueHom S s) •> D t + D s <• (residueHom S t)
        exact D.leibniz s t
    map_zero' := by apply TrivSqZeroExt.ext <;> simp
    map_add' := fun s t => by
      apply TrivSqZeroExt.ext
      · change residueHom S (s + t) = residueHom S s + residueHom S t
        exact map_add (residueHom S) s t
      · exact map_add D s t
    commutes' := fun r => by
      change (residueHom S (algebraMap Λ S r), D (algebraMap Λ S r)) =
        (algebraMap Λ k r, 0)
      simp [residueHom]
  }, ?_⟩
  ext s
  rfl

noncomputable def squareZeroPointEquiv
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) (V : Type x)
    [AddCommGroup V] [Module k V] : SquareZeroPoint S V ≃ Derivations S V := by
  letI : Module Λ V := Module.compHom V (algebraMap Λ k)
  letI : IsScalarTower Λ k V := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : IsScalarTower Λ kᵐᵒᵖ V := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module S V := Module.compHom V (residueHom S).toRingHom
  letI : Algebra Λ (TrivSqZeroExt k V) := TrivSqZeroExt.algebra' Λ k V
  refine {
    toFun := squareZeroPoint_toDerivation S V
    invFun := derivation_toSquareZeroPoint S V
    left_inv := ?_
    right_inv := ?_ }
  · intro f
    apply Subtype.ext
    apply AlgHom.ext
    intro s
    apply TrivSqZeroExt.ext
    · exact (squareZeroPoint_fst S V f s).symm
    · rfl
  · intro D
    exact Derivation.ext fun s => rfl

@[stacks 06IC "square_zero_points_derivations"]
noncomputable def squareZeroPointsDerivationsEquiv
    (S : CompleteLocalAlgCat.{u, v, w} Λ k)
    (V : Type x) [AddCommGroup V] [Module k V] :
    SquareZeroPoint S V ≃ Derivations S V := squareZeroPointEquiv S V

/-- In the forward identification, the derivation associated to `f` is the square-zero
component of `f`, i.e. `s ↦ f(s) - q(s)`. -/
@[stacks 06IC "square_zero_points_derivations"]
theorem squareZeroPointsDerivationsEquiv_apply
    (S : CompleteLocalAlgCat.{u, v, w} Λ k)
    (V : Type x) [AddCommGroup V] [Module k V]
    (f : SquareZeroPoint S V) (s : S) :
    squareZeroPointsDerivationsEquiv S V f s = (f.1 s).snd := rfl

/-- In the inverse identification, a derivation `D` is sent to the map
`s ↦ q(s) + D(s)` into `k[V]`. -/
@[stacks 06IC "square_zero_points_derivations"]
theorem squareZeroPointsDerivationsEquiv_symm_apply
    (S : CompleteLocalAlgCat.{u, v, w} Λ k)
    (V : Type x) [AddCommGroup V] [Module k V]
    (D : Derivations S V) (s : S) :
    ((squareZeroPointsDerivationsEquiv S V).symm D).1 s =
      (residueHom S s, D s) := rfl

/-- The canonical identification is functorial in the finite-dimensional vector space. -/
@[stacks 06IC "square_zero_points_derivations"]
theorem squareZeroPointsDerivationsEquiv_naturality
    (S : CompleteLocalAlgCat.{u, v, w} Λ k)
    {V : Type x} {W : Type y} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (l : V →ₗ[k] W)
    (f : SquareZeroPoint S V) (s : S) :
    squareZeroPointsDerivationsEquiv S W (f.map S l) s =
      l (squareZeroPointsDerivationsEquiv S V f s) := by
  change (TrivSqZeroExt.map l (f.1 s)).snd = l ((f.1 s).snd)
  simp

/-- The canonical identification is natural under precomposition in the representing
complete local algebra. -/
@[stacks 06IC "square_zero_points_derivations"]
theorem squareZeroPointsDerivationsEquiv_precomp
    (S : CompleteLocalAlgCat.{u, v, w} Λ k)
    (T : CompleteLocalAlgCat.{u, y, w} Λ k)
    (g : T →ₐ[Λ] S) (hg : (residueHom S).comp g = residueHom T)
    (V : Type x) [AddCommGroup V] [Module k V]
    (f : SquareZeroPoint S V) (t : T) :
    squareZeroPointsDerivationsEquiv T V (f.precomp S T g hg V) t =
      squareZeroPointsDerivationsEquiv S V f (g t) := rfl

noncomputable def squareZeroPointsHomSquareZeroPointEquiv
    (S A : CompleteLocalAlgCat.{u, v, w} Λ k)
    (V : Type x) [AddCommGroup V] [Module k V]
    (e : A ≃+* TrivSqZeroExt k V)
    (hΛ : ∀ r : Λ, e (algebraMap Λ A r) = (algebraMap Λ k r, 0))
    (he : ∀ a : A, (e a).fst = residueHom A a) :
    (S ⟶ A) ≃ SquareZeroPoint S V := by
  letI : Module Λ V := Module.compHom V (algebraMap Λ k)
  letI : IsScalarTower Λ k V := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : IsScalarTower Λ kᵐᵒᵖ V := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Algebra Λ (TrivSqZeroExt k V) := TrivSqZeroExt.algebra' Λ k V
  let toPoint (f : S ⟶ A) : SquareZeroPoint S V := by
    refine ⟨{
      toFun := fun s => e (f.hom s)
      map_one' := by simp
      map_mul' := fun s t => by simp [map_mul]
      map_zero' := by simp
      map_add' := fun s t => by simp [map_add]
      commutes' := fun r => by
        calc
          e (f.hom (algebraMap Λ S r)) = e (algebraMap Λ A r) := by rw [f.hom.commutes]
          _ = algebraMap Λ (TrivSqZeroExt k V) r := by
            rw [TrivSqZeroExt.algebraMap_eq_inl']
            change e (algebraMap Λ A r) = (algebraMap Λ k r, 0)
            exact hΛ r
    }, ?_⟩
    apply AlgHom.ext
    intro s
    calc
      (e (f.hom s)).fst = residueHom A (f.hom s) := he _
      _ = residueHom S s := by
        change A.residueEquiv (residue A (f.hom s)) = S.residueEquiv (residue S s)
        exact f.residue_comm s
  let fromPoint (f : SquareZeroPoint S V) : S ⟶ A := by
    let φ : S →ₐ[Λ] A := {
      toFun := fun s => e.symm (f.1 s)
      map_one' := by simp
      map_mul' := fun s t => by simp [map_mul]
      map_zero' := by simp
      map_add' := fun s t => by simp [map_add]
      commutes' := fun r => by
        apply e.injective
        calc
          e (e.symm (f.1 (algebraMap Λ S r))) = f.1 (algebraMap Λ S r) :=
            e.apply_symm_apply _
          _ = algebraMap Λ (TrivSqZeroExt k V) r := f.1.commutes r
          _ = e (algebraMap Λ A r) := by
            rw [TrivSqZeroExt.algebraMap_eq_inl']
            change (algebraMap Λ k r, 0) = e (algebraMap Λ A r)
            exact (hΛ r).symm
    }
    refine ⟨φ, ?_, ?_⟩
    · refine ⟨fun s hu => ?_⟩
      change IsUnit (e.symm (f.1 s)) at hu
      have huT' := hu.map e.toRingHom
      change IsUnit (e (e.symm (f.1 s))) at huT'
      have huT : IsUnit (f.1 s) := by simpa using huT'
      have hfst : IsUnit ((f.1 s).fst) := TrivSqZeroExt.isUnit_iff_isUnit_fst.mp huT
      have hq : IsUnit (residueHom S s) := by
        rw [← AlgHom.congr_fun f.2 s]
        exact hfst
      have hqne : residueHom S s ≠ 0 := hq.ne_zero
      have hrsne : residue S s ≠ 0 := by
        intro hrs
        apply hqne
        simp [residueHom, hrs]
      exact (IsLocalRing.residue_ne_zero_iff_isUnit s).mp hrsne
    · intro s
      change residueHom A (e.symm (f.1 s)) = residueHom S s
      calc
        residueHom A (e.symm (f.1 s)) = (e (e.symm (f.1 s))).fst := (he _).symm
        _ = (f.1 s).fst := by simp
        _ = residueHom S s := AlgHom.congr_fun f.2 s
  refine {
    toFun := toPoint
    invFun := fromPoint
    left_inv := ?_
    right_inv := ?_ }
  · intro f
    apply CompleteLocalAlgCat.Hom.ext
    apply AlgHom.ext
    intro s
    apply e.injective
    simp [toPoint, fromPoint]
  · intro f
    apply Subtype.ext
    apply AlgHom.ext
    intro s
    simp [toPoint, fromPoint]

/-- A finite-dimensional trivial square-zero extension, as an object of the category
of complete local `Λ`-algebras, with its algebra coordinates and residue augmentation. -/
@[stacks 06IC "square_zero_points_derivations"]
noncomputable def squareZeroExtensionObject
    (V : Type x) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    { A : CompleteLocalAlgCat.{u, max w x, w} Λ k //
      ∃ e : A ≃+* TrivSqZeroExt k V,
        (∀ r : Λ, e (algebraMap Λ A r) = (algebraMap Λ k r, 0)) ∧
        (∀ a : A, (e a).fst = residueHom A a) } := by
  let T := TrivSqZeroExt k V
  letI : Module Λ V := Module.compHom V (algebraMap Λ k)
  letI : IsScalarTower Λ k V := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : IsScalarTower Λ kᵐᵒᵖ V := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Algebra Λ T := TrivSqZeroExt.algebra' Λ k V
  letI : Module.Finite k T := by
    exact (Module.Basis.singleton Unit k).prod
      (Module.Basis.ofVectorSpace k V) |>.finiteDimensional_of_finite
  letI : IsNoetherianRing T := IsNoetherianRing.of_finite k T
  letI : IsArtinianRing T := IsArtinianRing.of_finite k T
  letI : IsLocalRing T := by
    apply IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add
    intro a b hab
    rcases TrivSqZeroExt.isUnit_or_isNilpotent a with ha | ha
    · exact Or.inl ha
    · right
      have ha0 : a.fst = 0 := by
        have hnil : IsNilpotent a.fst :=
          TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst.mp ha
        exact isNilpotent_iff_eq_zero.mp hnil
      have hbunit : IsUnit b.fst := by
        have hsum := hab.map (TrivSqZeroExt.fstHom k k V).toRingHom
        change IsUnit (a.fst + b.fst) at hsum
        rw [ha0, zero_add] at hsum
        exact hsum
      exact TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr hbunit
  have hsurj : Function.Surjective (TrivSqZeroExt.fstHom k k V) := by
    intro r
    exact ⟨(r, 0), rfl⟩
  have hker : RingHom.ker (TrivSqZeroExt.fstHom k k V).toRingHom =
      maximalIdeal T := IsLocalRing.ker_eq_maximalIdeal _ hsurj
  let e₁ : IsLocalRing.ResidueField T ≃ₐ[k]
      T ⧸ RingHom.ker (TrivSqZeroExt.fstHom k k V).toRingHom :=
    Ideal.quotientEquivAlgOfEq k hker.symm
  let e₂ : (T ⧸ RingHom.ker (TrivSqZeroExt.fstHom k k V).toRingHom) ≃ₐ[k] k :=
    Ideal.quotientKerAlgEquivOfSurjective hsurj
  let eΛ : IsLocalRing.ResidueField T ≃ₐ[Λ] k := (e₁.trans e₂).restrictScalars Λ
  let hcomplete : IsNoetherianCompleteLocalRing T :=
    ⟨inferInstance, inferInstance,
      IsAdicComplete.of_isNilpotent (maximalIdeal T) (by
        rw [← hker]
        exact ⟨2, TrivSqZeroExt.kerIdeal_sq k V⟩)⟩
  let A : CompleteLocalAlgCat.{u, max w x, w} Λ k := ⟨T, hcomplete, eΛ⟩
  refine ⟨A, ⟨RingEquiv.refl T, ?_, ?_⟩⟩
  · intro r
    rfl
  · intro a
    change a.fst = eΛ (IsLocalRing.residue T a)
    symm
    change (e₁.trans e₂) (IsLocalRing.residue T a) = a.fst
    calc
      (e₁.trans e₂) (IsLocalRing.residue T a) =
          e₂ (Ideal.Quotient.mk (RingHom.ker (TrivSqZeroExt.fstHom k k V).toRingHom) a) := by
        rw [AlgEquiv.trans_apply]
        rfl
      _ = (TrivSqZeroExt.fstHom k k V) a := by
        change Ideal.quotientKerAlgEquivOfSurjective hsurj
          (Ideal.Quotient.mk _ a) = _
        rw [Ideal.quotientKerAlgEquivOfSurjective_mk]
      _ = a.fst := rfl

/-- The identification for the actual morphism type of the category of complete local
`Λ`-algebras. The equivalence `e` identifies the chosen object `A` with `k[V]`, and
`he` says that its residue map is the square-zero augmentation. -/
@[stacks 06IC "square_zero_points_derivations"]
noncomputable def squareZeroPointsDerivationsEquivHom
    (S A : CompleteLocalAlgCat.{u, v, w} Λ k)
    (V : Type x) [AddCommGroup V] [Module k V]
    (e : A ≃+* TrivSqZeroExt k V)
    (hΛ : ∀ r : Λ, e (algebraMap Λ A r) = (algebraMap Λ k r, 0))
    (he : ∀ a : A, (e a).fst = residueHom A a) :
    (S ⟶ A) ≃ Derivations S V :=
  (squareZeroPointsHomSquareZeroPointEquiv S A V e hΛ he).trans
    (squareZeroPointsDerivationsEquiv S V)

/-- A categorical morphism `f : S ⟶ k[V]` determines the derivation given by its
square-zero component. -/
@[stacks 06IC "square_zero_points_derivations"]
theorem squareZeroPointsDerivationsEquivHom_apply
    (S A : CompleteLocalAlgCat.{u, v, w} Λ k)
    (V : Type x) [AddCommGroup V] [Module k V]
    (e : A ≃+* TrivSqZeroExt k V)
    (hΛ : ∀ r : Λ, e (algebraMap Λ A r) = (algebraMap Λ k r, 0))
    (he : ∀ a : A, (e a).fst = residueHom A a)
    (f : S ⟶ A) (s : S) :
    squareZeroPointsDerivationsEquivHom S A V e hΛ he f s =
      (e (f.hom s)).snd := by
  rfl

/-- Conversely, the categorical morphism determined by `D` is `s ↦ q(s) + D(s)`
in square-zero coordinates. -/
@[stacks 06IC "square_zero_points_derivations"]
theorem squareZeroPointsDerivationsEquivHom_symm_apply
    (S A : CompleteLocalAlgCat.{u, v, w} Λ k)
    (V : Type x) [AddCommGroup V] [Module k V]
    (e : A ≃+* TrivSqZeroExt k V)
    (hΛ : ∀ r : Λ, e (algebraMap Λ A r) = (algebraMap Λ k r, 0))
    (he : ∀ a : A, (e a).fst = residueHom A a)
    (D : Derivations S V) (s : S) :
    e (((squareZeroPointsDerivationsEquivHom S A V e hΛ he).symm D).hom s) =
      (residueHom S s, D s) := by
  simp only [squareZeroPointsDerivationsEquivHom, squareZeroPointsHomSquareZeroPointEquiv,
    squareZeroPointsDerivationsEquiv, squareZeroPointEquiv, Equiv.symm_trans, Equiv.symm_mk,
    Equiv.trans_apply, Equiv.coe_fn_mk, derivation_toSquareZeroPoint, AlgHom.coe_mk,
    RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, RingEquiv.apply_symm_apply]
  change (residueHom S s, D s) = (residueHom S s, D s)
  rfl

/-- The categorical identification commutes with maps between square-zero extensions. -/
@[stacks 06IC "square_zero_points_derivations"]
theorem squareZeroPointsDerivationsEquivHom_naturality
    (S A B : CompleteLocalAlgCat.{u, v, w} Λ k)
    (V : Type x) (W : Type y)
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (eA : A ≃+* TrivSqZeroExt k V)
    (hΛA : ∀ r : Λ, eA (algebraMap Λ A r) = (algebraMap Λ k r, 0))
    (heA : ∀ a : A, (eA a).fst = residueHom A a)
    (eB : B ≃+* TrivSqZeroExt k W)
    (hΛB : ∀ r : Λ, eB (algebraMap Λ B r) = (algebraMap Λ k r, 0))
    (heB : ∀ b : B, (eB b).fst = residueHom B b)
    (g : A ⟶ B) (l : V →ₗ[k] W)
    (hg : ∀ a : A, (eB (g.hom a)).snd = l (eA a).snd)
    (f : S ⟶ A) (s : S) :
    squareZeroPointsDerivationsEquivHom S B W eB hΛB heB (f ≫ g) s =
      l (squareZeroPointsDerivationsEquivHom S A V eA hΛA heA f s) := by
  rw [squareZeroPointsDerivationsEquivHom_apply,
    squareZeroPointsDerivationsEquivHom_apply, CompleteLocalAlgCat.comp_hom]
  exact hg (f.hom s)

/-- The categorical identification is natural in the representing algebra. -/
@[stacks 06IC "square_zero_points_derivations"]
theorem squareZeroPointsDerivationsEquivHom_precomp
    (T S A : CompleteLocalAlgCat.{u, v, w} Λ k)
    (V : Type x) [AddCommGroup V] [Module k V]
    (e : A ≃+* TrivSqZeroExt k V)
    (hΛ : ∀ r : Λ, e (algebraMap Λ A r) = (algebraMap Λ k r, 0))
    (he : ∀ a : A, (e a).fst = residueHom A a)
    (g : T ⟶ S) (f : S ⟶ A) (t : T) :
    squareZeroPointsDerivationsEquivHom T A V e hΛ he (g ≫ f) t =
      squareZeroPointsDerivationsEquivHom S A V e hΛ he f (g.hom t) := by
  rw [squareZeroPointsDerivationsEquivHom_apply,
    squareZeroPointsDerivationsEquivHom_apply, CompleteLocalAlgCat.comp_hom]
  rfl

end

end Deformation
