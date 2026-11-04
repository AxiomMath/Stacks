module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.Deformation.PredeformationTangent.LinearLift
public import StacksFrontier.Deformation.Predeformation.Associated
public import StacksFrontier.Deformation.SchlessingerConditions.SquareZeroExtension
public import StacksFrontier.Deformation.TangentSpace.Functor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tangent space of a predeformation category is a vector space

If the associated functor of isomorphism classes of a predeformation category satisfies
Schlessinger's condition (S2), then its values on finite-dimensional square-zero extensions
carry a natural `k`-vector space structure, and that functor is naturally tensoring with its
value on the dual numbers.

## Main definitions

* `Deformation.associatedTangentSpaceModuleStructure`: the canonical linear lift of the
  associated square-zero functor.
* `Deformation.associatedTangentSpaceAddCommGroup` and
  `Deformation.associatedTangentSpaceModule`: that structure, transported onto the tangent
  space itself.
* `Deformation.associatedTangentSpaceFunctor_iso_tensorLeft`: the canonical tensor
  equivalence.

## Main results

* `Deformation.associatedTangentSpaceModuleStructure_carrier`: the value of the linear lift at
  the rank-one module has underlying set the tangent space.
* `Deformation.associatedTangentSpaceFunctor_iso_tensorLeft_pure` characterizes the tensor
  equivalence on pure tensors, and
  `Deformation.associatedTangentSpaceFunctor_iso_tensorLeft_naturality` states its
  functoriality.

## Implementation notes

The associated functor is the canonical functor of fibrewise isomorphism classes of Tag 07W5.
We use the Artinian square-zero functor of Tag 06IB, with independent universes for the
coefficient ring, residue field, Artinian algebras and total category. Its linear lift is
defined on modules in the algebra carrier universe. The tangent space is
`Deformation.tangentSpaceArtinian`, whose rank-one module is `ULift k`. The tensor equivalence
sends `t ⊗ v` to the image of `t` under the map `ULift k → V`, `a ↦ a.down • v`.

The declarations ending in `Unlifted` retain the canonical structures and tensor formulas for
the `Deformation.artinianTangentSpace` model, which uses `k` itself as its rank-one module.
Both models obtain their structures from the same linear lift, so existing consumers can keep
their unlifted dual numbers.

The product condition on the associated functor is condition (S2) for the finite-dimensional
square-zero extension `k[M × N] → k`, which is Tag 06HZ.

## References

* [Stacks Project, Tag 06IH](https://stacks.math.columbia.edu/tag/06IH)
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory CategoryTheory.Limits

universe u v w u₁ v₁

/-! ### Scalar structures on the vector spaces -/

/-- The right action of `k` on a `k`-vector space. -/
local instance squareZeroProjectionModuleMulOpposite (k : Type w) [Field k]
    (V : FGModuleCat.{max v w} k) : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

/-- The left and right `k`-actions on a `k`-vector space agree. -/
local instance squareZeroProjectionIsCentralScalar (k : Type w) [Field k]
    (V : FGModuleCat.{max v w} k) : IsCentralScalar k V :=
  Module.isCentralScalar_oppositeOfCommSemiring k V

/-- A `k`-vector space as a `Λ`-module through the structure map of `k`. -/
local instance squareZeroProjectionModuleOfAlgebra (Λ : Type u) (k : Type w) [CommRing Λ] [Field k]
    [Algebra Λ k] (V : FGModuleCat.{max v w} k) : Module Λ V :=
  Module.compHom V (algebraMap Λ k)

/-- The scalar tower `Λ → k → V`. -/
local instance squareZeroProjectionIsScalarTower (Λ : Type u) (k : Type w) [CommRing Λ] [Field k]
    [Algebra Λ k] (V : FGModuleCat.{max v w} k) : IsScalarTower Λ k V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- The scalar tower `Λ → kᵐᵒᵖ → V`. -/
local instance squareZeroProjectionIsScalarTowerMulOpposite (Λ : Type u) (k : Type w) [CommRing Λ]
    [Field k] [Algebra Λ k] (V : FGModuleCat.{max v w} k) : IsScalarTower Λ kᵐᵒᵖ V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-! ### The square-zero projection and its products -/

/-- The augmentation `k[M] → k` of the square-zero object attached to `M`, as a morphism of
`𝒞_Λ` onto the residue-field object. -/
noncomputable def squareZeroProjection (M : FGModuleCat.{max v w} k) :
    (squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M ⟶
      residueFieldObject.{u, v, w} Λ k where
  hom := (ULift.algEquiv.{u, w, v} (R := Λ) (A := k)).symm.toAlgHom.comp
    (TrivSqZeroExt.fstHom Λ k M)
  isLocal := by
    let : IsLocalRing (TrivSqZeroExt k M) :=
      ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M).isLocalRing
    let hf : IsLocalHom (TrivSqZeroExt.fstHom Λ k M).toRingHom :=
      IsLocalHom.of_surjective _ TrivSqZeroExt.fst_surjective
    let := hf
    let : IsLocalHom
        ((ULift.algEquiv.{u, w, v} (R := Λ) (A := k)).symm.toAlgHom.toRingHom) :=
      inferInstance
    exact RingHom.isLocalHom_comp
      ((ULift.algEquiv.{u, w, v} (R := Λ) (A := k)).symm.toAlgHom.toRingHom)
      (TrivSqZeroExt.fstHom Λ k M).toRingHom
  residue_comm := by
    intro x
    change (ULift.algEquiv.{u, w, v} (R := Λ) (A := k))
        (ULift.up ((TrivSqZeroExt.fstHom Λ k M) x)) =
      ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M).residueEquiv
        (IsLocalRing.residue
          ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M) x)
    rw [ULift.algEquiv_apply]
    exact (squareZeroExtensionArtinian_residue Λ k M x).symm

/-- The augmentation of the square-zero object attached to `M` is the projection `k[M] → k`
in the sense of Tag 06HZ. -/
theorem squareZeroProjection_isSquareZeroProjection (M : FGModuleCat.{max v w} k) :
    IsSquareZeroProjection (V := (M : Type (max v w)))
      (squareZeroProjection.{u, v, w} (Λ := Λ) (k := k) M) := by
  refine ⟨ULift.algEquiv.{u, w, v} (R := Λ) (A := k), AlgEquiv.refl (R := Λ), ?_⟩
  apply AlgHom.ext
  intro x
  rfl

/-- The product of two finite-dimensional vector spaces, in the carrier universe of the
Artinian algebras. -/
abbrev prodModule (M N : FGModuleCat.{max v w} k) : FGModuleCat.{max v w} k :=
  FGModuleCat.of k (M × N)

variable {M N : FGModuleCat.{max v w} k}

/-- Two maps into a fibre product of square-zero objects agree in the first coordinate. -/
private theorem productBase_eq
    (s : PullbackCone (squareZeroProjection.{u, v, w} (Λ := Λ) (k := k) M)
      (squareZeroProjection.{u, v, w} (Λ := Λ) (k := k) N)) (x : s.pt) :
    (s.fst.hom x).fst = (s.snd.hom x).fst := by
  have h := congrArg
    (fun f : s.pt ⟶ residueFieldObject.{u, v, w} Λ k ↦ f.hom x) s.condition
  change ULift.up (TrivSqZeroExt.fst (s.fst.hom x)) =
    ULift.up (TrivSqZeroExt.fst (s.snd.hom x)) at h
  exact ULift.up_injective h

/-- The algebra map into `k[M × N]` determined by a cone over the two augmentations. -/
private noncomputable def productLiftAlg
    (s : PullbackCone (squareZeroProjection.{u, v, w} (Λ := Λ) (k := k) M)
      (squareZeroProjection.{u, v, w} (Λ := Λ) (k := k) N)) :
    s.pt →ₐ[Λ] TrivSqZeroExt k (prodModule M N) where
  toFun x := Prod.mk (TrivSqZeroExt.fst (s.fst.hom x))
    (Prod.mk (TrivSqZeroExt.snd (s.fst.hom x)) (TrivSqZeroExt.snd (s.snd.hom x)))
  map_one' := by
    apply TrivSqZeroExt.ext
    · change (s.fst.hom 1).fst = 1
      exact congrArg TrivSqZeroExt.fst s.fst.hom.map_one
    · apply Prod.ext
      · change (s.fst.hom 1).snd = 0
        exact congrArg TrivSqZeroExt.snd s.fst.hom.map_one
      · change (s.snd.hom 1).snd = 0
        exact congrArg TrivSqZeroExt.snd s.snd.hom.map_one
  map_mul' := by
    intro x y
    have hx := productBase_eq s x
    have hy := productBase_eq s y
    apply TrivSqZeroExt.ext
    · change (s.fst.hom (x * y)).fst = (s.fst.hom x).fst * (s.fst.hom y).fst
      exact congrArg TrivSqZeroExt.fst (s.fst.hom.map_mul x y)
    · apply Prod.ext
      · change (s.fst.hom (x * y)).snd =
          (s.fst.hom x).fst • (s.fst.hom y).snd +
            MulOpposite.op (s.fst.hom y).fst • (s.fst.hom x).snd
        have hm := congrArg TrivSqZeroExt.snd (s.fst.hom.map_mul x y)
        change (s.fst.hom (x * y)).snd = _ at hm
        exact hm
      · change (s.snd.hom (x * y)).snd =
          (s.fst.hom x).fst • (s.snd.hom y).snd +
            MulOpposite.op (s.fst.hom y).fst • (s.snd.hom x).snd
        have hm := congrArg TrivSqZeroExt.snd (s.snd.hom.map_mul x y)
        change (s.snd.hom (x * y)).snd =
          (s.snd.hom x).fst • (s.snd.hom y).snd +
            MulOpposite.op (s.snd.hom y).fst • (s.snd.hom x).snd at hm
        rw [← hx, ← hy] at hm
        exact hm
  map_zero' := by
    apply TrivSqZeroExt.ext
    · change (s.fst.hom 0).fst = 0
      exact congrArg TrivSqZeroExt.fst s.fst.hom.map_zero
    · apply Prod.ext
      · change (s.fst.hom 0).snd = 0
        have hz := congrArg TrivSqZeroExt.snd s.fst.hom.map_zero
        change (s.fst.hom 0).snd = 0 at hz
        exact hz
      · change (s.snd.hom 0).snd = 0
        have hz := congrArg TrivSqZeroExt.snd s.snd.hom.map_zero
        change (s.snd.hom 0).snd = 0 at hz
        exact hz
  map_add' := by
    intro x y
    apply TrivSqZeroExt.ext
    · change (s.fst.hom (x + y)).fst = (s.fst.hom x).fst + (s.fst.hom y).fst
      exact congrArg TrivSqZeroExt.fst (s.fst.hom.map_add x y)
    · apply Prod.ext
      · change (s.fst.hom (x + y)).snd = (s.fst.hom x).snd + (s.fst.hom y).snd
        exact congrArg TrivSqZeroExt.snd (s.fst.hom.map_add x y)
      · change (s.snd.hom (x + y)).snd = (s.snd.hom x).snd + (s.snd.hom y).snd
        exact congrArg TrivSqZeroExt.snd (s.snd.hom.map_add x y)
  commutes' r := by
    apply TrivSqZeroExt.ext
    · change (s.fst.hom (algebraMap Λ s.pt r)).fst = algebraMap Λ k r
      exact congrArg TrivSqZeroExt.fst (s.fst.hom.commutes r)
    · apply Prod.ext
      · change (s.fst.hom (algebraMap Λ s.pt r)).snd = 0
        have hc := congrArg TrivSqZeroExt.snd (s.fst.hom.commutes r)
        change (s.fst.hom (algebraMap Λ s.pt r)).snd = 0 at hc
        simpa using hc
      · change (s.snd.hom (algebraMap Λ s.pt r)).snd = 0
        have hc := congrArg TrivSqZeroExt.snd (s.snd.hom.commutes r)
        change (s.snd.hom (algebraMap Λ s.pt r)).snd = 0 at hc
        simpa using hc

/-- The morphism of `𝒞_Λ` determined by a cone over the two augmentations. -/
private noncomputable def productLiftHom
    (s : PullbackCone (squareZeroProjection.{u, v, w} (Λ := Λ) (k := k) M)
      (squareZeroProjection.{u, v, w} (Λ := Λ) (k := k) N)) :
    s.pt ⟶ (squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj
      (prodModule M N) where
  hom := productLiftAlg s
  isLocal := by
    refine ⟨fun x hunit => ?_⟩
    have hfst : IsUnit (TrivSqZeroExt.fst (productLiftAlg s x)) :=
      TrivSqZeroExt.isUnit_iff_isUnit_fst.mp hunit
    have hne : TrivSqZeroExt.fst (s.fst.hom x) ≠ 0 := by
      have hh := isUnit_iff_ne_zero.mp hfst
      have heq : TrivSqZeroExt.fst (productLiftAlg s x) =
          TrivSqZeroExt.fst (s.fst.hom x) := rfl
      rw [heq] at hh
      exact hh
    have hfst' : IsUnit (TrivSqZeroExt.fst (s.fst.hom x)) :=
      isUnit_iff_ne_zero.mpr hne
    have haug : IsUnit (((squareZeroProjection.{u, v, w}
        (Λ := Λ) (k := k) M).hom.comp s.fst.hom) x) := by
      change IsUnit (ULift.up (TrivSqZeroExt.fst (s.fst.hom x)))
      exact RingHom.isUnit_map (ULift.ringEquiv (R := k)).symm.toRingHom hfst'
    let : IsLocalHom
        ((squareZeroProjection.{u, v, w} (Λ := Λ) (k := k) M).hom.toRingHom) :=
      (squareZeroProjection.{u, v, w} (Λ := Λ) (k := k) M).isLocal
    let : IsLocalHom s.fst.hom.toRingHom := s.fst.isLocal
    let : IsLocalHom (((squareZeroProjection.{u, v, w}
        (Λ := Λ) (k := k) M).hom.comp s.fst.hom).toRingHom) :=
      RingHom.isLocalHom_comp _ _
    exact IsLocalHom.map_nonunit
      (f := ((squareZeroProjection.{u, v, w} (Λ := Λ) (k := k) M).hom.comp
        s.fst.hom).toRingHom) x haug
  residue_comm := by
    intro x
    change ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj
      (prodModule M N)).residueEquiv
        (IsLocalRing.residue _ (productLiftAlg s x)) =
      s.pt.residueEquiv (IsLocalRing.residue s.pt x)
    rw [squareZeroExtensionArtinian_residue]
    change (s.fst.hom x).fst = _
    rw [← squareZeroExtensionArtinian_residue Λ k M (s.fst.hom x)]
    exact s.fst.residue_comm x

/-- The first projection of the square-zero object on a product of modules. -/
noncomputable abbrev squareZeroProductFst :
    (squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj
        (prodModule M N) ⟶
      (squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M :=
  (squareZeroExtensionArtinian Λ k).map (FGModuleCat.ofHom (LinearMap.fst k M N))

/-- The second projection of the square-zero object on a product of modules. -/
noncomputable abbrev squareZeroProductSnd :
    (squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj
        (prodModule M N) ⟶
      (squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj N :=
  (squareZeroExtensionArtinian Λ k).map (FGModuleCat.ofHom (LinearMap.snd k M N))

private theorem squareZeroProduct_maps_commute :
    squareZeroProductFst.{u, v, w} (Λ := Λ) (k := k) (M := M) (N := N) ≫
      squareZeroProjection.{u, v, w} (Λ := Λ) (k := k) M =
    squareZeroProductSnd.{u, v, w} (Λ := Λ) (k := k) (M := M) (N := N) ≫
      squareZeroProjection.{u, v, w} (Λ := Λ) (k := k) N := by
  apply ArtinianLocalAlgCat.hom_ext
  ext x
  change TrivSqZeroExt k (prodModule M N) at x
  change (ULift.algEquiv.{u, w, v} (R := Λ) (A := k)).symm
      (TrivSqZeroExt.fst (TrivSqZeroExt.map (LinearMap.fst k M N) x)) =
    (ULift.algEquiv.{u, w, v} (R := Λ) (A := k)).symm
      (TrivSqZeroExt.fst (TrivSqZeroExt.map (LinearMap.snd k M N) x))
  rw [TrivSqZeroExt.fst_map, TrivSqZeroExt.fst_map]

/-- `k[M × N]` is the fibre product of `k[M] → k` and `k[N] → k` in `𝒞_Λ`. -/
theorem squareZeroProduct_isPullback :
    IsPullback
      (squareZeroProductFst.{u, v, w} (Λ := Λ) (k := k) (M := M) (N := N))
      (squareZeroProductSnd.{u, v, w} (Λ := Λ) (k := k) (M := M) (N := N))
      (squareZeroProjection.{u, v, w} (Λ := Λ) (k := k) M)
      (squareZeroProjection.{u, v, w} (Λ := Λ) (k := k) N) := by
  let comm := squareZeroProduct_maps_commute.{u, v, w} (Λ := Λ) (k := k) (M := M) (N := N)
  let cone := PullbackCone.mk
    (squareZeroProductFst.{u, v, w} (Λ := Λ) (k := k) (M := M) (N := N))
    (squareZeroProductSnd.{u, v, w} (Λ := Λ) (k := k) (M := M) (N := N)) comm
  have hlim : IsLimit cone := by
    refine PullbackCone.IsLimit.mk comm (fun s ↦ productLiftHom s) ?_ ?_ ?_
    · intro s
      apply ArtinianLocalAlgCat.hom_ext
      apply AlgHom.ext
      intro x
      change TrivSqZeroExt.map (LinearMap.fst k M N) (productLiftAlg s x) = s.fst.hom x
      exact TrivSqZeroExt.ext (TrivSqZeroExt.fst_map _ _) (TrivSqZeroExt.snd_map _ _)
    · intro s
      apply ArtinianLocalAlgCat.hom_ext
      apply AlgHom.ext
      intro x
      change TrivSqZeroExt.map (LinearMap.snd k M N) (productLiftAlg s x) = s.snd.hom x
      exact TrivSqZeroExt.ext ((TrivSqZeroExt.fst_map _ _).trans (productBase_eq s x))
        (TrivSqZeroExt.snd_map _ _)
    · intro s m hfst hsnd
      apply ArtinianLocalAlgCat.hom_ext
      apply AlgHom.ext
      intro x
      let z : TrivSqZeroExt k (prodModule M N) := m.hom x
      have hf : TrivSqZeroExt.map (LinearMap.fst k M N) z = s.fst.hom x :=
        congrArg (fun f : s.pt ⟶ (squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M ↦
          f.hom x) hfst
      have hg : TrivSqZeroExt.map (LinearMap.snd k M N) z = s.snd.hom x :=
        congrArg (fun f : s.pt ⟶ (squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj N ↦
          f.hom x) hsnd
      have h1 := congrArg TrivSqZeroExt.fst hf
      have h2 := congrArg TrivSqZeroExt.snd hf
      have h3 := congrArg TrivSqZeroExt.snd hg
      rw [TrivSqZeroExt.fst_map] at h1
      rw [TrivSqZeroExt.snd_map] at h2 h3
      exact TrivSqZeroExt.ext h1 (Prod.ext h2 h3)
  exact IsPullback.of_isLimit hlim

end

/-! ### Condition (S2) gives the product bijection -/

section
open CategoryTheory CategoryTheory.Limits

universe u v w u₁ v₁

/-- For a set-valued functor on `𝒞_Λ` whose category of elements is cofibered in groupoids and
satisfies (S2), evaluation on a fibre square over a square-zero projection is a bijection onto
the product. -/
theorem elements_bijective_of_schlessingerConditionS2
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (F : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type u₁)
    {A B X P : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {V : Type (max v w)} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (d : A ⟶ X) (e : B ⟶ X) (g : P ⟶ A) (h : P ⟶ B)
    (hPB : IsPullback h g e d)
    (hsq : IsSquareZeroProjection (V := V) e)
    (hcof : IsCofiberedInGroupoids (CategoryOfElements.π F))
    (hS2 : SchlessingerConditionS2 (CategoryOfElements.π F))
    (hcompat : ∀ x : F.obj A, ∀ y : F.obj B, F.map d x = F.map e y) :
    Function.Bijective (fun z : F.obj P ↦ (F.map g z, F.map h z)) := by
  classical
  let p := CategoryOfElements.π F
  constructor
  · intro x y hxy
    let xA : F.Elements := ⟨A, F.map g x⟩
    let yB : F.Elements := ⟨B, F.map h x⟩
    let zX : F.Elements := ⟨X, F.map d (F.map g x)⟩
    let d' : xA ⟶ zX := CategoryOfElements.homMk xA zX d (by dsimp [xA, zX])
    let e' : yB ⟶ zX := CategoryOfElements.homMk yB zX e (by
      dsimp [yB, zX]
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, hPB.w])
    let U : F.Elements := ⟨P, x⟩
    let W : F.Elements := ⟨P, y⟩
    let toA : U ⟶ xA := CategoryOfElements.homMk U xA g (by dsimp [U, xA])
    let toB : U ⟶ yB := CategoryOfElements.homMk U yB h (by dsimp [U, yB])
    have hxy₁ := congrArg Prod.fst hxy
    have hxy₂ := congrArg Prod.snd hxy
    let fromWtoA : W ⟶ xA := CategoryOfElements.homMk W xA g (by
      dsimp [W, xA]
      exact hxy₁.symm)
    let fromWtoB : W ⟶ yB := CategoryOfElements.homMk W yB h (by
      dsimp [W, yB]
      exact hxy₂.symm)
    let Pcomp : PullbackCompletion p d' e' g h := by
      refine ⟨U, rfl, toA, toB, ?_, ?_, ?_⟩
      · apply CategoryOfElements.ext F
        change (h : P ⟶ B) ≫ e = (g : P ⟶ A) ≫ d
        exact hPB.w
      · simp [toA, p, CategoryOfElements.π]
      · simp [toB, p, CategoryOfElements.π]
    let Qcomp : PullbackCompletion p d' e' g h := by
      refine ⟨W, rfl, fromWtoA, fromWtoB, ?_, ?_, ?_⟩
      · apply CategoryOfElements.ext F
        change (h : P ⟶ B) ≫ e = (g : P ⟶ A) ≫ d
        exact hPB.w
      · simp [fromWtoA, p, CategoryOfElements.π]
      · simp [fromWtoB, p, CategoryOfElements.π]
    obtain ⟨b, hb, hbase⟩ :=
      schlessingerConditionS2_comparison_squareZero
        p hcof hS2 d' e' hsq g h hPB Pcomp Qcomp
    have hbval := CategoryOfElements.map_snd b
    have hh := hbval
    change F.map (p.map b) x = y at hh
    rw [hbase] at hh
    simpa [Pcomp, Qcomp, U, W, p, CategoryOfElements.π, Functor.map_id_apply] using hh
  · intro xy
    rcases xy with ⟨x, y⟩
    let zX : F.Elements := ⟨X, F.map d x⟩
    let xA : F.Elements := ⟨A, x⟩
    let yB : F.Elements := ⟨B, y⟩
    let d' : xA ⟶ zX := CategoryOfElements.homMk xA zX d (by dsimp [xA, zX])
    let e' : yB ⟶ zX := CategoryOfElements.homMk yB zX e (by
      dsimp [yB, zX]
      exact (hcompat x y).symm)
    obtain ⟨Pcomp⟩ := schlessingerConditionS2_completion_squareZero
      p hcof hS2 d' e' hsq g h hPB
    let z : F.obj P := F.map (eqToHom Pcomp.apex_eq) Pcomp.apex.2
    refine ⟨z, ?_⟩
    apply Prod.ext
    · have hm := CategoryOfElements.map_snd Pcomp.toFirst
      change F.map (p.map Pcomp.toFirst) Pcomp.apex.2 = x at hm
      rw [Pcomp.map_toFirst] at hm
      change F.map (eqToHom Pcomp.apex_eq ≫ g) Pcomp.apex.2 = x at hm
      simpa [z, Functor.map_comp] using hm
    · have hm := CategoryOfElements.map_snd Pcomp.toSecond
      change F.map (p.map Pcomp.toSecond) Pcomp.apex.2 = y at hm
      rw [Pcomp.map_toSecond] at hm
      change F.map (eqToHom Pcomp.apex_eq ≫ h) Pcomp.apex.2 = y at hm
      simpa [z, Functor.map_comp] using hm

end

/-! ### The special fibre and the zero module -/

section
open CategoryTheory CategoryTheory.Limits

universe u v w u₁ v₁

local instance tangentSquareZeroModuleMulOpposite (k : Type w) [Field k]
    (V : FGModuleCat.{max v w} k) : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

local instance tangentSquareZeroIsCentralScalar (k : Type w) [Field k]
    (V : FGModuleCat.{max v w} k) : IsCentralScalar k V :=
  Module.isCentralScalar_oppositeOfCommSemiring k V

local instance tangentSquareZeroModuleOfAlgebra (Λ : Type u) (k : Type w) [CommRing Λ] [Field k]
    [Algebra Λ k] (V : FGModuleCat.{max v w} k) : Module Λ V :=
  Module.compHom V (algebraMap Λ k)

local instance tangentSquareZeroIsScalarTower (Λ : Type u) (k : Type w) [CommRing Λ] [Field k]
    [Algebra Λ k] (V : FGModuleCat.{max v w} k) : IsScalarTower Λ k V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

local instance tangentSquareZeroIsScalarTowerMulOpposite (Λ : Type u) (k : Type w) [CommRing Λ]
    [Field k] [Algebra Λ k] (V : FGModuleCat.{max v w} k) : IsScalarTower Λ kᵐᵒᵖ V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (h𝓕 : IsPredeformationCategory.{u, v, w} 𝓕.p)

/-- The associated functor of a predeformation category has at most one class over the
residue field. -/
theorem associatedClasses_subsingleton_on_special_fiber :
    Subsingleton ((isomorphismClasses 𝓕 h𝓕.cofibered).obj
      (residueFieldObject.{u, v, w} Λ k)) := by
  obtain ⟨h⟩ := isPredeformationFunctor_isomorphismClasses 𝓕 h𝓕
  exact ⟨fun x y ↦ (h.uniq x).trans (h.uniq y).symm⟩

/-- The associated functor of a predeformation category has a class over the residue
field. -/
theorem associatedClasses_nonempty_on_special_fiber :
    Nonempty ((isomorphismClasses 𝓕 h𝓕.cofibered).obj
      (residueFieldObject.{u, v, w} Λ k)) := by
  obtain ⟨h⟩ := isPredeformationFunctor_isomorphismClasses 𝓕 h𝓕
  exact ⟨h.default⟩

/-- The augmentation of the square-zero object on the zero module is an isomorphism of
algebras onto the residue field. -/
noncomputable def squareZeroZeroAlgEquiv :
    (squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj
        (FGModuleCat.of k PUnit.{max v w + 1}) ≃ₐ[Λ]
      residueFieldObject.{u, v, w} Λ k :=
  AlgEquiv.ofBijective
    (squareZeroProjection.{u, v, w} (Λ := Λ) (k := k)
      (FGModuleCat.of k PUnit.{max v w + 1})).hom
    (by
      constructor
      · intro x y hxy
        have hfst : TrivSqZeroExt.fst x = TrivSqZeroExt.fst y := by
          have hcmp := congrArg ULift.down hxy
          change TrivSqZeroExt.fst x = TrivSqZeroExt.fst y at hcmp
          exact hcmp
        apply TrivSqZeroExt.ext
        · exact hfst
        · cases TrivSqZeroExt.snd x
          cases TrivSqZeroExt.snd y
          rfl
      · intro y
        refine ⟨(TrivSqZeroExt.inl ((ULift.algEquiv.{u, w, v} (R := Λ) (A := k)) y) :
          TrivSqZeroExt k (FGModuleCat.of k PUnit.{max v w + 1})), ?_⟩
        change ULift.up (TrivSqZeroExt.fst
          (TrivSqZeroExt.inl ((ULift.algEquiv.{u, w, v} (R := Λ) (A := k)) y) :
            TrivSqZeroExt k (FGModuleCat.of k PUnit.{max v w + 1}))) = y
        apply ULift.ext
        simp)

/-- The augmentation of the square-zero object on the zero module is an isomorphism of
`𝒞_Λ`. -/
noncomputable def squareZeroZeroIso :
    (squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj
        (FGModuleCat.of k PUnit.{max v w + 1}) ≅
      residueFieldObject.{u, v, w} Λ k where
  hom := squareZeroProjection.{u, v, w} (Λ := Λ) (k := k)
    (FGModuleCat.of k PUnit.{max v w + 1})
  inv :=
    { hom := (squareZeroZeroAlgEquiv.{u, v, w} (Λ := Λ) (k := k)).symm.toAlgHom
      isLocal := by
        refine ⟨fun x hx => ?_⟩
        have h := RingHom.isUnit_map
          (squareZeroZeroAlgEquiv.{u, v, w} (Λ := Λ) (k := k)).toRingEquiv.toRingHom hx
        have heq : (squareZeroZeroAlgEquiv.{u, v, w}
            (Λ := Λ) (k := k)).toRingEquiv.toRingHom
            ((squareZeroZeroAlgEquiv.{u, v, w}
              (Λ := Λ) (k := k)).symm.toAlgHom.toRingHom x) = x :=
          (squareZeroZeroAlgEquiv.{u, v, w} (Λ := Λ) (k := k)).apply_symm_apply x
        rw [heq] at h
        exact h
      residue_comm := by
        intro x
        have h := (squareZeroProjection.{u, v, w} (Λ := Λ) (k := k)
          (FGModuleCat.of k PUnit.{max v w + 1})).residue_comm
            ((squareZeroZeroAlgEquiv.{u, v, w} (Λ := Λ) (k := k)).symm x) |>.symm
        have heq : (squareZeroProjection.{u, v, w} (Λ := Λ) (k := k)
            (FGModuleCat.of k PUnit.{max v w + 1})).hom
              ((squareZeroZeroAlgEquiv.{u, v, w} (Λ := Λ) (k := k)).symm x) = x :=
          (squareZeroZeroAlgEquiv.{u, v, w} (Λ := Λ) (k := k)).apply_symm_apply x
        rw [heq] at h
        exact h }
  hom_inv_id := by
    apply ArtinianLocalAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    exact (squareZeroZeroAlgEquiv.{u, v, w} (Λ := Λ) (k := k)).symm_apply_apply x
  inv_hom_id := by
    apply ArtinianLocalAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    exact (squareZeroZeroAlgEquiv.{u, v, w} (Λ := Λ) (k := k)).apply_symm_apply x

/-- Condition (S2) for the associated functor makes evaluation on the two projections of
`k[M × N]` a bijection onto the product. -/
theorem associatedClasses_product_bijective
    (hS2 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered)))
    (M N : FGModuleCat.{max v w} k) :
    Function.Bijective (fun z : (isomorphismClasses 𝓕 h𝓕.cofibered).obj
        ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj (prodModule M N)) ↦
      ((isomorphismClasses 𝓕 h𝓕.cofibered).map
          (squareZeroProductFst.{u, v, w} (Λ := Λ) (k := k) (M := M) (N := N)) z,
       (isomorphismClasses 𝓕 h𝓕.cofibered).map
          (squareZeroProductSnd.{u, v, w} (Λ := Λ) (k := k) (M := M) (N := N)) z)) := by
  let : Module.Finite k (M : Type (max v w)) := M.property
  have hb := elements_bijective_of_schlessingerConditionS2
    (isomorphismClasses 𝓕 h𝓕.cofibered)
    (squareZeroProjection.{u, v, w} (Λ := Λ) (k := k) N)
    (squareZeroProjection.{u, v, w} (Λ := Λ) (k := k) M)
    (squareZeroProductSnd.{u, v, w} (Λ := Λ) (k := k) (M := M) (N := N))
    (squareZeroProductFst.{u, v, w} (Λ := Λ) (k := k) (M := M) (N := N))
    (squareZeroProduct_isPullback.{u, v, w} (Λ := Λ) (k := k) (M := M) (N := N))
    (squareZeroProjection_isSquareZeroProjection.{u, v, w} (Λ := Λ) (k := k) M)
    ((isPredeformationCategory_iff (isomorphismClasses 𝓕 h𝓕.cofibered)).mpr
      (isPredeformationFunctor_isomorphismClasses 𝓕 h𝓕)).cofibered
    hS2
    (fun _ _ ↦ (associatedClasses_subsingleton_on_special_fiber 𝓕 h𝓕).elim _ _)
  constructor
  · intro x y hxy
    apply hb.injective
    exact Prod.ext (congrArg Prod.snd hxy) (congrArg Prod.fst hxy)
  · intro xy
    rcases xy with ⟨x, y⟩
    obtain ⟨z, hz⟩ := hb.surjective (y, x)
    exact ⟨z, Prod.ext (congrArg Prod.snd hz) (congrArg Prod.fst hz)⟩

/-- The hypotheses of the linear-lift construction, for the associated square-zero
functor. -/
theorem associatedSquareZeroFunctor_conditions
    (hS2 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) :
    let L := squareZeroExtensionArtinian.{u, w, max v w} Λ k ⋙
      isomorphismClasses 𝓕 h𝓕.cofibered
    Nonempty (L.obj (FGModuleCat.of k PUnit.{max v w + 1})) ∧
      Subsingleton (L.obj (FGModuleCat.of k PUnit.{max v w + 1})) ∧
      ∀ M N : FGModuleCat.{max v w} k, Function.Bijective
        (fun x : L.obj (prodModule M N) ↦
          (L.map (FGModuleCat.ofHom (LinearMap.fst k M N)) x,
            L.map (FGModuleCat.ofHom (LinearMap.snd k M N)) x)) := by
  let H := isomorphismClasses 𝓕 h𝓕.cofibered
  let i := squareZeroZeroIso.{u, v, w} (Λ := Λ) (k := k)
  obtain ⟨uK⟩ := associatedClasses_nonempty_on_special_fiber 𝓕 h𝓕
  let : Subsingleton (H.obj (residueFieldObject.{u, v, w} Λ k)) :=
    associatedClasses_subsingleton_on_special_fiber 𝓕 h𝓕
  refine ⟨⟨H.map i.inv uK⟩, ?_, ?_⟩
  · constructor
    intro x y
    have hinj : Function.Injective (H.map i.hom) := by
      intro a b hab
      have hh := congrArg (H.map i.inv) hab
      have hh' : H.map (i.hom ≫ i.inv) a = H.map (i.hom ≫ i.inv) b := by
        simpa only [Functor.map_comp_apply] using hh
      simpa only [Iso.hom_inv_id, Functor.map_id_apply] using hh'
    exact hinj (Subsingleton.elim _ _)
  · intro M N
    exact associatedClasses_product_bijective 𝓕 h𝓕 hS2 M N

/-! ### The natural vector space structure -/

/-- **Stacks Project, Tag 06IH.** The natural `k`-linear structure on the values of the
associated functor at finite-dimensional square-zero extensions. In particular its value on
`k[ε]` is the tangent space of the predeformation category. -/
@[stacks 06IH "natural vector space structure"]
noncomputable def associatedTangentSpaceModuleStructure
    (hS2 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) :
    LinearFunctorLift k
      (squareZeroExtensionArtinian.{u, w, max v w} Λ k ⋙
        isomorphismClasses 𝓕 h𝓕.cofibered) :=
  linearFunctorLiftOfProductConditions k _
    (associatedSquareZeroFunctor_conditions 𝓕 h𝓕 hS2).1
    (associatedSquareZeroFunctor_conditions 𝓕 h𝓕 hS2).2.1
    (associatedSquareZeroFunctor_conditions 𝓕 h𝓕 hS2).2.2

/-- The value of the linear lift at the rank-one module has underlying set the tangent space
of the associated functor. -/
theorem associatedTangentSpaceModuleStructure_carrier
    (hS2 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) :
    (((associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕 hS2).functor.obj
      (FGModuleCat.of k (ULift.{v} k)) : ModuleCat.{u₁} k) : Type u₁) =
      tangentSpaceArtinian.{u, w, v} Λ k (isomorphismClasses 𝓕 h𝓕.cofibered) :=
  congrArg (fun H : FGModuleCat.{max v w} k ⥤ Type u₁ ↦
    H.obj (FGModuleCat.of k (ULift.{v} k)))
      (associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕 hS2).forget_comp


/-! ### The unlifted presentation -/

/-- The linear lift in the Over-model presentation of the Artinian algebras, with unlifted
vector spaces. This is the universe specialization of the Artinian lift. -/
noncomputable def associatedTangentSpaceModuleStructureUnlifted
    (𝓖 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓖 : IsPredeformationCategory 𝓖.p)
    (hS2 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.cofibered))) :
    LinearFunctorLift k
      (tangentSpaceSetFunctor Λ k (artinianLocalOver Λ k)
        (squareZeroExtension_mem_artinianLocalOver Λ k)
        (artinianLocalOverToArtinian Λ k ⋙ isomorphismClasses 𝓖 h𝓖.cofibered)) :=
  associatedTangentSpaceModuleStructure.{u, w, w} 𝓖 h𝓖 hS2

/-- The value of the unlifted linear lift at the rank-one module has underlying set the
tangent space of the associated functor. -/
theorem associatedTangentSpaceModuleStructure_carrierUnlifted
    (𝓖 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓖 : IsPredeformationCategory 𝓖.p)
    (hS2 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.cofibered))) :
    (((associatedTangentSpaceModuleStructureUnlifted 𝓖 h𝓖 hS2).functor.obj
      (FGModuleCat.of k k) : ModuleCat.{u₁} k) : Type u₁) =
      artinianTangentSpace Λ k (isomorphismClasses 𝓖 h𝓖.cofibered) :=
  congrArg (fun H : FGModuleCat.{w} k ⥤ Type u₁ ↦ H.obj (FGModuleCat.of k k))
    (associatedTangentSpaceModuleStructureUnlifted 𝓖 h𝓖 hS2).forget_comp

/-- The canonical additive and scalar structures on the unlifted tangent space, transported
together from the linear lift. -/
noncomputable def associatedTangentSpaceModuleDataUnlifted
    (𝓖 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    [h𝓖 : Fact (IsPredeformationCategory 𝓖.p)]
    [hS2 : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.out.cofibered)))] :
    Σ G : AddCommGroup (artinianTangentSpace Λ k
      (isomorphismClasses 𝓖 h𝓖.out.cofibered)),
        letI := G
        Module k (artinianTangentSpace Λ k
          (isomorphismClasses 𝓖 h𝓖.out.cofibered)) :=
  let M := (associatedTangentSpaceModuleStructureUnlifted 𝓖 h𝓖.out hS2.out).functor.obj
    (FGModuleCat.of k k)
  have e : (M : Type u₁) = artinianTangentSpace Λ k
      (isomorphismClasses 𝓖 h𝓖.out.cofibered) :=
    associatedTangentSpaceModuleStructure_carrierUnlifted 𝓖 h𝓖.out hS2.out
  let D : Σ G : AddCommGroup (M : Type u₁), letI := G; Module k (M : Type u₁) :=
    ⟨inferInstance, inferInstance⟩
  e.rec D

/-- The additive group underlying the canonical unlifted tangent-space vector space. -/
@[sga "7 VI 1.3(c)" "additive structure"]
noncomputable instance associatedTangentSpaceAddCommGroupUnlifted
    (𝓖 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    [h𝓖 : Fact (IsPredeformationCategory 𝓖.p)]
    [hS2 : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.out.cofibered)))] :
    AddCommGroup (artinianTangentSpace Λ k
      (isomorphismClasses 𝓖 h𝓖.out.cofibered)) :=
  (associatedTangentSpaceModuleDataUnlifted 𝓖).1

/-- The canonical scalar action of the residue field on the unlifted tangent space. -/
noncomputable instance associatedTangentSpaceModuleUnlifted
    (𝓖 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    [h𝓖 : Fact (IsPredeformationCategory 𝓖.p)]
    [hS2 : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.out.cofibered)))] :
    Module k (artinianTangentSpace Λ k
      (isomorphismClasses 𝓖 h𝓖.out.cofibered)) :=
  (associatedTangentSpaceModuleDataUnlifted 𝓖).2

/-! ### The lifted vector space structure -/

/-- The canonical additive and scalar structures on the tangent space, transported together
from the linear lift. -/
noncomputable def associatedTangentSpaceModuleData
    (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    [h𝓕 : Fact (IsPredeformationCategory.{u, v, w} 𝓕.p)]
    [hS2 : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.out.cofibered)))] :
    Σ G : AddCommGroup (tangentSpaceArtinian.{u, w, v} Λ k
      (isomorphismClasses 𝓕 h𝓕.out.cofibered)),
        letI := G
        Module k (tangentSpaceArtinian.{u, w, v} Λ k
          (isomorphismClasses 𝓕 h𝓕.out.cofibered)) :=
  let M := (associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕.out hS2.out).functor.obj
    (FGModuleCat.of k (ULift.{v} k))
  have e : (M : Type u₁) = tangentSpaceArtinian.{u, w, v} Λ k
      (isomorphismClasses 𝓕 h𝓕.out.cofibered) :=
    associatedTangentSpaceModuleStructure_carrier.{u, v, w} 𝓕 h𝓕.out hS2.out
  let D : Σ G : AddCommGroup (M : Type u₁), letI := G; Module k (M : Type u₁) :=
    ⟨inferInstance, inferInstance⟩
  e.rec D

/-- The additive group underlying the canonical tangent-space vector space. -/
noncomputable instance associatedTangentSpaceAddCommGroup
    (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    [h𝓕 : Fact (IsPredeformationCategory.{u, v, w} 𝓕.p)]
    [hS2 : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.out.cofibered)))] :
    AddCommGroup (tangentSpaceArtinian.{u, w, v} Λ k
      (isomorphismClasses 𝓕 h𝓕.out.cofibered)) :=
  (associatedTangentSpaceModuleData.{u, v, w} 𝓕).1

/-- The canonical scalar action of the residue field on the tangent space. -/
noncomputable instance associatedTangentSpaceModule
    (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    [h𝓕 : Fact (IsPredeformationCategory.{u, v, w} 𝓕.p)]
    [hS2 : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.out.cofibered)))] :
    Module k (tangentSpaceArtinian.{u, w, v} Λ k
      (isomorphismClasses 𝓕 h𝓕.out.cofibered)) :=
  (associatedTangentSpaceModuleData.{u, v, w} 𝓕).2


/-! ### The tensor description of the square-zero functor -/

/-- Transporting additive and scalar structures along an equality of carriers is a linear
equivalence. -/
noncomputable def eqRecModuleDataLinearEquiv {α β : Type u₁} (e : α = β)
    (D : Σ G : AddCommGroup α, letI := G; Module k α) :
    letI := D.1
    letI := D.2
    let E : Σ G : AddCommGroup β, letI := G; Module k β := e.rec D
    letI := E.1
    letI := E.2
    α ≃ₗ[k] β := by
  letI := D.1
  letI := D.2
  let E : Σ G : AddCommGroup β, letI := G; Module k β := e.rec D
  letI := E.1
  letI := E.2
  exact
    { toFun := cast e
      invFun := cast e.symm
      left_inv := by intro x; cases e; rfl
      right_inv := by intro x; cases e; rfl
      map_add' := by intro x y; cases e; rfl
      map_smul' := by intro r x; cases e; rfl }

/-- The canonical linear identification of the tangent space with the value of the
module-valued lift at the rank-one module. -/
noncomputable def associatedTangentSpaceCarrierLinearEquiv
    (hS2 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered)))
    [h𝓕' : Fact (IsPredeformationCategory.{u, v, w} 𝓕.p)]
    [hS2' : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered)))] :
    (((associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕 hS2).functor.obj
      (FGModuleCat.of k (ULift.{v} k)) : ModuleCat.{u₁} k) : Type u₁) ≃ₗ[k]
      tangentSpaceArtinian.{u, w, v} Λ k (isomorphismClasses 𝓕 h𝓕.cofibered) := by
  letI : Fact (IsPredeformationCategory.{u, v, w} 𝓕.p) := ⟨h𝓕⟩
  letI : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) := ⟨hS2⟩
  let M := (associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕 hS2).functor.obj
    (FGModuleCat.of k (ULift.{v} k))
  let e := associatedTangentSpaceModuleStructure_carrier.{u, v, w} 𝓕 h𝓕 hS2
  let D : Σ G : AddCommGroup (M : Type u₁), letI := G; Module k (M : Type u₁) :=
    ⟨M.isAddCommGroup, M.isModule⟩
  have hD : associatedTangentSpaceModuleData.{u, v, w} 𝓕 = e.rec D := by
    simp [associatedTangentSpaceModuleData, M, D]
  convert eqRecModuleDataLinearEquiv e D using 1 <;> rfl

/-- The tensor equivalence exists with the prescribed pure-tensor formula. -/
theorem exists_associatedTangentTensorEquiv
    (hS2 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) :
    let L := (associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕 hS2).functor
    letI : Fact (IsPredeformationCategory.{u, v, w} 𝓕.p) := ⟨h𝓕⟩
    letI : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) := ⟨hS2⟩
    let T := tangentSpaceArtinian.{u, w, v} Λ k (isomorphismClasses 𝓕 h𝓕.cofibered)
    ∃ E : ∀ V : FGModuleCat.{max v w} k,
        TensorProduct k T V ≃ₗ[k] ((L.obj V : ModuleCat.{u₁} k) : Type u₁),
      ∀ (V : FGModuleCat.{max v w} k) (t : T) (v : V),
        E V (t ⊗ₜ[k] v) =
          (L.map (FGModuleCat.ofHom
            (LinearMap.smulRight (ULift.moduleEquiv : ULift.{v} k ≃ₗ[k] k).toLinearMap v))).hom
            (cast (associatedTangentSpaceModuleStructure_carrier.{u, v, w}
              𝓕 h𝓕 hS2).symm t) := by
  let : Fact (IsPredeformationCategory.{u, v, w} 𝓕.p) := ⟨h𝓕⟩
  let : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) := ⟨hS2⟩
  let L := (associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕 hS2).functor
  let T := tangentSpaceArtinian.{u, w, v} Λ k (isomorphismClasses 𝓕 h𝓕.cofibered)
  let e := associatedTangentSpaceCarrierLinearEquiv.{u, v, w} 𝓕 h𝓕 hS2
  let : L.Additive := (associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕 hS2).additive
  let : L.Linear k := (associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕 hS2).linear
  refine ⟨fun V ↦ rankOneTensorEquiv k (uliftRankOneCoord.{w, v} k) L T e V, ?_⟩
  intro V t v
  have hm : FGModuleCat.ofHom
      (LinearMap.smulRight (ULift.moduleEquiv : ULift.{v} k ≃ₗ[k] k).toLinearMap v) =
      rankOneSpan k (uliftRankOneCoord.{w, v} k) V v := by
    apply FGModuleCat.hom_ext
    ext
    rfl
  rw [hm]
  rfl

/-- **Stacks Project, Tag 06IH.** The canonical equivalence from tangent vectors tensored
with `V` to the associated functor evaluated on `k[V]`. -/
@[stacks 06IH "tensor equivalence", sga "7 VI 1.3(c)" "T ⊗ V ≅ [A(k[V])]", sga "7 VI 1.18" "(1)"]
noncomputable def associatedTangentSpaceFunctor_iso_tensorLeft
    (hS2 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) :
    let L := (associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕 hS2).functor
    letI : Fact (IsPredeformationCategory.{u, v, w} 𝓕.p) := ⟨h𝓕⟩
    letI : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) := ⟨hS2⟩
    let T := tangentSpaceArtinian.{u, w, v} Λ k (isomorphismClasses 𝓕 h𝓕.cofibered)
    ∀ V : FGModuleCat.{max v w} k,
      LinearEquiv (RingHom.id k) (TensorProduct k T V)
        ((L.obj V : ModuleCat.{u₁} k) : Type u₁) :=
  Classical.choose (exists_associatedTangentTensorEquiv.{u, v, w} 𝓕 h𝓕 hS2)

/-- **Stacks Project, Tag 06IH.** On pure tensors, the canonical equivalence is induced by the
map `ULift k → V` carrying `1` to `v`. -/
@[stacks 06IH "pure-tensor formula"]
theorem associatedTangentSpaceFunctor_iso_tensorLeft_pure
    (hS2 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) :
    let L := (associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕 hS2).functor
    letI : Fact (IsPredeformationCategory.{u, v, w} 𝓕.p) := ⟨h𝓕⟩
    letI : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) := ⟨hS2⟩
    let T := tangentSpaceArtinian.{u, w, v} Λ k (isomorphismClasses 𝓕 h𝓕.cofibered)
    ∀ (V : FGModuleCat.{max v w} k) (t : T) (v : V),
      associatedTangentSpaceFunctor_iso_tensorLeft.{u, v, w} 𝓕 h𝓕 hS2 V (t ⊗ₜ[k] v) =
        (L.map (FGModuleCat.ofHom
          (LinearMap.smulRight (ULift.moduleEquiv : ULift.{v} k ≃ₗ[k] k).toLinearMap v))).hom
          (cast (associatedTangentSpaceModuleStructure_carrier.{u, v, w}
            𝓕 h𝓕 hS2).symm t) :=
  Classical.choose_spec (exists_associatedTangentTensorEquiv.{u, v, w} 𝓕 h𝓕 hS2)

/-- Postcomposing the map `c ⊗ v` out of a module with `f` replaces `v` by `f v`. -/
private theorem ofHom_smulRight_comp {K V W : FGModuleCat.{max v₁ w} k} (c : K →ₗ[k] k) (f : V ⟶ W)
    (v : V) :
    FGModuleCat.ofHom (c.smulRight (f.hom.hom v)) = FGModuleCat.ofHom (c.smulRight v) ≫ f := by
  apply FGModuleCat.hom_ext
  ext r
  exact (f.hom.hom.map_smul (c r) v).symm

/-- **Stacks Project, Tag 06IH.** The canonical tensor equivalences commute with every linear
map between finite-dimensional vector spaces. -/
@[stacks 06IH "naturality"]
theorem associatedTangentSpaceFunctor_iso_tensorLeft_naturality
    (hS2 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) :
    let L := (associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕 hS2).functor
    letI : Fact (IsPredeformationCategory.{u, v, w} 𝓕.p) := ⟨h𝓕⟩
    letI : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) := ⟨hS2⟩
    let T := tangentSpaceArtinian.{u, w, v} Λ k (isomorphismClasses 𝓕 h𝓕.cofibered)
    ∀ (V W : FGModuleCat.{max v w} k) (f : V ⟶ W) (z : TensorProduct k T V),
      (L.map f).hom
          (associatedTangentSpaceFunctor_iso_tensorLeft.{u, v, w} 𝓕 h𝓕 hS2 V z) =
        associatedTangentSpaceFunctor_iso_tensorLeft.{u, v, w} 𝓕 h𝓕 hS2 W
          (TensorProduct.map (LinearMap.id : T →ₗ[k] T) f.hom.hom z) := by
  dsimp only
  intro V W f z
  let : Fact (IsPredeformationCategory.{u, v, w} 𝓕.p) := ⟨h𝓕⟩
  let : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) := ⟨hS2⟩
  let L := (associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕 hS2).functor
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul t v =>
      rw [TensorProduct.map_tmul, LinearMap.id_apply,
        associatedTangentSpaceFunctor_iso_tensorLeft_pure,
        associatedTangentSpaceFunctor_iso_tensorLeft_pure]
      rw [ofHom_smulRight_comp (K := FGModuleCat.of k (ULift.{v} k)) _ f v, Functor.map_comp]
      rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy


/-! ### The tensor description in the unlifted presentation -/

section Unlifted

variable (𝓖 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓖 : IsPredeformationCategory 𝓖.p)

/-- The canonical linear identification of the unlifted tangent space with the value of the
module-valued lift at the rank-one module. -/
noncomputable def associatedTangentSpaceCarrierLinearEquivUnlifted
    (hS2 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.cofibered)))
    [h𝓖' : Fact (IsPredeformationCategory 𝓖.p)]
    [hS2' : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.cofibered)))] :
    (((associatedTangentSpaceModuleStructureUnlifted 𝓖 h𝓖 hS2).functor.obj
      (FGModuleCat.of k k) : ModuleCat.{u₁} k) : Type u₁) ≃ₗ[k]
      artinianTangentSpace Λ k (isomorphismClasses 𝓖 h𝓖.cofibered) := by
  letI : Fact (IsPredeformationCategory 𝓖.p) := ⟨h𝓖⟩
  letI : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.cofibered))) := ⟨hS2⟩
  let M := (associatedTangentSpaceModuleStructureUnlifted 𝓖 h𝓖 hS2).functor.obj
    (FGModuleCat.of k k)
  let e := associatedTangentSpaceModuleStructure_carrierUnlifted 𝓖 h𝓖 hS2
  let D : Σ G : AddCommGroup (M : Type u₁), letI := G; Module k (M : Type u₁) :=
    ⟨M.isAddCommGroup, M.isModule⟩
  have hD : associatedTangentSpaceModuleDataUnlifted 𝓖 = e.rec D := by
    simp [associatedTangentSpaceModuleDataUnlifted, M, D]
  convert eqRecModuleDataLinearEquiv e D using 1 <;> rfl

/-- The unlifted tensor equivalence exists with the prescribed pure-tensor formula. -/
theorem exists_associatedTangentTensorEquivUnlifted
    (hS2 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.cofibered))) :
    let L := (associatedTangentSpaceModuleStructureUnlifted 𝓖 h𝓖 hS2).functor
    letI : Fact (IsPredeformationCategory 𝓖.p) := ⟨h𝓖⟩
    letI : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.cofibered))) := ⟨hS2⟩
    let T := artinianTangentSpace Λ k (isomorphismClasses 𝓖 h𝓖.cofibered)
    ∃ E : ∀ V : FGModuleCat.{w} k,
        TensorProduct k T V ≃ₗ[k] ((L.obj V : ModuleCat.{u₁} k) : Type u₁),
      ∀ (V : FGModuleCat.{w} k) (t : T) (v : V),
        E V (t ⊗ₜ[k] v) =
          (L.map (FGModuleCat.ofHom
            (LinearMap.smulRight (LinearMap.id : k →ₗ[k] k) v))).hom
            (cast (associatedTangentSpaceModuleStructure_carrierUnlifted
              𝓖 h𝓖 hS2).symm t) := by
  let : Fact (IsPredeformationCategory 𝓖.p) := ⟨h𝓖⟩
  let : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.cofibered))) := ⟨hS2⟩
  let L := (associatedTangentSpaceModuleStructureUnlifted 𝓖 h𝓖 hS2).functor
  let T := artinianTangentSpace Λ k (isomorphismClasses 𝓖 h𝓖.cofibered)
  let e := associatedTangentSpaceCarrierLinearEquivUnlifted 𝓖 h𝓖 hS2
  let : L.Additive := (associatedTangentSpaceModuleStructureUnlifted 𝓖 h𝓖 hS2).additive
  let : L.Linear k := (associatedTangentSpaceModuleStructureUnlifted 𝓖 h𝓖 hS2).linear
  refine ⟨fun V ↦ rankOneTensorEquiv k (rankOneCoord k) L T e V, ?_⟩
  intro V t v
  have hm : FGModuleCat.ofHom (LinearMap.smulRight (LinearMap.id : k →ₗ[k] k) v) =
      rankOneSpan k (rankOneCoord k) V v := by
    apply FGModuleCat.hom_ext
    ext
    rfl
  rw [hm]
  rfl

/-- The canonical equivalence from unlifted tangent vectors tensored with `V` to the
associated functor evaluated on `k[V]`. -/
noncomputable def associatedTangentSpaceFunctor_iso_tensorLeftUnlifted
    (hS2 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.cofibered))) :
    let L := (associatedTangentSpaceModuleStructureUnlifted 𝓖 h𝓖 hS2).functor
    letI : Fact (IsPredeformationCategory 𝓖.p) := ⟨h𝓖⟩
    letI : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.cofibered))) := ⟨hS2⟩
    let T := artinianTangentSpace Λ k (isomorphismClasses 𝓖 h𝓖.cofibered)
    ∀ V : FGModuleCat.{w} k,
      LinearEquiv (RingHom.id k) (TensorProduct k T V)
        ((L.obj V : ModuleCat.{u₁} k) : Type u₁) :=
  Classical.choose (exists_associatedTangentTensorEquivUnlifted 𝓖 h𝓖 hS2)

/-- On pure tensors, the unlifted equivalence is induced by the map `k → V` carrying `1`
to `v`. -/
theorem associatedTangentSpaceFunctor_iso_tensorLeft_pureUnlifted
    (hS2 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.cofibered))) :
    let L := (associatedTangentSpaceModuleStructureUnlifted 𝓖 h𝓖 hS2).functor
    letI : Fact (IsPredeformationCategory 𝓖.p) := ⟨h𝓖⟩
    letI : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.cofibered))) := ⟨hS2⟩
    let T := artinianTangentSpace Λ k (isomorphismClasses 𝓖 h𝓖.cofibered)
    ∀ (V : FGModuleCat.{w} k) (t : T) (v : V),
      associatedTangentSpaceFunctor_iso_tensorLeftUnlifted 𝓖 h𝓖 hS2 V (t ⊗ₜ[k] v) =
        (L.map (FGModuleCat.ofHom
          (LinearMap.smulRight (LinearMap.id : k →ₗ[k] k) v))).hom
          (cast (associatedTangentSpaceModuleStructure_carrierUnlifted
            𝓖 h𝓖 hS2).symm t) :=
  Classical.choose_spec (exists_associatedTangentTensorEquivUnlifted 𝓖 h𝓖 hS2)

/-- The unlifted tensor equivalences commute with every linear map between
finite-dimensional vector spaces. -/
theorem associatedTangentSpaceFunctor_iso_tensorLeft_naturalityUnlifted
    (hS2 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.cofibered))) :
    let L := (associatedTangentSpaceModuleStructureUnlifted 𝓖 h𝓖 hS2).functor
    letI : Fact (IsPredeformationCategory 𝓖.p) := ⟨h𝓖⟩
    letI : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.cofibered))) := ⟨hS2⟩
    let T := artinianTangentSpace Λ k (isomorphismClasses 𝓖 h𝓖.cofibered)
    ∀ (V W : FGModuleCat.{w} k) (f : V ⟶ W) (z : TensorProduct k T V),
      (L.map f).hom
          (associatedTangentSpaceFunctor_iso_tensorLeftUnlifted 𝓖 h𝓖 hS2 V z) =
        associatedTangentSpaceFunctor_iso_tensorLeftUnlifted 𝓖 h𝓖 hS2 W
          (TensorProduct.map (LinearMap.id : T →ₗ[k] T) f.hom.hom z) := by
  dsimp only
  intro V W f z
  let : Fact (IsPredeformationCategory 𝓖.p) := ⟨h𝓖⟩
  let : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.cofibered))) := ⟨hS2⟩
  let L := (associatedTangentSpaceModuleStructureUnlifted 𝓖 h𝓖 hS2).functor
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul t v =>
      rw [TensorProduct.map_tmul, LinearMap.id_apply,
        associatedTangentSpaceFunctor_iso_tensorLeft_pureUnlifted,
        associatedTangentSpaceFunctor_iso_tensorLeft_pureUnlifted]
      rw [ofHom_smulRight_comp (K := FGModuleCat.of k k) _ f v, Functor.map_comp]
      rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

end Unlifted

end

end Deformation
