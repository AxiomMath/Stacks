module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.Deformation.Predeformation.Associated
public import StacksFrontier.Deformation.PredeformationTangent.TangentVectorSpace
public import StacksFrontier.Deformation.SchlessingerConditions.SquareZeroExtension
public import StacksFrontier.Deformation.TangentSpace.Functor

/-!
# The tangent space of a predeformation category (Stacks 06IH)

Let `𝓕` be a predeformation category over `𝒞_Λ` and let `F` be its associated functor of
fibrewise isomorphism classes. If `F` satisfies Schlessinger's condition (S2), then the
values of `F` on the finite-dimensional square-zero extensions `k[V]` carry a canonical
`k`-linear structure, natural in `V`; in particular its value on the dual numbers — the
tangent space of `𝓕` — is a `k`-vector space.

The input the general construction of Stacks 06IA wants is that `F(k[0])` be a singleton
and that `F(k[V × W]) → F(k[V]) × F(k[W])` be bijective. This file supplies both from (S2).
The singleton condition is the defining property of a predeformation category, transported
along the isomorphism `k[0] ≅ k`. For the product condition one observes that
`k[V × W] = k[V] ×_k k[W]` is a prescribed pullback square in `𝒞_Λ` whose right-hand map is
the square-zero projection `k[W] → k`, so the existence and comparison clauses of (S2) for
square-zero extensions (Stacks 06HZ) say exactly that the induced map on the category of
elements of `F` is surjective and injective.

## Main results

* `associatedTangentSpaceFunctorConditions`: **Stacks 06IH**. Condition (S2) for the
  associated functor implies the singleton and binary-product conditions of Stacks 06IA,
  in the bundled form `TangentSpaceFunctorConditions` that the Over-model linear lift
  `tangentSpaceModuleStructure` consumes.

The vector space itself — the linear lift, its carrier identification, and the resulting
additive and scalar structures on the tangent space — is built in
`StacksFrontier.Deformation.PredeformationTangent.TangentVectorSpace`, where it is obtained
by specializing the lifted construction on `FGModuleCat.{max v w} k` to the carrier
universe of `k`. Its `associatedTangentSpaceAddCommGroupUnlifted` and
`associatedTangentSpaceModuleUnlifted` are the covering set of the *additive structure* and
*scalar structure* parts of Stacks 06IH, and they are registered as such at the end of this
file.

## Implementation notes

The associated functor is `isomorphismClasses`, the canonical functor of fibrewise
isomorphism classes of Stacks 07W5, and the tangent space is `artinianTangentSpace`, the
Over-model tangent space of Stacks 06IB. Both the vector spaces and the algebra carriers
live in the carrier universe of `k`, which is the universe the Over-model square-zero
functor of Stacks 06IA supports; the `Unlifted` suffix of the imported names records that
choice, as against the `ULift k` rank-one model of `tangentSpaceArtinian`.

The three conditions are proved here in the `zeroFGModule`/`prodFGModule` spelling that
`TangentSpaceFunctorConditions` is phrased in, which is not the `FGModuleCat.of k PUnit`
and `LinearMap.fst`/`LinearMap.snd` spelling that the lifted construction uses; the two
are equal only after transport, so neither derivation reduces to the other.

## References

* [Stacks Project, Tag 06IH](https://stacks.math.columbia.edu/tag/06IH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Deformation

/-! ### Condition (S2) gives the tangent-space functor conditions -/

section

universe u v w u₁ v₁

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

local instance (V : FGModuleCat.{w} k) : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

local instance (V : FGModuleCat.{w} k) : IsCentralScalar k V :=
  Module.isCentralScalar_oppositeOfCommSemiring k V

local instance (V : FGModuleCat.{w} k) : Module Λ V :=
  Module.compHom V (algebraMap Λ k)

local instance (V : FGModuleCat.{w} k) : IsScalarTower Λ k V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

local instance (V : ModuleCat.{w} k) : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

local instance (V : ModuleCat.{w} k) : IsCentralScalar k V :=
  Module.isCentralScalar_oppositeOfCommSemiring k V

local instance (V : ModuleCat.{w} k) : Module Λ V :=
  Module.compHom V (algebraMap Λ k)

local instance (V : ModuleCat.{w} k) : IsScalarTower Λ k V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

private noncomputable abbrev associatedSquareZeroObject (M : FGModuleCat.{w} k) :
    ArtinianLocalAlgCat.{u, w, w} Λ k :=
  (squareZeroExtensionArtinian Λ k).obj M

private noncomputable abbrev associatedResidueObject :
    ArtinianLocalAlgCat.{u, w, w} Λ k :=
  residueFieldObject.{u, w, w} Λ k

private noncomputable def associatedSquareZeroProjection (M : FGModuleCat.{w} k) :
    associatedSquareZeroObject (Λ := Λ) (k := k) M ⟶ associatedResidueObject (Λ := Λ) (k := k) where
  hom := (ULift.algEquiv.{u, w, w} (R := Λ) (A := k)).symm.toAlgHom.comp
    (TrivSqZeroExt.fstHom Λ k M)
  isLocal := by
    let : IsLocalRing (TrivSqZeroExt k M) :=
      (associatedSquareZeroObject (Λ := Λ) (k := k) M).isLocalRing
    have hf : IsLocalHom (TrivSqZeroExt.fstHom Λ k M).toRingHom :=
      IsLocalHom.of_surjective _ TrivSqZeroExt.fst_surjective
    let := hf
    let : IsLocalHom
        ((ULift.algEquiv.{u, w, w} (R := Λ) (A := k)).symm.toAlgHom.toRingHom) :=
      inferInstance
    exact RingHom.isLocalHom_comp
      ((ULift.algEquiv.{u, w, w} (R := Λ) (A := k)).symm.toAlgHom.toRingHom)
      (TrivSqZeroExt.fstHom Λ k M).toRingHom
  residue_comm := by
    intro x
    change (ULift.algEquiv.{u, w, w} (R := Λ) (A := k))
        (ULift.up ((TrivSqZeroExt.fstHom Λ k M) x)) =
      ((squareZeroExtensionArtinian Λ k).obj M).residueEquiv
        (IsLocalRing.residue ((squareZeroExtensionArtinian Λ k).obj M) x)
    rw [ULift.algEquiv_apply]
    exact (squareZeroExtensionArtinian_residue Λ k M x).symm

private theorem associatedSquareZeroProjection_isSquareZero
    (M : FGModuleCat.{w} k) :
    IsSquareZeroProjection (V := (M : Type (w)))
      (associatedSquareZeroProjection (Λ := Λ) (k := k) M) := by
  refine ⟨ULift.algEquiv.{u, w, w} (R := Λ) (A := k), AlgEquiv.refl (R := Λ), ?_⟩
  apply AlgHom.ext
  intro x
  rfl

private theorem associatedProductBase_eq
    (M N : FGModuleCat.{w} k)
    (s : PullbackCone
      (associatedSquareZeroProjection (Λ := Λ) (k := k) M)
      (associatedSquareZeroProjection (Λ := Λ) (k := k) N))
    (x : s.pt) :
    (s.fst.hom x).fst = (s.snd.hom x).fst := by
  have h := congrArg (fun f : s.pt ⟶ associatedResidueObject (Λ := Λ) (k := k) ↦ f.hom x)
    s.condition
  change ULift.up (TrivSqZeroExt.fst (s.fst.hom x)) =
    ULift.up (TrivSqZeroExt.fst (s.snd.hom x)) at h
  exact ULift.up_injective h

private noncomputable def associatedProductLiftAlg
    (M N : FGModuleCat.{w} k)
    (s : PullbackCone
      (associatedSquareZeroProjection (Λ := Λ) (k := k) M)
      (associatedSquareZeroProjection (Λ := Λ) (k := k) N)) :
    s.pt →ₐ[Λ] TrivSqZeroExt k (prodFGModule k M N : Type (w)) where
  toFun x := Prod.mk (TrivSqZeroExt.fst (s.fst.hom x))
    (Prod.mk (TrivSqZeroExt.snd (s.fst.hom x)) (TrivSqZeroExt.snd (s.snd.hom x)))
  map_one' := by
    apply TrivSqZeroExt.ext
    · change (s.fst.hom 1).fst = 1
      exact congrArg TrivSqZeroExt.fst (s.fst.hom.map_one)
    · apply Prod.ext
      · change (s.fst.hom 1).snd = 0
        exact congrArg TrivSqZeroExt.snd (s.fst.hom.map_one)
      · change (s.snd.hom 1).snd = 0
        exact congrArg TrivSqZeroExt.snd (s.snd.hom.map_one)
  map_mul' := by
    intro x y
    have hx := associatedProductBase_eq M N s x
    have hy := associatedProductBase_eq M N s y
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
      exact congrArg TrivSqZeroExt.fst (s.fst.hom.map_zero)
    · apply Prod.ext
      · change (s.fst.hom 0).snd = 0
        have hz := congrArg TrivSqZeroExt.snd (s.fst.hom.map_zero)
        change (s.fst.hom 0).snd = 0 at hz
        exact hz
      · change (s.snd.hom 0).snd = 0
        have hz := congrArg TrivSqZeroExt.snd (s.snd.hom.map_zero)
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

private noncomputable def associatedProductLiftHom
    (M N : FGModuleCat.{w} k)
    (s : PullbackCone
      (associatedSquareZeroProjection (Λ := Λ) (k := k) M)
      (associatedSquareZeroProjection (Λ := Λ) (k := k) N)) :
    s.pt ⟶ associatedSquareZeroObject (Λ := Λ) (k := k)
      (prodFGModule k M N) where
  hom := associatedProductLiftAlg (Λ := Λ) (k := k) M N s
  isLocal := by
    refine ⟨fun x hunit => ?_⟩
    have hfst : IsUnit (TrivSqZeroExt.fst
        (associatedProductLiftAlg (Λ := Λ) (k := k) M N s x)) :=
      (TrivSqZeroExt.isUnit_iff_isUnit_fst).mp hunit
    have hne : TrivSqZeroExt.fst (s.fst.hom x) ≠ 0 := by
      have hh := (isUnit_iff_ne_zero).mp hfst
      have heq : TrivSqZeroExt.fst
          (associatedProductLiftAlg (Λ := Λ) (k := k) M N s x) =
          TrivSqZeroExt.fst (s.fst.hom x) := rfl
      rw [heq] at hh
      exact hh
    have hfst' : IsUnit (TrivSqZeroExt.fst (s.fst.hom x)) :=
      isUnit_iff_ne_zero.mpr hne
    have haug : IsUnit (((associatedSquareZeroProjection (Λ := Λ) (k := k) M).hom.comp
        s.fst.hom) x) := by
      change IsUnit (ULift.up (TrivSqZeroExt.fst (s.fst.hom x)))
      exact RingHom.isUnit_map (ULift.ringEquiv (R := k)).symm.toRingHom hfst'
    let : IsLocalHom ((associatedSquareZeroProjection (Λ := Λ) (k := k) M).hom.toRingHom) :=
      (associatedSquareZeroProjection (Λ := Λ) (k := k) M).isLocal
    let : IsLocalHom (s.fst.hom.toRingHom) := s.fst.isLocal
    let : IsLocalHom (((associatedSquareZeroProjection (Λ := Λ) (k := k) M).hom.comp
        s.fst.hom).toRingHom) := RingHom.isLocalHom_comp _ _
    exact IsLocalHom.map_nonunit
      (f := ((associatedSquareZeroProjection (Λ := Λ) (k := k) M).hom.comp
        s.fst.hom).toRingHom) x haug
  residue_comm := by
    intro x
    change ((squareZeroExtensionArtinian Λ k).obj
      (prodFGModule k M N)).residueEquiv
        (IsLocalRing.residue _
          (associatedProductLiftAlg (Λ := Λ) (k := k) M N s x)) =
      s.pt.residueEquiv (IsLocalRing.residue s.pt x)
    rw [squareZeroExtensionArtinian_residue]
    change (s.fst.hom x).fst = _
    rw [← squareZeroExtensionArtinian_residue Λ k M (s.fst.hom x)]
    exact s.fst.residue_comm x

private noncomputable def associatedSquareZeroProductFst
    (M N : FGModuleCat.{w} k) :
    associatedSquareZeroObject (Λ := Λ) (k := k) (prodFGModule k M N) ⟶
      associatedSquareZeroObject (Λ := Λ) (k := k) M :=
  (squareZeroExtensionArtinian Λ k).map (prodFst k M N)

private noncomputable def associatedSquareZeroProductSnd
    (M N : FGModuleCat.{w} k) :
    associatedSquareZeroObject (Λ := Λ) (k := k) (prodFGModule k M N) ⟶
      associatedSquareZeroObject (Λ := Λ) (k := k) N :=
  (squareZeroExtensionArtinian Λ k).map (prodSnd k M N)

private theorem associatedSquareZeroProduct_maps_commute (M N : FGModuleCat.{w} k) :
    associatedSquareZeroProductFst (Λ := Λ) (k := k) M N ≫
      associatedSquareZeroProjection (Λ := Λ) (k := k) M =
    associatedSquareZeroProductSnd (Λ := Λ) (k := k) M N ≫
      associatedSquareZeroProjection (Λ := Λ) (k := k) N := by
  apply ArtinianLocalAlgCat.hom_ext
  ext x
  change TrivSqZeroExt k (M × N) at x
  change (ULift.algEquiv.{u, w, w} (R := Λ) (A := k)).symm
      (TrivSqZeroExt.fst (TrivSqZeroExt.map (LinearMap.fst k M N) x)) =
    (ULift.algEquiv.{u, w, w} (R := Λ) (A := k)).symm
      (TrivSqZeroExt.fst (TrivSqZeroExt.map (LinearMap.snd k M N) x))
  rw [TrivSqZeroExt.fst_map, TrivSqZeroExt.fst_map]

/-- An element of `k[M × N]` is determined by its images in `k[M]` and `k[N]`. -/
private theorem trivSqZeroExt_prod_ext (M N : FGModuleCat.{w} k) {z z' : TrivSqZeroExt k (M × N)}
    (h₁ : TrivSqZeroExt.map (LinearMap.fst k M N) z = TrivSqZeroExt.map (LinearMap.fst k M N) z')
    (h₂ : TrivSqZeroExt.map (LinearMap.snd k M N) z = TrivSqZeroExt.map (LinearMap.snd k M N) z') :
    z = z' := by
  have h₃ := congrArg TrivSqZeroExt.snd h₁
  have h₄ := congrArg TrivSqZeroExt.snd h₂
  rw [TrivSqZeroExt.snd_map, TrivSqZeroExt.snd_map] at h₃ h₄
  exact TrivSqZeroExt.ext (by simpa using congrArg TrivSqZeroExt.fst h₁) (Prod.ext h₃ h₄)

private theorem associatedSquareZeroProduct_isPullback (M N : FGModuleCat.{w} k) :
    IsPullback
      (associatedSquareZeroProductFst (Λ := Λ) (k := k) M N)
      (associatedSquareZeroProductSnd (Λ := Λ) (k := k) M N)
      (associatedSquareZeroProjection (Λ := Λ) (k := k) M)
      (associatedSquareZeroProjection (Λ := Λ) (k := k) N) := by
  let comm := associatedSquareZeroProduct_maps_commute (Λ := Λ) (k := k) M N
  have hfst (s : PullbackCone (associatedSquareZeroProjection (Λ := Λ) (k := k) M)
      (associatedSquareZeroProjection (Λ := Λ) (k := k) N)) (x : s.pt) :
      TrivSqZeroExt.map (LinearMap.fst k M N) (associatedProductLiftAlg M N s x) =
        s.fst.hom x :=
    TrivSqZeroExt.ext (by rw [TrivSqZeroExt.fst_map]; rfl) (by rw [TrivSqZeroExt.snd_map]; rfl)
  have hsnd (s : PullbackCone (associatedSquareZeroProjection (Λ := Λ) (k := k) M)
      (associatedSquareZeroProjection (Λ := Λ) (k := k) N)) (x : s.pt) :
      TrivSqZeroExt.map (LinearMap.snd k M N) (associatedProductLiftAlg M N s x) =
        s.snd.hom x :=
    TrivSqZeroExt.ext
      (by rw [TrivSqZeroExt.fst_map]; exact associatedProductBase_eq M N s x)
      (by rw [TrivSqZeroExt.snd_map]; rfl)
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk comm
    (fun s ↦ associatedProductLiftHom (Λ := Λ) (k := k) M N s) ?_ ?_ ?_)
  · exact fun s ↦ ArtinianLocalAlgCat.hom_ext (AlgHom.ext (hfst s))
  · exact fun s ↦ ArtinianLocalAlgCat.hom_ext (AlgHom.ext (hsnd s))
  · intro s m h₁ h₂
    refine ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun x ↦ trivSqZeroExt_prod_ext M N ?_ ?_)
    · exact (congrArg (fun f ↦ f.hom x) h₁).trans (hfst s x).symm
    · exact (congrArg (fun f ↦ f.hom x) h₂).trans (hsnd s x).symm

private theorem elements_s2_pullback_bijective
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (F : ArtinianLocalAlgCat.{u, w, w} Λ k ⥤ Type u₁)
    {A B X P : ArtinianLocalAlgCat.{u, w, w} Λ k}
    {V : Type (w)} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (d : A ⟶ X) (e : B ⟶ X) (g : P ⟶ A) (h : P ⟶ B)
    (hPB : IsPullback h g e d)
    (hsq : IsSquareZeroProjection (V := V) e)
    (hcof : IsCofiberedInGroupoids (CategoryOfElements.π F))
    (hS2 : SchlessingerConditionS2 (CategoryOfElements.π F))
    (hcompat : ∀ x : F.obj A, ∀ y : F.obj B, F.map d x = F.map e y) :
    Function.Bijective (fun z : F.obj P ↦ (F.map g z, F.map h z)) := by
  classical
  let p := CategoryOfElements.π F
  let d' (x : F.obj A) : F.elementsMk A x ⟶ F.elementsMk X (F.map d x) :=
    CategoryOfElements.homMk _ _ d rfl
  let e' (x : F.obj A) (y : F.obj B) (hxy : F.map d x = F.map e y) :
      F.elementsMk B y ⟶ F.elementsMk X (F.map d x) := CategoryOfElements.homMk _ _ e hxy.symm
  constructor
  · intro x y hxy
    have hw : F.map d (F.map g x) = F.map e (F.map h x) := by
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, hPB.w]
    let comp (z : F.obj P) (hz : F.map g z = F.map g x) (hz' : F.map h z = F.map h x) :
        PullbackCompletion p (d' (F.map g x)) (e' _ _ hw) g h := by
      refine ⟨F.elementsMk P z, rfl, CategoryOfElements.homMk _ _ g hz,
        CategoryOfElements.homMk _ _ h hz', ?_, ?_, ?_⟩
      · apply CategoryOfElements.ext F
        exact hPB.w
      · simp [p, CategoryOfElements.π]
      · simp [p, CategoryOfElements.π]
    obtain ⟨b, -, hbase⟩ := schlessingerConditionS2_comparison_squareZero
      p hcof hS2 (d' _) (e' _ _ hw) hsq g h hPB (comp x rfl rfl)
      (comp y (congrArg Prod.fst hxy).symm (congrArg Prod.snd hxy).symm)
    have hh : F.map (p.map b) x = y := CategoryOfElements.map_snd b
    rw [hbase] at hh
    simpa [comp, p, CategoryOfElements.π, Functor.map_id_apply] using hh
  · rintro ⟨x, y⟩
    obtain ⟨Pcomp⟩ := schlessingerConditionS2_completion_squareZero
      p hcof hS2 (d' x) (e' x y (hcompat x y)) hsq g h hPB
    refine ⟨F.map (eqToHom Pcomp.apex_eq) Pcomp.apex.2, Prod.ext ?_ ?_⟩
    · have hm := CategoryOfElements.map_snd Pcomp.toFirst
      change F.map (p.map Pcomp.toFirst) Pcomp.apex.2 = x at hm
      rw [Pcomp.map_toFirst] at hm
      simpa [Functor.map_comp] using hm
    · have hm := CategoryOfElements.map_snd Pcomp.toSecond
      change F.map (p.map Pcomp.toSecond) Pcomp.apex.2 = y at hm
      rw [Pcomp.map_toSecond] at hm
      simpa [Functor.map_comp] using hm

private theorem associatedUnliftedClasses_subsingleton_on_special_fiber
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓕 : IsPredeformationCategory 𝓕.p) :
    Subsingleton ((isomorphismClasses 𝓕 h𝓕.cofibered).obj
      (residueFieldObject Λ k)) := by
  obtain ⟨h⟩ := isPredeformationFunctor_isomorphismClasses 𝓕 h𝓕
  exact ⟨fun x y ↦ (h.uniq x).trans (h.uniq y).symm⟩

private theorem associatedUnliftedClasses_nonempty_on_special_fiber
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓕 : IsPredeformationCategory 𝓕.p) :
    Nonempty ((isomorphismClasses 𝓕 h𝓕.cofibered).obj
      (residueFieldObject Λ k)) := by
  obtain ⟨h⟩ := isPredeformationFunctor_isomorphismClasses 𝓕 h𝓕
  exact ⟨h.default⟩

private noncomputable def associatedZeroAlgEquiv :
    associatedSquareZeroObject (Λ := Λ) (k := k) (zeroFGModule k) ≃ₐ[Λ]
      associatedResidueObject (Λ := Λ) (k := k) :=
  AlgEquiv.ofBijective
    (associatedSquareZeroProjection (Λ := Λ) (k := k) (zeroFGModule k)).hom
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
        let x : TrivSqZeroExt k (zeroFGModule k : Type (w)) :=
          TrivSqZeroExt.inl ((ULift.algEquiv.{u, w, w} (R := Λ) (A := k)) y)
        refine ⟨x, ?_⟩
        change ULift.up (TrivSqZeroExt.fst x) = y
        apply ULift.ext
        simp [x])

private noncomputable def associatedZeroIso :
    associatedSquareZeroObject (Λ := Λ) (k := k) (zeroFGModule k) ≅
      associatedResidueObject (Λ := Λ) (k := k) where
  hom := associatedSquareZeroProjection (Λ := Λ) (k := k) (zeroFGModule k)
  inv :=
    { hom := (associatedZeroAlgEquiv (Λ := Λ) (k := k)).symm.toAlgHom
      isLocal := by
        refine ⟨fun x hx => ?_⟩
        have h := RingHom.isUnit_map
          (associatedZeroAlgEquiv (Λ := Λ) (k := k)).toRingEquiv.toRingHom hx
        have heq : (associatedZeroAlgEquiv (Λ := Λ) (k := k)).toRingEquiv.toRingHom
            ((associatedZeroAlgEquiv (Λ := Λ) (k := k)).symm.toAlgHom.toRingHom x) = x :=
          (associatedZeroAlgEquiv (Λ := Λ) (k := k)).apply_symm_apply x
        rw [heq] at h
        exact h
      residue_comm := by
        intro x
        have h := (associatedSquareZeroProjection (Λ := Λ) (k := k)
          (zeroFGModule k)).residue_comm
            ((associatedZeroAlgEquiv (Λ := Λ) (k := k)).symm x) |>.symm
        have heq : (associatedSquareZeroProjection (Λ := Λ) (k := k)
            (zeroFGModule k)).hom
              ((associatedZeroAlgEquiv (Λ := Λ) (k := k)).symm x) = x :=
          (associatedZeroAlgEquiv (Λ := Λ) (k := k)).apply_symm_apply x
        rw [heq] at h
        exact h }
  hom_inv_id := by
    apply ArtinianLocalAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    exact (associatedZeroAlgEquiv (Λ := Λ) (k := k)).symm_apply_apply x
  inv_hom_id := by
    apply ArtinianLocalAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    exact (associatedZeroAlgEquiv (Λ := Λ) (k := k)).apply_symm_apply x

private theorem associatedUnliftedClasses_product_bijective
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓕 : IsPredeformationCategory 𝓕.p)
    (hS2 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered)))
    (M N : FGModuleCat.{w} k) :
    Function.Bijective (fun z : (isomorphismClasses 𝓕 h𝓕.cofibered).obj
        (associatedSquareZeroObject (Λ := Λ) (k := k) (prodFGModule k M N)) ↦
      ((isomorphismClasses 𝓕 h𝓕.cofibered).map
          (associatedSquareZeroProductFst (Λ := Λ) (k := k) M N) z,
       (isomorphismClasses 𝓕 h𝓕.cofibered).map
          (associatedSquareZeroProductSnd (Λ := Λ) (k := k) M N) z)) := by
  let H := isomorphismClasses 𝓕 h𝓕.cofibered
  have hb := elements_s2_pullback_bijective H
    (associatedSquareZeroProjection (Λ := Λ) (k := k) N)
    (associatedSquareZeroProjection (Λ := Λ) (k := k) M)
    (associatedSquareZeroProductSnd (Λ := Λ) (k := k) M N)
    (associatedSquareZeroProductFst (Λ := Λ) (k := k) M N)
    (associatedSquareZeroProduct_isPullback (Λ := Λ) (k := k) M N)
    (associatedSquareZeroProjection_isSquareZero (Λ := Λ) (k := k) M)
    ((isPredeformationCategory_iff H).mpr
      (isPredeformationFunctor_isomorphismClasses 𝓕 h𝓕)).cofibered
    hS2 (fun _ _ ↦ (associatedUnliftedClasses_subsingleton_on_special_fiber 𝓕 h𝓕).elim _ _)
  constructor
  · intro x y hxy
    apply hb.injective
    exact Prod.ext (congrArg Prod.snd hxy) (congrArg Prod.fst hxy)
  · intro xy
    rcases xy with ⟨x, y⟩
    obtain ⟨z, hz⟩ := hb.surjective (y, x)
    refine ⟨z, ?_⟩
    exact Prod.ext (congrArg Prod.snd hz) (congrArg Prod.fst hz)

/-- The three conditions of Stacks 06IA, in the unbundled form in which they are proved. -/
private theorem associatedTangentSpaceConditionsAux
    (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓕 : IsPredeformationCategory 𝓕.p)
    (hS2 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) :
    let L := squareZeroExtensionArtinian.{u, w, w} Λ k ⋙
      isomorphismClasses 𝓕 h𝓕.cofibered
    Nonempty (L.obj (zeroFGModule k)) ∧
      Subsingleton (L.obj (zeroFGModule k)) ∧
      ∀ M N, Function.Bijective (fun x : L.obj (prodFGModule k M N) ↦
        (L.map (prodFst k M N) x, L.map (prodSnd k M N) x)) := by
  let H := isomorphismClasses 𝓕 h𝓕.cofibered
  let K := associatedResidueObject (Λ := Λ) (k := k)
  let Z := associatedSquareZeroObject (Λ := Λ) (k := k) (zeroFGModule k)
  let i := associatedZeroIso (Λ := Λ) (k := k)
  obtain ⟨uK⟩ := associatedUnliftedClasses_nonempty_on_special_fiber 𝓕 h𝓕
  let : Subsingleton (H.obj K) := associatedUnliftedClasses_subsingleton_on_special_fiber 𝓕 h𝓕
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨H.map i.inv uK⟩
  · constructor
    intro x y
    have hinj : Function.Injective (H.map i.hom) := by
      intro a b hab
      have hh := congrArg (H.map i.inv) hab
      have hh' : H.map (i.hom ≫ i.inv) a = H.map (i.hom ≫ i.inv) b := by
        simpa only [Functor.map_comp_apply] using hh
      simpa only [Iso.hom_inv_id, Functor.map_id_apply] using hh'
    apply hinj
    exact Subsingleton.elim _ _
  · intro M N
    simpa [H, associatedSquareZeroProductFst, associatedSquareZeroProductSnd] using
      associatedUnliftedClasses_product_bijective 𝓕 h𝓕 hS2 M N

/-- **Stacks Project, Tag 06IH.** Schlessinger's condition (S2) for the associated functor
of a predeformation category supplies the singleton and binary-product conditions that the
natural module structure of Stacks 06IA requires. -/
@[stacks 06IH "tangent-space functor conditions"]
theorem associatedTangentSpaceFunctorConditions
    (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓕 : IsPredeformationCategory 𝓕.p)
    (hS2 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) :
    TangentSpaceFunctorConditions Λ k (artinianLocalOver Λ k)
      (squareZeroExtension_mem_artinianLocalOver Λ k)
      (artinianLocalOverToArtinian Λ k ⋙ isomorphismClasses 𝓕 h𝓕.cofibered) :=
  let h := associatedTangentSpaceConditionsAux 𝓕 h𝓕 hS2
  ⟨h.1, h.2.1, h.2.2⟩

end

/-! ### The vector-space structure on the tangent space

The linear lift of the associated square-zero functor, the identification of its carrier at
the rank-one module with the tangent space, and the additive and scalar structures that the
identification transports, are all built in
`StacksFrontier.Deformation.PredeformationTangent.TangentVectorSpace` as the carrier-universe
specialization of the lifted construction on `FGModuleCat.{max v w} k`. The two instances
there are the covering set of the *additive structure* and *scalar structure* parts of
Stacks 06IH; they are registered here because that module states the lifted form, which is
tagged under the *natural vector space structure* part:
`associatedTangentSpaceAddCommGroupUnlifted` is the additive group underlying the canonical
vector-space structure on the tangent space, and `associatedTangentSpaceModuleUnlifted` is
the canonical action of the residue field on it. -/

add_to_stacks 06IH "additive structure" associatedTangentSpaceAddCommGroupUnlifted

add_to_stacks 06IH "scalar structure" associatedTangentSpaceModuleUnlifted

end Deformation

end
