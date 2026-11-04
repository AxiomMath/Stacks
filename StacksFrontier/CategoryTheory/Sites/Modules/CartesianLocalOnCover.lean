module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.Algebra.Category.Ring.PushoutTensorComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction
public import StacksFrontier.RingTheory.Descent.PushoutBaseChange

/-!
# Being cartesian over a morphism is local on a finite flat cover of the target

Let `R` be a presheaf of commutative rings on a category `C` with pullbacks, `M` a presheaf of
modules over it, and `f : U ⟶ V` a morphism along which the ring map is flat.  Suppose `V` has a
finite family `W i ⟶ V` for which `M` satisfies the sheaf axiom — over `V` and over `U` — on
whose base changes to `U` the presheaf `M` is cartesian, and whose attached squares of rings are
pushouts.  Then `M` is cartesian over `f` itself.

## Main definitions

* `Stacks.PresheafOfModules.restrictionBaseChangeOfSquare`: the comparison
  `R U ⊗[R V] M W ⟶ M T` attached to a commuting square `T ⟶ U ⟶ V`, `T ⟶ W ⟶ V`.

## Main results

* `Stacks.PresheafOfModules.bijective_restrictionBaseChangeOfSquare`: that comparison is
  bijective when the ring square is a pushout and `M` is cartesian over `T ⟶ W`.
* `Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_cover`: **being cartesian over `f` is
  local on a finite flat cover of the target.**

## Implementation notes

The module structures over `R V` on the various groups of sections are given by restriction of
scalars along explicit ring maps rather than by a typeclass search, through the abbreviations
`moduleOfRingHom` and `algebraOfRingHom`; a square of the site then gives an
`R V`-linear comparison with no coherence conditions to check.  All the restriction maps of `M`
appearing in the descent data are the same function, packaged as `R V`-linear maps by
`restrictionLinear` and `restrictionLinearOf`, so each compatibility identity reduces to
functoriality of `M`.

The double overlaps of the cover are taken as fibre products in `C`, which is why `C` is assumed
to have pullbacks; the squares of rings they produce are not automatically pushouts, so that is
a hypothesis.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u v r m w

namespace Stacks.PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{r}}
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))

/-- The module structure on a group of sections obtained by restricting scalars along an explicit
ring homomorphism from a base ring. -/
noncomputable abbrev moduleOfRingHom {R₀ : CommRingCat.{r}} {X : C}
    (φ : R₀ ⟶ R.obj (.op X)) : Module R₀ (M.obj (.op X)) :=
  Module.compHom _ φ.hom

/-- The algebra structure on a ring of sections given by an explicit ring homomorphism from a
base ring. -/
noncomputable abbrev algebraOfRingHom {R₀ : CommRingCat.{r}} {X : C}
    (φ : R₀ ⟶ R.obj (.op X)) : Algebra R₀ (R.obj (.op X)) :=
  φ.hom.toAlgebra

/-- The comparison `R U ⊗[R V] M W ⟶ M T` attached to a commuting square with `U` and `W` over
`V` and `T` over both: it sends `b ⊗ₜ x` to `b` acting on the restriction of `x` to `T`. -/
noncomputable def restrictionBaseChangeOfSquare
    {V U W T : C} (f : U ⟶ V) (gw : W ⟶ V) (qt : T ⟶ U) (pt : T ⟶ W)
    (hcomm : R.map f.op ≫ R.map qt.op = R.map gw.op ≫ R.map pt.op) :
    letI := algebraOfRingHom (R := R) (R.map f.op)
    letI := moduleOfRingHom M (R.map gw.op)
    letI := moduleOfRingHom M (R.map f.op ≫ R.map qt.op)
    (R.obj (.op U)) ⊗[R.obj (.op V)] (M.obj (.op W)) →ₗ[R.obj (.op V)] M.obj (.op T) := by
  letI := algebraOfRingHom (R := R) (R.map f.op)
  letI := moduleOfRingHom M (R.map gw.op)
  letI := moduleOfRingHom M (R.map f.op ≫ R.map qt.op)
  refine TensorProduct.lift ?_
  refine
    { toFun := fun b =>
        { toFun := fun x => (R.map qt.op).hom b • (M.map pt.op x : M.obj (.op T))
          map_add' := ?_
          map_smul' := ?_ }
      map_add' := ?_
      map_smul' := ?_ }
  · intro x y
    change (R.map qt.op).hom b • (M.map pt.op (x + y) : M.obj (.op T)) =
      (R.map qt.op).hom b • (M.map pt.op x : M.obj (.op T)) +
        (R.map qt.op).hom b • (M.map pt.op y : M.obj (.op T))
    rw [map_add (M.map pt.op).hom x y, smul_add]
  · intro c x
    change (R.map qt.op).hom b • (M.map pt.op ((R.map gw.op).hom c • x) : M.obj (.op T)) =
      (R.map f.op ≫ R.map qt.op).hom c • ((R.map qt.op).hom b • (M.map pt.op x : M.obj (.op T)))
    rw [M.map_smul, smul_smul, smul_smul]
    congr 1
    change (R.map qt.op).hom b * ((R.map gw.op) ≫ (R.map pt.op)).hom c =
      (R.map f.op ≫ R.map qt.op).hom c * (R.map qt.op).hom b
    rw [hcomm, mul_comm]
  · intro b b'
    refine LinearMap.ext (fun x => ?_)
    change (R.map qt.op).hom (b + b') • (M.map pt.op x : M.obj (.op T)) =
      (R.map qt.op).hom b • (M.map pt.op x : M.obj (.op T)) +
        (R.map qt.op).hom b' • (M.map pt.op x : M.obj (.op T))
    rw [map_add, add_smul]
  · intro c b
    refine LinearMap.ext (fun x => ?_)
    change (R.map qt.op).hom ((R.map f.op).hom c * b) • (M.map pt.op x : M.obj (.op T)) =
      (R.map f.op ≫ R.map qt.op).hom c •
        ((R.map qt.op).hom b • (M.map pt.op x : M.obj (.op T)))
    rw [map_mul, mul_smul]
    rfl

/-- `Stacks.PresheafOfModules.restrictionBaseChangeOfSquare` on a pure tensor. -/
@[simp] theorem restrictionBaseChangeOfSquare_tmul
    {V U W T : C} (f : U ⟶ V) (gw : W ⟶ V) (qt : T ⟶ U) (pt : T ⟶ W)
    (hcomm : R.map f.op ≫ R.map qt.op = R.map gw.op ≫ R.map pt.op)
    (b : R.obj (.op U)) (x : M.obj (.op W)) :
    letI := algebraOfRingHom (R := R) (R.map f.op)
    letI := moduleOfRingHom M (R.map gw.op)
    letI := moduleOfRingHom M (R.map f.op ≫ R.map qt.op)
    restrictionBaseChangeOfSquare M f gw qt pt hcomm (b ⊗ₜ x) =
      (R.map qt.op).hom b • (M.map pt.op x : M.obj (.op T)) := rfl

/-- `Stacks.PresheafOfModules.restrictionBaseChangeOfSquare` is bijective when the square of rings
is a pushout and `M` is cartesian over `T ⟶ W`. -/
theorem bijective_restrictionBaseChangeOfSquare
    {V U W T : C} (f : U ⟶ V) (gw : W ⟶ V) (qt : T ⟶ U) (pt : T ⟶ W)
    (hcomm : R.map f.op ≫ R.map qt.op = R.map gw.op ≫ R.map pt.op)
    (hpo : IsPushout (R.map f.op) (R.map gw.op) (R.map qt.op) (R.map pt.op))
    (hiso : IsIso (restrictionBaseChange M pt.op)) :
    letI := algebraOfRingHom (R := R) (R.map f.op)
    letI := moduleOfRingHom M (R.map gw.op)
    letI := moduleOfRingHom M (R.map f.op ≫ R.map qt.op)
    Function.Bijective (restrictionBaseChangeOfSquare M f gw qt pt hcomm) := by
  let algB := algebraOfRingHom (R := R) (R.map f.op)
  let algA := algebraOfRingHom (R := R) (R.map gw.op)
  let algD := algebraOfRingHom (R := R) (R.map f.op ≫ R.map qt.op)
  let algAD : Algebra (R.obj (.op W)) (R.obj (.op T)) := (R.map pt.op).hom.toAlgebra
  let algBD : Algebra (R.obj (.op U)) (R.obj (.op T)) := (R.map qt.op).hom.toAlgebra
  let modW := moduleOfRingHom M (R.map gw.op)
  let modT := moduleOfRingHom M (R.map f.op ≫ R.map qt.op)
  let : IsScalarTower (R.obj (.op V)) (R.obj (.op W)) (R.obj (.op T)) := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    show (R.map f.op ≫ R.map qt.op).hom x = ((R.map gw.op) ≫ (R.map pt.op)).hom x
    rw [hcomm]
  let : IsScalarTower (R.obj (.op V)) (R.obj (.op U)) (R.obj (.op T)) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower (R.obj (.op V)) (R.obj (.op W)) (M.obj (.op W)) :=
    ⟨fun x y z => mul_smul _ _ _⟩
  let : IsScalarTower (R.obj (.op V)) (R.obj (.op T)) (M.obj (.op T)) :=
    ⟨fun x y z => mul_smul _ _ _⟩
  let e : (R.obj (.op W)) ⊗[R.obj (.op V)] (R.obj (.op U)) ≃ₗ[R.obj (.op V)] R.obj (.op T) :=
    (TensorProduct.comm _ _ _).trans
      (CommRingCat.pushoutTensorLinearEquiv _ _ _ _ (R.map f.op) (R.map gw.op) (R.map qt.op)
        (R.map pt.op) hpo)
  have he : ∀ (a : R.obj (.op W)) (b : R.obj (.op U)),
      e (a ⊗ₜ b) = algebraMap (R.obj (.op W)) (R.obj (.op T)) a *
        algebraMap (R.obj (.op U)) (R.obj (.op T)) b := by
    intro a b
    show CommRingCat.pushoutTensorLinearEquiv _ _ _ _ (R.map f.op) (R.map gw.op) (R.map qt.op)
      (R.map pt.op) hpo (b ⊗ₜ a) = _
    rw [CommRingCat.pushoutTensorLinearEquiv_tmul]
    exact mul_comm _ _
  let κ : (R.obj (.op T)) ⊗[R.obj (.op W)] (M.obj (.op W)) →ₗ[R.obj (.op T)]
      M.obj (.op T) := (restrictionBaseChange M pt.op).hom
  have hκ : Function.Bijective κ :=
    ConcreteCategory.bijective_of_isIso (restrictionBaseChange M pt.op)
  refine Module.Descent.bijective_pushout_comparison e he κ hκ
    (restrictionBaseChangeOfSquare M f gw qt pt hcomm) ?_
  intro b x
  have h1 : κ ((1 : R.obj (.op T)) ⊗ₜ x) = M.map pt.op x :=
    restrictionBaseChange_one_tmul M pt.op x
  rw [restrictionBaseChangeOfSquare_tmul, h1]
  rfl

/-- Restriction from the base object, as a linear map over its ring of sections. -/
noncomputable def restrictionLinear {V X : C} (a : X ⟶ V) :
    letI := moduleOfRingHom M (R.map a.op)
    M.obj (.op V) →ₗ[R.obj (.op V)] M.obj (.op X) :=
  let := moduleOfRingHom M (R.map a.op)
  { toFun := fun x => M.map a.op x
    map_add' := fun x y => map_add (M.map a.op).hom x y
    map_smul' := fun c x => M.map_smul a.op c x }

/-- `Stacks.PresheafOfModules.restrictionLinear` acts by restriction of sections. -/
@[simp] theorem restrictionLinear_apply {V X : C} (a : X ⟶ V) (x : M.obj (.op V)) :
    letI := moduleOfRingHom M (R.map a.op)
    restrictionLinear M a x = M.map a.op x := rfl

/-- Restriction between two objects, each with a specified ring map from a base ring, as a linear
map over that base ring. -/
noncomputable def restrictionLinearOf {V X Y : C} (φX : R.obj (.op V) ⟶ R.obj (.op X))
    (φY : R.obj (.op V) ⟶ R.obj (.op Y)) (a : X ⟶ Y) (hφ : φX = φY ≫ R.map a.op) :
    letI := moduleOfRingHom M φX
    letI := moduleOfRingHom M φY
    M.obj (.op Y) →ₗ[R.obj (.op V)] M.obj (.op X) :=
  let := moduleOfRingHom M φX
  let := moduleOfRingHom M φY
  { toFun := fun x => M.map a.op x
    map_add' := fun x y => map_add (M.map a.op).hom x y
    map_smul' := fun c x => by
      change M.map a.op (φY.hom c • x) = φX.hom c • M.map a.op x
      rw [M.map_smul]
      congr 1
      change (φY ≫ R.map a.op).hom c = φX.hom c
      rw [hφ] }

/-- `Stacks.PresheafOfModules.restrictionLinearOf` acts by restriction of sections. -/
@[simp] theorem restrictionLinearOf_apply {V X Y : C}
    (φX : R.obj (.op V) ⟶ R.obj (.op X))
    (φY : R.obj (.op V) ⟶ R.obj (.op Y)) (a : X ⟶ Y) (hφ : φX = φY ≫ R.map a.op)
    (x : M.obj (.op Y)) :
    letI := moduleOfRingHom M φX
    letI := moduleOfRingHom M φY
    restrictionLinearOf M φX φY a hφ x = M.map a.op x := rfl

/-- **Being cartesian over `f` is local on a finite flat cover of the target.**  The base-change
comparison along `f : U ⟶ V` is an isomorphism as soon as the ring map along `f` is flat, `M`
satisfies the sheaf axiom for a finite family `W i ⟶ V` and for its base change to `U`, the
attached squares of rings are pushouts, and `M` is cartesian over the projections of those base
changes. -/
theorem isIso_restrictionBaseChange_of_cover
    [HasPullbacks C] {U V : C} (f : U ⟶ V)
    {I : Type w} [Finite I]
    (W : I → C) (g : ∀ i, W i ⟶ V)
    (hflat : (R.map f.op).hom.Flat)
    (hsfV : Presieve.IsSheafFor (M.presheaf ⋙ forget AddCommGrpCat) (Presieve.ofArrows W g))
    (hsfU : Presieve.IsSheafFor (M.presheaf ⋙ forget AddCommGrpCat)
      (Presieve.ofArrows (fun i => pullback f (g i)) (fun i => pullback.fst f (g i))))
    (hpo : ∀ i, IsPushout (R.map f.op) (R.map (g i).op)
      (R.map (pullback.fst f (g i)).op) (R.map (pullback.snd f (g i)).op))
    (hpo' : ∀ c : I × I,
      IsPushout (R.map f.op) (R.map (pullback.fst (g c.1) (g c.2) ≫ g c.1).op)
        (R.map (pullback.fst f (pullback.fst (g c.1) (g c.2) ≫ g c.1)).op)
        (R.map (pullback.snd f (pullback.fst (g c.1) (g c.2) ≫ g c.1)).op))
    (hcart : ∀ i, IsIso (restrictionBaseChange M (pullback.snd f (g i)).op))
    (hcart' : ∀ c : I × I, IsIso (restrictionBaseChange M
      (pullback.snd f (pullback.fst (g c.1) (g c.2) ≫ g c.1)).op)) :
    IsIso (restrictionBaseChange M f.op) := by
  let algB := algebraOfRingHom (R := R) (R.map f.op)
  let : Module.Flat (R.obj (.op V)) (R.obj (.op U)) := hflat
  let T : I → C := fun i => pullback f (g i)
  let q : ∀ i, T i ⟶ U := fun i => pullback.fst f (g i)
  let pr : ∀ i, T i ⟶ W i := fun i => pullback.snd f (g i)
  let w1 : ∀ c : I × I, pullback (g c.1) (g c.2) ⟶ W c.1 := fun c => pullback.fst (g c.1) (g c.2)
  let w2 : ∀ c : I × I, pullback (g c.1) (g c.2) ⟶ W c.2 := fun c => pullback.snd (g c.1) (g c.2)
  let Wp : I × I → C := fun c => pullback (g c.1) (g c.2)
  let gp : ∀ c : I × I, Wp c ⟶ V := fun c => w1 c ≫ g c.1
  let Tp : I × I → C := fun c => pullback f (gp c)
  let qp : ∀ c : I × I, Tp c ⟶ U := fun c => pullback.fst f (gp c)
  let pp : ∀ c : I × I, Tp c ⟶ Wp c := fun c => pullback.snd f (gp c)
  have hw : ∀ c : I × I, w1 c ≫ g c.1 = w2 c ≫ g c.2 := fun c => pullback.condition
  let mc : ∀ c : I × I, Tp c ⟶ T c.1 := fun c =>
    pullback.lift (qp c) (pp c ≫ w1 c) (by rw [Category.assoc]; exact pullback.condition)
  let mc' : ∀ c : I × I, Tp c ⟶ T c.2 := fun c =>
    pullback.lift (qp c) (pp c ≫ w2 c)
      (by rw [Category.assoc, ← hw c]; exact pullback.condition)
  have hmc1 : ∀ c : I × I, mc c ≫ q c.1 = qp c := fun c => pullback.lift_fst _ _ _
  have hmc2 : ∀ c : I × I, mc c ≫ pr c.1 = pp c ≫ w1 c := fun c => pullback.lift_snd _ _ _
  have hmc1' : ∀ c : I × I, mc' c ≫ q c.2 = qp c := fun c => pullback.lift_fst _ _ _
  have hmc2' : ∀ c : I × I, mc' c ≫ pr c.2 = pp c ≫ w2 c := fun c => pullback.lift_snd _ _ _
  let instMi : ∀ i, Module (R.obj (.op V)) (M.obj (.op (W i))) :=
    fun i => moduleOfRingHom M (R.map (g i).op)
  let instMp : ∀ c : I × I, Module (R.obj (.op V)) (M.obj (.op (Wp c))) :=
    fun c => moduleOfRingHom M (R.map (gp c).op)
  let instMUi : ∀ i, Module (R.obj (.op V)) (M.obj (.op (T i))) :=
    fun i => moduleOfRingHom M (R.map f.op ≫ R.map (q i).op)
  let instMUp : ∀ c : I × I, Module (R.obj (.op V)) (M.obj (.op (Tp c))) :=
    fun c => moduleOfRingHom M (R.map f.op ≫ R.map (qp c).op)
  let instMU : Module (R.obj (.op V)) (M.obj (.op U)) := moduleOfRingHom M (R.map f.op)
  let towU : IsScalarTower (R.obj (.op V)) (R.obj (.op U)) (M.obj (.op U)) :=
    ⟨fun x y z => mul_smul _ _ _⟩
  let ε : M.obj (.op V) →ₗ[R.obj (.op V)] ∀ i, M.obj (.op (W i)) :=
    LinearMap.pi (fun i => restrictionLinear M (g i))
  let εU : M.obj (.op U) →ₗ[R.obj (.op V)] ∀ i, M.obj (.op (T i)) :=
    LinearMap.pi (fun i =>
      restrictionLinearOf M (R.map f.op ≫ R.map (q i).op) (R.map f.op) (q i) rfl)
  let δ : ∀ c : I × I, M.obj (.op (W c.1)) →ₗ[R.obj (.op V)] M.obj (.op (Wp c)) := fun c =>
    restrictionLinearOf M (R.map (gp c).op) (R.map (g c.1).op) (w1 c) (by
      show R.map ((w1 c ≫ g c.1)).op = _
      rw [op_comp, R.map_comp])
  let δ' : ∀ c : I × I, M.obj (.op (W c.2)) →ₗ[R.obj (.op V)] M.obj (.op (Wp c)) := fun c =>
    restrictionLinearOf M (R.map (gp c).op) (R.map (g c.2).op) (w2 c) (by
      show R.map ((w1 c ≫ g c.1)).op = _
      rw [hw c, op_comp, R.map_comp])
  let ρ : ∀ c : I × I, M.obj (.op (T c.1)) →ₗ[R.obj (.op V)] M.obj (.op (Tp c)) := fun c =>
    restrictionLinearOf M (R.map f.op ≫ R.map (qp c).op)
      (R.map f.op ≫ R.map (q c.1).op) (mc c) (by
        rw [Category.assoc]
        congr 1
        rw [← R.map_comp, ← op_comp, hmc1 c])
  let ρ' : ∀ c : I × I, M.obj (.op (T c.2)) →ₗ[R.obj (.op V)] M.obj (.op (Tp c)) := fun c =>
    restrictionLinearOf M (R.map f.op ≫ R.map (qp c).op)
      (R.map f.op ≫ R.map (q c.2).op) (mc' c) (by
        rw [Category.assoc]
        congr 1
        rw [← R.map_comp, ← op_comp, hmc1' c])
  let Φ : (∀ i, M.obj (.op (W i))) →ₗ[R.obj (.op V)] (∀ c : I × I, M.obj (.op (Wp c))) :=
    LinearMap.pi (fun c => δ c ∘ₗ LinearMap.proj c.1 - δ' c ∘ₗ LinearMap.proj c.2)
  let ψ : ∀ i, (R.obj (.op U)) ⊗[R.obj (.op V)] (M.obj (.op (W i)))
      ≃ₗ[R.obj (.op V)] M.obj (.op (T i)) := fun i =>
    LinearEquiv.ofBijective (restrictionBaseChangeOfSquare M f (g i) (q i) (pr i) (hpo i).w)
      (bijective_restrictionBaseChangeOfSquare M f (g i) (q i) (pr i) (hpo i).w
        (hpo i) (hcart i))
  let ψ' : ∀ c : I × I, (R.obj (.op U)) ⊗[R.obj (.op V)] (M.obj (.op (Wp c)))
      ≃ₗ[R.obj (.op V)] M.obj (.op (Tp c)) := fun c =>
    LinearEquiv.ofBijective (restrictionBaseChangeOfSquare M f (gp c) (qp c) (pp c) (hpo' c).w)
      (bijective_restrictionBaseChangeOfSquare M f (gp c) (qp c) (pp c) (hpo' c).w
        (hpo' c) (hcart' c))
  let θ : (R.obj (.op U)) ⊗[R.obj (.op V)] (M.obj (.op V)) →ₗ[R.obj (.op V)] M.obj (.op U) :=
    { toFun := fun z => restrictionBaseChange M f.op z
      map_add' := fun z z' => map_add (restrictionBaseChange M f.op).hom z z'
      map_smul' := fun c z => by
        have h := (restrictionBaseChange M f.op).hom.map_smul
          (algebraMap (R.obj (.op V)) (R.obj (.op U)) c) z
        rwa [algebraMap_smul] at h }
  have hV := (Presieve.isSheafFor_arrows_iff_pullbacks _ _).mp hsfV
  have hU := (Presieve.isSheafFor_arrows_iff_pullbacks _ _).mp hsfU
  have hbij : Function.Bijective θ := by
    refine Module.Descent.bijective_of_flat_descent ε ?_ δ δ' Φ ?_ ?_ εU ?_ ρ ρ' ?_ ψ ψ' ?_ ?_
      θ ?_
    · intro x y hxy
      have hcompat : Presieve.Arrows.PullbackCompatible
          (M.presheaf ⋙ forget AddCommGrpCat) g (fun i => M.map (g i).op x) := by
        intro i j
        show M.map (pullback.fst (g i) (g j)).op (M.map (g i).op x) =
          M.map (pullback.snd (g i) (g j)).op (M.map (g j).op x)
        rw [← M.map_comp_apply, ← M.map_comp_apply, ← op_comp, ← op_comp, pullback.condition]
      obtain ⟨t, -, huniq⟩ := hV _ hcompat
      exact (huniq x fun _ => rfl).trans (huniq y fun i => (congrFun hxy i).symm).symm
    · exact fun _ _ => rfl
    · intro mm
      constructor
      · intro h0
        have hcompat : Presieve.Arrows.PullbackCompatible
            (M.presheaf ⋙ forget AddCommGrpCat) g mm := by
          intro i j
          have h : δ (i, j) (mm i) - δ' (i, j) (mm j) = 0 := congrFun h0 (i, j)
          exact sub_eq_zero.mp h
        obtain ⟨t, ht, _⟩ := hV _ hcompat
        exact ⟨t, funext ht⟩
      · rintro ⟨t, rfl⟩
        funext c
        have e1 : (δ c (ε t c.1) : M.obj (.op (Wp c))) = M.map ((w1 c ≫ g c.1)).op t := by
          show (M.map (w1 c).op (M.map (g c.1).op t) : M.obj (.op (Wp c))) = _
          rw [← M.map_comp_apply, ← op_comp]
        have e2 : (δ' c (ε t c.2) : M.obj (.op (Wp c))) = M.map ((w2 c ≫ g c.2)).op t := by
          show (M.map (w2 c).op (M.map (g c.2).op t) : M.obj (.op (Wp c))) = _
          rw [← M.map_comp_apply, ← op_comp]
        show δ c (ε t c.1) - δ' c (ε t c.2) = 0
        rw [e1, e2, hw c]
        exact sub_self _
    · intro x y hxy
      have hcompat : Presieve.Arrows.PullbackCompatible
          (M.presheaf ⋙ forget AddCommGrpCat) (fun i => pullback.fst f (g i))
          (fun i => M.map (q i).op x) := by
        intro i j
        show M.map (pullback.fst (q i) (q j)).op (M.map (q i).op x) =
          M.map (pullback.snd (q i) (q j)).op (M.map (q j).op x)
        rw [← M.map_comp_apply, ← M.map_comp_apply, ← op_comp, ← op_comp, pullback.condition]
      obtain ⟨t, -, huniq⟩ := hU _ hcompat
      exact (huniq x fun _ => rfl).trans (huniq y fun i => (congrFun hxy i).symm).symm
    · intro t c
      show M.map (mc c).op (M.map (q c.1).op t) = M.map (mc' c).op (M.map (q c.2).op t)
      rw [← M.map_comp_apply, ← M.map_comp_apply, ← op_comp, ← op_comp, hmc1 c, hmc1' c]
    · intro c b x
      have hm : (M.map (mc c).op (M.map (pr c.1).op x) : M.obj (.op (Tp c)))
          = M.map (pp c).op (M.map (w1 c).op x) := by
        rw [← M.map_comp_apply, ← M.map_comp_apply, ← op_comp, ← op_comp, hmc2 c]
      have hsc : ((R ⋙ forget₂ CommRingCat RingCat).map (mc c).op) ((R.map (q c.1).op).hom b)
          = (R.map (qp c).op).hom b := by
        show ((R.map (q c.1).op) ≫ (R.map (mc c).op)).hom b = (R.map (qp c).op).hom b
        rw [← R.map_comp, ← op_comp, hmc1 c]
      have key : ((R ⋙ forget₂ CommRingCat RingCat).map (mc c).op) ((R.map (q c.1).op).hom b) •
            (M.map (mc c).op (M.map (pr c.1).op x) : M.obj (.op (Tp c)))
          = (R.map (qp c).op).hom b •
            (M.map (pp c).op (M.map (w1 c).op x) : M.obj (.op (Tp c))) := by
        rw [hsc, hm]
        rfl
      exact key.symm.trans (M.map_smul (mc c).op _ _).symm
    · intro c b y
      have hm : (M.map (mc' c).op (M.map (pr c.2).op y) : M.obj (.op (Tp c)))
          = M.map (pp c).op (M.map (w2 c).op y) := by
        rw [← M.map_comp_apply, ← M.map_comp_apply, ← op_comp, ← op_comp, hmc2' c]
      have hsc : ((R ⋙ forget₂ CommRingCat RingCat).map (mc' c).op) ((R.map (q c.2).op).hom b)
          = (R.map (qp c).op).hom b := by
        show ((R.map (q c.2).op) ≫ (R.map (mc' c).op)).hom b = (R.map (qp c).op).hom b
        rw [← R.map_comp, ← op_comp, hmc1' c]
      have key : ((R ⋙ forget₂ CommRingCat RingCat).map (mc' c).op) ((R.map (q c.2).op).hom b) •
            (M.map (mc' c).op (M.map (pr c.2).op y) : M.obj (.op (Tp c)))
          = (R.map (qp c).op).hom b •
            (M.map (pp c).op (M.map (w2 c).op y) : M.obj (.op (Tp c))) := by
        rw [hsc, hm]
        rfl
      exact key.symm.trans (M.map_smul (mc' c).op _ _).symm
    · intro b n i
      have hθt : (θ (b ⊗ₜ n) : M.obj (.op U)) = b • (M.map f.op n : M.obj (.op U)) :=
        restrictionBaseChange_tmul M f.op b n
      have hmv : (M.map (q i).op (M.map f.op n) : M.obj (.op (T i)))
          = M.map (pr i).op (M.map (g i).op n) := by
        rw [← M.map_comp_apply, ← M.map_comp_apply, ← op_comp, ← op_comp, pullback.condition]
      have key : ((R ⋙ forget₂ CommRingCat RingCat).map (q i).op) b •
            (M.map (q i).op (M.map f.op n) : M.obj (.op (T i)))
          = (R.map (q i).op).hom b •
            (M.map (pr i).op (M.map (g i).op n) : M.obj (.op (T i))) := by
        rw [hmv]
        rfl
      exact ((congrArg (fun z => (M.map (q i).op z : M.obj (.op (T i)))) hθt).trans
        (M.map_smul (q i).op b (M.map f.op n))).trans key
  rwa [ConcreteCategory.isIso_iff_bijective]

end Stacks.PresheafOfModules

end
