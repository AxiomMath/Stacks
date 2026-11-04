module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicFiniteEtaleDirectImageRealizable
public import StacksFrontier.FieldTheory.SeparableTensorSplitting

/-!
# The trace formula for the direct image along a finite étale morphism

Let `π : X ⟶ Y` be a finite étale morphism of schemes over a finite field, `F` an ℓ-adic sheaf on
`X` with levels locally constant of finite type, and `y` a point of `Y` with finite residue field.
For `n ≥ 1`,

  `Tr(π_y ^ n | (π_* F)_ȳ ⊗ ℚ_ℓ) = ∑_{x ↦ y, d_x ∣ n} d_x · Tr(π_x ^ (n / d_x) | F_x̄ ⊗ ℚ_ℓ)`,

the sum over the points `x` of `X` over `y`, with `d_x = [κ(x) : κ(y)]`. The lifts of the
geometric point `ȳ` over `x` are the `κ(y)`-embeddings `κ(x) → κ(y)‾`, of which there are `d_x`
(`κ(x)/κ(y)` is a finite extension of finite fields); a lift is fixed by `π_y ^ n` exactly when its
embedding lands in the fixed field of `π_y ^ n`, that is when `d_x ∣ n`; and at a fixed lift the
diagonal block of `π_y ^ n` has the trace of `π_x ^ (n / d_x)`, as
`#κ(x) ^ (n / d_x) = #κ(y) ^ n`. The trace of `π_y ^ n` is the sum of the diagonal blocks over the
fixed lifts (`Stacks.EtaleCohomology.LAdicSheaf.trace_rationalStalkFrobenius_directImage_pow`).

## Main definitions

* `Stacks.EtaleCohomology.liftResidueDegree`: `[κ(x) : κ(π x)]`.

## Main results

* `Stacks.EtaleCohomology.natCard_geometricLifts_over`: there are `[κ(x) : κ(y)]` lifts over `x`.
* `Stacks.EtaleCohomology.geometricLiftsPerm_pow_fixed_iff`: the fixed lifts.
* `Stacks.EtaleCohomology.LAdicSheaf.trace_rationalStalkFrobenius_directImage_pow_eq_sum`: the
  trace formula.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

/-- The degree `[κ(x) : κ(g(x))]` of the residue field extension at a point. -/
public def liftResidueDegree {X Y : Scheme.{u}} (g : X ⟶ Y) (x : X) : ℕ :=
  letI : Algebra (Y.residueField (g.base x)) (X.residueField x) :=
    (g.residueFieldMap x).hom.toAlgebra
  Module.finrank (Y.residueField (g.base x)) (X.residueField x)

section Lifts

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (π : X ⟶ Y)

/-- The morphism `Spec κ(y)‾ ⟶ X` determined by `τ : κ(x) ⟶ κ(y)‾` lies over the geometric point
at `y = π(x)` exactly when `τ` is a `κ(y)`-embedding. -/
theorem fromSpecResidueField_comp_eq_geometricPointAt_iff (x : X.1)
    (τ : X.1.residueField x ⟶
      CommRingCat.of (AlgebraicClosure (Y.1.residueField ((B.inclusion.map π).base x)))) :
    (Spec.map τ ≫ X.1.fromSpecResidueField x) ≫ B.inclusion.map π =
        (geometricPointAt Y.1 ((B.inclusion.map π).base x)).hom ↔
      (B.inclusion.map π).residueFieldMap x ≫ τ =
        CommRingCat.ofHom (algebraMap (Y.1.residueField ((B.inclusion.map π).base x))
          (AlgebraicClosure (Y.1.residueField ((B.inclusion.map π).base x)))) := by
  have key : (Spec.map τ ≫ X.1.fromSpecResidueField x) ≫ B.inclusion.map π =
      Spec.map ((B.inclusion.map π).residueFieldMap x ≫ τ) ≫
        Y.1.fromSpecResidueField ((B.inclusion.map π).base x) := by
    rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, Spec.map_comp,
      Category.assoc]
    rfl
  rw [key]
  show _ = (Scheme.SpecToEquivOfField _ Y.1).symm
      ⟨_, CommRingCat.ofHom (algebraMap (Y.1.residueField ((B.inclusion.map π).base x))
        (AlgebraicClosure (Y.1.residueField ((B.inclusion.map π).base x))))⟩ ↔ _
  rw [show Spec.map ((B.inclusion.map π).residueFieldMap x ≫ τ) ≫
      Y.1.fromSpecResidueField ((B.inclusion.map π).base x) =
      (Scheme.SpecToEquivOfField _ Y.1).symm ⟨_, (B.inclusion.map π).residueFieldMap x ≫ τ⟩
      from rfl, Equiv.apply_eq_iff_eq]
  exact ⟨fun h => eq_of_heq (Sigma.mk.inj h).2, fun h => congrArg (Sigma.mk _) h⟩

/-- The residue field extension `κ(π x) → κ(x)` at a point of a finite étale morphism is finite. -/
private theorem finite_residueFieldMap_hom (x : X.1)
    [AlgebraicGeometry.Etale (B.inclusion.map π)] :
    ((B.inclusion.map π).residueFieldMap x).hom.Finite := by
  let g := B.inclusion.map π
  let mres := (g.residueFieldMap x).hom
  dsimp at mres
  algebraize [mres]
  have hm : mres.QuasiFinite := by
    apply RingHom.QuasiFinite.of_comp (g := (Y.1.residue (g.base x)).hom)
    rw [← CommRingCat.hom_comp, Scheme.residue_residueFieldMap]
    exact (RingHom.QuasiFinite.of_finite (RingHom.Finite.of_surjective _
      IsLocalRing.residue_surjective)).comp (g.quasiFiniteAt x)
  have : Algebra.QuasiFinite (Y.1.residueField (g.base x)) (X.1.residueField x) := hm
  have : Module.Finite (Y.1.residueField (g.base x)) (X.1.residueField x) := .of_quasiFinite
  exact RingHom.finite_algebraMap.2 this

variable [IsFinite (B.inclusion.map π)]

/-- **The lifts over `x` of the geometric point at `π(x)` are the `κ(π x)`-embeddings of
`κ(x)` into `κ(π x)‾`.** -/
def geometricLiftsOverEquiv (x : X.1) :
    letI : Algebra (Y.1.residueField ((B.inclusion.map π).base x)) (X.1.residueField x) :=
      ((B.inclusion.map π).residueFieldMap x).hom.toAlgebra
    (X.1.residueField x →ₐ[Y.1.residueField ((B.inclusion.map π).base x)]
        AlgebraicClosure (Y.1.residueField ((B.inclusion.map π).base x))) ≃
      {l : GeometricLifts B π (geometricPointAt Y.1 ((B.inclusion.map π).base x)) //
        geometricLiftPoint B π _ l = x} := by
  letI : Algebra (Y.1.residueField ((B.inclusion.map π).base x)) (X.1.residueField x) :=
    ((B.inclusion.map π).residueFieldMap x).hom.toAlgebra
  let e := Scheme.SpecToEquivOfField
    (AlgebraicClosure (Y.1.residueField ((B.inclusion.map π).base x))) X.1
  have hc : ∀ φ : X.1.residueField x →ₐ[Y.1.residueField ((B.inclusion.map π).base x)]
      AlgebraicClosure (Y.1.residueField ((B.inclusion.map π).base x)),
      (B.inclusion.map π).residueFieldMap x ≫ CommRingCat.ofHom φ.toRingHom =
        CommRingCat.ofHom (algebraMap (Y.1.residueField ((B.inclusion.map π).base x))
          (AlgebraicClosure (Y.1.residueField ((B.inclusion.map π).base x)))) := fun φ => by
    ext c
    exact φ.commutes c
  refine Equiv.ofBijective (fun φ => ⟨⟨e.symm ⟨x, CommRingCat.ofHom φ.toRingHom⟩,
      (fromSpecResidueField_comp_eq_geometricPointAt_iff B π x _).2 (hc φ)⟩, ?_⟩) ⟨?_, ?_⟩
  · change (e (e.symm ⟨x, _⟩)).1 = x
    rw [Equiv.apply_symm_apply]
  · intro φ ψ h
    have h1 := congrArg (fun l => e l.1.1) h
    simp only [Equiv.apply_symm_apply] at h1
    have h2 := eq_of_heq (Sigma.mk.inj h1).2
    ext c
    exact congrArg (fun τ => τ.hom c) h2
  · rintro ⟨l, hl⟩
    obtain ⟨⟨x', τ⟩, hx⟩ : ∃ s, e.symm s = l.1 := ⟨_, e.symm_apply_apply _⟩
    have hx' : x' = x := by
      rw [← hl]
      change x' = (e l.1).1
      rw [← hx, Equiv.apply_symm_apply]
    subst hx'
    have hτ : (B.inclusion.map π).residueFieldMap x' ≫ τ =
        CommRingCat.ofHom (algebraMap (Y.1.residueField ((B.inclusion.map π).base x'))
          (AlgebraicClosure (Y.1.residueField ((B.inclusion.map π).base x')))) :=
      (fromSpecResidueField_comp_eq_geometricPointAt_iff B π x' τ).1 (by
        rw [show Spec.map τ ≫ X.1.fromSpecResidueField x' = e.symm ⟨x', τ⟩ from rfl, hx]
        exact l.2)
    refine ⟨{ toRingHom := τ.hom, commutes' := fun c => congrArg (fun t => t.hom c) hτ }, ?_⟩
    refine Subtype.ext (Subtype.ext ?_)
    exact hx

variable [AlgebraicGeometry.Etale (B.inclusion.map π)]

omit [IsFinite (B.inclusion.map π)] in
/-- **There are `[κ(x) : κ(π x)]` lifts over `x`** of the geometric point at `π(x)`, when `κ(π x)`
is finite: `κ(x)/κ(π x)` is a finite separable extension and `κ(π x)‾` is normal over `κ(π x)`. -/
public theorem natCard_geometricLifts_over (x : X.1)
    [Finite (Y.1.residueField ((B.inclusion.map π).base x))] :
    Nat.card {l : GeometricLifts B π (geometricPointAt Y.1 ((B.inclusion.map π).base x)) //
        geometricLiftPoint B π _ l = x} = liftResidueDegree (B.inclusion.map π) x := by
  let : Algebra (Y.1.residueField ((B.inclusion.map π).base x)) (X.1.residueField x) :=
    ((B.inclusion.map π).residueFieldMap x).hom.toAlgebra
  rw [← Nat.card_congr (geometricLiftsOverEquiv B π x)]
  -- `κ(x)` is finite over `κ(π x)`
  let g := B.inclusion.map π
  have : Module.Finite (Y.1.residueField (g.base x)) (X.1.residueField x) :=
    finite_residueFieldMap_hom B π x
  have : Finite (X.1.residueField x) := Module.finite_of_finite (Y.1.residueField (g.base x))
  have : Algebra.IsSeparable (Y.1.residueField (g.base x)) (X.1.residueField x) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  let ι : X.1.residueField x →ₐ[Y.1.residueField (g.base x)]
      AlgebraicClosure (Y.1.residueField (g.base x)) := IsAlgClosed.lift
  exact Stacks.FieldTheory.natCard_algHom_eq_finrank _ _ _ ι

/-- **A lift over `x` is fixed by `π_y ^ (e + 1)` iff `[κ(x) : κ(y)]` divides `e + 1`**, for
`y = π(x)`: the lift is fixed iff its embedding `κ(x) → κ(y)‾` lands in the fixed field of
`π_y ^ (e + 1)`, i.e. iff every element of `κ(x)` is fixed by raising to the power
`#κ(y) ^ (e + 1)`. -/
public theorem geometricLiftsPerm_pow_fixed_iff [IsNoetherian X.1] [IsNoetherian Y.1] (x : X.1)
    [Finite (Y.1.residueField ((B.inclusion.map π).base x))]
    (l : GeometricLifts B π (geometricPointAt Y.1 ((B.inclusion.map π).base x)))
    (hl : geometricLiftPoint B π _ l = x) (e : ℕ) :
    haveI := isIso_frobeniusPointHom_hom Y.1 ((B.inclusion.map π).base x)
    ((geometricLiftsPerm π (frobeniusPointHom Y.1 ((B.inclusion.map π).base x))) ^ (e + 1)) l = l ↔
      liftResidueDegree (B.inclusion.map π) x ∣ e + 1 := by
  classical
  have := isIso_frobeniusPointHom_hom Y.1 ((B.inclusion.map π).base x)
  obtain ⟨⟨x', τ⟩, hx⟩ : ∃ s, (Scheme.SpecToEquivOfField _ X.1).symm s = l.1 :=
    ⟨_, (Scheme.SpecToEquivOfField _ X.1).symm_apply_apply _⟩
  have hx' : x' = x := by
    rw [← hl]
    show x' = (Scheme.SpecToEquivOfField _ X.1 l.1).1
    rw [← hx, Equiv.apply_symm_apply]
  subst hx'
  have hlφ : l.1 = Spec.map τ ≫ X.1.fromSpecResidueField x' := hx.symm
  set ψ := (residueGeometricFrobenius Y.1 ((B.inclusion.map π).base x')) ^ (e + 1)
  let : Fintype (Y.1.residueField ((B.inclusion.map π).base x')) := Fintype.ofFinite _
  -- `κ(x')` is finite over `κ(y)`
  let g := B.inclusion.map π
  let mres := (g.residueFieldMap x').hom
  dsimp at mres
  algebraize [mres]
  have : Module.Finite (Y.1.residueField (g.base x')) (X.1.residueField x') :=
    finite_residueFieldMap_hom B π x'
  rw [Subtype.ext_iff, geometricLiftsPerm_pow_succ_apply]
  show ((frobeniusPointHom Y.1 ((B.inclusion.map π).base x')).iterate e).hom ≫ l.1 = l.1 ↔ _
  rw [frobeniusPointHom, galoisPointHom_iterate_hom, hlφ, ← Category.assoc, ← Spec.map_comp]
  unfold liftResidueDegree
  have : Finite ((B.inclusion.obj Y).residueField ((B.inclusion.map π).base x')) :=
    ‹Finite (Y.1.residueField ((B.inclusion.map π).base x'))›
  let : Fintype ((B.inclusion.obj Y).residueField ((B.inclusion.map π).base x')) :=
    Fintype.ofFinite _
  rw [← AlgebraicGeometry.forall_pow_card_pow_eq_iff]
  constructor
  · intro h c
    have h1 := congrArg (Scheme.SpecToEquivOfField _ X.1) h
    rw [show Spec.map (τ ≫ CommRingCat.ofHom ψ.toAlgHom.toRingHom) ≫
        X.1.fromSpecResidueField x' = (Scheme.SpecToEquivOfField _ X.1).symm
          ⟨x', τ ≫ CommRingCat.ofHom ψ.toAlgHom.toRingHom⟩ from rfl,
      show Spec.map (τ) ≫ X.1.fromSpecResidueField x' =
        (Scheme.SpecToEquivOfField _ X.1).symm ⟨x', τ⟩ from rfl,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h1
    have h2 := congrArg (fun τ => τ.hom c) (eq_of_heq (Sigma.mk.inj h1).2)
    change ψ (τ.hom c) = τ.hom c at h2
    apply τ.hom.injective
    rw [map_pow, Fintype.card_eq_nat_card]
    have h3 := residueGeometricFrobenius_pow_pow_card Y.1 ((B.inclusion.map π).base x') (e + 1)
      (τ.hom c)
    change (ψ (τ.hom c)) ^ _ = τ.hom c at h3
    rwa [h2] at h3
  · intro h
    congr 2
    ext c
    show ψ (τ.hom c) = τ.hom c
    apply ψ.symm.injective
    rw [AlgEquiv.symm_apply_apply]
    have h3 := residueGeometricFrobenius_pow_pow_card Y.1 ((B.inclusion.map π).base x') (e + 1)
      (ψ.symm (τ.hom c))
    change (ψ (ψ.symm (τ.hom c))) ^ _ = ψ.symm (τ.hom c) at h3
    rw [AlgEquiv.apply_symm_apply] at h3
    rw [← h3, ← map_pow]
    congr 1
    have hc := h c
    rw [Fintype.card_eq_nat_card] at hc
    exact hc.symm

end Lifts

/-! ### The trace formula -/

section TraceFormula

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme} (π : X ⟶ Y) [IsFinite (B.inclusion.map π)]
  [AlgebraicGeometry.Etale (B.inclusion.map π)] {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.obj] [IsNoetherian Y.obj]

/-- The residue field at a point over a point with finite residue field is finite. -/
public theorem finite_residueField_of_base_eq {v : Y.1} [Finite (Y.1.residueField v)] (x : X.1)
    (hx : (B.inclusion.map π).base x = v) : Finite (X.1.residueField x) := by
  subst hx
  let g := B.inclusion.map π
  let mres := (g.residueFieldMap x).hom
  dsimp at mres
  algebraize [mres]
  have : Module.Finite (Y.1.residueField (g.base x)) (X.1.residueField x) :=
    finite_residueFieldMap_hom B π x
  exact Module.finite_of_finite (Y.1.residueField (g.base x))

/-- The residue degree over the base is positive. -/
theorem liftResidueDegree_pos (x : X.1) [Finite (Y.1.residueField ((B.inclusion.map π).base x))] :
    0 < liftResidueDegree (B.inclusion.map π) x := by
  rw [← natCard_geometricLifts_over B π x]
  have := finite_geometricLifts B π (geometricPointAt Y.1 ((B.inclusion.map π).base x))
  let : Algebra (Y.1.residueField ((B.inclusion.map π).base x)) (X.1.residueField x) :=
    ((B.inclusion.map π).residueFieldMap x).hom.toAlgebra
  have := finite_residueField_of_base_eq π x rfl
  have : Module.Finite (Y.1.residueField ((B.inclusion.map π).base x)) (X.1.residueField x) :=
    Module.Finite.of_finite
  have : Algebra.IsAlgebraic (Y.1.residueField ((B.inclusion.map π).base x))
    (X.1.residueField x) := Algebra.IsIntegral.isAlgebraic
  let ι : X.1.residueField x →ₐ[Y.1.residueField ((B.inclusion.map π).base x)]
      AlgebraicClosure (Y.1.residueField ((B.inclusion.map π).base x)) := IsAlgClosed.lift
  exact Nat.card_pos_iff.2 ⟨⟨geometricLiftsOverEquiv B π x ι⟩, inferInstance⟩

variable (v : Y.1) [Finite (Y.1.residueField v)]

/-- The points of `X` under the lifts of the geometric point at `v`. -/
public def geometricLiftPoints : Finset X.1 :=
  haveI := finite_geometricLifts B π (geometricPointAt Y.1 v)
  letI : Fintype (GeometricLifts B π (geometricPointAt Y.1 v)) := Fintype.ofFinite _
  open Classical in Finset.univ.image (geometricLiftPoint B π v)

/-- **The points under the lifts of `v̄` are the points over `v`.** -/
public theorem mem_geometricLiftPoints_iff (x : X.1) :
    x ∈ geometricLiftPoints π v ↔ (B.inclusion.map π).base x = v := by
  classical
  constructor
  · intro hx
    simp only [geometricLiftPoints, Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨l, rfl⟩ := hx
    exact base_geometricLiftPoint B π v l
  · intro hx
    subst hx
    obtain ⟨⟨l, hl⟩⟩ := Nat.card_pos_iff.1 ((natCard_geometricLifts_over B π x).symm ▸
      liftResidueDegree_pos π x) |>.1
    simp only [geometricLiftPoints, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨l, hl⟩

variable (F : LAdicSheaf.{u, u + 1} B X ℓ)
  (hF : ∀ n, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (n + 1)))
    (SmallEtale.topology B X.1 X.property) (F.level n))

open Classical in
/-- The contribution of the lifts over one point `x` over `v`: `d_x · Tr(π_x ^ (n / d_x))` if
`d_x = [κ(x) : κ(v)]` divides `n`, and `0` otherwise. -/
theorem sum_trace_directImageRationalBlock_over
    [Fintype (GeometricLifts B π (geometricPointAt Y.1 v))]
    [DecidableEq (GeometricLifts B π (geometricPointAt Y.1 v))] (x : X.1)
    (hxv : (B.inclusion.map π).base x = v) (e : ℕ) :
    haveI := isIso_frobeniusPointHom_hom Y.1 v
    ∑ l ∈ (Finset.univ.filter (fun l =>
        ((geometricLiftsPerm π (frobeniusPointHom Y.1 v)) ^ (e + 1)) l = l)).filter
          (fun l => geometricLiftPoint B π v l = x),
      LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.directImageRationalPr π F hF _ l ∘ₗ
        (LAdicSheaf.rationalStalkFrobenius B Y ℓ
          (SmallEtale.LAdicSheaf.directImage π F hF) v ‹_› ^ (e + 1)) ∘ₗ
        LAdicSheaf.directImageRationalInc π F hF _ l) =
      if liftResidueDegree (B.inclusion.map π) x ∣ e + 1 then
        (liftResidueDegree (B.inclusion.map π) x : ℚ_[ℓ]) * LinearMap.trace ℚ_[ℓ] _
          (LAdicSheaf.rationalStalkFrobenius B X ℓ F x (finite_residueField_of_base_eq π x hxv) ^
            ((e + 1) / liftResidueDegree (B.inclusion.map π) x))
      else 0 := by
  subst hxv
  have := isIso_frobeniusPointHom_hom Y.1 ((B.inclusion.map π).base x)
  set d := liftResidueDegree (B.inclusion.map π) x with hd_def
  by_cases hd : d ∣ e + 1
  · rw [ite_eq_left hd]
    have hfilt : (Finset.univ.filter (fun l =>
        ((geometricLiftsPerm π (frobeniusPointHom Y.1 ((B.inclusion.map π).base x))) ^ (e + 1)) l =
          l)).filter (fun l => geometricLiftPoint B π _ l = x) =
        Finset.univ.filter (fun l => geometricLiftPoint B π _ l = x) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun hl => ⟨(geometricLiftsPerm_pow_fixed_iff B π x l hl e).2 hd, hl⟩⟩
    rw [hfilt]
    have hdpos := liftResidueDegree_pos π x
    obtain ⟨m, hm⟩ : ∃ m, (e + 1) / d = m + 1 := ⟨(e + 1) / d - 1, by
      have : 0 < (e + 1) / d := Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos e) hd) hdpos
      omega⟩
    have hxfin : Finite (X.1.residueField x) := finite_residueField_of_base_eq π x rfl
    have hcardx : Nat.card (X.1.residueField x) =
        Nat.card (Y.1.residueField ((B.inclusion.map π).base x)) ^ d := by
      let : Algebra (Y.1.residueField ((B.inclusion.map π).base x)) (X.1.residueField x) :=
        ((B.inclusion.map π).residueFieldMap x).hom.toAlgebra
      have : Module.Finite (Y.1.residueField ((B.inclusion.map π).base x))
        (X.1.residueField x) := Module.Finite.of_finite
      exact Module.natCard_eq_pow_finrank
    have key : ∀ (y : X.1) (hy : y = x) (h1 : Finite (X.1.residueField y)),
        LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B X ℓ F y h1 ^ (m + 1)) =
          LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B X ℓ F x
            (finite_residueField_of_base_eq π x rfl) ^ (m + 1)) := by
      rintro _ rfl _
      rfl
    rw [Finset.sum_congr rfl (g := fun _ => LinearMap.trace ℚ_[ℓ] _
      (LAdicSheaf.rationalStalkFrobenius B X ℓ F x (finite_residueField_of_base_eq π x rfl) ^
        ((e + 1) / d))) ?_]
    · rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, natCard_geometricLifts_over B π x]
    · intro l hl
      have hl' := (Finset.mem_filter.1 hl).2
      have hfix := (geometricLiftsPerm_pow_fixed_iff B π x l hl' e).2 hd
      have : Finite (X.1.residueField (geometricLiftPoint B π _ l)) := by rw [hl']; exact hxfin
      have hc : Nat.card (X.1.residueField (geometricLiftPoint B π _ l)) ^ (m + 1) =
          Nat.card (Y.1.residueField ((B.inclusion.map π).base x)) ^ (e + 1) := by
        rw [hl', hcardx, ← pow_mul, ← hm, Nat.mul_div_cancel' hd]
      rw [LAdicSheaf.trace_directImageRationalBlock_eq π F hF _ l e hfix m hc, hm]
      exact key _ hl' _
  · rw [ite_eq_right hd]
    refine Finset.sum_eq_zero fun l hl => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hl
    exact absurd ((geometricLiftsPerm_pow_fixed_iff B π x l h2 e).1 (Finset.mem_filter.1 h1).2) hd

open Classical in
/-- **The trace formula for the direct image along a finite étale morphism**: at a point `v`
with finite residue field and for `n = e + 1 ≥ 1`,
`Tr(π_v ^ n | (π_* F)_v̄ ⊗ ℚ_ℓ) = ∑_{x ↦ v, d_x ∣ n} d_x · Tr(π_x ^ (n / d_x) | F_x̄ ⊗ ℚ_ℓ)`,
the sum over the points `x` of `X` over `v` (`Stacks.EtaleCohomology.mem_geometricLiftPoints_iff`),
with `d_x = [κ(x) : κ(v)]`. -/
public theorem LAdicSheaf.trace_rationalStalkFrobenius_directImage_pow_eq_sum (e : ℕ) :
    LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B Y ℓ
        (SmallEtale.LAdicSheaf.directImage π F hF) v ‹_› ^ (e + 1)) =
      ∑ x ∈ geometricLiftPoints π v,
        if h : (B.inclusion.map π).base x = v then
          (if liftResidueDegree (B.inclusion.map π) x ∣ e + 1 then
            (liftResidueDegree (B.inclusion.map π) x : ℚ_[ℓ]) * LinearMap.trace ℚ_[ℓ] _
              (LAdicSheaf.rationalStalkFrobenius B X ℓ F x (finite_residueField_of_base_eq π x h) ^
                ((e + 1) / liftResidueDegree (B.inclusion.map π) x))
          else 0)
        else 0 := by
  classical
  have := finite_geometricLifts B π (geometricPointAt Y.1 v)
  let : Fintype (GeometricLifts B π (geometricPointAt Y.1 v)) := Fintype.ofFinite _
  rw [LAdicSheaf.trace_rationalStalkFrobenius_directImage_pow π F hF v (e + 1),
    ← Finset.sum_fiberwise_of_maps_to (g := geometricLiftPoint B π v) (t := geometricLiftPoints π v)
      (fun l _ => (mem_geometricLiftPoints_iff π v _).2 (base_geometricLiftPoint B π v l))]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [dite_eq_left ((mem_geometricLiftPoints_iff π v x).1 hx)]
  exact sum_trace_directImageRationalBlock_over π v F hF x
    ((mem_geometricLiftPoints_iff π v x).1 hx) e

end TraceFormula

end Stacks.EtaleCohomology

end
