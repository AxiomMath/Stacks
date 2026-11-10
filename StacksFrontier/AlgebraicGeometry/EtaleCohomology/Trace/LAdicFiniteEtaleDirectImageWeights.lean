module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicFiniteEtaleDirectImageStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharpolyPermutedBlockRoots
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PointwiseMixedInverseImage
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteFieldFrobeniusDense

/-!
# Pointwise weights of the direct image along a finite étale morphism

Let `π : X ⟶ Y` be a finite étale morphism of schemes of finite type over a finite field `k` with
`q` elements (objects of a big étale site), and `F` an ℓ-adic sheaf on `X` whose levels are
locally constant of finite type. At a closed point `v` of `Y`, the rational stalk of `π_* F` at
`v̄` is the direct sum of the rational stalks of `F` at the lifts `x̄` of `v̄`
(`Stacks.EtaleCohomology.LAdicSheaf.directImageRational_sum`); the geometric Frobenius `π_v`
permutes the lifts and the summands (`…rationalStalkEnd_directImage_comp_inc_comp_pr`), and a power
`π_v ^ d` fixing a lift `x̄` acts on its summand as an endomorphism of the geometric point `x̄`
(`…directImageRationalPr_comp_rationalStalkEnd_pow_comp_inc`).

That endomorphism is compared with the geometric Frobenius at the closed point `u` of `X` under
`x̄`: an embedding `κ(u)‾ → κ(v)‾` extending `κ(u) → κ(v)‾` is a morphism of geometric points
from `x̄` to the geometric point at `u`, and it intertwines `π_v ^ (d · deg u)` and
`π_u ^ (d · deg v)`, both of which raise to the power `q ^ (d · deg u · deg v)` on the
algebraically closed fields, up to inversion. Hence every characteristic root `z` of `π_v ^ d` on
the summand of `x̄` has `z ^ deg u = α ^ (d · deg v)` for a characteristic root `α` of `π_u`, and
if `F` is pointwise `ι`-mixed of weights `≤ w` then `|z| = q ^ (d · deg v · w' / 2)` with
`w' ≤ w`. By `Stacks.EtaleCohomology.norm_eq_of_permutedBlocks`, `π_* F` is pointwise `ι`-mixed
of weights `≤ w` (Weil II 1.2.2; this is the step of the reduction of Weil II 3.3, and of the
weight bound of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), to opens of the affine
line in which a lisse sheaf is pushed along a finite étale map).

## Main definitions

* `Stacks.EtaleCohomology.geometricLiftPoint`: the point of `X` under a lift of the geometric
  point at `v`.
* `Stacks.EtaleCohomology.geometricLiftPointHom`: the morphism of geometric points from the lift
  to the geometric point at that point.

## Main results

* `Stacks.EtaleCohomology.geometricLiftPointHom_comp_frobenius_iterate`: the comparison of the
  Frobenius powers.
* `Stacks.EtaleCohomology.LAdicSheaf.IsPointwiseMixedOfWeightLE.directImage`: pointwise
  mixedness passes to `π_* F`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

/-! ### Iterates of an endomorphism of a geometric point -/

/-- The underlying morphisms of iterates compose like exponents. -/
public theorem GeometricPoint.Hom.iterate_hom_comp {S : Scheme.{u}} {s : GeometricPoint S}
    (a : GeometricPoint.Hom s s) (i j : ℕ) :
    (a.iterate i).hom ≫ (a.iterate j).hom = (a.iterate (i + j + 1)).hom := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change (a.iterate i).hom ≫ ((a.iterate j).hom ≫ a.hom) = ((a.iterate (i + j + 1)).hom ≫ a.hom)
    rw [← ih]
    exact (Category.assoc _ _ _).symm

/-! ### The point under a lift of a geometric point, and its geometric point -/

section LiftPoint

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (π : X ⟶ Y) (v : Y.1)

/-- The point of `X` under a lift `x̄` of the geometric point at `v`, with the embedding
`κ(u) ⟶ κ(v)‾` of its residue field. -/
public abbrev geometricLiftData (x : GeometricLifts B π (geometricPointAt Y.1 v)) :
    Σ u : X.1, X.1.residueField u ⟶ CommRingCat.of (AlgebraicClosure (Y.1.residueField v)) :=
  Scheme.SpecToEquivOfField (AlgebraicClosure (Y.1.residueField v)) X.1 x.1

/-- The point of `X` under a lift of the geometric point at `v`. -/
public abbrev geometricLiftPoint (x : GeometricLifts B π (geometricPointAt Y.1 v)) : X.1 :=
  (geometricLiftData B π v x).1

/-- A lift `x̄` of the geometric point at `v` factors as `Spec κ(v)‾ ⟶ Spec κ(u) ⟶ X`, through
the embedding of `geometricLiftData` and the residue field of its point `u`. -/
public theorem geometricLift_eq (x : GeometricLifts B π (geometricPointAt Y.1 v)) :
    x.1 = Spec.map (geometricLiftData B π v x).2 ≫
      X.1.fromSpecResidueField (geometricLiftPoint B π v x) :=
  ((Scheme.SpecToEquivOfField (AlgebraicClosure (Y.1.residueField v)) X.1).symm_apply_apply
    x.1).symm

/-- The point under a lift of the geometric point at `v` lies over `v`. -/
public theorem base_geometricLiftPoint (x : GeometricLifts B π (geometricPointAt Y.1 v)) :
    (B.inclusion.map π).base (geometricLiftPoint B π v x) = v := by
  have h1 : geometricLiftPoint B π v x = x.1.base default := by
    simp only [geometricLiftPoint, geometricLiftData, Scheme.SpecToEquivOfField]
    exact congrArg x.1.base
      (Subsingleton.elim (α := Spec (CommRingCat.of (AlgebraicClosure (Y.1.residueField v)))) _ _)
  rw [h1, ← Scheme.Hom.comp_apply, x.2]
  exact geometricPointAt_liesOver Y.1 v

/-- `κ(u)‾` and `κ(v)‾`: the embedding `κ(u) → κ(v)‾` makes the latter a `κ(u)`-algebra. -/
public abbrev geometricLiftAlgebra (x : GeometricLifts B π (geometricPointAt Y.1 v)) :
    Algebra (X.1.residueField (geometricLiftPoint B π v x))
      (AlgebraicClosure (Y.1.residueField v)) :=
  (geometricLiftData B π v x).2.hom.toAlgebra

/-- An embedding `κ(u)‾ → κ(v)‾` over `κ(u) → κ(v)‾`. -/
public def geometricLiftEmbedding (x : GeometricLifts B π (geometricPointAt Y.1 v)) :
    AlgebraicClosure (X.1.residueField (geometricLiftPoint B π v x)) →+*
      AlgebraicClosure (Y.1.residueField v) :=
  letI := geometricLiftAlgebra B π v x
  (IsAlgClosed.lift (M := AlgebraicClosure (Y.1.residueField v))
    (R := X.1.residueField (geometricLiftPoint B π v x))
    (S := AlgebraicClosure (X.1.residueField (geometricLiftPoint B π v x)))).toRingHom

/-- `geometricLiftEmbedding` extends the embedding `κ(u) → κ(v)‾` of `geometricLiftData`. -/
public theorem geometricLiftEmbedding_algebraMap (x : GeometricLifts B π (geometricPointAt Y.1 v))
    (z : X.1.residueField (geometricLiftPoint B π v x)) :
    geometricLiftEmbedding B π v x (algebraMap _ _ z) = (geometricLiftData B π v x).2.hom z := by
  let := geometricLiftAlgebra B π v x
  exact (IsAlgClosed.lift (M := AlgebraicClosure (Y.1.residueField v))
    (R := X.1.residueField (geometricLiftPoint B π v x))
    (S := AlgebraicClosure (X.1.residueField (geometricLiftPoint B π v x)))).commutes z

/-- **The morphism of geometric points from a lift of `v̄` to the geometric point at the point
under it**: `Spec` of an embedding of algebraic closures. -/
public def geometricLiftPointHom (x : GeometricLifts B π (geometricPointAt Y.1 v)) :
    GeometricPoint.Hom (geometricPointLift (B.inclusion.map π) (geometricPointAt Y.1 v) x)
      (geometricPointAt X.1 (geometricLiftPoint B π v x)) where
  hom := Spec.map (CommRingCat.ofHom (geometricLiftEmbedding B π v x))
  comm := by
    change Spec.map (CommRingCat.ofHom (geometricLiftEmbedding B π v x)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (X.1.residueField (geometricLiftPoint B π v x))
          (AlgebraicClosure (X.1.residueField (geometricLiftPoint B π v x))))) ≫
        X.1.fromSpecResidueField (geometricLiftPoint B π v x) = x.1
    rw [geometricLift_eq B π v x, ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext z
    exact geometricLiftEmbedding_algebraMap B π v x z

/-- Raising to the power `#κ` inverts the geometric Frobenius of an algebraic closure of a
finite field `κ`, and so its iterates. -/
theorem residueGeometricFrobenius_pow_pow_card (Z : Scheme.{u}) (z : Z)
    [Finite (Z.residueField z)] (n : ℕ) (w : AlgebraicClosure (Z.residueField z)) :
    (((residueGeometricFrobenius Z z) ^ n) w) ^ Nat.card (Z.residueField z) ^ n = w := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
      rw [pow_succ' (residueGeometricFrobenius Z z) n, AlgEquiv.mul_apply,
        pow_succ' (Nat.card (Z.residueField z)) n, pow_mul,
        ← residueGeometricFrobenius_symm_apply, AlgEquiv.symm_apply_apply]
      exact ih w

variable [Finite (Y.1.residueField v)]

/-- **The geometric Frobenius powers at the lift and at the point under it agree**: if
`#κ(u) ^ (m + 1) = #κ(v) ^ (d + 1)`, the embedding of algebraic closures intertwines
`π_u ^ (m + 1)` and `π_v ^ (d + 1)`, both inverse to raising to that power. -/
public theorem geometricLiftPointHom_comp_frobenius_iterate
    (x : GeometricLifts B π (geometricPointAt Y.1 v))
    [Finite (X.1.residueField (geometricLiftPoint B π v x))] (m d : ℕ)
    (hmd : Nat.card (X.1.residueField (geometricLiftPoint B π v x)) ^ (m + 1) =
      Nat.card (Y.1.residueField v) ^ (d + 1))
    (b : GeometricPoint.Hom (geometricPointLift (B.inclusion.map π) (geometricPointAt Y.1 v) x)
      (geometricPointLift (B.inclusion.map π) (geometricPointAt Y.1 v) x))
    (hb : b.hom = ((frobeniusPointHom Y.1 v).iterate d).hom) :
    (geometricLiftPointHom B π v x).comp
        ((frobeniusPointHom X.1 (geometricLiftPoint B π v x)).iterate m) =
      b.comp (geometricLiftPointHom B π v x) := by
  refine GeometricPoint.Hom.ext' ?_
  change Spec.map (CommRingCat.ofHom (geometricLiftEmbedding B π v x)) ≫
      ((frobeniusPointHom X.1 (geometricLiftPoint B π v x)).iterate m).hom =
    b.hom ≫ Spec.map (CommRingCat.ofHom (geometricLiftEmbedding B π v x))
  rw [hb, frobeniusPointHom, galoisPointHom_iterate_hom, frobeniusPointHom,
    galoisPointHom_iterate_hom, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext z
  change geometricLiftEmbedding B π v x
      (((residueGeometricFrobenius X.1 (geometricLiftPoint B π v x)) ^ (m + 1)) z) =
    ((residueGeometricFrobenius Y.1 v) ^ (d + 1)) (geometricLiftEmbedding B π v x z)
  set φ := (residueGeometricFrobenius Y.1 v) ^ (d + 1)
  set t := φ.symm (geometricLiftEmbedding B π v x
    (((residueGeometricFrobenius X.1 (geometricLiftPoint B π v x)) ^ (m + 1)) z))
  have ht : t = geometricLiftEmbedding B π v x z := by
    have h1 := residueGeometricFrobenius_pow_pow_card Y.1 v (d + 1) t
    rw [AlgEquiv.apply_symm_apply] at h1
    rw [← h1, ← map_pow, ← hmd, residueGeometricFrobenius_pow_pow_card]
  rw [← ht, AlgEquiv.apply_symm_apply]

/-- The residue field extension at a point of `X` over a quasi-finite `π` is finite. -/
private theorem residueFieldMap_finite [LocallyQuasiFinite (B.inclusion.map π)] (w : X.1) :
    (((B.inclusion.map π).residueFieldMap w).hom).Finite := by
  have hm : (((B.inclusion.map π).residueFieldMap w).hom).QuasiFinite := by
    apply RingHom.QuasiFinite.of_comp (g := (Y.1.residue ((B.inclusion.map π).base w)).hom)
    rw [← CommRingCat.hom_comp, Scheme.residue_residueFieldMap]
    exact (RingHom.QuasiFinite.of_finite (RingHom.Finite.of_surjective _
      IsLocalRing.residue_surjective)).comp ((B.inclusion.map π).quasiFiniteAt w)
  algebraize [((B.inclusion.map π).residueFieldMap w).hom]
  exact Module.Finite.of_quasiFinite

/-- The residue field at the point under a lift is finite when that at `v` is: it is a finite
extension of `κ(v)`, `π` being quasi-finite. -/
public theorem finite_residueField_geometricLiftPoint [LocallyQuasiFinite (B.inclusion.map π)]
    (x : GeometricLifts B π (geometricPointAt Y.1 v)) :
    Finite (X.1.residueField (geometricLiftPoint B π v x)) := by
  set w := geometricLiftPoint B π v x
  have hw := base_geometricLiftPoint B π v x
  let g := B.inclusion.map π
  let m := (g.residueFieldMap w).hom
  dsimp at m
  have hm : m.Finite := residueFieldMap_finite B π w
  algebraize [m]
  have : Finite (Y.1.residueField (g.base w)) := hw ▸ ‹Finite (Y.1.residueField v)›
  exact Module.finite_of_finite (Y.1.residueField (g.base w))

/-- **A lift fixed by a power of the Frobenius has residue degree dividing it**: if
`π_v ^ (e + 1)` fixes the lift `x̄` over `u`, then `#κ(u) ^ (m + 1) = #κ(v) ^ (e + 1)` for some
`m`. The fixed lift says that `κ(u) → κ(v)‾` lands in the fixed field of `π_v ^ (e + 1)`, so that
every element of `κ(u)` is fixed by raising to the power `#κ(v) ^ (e + 1)`; hence
`[κ(u) : κ(v)]` divides `e + 1` (`AlgebraicGeometry.forall_pow_card_pow_eq_iff`). -/
public theorem exists_natCard_pow_eq_of_iterate_fixed [LocallyQuasiFinite (B.inclusion.map π)]
    (x : GeometricLifts B π (geometricPointAt Y.1 v))
    [Finite (X.1.residueField (geometricLiftPoint B π v x))] (e : ℕ)
    (hx : ((frobeniusPointHom Y.1 v).iterate e).hom ≫ x.1 = x.1) :
    ∃ m : ℕ, Nat.card (X.1.residueField (geometricLiftPoint B π v x)) ^ (m + 1) =
      Nat.card (Y.1.residueField v) ^ (e + 1) := by
  set w := geometricLiftPoint B π v x
  set σ := (geometricLiftData B π v x).2
  set φ := (residueGeometricFrobenius Y.1 v) ^ (e + 1)
  -- the embedding is fixed by `φ`
  have hfix : σ ≫ CommRingCat.ofHom φ.toAlgHom.toRingHom = σ := by
    have h1 : Spec.map (σ ≫ CommRingCat.ofHom φ.toAlgHom.toRingHom) ≫ X.1.fromSpecResidueField w =
        Spec.map σ ≫ X.1.fromSpecResidueField w := by
      rw [Spec.map_comp, Category.assoc, ← geometricLift_eq B π v x]
      rwa [frobeniusPointHom, galoisPointHom_iterate_hom] at hx
    have h3 := congrArg (Scheme.SpecToEquivOfField (AlgebraicClosure (Y.1.residueField v)) X.1) h1
    rw [show Spec.map (σ ≫ CommRingCat.ofHom φ.toAlgHom.toRingHom) ≫ X.1.fromSpecResidueField w =
        (Scheme.SpecToEquivOfField _ X.1).symm ⟨w, σ ≫ CommRingCat.ofHom φ.toAlgHom.toRingHom⟩
        from rfl, show Spec.map σ ≫ X.1.fromSpecResidueField w =
        (Scheme.SpecToEquivOfField _ X.1).symm ⟨w, σ⟩ from rfl, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply] at h3
    exact eq_of_heq (Sigma.mk.inj h3).2
  have hpow : ∀ c : X.1.residueField w, c ^ Nat.card (Y.1.residueField v) ^ (e + 1) = c := by
    intro c
    apply σ.hom.injective
    have h1 := congrArg (fun τ => τ.hom c) hfix
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
    rw [map_pow]
    have h2 := residueGeometricFrobenius_pow_pow_card Y.1 v (e + 1) (σ.hom c)
    change (φ (σ.hom c)) ^ _ = σ.hom c at h2
    change φ (σ.hom c) = σ.hom c at h1
    rwa [h1] at h2
  -- `κ(u)` is a finite extension of `κ(π(u))`
  have hw := base_geometricLiftPoint B π v x
  let g := B.inclusion.map π
  let mres := (g.residueFieldMap w).hom
  dsimp at mres
  have hm : mres.Finite := residueFieldMap_finite B π w
  algebraize [mres]
  have hcardY : Nat.card (Y.1.residueField (g.base w)) = Nat.card (Y.1.residueField v) := by
    rw [hw]
  have : Finite (Y.1.residueField (g.base w)) := hw ▸ ‹Finite (Y.1.residueField v)›
  let : Fintype (Y.1.residueField (g.base w)) := Fintype.ofFinite _
  obtain ⟨t, ht⟩ := (AlgebraicGeometry.forall_pow_card_pow_eq_iff
    (k := Y.1.residueField (g.base w)) (X.1.residueField w) (e + 1)).1 (by
      intro c
      rw [Fintype.card_eq_nat_card, hcardY]
      exact hpow c)
  obtain ⟨m, hm'⟩ := Nat.exists_eq_add_one_of_ne_zero (n := t) (by rintro rfl; omega)
  refine ⟨m, ?_⟩
  rw [Module.natCard_eq_pow_finrank (K := Y.1.residueField (g.base w)), ← pow_mul, ← hm', ← ht,
    hcardY]

end LiftPoint

/-! ### Pointwise mixedness of the direct image -/

section Weights

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
  (F : LAdicSheaf.{u, u + 1} B X ℓ)
  (hF : ∀ n, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (n + 1)))
    (SmallEtale.topology B X.1 X.property) (F.level n))
  {k : Type u} [Field k] [Finite k] (fV : Y.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fV]

/-- The geometric Frobenius at a point with finite residue field is an isomorphism. -/
theorem isIso_frobeniusPointHom_hom (Z : Scheme.{u}) (z : Z) [Finite (Z.residueField z)] :
    IsIso (frobeniusPointHom Z z).hom := by
  rw [frobeniusPointHom_hom]
  have : IsIso (CommRingCat.ofHom (residueGeometricFrobenius Z z).toAlgHom.toRingHom) :=
    ⟨⟨CommRingCat.ofHom (residueGeometricFrobenius Z z).symm.toAlgHom.toRingHom,
      by ext w; exact (residueGeometricFrobenius Z z).symm_apply_apply w,
      by ext w; exact (residueGeometricFrobenius Z z).apply_symm_apply w⟩⟩
  infer_instance

/-- **Pointwise mixedness passes to the direct image along a finite étale morphism** (Weil II
1.2.2): if `F` is pointwise `ι`-mixed of weights `≤ w` on `X`, over `k` through `π`, then so is
`π_* F` on `Y`. At a closed point `v`, the geometric Frobenius permutes the summands of
`(π_* F)_v̄ ⊗ ℚ_ℓ` at the lifts `x̄` of `v̄`, and a power `π_v ^ d` fixing `x̄` acts on its summand
with characteristic roots `z` satisfying `z ^ deg u = α ^ (d · deg v)` for a characteristic root
`α` of `π_u`, `u` the point under `x̄`. -/
public theorem LAdicSheaf.IsPointwiseMixedOfWeightLE.directImage {q : ℕ} {ι : ℚ_[ℓ] →+* ℂ}
    {w : ℤ} (hFw : LAdicSheaf.IsPointwiseMixedOfWeightLE B X ℓ (B.inclusion.map π ≫ fV) F q ι w) :
    LAdicSheaf.IsPointwiseMixedOfWeightLE B Y ℓ fV (SmallEtale.LAdicSheaf.directImage π F hF)
      q ι w := by
  classical
  intro v z hz
  have hv : Finite (Y.1.residueField v.1) := finite_residueField fV v.1 v.2
  let := Fintype.ofFinite k
  have := finite_geometricLifts B π (geometricPointAt Y.1 v.1)
  let : Fintype (GeometricLifts B π (geometricPointAt Y.1 v.1)) := Fintype.ofFinite _
  have : IsIso (frobeniusPointHom Y.1 v.1).hom := isIso_frobeniusPointHom_hom Y.1 v.1
  set a := frobeniusPointHom Y.1 v.1
  have hz' : ((LAdicSheaf.rationalStalkEnd B Y ℓ (SmallEtale.LAdicSheaf.directImage π F hF)
      a).charpoly.map ι).IsRoot z := hz
  have key := norm_eq_of_permutedBlocks (q := q) (a := residueDegree fV v.1) (b := w) ι
    (LAdicSheaf.directImageRationalPr π F hF _) (LAdicSheaf.directImageRationalInc π F hF _)
    (LAdicSheaf.directImageRational_sum π F hF _)
    (LAdicSheaf.directImageRational_pr_inc_self π F hF _) (geometricLiftsPerm π a) _
    (LAdicSheaf.rationalStalkEnd_directImage_comp_inc_comp_pr π F hF a) ?_ hz'
  · obtain ⟨w', hw', hnorm⟩ := key
    refine ⟨w', hw', ?_⟩
    rw [hnorm]
    congr 1
  intro x d hd hx w0 hw0
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hfix : (a.iterate e).hom ≫ x.1 = x.1 := by
    have := congrArg Subtype.val hx
    rwa [geometricLiftsPerm_pow_succ_apply] at this
  let b : GeometricPoint.Hom (geometricPointLift (B.inclusion.map π) (geometricPointAt Y.1 v.1) x)
      (geometricPointLift (B.inclusion.map π) (geometricPointAt Y.1 v.1) x) :=
    ⟨(a.iterate e).hom, hfix⟩
  rw [LAdicSheaf.directImageRationalPr_comp_rationalStalkEnd_pow_comp_inc π F hF a x e hx b rfl]
    at hw0
  set u := geometricLiftPoint B π v.1 x
  have hu : Finite (X.1.residueField u) := finite_residueField_geometricLiftPoint B π v.1 x
  have : Finite ((B.inclusion.obj X).residueField u) := hu
  have : Finite ((B.inclusion.obj Y).residueField v.1) := hv
  have huc : IsClosed ({u} : Set X.1) :=
    isClosed_singleton_of_module_finite_residueField (B.inclusion.map π ≫ fV) u (by
      let : Algebra k ((B.inclusion.obj X).residueField u) :=
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (B.inclusion.map π ≫ fV).appTop ≫
          (B.inclusion.obj X).Γevaluation u).hom.toAlgebra
      exact Module.Finite.of_finite)
  set N := residueDegree (B.inclusion.map π ≫ fV) u
  set D := residueDegree fV v.1
  have hcardu : Nat.card (X.1.residueField u) = Fintype.card k ^ N :=
    natCard_residueField_eq_pow_residueDegree _ u
  have hcardv : Nat.card (Y.1.residueField v.1) = Fintype.card k ^ D :=
    natCard_residueField_eq_pow_residueDegree _ v.1
  have hN : N ≠ 0 := by
    intro h0
    have h1 : Nat.card (X.1.residueField u) = 1 := by rw [hcardu, h0, pow_zero]
    exact (Finite.one_lt_card (α := X.1.residueField u)).ne' h1
  have hD : D ≠ 0 := by
    intro h0
    have h1 : Nat.card (Y.1.residueField v.1) = 1 := by rw [hcardv, h0, pow_zero]
    exact (Finite.one_lt_card (α := Y.1.residueField v.1)).ne' h1
  obtain ⟨N', hN'⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m, (e + 1) * D = m + 1 := ⟨(e + 1) * D - 1, by
    have : 0 < (e + 1) * D := Nat.mul_pos (Nat.succ_pos e) (Nat.pos_of_ne_zero hD)
    omega⟩
  obtain ⟨d', hd'⟩ : ∃ d', (e + 1) * (N' + 1) = d' + 1 := ⟨(e + 1) * (N' + 1) - 1, by
    have : 0 < (e + 1) * (N' + 1) := Nat.mul_pos (Nat.succ_pos e) (Nat.succ_pos N')
    omega⟩
  have hiter : ∀ j : ℕ, (b.iterate j).hom = (a.iterate ((e + 1) * (j + 1) - 1)).hom := by
    intro j
    induction j with
    | zero => rw [show (e + 1) * (0 + 1) - 1 = e by omega]; rfl
    | succ j ih =>
      change (b.iterate j).hom ≫ (a.iterate e).hom = _
      rw [ih, GeometricPoint.Hom.iterate_hom_comp]
      have h0 : 0 < (e + 1) * (j + 1) := Nat.mul_pos (Nat.succ_pos e) (Nat.succ_pos j)
      have h2 : (e + 1) * (j + 1 + 1) = (e + 1) * (j + 1) + (e + 1) := by ring
      rw [show (e + 1) * (j + 1) - 1 + e + 1 = (e + 1) * (j + 1 + 1) - 1 by omega]
  have hbhom : (b.iterate N').hom = ((frobeniusPointHom Y.1 v.1).iterate d').hom := by
    rw [hiter N', hd', Nat.add_sub_cancel]
  have hcard : Nat.card (X.1.residueField u) ^ (m + 1) =
      Nat.card (Y.1.residueField v.1) ^ (d' + 1) := by
    rw [hcardu, hcardv, ← pow_mul, ← pow_mul, ← hm, ← hd', ← hN']
    congr 1
    ring
  have hcomm := geometricLiftPointHom_comp_frobenius_iterate B π v.1 x m d' hcard (b.iterate N')
    hbhom
  have h1 : ((LAdicSheaf.rationalStalkEnd B X ℓ F (b.iterate N')).charpoly.map ι).IsRoot
      (w0 ^ (N' + 1)) := by
    rw [LAdicSheaf.rationalStalkEnd_iterate]
    let := ι.toAlgebra
    rw [isRoot_charpoly_map_iff_hasEigenvalue_baseChange] at hw0 ⊢
    rw [LinearMap.baseChange_pow]
    exact hw0.pow _
  have h2 := LAdicSheaf.isRoot_charpoly_rationalStalkEnd_of_comp_eq B X ℓ F
    (geometricLiftPointHom B π v.1 x) hcomm ι h1
  rw [LAdicSheaf.rationalStalkEnd_iterate] at h2
  obtain ⟨α, hα, hαeq⟩ := exists_isRoot_charpoly_map_pow_eq ι _ m.succ_ne_zero h2
  obtain ⟨w', hw', hαn⟩ := hFw ⟨u, huc⟩ α hα
  refine ⟨w', hw', ?_⟩
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hpow : ‖w0‖ ^ (N' + 1) = ((q : ℝ) ^ ((((e + 1) * D : ℕ) : ℝ) * w' / 2)) ^ (N' + 1) := by
    rw [← norm_pow, ← hαeq, norm_pow, hαn, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul hq, ← Real.rpow_mul hq]
    congr 1
    change (((N : ℤ) : ℝ) * w') / 2 * ((m + 1 : ℕ) : ℝ) = _
    rw [hN', ← hm]
    push_cast
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg hq _) N'.succ_ne_zero).1 hpow

end Weights

end Stacks.EtaleCohomology

end
