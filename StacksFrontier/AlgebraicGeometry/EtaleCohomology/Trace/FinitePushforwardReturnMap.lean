module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FinitePushforwardFrobeniusCharSeries
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FiniteCoefficientLFunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparisonNaturality

/-!
# The return map of a finite direct image is the Frobenius upstairs

Let `f : X ⟶ Y` be a finite morphism of a big étale site, `y` a point of `Y` with finite residue
field and `x` a point over `y`. Going once around the orbit of the base lift over `x` under the
geometric Frobenius `σ_y` of `ȳ` is the stalk map along `σ_y ^ [κ(x) : κ(y)]` at that lift
(`Stacks.EtaleCohomology.returnMap`). An isomorphism `κ̄(x) ≅ κ̄(y)` extending the base embedding
`κ(x) → κ̄(y)` carries the geometric Frobenius `σ_x` of `κ̄(x)` to `σ_y ^ [κ(x) : κ(y)]`, and the
return map is conjugate to the geometric Frobenius at `x`. Their characteristic series agree, also
with the Frobenius of Mathlib's small étale site used in the L-function.

## Main results

* `Stacks.EtaleCohomology.charSeries_returnMap_eq_closedPointFrobenius`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] ModuleCat.hasLimitsOfSize

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) (Λ : Type) [CommRing Λ]
  (G : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} Λ)) (y : Y.1)
  [Finite (Y.1.residueField y)]
  (hres : ∀ x : {x : X.1 // (fS B f) x = y}, Finite (X.1.residueField x.1))
  (x : {x : X.1 // (fS B f) x = y})

/-- The embedding `κ(x) → κ̄(y)` of the base lift over `x`. -/
public abbrev baseEmbedding : FiberEmbeddings (fS B f) y x :=
  Classical.choice (nonempty_fiberEmbeddings B f y hres x)

/-- `κ̄(y)` as a `κ(x)`-algebra through the base embedding. -/
public abbrev baseEmbeddingAlgebra :
    Algebra (X.1.residueField x.1) (AlgebraicClosure (Y.1.residueField y)) :=
  letI := fiberResidueAlgebra (fS B f) y x
  (baseEmbedding B f y hres x).toRingHom.toAlgebra

/-- Through the base embedding, `κ̄(y)` is an algebraic closure of `κ(x)`. -/
public theorem isAlgClosure_baseEmbedding :
    letI := baseEmbeddingAlgebra B f y hres x
    IsAlgClosure (X.1.residueField x.1) (AlgebraicClosure (Y.1.residueField y)) := by
  let := fiberResidueAlgebra (fS B f) y x
  let := baseEmbeddingAlgebra B f y hres x
  have : IsScalarTower (Y.1.residueField y) (X.1.residueField x.1)
      (AlgebraicClosure (Y.1.residueField y)) :=
    IsScalarTower.of_algebraMap_eq fun r => ((baseEmbedding B f y hres x).commutes r).symm
  have : Algebra.IsAlgebraic (X.1.residueField x.1) (AlgebraicClosure (Y.1.residueField y)) :=
    Algebra.IsAlgebraic.tower_top (K := Y.1.residueField y) (X.1.residueField x.1)
  exact ⟨inferInstance, inferInstance⟩

/-- An isomorphism `κ̄(x) ≅ κ̄(y)` extending the base embedding. -/
public def baseClosureEquiv :
    AlgebraicClosure (X.1.residueField x.1) ≃+* AlgebraicClosure (Y.1.residueField y) :=
  letI := baseEmbeddingAlgebra B f y hres x
  haveI := isAlgClosure_baseEmbedding B f y hres x
  (IsAlgClosure.equiv (X.1.residueField x.1) (AlgebraicClosure (X.1.residueField x.1))
    (AlgebraicClosure (Y.1.residueField y))).toRingEquiv

public theorem baseClosureEquiv_algebraMap (z : X.1.residueField x.1) :
    letI := fiberResidueAlgebra (fS B f) y x
    baseClosureEquiv B f y hres x (algebraMap _ (AlgebraicClosure (X.1.residueField x.1)) z) =
      baseEmbedding B f y hres x z := by
  let := fiberResidueAlgebra (fS B f) y x
  let := baseEmbeddingAlgebra B f y hres x
  have := isAlgClosure_baseEmbedding B f y hres x
  exact (IsAlgClosure.equiv (X.1.residueField x.1) (AlgebraicClosure (X.1.residueField x.1))
    (AlgebraicClosure (Y.1.residueField y))).commutes z

/-- The morphism of geometric points from the base lift over `x` to the geometric point at `x`
given by `κ̄(x) ≅ κ̄(y)`. -/
public def baseLiftHom :
    GeometricPoint.Hom
      (geometricPointLift (fS B f) (geometricPointAt Y.1 y) (baseLift B f y hres x))
      (geometricPointAt X.1 x.1) where
  hom := Spec.map (CommRingCat.ofHom (baseClosureEquiv B f y hres x).toRingHom)
  comm := by
    let := fiberResidueAlgebra (fS B f) y x
    change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (X.1.residueField x.1)
        (AlgebraicClosure (X.1.residueField x.1)))) ≫ X.1.fromSpecResidueField x.1 =
      Spec.map (CommRingCat.ofHom (baseEmbedding B f y hres x).toRingHom) ≫
        X.1.fromSpecResidueField x.1
    rw [← Spec.map_comp_assoc]
    congr 2
    ext z
    exact baseClosureEquiv_algebraMap B f y hres x z

/-- The powers of the geometric Frobenius undo the powers of the cardinality. -/
theorem residueGeometricFrobenius_pow_apply_pow (n : ℕ)
    (v : AlgebraicClosure (Y.1.residueField y)) :
    (residueGeometricFrobenius Y.1 y ^ n) (v ^ (Nat.card (Y.1.residueField y) ^ n)) = v := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, AlgEquiv.mul_apply, pow_succ, pow_mul,
      ← residueGeometricFrobenius_symm_apply, AlgEquiv.apply_symm_apply, ih]

include hres in
/-- `#κ(x) = #κ(y) ^ [κ(x) : κ(y)]`. -/
theorem natCard_residueField_eq_pow :
    Nat.card (X.1.residueField x.1) = Nat.card (Y.1.residueField y) ^ fiberDegree B f y x := by
  let := fiberResidueAlgebra (fS B f) y x
  have := hres x
  let : Fintype (Y.1.residueField y) := Fintype.ofFinite _
  let : Fintype (X.1.residueField x.1) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := Y.1.residueField y)]
  rfl

/-- **`κ̄(x) ≅ κ̄(y)` carries `σ_x` to `σ_y ^ [κ(x) : κ(y)]`.** -/
public theorem residueGeometricFrobenius_pow_baseClosureEquiv
    (z : AlgebraicClosure (X.1.residueField x.1)) :
    haveI := hres x
    (residueGeometricFrobenius Y.1 y ^ fiberDegree B f y x) (baseClosureEquiv B f y hres x z) =
      baseClosureEquiv B f y hres x (residueGeometricFrobenius X.1 x.1 z) := by
  have := hres x
  set w := residueGeometricFrobenius X.1 x.1 z
  have hz : z = w ^ Nat.card (X.1.residueField x.1) := by
    rw [← residueGeometricFrobenius_symm_apply, AlgEquiv.symm_apply_apply]
  rw [hz, map_pow, natCard_residueField_eq_pow B f y hres x,
    residueGeometricFrobenius_pow_apply_pow]

/-- **The return map is compatible with the Frobenius at `x`.** -/
public theorem homOfComm_comp_baseLiftHom :
    haveI := hres x
    (GeometricLifts.homOfComm B f
      (galoisPow B y (residueGeometricFrobenius Y.1 y) (fiberDegree B f y x))
      (baseLift B f y hres x) (baseLift B f y hres x)
      (congrArg Subtype.val (liftAct_pow_fiberDegree_baseLift B f y hres x))).comp
        (baseLiftHom B f y hres x) =
      (baseLiftHom B f y hres x).comp (frobeniusPointHom X.1 x.1) := by
  have := hres x
  refine GeometricPoint.Hom.ext_of_hom ?_
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext z
  exact residueGeometricFrobenius_pow_baseClosureEquiv B f y hres x z

/-- The stalk map along `κ̄(x) ≅ κ̄(y)`, from the stalk at `x̄` to the stalk at the base lift. -/
public abbrev baseLiftStalkMap :
    etaleStalk (A := ModuleCat.{u + 1} Λ) B X.1 X.property (geometricPointAt X.1 x.1) G.obj →ₗ[Λ]
      liftStalk B f Λ G y (baseLift B f y hres x) :=
  ((geometricPointStalkMap B X.1 X.property (baseLiftHom B f y hres x)
    (ModuleCat.{u + 1} Λ)).app G.obj).hom

public theorem baseLiftStalkMap_bijective :
    Function.Bijective (baseLiftStalkMap B f Λ G y hres x) := by
  let i := Scheme.Spec.mapIso (baseClosureEquiv B f y hres x).toCommRingCatIso.op
  exact geometricPointStalkMap_app_bijective B Λ X.property (baseLiftHom B f y hres x) i.inv
    i.hom_inv_id i.inv_hom_id G.obj

/-- The geometric Frobenius at `x` on the stalk at `x̄` of the bounded site. -/
public abbrev pointFrobeniusStalkMap :
    haveI := hres x
    etaleStalk (A := ModuleCat.{u + 1} Λ) B X.1 X.property (geometricPointAt X.1 x.1) G.obj →ₗ[Λ]
      etaleStalk (A := ModuleCat.{u + 1} Λ) B X.1 X.property (geometricPointAt X.1 x.1) G.obj :=
  haveI := hres x
  ((geometricPointStalkMap B X.1 X.property (frobeniusPointHom X.1 x.1)
    (ModuleCat.{u + 1} Λ)).app G.obj).hom

/-- **The return map is conjugate to the geometric Frobenius at `x`** (on the bounded site). -/
public theorem returnMap_eq_conj :
    haveI := hres x
    returnMap B f Λ G y hres x =
      (LinearEquiv.ofBijective _ (baseLiftStalkMap_bijective B f Λ G y hres x)).conj
        (pointFrobeniusStalkMap B f Λ G y hres x) := by
  have := hres x
  have h := congrArg (fun a => ((geometricPointStalkMap B X.1 X.property a
    (ModuleCat.{u + 1} Λ)).app G.obj).hom) (homOfComm_comp_baseLiftHom B f y hres x)
  simp only [geometricPointStalkMap_comp, NatTrans.comp_app, ModuleCat.hom_comp] at h
  refine LinearMap.ext fun v => ?_
  obtain ⟨u, rfl⟩ := (baseLiftStalkMap_bijective B f Λ G y hres x).2 v
  rw [LinearEquiv.conj_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearEquiv.ofBijective_symm_apply_apply]
  exact LinearMap.congr_fun h u

/-- **The local factor of the return map is that of the geometric Frobenius at `x`**, read on
Mathlib's small étale site as in the L-function. -/
public theorem charSeries_returnMap_eq_closedPointFrobenius
    (hfin : ∀ s : GeometricPoint X.1,
      Module.Finite Λ ((etaleModuleStalkFunctor.{u, u + 1, 0} B X Λ s).obj G))
    (hproj : ∀ s : GeometricPoint X.1,
      Module.Projective Λ ((etaleModuleStalkFunctor.{u, u + 1, 0} B X Λ s).obj G))
    {k : Type u} [Field k] [Finite k] (fX : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fX]
    (hx : x.1 ∈ closedPoints X.1) (n : ℕ) :
    haveI : Module.Finite Λ (liftStalk B f Λ G y (baseLift B f y hres x)) := hfin _
    haveI : Module.Projective Λ (liftStalk B f Λ G y (baseLift B f y hres x)) := hproj _
    haveI := finite_sheafFiber_sheafEquiv.{u, u + 1, 0} B X Λ (geometricPointAt X.1 x.1) G (hfin _)
    haveI := projective_sheafFiber_sheafEquiv.{u, u + 1, 0} B X Λ G (geometricPointAt X.1 x.1)
      (hproj _)
    ProjectiveDeterminant.charSeries (returnMap B f Λ G y hres x) n =
      ProjectiveDeterminant.charSeries
        (closedPointFrobenius.{u, u + 1, 0} B X Λ G fX ⟨x.1, hx⟩) n := by
  have : Module.Finite Λ (liftStalk B f Λ G y (baseLift B f y hres x)) := hfin _
  have : Module.Projective Λ (liftStalk B f Λ G y (baseLift B f y hres x)) := hproj _
  have := finite_sheafFiber_sheafEquiv.{u, u + 1, 0} B X Λ (geometricPointAt X.1 x.1) G (hfin _)
  have := projective_sheafFiber_sheafEquiv.{u, u + 1, 0} B X Λ G (geometricPointAt X.1 x.1)
    (hproj _)
  have : Module.Finite Λ (etaleStalk (A := ModuleCat.{u + 1} Λ) B X.1 X.property
      (geometricPointAt X.1 x.1) G.obj) := hfin _
  have : Module.Projective Λ (etaleStalk (A := ModuleCat.{u + 1} Λ) B X.1 X.property
      (geometricPointAt X.1 x.1) G.obj) := hproj _
  have := hres x
  let e := (sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X Λ (geometricPointAt X.1 x.1)).app G
  have hnat : e.inv ≫ frobeniusStalk (ModuleCat.{u + 1} Λ) X.1 x.1
      ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} Λ)).functor.obj G) =
      (geometricPointStalkMap B X.1 X.property (frobeniusPointHom X.1 x.1)
        (ModuleCat.{u + 1} Λ)).app G.obj ≫ e.inv := by
    have h := NatTrans.congr_app (sheafEquivCompSheafFiberIso_inv_naturality.{u, u + 1, 0} B X
      Λ (frobeniusPointHom X.1 x.1)) G
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
    exact h
  have hfrob : frobeniusStalk (ModuleCat.{u + 1} Λ) X.1 x.1
      ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} Λ)).functor.obj G) =
      e.hom ≫ (geometricPointStalkMap B X.1 X.property (frobeniusPointHom X.1 x.1)
        (ModuleCat.{u + 1} Λ)).app G.obj ≫ e.inv :=
    (Iso.hom_inv_id_assoc e _).symm.trans (congrArg (e.hom ≫ ·) hnat)
  have h : closedPointFrobenius.{u, u + 1, 0} B X Λ G fX ⟨x.1, hx⟩ =
      e.toLinearEquiv.symm.conj (pointFrobeniusStalkMap B f Λ G y hres x) :=
    LinearMap.ext fun v => congrArg (fun g => g.hom v) hfrob
  rw [h, ProjectiveDeterminant.charSeries_conj, returnMap_eq_conj]
  exact ProjectiveDeterminant.charSeries_conj _ _ _

end Stacks.EtaleCohomology

end
