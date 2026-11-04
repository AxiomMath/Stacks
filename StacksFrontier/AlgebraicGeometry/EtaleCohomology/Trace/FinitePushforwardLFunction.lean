module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FinitePushforwardReturnMap

/-!
# The L-function of a finite direct image

Let `f : X ⟶ Y` be a finite morphism of a big étale site, `Y` locally of finite type and
quasi-compact over a finite field `k`, and `G` a sheaf of modules over a commutative ring `Λ` on
`X_étale` with finite projective stalks. Then `f_* G` has finite projective stalks, and
`L(Y, f_* G) = L(X, G)`: the local factor of `f_* G` at a closed point `y` is the product of
the local factors of `G` at the points over `y`, with `deg x = deg y · [κ(x) : κ(y)]`, and the
Euler products regroup along the fibres.

## Main results

* `Stacks.EtaleCohomology.EulerSystem.eulerProduct_eq_of_fibres`: Euler products regroup along a
  map of index sets with finite fibres.
* `Stacks.EtaleCohomology.lFunctionOfFiniteProjectiveStalks_moduleDirectImage`:
  `L(Y, f_* G) = L(X, G)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Stacks.Frobenius

universe u v w w'

namespace Stacks.EtaleCohomology

/-- **Euler products regroup along the fibres of a map of index sets.** If the factor of `E'` at
`j` is the product of the factors of `E` over the finite fibre of `p` at `j`, and `p` does not
raise degrees, the two Euler products agree. -/
public theorem EulerSystem.eulerProduct_eq_of_fibres {Λ : Type v} [CommRing Λ] {ι : Type w}
    {ι' : Type w'} (E : EulerSystem Λ ι) (E' : EulerSystem Λ ι') (p : ι → ι')
    (fib : ι' → Finset ι) (hfib : ∀ i j, i ∈ fib j ↔ p i = j) (hdeg : ∀ i, E'.deg (p i) ≤ E.deg i)
    (hfac : ∀ j, E'.factor j = ∏ i ∈ fib j, E.factor i) :
    E'.eulerProduct = E.eulerProduct := by
  classical
  ext n
  rw [E'.coeff_eulerProduct_eq (t := E'.support n) subset_rfl,
    E.coeff_eulerProduct_eq (t := (E'.support n).biUnion fib) ?_]
  · rw [Finset.prod_biUnion]
    · exact congrArg _ (Finset.prod_congr rfl fun j _ => hfac j)
    · intro j _ j' _ hjj'
      exact Finset.disjoint_left.2 fun i hi hi' =>
        hjj' (((hfib i j).1 hi).symm.trans ((hfib i j').1 hi'))
  · intro i hi
    rw [Finset.mem_biUnion]
    exact ⟨p i, E'.mem_support.2 ((hdeg i).trans (E.mem_support.1 hi)), (hfib i (p i)).2 rfl⟩

/-- The structural map to a residue field of a composite. -/
public theorem fieldToResidue_comp {k : Type u} [Field k] {Z W : Scheme.{u}} (g : Z ⟶ W)
    (h : W ⟶ Spec (.of k)) (z : Z) :
    fieldToResidue (g ≫ h) z = fieldToResidue h (g z) ≫ g.residueFieldMap z := by
  simp only [fieldToResidue, fieldToStalk, Scheme.Hom.comp_appTop, Category.assoc,
    Scheme.residue_residueFieldMap]
  congr 2
  exact (g.germ_stalkMap_assoc ⊤ z trivial _).symm

section Points

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) {k : Type u} [Field k]
  (fY : Y.1 ⟶ Spec (.of k))

/-- **The degree is multiplicative in a finite cover**: `deg x = deg y · [κ(x) : κ(y)]`. -/
public theorem residueDegree_comp (y : Y.1) (x : {x : X.1 // (fS B f) x = y}) :
    residueDegree (fS B f ≫ fY) x.1 = residueDegree fY y * fiberDegree B f y x := by
  obtain ⟨x, rfl⟩ := x
  let : Algebra k (Y.1.residueField ((fS B f) x)) :=
    (fieldToResidue fY ((fS B f) x)).hom.toAlgebra
  let : Algebra k (X.1.residueField x) := (fieldToResidue (fS B f ≫ fY) x).hom.toAlgebra
  let := fiberResidueAlgebra (fS B f) ((fS B f) x) ⟨x, rfl⟩
  have : IsScalarTower k (Y.1.residueField ((fS B f) x)) (X.1.residueField x) := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    show (fieldToResidue (fS B f ≫ fY) x).hom r = _
    rw [fieldToResidue_comp]
    rfl
  exact (Module.finrank_mul_finrank k (Y.1.residueField ((fS B f) x)) (X.1.residueField x)).symm

variable [IsFinite (fS B f)] [LocallyOfFiniteType fY]

include fY in
/-- A finite morphism of schemes locally of finite type over a field maps closed points to closed
points. -/
public theorem isClosed_singleton_fS {x : X.1} (hx : IsClosed ({x} : Set X.1)) :
    IsClosed ({(fS B f) x} : Set Y.1) := by
  have : JacobsonSpace Y.1 := LocallyOfFiniteType.jacobsonSpace fY
  exact (fS B f).closePoints_subset_preimage_closedPoints hx

include fY in
/-- The points of a finite cover over a closed point of a scheme locally of finite type over a
field are closed. -/
public theorem isClosed_singleton_of_fS {x : X.1} (hx : IsClosed ({(fS B f) x} : Set Y.1)) :
    IsClosed ({x} : Set X.1) := by
  have : JacobsonSpace Y.1 := LocallyOfFiniteType.jacobsonSpace fY
  have : JacobsonSpace X.1 := LocallyOfFiniteType.jacobsonSpace (fS B f ≫ fY)
  rw [isClosed_singleton_iff_locallyOfFiniteType] at hx ⊢
  let m := ((fS B f).residueFieldMap x).hom
  let : Algebra (Y.1.residueField ((fS B f) x)) (X.1.residueField x) := m.toAlgebra
  have hm : m.QuasiFinite := by
    apply RingHom.QuasiFinite.of_comp (g := (Y.1.residue ((fS B f) x)).hom)
    rw [← CommRingCat.hom_comp, Scheme.residue_residueFieldMap]
    exact (RingHom.QuasiFinite.of_finite (RingHom.Finite.of_surjective _
      IsLocalRing.residue_surjective)).comp ((fS B f).quasiFiniteAt x)
  have : Algebra.QuasiFinite (Y.1.residueField ((fS B f) x)) (X.1.residueField x) := hm
  have : Module.Finite (Y.1.residueField ((fS B f) x)) (X.1.residueField x) := .of_quasiFinite
  have hft : LocallyOfFiniteType (Spec.map ((fS B f).residueFieldMap x)) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.Finite.finiteType (show m.Finite from ‹_›)
  have hcomp : LocallyOfFiniteType (X.1.fromSpecResidueField x ≫ fS B f) := by
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    infer_instance
  exact locallyOfFiniteType_of_comp _ (fS B f)

end Points

/-! ### The local factors of a finite direct image -/

section LocalFactor

attribute [local instance] ModuleCat.hasLimitsOfSize

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) [IsFinite (fS B f)] (Λ : Type)
  [CommRing Λ] (G : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} Λ))
  (hfin : ∀ s : GeometricPoint X.1,
    Module.Finite Λ ((etaleModuleStalkFunctor.{u, u + 1, 0} B X Λ s).obj G))
  (hproj : ∀ s : GeometricPoint X.1,
    Module.Projective Λ ((etaleModuleStalkFunctor.{u, u + 1, 0} B X Λ s).obj G))
  {k : Type u} [Field k] [Finite k] (fY : Y.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fY]

/-- **The Frobenius of `f_* G` at a closed point**, read on Mathlib's small étale site, has the
local factor of the stalk map of `f_* G` along the geometric Frobenius of `ȳ`. -/
public theorem charSeries_closedPointFrobenius_moduleDirectImage (y : closedPoints Y.1) (n : ℕ) :
    haveI := finite_residueField fY y.1 y.2
    haveI := finite_sheafFiber_sheafEquiv.{u, u + 1, 0} B Y Λ (geometricPointAt Y.1 y.1)
      (moduleDirectImage B f Λ G) (finite_etaleModuleStalk_moduleDirectImage B f Λ G hfin _)
    haveI := projective_sheafFiber_sheafEquiv.{u, u + 1, 0} B Y Λ (moduleDirectImage B f Λ G)
      (geometricPointAt Y.1 y.1) (projective_etaleModuleStalk_moduleDirectImage B f Λ G hproj _)
    haveI : Module.Finite Λ (pushforwardStalkAt B f Λ G y.1) :=
      finite_etaleModuleStalk_moduleDirectImage B f Λ G hfin _
    haveI : Module.Projective Λ (pushforwardStalkAt B f Λ G y.1) :=
      projective_etaleModuleStalk_moduleDirectImage B f Λ G hproj _
    ProjectiveDeterminant.charSeries
        (closedPointFrobenius.{u, u + 1, 0} B Y Λ (moduleDirectImage B f Λ G) fY y) n =
      ProjectiveDeterminant.charSeries
        (pushforwardStalkGalois B f Λ G y.1 (residueGeometricFrobenius Y.1 y.1)) n := by
  have := finite_residueField fY y.1 y.2
  have := finite_sheafFiber_sheafEquiv.{u, u + 1, 0} B Y Λ (geometricPointAt Y.1 y.1)
    (moduleDirectImage B f Λ G) (finite_etaleModuleStalk_moduleDirectImage B f Λ G hfin _)
  have := projective_sheafFiber_sheafEquiv.{u, u + 1, 0} B Y Λ (moduleDirectImage B f Λ G)
    (geometricPointAt Y.1 y.1) (projective_etaleModuleStalk_moduleDirectImage B f Λ G hproj _)
  have : Module.Finite Λ (pushforwardStalkAt B f Λ G y.1) :=
    finite_etaleModuleStalk_moduleDirectImage B f Λ G hfin _
  have : Module.Projective Λ (pushforwardStalkAt B f Λ G y.1) :=
    projective_etaleModuleStalk_moduleDirectImage B f Λ G hproj _
  let e := (sheafEquivCompSheafFiberIso.{u, u + 1, 0} B Y Λ (geometricPointAt Y.1 y.1)).app
    (moduleDirectImage B f Λ G)
  have hnat : e.inv ≫ frobeniusStalk (ModuleCat.{u + 1} Λ) Y.1 y.1
      ((SmallEtale.sheafEquiv B Y.1 Y.property (ModuleCat.{u + 1} Λ)).functor.obj
        (moduleDirectImage B f Λ G)) =
      (geometricPointStalkMap B Y.1 Y.property (frobeniusPointHom Y.1 y.1)
        (ModuleCat.{u + 1} Λ)).app (moduleDirectImage B f Λ G).obj ≫ e.inv := by
    have h := NatTrans.congr_app (sheafEquivCompSheafFiberIso_inv_naturality.{u, u + 1, 0} B Y
      Λ (frobeniusPointHom Y.1 y.1)) (moduleDirectImage B f Λ G)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
    exact h
  have hfr : frobeniusPointHom Y.1 y.1 = galoisPow B y.1 (residueGeometricFrobenius Y.1 y.1) 1 := by
    show _ = galoisPointHom _ (residueGeometricFrobenius Y.1 y.1 ^ 1) _
    rw [pow_one]
    rfl
  rw [hfr] at hnat
  have hfrob : frobeniusStalk (ModuleCat.{u + 1} Λ) Y.1 y.1
      ((SmallEtale.sheafEquiv B Y.1 Y.property (ModuleCat.{u + 1} Λ)).functor.obj
        (moduleDirectImage B f Λ G)) =
      e.hom ≫ (geometricPointStalkMap B Y.1 Y.property
        (galoisPow B y.1 (residueGeometricFrobenius Y.1 y.1) 1)
        (ModuleCat.{u + 1} Λ)).app (moduleDirectImage B f Λ G).obj ≫ e.inv :=
    (Iso.hom_inv_id_assoc e _).symm.trans (congrArg (e.hom ≫ ·) hnat)
  have h : closedPointFrobenius.{u, u + 1, 0} B Y Λ (moduleDirectImage B f Λ G) fY y =
      e.toLinearEquiv.symm.conj
        (pushforwardStalkGalois B f Λ G y.1 (residueGeometricFrobenius Y.1 y.1)) :=
    LinearMap.ext fun v => congrArg (fun g => g.hom v) hfrob
  rw [h]
  have := finite_etaleModuleStalk_moduleDirectImage B f Λ G hfin (geometricPointAt Y.1 y.1)
  have := projective_etaleModuleStalk_moduleDirectImage B f Λ G hproj (geometricPointAt Y.1 y.1)
  exact ProjectiveDeterminant.charSeries_conj _ _ _

/-- The map induced by `f` on closed points. -/
public def closedPointsMap (x : closedPoints X.1) : closedPoints Y.1 :=
  ⟨(fS B f) x.1, isClosed_singleton_fS B f fY x.2⟩

/-- The closed points over a closed point. -/
public def closedFiber (y : closedPoints Y.1) : Finset (closedPoints X.1) :=
  haveI := finite_residueField fY y.1 y.2
  letI := @Fintype.ofFinite _ (finite_fiber B f y.1 (finite_residueField_of_isFinite B f y.1))
  letI := Classical.decEq (closedPoints X.1)
  Finset.univ.image fun x : {x : X.1 // (fS B f) x = y.1} =>
    (⟨x.1, isClosed_singleton_of_fS B f fY (by rw [x.2]; exact y.2)⟩ : closedPoints X.1)

/-- A closed point of `X` lies in the closed fibre over `y` exactly when it maps to `y`. -/
public theorem mem_closedFiber (x : closedPoints X.1) (y : closedPoints Y.1) :
    x ∈ closedFiber B f fY y ↔ closedPointsMap B f fY x = y := by
  have := finite_residueField fY y.1 y.2
  let := @Fintype.ofFinite _ (finite_fiber B f y.1 (finite_residueField_of_isFinite B f y.1))
  simp only [closedFiber, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x', rfl⟩
    exact Subtype.ext x'.2
  · intro h
    exact ⟨⟨x.1, congrArg Subtype.val h⟩, rfl⟩

/-- **The local factor of `f_* G` at a closed point `y` is the product of the local factors of `G`
at the closed points over `y`.** -/
public theorem finiteProjectiveLocalCharSeries_moduleDirectImage (y : closedPoints Y.1) :
    finiteProjectiveLocalCharSeries.{u, u + 1, 0} B Y Λ (moduleDirectImage B f Λ G) fY
        (finite_etaleModuleStalk_moduleDirectImage B f Λ G hfin)
        (projective_etaleModuleStalk_moduleDirectImage B f Λ G hproj) y =
      ∏ x ∈ closedFiber B f fY y,
        finiteProjectiveLocalCharSeries.{u, u + 1, 0} B X Λ G (fS B f ≫ fY) hfin hproj x := by
  have := finite_residueField fY y.1 y.2
  have hres := finite_residueField_of_isFinite B f y.1
  let := @Fintype.ofFinite _ (finite_fiber B f y.1 hres)
  let := Classical.decEq (closedPoints X.1)
  rw [finiteProjectiveLocalCharSeries, charSeries_closedPointFrobenius_moduleDirectImage B f Λ G
    hfin hproj fY y, charSeries_pushforwardStalkGalois B f Λ G y.1 hres hfin hproj, closedFiber,
    Finset.prod_image]
  swap
  · intro a _ b _ h
    exact Subtype.ext (congrArg (fun z : closedPoints X.1 => z.1) h)
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [charSeries_returnMap_eq_closedPointFrobenius B f Λ G y.1 hres x hfin hproj (fS B f ≫ fY)
    (isClosed_singleton_of_fS B f fY (by rw [x.2]; exact y.2)), finiteProjectiveLocalCharSeries,
    residueDegree_comp B f fY y.1 x]

/-- The local Euler factor of `f_* G` at `y` is the product of those of `G` over `y`. -/
public theorem finiteProjectiveLocalFactor_moduleDirectImage (y : closedPoints Y.1) :
    finiteProjectiveLocalFactor.{u, u + 1, 0} B Y Λ (moduleDirectImage B f Λ G) fY
        (finite_etaleModuleStalk_moduleDirectImage B f Λ G hfin)
        (projective_etaleModuleStalk_moduleDirectImage B f Λ G hproj) y =
      ∏ x ∈ closedFiber B f fY y,
        finiteProjectiveLocalFactor.{u, u + 1, 0} B X Λ G (fS B f ≫ fY) hfin hproj x := by
  have hY := finiteProjectiveLocalCharSeries_mul_localFactor.{u, u + 1, 0} B Y Λ
    (moduleDirectImage B f Λ G) fY (finite_etaleModuleStalk_moduleDirectImage B f Λ G hfin)
    (projective_etaleModuleStalk_moduleDirectImage B f Λ G hproj) y
  have hX := fun x => finiteProjectiveLocalCharSeries_mul_localFactor.{u, u + 1, 0} B X Λ G
    (fS B f ≫ fY) hfin hproj x
  rw [finiteProjectiveLocalCharSeries_moduleDirectImage B f Λ G hfin hproj fY y] at hY
  set P := ∏ x ∈ closedFiber B f fY y,
    finiteProjectiveLocalCharSeries.{u, u + 1, 0} B X Λ G (fS B f ≫ fY) hfin hproj x
  set Q := ∏ x ∈ closedFiber B f fY y,
    finiteProjectiveLocalFactor.{u, u + 1, 0} B X Λ G (fS B f ≫ fY) hfin hproj x
  set L := finiteProjectiveLocalFactor.{u, u + 1, 0} B Y Λ (moduleDirectImage B f Λ G) fY
    (finite_etaleModuleStalk_moduleDirectImage B f Λ G hfin)
    (projective_etaleModuleStalk_moduleDirectImage B f Λ G hproj) y
  have hPQ : P * Q = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun x _ => hX x
  calc L = L * (P * Q) := by rw [hPQ, mul_one]
    _ = (P * L) * Q := by ring
    _ = Q := by rw [hY, one_mul]

variable [QuasiCompact fY]

/-- **The L-function of a finite direct image.** For a finite morphism `f : X ⟶ Y`, `Y` locally of
finite type and quasi-compact over a finite field, and a sheaf `G` of modules over any commutative
ring `Λ` on `X_étale` with finite projective stalks, `f_* G` has finite projective stalks and
`L(Y, f_* G) = L(X, G)`. -/
public theorem lFunctionOfFiniteProjectiveStalks_moduleDirectImage :
    lFunctionOfFiniteProjectiveStalks.{u, u + 1, 0} B Y Λ (moduleDirectImage B f Λ G) fY
        (finite_etaleModuleStalk_moduleDirectImage B f Λ G hfin)
        (projective_etaleModuleStalk_moduleDirectImage B f Λ G hproj) =
      lFunctionOfFiniteProjectiveStalks.{u, u + 1, 0} B X Λ G (fS B f ≫ fY) hfin hproj := by
  refine EulerSystem.eulerProduct_eq_of_fibres _ _ (closedPointsMap B f fY) (closedFiber B f fY)
    (mem_closedFiber B f fY) (fun x => ?_)
    (finiteProjectiveLocalFactor_moduleDirectImage B f Λ G hfin hproj fY)
  have := finite_residueField fY _ (isClosed_singleton_fS B f fY x.2)
  have hres := finite_residueField_of_isFinite B f ((fS B f) x.1)
  show residueDegree fY ((fS B f) x.1) ≤ residueDegree (fS B f ≫ fY) x.1
  rw [residueDegree_comp B f fY ((fS B f) x.1) ⟨x.1, rfl⟩]
  exact Nat.le_mul_of_pos_right _ (fiberDegree_pos B f _ hres _)

/-- **`L(Y, f_* G) = L(X, G)` for a constructible flat `G`** (Tag 03UV on `X`): the L-function of
the finite direct image, with its finite projective stalks, is the L-function of `G`. -/
public theorem lFunctionOfFiniteProjectiveStalks_moduleDirectImage_eq_constructibleFlatLFunction
    [∀ (S T : B.Scheme) (g : T ⟶ S),
      ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{u + 1} Λ)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} Λ)]
    (hG : IsConstructibleFlatModuleSheaf B X Λ G) :
    lFunctionOfFiniteProjectiveStalks.{u, u + 1, 0} B Y Λ (moduleDirectImage B f Λ G) fY
        (finite_etaleModuleStalk_moduleDirectImage B f Λ G
          (finite_etaleModuleStalk_of_isConstructibleFlatModuleSheaf B X Λ G hG))
        (projective_etaleModuleStalk_moduleDirectImage B f Λ G
          (projective_etaleModuleStalk_of_isConstructibleFlatModuleSheaf B X Λ G hG)) =
      constructibleFlatLFunction B X Λ G (fS B f ≫ fY) hG :=
  lFunctionOfFiniteProjectiveStalks_moduleDirectImage B f Λ G _ _ fY

end LocalFactor

end Stacks.EtaleCohomology

end
