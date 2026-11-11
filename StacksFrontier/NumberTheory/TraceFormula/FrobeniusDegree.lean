module

public import Mathlib.FieldTheory.Finite.Extension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldBaseChangeGeometry
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusElementDegree
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FrobeniusSplitting.LocalFrobeniusAction
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.OpenSubgroups
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricIrreducibleComponents.ConnectedComponents
public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.GaloisSide
public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.PlacesOver
public import StacksFrontier.NumberTheory.TraceFormula.GeometricMonodromyFiniteness

/-!
# Frobenius elements and the degrees of closed points

Let `k` be a finite field, `K` an algebraic closure of `k` and `X` a geometrically irreducible
curve over `k`, with a geometric point `x̄` of `X_K` and its image in `X`. This file relates the
Frobenius elements of `π₁(X)` to the degrees `deg y = [κ(y) : k]` of the closed points `y` of
`X`, and the closed points of a smooth curve to the places of its function field.

* For every `M > 0` there is an open subgroup `U` of `π₁(X)` containing the image of the
  geometric fundamental group `π₁(X_K)`, such that `M ∣ deg y` whenever a Frobenius element at
  `y` lies in `U`. It is the preimage of the stabilizer of a point of the geometric fibre of
  `Spec k_M ⟶ Spec k`, `k_M` the extension of degree `M`: a Frobenius element at `y` acts on that
  fibre as the `deg y`-th power of the Frobenius of `k`, which fixes a `k`-embedding
  `k_M → Ω` exactly when `M ∣ deg y`.
* Every Frobenius element at a closed point `y` is the Frobenius element given by the algebraic
  closure `AlgebraicClosure κ(y)` and a suitable path, since any two algebraic closures of
  `κ(y)` are isomorphic compatibly with the arithmetic Frobenius.
* At a closed point `y` of a smooth curve the local ring is a discrete valuation ring, so `y` is
  the centre of a place `v` of the function field, and every Frobenius element at `y` is the
  inverse of a geometric Frobenius element at `v`. The residue field of `v` is `κ(y)`, which
  has `#k ^ deg y` elements.

## Main results

* `Stacks.TraceFormula.exists_isOpen_subgroup_dvd_residueDegree` — the open subgroup `U`.
* `Stacks.TraceFormula.exists_frobeniusDataOfPath_element_eq` — every Frobenius element comes
  from `AlgebraicClosure κ(y)` and a path.
* `Stacks.TraceFormula.exists_isCentreOf_isGeometricFrobeniusAt_inv` — a closed point is the
  centre of a place at which the inverse of each of its Frobenius elements is a geometric
  Frobenius element.
* `Stacks.TraceFormula.resCard_eq_natCard_residueField_of_isCentreOf` — the residue field of a
  place has as many elements as the residue field of its centre.
* `Stacks.TraceFormula.natCard_residueField_eq_pow_residueDegree` — `#κ(y) = #k ^ deg y`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.TraceFormula

/-! ### Frobenius elements from the standard algebraic closure -/

section ChangeClosure

/-- An isomorphism `α : t.source ≅ s.source` of the sources of two geometric points of `X`
compatible with the maps to `X` induces an isomorphism of geometric fibre functors: a lift
`q` of `s` goes to the lift `α ≫ q` of `t`. -/
def finiteEtaleFiberIsoOfSourceIso {X : Scheme.{u}} {s t : GeometricPoint X}
    (α : t.source ≅ s.source) (hα : α.hom ≫ s.hom = t.hom) :
    finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor t :=
  NatIso.ofComponents (fun V => Equiv.toIso
    { toFun := fun q => ⟨α.hom ≫ q.1, by rw [Category.assoc, q.2, hα]⟩
      invFun := fun q => ⟨α.inv ≫ q.1, by
        rw [Category.assoc, q.2]
        exact (Iso.inv_comp_eq α).2 hα.symm⟩
      left_inv := fun q => Subtype.ext (by simp)
      right_inv := fun q => Subtype.ext (by simp) })
    (fun {V W} g => by
      ext q
      exact Subtype.ext (Category.assoc _ _ _).symm)

/-- `finiteEtaleFiberIsoOfSourceIso α hα` sends a lift `q` to `α ≫ q`. -/
theorem finiteEtaleFiberIsoOfSourceIso_hom_app_coe {X : Scheme.{u}} {s t : GeometricPoint X}
    (α : t.source ≅ s.source) (hα : α.hom ≫ s.hom = t.hom) (V : FiniteEtaleOver X)
    (q : finiteEtaleFiber s V) :
    (((finiteEtaleFiberIsoOfSourceIso α hα).hom.app V) q).1 = α.hom ≫ q.1 :=
  rfl

/-- The inverse of `finiteEtaleFiberIsoOfSourceIso α hα` sends a lift `q` to `α⁻¹ ≫ q`. -/
theorem finiteEtaleFiberIsoOfSourceIso_inv_app_coe {X : Scheme.{u}} {s t : GeometricPoint X}
    (α : t.source ≅ s.source) (hα : α.hom ≫ s.hom = t.hom) (V : FiniteEtaleOver X)
    (q : finiteEtaleFiber t V) :
    (((finiteEtaleFiberIsoOfSourceIso α hα).inv.app V) q).1 = α.inv ≫ q.1 :=
  rfl

variable {X : Scheme.{u}} {y : closedPoints X}

/-- The geometric point of `X` over the closed point `y` given by an algebraic closure `Ω` of
`κ(y)`. -/
abbrev closureGeometricPoint (y : closedPoints X) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    [Algebra (X.residueField y.1) Ω] : GeometricPoint X :=
  (algebraicClosureGeometricPoint (X.residueField y.1) Ω).map (X.fromSpecResidueField y.1)

/-- A `κ(y)`-algebra map `Ω → Ω'` of algebraic closures commutes with the geometric points over
`y`. -/
theorem specMap_comp_closureGeometricPoint_hom {Ω Ω' : Type u} [Field Ω] [Field Ω']
    [IsAlgClosed Ω] [IsAlgClosed Ω'] [Algebra (X.residueField y.1) Ω]
    [Algebra (X.residueField y.1) Ω'] (e : Ω →ₐ[X.residueField y.1] Ω') :
    Spec.map (CommRingCat.ofHom (e : Ω →+* Ω')) ≫ (closureGeometricPoint y Ω).hom =
      (closureGeometricPoint y Ω').hom := by
  change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (X.residueField y.1) Ω)) ≫
      X.fromSpecResidueField y.1 =
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField y.1) Ω')) ≫ _
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap]

/-- The isomorphism `Spec Ω' ≅ Spec Ω` induced by a ring isomorphism `e : Ω ≃ Ω'`. -/
def specFieldIsoOfRingEquiv {Ω Ω' : Type u} [Field Ω] [Field Ω'] (e : Ω ≃+* Ω') :
    Spec (.of Ω') ≅ Spec (.of Ω) where
  hom := Spec.map (CommRingCat.ofHom (e : Ω →+* Ω'))
  inv := Spec.map (CommRingCat.ofHom (e.symm : Ω' →+* Ω))
  hom_inv_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (e : Ω →+* Ω').comp (e.symm : Ω' →+* Ω) = RingHom.id Ω' :=
      RingHom.ext fun a => e.apply_symm_apply a
    rw [this]
    exact Spec.map_id _
  inv_hom_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (e.symm : Ω' →+* Ω).comp (e : Ω →+* Ω') = RingHom.id Ω :=
      RingHom.ext fun a => e.symm_apply_apply a
    rw [this]
    exact Spec.map_id _

variable [ConnectedSpace X] {base : GeometricPoint X}

omit [ConnectedSpace X] in
/-- The arithmetic Frobenius of `c.closure` raises to the power `#κ(y)`. -/
theorem frobenius_apply_eq_pow (c : FrobeniusData base y) (a : c.closure) :
    c.frobenius a = a ^ Nat.card (X.residueField y.1) := by
  have : Finite (X.residueField y.1) := c.finite_residueField
  let _ : Fintype (X.residueField y.1) := Fintype.ofFinite _
  change FiniteField.frobeniusAlgEquivOfAlgebraic (X.residueField y.1) c.closure a = _
  rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, Nat.card_eq_fintype_card]

omit [ConnectedSpace X] in
/-- Conjugating the arithmetic Frobenius along an isomorphism of algebraic closures gives the
arithmetic Frobenius: `Spec e ≫ Spec φ ≫ Spec e⁻¹ = Spec φ'`. -/
theorem specMap_frobenius_conj (c c' : FrobeniusData base y)
    (e : c.closure ≃ₐ[X.residueField y.1] c'.closure) :
    Spec.map (CommRingCat.ofHom (e : c.closure →+* c'.closure)) ≫
        Spec.map (CommRingCat.ofHom (c.frobenius : c.closure →+* c.closure)) ≫
          Spec.map (CommRingCat.ofHom (e.symm : c'.closure →+* c.closure)) =
      Spec.map (CommRingCat.ofHom (c'.frobenius : c'.closure →+* c'.closure)) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun a => ?_
  change e (c.frobenius (e.symm a)) = c'.frobenius a
  rw [frobenius_apply_eq_pow c, frobenius_apply_eq_pow c', map_pow, AlgEquiv.apply_symm_apply]

/-- **Frobenius elements come from the standard algebraic closure.** Every Frobenius element at
a closed point `y` is the Frobenius element given by `AlgebraicClosure κ(y)` and some path. -/
theorem exists_frobeniusDataOfPath_element_eq (c : FrobeniusData base y) :
    letI : Finite (X.residueField y.1) := c.finite_residueField
    ∃ t : finiteEtaleFiberFunctor (Stacks.Frobenius.geometricPointAt X y.1) ≅
        finiteEtaleFiberFunctor base,
      (Stacks.EtaleCohomology.frobeniusDataOfPath base y t).element = c.element := by
  have : Algebra.IsAlgebraic (X.residueField y.1) c.closure :=
    Algebra.IsSeparable.isAlgebraic _ _
  have : IsAlgClosure (X.residueField y.1) c.closure := ⟨inferInstance, inferInstance⟩
  let e := IsAlgClosure.equiv (X.residueField y.1) (AlgebraicClosure (X.residueField y.1)) c.closure
  have : Finite (X.residueField y.1) := c.finite_residueField
  let α : c.geometricPoint.source ≅ (Stacks.Frobenius.geometricPointAt X y.1).source :=
    specFieldIsoOfRingEquiv e.toRingEquiv
  have hα : α.hom ≫ (Stacks.Frobenius.geometricPointAt X y.1).hom = c.geometricPoint.hom :=
    specMap_comp_closureGeometricPoint_hom e.toAlgHom
  let s := finiteEtaleFiberIsoOfSourceIso α hα
  let c₀ := Stacks.EtaleCohomology.frobeniusDataOfPath base y (s ≪≫ c.path)
  refine ⟨s ≪≫ c.path, (Iso.trans_conjAut s c.path c₀.localElement).trans ?_⟩
  change c.path.conjAut (s.conjAut c₀.localElement) = c.path.conjAut c.localElement
  congr 1
  refine Aut.ext (Iso.ext (NatTrans.ext (funext fun V => ?_)))
  ext q
  apply Subtype.ext
  exact (congrArg Subtype.val (Stacks.FundamentalGroup.conjAut_app_apply_inv s _ V q)).trans <|
    (congrArg (α.hom ≫ ·) (FrobeniusData.localElement_app_apply c₀ V (s.inv.app V q))).trans <|
    (congrArg (α.hom ≫ ·) (Category.assoc _ α.inv q.1).symm).trans <|
    (Category.assoc α.hom _ q.1).symm.trans <|
    (congrArg (· ≫ q.1) ((Category.assoc _ _ _).symm.trans (specMap_frobenius_conj c₀ c e))).trans
    (FrobeniusData.localElement_app_apply c V q).symm

end ChangeClosure

/-! ### Closed points and places -/

section Places

open Stacks.Adeles Stacks.Adeles.GlobalFunctionField

variable {X : Scheme.{u}} [IsIntegral X]

/-- The local ring at a point whose stalk is a discrete valuation ring is a proper valuation
subring of the function field. -/
theorem stalkValuationSubring_ne_top (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    Stacks.BombieriStepanov.stalkValuationSubring x ≠ ⊤ := by
  intro htop
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk x)
  have hne : algebraMap (X.presheaf.stalk x) X.functionField ϖ ≠ 0 := fun h =>
    hϖ.ne_zero (IsFractionRing.injective (X.presheaf.stalk x) X.functionField
      (h.trans (map_zero _).symm))
  have hmem : (algebraMap (X.presheaf.stalk x) X.functionField ϖ)⁻¹ ∈
      Stacks.BombieriStepanov.stalkValuationSubring x := htop ▸ ValuationSubring.mem_top _
  obtain ⟨a, ha⟩ := hmem
  have h1 : ϖ * a = 1 := IsFractionRing.injective (X.presheaf.stalk x) X.functionField <| by
    rw [map_mul, map_one]
    exact (congrArg _ ha).trans (mul_inv_cancel₀ hne)
  exact hϖ.not_isUnit ⟨⟨ϖ, a, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

/-- The place of the function field given by the local ring at a point whose stalk is a
discrete valuation ring. -/
def stalkPlace (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    Place X.functionField :=
  ⟨Stacks.BombieriStepanov.stalkValuationSubring x, stalkValuationSubring_ne_top x⟩

/-- A point whose stalk is a discrete valuation ring is the centre of its place. -/
theorem isCentreOf_stalkPlace (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    IsCentreOf (stalkPlace x) x := fun _ => Iff.rfl

/-- **The residue field of a place is that of its centre**: if `x` is the centre of `v`, then
`#κ_v = #κ(x)`. -/
theorem resCard_eq_natCard_residueField_of_isCentreOf {v : Place X.functionField} {x : X}
    (hv : IsCentreOf v x) : v.resCard = Nat.card (X.residueField x) := by
  let e : X.presheaf.stalk x ≃+* v.1 := RingEquiv.ofBijective
    ((algebraMap (X.presheaf.stalk x) X.functionField).codRestrict v.1.toSubring
      fun a => (hv _).2 ⟨a, rfl⟩)
    ⟨fun a b h => IsFractionRing.injective (X.presheaf.stalk x) X.functionField
      (congrArg Subtype.val h), fun ⟨g, hg⟩ => by
        obtain ⟨a, ha⟩ := (hv g).1 hg
        exact ⟨a, Subtype.ext ha⟩⟩
  exact (Nat.card_congr (IsLocalRing.ResidueField.mapEquiv e).toEquiv).symm

omit [IsIntegral X] in
/-- **A closed point of a scheme of finite type over a finite field has `#k ^ deg y` residue
elements.** -/
theorem natCard_residueField_eq_pow_residueDegree {k : Type u} [Field k] [Finite k]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (y : closedPoints X) :
    Nat.card (X.residueField y.1) =
      Nat.card k ^ Stacks.EtaleCohomology.residueDegree f y.1 := by
  have := Stacks.EtaleCohomology.finite_residueField f y.1 y.2
  let : Algebra k (X.residueField y.1) := (fieldToResidue f y.1).hom.toAlgebra
  have : Module.Finite k (X.residueField y.1) := Module.Finite.of_finite
  exact Module.natCard_eq_pow_finrank (K := k)

variable [ConnectedSpace X]

/-- **Frobenius elements at a closed point are geometric Frobenius elements at a place.** On a
smooth curve every closed point `y` is the centre of a place `v`, and for every Frobenius
element `F` at `y` the inverse `F⁻¹` is a geometric Frobenius element at `v`. -/
theorem exists_isCentreOf_isGeometricFrobeniusAt_inv {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] {base : GeometricPoint X}
    (y : closedPoints X) (c : FrobeniusData base y) :
    ∃ v : Place X.functionField, IsCentreOf v y.1 ∧
      IsGeometricFrobeniusAt base v c.element⁻¹ := by
  have := IsCurve.isDiscreteValuationRing_stalk_of_isClosed k f y.2
  have : Finite (X.residueField y.1) := c.finite_residueField
  obtain ⟨t, ht⟩ := exists_frobeniusDataOfPath_element_eq c
  exact ⟨stalkPlace y.1, isCentreOf_stalkPlace y.1, y, isCentreOf_stalkPlace y.1, inferInstance,
    t, by rw [ht]⟩

end Places

/-! ### An open subgroup detecting divisibility of degrees -/

section Degree

/-- If every element of a finite extension `L` of a finite field `k` is fixed by
`a ↦ a ^ (#k ^ d)`, then `[L : k] ∣ d`: the Frobenius of `L / k` has order `[L : k]`. -/
theorem finrank_dvd_of_forall_pow_eq {k L : Type*} [Field k] [Fintype k] [Field L] [Algebra k L]
    [Finite L] {d : ℕ} (h : ∀ a : L, a ^ (Fintype.card k ^ d) = a) :
    Module.finrank k L ∣ d := by
  rw [← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic k L]
  refine orderOf_dvd_of_pow_eq_one (AlgEquiv.ext fun a => ?_)
  rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, AlgEquiv.one_apply]
  exact h a

/-- The spectrum of a finite extension of a finite field is finite étale over it. -/
theorem finiteEtale_specMap_algebraMap {k : Type u} [Field k] [Finite k]
    (L : Type u) [Field L] [Algebra k L] [Finite L] :
    finiteEtale (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
  have : Module.Finite k L := Module.Finite.of_finite
  refine ⟨?_, ?_⟩
  · rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  · have : Algebra.FinitePresentation k L :=
      (Algebra.FinitePresentation.of_finiteType (R := k) (A := L)).mp inferInstance
    have : Algebra.FormallyEtale k L := Algebra.FormallyEtale.of_isSeparable k L
    have : Algebra.Etale k L := ⟨inferInstance, inferInstance⟩
    exact HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)

variable {k : Type u} [Field k] [Fintype k] (p n : ℕ) [Fact p.Prime] [CharP k p]
  (hq : Fintype.card k = p ^ n)

include hq in
/-- **An open subgroup of `π₁(Spec k)` detecting `M ∣ d`.** For every `M > 0` there is an open
subgroup of `π₁(Spec k, z)` such that `M ∣ d` whenever it contains the power `Φ ^ d` of the
Frobenius of `k`: the stabilizer of a point of the geometric fibre of `Spec k_M`, where `k_M` is the
extension of degree `M`. -/
theorem exists_isOpen_finiteFieldFrobenius_pow_mem (z : GeometricPoint (Spec (.of k))) (M : ℕ)
    [NeZero M] :
    ∃ W : Subgroup (EtaleFundamentalGroup (Spec (.of k)) z),
      IsOpen (W : Set (EtaleFundamentalGroup (Spec (.of k)) z)) ∧
        ∀ d : ℕ, finiteFieldFrobenius p n hq z ^ d ∈ W → M ∣ d := by
  let L := ULift.{u} (FiniteField.Extension k p M)
  let Y : FiniteEtaleOver (Spec (.of k)) :=
    MorphismProperty.Over.mk ⊤ (Spec.map (CommRingCat.ofHom (algebraMap k L)))
      (finiteEtale_specMap_algebraMap L)
  let : Algebra k z.residueField := (Spec.preimage z.hom).hom.toAlgebra
  let φ : L →ₐ[k] z.residueField := IsAlgClosed.lift
  let y₀ : (finiteEtaleFiberFunctor z).obj Y :=
    ⟨Spec.map (CommRingCat.ofHom (φ : L →+* z.residueField)), by
      change Spec.map _ ≫ Spec.map _ = z.hom
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap]
      exact Spec.map_preimage z.hom⟩
  refine ⟨MulAction.stabilizer _ y₀,
    EtaleFundamentalGroup.isOpen_coe_of_isOpenSubgroup ⟨Y, y₀, rfl⟩, fun d hd => ?_⟩
  rw [MulAction.mem_stabilizer_iff] at hd
  have := z.charP_residueField p
  have h1 := finiteFieldFrobenius_pow_app_coe_specMap p n hq z d Y y₀
  have h2 : Spec.map (CommRingCat.ofHom (iterateFrobenius z.residueField p (n * d))) ≫
      Spec.map (CommRingCat.ofHom (φ : L →+* z.residueField)) =
      Spec.map (CommRingCat.ofHom (φ : L →+* z.residueField)) :=
    h1.symm.trans (congrArg Subtype.val hd)
  rw [← Spec.map_comp] at h2
  have h3 := congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
  have hfix : ∀ a : L, a ^ (Fintype.card k ^ d) = a := fun a => by
    apply φ.injective
    have h4 := RingHom.congr_fun h3 a
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h4
    rw [iterateFrobenius_def] at h4
    rw [map_pow, hq, ← pow_mul]
    exact h4
  have := finrank_dvd_of_forall_pow_eq hfix
  rwa [finrank_ulift, FiniteField.finrank_extension] at this

end Degree

section Curve

/-- An integral scheme is connected; pinned, since the general search for `ConnectedSpace X`
runs out of heartbeats with the imports of this file. -/
local instance (priority := 3000) connectedSpace_of_isIntegral_curve {X : Scheme.{u}}
    [IsIntegral X] : ConnectedSpace X :=
  inferInstance

variable (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [IsCurve k f] [GeometricallyIrreducible f]

omit [IsCurve k f] in
/-- The geometric curve of a geometrically irreducible scheme is connected. -/
theorem connectedSpace_pullback_of_geometricallyIrreducible :
    ConnectedSpace
      ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) :=
  have := geometricallyConnected_of_geometricallyIrreducible f
  connectedSpace_fieldBaseChange f K

/-- **Frobenius elements in an open subgroup containing the geometric fundamental group.** Let
`k` be a finite field, `K` an algebraically closed extension and `X` a geometrically irreducible
curve over `k`, with base point the image of a geometric point `x̄` of `X_K`. For every `M > 0`
there is an open subgroup `U` of `π₁(X)` containing the image of `π₁(X_K)` such that `M` divides
the degree of a closed point `y` whenever a Frobenius element at `y` lies in `U`. -/
theorem exists_isOpen_subgroup_dvd_residueDegree [Finite k] [IsAlgClosed K]
    (x : GeometricPoint (geometricBaseChange k K f)) (M : ℕ) (hM : 0 < M) :
    ∃ U : Subgroup (EtaleFundamentalGroup X (x.map (geometricProjection k K f))),
      IsOpen (U : Set (EtaleFundamentalGroup X (x.map (geometricProjection k K f)))) ∧
      (∀ g, etaleFundamentalGroupMap (geometricProjection k K f) x g ∈ U) ∧
      ∀ (y : closedPoints X) (c : FrobeniusData (x.map (geometricProjection k K f)) y),
        c.element ∈ U → M ∣ Stacks.EtaleCohomology.residueDegree f y.1 := by
  have := connectedSpace_pullback_of_geometricallyIrreducible k K f
  let _ : Fintype k := Fintype.ofFinite k
  obtain ⟨n, hp, hq⟩ := FiniteField.card k (ringChar k)
  have : Fact (ringChar k).Prime := ⟨hp⟩
  have : NeZero M := ⟨hM.ne'⟩
  obtain ⟨W, hWo, hW⟩ := exists_isOpen_finiteFieldFrobenius_pow_mem (ringChar k) n hq
    ((x.map (geometricProjection k K f)).map f) M
  refine ⟨W.comap (etaleFundamentalGroupMap f (x.map (geometricProjection k K f))).toMonoidHom,
    (etaleFundamentalGroupMap f _).continuous.isOpen_preimage _ hWo, fun g => ?_,
    fun y c hc => ?_⟩
  · have h := DFunLike.congr_fun (etaleFundamentalGroupMap_comp_eq_one_isAlgClosed k K f x) g
    change etaleFundamentalGroupMap f _ (etaleFundamentalGroupMap _ x g) ∈ W
    exact (show _ = (1 : EtaleFundamentalGroup _ _) from h) ▸ W.one_mem
  · have : Finite (X.residueField y.1) := c.finite_residueField
    obtain ⟨t, ht⟩ := exists_frobeniusDataOfPath_element_eq c
    rw [← ht] at hc
    have h := etaleFundamentalGroupMap_element_frobeniusDataOfPath (ringChar k) n hq f
      (x.map (geometricProjection k K f)) y t
    exact hW _ (h ▸ hc)

end Curve

end Stacks.TraceFormula

end
