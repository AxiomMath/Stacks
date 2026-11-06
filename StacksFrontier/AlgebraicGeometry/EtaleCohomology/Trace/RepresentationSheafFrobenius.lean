module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LFunctionRationalSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricFrobeniusClosedPoint
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FrobeniusGeneration
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DeligneConjectureConclusions

/-!
# The geometric Frobenius on the stalks of `ℱ_ρ`

Let `X` be a connected scheme with a geometric point `x̄`, let `ρ : π₁(X, x̄) → GL_r(ℚ_ℓ)` be
continuous and let `ℱ_ρ` be the lisse sheaf of the notation preceding
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH). At a point `y` of `X` with finite residue
field the geometric Frobenius `π_y^*` acts on the stalk of `ℱ_ρ` at the geometric point `ȳ` over
`y`. The geometric Frobenius of `κ(y)` is an element of `π₁(Spec κ(y))`, whose image in
`π₁(X, ȳ)` is a geometric Frobenius element at `y`, and a path from `ȳ` to `x̄` carries it to an
element `F_y` of `π₁(X, x̄)`, well defined up to conjugation. The characteristic polynomial of
`π_y^*` on the stalk of `ℱ_ρ` is that of `ρ(F_y)`.

## Main definitions

* `Stacks.EtaleCohomology.localGeometricFrobenius`: the geometric Frobenius element of
  `π₁(X, ȳ)`.
* `Stacks.EtaleCohomology.geometricFrobeniusElement`: a geometric Frobenius element of
  `π₁(X, x̄)` at `y`, transported along a chosen path.
* `Stacks.EtaleCohomology.geometricFrobeniusFamily`: these elements at the closed points of a
  scheme of finite type over a finite field.

## Main results

* `Stacks.EtaleCohomology.charpoly_rationalStalkFrobenius_representationSheaf`: the
  characteristic polynomial of `π_y^*` on the rational stalk of `ℱ_ρ` is that of `ρ(F_y)`, for
  every path.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
  Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

section Element

variable {X : Scheme.{u}} [ConnectedSpace X] (base : GeometricPoint X) (y : closedPoints X)
  [Finite (X.residueField y.1)]

/-- The Frobenius data at a closed point `y` with finite residue field given by the algebraic
closure `AlgebraicClosure κ(y)`, whose geometric point is `geometricPointAt X y`, and a path from
it to the base point. -/
public def frobeniusDataOfPath
    (t : finiteEtaleFiberFunctor (geometricPointAt X y.1) ≅ finiteEtaleFiberFunctor base) :
    FrobeniusData base y where
  closure := AlgebraicClosure (X.residueField y.1)
  finite_residueField := inferInstance
  path := t

/-- The arithmetic Frobenius element of `π₁(X, ȳ)` acts on geometric fibres by precomposition with
the arithmetic Frobenius of `ȳ`. -/
public theorem localElement_app_coe
    (t : finiteEtaleFiberFunctor (geometricPointAt X y.1) ≅ finiteEtaleFiberFunctor base)
    (V : FiniteEtaleOver X) (q : finiteEtaleFiber (geometricPointAt X y.1) V) :
    (((frobeniusDataOfPath base y t).localElement.asIso.app V).hom q).1 =
      Spec.map (CommRingCat.ofHom (residueGeometricFrobenius X y.1).symm.toAlgHom.toRingHom) ≫
        q.1 := by
  let : Fintype (X.residueField y.1) := Fintype.ofFinite _
  refine (congrArg Subtype.val (etaleFundamentalGroupMonoidHom_app_apply
    (X.fromSpecResidueField y.1)
    (algebraicClosureGeometricPoint (X.residueField y.1) (AlgebraicClosure (X.residueField y.1)))
    V (galoisEquivEtaleFundamentalGroup (X.residueField y.1)
      (AlgebraicClosure (X.residueField y.1)) (AlgebraicClosure (X.residueField y.1))
      (FiniteField.frobeniusAlgEquivOfAlgebraic (X.residueField y.1)
        (AlgebraicClosure (X.residueField y.1)))) q)).trans ?_
  have hid : Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure (X.residueField y.1))
      (AlgebraicClosure (X.residueField y.1)))) = 𝟙 _ := by
    rw [Algebra.algebraMap_self]
    exact Spec.map_id _
  have hproj : ∀ p, (finiteEtaleFiberProjection (X.fromSpecResidueField y.1)
      (algebraicClosureGeometricPoint (X.residueField y.1) (AlgebraicClosure (X.residueField y.1)))
      V p).1 = p.1 ≫ pullback.fst V.hom (X.fromSpecResidueField y.1) := fun _ => rfl
  have hσ : FiniteField.frobeniusAlgEquivOfAlgebraic (X.residueField y.1)
      (AlgebraicClosure (X.residueField y.1)) = (residueGeometricFrobenius X y.1).symm := by
    ext z
    rw [residueGeometricFrobenius_symm_apply, FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
      Nat.card_eq_fintype_card]
  have hg := galoisEquivEtaleFundamentalGroup_apply (X.residueField y.1)
    (AlgebraicClosure (X.residueField y.1)) (AlgebraicClosure (X.residueField y.1))
    ((finiteEtaleBaseChange (X.fromSpecResidueField y.1)).obj V)
    (FiniteField.frobeniusAlgEquivOfAlgebraic (X.residueField y.1)
      (AlgebraicClosure (X.residueField y.1)))
    ((finiteEtaleFiberProjectionEquiv (X.fromSpecResidueField y.1)
      (algebraicClosureGeometricPoint (X.residueField y.1) (AlgebraicClosure (X.residueField y.1)))
      V).symm q)
    ((finiteEtaleFiberProjectionEquiv (X.fromSpecResidueField y.1)
      (algebraicClosureGeometricPoint (X.residueField y.1) (AlgebraicClosure (X.residueField y.1)))
      V).symm q).1 (by rw [hid]; exact (Category.id_comp _).symm)
  rw [hproj, hg, hid, Category.id_comp]
  refine (Category.assoc _ _ _).trans ?_
  rw [hσ]
  exact congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)

omit [ConnectedSpace X] in
/-- An automorphism of the fibre functor at `ȳ` acting by precomposition with the arithmetic
Frobenius has inverse acting by precomposition with the geometric Frobenius. -/
public theorem inv_hom_eq_finiteEtaleFiberMap_frobeniusPointHom
    (σ : Aut (finiteEtaleFiberFunctor (geometricPointAt X y.1)))
    (hσ : ∀ V q, ((σ.asIso.hom.app V) q).1 =
      Spec.map (CommRingCat.ofHom (residueGeometricFrobenius X y.1).symm.toAlgHom.toRingHom) ≫
        q.1) :
    σ⁻¹.asIso.hom = finiteEtaleFiberMap (frobeniusPointHom X y.1) := by
  apply NatTrans.ext
  funext V
  ext q
  have hinv' : ∀ z, σ.asIso.inv.app V (σ.asIso.hom.app V z) = z := fun z =>
    ConcreteCategory.congr_hom (σ.asIso.app V).hom_inv_id z
  show σ.asIso.inv.app V q = (finiteEtaleFiberMap (frobeniusPointHom X y.1)).app V q
  rw [← hinv' ((finiteEtaleFiberMap (frobeniusPointHom X y.1)).app V q)]
  congr 1
  apply Subtype.ext
  symm
  rw [hσ, finiteEtaleFiberMap_app_coe, frobeniusPointHom_hom, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have : (residueGeometricFrobenius X y.1).symm.toAlgHom.toRingHom.comp
      (residueGeometricFrobenius X y.1).toAlgHom.toRingHom = RingHom.id _ := by
    ext z
    exact (residueGeometricFrobenius X y.1).symm_apply_apply z
  rw [this, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

/-- The geometric Frobenius element of `π₁(X, ȳ)`, the inverse of the arithmetic one, acts on
geometric fibres by precomposition with the geometric Frobenius `frobeniusPointHom X y` of
`ȳ`. -/
public theorem inv_localElement_hom
    (t : finiteEtaleFiberFunctor (geometricPointAt X y.1) ≅ finiteEtaleFiberFunctor base) :
    ((frobeniusDataOfPath base y t).localElement⁻¹).asIso.hom =
      finiteEtaleFiberMap (frobeniusPointHom X y.1) :=
  inv_hom_eq_finiteEtaleFiberMap_frobeniusPointHom y _ (localElement_app_coe base y t)

end Element


section Sheaf

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1]
  (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)

set_option synthInstance.maxHeartbeats 200000 in
/-- **The geometric Frobenius on the stalk of `ℱ_ρ` at a closed point `y` with finite residue
field has the characteristic polynomial of `ρ(F_y)`**, where `F_y` is the geometric Frobenius
element (the inverse of the arithmetic Frobenius element `FrobeniusData.element`) determined by
any path `t` from the geometric point over `y` to `x̄`. -/
public theorem charpoly_rationalStalkFrobenius_representationSheaf (y : closedPoints X.1)
    [Finite (X.1.residueField y.1)]
    (t : finiteEtaleFiberFunctor (geometricPointAt X.1 y.1) ≅ finiteEtaleFiberFunctor x) :
    (LAdicSheaf.rationalStalkFrobenius B X ℓ (LAdicSheaf.representationSheaf B X x ρ hρ) y.1
        inferInstance).charpoly =
      (ρ (frobeniusDataOfPath x y t).element⁻¹).val.charpoly := by
  have := compactSpace_etaleFundamentalGroup X.1 x
  have h := charpoly_rationalStalkEnd_representationLAdicSheaf B X x (integralModel ρ hρ)
    (continuous_integralModel ρ hρ) t (frobeniusPointHom X.1 y.1)
    ((frobeniusDataOfPath x y t).localElement⁻¹) (inv_localElement_hom x y t)
  have he : etaleFundamentalGroupMulEquiv t (frobeniusDataOfPath x y t).localElement⁻¹ =
      (frobeniusDataOfPath x y t).element⁻¹ :=
    MulEquiv.map_inv (etaleFundamentalGroupMulEquiv t) _
  rw [he] at h
  exact h.trans (charpoly_integralModel ρ hρ _)

end Sheaf

section Family

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} [ConnectedSpace X]
  (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (base : GeometricPoint X)

/-- **The geometric Frobenius elements `F_y ∈ π₁(X, x̄)` at the closed points `y` of a connected
scheme of finite type over a finite field**: the inverse of the Frobenius element
`FrobeniusData.element` of the Frobenius data at `y` given by the algebraic closure
`AlgebraicClosure κ(y)` and a chosen path to the base point. Each is well defined up to
conjugation (`FrobeniusData.element_path_trans`). -/
public def geometricFrobeniusFamily (y : closedPoints X) : EtaleFundamentalGroup X base :=
  haveI := finite_residueField f y.1 y.2
  (frobeniusDataOfPath base y
    (nonempty_finiteEtaleFiberFunctorIso X (geometricPointAt X y.1) base).some).element⁻¹

/-- The geometric Frobenius element at `y` is the inverse of a Frobenius element at `y`. -/
public theorem inv_geometricFrobeniusFamily_mem_frobeniusElements (y : closedPoints X) :
    (geometricFrobeniusFamily f base y)⁻¹ ∈ frobeniusElements base Set.univ := by
  have := finite_residueField f y.1 y.2
  exact ⟨y, Set.mem_univ _, _, (inv_inv _).symm⟩

end Family

section SheafFamily

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1]
  {k : Type u} [Field k] [Finite k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)

set_option synthInstance.maxHeartbeats 200000 in
/-- **The geometric Frobenius `π_y^*` on the rational stalk of `ℱ_ρ` at a closed point `y` has the
characteristic polynomial of `ρ(F_y)`**, for the geometric Frobenius elements
`Stacks.EtaleCohomology.geometricFrobeniusFamily`. -/
public theorem charpoly_rationalStalkFrobenius_representationSheaf_eq (y : closedPoints X.1) :
    (LAdicSheaf.rationalStalkFrobenius B X ℓ (LAdicSheaf.representationSheaf B X x ρ hρ) y.1
        (finite_residueField f y.1 y.2)).charpoly =
      (ρ (geometricFrobeniusFamily f x y)).val.charpoly :=
  have := finite_residueField f y.1 y.2
  charpoly_rationalStalkFrobenius_representationSheaf B X x ρ hρ y _

set_option synthInstance.maxHeartbeats 200000 in
/-- **The geometric Frobenius on the stalk of the dual sheaf `ℱ_{ρ^∨}`**, the sheaf of the
contragredient `ρ^∨`, has the dual characteristic polynomial of `ρ(F_y)`: its eigenvalues are the
inverses of those of `π_y^*` on `ℱ_ρ`. -/
public theorem charpoly_rationalStalkFrobenius_representationSheaf_contragredient
    (y : closedPoints X.1) :
    (LAdicSheaf.rationalStalkFrobenius B X ℓ (LAdicSheaf.representationSheaf B X x
        (contragredient ρ) (continuous_contragredient hρ)) y.1
        (finite_residueField f y.1 y.2)).charpoly =
      dualCharpoly (ρ (geometricFrobeniusFamily f x y)).val.charpoly :=
  (charpoly_rationalStalkFrobenius_representationSheaf_eq B X x f (contragredient ρ)
    (continuous_contragredient hρ) y).trans (charpoly_contragredient ρ _)

end SheafFamily

end Stacks.EtaleCohomology

end
