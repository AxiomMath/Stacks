module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedPointDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafFrobenius
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.AlgebraicClosureBaseChange
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteFieldFundamentalGroup
public import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusTorsion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Frobenius elements lie over powers of the Frobenius of the base field

Let `k` be a finite field with `q = p ^ n` elements and let `z` be a geometric point of
`Spec k`, given by an algebraically closed field `Ω`. The `q`-th power map of `Ω` fixes `k`, so
its spectrum is an automorphism of `Spec Ω` over `Spec k`; precomposition with it is a natural
automorphism of the geometric fibre functor at `z`, the *Frobenius* `Φ_z ∈ π₁(Spec k, z)`.
Through the naturality of the absolute Frobenius, `Φ_z` acts on the fibre of a finite étale
cover `V` by postcomposition with the `n`-fold absolute Frobenius of `V`, which is an
endomorphism of `V` over `k`.

For a scheme `X` over `k` and a closed point `y` of degree `d = [κ(y) : k]`, the Frobenius
elements of `π₁(X, x)` at `y` lie over `Φ ^ d`: the arithmetic Frobenius of `κ(y)` is the
`n d`-fold Frobenius of `κ̄(y)`, it acts on the fibre of `V ×_k X` by postcomposition with the
base change of the `n d`-fold absolute Frobenius of `V` (an endomorphism of finite étale covers of
`X`), and every path between fibre functors is natural with respect to that endomorphism.
Consequently the geometric Frobenius elements at `y` lie in the coset `φ ^ d · π₁(X_k̄)` for any
`φ` lying over `Φ⁻¹`.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.sourceAutElement` — the element of `π₁(S, z)` given by an
  automorphism of `Spec Ω` over `S`, acting on fibres by precomposition.
* `AlgebraicGeometry.finiteFieldFrobenius` — the Frobenius `Φ_z ∈ π₁(Spec k, z)` of a finite
  field.

## Main results

* `AlgebraicGeometry.finiteFieldFrobenius_pow_app_coe` — `Φ_z ^ d` acts by postcomposition with
  the `n d`-fold absolute Frobenius of the cover.
* `AlgebraicGeometry.etaleFundamentalGroupMap_element_frobeniusDataOfPath` — a Frobenius element
  at a closed point of degree `d` maps to `Φ ^ d` in `π₁(Spec k)`.
* `AlgebraicGeometry.etaleFundamentalGroupMap_geometricFrobeniusFamily` — the geometric
  Frobenius element maps to `Φ ^ (-d)`.
* `AlgebraicGeometry.inv_pow_mul_geometricFrobeniusFamily_mem_ker` — for `φ` over `Φ⁻¹`, the
  geometric Frobenius element at `y` lies in `φ ^ d` times the geometric fundamental group.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-! ### Automorphisms of a geometric point -/

section SourceAut

variable {S : Scheme.{u}} [ConnectedSpace S] (z : GeometricPoint S)

/-- An automorphism `α` of the source `Spec Ω` of a geometric point `z` over `S` acts on every
geometric fibre at `z` by precomposition, naturally in the cover: an element of `π₁(S, z)`. -/
def GeometricPoint.sourceAutElement (α : z.source ≅ z.source) (hα : α.hom ≫ z.hom = z.hom) :
    EtaleFundamentalGroup S z :=
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

/-- The element given by an automorphism of the source acts by precomposition. -/
theorem GeometricPoint.sourceAutElement_app_coe (α : z.source ≅ z.source)
    (hα : α.hom ≫ z.hom = z.hom) (V : FiniteEtaleOver S) (q : finiteEtaleFiber z V) :
    (((z.sourceAutElement α hα).app V).hom q).1 = α.hom ≫ q.1 :=
  rfl

end SourceAut

/-! ### The Frobenius of a finite field -/

section FiniteField

variable {k : Type u} [Field k] [Fintype k] (p n : ℕ) [Fact p.Prime] [CharP k p]

omit [Fintype k] [Fact (Nat.Prime p)] in
/-- The residue field of a geometric point of the spectrum of a field of characteristic `p` has
characteristic `p`. -/
theorem GeometricPoint.charP_residueField (z : GeometricPoint (Spec (.of k))) :
    CharP z.residueField p :=
  charP_of_injective_ringHom (Spec.preimage z.hom).hom.injective p

/-- The `n`-fold absolute Frobenius of a scheme over a finite field with `p ^ n` elements,
iterated `d` times, is a morphism over the field. -/
theorem absoluteFrobeniusPow_mul_comp_hom (hq : Fintype.card k = p ^ n)
    (V : Over (Spec (.of k))) (d : ℕ) :
    absoluteFrobeniusPow V.left p (isInCharacteristic_of_over V) (n * d) ≫ V.hom = V.hom := by
  have key (a : k) : ((Scheme.ΓSpecIso (.of k)).inv ≫ V.hom.appTop).hom a ^ p ^ (n * d) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ V.hom.appTop).hom a := by
    rw [← map_pow, pow_mul, ← hq, FiniteField.pow_card_pow]
  refine ext_to_Spec ?_
  show ((Scheme.ΓSpecIso (.of k)).inv ≫
      (absoluteFrobeniusPow V.left p (isInCharacteristic_of_over V) (n * d) ≫ V.hom).appTop :
        CommRingCat.of k ⟶ Γ(V.left, ⊤)) = (Scheme.ΓSpecIso (.of k)).inv ≫ V.hom.appTop
  rw [Scheme.Hom.comp_appTop, ← Category.assoc]
  ext a
  rw [CommRingCat.comp_apply, absoluteFrobeniusPow_appTop_apply]
  exact key a

/-- The `n d`-fold absolute Frobenius of a finite étale cover of `Spec k`, `#k = p ^ n`, as an
endomorphism of the cover. -/
def frobeniusCoverEnd (hq : Fintype.card k = p ^ n) (V : FiniteEtaleOver (Spec (.of k)))
    (d : ℕ) : V ⟶ V :=
  MorphismProperty.Over.homMk
    (absoluteFrobeniusPow V.left p (isInCharacteristic_of_over (Over.mk V.hom)) (n * d))
    (absoluteFrobeniusPow_mul_comp_hom p n hq (Over.mk V.hom) d)

/-- The `p ^ n`-th power automorphism of the source of a geometric point. -/
def frobeniusSourceIso (z : GeometricPoint (Spec (.of k))) : z.source ≅ z.source :=
  haveI := z.charP_residueField p
  Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso (iterateFrobeniusEquiv z.residueField p n)).op

omit [Fintype k] in
/-- The morphism underlying `frobeniusSourceIso p n z` is the spectrum of the `p ^ n`-th power
map of the residue field of `z`. -/
theorem frobeniusSourceIso_hom (z : GeometricPoint (Spec (.of k))) :
    haveI := z.charP_residueField p
    (frobeniusSourceIso p n z).hom =
      Spec.map (CommRingCat.ofHom (iterateFrobenius z.residueField p n)) :=
  rfl

omit [Fintype k] in
/-- The spectrum of the `p ^ m`-th power map of the residue field of a geometric point is the
`m`-fold absolute Frobenius of its source. -/
theorem specMap_iterateFrobenius_eq (z : GeometricPoint (Spec (.of k))) (m : ℕ) :
    haveI := z.charP_residueField p
    Spec.map (CommRingCat.ofHom (iterateFrobenius z.residueField p m)) =
      absoluteFrobeniusPow z.source p
        (Stacks.Frobenius.isInCharacteristic_spec z.residueField p) m := by
  have := z.charP_residueField p
  exact specMap_eq_absoluteFrobeniusPow _ p m _ fun a => rfl

/-- The Frobenius of `Ω` lies over `Spec k`: it fixes the image of `k`. -/
theorem frobeniusSourceIso_hom_comp (hq : Fintype.card k = p ^ n)
    (z : GeometricPoint (Spec (.of k))) : (frobeniusSourceIso p n z).hom ≫ z.hom = z.hom := by
  have := z.charP_residueField p
  rw [frobeniusSourceIso_hom, ← Spec.map_preimage z.hom, ← Spec.map_comp]
  congr 1
  ext a
  show (Spec.preimage z.hom).hom a ^ p ^ n = (Spec.preimage z.hom).hom a
  rw [← map_pow, ← hq, FiniteField.pow_card]

/-- **The Frobenius of a finite field** `k` with `p ^ n` elements in `π₁(Spec k, z)`: it acts on
geometric fibres by precomposition with the `p ^ n`-th power map of the residue field of `z`. -/
@[sga "7 IX 4.3"]
def finiteFieldFrobenius (hq : Fintype.card k = p ^ n) (z : GeometricPoint (Spec (.of k))) :
    EtaleFundamentalGroup (Spec (.of k)) z :=
  z.sourceAutElement (frobeniusSourceIso p n z) (frobeniusSourceIso_hom_comp p n hq z)

/-- The `d`-th power of the Frobenius acts by precomposition with the `p ^ (n d)`-th power map. -/
@[sga "7 IX 4.3" "partial"]
theorem finiteFieldFrobenius_pow_app_coe_specMap (hq : Fintype.card k = p ^ n)
    (z : GeometricPoint (Spec (.of k))) (d : ℕ) (V : FiniteEtaleOver (Spec (.of k)))
    (q : finiteEtaleFiber z V) :
    haveI := z.charP_residueField p
    ((((finiteFieldFrobenius p n hq z) ^ d).app V).hom q).1 =
      Spec.map (CommRingCat.ofHom (iterateFrobenius z.residueField p (n * d))) ≫ q.1 := by
  have := z.charP_residueField p
  induction d generalizing q with
  | zero =>
    rw [mul_zero, iterateFrobenius_zero, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    rfl
  | succ d ih =>
    rw [pow_succ]
    show ((((finiteFieldFrobenius p n hq z) ^ d).app V).hom
      (((finiteFieldFrobenius p n hq z).app V).hom q)).1 = _
    rw [ih]
    show _ ≫ (frobeniusSourceIso p n z).hom ≫ q.1 = _
    rw [frobeniusSourceIso_hom, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← iterateFrobenius_add, mul_add, mul_one, add_comm]

/-- **The `d`-th power of the Frobenius acts by the `n d`-fold absolute Frobenius of the cover.**
-/
theorem finiteFieldFrobenius_pow_app_coe (hq : Fintype.card k = p ^ n)
    (z : GeometricPoint (Spec (.of k))) (d : ℕ) (V : FiniteEtaleOver (Spec (.of k)))
    (q : finiteEtaleFiber z V) :
    ((((finiteFieldFrobenius p n hq z) ^ d).app V).hom q).1 =
      q.1 ≫ (frobeniusCoverEnd p n hq V d).left := by
  rw [finiteFieldFrobenius_pow_app_coe_specMap, specMap_iterateFrobenius_eq]
  exact absoluteFrobeniusPow_naturality q.1 p _ _ _

end FiniteField

/-! ### Frobenius elements over the Frobenius of the base field -/

section Degree

variable {k : Type u} [Field k] [Fintype k] (p n : ℕ) [Fact p.Prime] [CharP k p]
  (hq : Fintype.card k = p ^ n)
  {X : Scheme.{u}} [ConnectedSpace X] (f : X ⟶ Spec (.of k)) (x : GeometricPoint X)
  (y : closedPoints X) [Finite (X.residueField y.1)]

omit [Fact (Nat.Prime p)] [CharP k p] [ConnectedSpace X] in
/-- The residue field at a point of degree `d` over a field with `p ^ n` elements has
`p ^ (n d)` elements. -/
theorem natCard_residueField_eq (hq : Fintype.card k = p ^ n) :
    Nat.card (X.residueField y.1) = p ^ (n * Stacks.EtaleCohomology.residueDegree f y.1) := by
  let : Algebra k (X.residueField y.1) :=
    (fieldToResidue f y.1).hom.toAlgebra
  have : Module.Finite k (X.residueField y.1) := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := k), Nat.card_eq_fintype_card, hq, ← pow_mul]
  rfl

omit [ConnectedSpace X] in
/-- The arithmetic Frobenius of `κ̄(y)` commutes with every lift of the geometric point above `y`
to `V ×_k X`, up to the base change of the `n d`-fold absolute Frobenius of `V`. -/
theorem specMap_residueGeometricFrobenius_symm_comp (V : FiniteEtaleOver (Spec (.of k)))
    (g : Spec (.of (AlgebraicClosure (X.residueField y.1))) ⟶ pullback V.hom f)
    (hg : g ≫ pullback.snd V.hom f = (Stacks.Frobenius.geometricPointAt X y.1).hom) :
    Spec.map (CommRingCat.ofHom
        (Stacks.Frobenius.residueGeometricFrobenius X y.1).symm.toAlgHom.toRingHom) ≫ g =
      g ≫ ((finiteEtaleBaseChange f).map
        (frobeniusCoverEnd p n hq V (Stacks.EtaleCohomology.residueDegree f y.1))).left := by
  let d := Stacks.EtaleCohomology.residueDegree f y.1
  let Ω := AlgebraicClosure (X.residueField y.1)
  have : CharP (X.residueField y.1) p := charP_of_injective_ringHom
    (fieldToResidue f y.1).hom.injective p
  have : CharP Ω p := charP_of_injective_algebraMap' (X.residueField y.1) p
  have hσ : Spec.map (CommRingCat.ofHom
      (Stacks.Frobenius.residueGeometricFrobenius X y.1).symm.toAlgHom.toRingHom) =
      absoluteFrobeniusPow (Spec (.of Ω)) p
        (Stacks.Frobenius.isInCharacteristic_spec Ω p) (n * d) := by
    refine specMap_eq_absoluteFrobeniusPow _ p (n * d) _ fun a => ?_
    show (Stacks.Frobenius.residueGeometricFrobenius X y.1).symm a = _
    rw [Stacks.Frobenius.residueGeometricFrobenius_symm_apply,
      natCard_residueField_eq p n f y hq]
  let e : pullback V.hom f ⟶ pullback V.hom f :=
    ((finiteEtaleBaseChange f).map (frobeniusCoverEnd p n hq V d)).left
  have hfst : e ≫ pullback.fst V.hom f = pullback.fst V.hom f ≫
      (frobeniusCoverEnd p n hq V d).left :=
    finiteEtaleBaseChange_map_left_fst f _
  have hsnd : e ≫ pullback.snd V.hom f = pullback.snd V.hom f :=
    MorphismProperty.Over.w ((finiteEtaleBaseChange f).map (frobeniusCoverEnd p n hq V d))
  show _ ≫ g = g ≫ e
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, hfst, hσ, ← Category.assoc g]
    exact absoluteFrobeniusPow_naturality (g ≫ pullback.fst V.hom f) p _ _ _
  · rw [Category.assoc, Category.assoc, hsnd, hg]
    show _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (X.residueField y.1) Ω)) ≫
      X.fromSpecResidueField y.1 = Spec.map (CommRingCat.ofHom (algebraMap _ Ω)) ≫ _
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun a =>
      (Stacks.Frobenius.residueGeometricFrobenius X y.1).symm.commutes a

/-- The arithmetic Frobenius element at `y` acts on the fibre of a base-changed cover `V ×_k X`
at the geometric point above `y` as the base change of the `n d`-fold absolute Frobenius of `V`. -/
theorem localElement_frobeniusDataOfPath_app_baseChange
    (t : finiteEtaleFiberFunctor (Stacks.Frobenius.geometricPointAt X y.1) ≅
      finiteEtaleFiberFunctor x)
    (V : FiniteEtaleOver (Spec (.of k)))
    (s : finiteEtaleFiber (Stacks.Frobenius.geometricPointAt X y.1)
      ((finiteEtaleBaseChange f).obj V)) :
    (((Stacks.EtaleCohomology.frobeniusDataOfPath x y t).localElement.app
        ((finiteEtaleBaseChange f).obj V)).hom s) =
      (finiteEtaleFiberFunctor (Stacks.Frobenius.geometricPointAt X y.1)).map
        ((finiteEtaleBaseChange f).map
          (frobeniusCoverEnd p n hq V (Stacks.EtaleCohomology.residueDegree f y.1))) s := by
  apply Subtype.ext
  rw [Stacks.EtaleCohomology.localElement_app_coe]
  exact specMap_residueGeometricFrobenius_symm_comp p n hq f y V s.1 s.2

/-- **A Frobenius element at a closed point of degree `d` lies over `Φ ^ d`.** -/
theorem etaleFundamentalGroupMap_element_frobeniusDataOfPath
    (t : finiteEtaleFiberFunctor (Stacks.Frobenius.geometricPointAt X y.1) ≅
      finiteEtaleFiberFunctor x) :
    etaleFundamentalGroupMap f x (Stacks.EtaleCohomology.frobeniusDataOfPath x y t).element =
      finiteFieldFrobenius p n hq (x.map f) ^ Stacks.EtaleCohomology.residueDegree f y.1 := by
  set c := Stacks.EtaleCohomology.frobeniusDataOfPath x y t
  set d := Stacks.EtaleCohomology.residueDegree f y.1
  refine Iso.ext (NatTrans.ext (funext fun V => ?_))
  ext q
  apply Subtype.ext
  show (((etaleFundamentalGroupMap f x c.element).app V).hom q).1 =
    ((((finiteFieldFrobenius p n hq (x.map f)) ^ d).app V).hom q).1
  rw [finiteFieldFrobenius_pow_app_coe]
  let w := (finiteEtaleFiberProjectionEquiv f x V).symm q
  let fe := (finiteEtaleBaseChange f).map (frobeniusCoverEnd p n hq V d)
  have h1 : ((etaleFundamentalGroupMap f x c.element).app V).hom q =
      finiteEtaleFiberProjection f x V ((c.element.app _).hom w) :=
    etaleFundamentalGroupMonoidHom_app_apply f x V c.element q
  have h2 : (c.element.app ((finiteEtaleBaseChange f).obj V)).hom w =
      t.hom.app _ ((c.localElement.app _).hom (t.inv.app _ w)) :=
    Stacks.FundamentalGroup.conjAut_app_apply_inv t c.localElement _ w
  have h3 : (c.localElement.app ((finiteEtaleBaseChange f).obj V)).hom (t.inv.app _ w) =
      (finiteEtaleFiberFunctor (Stacks.Frobenius.geometricPointAt X y.1)).map fe
        (t.inv.app _ w) :=
    localElement_frobeniusDataOfPath_app_baseChange p n hq f x y t V _
  have h4 : t.hom.app _ ((finiteEtaleFiberFunctor (Stacks.Frobenius.geometricPointAt X y.1)).map
      fe (t.inv.app _ w)) = (finiteEtaleFiberFunctor x).map fe w := by
    rw [NatTrans.naturality_apply t.hom fe (t.inv.app _ w), Iso.inv_hom_id_app_apply]
  rw [h1, h2, h3, h4]
  show (w.1 ≫ fe.left) ≫ pullback.fst V.hom f = q.1 ≫ _
  calc (w.1 ≫ fe.left) ≫ pullback.fst V.hom f
      = w.1 ≫ (fe.left ≫ pullback.fst V.hom f) := Category.assoc _ _ _
    _ = w.1 ≫ (pullback.fst V.hom f ≫ (frobeniusCoverEnd p n hq V d).left) :=
        congrArg (w.1 ≫ ·) (finiteEtaleBaseChange_map_left_fst f _)
    _ = (w.1 ≫ pullback.fst V.hom f) ≫ (frobeniusCoverEnd p n hq V d).left :=
        (Category.assoc _ _ _).symm
    _ = q.1 ≫ (frobeniusCoverEnd p n hq V d).left :=
        congrArg (· ≫ (frobeniusCoverEnd p n hq V d).left) (pullback.lift_fst _ _ _)

/-- **The geometric Frobenius element at a closed point of degree `d` lies over `Φ ^ (-d)`.** -/
theorem etaleFundamentalGroupMap_geometricFrobeniusFamily [LocallyOfFiniteType f] :
    etaleFundamentalGroupMap f x (Stacks.EtaleCohomology.geometricFrobeniusFamily f x y) =
      (finiteFieldFrobenius p n hq (x.map f) ^
        Stacks.EtaleCohomology.residueDegree f y.1)⁻¹ := by
  rw [Stacks.EtaleCohomology.geometricFrobeniusFamily, map_inv]
  exact congrArg _ (etaleFundamentalGroupMap_element_frobeniusDataOfPath p n hq f x y _)

/-- **Geometric Frobenius elements in the cosets of the geometric fundamental group.** If `φ` lies
over the inverse of the Frobenius of `k`, then the geometric Frobenius element at a closed point of
degree `d` lies in `φ ^ d · ker(π₁(X, x) → π₁(Spec k))`. -/
theorem inv_pow_mul_geometricFrobeniusFamily_mem_ker [LocallyOfFiniteType f]
    (φ : EtaleFundamentalGroup X x)
    (hφ : etaleFundamentalGroupMap f x φ = (finiteFieldFrobenius p n hq (x.map f))⁻¹) :
    (φ ^ Stacks.EtaleCohomology.residueDegree f y.1)⁻¹ *
        Stacks.EtaleCohomology.geometricFrobeniusFamily f x y ∈
      (etaleFundamentalGroupMap f x).toMonoidHom.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow]
  show (etaleFundamentalGroupMap f x φ ^ _)⁻¹ *
    etaleFundamentalGroupMap f x (Stacks.EtaleCohomology.geometricFrobeniusFamily f x y) = 1
  rw [etaleFundamentalGroupMap_geometricFrobeniusFamily p n hq f x y, hφ, inv_pow, inv_inv,
    mul_inv_cancel]

/-- For a scheme `X` over `k` that stays connected over an algebraically closed extension `Ω`, some
element of `π₁(X, x)` lies over the inverse of the Frobenius of `k`, by the surjectivity of
`π₁(X, x) → π₁(Spec k)` (Stacks 0BTX). -/
theorem exists_etaleFundamentalGroupMap_eq_finiteFieldFrobenius_inv (Ω : Type u) [Field Ω]
    [Algebra k Ω] [IsAlgClosed Ω]
    [ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))] :
    ∃ φ : EtaleFundamentalGroup X x,
      etaleFundamentalGroupMap f x φ = (finiteFieldFrobenius p n hq (x.map f))⁻¹ :=
  surjective_etaleFundamentalGroupMap_isAlgClosed k Ω f x _

end Degree

end AlgebraicGeometry
