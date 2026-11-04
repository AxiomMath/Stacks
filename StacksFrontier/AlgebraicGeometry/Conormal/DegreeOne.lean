module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Conormal.Charts
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Immersion
public import StacksFrontier.AlgebraicGeometry.PartTwo.Restrict
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.Functoriality
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.ConormalSections
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# The degree-one piece of the conormal algebra is the conormal sheaf

Let `i : Z ⟶ X` be an immersion of schemes, `𝒞_{Z/X}` its conormal sheaf and `𝒞_{Z/X,*}` its
conormal algebra. Then `𝒞_{Z/X,1} = 𝒞_{Z/X}` canonically.

## Main definitions

* `Stacks.Conormal.conormalDegreeOneHom`: the canonical morphism `𝒞_{Z/X} ⟶ 𝒞_{Z/X,1}`.
* `Stacks.Conormal.conormalDegreeOneIso`: that morphism as an isomorphism.

## Main results

* `Stacks.Conormal.conormalDegreeOneHom_isIso`: the canonical morphism is an isomorphism.
* `Stacks.Conormal.conormalDegreeOneHom_localMap`: over an affine open on which `i` restricts to
  a closed immersion with kernel ideal `I`, the morphism carries the class of `a ∈ I` in `I/I²`
  to the degree-one associated-graded class of `a`.

## Implementation notes

The two sheaves are built from different constructions — `𝒞_{Z/X}` as a module pullback of an
ideal sheaf, `𝒞_{Z/X,1}` as the degree-one piece of a pullback of a Rees algebra — so the
comparison is assembled from their common affine-local description. Over an affine open `U ⊆ X`
on which `i` restricts to a closed immersion with kernel ideal `I = I(U)`, the sections of
`𝒞_{Z/X}` over `i⁻¹U` are `I/I²` by [Stacks, Tag 01R3] part (2), and the degree-one sections of
`𝒞_{Z/X,1}` are `I/I²` by the local associated-graded presentation of [Stacks, Tag 0630]. The
composite of those two identifications is an additive bijection compatible with restriction, and
the opens `i⁻¹U` form a basis of `Z`, so the chartwise maps extend to a single morphism of
sheaves which is an isomorphism and is linear.

## References

* [Stacks Project, Tag 0632](https://stacks.math.columbia.edu/tag/0632)
* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction

universe u v

namespace Stacks.Conormal

variable {Z X : Scheme.{u}}

/-- If an isomorphism of modules sends `y` to `z`, then `y` is the inverse image of `z`.  Stated
through the `hom` projection because the element coercion of `CategoryTheory.ConcreteCategory` is
not available when the ring is spelled in two definitionally equal ways. -/
private theorem moduleIso_eq_inv_of_hom_eq {R : Type u} [Ring R] {A B : ModuleCat.{v} R}
    (q : A ≅ B) {y : A} {z : B} (h : q.hom.hom y = z) : y = q.inv.hom z :=
  h ▸ (congrArg (fun k : A ⟶ A => k.hom y) q.hom_inv_id).symm

/-- The inverse of an isomorphism of modules followed by the isomorphism is the identity, on an
element. -/
private theorem moduleIso_inv_hom_apply {R : Type u} [Ring R] {A B : ModuleCat.{v} R} (q : A ≅ B)
    (y : B) : q.hom.hom (q.inv.hom y) = y :=
  congrArg (fun k : B ⟶ B => k.hom y) q.inv_hom_id

/-! ### Affine charts of an immersion -/

/-- The affine model of an affine closed-immersion chart, with its ideal named as the kernel
ideal of the chart. -/
private theorem exists_chartIdeal_affineModel (i : Z ⟶ X) (U : X.affineOpens)
    (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl)) :
    ∃ e : pullback i U.1.ι ≅ Spec (.of (Γ(X, U) ⧸ chartIdeal i U)),
      pullback.snd i U.1.ι ≫ U.2.isoSpec.hom =
        e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (chartIdeal i U))) := by
  obtain ⟨I, e, he⟩ := exists_affineModel_of_resLE i U.1 U.2 hU
  obtain rfl : chartIdeal i U = I := by
    rw [chartIdeal, Scheme.Hom.app_eq_appLE]
    exact ker_appLE_eq_of_affineModel i U.1 U.2 I e he
  exact ⟨e, he⟩

/-- The affine model of a chart is unique: the quotient immersion is a monomorphism. -/
private theorem chartIdeal_affineModel_unique (i : Z ⟶ X) (U : X.affineOpens)
    (e e' : pullback i U.1.ι ≅ Spec (.of (Γ(X, U) ⧸ chartIdeal i U)))
    (he : pullback.snd i U.1.ι ≫ U.2.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (chartIdeal i U))))
    (he' : pullback.snd i U.1.ι ≫ U.2.isoSpec.hom =
      e'.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (chartIdeal i U)))) : e = e' :=
  Iso.ext <| (cancel_mono (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (chartIdeal i U))))).1 (he.symm.trans he')

/-! ### The comparison over an affine chart -/

/-- **Over an affine closed-immersion chart the degree-one sections of the conormal algebra are
`I/I²`.** The local associated-graded presentation of [Stacks, Tag 0630] in degree one has kernel
`I²` and is surjective, so it factors through `Ideal.Cotangent` as a bijection. -/
private noncomputable def affineCotangentPieceEquiv (i : Z ⟶ X) [IsImmersion i]
    (U : X.affineOpens) (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl)) :
    let R := Γ(X, U)
    let I := chartIdeal i U
    let T := ((conormalAlgebra i).algebra.piece 1).val.obj (op (i ⁻¹ᵁ U.1))
    let φ : R →+* Γ(Z, i ⁻¹ᵁ U.1) := (i.app U).hom
    letI : Algebra R Γ(Z, i ⁻¹ᵁ U.1) := φ.toAlgebra
    letI : Module (Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ U.1))) (↑T) := T.isModule
    letI : Module (↑R) (↑T) :=
      Module.compHom (R := Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ U.1))) (S := (↑R)) (↑T) φ
    I.Cotangent ≃ₗ[R] T := by
  let R := Γ(X, U)
  let I := chartIdeal i U
  let T := ((conormalAlgebra i).algebra.piece 1).val.obj (op (i ⁻¹ᵁ U.1))
  let φ : R →+* Γ(Z, i ⁻¹ᵁ U.1) := (i.app U).hom
  letI : Algebra R Γ(Z, i ⁻¹ᵁ U.1) := φ.toAlgebra
  letI : Module (Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ U.1))) (↑T) := T.isModule
  letI : Module (↑R) (↑T) :=
    Module.compHom (R := Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ U.1))) (S := (↑R)) (↑T) φ
  let ePow : I ≃ₗ[R] ↥(I ^ 1) :=
    { toFun := fun a => ⟨a.1, by simp⟩
      invFun := fun a => ⟨a.1, by simpa using a.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  let f : I →ₗ[R] T :=
    { toFun := fun a => (conormalAlgebra i).localMap U hU 1 (ePow a)
      map_add' := by
        intro a b
        change (conormalAlgebra i).localMap U hU 1 (ePow (a + b)) = _
        rw [ePow.map_add]
        exact (conormalAlgebra i).localMap U hU 1 |>.map_add _ _
      map_smul' r a :=
        (conormalAlgebra i).localMap_smul U hU 1 r (ePow a) (ePow (r • a)) (by simp [ePow]) }
  let q : I.Cotangent →ₗ[R] T := Ideal.Cotangent.lift f fun a b ↦
    ((conormalAlgebra i).localMap_eq_zero_iff U hU 1 (ePow (a * b))).2 <| by
      change (a * b : R) ∈ I ^ 2
      simpa only [pow_two] using Ideal.mul_mem_mul a.2 b.2
  apply LinearEquiv.ofBijective q
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := I.toCotangent_surjective x
    obtain ⟨b, rfl⟩ := I.toCotangent_surjective y
    rw [Ideal.Cotangent.lift_toCotangent, Ideal.Cotangent.lift_toCotangent] at hxy
    have hsq : (a - b : R) ∈ I ^ 2 := by
      have hz : (conormalAlgebra i).localMap U hU 1 (ePow (a - b)) = 0 := by
        change f (a - b) = 0
        rw [map_sub, hxy, sub_self]
      exact ((conormalAlgebra i).localMap_eq_zero_iff U hU 1 (ePow (a - b))).mp hz
    exact I.toCotangent_eq.mpr hsq
  · intro y
    obtain ⟨a, ha⟩ := (conormalAlgebra i).localMap_surjective U hU 1 y
    refine ⟨I.toCotangent (ePow.symm a), ?_⟩
    rw [Ideal.Cotangent.lift_toCotangent]
    change (conormalAlgebra i).localMap U hU 1 (ePow (ePow.symm a)) = y
    simpa using ha

private theorem affineCotangentPieceEquiv_toCotangent (i : Z ⟶ X) [IsImmersion i]
    (U : X.affineOpens) (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
    (a : chartIdeal i U) :
    (affineCotangentPieceEquiv i U hU) ((chartIdeal i U).toCotangent a) =
      (conormalAlgebra i).localMap U hU 1 ⟨a.1, by simpa only [pow_one] using a.2⟩ := by
  simp [affineCotangentPieceEquiv]

/-- **The comparison over an affine closed-immersion chart**: the sections of the conormal sheaf
over `i⁻¹U` are `I/I²` by [Stacks, Tag 01R3] part (2), and those are the degree-one sections of
the conormal algebra. -/
private noncomputable def chartDegreeOneAddHom (i : Z ⟶ X) [IsImmersion i] (U : X.affineOpens)
    (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
    (e : pullback i U.1.ι ≅ Spec (.of (Γ(X, U) ⧸ chartIdeal i U)))
    (he : pullback.snd i U.1.ι ≫ U.2.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (chartIdeal i U)))) :
    AddCommGrpCat.of ((conormalSheaf i).val.obj (op (i ⁻¹ᵁ U.1))) ⟶
      AddCommGrpCat.of (((conormalAlgebra i).algebra.piece 1).val.obj (op (i ⁻¹ᵁ U.1))) := by
  let R := Γ(X, U)
  let V := i ⁻¹ᵁ U.1
  let φ : R →+* Γ(Z, V) := (i.app U).hom
  letI : Algebra R Γ(Z, V) := φ.toAlgebra
  let T := ((conormalAlgebra i).algebra.piece 1).val.obj (op V)
  letI : Module (Z.ringCatSheaf.obj.obj (op V)) (↑T) := T.isModule
  letI : Module (↑R) (↑T) :=
    Module.compHom (R := Z.ringCatSheaf.obj.obj (op V)) (S := (↑R)) (↑T) φ
  let q := Stacks.Conormal.affineConormalIsoCotangent i U.1 U.2 (chartIdeal i U) e he
  let l := affineCotangentPieceEquiv i U hU
  exact AddCommGrpCat.ofHom
    { toFun := fun x => l (q.hom.hom x)
      map_zero' := (congrArg (fun w => l w) (map_zero q.hom.hom)).trans l.map_zero
      map_add' := fun x y =>
        (congrArg (fun w => l w) (map_add q.hom.hom x y)).trans (l.map_add _ _) }

private theorem chartDegreeOneAddHom_generator (i : Z ⟶ X) [IsImmersion i] (U : X.affineOpens)
    (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
    (e : pullback i U.1.ι ≅ Spec (.of (Γ(X, U) ⧸ chartIdeal i U)))
    (he : pullback.snd i U.1.ι ≫ U.2.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (chartIdeal i U))))
    (a : chartIdeal i U) :
    (chartDegreeOneAddHom i U hU e he).hom
        ((Stacks.Conormal.affineConormalIsoCotangent i U.1 U.2
          (chartIdeal i U) e he).inv.hom ((chartIdeal i U).toCotangent a)) =
      (conormalAlgebra i).localMap U hU 1 ⟨a.1, by simpa only [pow_one] using a.2⟩ := by
  let q := Stacks.Conormal.affineConormalIsoCotangent i U.1 U.2 (chartIdeal i U) e he
  show (affineCotangentPieceEquiv i U hU)
      (q.hom.hom (q.inv.hom ((chartIdeal i U).toCotangent a))) = _
  rw [moduleIso_inv_hom_apply q ((chartIdeal i U).toCotangent a)]
  exact affineCotangentPieceEquiv_toCotangent i U hU a

private theorem chartDegreeOneAddHom_bijective (i : Z ⟶ X) [IsImmersion i] (U : X.affineOpens)
    (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
    (e : pullback i U.1.ι ≅ Spec (.of (Γ(X, U) ⧸ chartIdeal i U)))
    (he : pullback.snd i U.1.ι ≫ U.2.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (chartIdeal i U)))) :
    Function.Bijective (chartDegreeOneAddHom i U hU e he).hom := by
  let q := Stacks.Conormal.affineConormalIsoCotangent i U.1 U.2 (chartIdeal i U) e he
  let l := affineCotangentPieceEquiv i U hU
  show Function.Bijective (fun x => l (q.hom.hom x))
  exact l.bijective.comp (ConcreteCategory.bijective_of_isIso q.hom)

private theorem chartDegreeOneAddHom_smul (i : Z ⟶ X) [IsImmersion i] (U : X.affineOpens)
    (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
    (e : pullback i U.1.ι ≅ Spec (.of (Γ(X, U) ⧸ chartIdeal i U)))
    (he : pullback.snd i U.1.ι ≫ U.2.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (chartIdeal i U))))
    (r : Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ U.1)))
    (x : (conormalSheaf i).val.obj (op (i ⁻¹ᵁ U.1))) :
    letI : Module (Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ U.1)))
        ((conormalSheaf i).val.obj (op (i ⁻¹ᵁ U.1))) :=
      ((conormalSheaf i).val.obj (op (i ⁻¹ᵁ U.1))).isModule
    letI : Module (Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ U.1)))
        (((conormalAlgebra i).algebra.piece 1).val.obj (op (i ⁻¹ᵁ U.1))) :=
      (((conormalAlgebra i).algebra.piece 1).val.obj (op (i ⁻¹ᵁ U.1))).isModule
    (chartDegreeOneAddHom i U hU e he).hom (r • x) =
      r • (chartDegreeOneAddHom i U hU e he).hom x := by
  let : Module (Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ U.1)))
      ((conormalSheaf i).val.obj (op (i ⁻¹ᵁ U.1))) :=
    ((conormalSheaf i).val.obj (op (i ⁻¹ᵁ U.1))).isModule
  let : Module (Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ U.1)))
      (((conormalAlgebra i).algebra.piece 1).val.obj (op (i ⁻¹ᵁ U.1))) :=
    (((conormalAlgebra i).algebra.piece 1).val.obj (op (i ⁻¹ᵁ U.1))).isModule
  obtain ⟨s, rfl⟩ := AlgebraicGeometry.app_surjective_of_closedRestriction i U hU r
  let q := Stacks.Conormal.affineConormalIsoCotangent i U.1 U.2 (chartIdeal i U) e he
  let l := affineCotangentPieceEquiv i U hU
  let : Module (↑Γ(X, U)) (chartIdeal i U).Cotangent :=
    (ModuleCat.of (↑Γ(X, U)) (chartIdeal i U).Cotangent).isModule
  let : Module
      (↑((structureSheafRing X.toLocallyRingedSpace.toRingedSpace).obj.obj (op U.1)))
      (↑(ModuleCat.of (↑Γ(X, U)) (chartIdeal i U).Cotangent)) :=
    (ModuleCat.of (↑Γ(X, U)) (chartIdeal i U).Cotangent).isModule
  have hq : q.hom.hom
      ((show Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ U.1)) from (i.app U).hom s) • x) =
      s • q.hom.hom x := (q.hom.hom).map_smul s x
  show l (q.hom.hom
      ((show Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ U.1)) from (i.app U).hom s) • x)) =
    (show Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ U.1)) from (i.app U).hom s) • l (q.hom.hom x)
  rw [hq]
  exact l.map_smul s (q.hom.hom x)

private theorem chartDegreeOneAddHom_restrict (i : Z ⟶ X) [IsImmersion i]
    (U A : X.affineOpens) (hAU : A.1 ≤ U.1) (hZU : (i ⁻¹ᵁ A.1) ≤ (i ⁻¹ᵁ U.1))
    (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
    (hA : IsClosedImmersion (i.resLE A.1 (i ⁻¹ᵁ A.1) le_rfl))
    (eU : pullback i U.1.ι ≅ Spec (.of (Γ(X, U) ⧸ chartIdeal i U)))
    (heU : pullback.snd i U.1.ι ≫ U.2.isoSpec.hom =
      eU.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (chartIdeal i U))))
    (eA : pullback i A.1.ι ≅ Spec (.of (Γ(X, A) ⧸ chartIdeal i A)))
    (heA : pullback.snd i A.1.ι ≫ A.2.isoSpec.hom =
      eA.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (chartIdeal i A))))
    (x : (conormalSheaf i).val.obj (op (i ⁻¹ᵁ U.1))) :
    ((conormalAlgebra i).algebra.piece 1).val.map (homOfLE hZU).op
        ((chartDegreeOneAddHom i U hU eU heU).hom x) =
      (chartDegreeOneAddHom i A hA eA heA).hom
        ((conormalSheaf i).val.map (homOfLE hZU).op x) := by
  let I := chartIdeal i U
  let J := chartIdeal i A
  let qU := Stacks.Conormal.affineConormalIsoCotangent i U.1 U.2 I eU heU
  let qA := Stacks.Conormal.affineConormalIsoCotangent i A.1 A.2 J eA heA
  obtain ⟨a, ha⟩ := I.toCotangent_surjective (qU.hom.hom x)
  rw [moduleIso_eq_inv_of_hom_eq qU ha.symm]
  let ar : J := ⟨(X.presheaf.map (homOfLE hAU).op).hom a.1, by
    have hn := i.naturality (homOfLE hAU).op
    have ha0 : (i.app U).hom a.1 = 0 := RingHom.mem_ker.mp a.2
    show (X.presheaf.map (homOfLE hAU).op ≫ i.app A).hom a.1 = 0
    rw [hn, ConcreteCategory.comp_apply, ha0]
    simp⟩
  have hqA : qA.hom.hom
      ((conormalSheaf i).val.map (homOfLE hZU).op (qU.inv.hom (I.toCotangent a))) =
      J.toCotangent ar :=
    Stacks.Tag01R3PartTwo.affineConormalIsoCotangent_restrict i U.1 A.1 hAU U.2 A.2 I J
      eU heU eA heA a ar.2
  have hsrc : (conormalSheaf i).val.map (homOfLE hZU).op (qU.inv.hom (I.toCotangent a)) =
      qA.inv.hom (J.toCotangent ar) := moduleIso_eq_inv_of_hom_eq qA hqA
  rw [chartDegreeOneAddHom_generator i U hU eU heU a, hsrc,
    chartDegreeOneAddHom_generator i A hA eA heA ar]
  exact (conormalAlgebra i).localMap_naturality U A hAU hZU hU hA 1
    ⟨a.1, by simpa only [pow_one] using a.2⟩ ⟨ar.1, by simpa only [pow_one] using ar.2⟩ rfl

/-! ### Gluing the chartwise comparisons -/

/-- The comparison over a chart, with the affine model chosen once and for all. -/
private noncomputable def conormalChartDegreeOneHom (i : Z ⟶ X) [IsImmersion i]
    (U : ConormalChart i) :
    AddCommGrpCat.of ((conormalSheaf i).val.obj (op (i ⁻¹ᵁ U.1.1))) ⟶
      AddCommGrpCat.of (((conormalAlgebra i).algebra.piece 1).val.obj (op (i ⁻¹ᵁ U.1.1))) :=
  chartDegreeOneAddHom i U.1 (isClosedImmersion_resLE_of_le_coborderRange i U.1.1 U.2)
    (Classical.choose (exists_chartIdeal_affineModel i U.1
      (isClosedImmersion_resLE_of_le_coborderRange i U.1.1 U.2)))
    (Classical.choose_spec (exists_chartIdeal_affineModel i U.1
      (isClosedImmersion_resLE_of_le_coborderRange i U.1.1 U.2)))

private theorem conormalChartDegreeOneHom_restrict (i : Z ⟶ X) [IsImmersion i]
    (U A : ConormalChart i) (hAU : A.1.1 ≤ U.1.1) (hZU : (i ⁻¹ᵁ A.1.1) ≤ (i ⁻¹ᵁ U.1.1))
    (x : (conormalSheaf i).val.obj (op (i ⁻¹ᵁ U.1.1))) :
    ((conormalAlgebra i).algebra.piece 1).val.map (homOfLE hZU).op
        ((conormalChartDegreeOneHom i U).hom x) =
      (conormalChartDegreeOneHom i A).hom ((conormalSheaf i).val.map (homOfLE hZU).op x) :=
  chartDegreeOneAddHom_restrict i U.1 A.1 hAU hZU
    (isClosedImmersion_resLE_of_le_coborderRange i U.1.1 U.2)
    (isClosedImmersion_resLE_of_le_coborderRange i A.1.1 A.2) _
    (Classical.choose_spec (exists_chartIdeal_affineModel i U.1
      (isClosedImmersion_resLE_of_le_coborderRange i U.1.1 U.2))) _
    (Classical.choose_spec (exists_chartIdeal_affineModel i A.1
      (isClosedImmersion_resLE_of_le_coborderRange i A.1.1 A.2))) x

private theorem conormalChartDegreeOneHom_restrict_of_le (i : Z ⟶ X) [IsImmersion i]
    (U A : ConormalChart i) (hZU : (i ⁻¹ᵁ A.1.1) ≤ (i ⁻¹ᵁ U.1.1))
    (x : (conormalSheaf i).val.obj (op (i ⁻¹ᵁ U.1.1))) :
    ((conormalAlgebra i).algebra.piece 1).val.map (homOfLE hZU).op
        ((conormalChartDegreeOneHom i U).hom x) =
      (conormalChartDegreeOneHom i A).hom ((conormalSheaf i).val.map (homOfLE hZU).op x) := by
  apply TopCat.Presheaf.IsSheaf.section_ext ((conormalAlgebra i).algebra.piece 1).isSheaf
  intro z hz
  obtain ⟨W, ⟨V, hV, rfl⟩, hzV, hVAU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show i z ∈ (A.1.1 : Set X) ∩ (U.1.1 : Set X) from ⟨by simpa using hz, by simpa using hZU hz⟩)
      (A.1.1.2.inter U.1.1.2)
  let C : ConormalChart i := ⟨⟨V, hV⟩, hVAU.trans inf_le_right |>.trans U.2⟩
  have hBC : C.1.1 ≤ A.1.1 := fun y hy => (hVAU hy).1
  have hBU : C.1.1 ≤ U.1.1 := fun y hy => (hVAU hy).2
  have hZB_A : (i ⁻¹ᵁ C.1.1) ≤ (i ⁻¹ᵁ A.1.1) := i.preimage_mono hBC
  have hZB_U : (i ⁻¹ᵁ C.1.1) ≤ (i ⁻¹ᵁ U.1.1) := i.preimage_mono hBU
  refine ⟨i ⁻¹ᵁ C.1.1, hZB_A, hzV, ?_⟩
  show ((conormalAlgebra i).algebra.piece 1).val.map (homOfLE hZB_A).op
      (((conormalAlgebra i).algebra.piece 1).val.map (homOfLE hZU).op
        ((conormalChartDegreeOneHom i U).hom x)) =
    ((conormalAlgebra i).algebra.piece 1).val.map (homOfLE hZB_A).op
      ((conormalChartDegreeOneHom i A).hom
        ((conormalSheaf i).val.map (homOfLE hZU).op x))
  have hU := conormalChartDegreeOneHom_restrict i U C hBU hZB_U x
  have hA := conormalChartDegreeOneHom_restrict i A C hBC hZB_A
    ((conormalSheaf i).val.map (homOfLE hZU).op x)
  have hcomp : (homOfLE hZU).op ≫ (homOfLE hZB_A).op = (homOfLE hZB_U).op :=
    Subsingleton.elim _ _
  rw [← ((conormalAlgebra i).algebra.piece 1).val.map_comp_apply, hcomp, hU, hA,
    ← (conormalSheaf i).val.map_comp_apply, hcomp]

private noncomputable def conormalChartDegreeOneNatTrans (i : Z ⟶ X) [IsImmersion i] :
    ((inducedFunctor (conormalChartFunctor i).obj).op ⋙
        ((SheafOfModules.toSheaf Z.ringCatSheaf).obj (conormalSheaf i)).obj) ⟶
      ((inducedFunctor (conormalChartFunctor i).obj).op ⋙
        ((SheafOfModules.toSheaf Z.ringCatSheaf).obj
          ((conormalAlgebra i).algebra.piece 1)).obj) := by
  refine { app := fun U => conormalChartDegreeOneHom i U.unop, naturality := ?_ }
  rintro ⟨U⟩ ⟨V⟩ f
  ext x
  exact (conormalChartDegreeOneHom_restrict_of_le i U V f.unop.hom.le x).symm

/-- The comparison as a morphism of sheaves of abelian groups. -/
private noncomputable def conormalDegreeOneAddHom (i : Z ⟶ X) [IsImmersion i] :
    (SheafOfModules.toSheaf Z.ringCatSheaf).obj (conormalSheaf i) ⟶
      (SheafOfModules.toSheaf Z.ringCatSheaf).obj ((conormalAlgebra i).algebra.piece 1) :=
  (Sheaf.homEquiv).symm
    (TopCat.Sheaf.restrictHomEquivHom
      ((SheafOfModules.toSheaf Z.ringCatSheaf).obj (conormalSheaf i)).obj
      ((SheafOfModules.toSheaf Z.ringCatSheaf).obj ((conormalAlgebra i).algebra.piece 1))
      (conormalChart_isBasis i) (conormalChartDegreeOneNatTrans i))

private theorem conormalDegreeOneAddHom_chart (i : Z ⟶ X) [IsImmersion i] (U : ConormalChart i) :
    (conormalDegreeOneAddHom i).hom.app (op ((conormalChartFunctor i).obj U)) =
      conormalChartDegreeOneHom i U :=
  TopCat.Sheaf.extend_hom_app
    ((SheafOfModules.toSheaf Z.ringCatSheaf).obj (conormalSheaf i)).obj
    ((SheafOfModules.toSheaf Z.ringCatSheaf).obj ((conormalAlgebra i).algebra.piece 1))
    (conormalChart_isBasis i) (conormalChartDegreeOneNatTrans i) U

private theorem conormalDegreeOneAddHom_smul (i : Z ⟶ X) [IsImmersion i] (U : Z.Opens)
    (r : Z.ringCatSheaf.obj.obj (op U)) (x : (conormalSheaf i).val.obj (op U)) :
    letI : Module (Z.ringCatSheaf.obj.obj (op U)) ((conormalSheaf i).val.obj (op U)) :=
      ((conormalSheaf i).val.obj (op U)).isModule
    letI : Module (Z.ringCatSheaf.obj.obj (op U))
        (((SheafOfModules.toSheaf Z.ringCatSheaf).obj
          ((conormalAlgebra i).algebra.piece 1)).obj.obj (op U)) :=
      (((conormalAlgebra i).algebra.piece 1).val.obj (op U)).isModule
    ((conormalDegreeOneAddHom i).hom.app (op U)).hom (r • x) =
      r • ((conormalDegreeOneAddHom i).hom.app (op U)).hom x := by
  let : Module (Z.ringCatSheaf.obj.obj (op U)) ((conormalSheaf i).val.obj (op U)) :=
    ((conormalSheaf i).val.obj (op U)).isModule
  let : Module (Z.ringCatSheaf.obj.obj (op U))
      (((SheafOfModules.toSheaf Z.ringCatSheaf).obj
        ((conormalAlgebra i).algebra.piece 1)).obj.obj (op U)) :=
    (((conormalAlgebra i).algebra.piece 1).val.obj (op U)).isModule
  apply TopCat.Presheaf.IsSheaf.section_ext ((conormalAlgebra i).algebra.piece 1).isSheaf
  intro z hz
  obtain ⟨A, hzA, hAU, hAW⟩ := exists_chart_near i U z hz
  let C : ConormalChart i := ⟨A, hAW⟩
  refine ⟨i ⁻¹ᵁ A.1, hAU, hzA, ?_⟩
  let f := (homOfLE hAU).op
  let P := (conormalAlgebra i).algebra.piece 1
  let Φ := ((conormalDegreeOneAddHom i).hom.app (op U)).hom
  let ψ := (conormalChartDegreeOneHom i C).hom
  let r' := Z.ringCatSheaf.obj.map f r
  have hnat : ∀ y : (conormalSheaf i).val.obj (op U),
      P.val.map f (Φ y) = ψ ((conormalSheaf i).val.map f y) := by
    intro y
    have h := (conormalDegreeOneAddHom i).hom.naturality f
    have happ : (conormalDegreeOneAddHom i).hom.app (op (i ⁻¹ᵁ A.1)) =
        conormalChartDegreeOneHom i C := conormalDegreeOneAddHom_chart i C
    rw [happ] at h
    exact (congrArg (fun k => k.hom y) h).symm
  have hA' := isClosedImmersion_resLE_of_le_coborderRange i A.1 hAW
  have hmodel := exists_chartIdeal_affineModel i A hA'
  have e2 := (conormalSheaf i).val.map_smul f r x
  have e3 := chartDegreeOneAddHom_smul i A hA' (Classical.choose hmodel)
    (Classical.choose_spec hmodel) r' ((conormalSheaf i).val.map f x)
  have e4 := P.val.map_smul f r (Φ x)
  show P.val.map f (Φ (r • x)) = P.val.map f (r • Φ x)
  refine (hnat (r • x)).trans ?_
  refine (congrArg (fun w => ψ w) e2).trans ?_
  refine e3.trans ?_
  refine Eq.trans ?_ e4.symm
  exact congrArg (fun w : P.val.obj (op (i ⁻¹ᵁ A.1)) => r' • w) (hnat x).symm

private theorem conormalChartDegreeOneHom_bijective (i : Z ⟶ X) [IsImmersion i]
    (U : ConormalChart i) : Function.Bijective (conormalChartDegreeOneHom i U).hom :=
  chartDegreeOneAddHom_bijective i U.1 (isClosedImmersion_resLE_of_le_coborderRange i U.1.1 U.2) _
    (Classical.choose_spec (exists_chartIdeal_affineModel i U.1
      (isClosedImmersion_resLE_of_le_coborderRange i U.1.1 U.2)))

private theorem conormalDegreeOneAddHom_isIso (i : Z ⟶ X) [IsImmersion i] :
    IsIso (conormalDegreeOneAddHom i) := by
  refine TopCat.Sheaf.isIso_iff_isIso_basis (conormalChart_isBasis i) fun U ↦ ?_
  rw [conormalDegreeOneAddHom_chart i U]
  exact (ConcreteCategory.isIso_iff_bijective _).2 (conormalChartDegreeOneHom_bijective i U)

/-! ### Tag 0632: the degree-one comparison -/

/-- **The canonical morphism `𝒞_{Z/X} ⟶ 𝒞_{Z/X,1}`** from the conormal sheaf of an immersion to
the degree-one piece of its conormal algebra. Over an affine open on which `i` restricts to a
closed immersion with kernel ideal `I`, it carries the class of `a ∈ I` in `I/I²` to the
degree-one associated-graded class of `a`. -/
@[no_expose]
noncomputable def conormalDegreeOneHom (i : Z ⟶ X) [IsImmersion i] :
    conormalSheaf i ⟶ (conormalAlgebra i).algebra.piece 1 :=
  ⟨PresheafOfModules.homMk (conormalDegreeOneAddHom i).hom fun U r m =>
    conormalDegreeOneAddHom_smul i U.unop r m⟩

/-- **[Stacks, Tag 0632]: the conormal algebra in degree one is the conormal sheaf.** The
canonical morphism `𝒞_{Z/X} ⟶ 𝒞_{Z/X,1}` is an isomorphism.

This is the degree-one assertion of the canonical surjection `Sym^*(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}`: the
identification of the degree-one piece of the conormal algebra with the conormal sheaf, which is
what makes that surjection an isomorphism in degree one. -/
@[stacks 0632 "degree one: the conormal algebra in degree one is the conormal sheaf"]
theorem conormalDegreeOneHom_isIso (i : Z ⟶ X) [IsImmersion i] :
    IsIso (conormalDegreeOneHom i) := by
  have hReflect : (SheafOfModules.toSheaf.{u} Z.ringCatSheaf).ReflectsIsomorphisms := by
    have h : (SheafOfModules.toSheaf.{u} Z.ringCatSheaf ⋙
        sheafToPresheaf _ _).ReflectsIsomorphisms :=
      inferInstanceAs (SheafOfModules.forget Z.ringCatSheaf ⋙
        PresheafOfModules.toPresheaf _).ReflectsIsomorphisms
    exact reflectsIsomorphisms_of_comp _ (sheafToPresheaf _ _)
  have : IsIso ((SheafOfModules.toSheaf.{u} Z.ringCatSheaf).map (conormalDegreeOneHom i)) :=
    conormalDegreeOneAddHom_isIso i
  exact hReflect.reflects (conormalDegreeOneHom i)

/-- **[Stacks, Tag 0632]: the degree-one identification `𝒞_{Z/X} ≅ 𝒞_{Z/X,1}`.** -/
@[no_expose, stacks 0632 "degree one: the identification as an isomorphism"]
noncomputable def conormalDegreeOneIso (i : Z ⟶ X) [IsImmersion i] :
    conormalSheaf i ≅ (conormalAlgebra i).algebra.piece 1 :=
  haveI := conormalDegreeOneHom_isIso i
  asIso (conormalDegreeOneHom i)

/-- The degree-one identification `𝒞_{Z/X} ≅ 𝒞_{Z/X,1}` is the canonical morphism. -/
theorem conormalDegreeOneIso_hom (i : Z ⟶ X) [IsImmersion i] :
    (conormalDegreeOneIso i).hom = conormalDegreeOneHom i := by
  rw [conormalDegreeOneIso]
  exact @asIso_hom _ _ _ _ _ (conormalDegreeOneHom_isIso i)

/-- **The degree-one comparison is the canonical one.** Over an affine open on which `i`
restricts to a closed immersion, it carries the class in `I/I²` of a section `a` of the kernel
ideal to the degree-one local associated-graded class of `a`. -/
theorem conormalDegreeOneHom_localMap (i : Z ⟶ X) [IsImmersion i] (U : X.affineOpens)
    (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
    (e : pullback i U.1.ι ≅ Spec (.of (Γ(X, U.1) ⧸ chartIdeal i U)))
    (he : pullback.snd i U.1.ι ≫ U.2.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (chartIdeal i U))))
    (a : ↥(chartIdeal i U)) :
    ((conormalDegreeOneHom i).val.app (op (i ⁻¹ᵁ U.1)))
        ((Stacks.Conormal.affineConormalIsoCotangent i U.1 U.2
          (chartIdeal i U) e he).inv.hom ((chartIdeal i U).toCotangent a)) =
      (conormalAlgebra i).localMap U hU 1 ⟨a.1, by simpa only [pow_one] using a.2⟩ := by
  obtain rfl : e = Classical.choose (exists_chartIdeal_affineModel i U hU) :=
    chartIdeal_affineModel_unique i U e _ he
      (Classical.choose_spec (exists_chartIdeal_affineModel i U hU))
  have hUW := le_coborderRange_of_isClosedImmersion_resLE i U.1 hU
  have hC : (conormalDegreeOneAddHom i).hom.app (op (i ⁻¹ᵁ U.1)) =
      conormalChartDegreeOneHom i ⟨U, hUW⟩ := conormalDegreeOneAddHom_chart i ⟨U, hUW⟩
  show ((conormalDegreeOneAddHom i).hom.app (op (i ⁻¹ᵁ U.1))).hom _ = _
  rw [hC]
  exact chartDegreeOneAddHom_generator i U hU
    (Classical.choose (exists_chartIdeal_affineModel i U hU)) he a

end Stacks.Conormal

end
