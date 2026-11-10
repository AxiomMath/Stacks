module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowEtaleOfIsUnit
public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowTangent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.BaseChangeLocus
public import Mathlib.Algebra.Module.Torsion.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The `n`-torsion subgroup scheme of an abelian variety

For a group scheme `A` over a field `k` and an integer `n`, the `n`-torsion subgroup scheme
`A[n] = Ker([n] : A ⟶ A)` is the fibre product of `[n]` with the unit section. This file
identifies its rational points with the `n`-torsion of the group `A(k)` of rational points, and
proves that for an abelian variety `A[n]` is étale over `k` when `n` is invertible in `k`, and
conversely when `A` is nonzero ([Stacks, Tag 03RP], clause (6)).

## Main definitions

* `Stacks.Groupoids.torsionScheme A n`: the scheme `A[n]` over `k`.

## Main results

* `Stacks.Groupoids.torsionSchemePointsEquiv`: rational points of `A[n]` are the `n`-torsion
  points of `A(k)`, for `n` a natural number.
* `Stacks.Groupoids.etale_torsionScheme_hom_of_isUnit`: `A[n]` is étale over `k` for `n`
  invertible in `k`.
* `Stacks.Groupoids.etale_torsionScheme_hom_iff_isUnit`: for `A` nonzero, `A[n]` is étale over
  `k` if and only if `n` is invertible in `k`.

## Implementation notes

`A[n]` is `Over.mk (pullback.snd [n] e)`. The étale direction is the base change of
`Stacks.Groupoids.etale_zpow_id_left_of_isUnit` ([Stacks, Tag 0BFH]). For the converse, étaleness
of `A[n]` at the identity makes it unramified there, and unramifiedness at a point is unchanged by
base change ([Stacks, Tag 0475]), so `[n]` is unramified at the identity and
`Stacks.Groupoids.unramifiedAt_zpow_id_identity_iff_isUnit` applies; unlike the source this does
not use [Stacks, Tag 0BFG].

## References

* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

/-- An element of a commutative group is `n`-torsion in its additive form exactly when its
`n`-th power is `1`. -/
theorem mem_torsionBy_int_iff_pow {G : Type u} [CommGroup G]
    (x : G) (n : ℕ) :
    Additive.ofMul x ∈ AddSubgroup.torsionBy (Additive G) (n : ℤ) ↔ x ^ n = 1 := by
  change Additive.ofMul x ∈ Submodule.torsionBy ℤ (Additive G) (n : ℤ) ↔ _
  rw [Submodule.mem_torsionBy_iff]
  change (n : ℤ) • (Additive.ofMul x) = 0 ↔ x ^ n = 1
  rw [Nat.cast_smul_eq_nsmul ℤ n]
  change Additive.ofMul (x ^ n) = Additive.ofMul 1 ↔ x ^ n = 1
  exact Additive.ofMul.injective.eq_iff

/-- Points of `X` over `S` killed by an endomorphism `f`, i.e. sent by `f` to a given point `i`,
are the sections of the fibre product of `f` and `i` over `S`. -/
noncomputable def pullbackKernelPointsEquiv {S : Scheme.{u}} {X : Over S}
    (f : X ⟶ X) (i : Over.mk (𝟙 S) ⟶ X) :
    {p : Over.mk (𝟙 S) ⟶ X // p ≫ f = i} ≃
      {q : S ⟶ (Over.mk (pullback.snd f.left i.left)).left //
        q ≫ (Over.mk (pullback.snd f.left i.left)).hom = 𝟙 S} where
  toFun p := by
    let q : S ⟶ pullback f.left i.left :=
      pullback.lift p.1.left (𝟙 S) (congrArg Over.Hom.left p.2)
    refine ⟨q, ?_⟩
    change q ≫ pullback.snd f.left i.left = 𝟙 S
    simpa [q] using (pullback.lift_snd p.1.left (𝟙 S)
      (congrArg Over.Hom.left p.2))
  invFun q := by
    let hcond : q.1 ≫ pullback.fst f.left i.left ≫ f.left =
        q.1 ≫ pullback.snd f.left i.left ≫ i.left := by
      simpa only [Category.assoc] using
        congrArg (fun t => q.1 ≫ t) (pullback.condition :
          pullback.fst f.left i.left ≫ f.left = pullback.snd f.left i.left ≫ i.left)
    have hqbase : q.1 ≫ pullback.snd f.left i.left = 𝟙 S := by
      simpa using q.2
    have hbase : (q.1 ≫ pullback.fst f.left i.left) ≫ X.hom = 𝟙 S := by
      calc
        (q.1 ≫ pullback.fst f.left i.left) ≫ X.hom =
            (q.1 ≫ pullback.fst f.left i.left ≫ f.left) ≫ X.hom := by
              simp only [Category.assoc, f.w]
        _ = (q.1 ≫ pullback.snd f.left i.left ≫ i.left) ≫ X.hom :=
              congrArg (fun t => t ≫ X.hom) hcond
        _ = 𝟙 S := by simp [Category.assoc, i.w, hqbase]
    let p : Over.mk (𝟙 S) ⟶ X := Over.homMk (q.1 ≫ pullback.fst f.left i.left) hbase
    refine ⟨p, ?_⟩
    apply Over.OverMorphism.ext
    change q.1 ≫ pullback.fst f.left i.left ≫ f.left = i.left
    exact hcond.trans (by rw [← Category.assoc, hqbase, Category.id_comp])
  left_inv p := by
    apply Subtype.ext
    apply Over.OverMorphism.ext
    change (pullback.lift p.1.left (𝟙 S) (congrArg Over.Hom.left p.2) ≫
      pullback.fst f.left i.left) = p.1.left
    exact pullback.lift_fst p.1.left (𝟙 S) (congrArg Over.Hom.left p.2)
  right_inv q := by
    apply Subtype.ext
    apply pullback.hom_ext
    · change (pullback.lift (q.1 ≫ pullback.fst f.left i.left) (𝟙 S) _ ≫
        pullback.fst f.left i.left) = q.1 ≫ pullback.fst f.left i.left
      exact pullback.lift_fst _ _ _
    · change (pullback.lift (q.1 ≫ pullback.fst f.left i.left) (𝟙 S) _ ≫
        pullback.snd f.left i.left) = q.1 ≫ pullback.snd f.left i.left
      exact (pullback.lift_snd _ _ _).trans (by simpa using q.2.symm)

/-- The `n`-torsion of the group of points `S ⟶ A` of a commutative group scheme is the set of
points killed by `[n]`. -/
noncomputable def torsionKernelEquiv
    (k : Type u) [Field k] (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) (n : ℤ) ≃
      {p : 𝟙_ (Over (Spec (.of k))) ⟶ A //
        p ≫ (𝟙 A : A ⟶ A) ^ (n : ℤ) = η[A]} where
  toFun x := by
    let p : 𝟙_ (Over (Spec (.of k))) ⟶ A := x.1
    have hpow : p ^ n = 1 := (mem_torsionBy_int_iff_pow p n).mp x.2
    have hcomp : p ≫ (𝟙 A : A ⟶ A) ^ (n : ℤ) = p ^ n := by
      simpa [zpow_natCast] using (MonObj.comp_pow (𝟙 A) n p)
    refine ⟨p, ?_⟩
    rw [hcomp, hpow, CategoryTheory.Hom.one_def]
    exact Category.id_comp _
  invFun p := by
    let x : 𝟙_ (Over (Spec (.of k))) ⟶ A := p.1
    have hcomp : x ≫ (𝟙 A : A ⟶ A) ^ (n : ℤ) = x ^ n := by
      simpa [zpow_natCast] using (MonObj.comp_pow (𝟙 A) n x)
    have hpow : x ^ n = 1 := hcomp.symm.trans <| p.2.trans <| by
      rw [CategoryTheory.Hom.one_def]
      exact (Category.id_comp _).symm
    refine ⟨Additive.ofMul x, (mem_torsionBy_int_iff_pow x n).mpr hpow⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- The `n`-torsion subgroup scheme `A[n] = Ker([n])` of a group scheme over a field: the fibre
product of multiplication by `n` with the unit section, as a scheme over `k`. -/
@[sga "3 IX 2.2" "special case",
  sga "3 IX 4.7" "special case",
  sga "3 IX 6.1" "special case",
  sga "3 VIII 3.5",
  sga "3 VIII 7.2" "special case",
  sga "3 X 3.6",
  sga "3 XI 6.1" "special case"]
noncomputable def torsionScheme (n : ℤ) : Over (Spec (.of k)) :=
  Over.mk (pullback.snd ((𝟙 A : A ⟶ A) ^ n).left (η[A]).left)

/-- **The rational points of `A[n]` are the `n`-torsion points of `A(k)`.** -/
noncomputable def torsionSchemePointsEquiv [IsCommMonObj A] (n : ℕ) :
    Submodule.torsionBy ℤ (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) (n : ℤ) ≃
      {q : Spec (.of k) ⟶ (torsionScheme A (n : ℤ)).left //
        q ≫ (torsionScheme A (n : ℤ)).hom = 𝟙 _} :=
  (torsionKernelEquiv k A n).trans
    (pullbackKernelPointsEquiv ((𝟙 A : A ⟶ A) ^ (n : ℤ)) (η[A]))

/-- **Stacks Project, Tag 03RP, clause (6), the étale direction.** For `n` invertible in `k`,
the `n`-torsion subgroup scheme of an abelian variety is étale over `k`: it is a base change of
`[n]`, which is étale (Tag 0BFH). -/
@[sga "3 XII 4.4.2" "partial", sga "7 IX 3.1" "clause a), special case"]
theorem etale_torsionScheme_hom_of_isUnit [AlgebraicGeometry.IsAbelianVariety k A] (n : ℤ)
    (hn : IsUnit (n : k)) : Etale (torsionScheme A n).hom := by
  have := etale_zpow_id_left_of_isUnit A n hn
  change Etale (pullback.snd ((𝟙 A : A ⟶ A) ^ n).left (η[A]).left)
  infer_instance

/-- **Stacks Project, Tag 03RP, clause (6), for a nonzero abelian variety.** The `n`-torsion
subgroup scheme of an abelian variety of positive dimension is étale over `k` if and only if `n`
is invertible in `k`. -/
@[sga "3 XII 4.4.2" "partial"]
theorem etale_torsionScheme_hom_iff_isUnit [AlgebraicGeometry.IsAbelianVariety k A]
    (hA : 0 < topologicalKrullDim A.left) (n : ℤ) :
    Etale (torsionScheme A n).hom ↔ IsUnit (n : k) := by
  refine ⟨fun h => ?_, etale_torsionScheme_hom_of_isUnit A n⟩
  have := locallyOfFinitePresentation_zpow_id_left A n
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  set f := ((𝟙 A : A ⟶ A) ^ n).left
  set s : Spec (.of k) := IsLocalRing.closedPoint k
  have hfix : f ((η[A]).left s) = (η[A]).left s := zpow_id_fixes_identity A s n
  have hw : 𝟙 _ ≫ (η[A]).left = (η[A]).left ≫ f := by
    rw [Category.id_comp]
    exact (congrArg Over.Hom.left (show η[A] ≫ (𝟙 A : A ⟶ A) ^ n = η[A] by
      rw [GrpObj.comp_zpow, Category.comp_id, MonObj.one_eq_one A]; simp)).symm
  let z : ↥(pullback f (η[A]).left) := (pullback.lift (η[A]).left (𝟙 _) hw.symm).base s
  have hz : pullback.fst f (η[A]).left z = (η[A]).left s := by
    change (pullback.lift (η[A]).left (𝟙 _) hw.symm ≫ pullback.fst f (η[A]).left).base s = _
    rw [pullback.lift_fst]
  have hEt : EtaleAt (pullback.snd f (η[A]).left) z :=
    (etale_iff_forall_etaleAt _).mp h z
  have hun : UnramifiedAt (pullback.snd f (η[A]).left) z := by
    have h4 := ((etaleAt_tfae (pullback.snd f (η[A]).left) z).out 1 4).mp hEt
    exact ((unramifiedAt_tfae (pullback.snd f (η[A]).left) z).out 1 3).mpr h4.2
  have hf : UnramifiedAt f (pullback.fst f (η[A]).left z) :=
    (unramifiedAt_iff_of_isPullback (IsPullback.of_hasPullback f (η[A]).left) z).mpr hun
  rw [hz] at hf
  exact (unramifiedAt_zpow_id_identity_iff_isUnit k A hA s n).1 hf

end Stacks.Groupoids

end
