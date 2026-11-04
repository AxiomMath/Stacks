module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Fiber
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.Torsion
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.TorsionScheme
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVariety

/-!
# Torsion points of abelian varieties prime to the characteristic

Let `A` be an abelian variety over a field `k` and `n` an integer invertible in `k`. This file
proves that multiplication by `n` on `A` is finite, that the `n`-torsion subgroup scheme `A[n]`
is finite étale over `k`, that the group `A(k)[n]` of `n`-torsion rational points is finite when
`k` is algebraically closed, and that for `k` algebraically closed and any field extension `K/k`
base change of points is an isomorphism `A(k)[n] ≃+ A_K(K)[n]`.

## Main definitions

* `Stacks.Groupoids.pointBaseChange A K`: the additive homomorphism `A(k) →+ A_K(K)` sending a
  rational point `p` to its base change `p_K`.
* `Stacks.Groupoids.torsionPointBaseChange A K n`: its restriction `A(k)[n] →+ A_K(K)[n]`.
* `Stacks.Groupoids.torsionPointBaseChangeEquiv A K n hn`: for `k` algebraically closed and
  `n` invertible in `k`, this restriction as an additive isomorphism.

## Main results

* `Stacks.Groupoids.isFinite_zpow_id_left_of_isUnit`: `[n]` is finite for `n ∈ k*`.
* `Stacks.Groupoids.isFinite_torsionScheme_hom_of_isUnit`: `A[n]` is finite (and étale) over `k`.
* `Stacks.Groupoids.finite_torsionBy_of_isUnit`: `A(k)[n]` is finite for `k` algebraically
  closed.
* `Stacks.Groupoids.pointBaseChange_injective`: base change of points is injective for `k`
  algebraically closed.
* `Stacks.Groupoids.torsionPointBaseChange_bijective`: `A(k)[n] → A_K(K)[n]` is bijective for
  `k` algebraically closed and `n ∈ k*`.

## Implementation notes

Rational points are morphisms `𝟙_ ⟶ A` of schemes over `Spec k`, written additively through
`Additive` as in `Stacks.Groupoids.exists_nsmul_eq_of_isUnit`. The base change `A_K` is the one of
[Stacks, Tag 0BFB], `(Over.pullback (Spec K ⟶ Spec k)).obj A`, and the base change of a point is
`ε ≫ (Over.pullback _).map p`; on underlying schemes it is the morphism `Spec K ⟶ A ×_k Spec K`
with components `Spec K ⟶ Spec k ⟶ A` and the identity (`pointBaseChange_left`), and it is
additive because pulling back is a monoidal functor.

The bijectivity does not count points. A `K`-point `y` of `A_K` killed by `n` lies over a point
`a` of `A` with `[n](a) = e`; as `[n]` is étale, hence locally quasi-finite, the fibre of `[n]`
over the closed point `e` is discrete, so `a` is closed and, `k` being algebraically closed, is
the image of a rational point `x`, which is then `n`-torsion. Finally `y = x_K`, because two
morphisms `Spec K ⟶ A` over `k` hitting the same closed point agree: the residue field there is
`k` (`AlgebraicGeometry.ext_of_apply_closedPoint_eq_of_comp_eq`).

## References

* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP)
* [Stacks Project, Tag 0BFB](https://stacks.math.columbia.edu/tag/0BFB)
* [Stacks Project, Tag 0BFH](https://stacks.math.columbia.edu/tag/0BFH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

/-- A point in the fibre of a locally quasi-finite morphism over a closed point is closed: the
fibre is closed and discrete. -/
theorem Scheme.Hom.isClosed_singleton_of_apply_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] {x : X} {y : Y} (hy : IsClosed {y}) (hx : f x = y) :
    IsClosed {x} := by
  have hF : IsClosed (f ⁻¹' {y}) := hy.preimage f.continuous
  have : DiscreteTopology (f ⁻¹' {y}) := (f.isDiscrete_preimage_singleton y).to_subtype
  have h := hF.isClosedEmbedding_subtypeVal.isClosedMap {⟨x, hx⟩} (isClosed_discrete _)
  simpa using h

/-- Two morphisms from the spectrum of a field `K` to a scheme locally of finite type over an
algebraically closed field `k`, equal over `k` and sending the point to the same closed point,
are equal: the residue field at a closed point is `k`. -/
theorem ext_of_apply_closedPoint_eq_of_comp_eq {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (h : X ⟶ Spec (.of k)) [LocallyOfFiniteType h] {K : Type u} [Field K]
    {x : X} (hx : IsClosed {x}) {f g : Spec (.of K) ⟶ X}
    (hf : f (IsLocalRing.closedPoint K) = x) (hg : g (IsLocalRing.closedPoint K) = x)
    (hfg : f ≫ h = g ≫ h) : f = g := by
  obtain ⟨φ, rfl⟩ :
      ∃ φ : X.residueField x ⟶ .of K, Spec.map φ ≫ X.fromSpecResidueField x = f := by
    subst hf
    exact ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X f⟩
  obtain ⟨ψ, rfl⟩ :
      ∃ ψ : X.residueField x ⟶ .of K, Spec.map ψ ≫ X.fromSpecResidueField x = g := by
    subst hg
    exact ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X g⟩
  have e : (residueFieldIsoBase h x hx).inv ≫ φ = (residueFieldIsoBase h x hx).inv ≫ ψ := by
    apply Spec.map_injective
    simpa only [Spec.map_comp, Category.assoc, SpecMap_residueFieldIsoBase_inv] using hfg
  rw [(cancel_epi _).mp e]

end AlgebraicGeometry

namespace Stacks.Groupoids

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-! ### Finiteness -/

/-- **Multiplication by `d` on an abelian variety is finite for `d` invertible in `k`**: it is
étale (Tag 0BFH), hence locally quasi-finite, and it is proper. -/
theorem isFinite_zpow_id_left_of_isUnit [AlgebraicGeometry.IsAbelianVariety k A] (d : ℤ)
    (hd : IsUnit (d : k)) :
    IsFinite ((𝟙 A : A ⟶ A) ^ d).left := by
  have := etale_zpow_id_left_of_isUnit A d hd
  exact (isFinite_zpow_id_left_iff_locallyQuasiFinite A d).mpr inferInstance

/-- **The `n`-torsion subgroup scheme `A[n]` of an abelian variety is finite over `k`** for `n`
invertible in `k`: it is a base change of the finite morphism `[n]`. -/
theorem isFinite_torsionScheme_hom_of_isUnit [AlgebraicGeometry.IsAbelianVariety k A] (n : ℤ)
    (hn : IsUnit (n : k)) : IsFinite (torsionScheme A n).hom := by
  have := isFinite_zpow_id_left_of_isUnit A n hn
  show IsFinite (pullback.snd ((𝟙 A : A ⟶ A) ^ n).left (η[A]).left)
  infer_instance

/-- The point of `Spec k` is closed, hence so is its image under the unit section. -/
theorem isClosed_singleton_unit_left (s : (𝟙_ (Over (Spec (.of k)))).left) :
    IsClosed {(η[A]).left s} := by
  have hc : IsClosed ({s} : Set (𝟙_ (Over (Spec (.of k)))).left) :=
    isClosed_discrete (α := Spec (.of k)) _
  have h := (η[A]).left.isClosedMap _ hc
  rwa [Set.image_singleton] at h

/-- Two rational points of `A` over an algebraically closed field with the same image point are
equal. -/
private theorem eq_of_apply_closedPoint_eq [IsAlgClosed k] [AlgebraicGeometry.IsAbelianVariety k A]
    {p q : 𝟙_ (Over (Spec (.of k))) ⟶ A}
    (h : (p.left : Spec (.of k) ⟶ A.left) (IsLocalRing.closedPoint k) =
      (q.left : Spec (.of k) ⟶ A.left) (IsLocalRing.closedPoint k)) : p = q :=
  Over.OverMorphism.ext (ext_of_apply_closedPoint_eq A.hom (Over.w _) (Over.w _) h)

/-- **For `k` algebraically closed and `n` invertible in `k`, the group `A(k)[n]` is finite.**
A rational point is determined by its closed image point, and the image of an `n`-torsion point
lies in the fibre of the finite morphism `[n]` over the identity, a finite set. -/
theorem finite_torsionBy_of_isUnit [IsAlgClosed k] [AlgebraicGeometry.IsAbelianVariety k A]
    (n : ℕ) (hn : IsUnit (n : k)) :
    Finite (Submodule.torsionBy ℤ (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) (n : ℤ)) := by
  have := isFinite_zpow_id_left_of_isUnit A n (by simpa using hn)
  set pk : Spec (.of k) := IsLocalRing.closedPoint k
  set e := ((η[A]).left : Spec (.of k) ⟶ A.left) pk
  have := (Scheme.Hom.finite_preimage_singleton ((𝟙 A : A ⟶ A) ^ (n : ℤ)).left e).to_subtype
  show Finite (AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) (n : ℤ))
  rw [(torsionKernelEquiv k A n).finite_iff]
  refine Finite.of_injective (β := ((𝟙 A : A ⟶ A) ^ (n : ℤ)).left ⁻¹' {e})
    (fun p => ⟨(p.1.left : Spec (.of k) ⟶ A.left) pk, ?_⟩) ?_
  · exact congrArg (fun f : 𝟙_ (Over (Spec (.of k))) ⟶ A => (f.left : Spec (.of k) ⟶ A.left) pk)
      p.2
  · intro p q hpq
    exact Subtype.ext (eq_of_apply_closedPoint_eq A (congrArg Subtype.val hpq))

/-! ### Base change of points -/

variable (K : Type u) [Field K] [Algebra k K]

/-- **Base change of rational points**, `A(k) →+ A_K(K)`, `p ↦ p_K`: the image of `p` under the
pullback functor along `Spec K ⟶ Spec k`, precomposed with the comparison `𝟙_ ⟶ (𝟙_)_K`. It is
additive since the pullback functor is monoidal. -/
noncomputable def pointBaseChange :
    Additive (𝟙_ (Over (Spec (.of k))) ⟶ A) →+
      Additive (𝟙_ (Over (Spec (.of K))) ⟶
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A) where
  toFun p := Additive.ofMul
    (Functor.LaxMonoidal.ε (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map p.toMul)
  map_zero' := by
    change Additive.ofMul (_ ≫ (Over.pullback _).map (1 : 𝟙_ (Over (Spec (.of k))) ⟶ A)) =
      Additive.ofMul 1
    rw [Functor.map_one, MonObj.comp_one]
    rfl
  map_add' p q := by
    change Additive.ofMul (_ ≫ (Over.pullback _).map (p.toMul * q.toMul)) =
      Additive.ofMul (_ * _)
    rw [Functor.map_mul, MonObj.comp_mul]
    rfl

/-- The base change `p_K` of a rational point, followed by the projection `A_K ⟶ A`, is
`Spec K ⟶ Spec k` followed by `p`. -/
theorem pointBaseChange_left_fst (p : Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) :
    (pointBaseChange A K p).toMul.left ≫
        pullback.fst A.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ p.toMul.left := by
  set g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hc : pullback.fst (𝟙 (Spec (.of k))) g = pullback.snd (𝟙 (Spec (.of k))) g ≫ g := by
    simpa using (pullback.condition : pullback.fst (𝟙 (Spec (.of k))) g ≫ 𝟙 _ = _)
  show (Functor.LaxMonoidal.ε (Over.pullback g)).left ≫
    ((Over.pullback g).map p.toMul).left ≫ pullback.fst A.hom g = _
  simp only [Over.pullback_map_left, pullback.lift_fst, Over.ε_pullback_left]
  show inv (pullback.snd (𝟙 (Spec (.of k))) g) ≫ pullback.fst (𝟙 (Spec (.of k))) g ≫ _ = _
  rw [hc, Category.assoc, IsIso.inv_hom_id_assoc]

/-- The base change `p_K` of a rational point is a section of `A_K ⟶ Spec K`. -/
theorem pointBaseChange_left_snd (p : Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) :
    (pointBaseChange A K p).toMul.left ≫
        pullback.snd A.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) = 𝟙 _ :=
  Over.w (pointBaseChange A K p).toMul

/-- **The base change of a rational point, explicitly**: on underlying schemes `p_K` is the
morphism `Spec K ⟶ A ×_k Spec K` with components `Spec K ⟶ Spec k ⟶ A` and the identity. -/
theorem pointBaseChange_left (p : Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) :
    (pointBaseChange A K p).toMul.left =
      pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ p.toMul.left) (𝟙 _)
        (by rw [Category.assoc, Over.w p.toMul, Category.id_comp]; exact Category.comp_id _) := by
  apply pullback.hom_ext
  · rw [pointBaseChange_left_fst, pullback.lift_fst]
  · rw [pointBaseChange_left_snd, pullback.lift_snd]
    rfl

/-- **Base change of rational points is injective** when `k` is algebraically closed: `p` and
`q` with `p_K = q_K` hit the same closed point of `A`, and a rational point is determined by its
image point. -/
theorem pointBaseChange_injective [IsAlgClosed k] [AlgebraicGeometry.IsAbelianVariety k A] :
    Function.Injective (pointBaseChange A K) := by
  intro p q hpq
  set pK : Spec (.of K) := IsLocalRing.closedPoint K
  set pk : Spec (.of k) := IsLocalRing.closedPoint k
  have h : Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ p.toMul.left =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ q.toMul.left := by
    rw [← pointBaseChange_left_fst, ← pointBaseChange_left_fst, hpq]
  have hpt : (p.toMul.left : Spec (.of k) ⟶ A.left) pk =
      (q.toMul.left : Spec (.of k) ⟶ A.left) pk := by
    have h' := congrArg (fun f : Spec (.of K) ⟶ A.left => f pK) h
    have e : (Spec.map (CommRingCat.ofHom (algebraMap k K)) : Spec (.of K) ⟶ Spec (.of k)) pK =
      pk := Subsingleton.elim _ _
    exact (congrArg (fun z => (p.toMul.left : Spec (.of k) ⟶ A.left) z) e.symm).trans
      (h'.trans (congrArg (fun z => (q.toMul.left : Spec (.of k) ⟶ A.left) z) e))
  exact eq_of_apply_closedPoint_eq A hpt

/-- **Base change of `n`-torsion points**, `A(k)[n] →+ A_K(K)[n]`: the restriction of
`pointBaseChange`, which as an additive map carries `n`-torsion to `n`-torsion. -/
noncomputable def torsionPointBaseChange [AlgebraicGeometry.IsAbelianVariety k A] (n : ℕ) :
    Submodule.torsionBy ℤ (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) (n : ℤ) →+
      Submodule.torsionBy ℤ (Additive (𝟙_ (Over (Spec (.of K))) ⟶
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A)) (n : ℤ) :=
  ((pointBaseChange A K).toIntLinearMap.restrict (fun x hx => by
    rw [Submodule.mem_torsionBy_iff] at hx ⊢
    rw [AddMonoidHom.coe_toIntLinearMap, ← map_zsmul, hx, map_zero])).toAddMonoidHom

/-- The base change of an `n`-torsion point is its base change as a rational point. -/
@[simp]
theorem torsionPointBaseChange_apply_coe [AlgebraicGeometry.IsAbelianVariety k A] (n : ℕ)
    (x : Submodule.torsionBy ℤ (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) (n : ℤ)) :
    (torsionPointBaseChange A K n x : Additive (𝟙_ (Over (Spec (.of K))) ⟶
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A)) =
      pointBaseChange A K x :=
  rfl

/-- **Every `n`-torsion `K`-point of `A_K` comes from an `n`-torsion rational point of `A`**, for
`k` algebraically closed and `n` invertible in `k`. Its image `a` in `A` satisfies `[n](a) = e`,
so lies in a discrete closed fibre of the étale morphism `[n]` and is closed; the rational point
`x` at `a` is `n`-torsion, and `x_K` agrees with the given point as both lie over `a`. -/
theorem torsionPointBaseChange_surjective [IsAlgClosed k]
    [AlgebraicGeometry.IsAbelianVariety k A] (n : ℕ) (hn : IsUnit (n : k)) :
    Function.Surjective (torsionPointBaseChange A K n) := by
  set pK : Spec (.of K) := IsLocalRing.closedPoint K
  set pk : Spec (.of k) := IsLocalRing.closedPoint k
  have hn' : IsUnit ((n : ℤ) : k) := by simpa using hn
  have : Etale ((𝟙 A : A ⟶ A) ^ (n : ℤ)).left := etale_zpow_id_left_of_isUnit A n hn'
  rintro ⟨y, hy⟩
  have hY : (y.toMul.left : Spec (.of K) ⟶ pullback A.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ≫
        pullback.snd A.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) = 𝟙 _ :=
    Over.w y.toMul
  have hyn : y.toMul ^ n = 1 := (mem_torsionBy_int_iff_pow y.toMul n).mp hy
  have hmap : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map
      ((𝟙 A : A ⟶ A) ^ (n : ℤ)) =
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map (𝟙 A)) ^ n := by
    rw [zpow_natCast]
    exact ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).homMonoidHom
      (X := A) (M := A)).map_pow (𝟙 A) n
  have hpow : y.toMul ≫ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map
      ((𝟙 A : A ⟶ A) ^ (n : ℤ)) = 1 := by
    rw [hmap, CategoryTheory.Functor.map_id, MonObj.comp_pow, Category.comp_id, hyn]
  have hone : (1 : 𝟙_ (Over (Spec (.of K))) ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A) =
        (pointBaseChange A K 0).toMul := by
    rw [map_zero, toMul_zero]
  have hu : (y.toMul.left ≫ pullback.fst A.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
      Spec (.of K) ⟶ A.left) ≫ ((𝟙 A : A ⟶ A) ^ (n : ℤ)).left =
        Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ (η[A]).left := by
    have h1 := congrArg (fun t => t.left ≫
      pullback.fst A.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))) hpow
    simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst] at h1
    rw [hone, pointBaseChange_left_fst] at h1
    rw [Category.assoc]
    exact h1.trans (congrArg (fun t => Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫
      Over.Hom.left t) (MonObj.one_eq_one A).symm)
  have hgpt : (Spec.map (CommRingCat.ofHom (algebraMap k K)) : Spec (.of K) ⟶ Spec (.of k)) pK =
      pk := Subsingleton.elim _ _
  set a : A.left := (y.toMul.left ≫
    pullback.fst A.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
      Spec (.of K) ⟶ A.left) pK with ha_def
  have hNa : ((𝟙 A : A ⟶ A) ^ (n : ℤ)).left a = (η[A]).left pk := by
    have h := congrArg (fun f : Spec (.of K) ⟶ A.left => f pK) hu
    simp only [Scheme.Hom.comp_apply] at h
    rw [ha_def, Scheme.Hom.comp_apply, h, hgpt]
  have ha : IsClosed {a} :=
    Scheme.Hom.isClosed_singleton_of_apply_eq ((𝟙 A : A ⟶ A) ^ (n : ℤ)).left
      (isClosed_singleton_unit_left A pk) hNa
  let x : 𝟙_ (Over (Spec (.of k))) ⟶ A :=
    Over.homMk (pointOfClosedPoint A.hom a ha) (pointOfClosedPoint_comp A.hom a ha)
  have hxa : (x.left : Spec (.of k) ⟶ A.left) pk = a := pointOfClosedPoint_apply A.hom a ha pk
  have hxl : (x.left : Spec (.of k) ⟶ A.left) ≫ A.hom = 𝟙 _ := Over.w x
  have hxN : x ≫ (𝟙 A : A ⟶ A) ^ (n : ℤ) = η[A] := by
    refine eq_of_apply_closedPoint_eq A ?_
    exact (congrArg ((𝟙 A : A ⟶ A) ^ (n : ℤ)).left hxa).trans hNa
  have hxpow : x ^ n = 1 := by
    rw [← MonObj.one_eq_one A, ← hxN, zpow_natCast, MonObj.comp_pow, Category.comp_id]
  refine ⟨⟨Additive.ofMul x, (mem_torsionBy_int_iff_pow x n).mpr hxpow⟩, Subtype.ext ?_⟩
  rw [torsionPointBaseChange_apply_coe]
  apply Additive.toMul.injective
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [pointBaseChange_left_fst, toMul_ofMul]
    refine ext_of_apply_closedPoint_eq_of_comp_eq A.hom ha ?_ ha_def.symm ?_
    · exact (congrArg x.left hgpt).trans hxa
    · rw [Category.assoc, hxl, Category.assoc, pullback.condition, reassoc_of% hY]
      exact Category.comp_id _
  · rw [pointBaseChange_left_snd]
    exact hY.symm

/-- **Base change of `n`-torsion points `A(k)[n] → A_K(K)[n]` is bijective** for `k`
algebraically closed, `K/k` any field extension and `n` invertible in `k`. -/
theorem torsionPointBaseChange_bijective [IsAlgClosed k]
    [AlgebraicGeometry.IsAbelianVariety k A] (n : ℕ) (hn : IsUnit (n : k)) :
    Function.Bijective (torsionPointBaseChange A K n) :=
  ⟨fun _ _ hxy => Subtype.ext (pointBaseChange_injective A K (congrArg Subtype.val hxy)),
    torsionPointBaseChange_surjective A K n hn⟩

/-- **Base change of `n`-torsion points as an additive isomorphism `A(k)[n] ≃+ A_K(K)[n]`**,
for `k` algebraically closed and `n` invertible in `k`. -/
noncomputable def torsionPointBaseChangeEquiv [IsAlgClosed k]
    [AlgebraicGeometry.IsAbelianVariety k A] (n : ℕ) (hn : IsUnit (n : k)) :
    Submodule.torsionBy ℤ (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) (n : ℤ) ≃+
      Submodule.torsionBy ℤ (Additive (𝟙_ (Over (Spec (.of K))) ⟶
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A)) (n : ℤ) :=
  AddEquiv.ofBijective (torsionPointBaseChange A K n) (torsionPointBaseChange_bijective A K n hn)

/-- The isomorphism `A(k)[n] ≃+ A_K(K)[n]` sends a torsion point to its base change. -/
@[simp]
theorem torsionPointBaseChangeEquiv_apply_coe [IsAlgClosed k]
    [AlgebraicGeometry.IsAbelianVariety k A] (n : ℕ) (hn : IsUnit (n : k))
    (x : Submodule.torsionBy ℤ (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) (n : ℤ)) :
    (torsionPointBaseChangeEquiv A K n hn x : Additive (𝟙_ (Over (Spec (.of K))) ⟶
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A)) =
      pointBaseChange A K x :=
  rfl

end Stacks.Groupoids

end
