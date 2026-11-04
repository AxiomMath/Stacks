module

public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalPointFibreOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.CoproductUniformAtlas
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.Deformation.Artin.RimSchlessinger

/-!
# Axiom [-1] for the fibre `𝒴` of the diagonal in the proof of Stacks 07Y5

Let `𝒳` be a category fibred in groupoids over the big fppf site of `S`, let `V` be an affine
object of that site and let `y` be a point of `𝒳 × 𝒳` over `V`. The proof of Stacks 07Y5 applies
Proposition 07Y1 to the functor `Y` of isomorphism classes of

`𝒴 = (Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳`,

and the set-theoretic axiom [-1] for `Y` is one of the details the source omits. This file proves
it from axiom [-1] for `𝒳`.

An object of `𝒴` over `U` is a morphism `t : U ⟶ V` together with an object of `𝒳` over `U` and an
isomorphism of its diagonal image with `y|_t`; its class is determined by `t` and by the twist
`y₁|_t ≅ y₂|_t`, an arrow of the fibre `𝒳_U`
(`CategoryTheory.TwoFibreProductOver.DiagonalPoint.nonempty_iso_of_structureTwist_eq`). Hence

`|Ob(𝒴_U)/≅| ≤ |Mor_S(U, V)| · |Arrows(𝒳_U)|`.

For `U = Spec(k)` with `k` of finite type over `S`, the second factor is bounded by axiom [-1]
for `𝒳`, and the first by `2 ^ max(size S, size V)`: a morphism to the affine scheme `V` is
determined by its map on global sections, `|k| ≤ size S` (Stacks 04T7) and
`|Γ(V, 𝒪_V)| ≤ size V`. An object of the site of at least that size exists because the cutoff of
the site is a strong limit.

## Main results

* `AlgebraicGeometry.Stack.mk_isoClasses_diagonalPointFibreOverBase_le`: the displayed bound.
* `AlgebraicGeometry.Stack.diagonalPointFibreOverBase_isSizeBounded`: axiom [-1] for `𝒴`, the
  isomorphism-class half.
* `AlgebraicGeometry.Stack.diagonalPointFunctorOverBase_isSizeBounded`: axiom [-1] for `Y`, in
  the form of Section 07XZ.

## References

* [Stacks Project, Tag 07Y5](https://stacks.math.columbia.edu/tag/07Y5)
* [Stacks Project, Tag 07XJ](https://stacks.math.columbia.edu/tag/07XJ)
* [Stacks Project, Tag 07XZ](https://stacks.math.columbia.edu/tag/07XZ)
-/

@[expose] public section

open CategoryTheory Cardinal

namespace CategoryTheory.TwoFibreProductOver.DiagonalPoint

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒯 : Type u₂} [Category.{v₂} 𝒯]
  {𝒮 : Type u₃} [Category.{v₃} 𝒮]
  {pT : 𝒯 ⥤ 𝒞} {p : 𝒮 ⥤ 𝒞} {y : 𝒯 ⥤ TwoFibreProductOver p p (𝟭 𝒞) p p}

attribute [local instance_reducible] diagonal

/-- The twist of an object of `𝒯 ×_{y, 𝒮 × 𝒮, Δ} 𝒮` is vertical: it lies over the identity of
the base of the object. -/
lemma isHomLift_twist (P : DiagonalPoint pT p y) : p.IsHomLift (𝟙 P.base) (twist P) := by
  have : (structureFunctor p p (𝟭 𝒞) p p).IsHomLift (𝟙 P.base) P.iso.hom := P.vertical
  have : (structureFunctor p p (𝟭 𝒞) p p).IsHomLift (𝟙 P.base) P.iso.inv := inferInstance
  have : p.IsHomLift (𝟙 P.base) P.iso.hom.a := isHomLift_a_of_isHomLift _ P.iso.hom
  have : p.IsHomLift (𝟙 P.base) P.iso.inv.b := isHomLift_b_of_isHomLift _ P.iso.inv
  unfold twist
  infer_instance

end CategoryTheory.TwoFibreProductOver.DiagonalPoint

namespace AlgebraicGeometry.Stack

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {V : BigFppfOver B S hS}
  {y : BigFppfOver B V.left.1 V.left.2 ⥤ (CatFiberedInGroupoids.product 𝒳 𝒳).val.obj}

/-- **The isomorphism classes of a fibre of `𝒴`** are at most as many as the pairs of a morphism
`t : U ⟶ V` and an arrow of the fibre `𝒳_U`. -/
theorem mk_isoClasses_diagonalPointFibreOverBase_le (U : BigFppfOver B S hS) :
    #(_root_.Quotient (isIsomorphicSetoid ((diagonalPointFibreOverBase B S hS 𝒳 V y).Fiber U))) ≤
      #{t : BigFppfOver B V.left.1 V.left.2 // (Over.map V.hom).obj t = U} *
        #(Σ a b : 𝒳.val.p.Fiber U, a ⟶ b) := by
  have := faithful_sliceMap V.hom
  let T := {t : BigFppfOver B V.left.1 V.left.2 // (Over.map V.hom).obj t = U}
  let A : T → Type (u + 1) := fun t =>
    ULift.{u + 1} {φ : (y.obj t.1).x ⟶ (y.obj t.1).y // 𝒳.val.p.IsHomLift (𝟙 U) φ}
  let F : _root_.Quotient (isIsomorphicSetoid ((diagonalPointFibreOverBase B S hS 𝒳 V y).Fiber U)) →
      Σ t : T, A t := fun q =>
    ⟨⟨q.out.1.x, q.out.1.hx.trans q.out.2⟩,
      ⟨⟨TwoFibreProductOver.DiagonalPoint.twist q.out.1, by
        have h := TwoFibreProductOver.DiagonalPoint.isHomLift_twist q.out.1
        have hb : q.out.1.base = U := q.out.2
        rw [hb] at h
        exact h⟩⟩⟩
  have hF : Function.Injective F := by
    intro q q' h
    have h' := congrArg (@Sigma.map T T A (fun t => (y.obj t.1).x ⟶ (y.obj t.1).y) id
      (fun _ φ => φ.down.1)) h
    rw [← _root_.Quotient.out_eq q, ← _root_.Quotient.out_eq q']
    exact Functor.isoClassMk_eq_of_iso
      (TwoFibreProductOver.DiagonalPoint.nonempty_iso_of_structureTwist_eq _ _ h').some
  have hA (t : T) : #(A t) ≤ #(Σ a b : 𝒳.val.p.Fiber U, a ⟶ b) := by
    refine mk_le_of_injective (f := fun φ =>
      have := φ.down.2
      ⟨_, _, Functor.Fiber.homMk 𝒳.val.p U φ.down.1⟩) ?_
    rintro ⟨φ, hφ⟩ ⟨ψ, hψ⟩ h
    have h₁ := (Sigma.mk.inj_iff.1 h).2
    have h₂ := (Sigma.mk.inj_iff.1 (eq_of_heq h₁)).2
    have h₃ := congrArg (fun k => Functor.Fiber.fiberInclusion.map k) (eq_of_heq h₂)
    simp only [Functor.Fiber.fiberInclusion_homMk] at h₃
    subst h₃
    rfl
  calc #(_root_.Quotient (isIsomorphicSetoid ((diagonalPointFibreOverBase B S hS 𝒳 V y).Fiber U)))
      ≤ #(Σ t : T, A t) := mk_le_of_injective hF
    _ = Cardinal.sum (fun t => #(A t)) := mk_sigma _
    _ ≤ Cardinal.sum (fun _ : T => #(Σ a b : 𝒳.val.p.Fiber U, a ⟶ b)) := sum_le_sum _ _ hA
    _ = #T * #(Σ a b : 𝒳.val.p.Fiber U, a ⟶ b) := sum_const' _ _

/-- The morphisms over `S` from an object `U` of the site to `V` are at most as many as the
morphisms of schemes `U ⟶ V`. -/
theorem mk_overMap_fiber_le (U : BigFppfOver B S hS) :
    #{t : BigFppfOver B V.left.1 V.left.2 // (Over.map V.hom).obj t = U} ≤
      Cardinal.lift.{u + 1} #(U.left.1 ⟶ V.left.1) := by
  rw [← Cardinal.lift_id'.{u, u + 1} #{t : BigFppfOver B V.left.1 V.left.2 //
    (Over.map V.hom).obj t = U}]
  refine Cardinal.lift_mk_le_lift_mk_of_injective
    (f := fun t => B.inclusion.map (eqToHom (congrArg Comma.left t.2).symm ≫ t.1.hom)) ?_
  rintro ⟨⟨tl, ⟨⟩, th⟩, ht⟩ ⟨⟨tl', ⟨⟩, th'⟩, ht'⟩ h
  obtain rfl : tl = U.left := congrArg Comma.left ht
  obtain rfl : tl' = U.left := congrArg Comma.left ht'
  simp only [eqToHom_refl, Category.id_comp] at h
  obtain rfl : th = th' := B.inclusion.map_injective h
  rfl

/-- The morphisms of schemes from `Spec k` to an affine scheme `V` are at most
`2 ^ max (#k) (size V)`: a morphism to an affine scheme is determined by its map on global
sections. -/
theorem mk_hom_spec_le {k : Type u} [Field k] (W : Scheme.{u}) [IsAffine W] :
    #(Spec (.of k) ⟶ W) ≤ 2 ^ max (#k) W.size := by
  have hκ : ℵ₀ ≤ max (#k) W.size := le_max_of_le_right W.aleph0_le_size
  have hΓ : #Γ(Spec (.of k), ⊤) = #k := by
    rw [← Cardinal.mk_congr (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toEquiv.symm]
  calc #(Spec (.of k) ⟶ W) ≤ #(Γ(W, ⊤) →+* Γ(Spec (.of k), ⊤)) :=
        mk_le_of_injective (f := fun f => f.appTop.hom) (fun f g h =>
          ext_of_isAffine (CommRingCat.hom_ext h))
    _ ≤ #(Γ(W, ⊤) → Γ(Spec (.of k), ⊤)) := mk_le_of_injective DFunLike.coe_injective
    _ = #Γ(Spec (.of k), ⊤) ^ #Γ(W, ⊤) := by simp only [mk_arrow, lift_id]
    _ ≤ max (#k) W.size ^ max (#k) W.size := by
        rw [hΓ]
        exact (power_le_power_right (le_max_left _ _)).trans
          (power_le_power_left (aleph0_pos.trans_le hκ).ne'
            ((W.mk_sections_le_size ⟨⊤, isAffineOpen_top W⟩).trans (le_max_right _ _)))
    _ = 2 ^ max (#k) W.size := power_self_eq hκ

variable (hy : y ⋙ (CatFiberedInGroupoids.product 𝒳 𝒳).val.p = Over.map V.hom)

/-- **Axiom [-1] for `𝒴`** (the isomorphism classes of its fibres over finite type fields): if
the arrows of the fibres of `𝒳` over finite type fields are bounded by the size of an object
`T₀` of the site, and `V` is affine, then the isomorphism classes of the fibres of `𝒴` over
finite type fields are bounded by the size of an object of the site. -/
theorem diagonalPointFibreOverBase_isSizeBounded [IsAffine V.left.1]
    (hsize : ∃ T₀ : BigFppfOver B S hS,
      ∀ (U : BigFppfOver B S hS) (k : Type u) [Field k],
        U.left.1 = Spec (.of k) → Deformation.Artin.IsFiniteTypeOver B S hS U →
        Cardinal.lift.{u, u + 1} (#(Σ a b : 𝒳.val.p.Fiber U, a ⟶ b)) ≤
          Cardinal.lift.{u + 1, u} T₀.left.1.size) :
    ∃ T : BigFppfOver B S hS,
      ∀ (U : BigFppfOver B S hS) (k : Type u) [Field k],
        U.left.1 = Spec (.of k) → Deformation.Artin.IsFiniteTypeOver B S hS U →
        Cardinal.lift.{u, u + 1}
            (#(_root_.Quotient (isIsomorphicSetoid
              ((diagonalPointFibreOverBase B S hS 𝒳 V y).Fiber U)))) ≤
          Cardinal.lift.{u + 1, u} T.left.1.size := by
  obtain ⟨T₀, hT₀⟩ := hsize
  rcases isEmpty_or_nonempty S with hSe | hSne
  · refine ⟨T₀, fun U k _ hU _ => ?_⟩
    have x : U.left.1 := hU ▸ IsLocalRing.closedPoint k
    exact (hSe.false ((B.inclusion.map U.hom) x)).elim
  let ν : Cardinal.{u} := max (2 ^ max S.size V.left.1.size) T₀.left.1.size
  have hν : ν < B.cutoff := max_lt
    (B.cutoff_isStrongPrelimit (max_lt hS V.left.2)) T₀.left.2
  have hSν : S.size ≤ ν := le_max_of_le_left ((le_max_left _ _).trans (cantor _).le)
  obtain ⟨T, hT⟩ := BigFppfOver.exists_size_ge B S hS hSne ν hSν hν
  refine ⟨T, fun U k _ hU hft => ?_⟩
  have hν0 : ℵ₀ ≤ ν := S.aleph0_le_size.trans hSν
  have hk : #k ≤ S.size := by
    have : LocallyOfFiniteType (B.inclusion.map U.hom) := hft.1
    have : QuasiCompact (B.inclusion.map U.hom) := hft.2
    have h := Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact (B.inclusion.map U.hom)
    change U.left.1.size ≤ S.size at h
    rw [hU, Scheme.size_Spec] at h
    exact (le_max_right _ _).trans h
  have hhom : #(U.left.1 ⟶ V.left.1) ≤ ν := by
    rw [hU]
    exact (mk_hom_spec_le V.left.1).trans
      (le_max_of_le_left (power_le_power_left two_ne_zero (max_le_max hk le_rfl)))
  calc Cardinal.lift.{u, u + 1} (#(_root_.Quotient (isIsomorphicSetoid
          ((diagonalPointFibreOverBase B S hS 𝒳 V y).Fiber U))))
      ≤ Cardinal.lift.{u} (#{t : BigFppfOver B V.left.1 V.left.2 // (Over.map V.hom).obj t = U} *
          #(Σ a b : 𝒳.val.p.Fiber U, a ⟶ b)) :=
        Cardinal.lift_le.2 (mk_isoClasses_diagonalPointFibreOverBase_le (y := y) U)
    _ = Cardinal.lift.{u} #{t : BigFppfOver B V.left.1 V.left.2 // (Over.map V.hom).obj t = U} *
          Cardinal.lift.{u} #(Σ a b : 𝒳.val.p.Fiber U, a ⟶ b) := Cardinal.lift_mul _ _
    _ ≤ Cardinal.lift.{u + 1} ν * Cardinal.lift.{u + 1} ν := by
        refine mul_le_mul' ?_ ((hT₀ U k hU hft).trans (Cardinal.lift_le.2 (le_max_right _ _)))
        exact (Cardinal.lift_le.2 (mk_overMap_fiber_le (V := V) U)).trans (by
          rw [Cardinal.lift_lift]
          exact Cardinal.lift_le.2 hhom)
    _ = Cardinal.lift.{u + 1} ν := by
        rw [← Cardinal.lift_mul, mul_eq_self hν0]
    _ ≤ Cardinal.lift.{u + 1} T.left.1.size := Cardinal.lift_le.2 hT

/-- **Axiom [-1] for `Y`** in the form of Section 07XZ: for `V` affine, the values of the functor
`Y` of isomorphism classes of `𝒴` on the finite type fields over `S` are bounded by the size of
one object of the site. -/
theorem diagonalPointFunctorOverBase_isSizeBounded [IsAffine V.left.1]
    (hsize : ∃ T₀ : BigFppfOver B S hS,
      ∀ (U : BigFppfOver B S hS) (k : Type u) [Field k],
        U.left.1 = Spec (.of k) → Deformation.Artin.IsFiniteTypeOver B S hS U →
        Cardinal.lift.{u, u + 1} (#(Σ a b : 𝒳.val.p.Fiber U, a ⟶ b)) ≤
          Cardinal.lift.{u + 1, u} T₀.left.1.size) :
    ∃ T : BigFppfOver B S hS,
      ∀ (U : BigFppfOver B S hS) (k : Type u) [Field k],
        U.left.1 = Spec (.of k) → Deformation.Artin.IsFiniteTypeOver B S hS U →
        #((diagonalPointFunctorOverBase hy).obj (Opposite.op U)) ≤ T.left.1.size := by
  obtain ⟨T, hT⟩ := diagonalPointFibreOverBase_isSizeBounded (y := y) hsize
  refine ⟨T, fun U k _ hU hft => ?_⟩
  let := (diagonalPointFibreOverBase_isFiberedInGroupoids hy).isFibered
  let := small_isoClassPresheaf_diagonalPointFibreOverBase hy
  have h : Cardinal.lift.{u + 1} #((diagonalPointFunctorOverBase hy).obj (Opposite.op U)) =
      Cardinal.lift.{u} #(_root_.Quotient (isIsomorphicSetoid
        ((diagonalPointFibreOverBase B S hS 𝒳 V y).Fiber U))) :=
    (Cardinal.lift_mk_eq'.2 ⟨Functor.isoClassPresheafModelEquiv.{u}
      (diagonalPointFibreOverBase B S hS 𝒳 V y) (Opposite.op U)⟩).symm
  exact Cardinal.lift_le.{u + 1}.1 (h.trans_le (hT U k hU hft))

end AlgebraicGeometry.Stack

end
