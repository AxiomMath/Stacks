module

public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingDiagonalMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LimitPreservingOnObjects
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverIso

/-!
# Relative descent of morphisms and equalities along an affine inverse limit

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf category of a
scheme `S`, and let `U = lim Uᵢ` be a cofiltered limit of affine schemes over `S`. Relative to `f`
there are two descent conditions on morphisms of `𝒳`, the stagewise content of full faithfulness
of the comparison `colim 𝒳_{Uᵢ} ⟶ 𝒳_U ×_{𝒴_U} colim 𝒴_{Uᵢ}` of Stacks 0CMW:

* `AlgebraicGeometry.Stack.RelativeDescentHom`: a vertical morphism `α` between pullbacks to `U`
  of two objects `a₁`, `a₂` over a stage, together with a vertical morphism `β : f a₁ ⟶ f a₂` at
  the stage whose pullback is `f α`, comes from a vertical morphism `m` at a later stage with
  `f m` the pullback of `β`;
* `AlgebraicGeometry.Stack.RelativeDescentEq`: two vertical morphisms at a stage which agree over
  `U` and have the same image under `f` already agree at a later stage.

Both are read off limit preservation on objects (Stacks 06CU) of a diagonal: the first of the
relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳`, the second of the diagonal `Δ_{Δ_f}` of `Δ_f`.

## Main definitions

* `AlgebraicGeometry.Stack.RelativeDescentHom`
* `AlgebraicGeometry.Stack.RelativeDescentEq`

## Main results

* `AlgebraicGeometry.Stack.relativeDescentHom_of_isLimitPreservingOnObjects_diagonal`
* `AlgebraicGeometry.Stack.relativeDescentEq_of_isLimitPreservingOnObjects_diagonal_diagonal`

## Implementation notes

An object of `𝒳 ×_𝒴 𝒳` over a stage is a triple `(a₁, a₂, β)` with `β : f a₁ ≅ f a₂` vertical,
and a morphism `Δ_f(x) ⟶ (a₁, a₂, β)` lying over `U ⟶ Uᵢ` is a pair of morphisms `x ⟶ a₁`,
`x ⟶ a₂` over `U ⟶ Uᵢ` intertwining `β` with the identity of `f x`. Limit preservation on objects
of `Δ_f` descends such a pair to a stage, which is exactly a descended morphism `a₁ ⟶ a₂`
compatible with `β`. One level up, an object of `𝒳 ×_{𝒳 ×_𝒴 𝒳} 𝒳` over a stage is a triple
`(b₁, b₂, (m, m'))` with `m, m' : b₁ ⟶ b₂` vertical and `f m = f m'`, and a morphism from
`Δ_{Δ_f}(x)` into it is a morphism `x ⟶ b₁` equalising `m` and `m'`; descending it equalises them
at a stage.

The two conditions are stated for an arbitrary cofiltered diagram of affine schemes with a cone,
the limiting hypothesis being carried by the results, and with the restrictions to the limit and
to the later stage given as arbitrary morphisms lying over the cone and transition maps, as in
`Deformation.Artin.DescentHom`.

## References

* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 0CMV](https://stacks.math.columbia.edu/tag/0CMV)
* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u v w v' w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w} (BigFppfOver B S hS)}

/-- **Relative descent of morphisms.** Let `a₁`, `a₂` be objects of `𝒳` over a stage `Uᵢ`, with
pullbacks `δ₁ : x₁ ⟶ a₁`, `δ₂ : x₂ ⟶ a₂` to the limit `U`; let `β : f a₁ ⟶ f a₂` be vertical and
let `α : x₁ ⟶ x₂` be vertical with `f α` the pullback of `β`. Then at some later stage `Uₖ` there
are pullbacks `d₁ : b₁ ⟶ a₁`, `d₂ : b₂ ⟶ a₂`, a vertical `m : b₁ ⟶ b₂` with `f m` the pullback of
`β`, and a pullback `ε : x₁ ⟶ b₁` of `b₁` to `U` along which `m` pulls back to `α`. -/
def RelativeDescentHom (f : 𝒳 ⟶ 𝒴) {I : Type v'} [Category.{w'} I]
    (D : I ⥤ BigAffineFppf B S hS) (c : Cone D) : Prop :=
  ∀ (i : I) (a₁ a₂ : 𝒳.val.p.Fiber ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
    (x₁ x₂ : 𝒳.val.p.Fiber ((BigAffineFppf.inclusion B S hS).obj c.pt))
    (δ₁ : x₁.1 ⟶ a₁.1) (δ₂ : x₂.1 ⟶ a₂.1),
    𝒳.val.p.IsHomLift ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) δ₁ →
    𝒳.val.p.IsHomLift ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) δ₂ →
    ∀ (β : (CatFiberedInGroupoids.homFunctor f).obj a₁.1 ⟶
        (CatFiberedInGroupoids.homFunctor f).obj a₂.1),
      𝒴.val.p.IsHomLift (𝟙 ((BigAffineFppf.inclusion B S hS).obj (D.obj i))) β →
    ∀ (α : x₁.1 ⟶ x₂.1),
      𝒳.val.p.IsHomLift (𝟙 ((BigAffineFppf.inclusion B S hS).obj c.pt)) α →
      (CatFiberedInGroupoids.homFunctor f).map α ≫ (CatFiberedInGroupoids.homFunctor f).map δ₂ =
        (CatFiberedInGroupoids.homFunctor f).map δ₁ ≫ β →
    ∃ (k : I) (s : k ⟶ i) (b₁ b₂ : 𝒳.val.p.Fiber ((BigAffineFppf.inclusion B S hS).obj (D.obj k)))
      (d₁ : b₁.1 ⟶ a₁.1) (d₂ : b₂.1 ⟶ a₂.1) (ε : x₁.1 ⟶ b₁.1) (m : b₁.1 ⟶ b₂.1),
      𝒳.val.p.IsHomLift ((BigAffineFppf.inclusion B S hS).map (D.map s)) d₁ ∧
      𝒳.val.p.IsHomLift ((BigAffineFppf.inclusion B S hS).map (D.map s)) d₂ ∧
      𝒳.val.p.IsHomLift ((BigAffineFppf.inclusion B S hS).map (c.π.app k)) ε ∧
      𝒳.val.p.IsHomLift (𝟙 ((BigAffineFppf.inclusion B S hS).obj (D.obj k))) m ∧
      ε ≫ d₁ = δ₁ ∧ ε ≫ m ≫ d₂ = α ≫ δ₂ ∧
      (CatFiberedInGroupoids.homFunctor f).map m ≫ (CatFiberedInGroupoids.homFunctor f).map d₂ =
        (CatFiberedInGroupoids.homFunctor f).map d₁ ≫ β

/-- **Relative descent of equalities.** Two vertical morphisms `m, m' : b₁ ⟶ b₂` over a stage
`Uᵢ` which have the same image under `f` and agree after pulling back along some `δ : x ⟶ b₁` over
`U ⟶ Uᵢ` already agree after pulling back along some `d : b ⟶ b₁` over a transition map. -/
def RelativeDescentEq (f : 𝒳 ⟶ 𝒴) {I : Type v'} [Category.{w'} I]
    (D : I ⥤ BigAffineFppf B S hS) (c : Cone D) : Prop :=
  ∀ (i : I) (b₁ b₂ : 𝒳.val.p.Fiber ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
    (x : 𝒳.val.p.Fiber ((BigAffineFppf.inclusion B S hS).obj c.pt)) (δ : x.1 ⟶ b₁.1),
    𝒳.val.p.IsHomLift ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) δ →
    ∀ (m m' : b₁.1 ⟶ b₂.1),
      𝒳.val.p.IsHomLift (𝟙 ((BigAffineFppf.inclusion B S hS).obj (D.obj i))) m →
      𝒳.val.p.IsHomLift (𝟙 ((BigAffineFppf.inclusion B S hS).obj (D.obj i))) m' →
      δ ≫ m = δ ≫ m' →
      (CatFiberedInGroupoids.homFunctor f).map m = (CatFiberedInGroupoids.homFunctor f).map m' →
    ∃ (k : I) (s : k ⟶ i) (b : 𝒳.val.p.Fiber ((BigAffineFppf.inclusion B S hS).obj (D.obj k)))
      (d : b.1 ⟶ b₁.1),
      𝒳.val.p.IsHomLift ((BigAffineFppf.inclusion B S hS).map (D.map s)) d ∧ d ≫ m = d ≫ m'

/-- **Limit preservation on objects of the relative diagonal gives relative descent of
morphisms.** The data `(δ₁, α ≫ δ₂)` is a morphism from `Δ_f(x₁)` to the object `(a₁, a₂, β)` of
`𝒳 ×_𝒴 𝒳` over the stage; descending it along limit preservation on objects of `Δ_f` produces an
object `b` at a later stage with two pullbacks `b ⟶ a₁`, `b ⟶ a₂` intertwining `β`, and `m` is the
identity of `b`. -/
theorem relativeDescentHom_of_isLimitPreservingOnObjects_diagonal (f : 𝒳 ⟶ 𝒴)
    (hΔ : BigFppfOver.IsLimitPreservingOnObjects.{u, v', w'} B S hS 𝒳
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f)
      (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f))
    {I : Type v'} [Category.{w'} I] [IsCofiltered I] (D : I ⥤ BigAffineFppf B S hS) (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    RelativeDescentHom B S hS f D c := by
  intro i a₁ a₂ x₁ x₂ δ₁ δ₂ hδ₁ hδ₂ β hβ α hα hw
  let inc := BigAffineFppf.inclusion B S hS
  let F := CatFiberedInGroupoids.homFunctor f
  have hF : F ⋙ 𝒴.val.p = 𝒳.val.p := CatFiberedInGroupoids.homFunctor_comp_p f
  have hβc : 𝒴.val.p.IsStronglyCartesian (𝟙 (inc.obj (D.obj i))) β :=
    𝒴.2.isStronglyCartesian_homLift _ _
  have : IsIso β := Functor.IsStronglyCartesian.isIso_of_base_isIso (p := 𝒴.val.p)
    (f := 𝟙 (inc.obj (D.obj i))) β
  let P := BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f
  let yP : TwoFibreProductOver 𝒳.val.p 𝒳.val.p 𝒴.val.p F F :=
    { base := inc.obj (D.obj i)
      x := a₁.1
      y := a₂.1
      hx := a₁.2
      hy := a₂.2
      iso := asIso β
      vertical := hβ }
  let y : P.val.p.Fiber (inc.obj (D.obj i)) := ⟨yP, rfl⟩
  have hδ₂' : 𝒳.val.p.IsHomLift (inc.map (c.π.app i)) (α ≫ δ₂) := by
    have h := IsHomLift.comp (p := 𝒳.val.p) (𝟙 (inc.obj c.pt)) (inc.map (c.π.app i)) α δ₂
    rwa [Category.id_comp] at h
  let γ : (CatFiberedInGroupoids.homFunctor
      (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f)).obj x₁.1 ⟶ y.1 :=
    TwoFibreProductOver.Hom.mk' δ₁ (α ≫ δ₂)
      (by
        have h₁ := IsHomLift.fac' 𝒳.val.p (inc.map (c.π.app i)) δ₁
        have h₂ := IsHomLift.fac' 𝒳.val.p (inc.map (c.π.app i)) (α ≫ δ₂)
        change eqToHom rfl ≫ 𝒳.val.p.map (α ≫ δ₂) ≫ eqToHom a₂.2 =
          eqToHom rfl ≫ 𝒳.val.p.map δ₁ ≫ eqToHom a₁.2
        rw [h₁, h₂]
        simp)
      (by
        change F.map δ₁ ≫ β = 𝟙 _ ≫ F.map (α ≫ δ₂)
        rw [Category.id_comp, F.map_comp, hw])
  have hγ : P.val.p.IsStronglyCartesian (inc.map (c.π.app i)) γ := by
    have : P.val.p.IsHomLift (inc.map (c.π.app i)) γ :=
      TwoFibreProductOver.structureFunctor_isHomLift γ _ hδ₁
    exact P.2.isStronglyCartesian_homLift _ _
  obtain ⟨k, s, b, xU, δ, β', γ', hδ, hβ', hβ'iso, hγ', hcomm⟩ :=
    hΔ I D c hc i y x₁ γ hγ
  have hγ'l : P.val.p.IsHomLift (inc.map (D.map s)) γ' := hγ'.toIsHomLift
  have hd₁ : 𝒳.val.p.IsHomLift (inc.map (D.map s)) γ'.a :=
    TwoFibreProductOver.isHomLift_a γ' _ hγ'l
  have hd₂ : 𝒳.val.p.IsHomLift (inc.map (D.map s)) γ'.b :=
    TwoFibreProductOver.isHomLift_b γ' _ hγ'l
  have hca := congrArg TwoFibreProductOver.Hom.a hcomm
  have hcb := congrArg TwoFibreProductOver.Hom.b hcomm
  change δ ≫ γ'.a = β' ≫ δ₁ at hca
  change δ ≫ γ'.b = β' ≫ (α ≫ δ₂) at hcb
  have hε : 𝒳.val.p.IsHomLift (inc.map (c.π.app k)) (inv β' ≫ δ) := by
    have := hβ'
    have := hδ.toIsHomLift
    have h := IsHomLift.comp (p := 𝒳.val.p) (𝟙 (inc.obj c.pt)) (inc.map (c.π.app k))
      (inv β') δ
    rwa [Category.id_comp] at h
  refine ⟨k, s, b, b, γ'.a, γ'.b, inv β' ≫ δ, 𝟙 b.1, hd₁, hd₂, hε, IsHomLift.id b.2, ?_, ?_, ?_⟩
  · exact (Category.assoc _ _ _).trans
      ((congrArg (inv β' ≫ ·) hca).trans (IsIso.inv_hom_id_assoc _ _))
  · exact (congrArg ((inv β' ≫ δ) ≫ ·) (Category.id_comp _)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (inv β' ≫ ·) hcb).trans (IsIso.inv_hom_id_assoc _ _)))
  · have hw' := γ'.w
    change F.map γ'.a ≫ β = 𝟙 _ ≫ F.map γ'.b at hw'
    exact ((congrArg (· ≫ F.map γ'.b) (F.map_id _)).trans (Category.id_comp _)).trans
      (hw'.trans (Category.id_comp _)).symm

/-- **Limit preservation on objects of the second diagonal gives relative descent of
equalities.** The pair `(m, m')` is a vertical isomorphism `Δ_f(b₁) ≅ Δ_f(b₂)` of `𝒳 ×_𝒴 𝒳`, so
`(b₁, b₂, (m, m'))` is an object of `𝒳 ×_{𝒳 ×_𝒴 𝒳} 𝒳` over the stage, and `(δ, δ ≫ m)` is a
morphism into it from `Δ_{Δ_f}(x)` exactly because `δ ≫ m = δ ≫ m'`. Descending it produces a
morphism `d` into `b₁` over a transition map with `d ≫ m` and `d ≫ m'` both equal to the second
component, so `d` equalises `m` and `m'`. -/
theorem relativeDescentEq_of_isLimitPreservingOnObjects_diagonal_diagonal (f : 𝒳 ⟶ 𝒴)
    (hΔΔ : BigFppfOver.IsLimitPreservingOnObjects.{u, v', w'} B S hS 𝒳
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳
        (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f) 𝒳
        (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f)
        (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f))
      (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳
        (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f)
        (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f)))
    {I : Type v'} [Category.{w'} I] [IsCofiltered I] (D : I ⥤ BigAffineFppf B S hS) (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    RelativeDescentEq B S hS f D c := by
  intro i b₁ b₂ x δ hδ m m' hm hm' hδm hfm
  let inc := BigAffineFppf.inclusion B S hS
  let F := CatFiberedInGroupoids.homFunctor f
  let P := BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f
  let Δ := BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f
  let G := CatFiberedInGroupoids.homFunctor Δ
  let Q := BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 P 𝒳 Δ Δ
  have hbase : ∀ (n : b₁.1 ⟶ b₂.1),
      𝒳.val.p.IsHomLift (𝟙 (inc.obj (D.obj i))) n →
        𝒳.val.p.map n = eqToHom (b₁.2.trans b₂.2.symm) := by
    intro n hn
    rw [IsHomLift.fac' 𝒳.val.p (𝟙 (inc.obj (D.obj i))) n]
    simp
  let φ : G.obj b₁.1 ⟶ G.obj b₂.1 :=
    TwoFibreProductOver.Hom.mk' m m'
      (by
        change eqToHom rfl ≫ 𝒳.val.p.map m' ≫ eqToHom rfl =
          eqToHom rfl ≫ 𝒳.val.p.map m ≫ eqToHom rfl
        rw [hbase m hm, hbase m' hm'])
      (by
        change F.map m ≫ 𝟙 _ = 𝟙 _ ≫ F.map m'
        rw [Category.comp_id, Category.id_comp, hfm])
  have hφ : P.val.p.IsHomLift (𝟙 (inc.obj (D.obj i))) φ :=
    TwoFibreProductOver.structureFunctor_isHomLift φ _ hm
  have : IsIso φ := TwoFibreProductOver.isIso_of_isHomLift_id 𝒳.2 𝒳.2 φ hφ
  let yQ : TwoFibreProductOver 𝒳.val.p 𝒳.val.p P.val.p G G :=
    { base := inc.obj (D.obj i)
      x := b₁.1
      y := b₂.1
      hx := b₁.2
      hy := b₂.2
      iso := asIso φ
      vertical := hφ }
  let y : Q.val.p.Fiber (inc.obj (D.obj i)) := ⟨yQ, rfl⟩
  have hδm' : 𝒳.val.p.IsHomLift (inc.map (c.π.app i)) (δ ≫ m) := by
    have h := IsHomLift.comp (p := 𝒳.val.p) (inc.map (c.π.app i))
      (𝟙 (inc.obj (D.obj i))) δ m
    rwa [Category.comp_id] at h
  let γ : (CatFiberedInGroupoids.homFunctor
      (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 P Δ)).obj x.1 ⟶ y.1 :=
    TwoFibreProductOver.Hom.mk' δ (δ ≫ m)
      (by
        have h₁ := IsHomLift.fac' 𝒳.val.p (inc.map (c.π.app i)) δ
        have h₂ := IsHomLift.fac' 𝒳.val.p (inc.map (c.π.app i)) (δ ≫ m)
        change eqToHom rfl ≫ 𝒳.val.p.map (δ ≫ m) ≫ eqToHom b₂.2 =
          eqToHom rfl ≫ 𝒳.val.p.map δ ≫ eqToHom b₁.2
        rw [h₁, h₂]
        simp)
      (by
        change G.map δ ≫ φ = 𝟙 _ ≫ G.map (δ ≫ m)
        rw [Category.id_comp]
        refine TwoFibreProductOver.Hom.ext' ?_ ?_
        · change δ ≫ m = δ ≫ m
          rfl
        · change δ ≫ m' = δ ≫ m
          exact hδm.symm)
  have hγ : Q.val.p.IsStronglyCartesian (inc.map (c.π.app i)) γ := by
    have : Q.val.p.IsHomLift (inc.map (c.π.app i)) γ :=
      TwoFibreProductOver.structureFunctor_isHomLift γ _ hδ
    exact Q.2.isStronglyCartesian_homLift _ _
  obtain ⟨k, s, b, xU, ε, β', γ', hε, hβ', hβ'iso, hγ', hcomm⟩ :=
    hΔΔ I D c hc i y x γ hγ
  have hγ'l : Q.val.p.IsHomLift (inc.map (D.map s)) γ' := hγ'.toIsHomLift
  have hd : 𝒳.val.p.IsHomLift (inc.map (D.map s)) γ'.a :=
    TwoFibreProductOver.isHomLift_a γ' _ hγ'l
  have hw := γ'.w
  change G.map γ'.a ≫ φ = 𝟙 _ ≫ G.map γ'.b at hw
  rw [Category.id_comp] at hw
  have ha := congrArg TwoFibreProductOver.Hom.a hw
  have hb := congrArg TwoFibreProductOver.Hom.b hw
  change γ'.a ≫ m = γ'.b at ha
  change γ'.a ≫ m' = γ'.b at hb
  exact ⟨k, s, b, γ'.a, hd, ha.trans hb.symm⟩

end AlgebraicGeometry.Stack

end
