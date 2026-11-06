module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartBaseChangeCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleStabilizerPreservingIsomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSeparatedChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesEtaleAmbient
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveGeometricTwoArrows
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Restriction

/-!
# A cartesian criterion for squares over algebraic spaces

Let `h : 𝒳' ⟶ 𝒳` be a 1-morphism of algebraic stacks, `f : 𝒳 ⟶ M` and `f' : 𝒳' ⟶ M'` 1-morphisms to
algebraic spaces and `g : M' ⟶ M` a morphism of algebraic spaces with `f' ≫ g = h ≫ f`. Both the
proof of the Keel–Mori theorem (Stacks 0DUT, the squares `𝒳ᵢ ⟶ Mᵢ ×_M 𝒳`) and the proof of Stacks
0DUV conclude that such a square is cartesian from the same facts: `h` is étale and induces
isomorphisms between automorphism groups (Stacks 0DTW), `g` is étale, `f` is injective on
isomorphism classes of geometric points and `f'` is bijective from isomorphism classes of geometric
points onto geometric points of `M'`. This file proves that criterion, following the proof of
Stacks 0DUD for the comparison `𝒳' ⟶ M' ×_M 𝒳`.

## Main results

* `AlgebraicGeometry.Stack.spaceModuliComparison`: the comparison `𝒳' ⟶ M' ×_M 𝒳`.
* `AlgebraicGeometry.Stack.isEtale_spaceModuliComparison`
* `AlgebraicGeometry.Stack.full_geometricFibreFunctor_spaceModuliComparison`
* `AlgebraicGeometry.Stack.essSurj_geometricFibreFunctor_spaceModuliComparison`
* `AlgebraicGeometry.Stack.nonempty_isTwoFibreProduct_spaceModuliSquare`: the criterion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Criterion

variable {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} (h : 𝒳' ⟶ 𝒳)
  {M M' : AlgebraicSpaces B S hS}
  (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS M.obj M.property)
  (f' : 𝒳' ⟶ algebraicSpaceStack.{u, w} B S hS M'.obj M'.property) (g : M' ⟶ M)
  (hcomm : f'.hom ≫ (associatedMap B S hS g.hom).1 = h.hom ≫ f.hom)

/-- The commutative square `𝒳' ⟶ 𝒳` over `g : M' ⟶ M`, with first leg `f'` and second leg `h`. -/
noncomputable abbrev spaceModuliSquare :
    Bicategory.TwoCommSq (associatedMap B S hS g.hom).1 f.hom :=
  ⟨𝒳'.val, f'.hom, h.hom, eqToIso hcomm⟩

/-- The canonical 2-fibre product `M' ×_M 𝒳` in the 2-category of algebraic stacks. -/
noncomputable abbrev spaceModuliBaseChange :
    Bicategory.TwoCommSq ((algebraicSpaceStackFunctor.{u, w} B S hS).map g) f :=
  twoFibreProductSquareAlgebraicStacks B S hS ((algebraicSpaceStackFunctor.{u, w} B S hS).map g) f

/-- The comparison 1-morphism `𝒳' ⟶ M' ×_M 𝒳` of the square. -/
noncomputable def spaceModuliComparison : 𝒳' ⟶ (spaceModuliBaseChange B S hS f g).pt :=
  Bicategory.InducedBicategory.mkHom
    (CatFiberedInGroupoids.liftTwoFibreProductSquare.{u, u, u + 1, u + 1} _ _
      (spaceModuliSquare B S hS h f f' g hcomm))

/-- The comparison followed by the projection to `𝒳` is `h`. -/
theorem spaceModuliComparison_comp_snd :
    spaceModuliComparison B S hS h f f' g hcomm ≫ (spaceModuliBaseChange B S hS f g).snd = h :=
  rfl

/-- **A vertical morphism of the category attached to a presheaf of sets has equal source and
target.** -/
theorem fibredCategory_obj_eq_of_isHomLift_id {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {X Y : (fibredCategory B S hS F).val.obj} {V : BigFppfOver B S hS} (hX : X.base = V)
    (hY : Y.base = V) (φ : X ⟶ Y) (hφ : (fibredCategory B S hS F).val.p.IsHomLift (𝟙 V) φ) :
    X = Y :=
  PresheafOfCategories.obj_eq_of_elementOf_eq hX hY (by
    rw [ChartBaseChange.fibredCategory_elementOf_eq_map hX hY (𝟙 V) φ hφ]
    simp)

/-- The second leg of the canonical base change `M' ×_M 𝒳 ⟶ 𝒳` of an étale morphism of algebraic
spaces is relatively étale (Stacks 04XB), as a base change of the 1-morphism attached to it. -/
theorem isRelativelyEtale_spaceModuliBaseChange_snd (hg : Space.IsEtale B S hS g.hom) :
    IsRelativelyEtale B S hS (spaceModuliBaseChange B S hS f g).snd.hom := by
  have hrep : IsRepresentableByAlgebraicSpaces B S hS
      ((algebraicSpaceStackFunctor.{u, w} B S hS).map g).hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS
      ((algebraicSpaceStackFunctor.{u, w} B S hS).obj M).property
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS M'.obj M'.property) _
  exact isRelativelyEtale_baseChange B S hS _ _ _ _ _
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      ((algebraicSpaceStackFunctor.{u, w} B S hS).map g).hom f.hom).swap
    (Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _))
    (isRelativelyEtale_of_isEtale B S hS _ hrep
      ((isEtale_algebraicSpaceStackFunctor_map_iff g).2 hg))

/-- The comparison `𝒳' ⟶ M' ×_M 𝒳` is representable by algebraic spaces when `h` is: its composite
with the representable projection `M' ×_M 𝒳 ⟶ 𝒳` is `h`. -/
theorem isRepresentableByAlgebraicSpaces_spaceModuliComparison
    (hg : Space.IsEtale B S hS g.hom)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS h.hom.hom) :
    IsRepresentableByAlgebraicSpaces B S hS
      (spaceModuliComparison B S hS h f f' g hcomm).hom.hom :=
  isRepresentableByAlgebraicSpaces_of_comp B S hS (spaceModuliComparison B S hS h f f' g hcomm).hom
    (spaceModuliBaseChange B S hS f g).snd.hom hrep
    (isRelativelyEtale_spaceModuliBaseChange_snd B S hS f g hg).1

/-- The comparison `𝒳' ⟶ M' ×_M 𝒳` is étale when `h` is étale and representable and `g` is
étale: both `h` and the projection `M' ×_M 𝒳 ⟶ 𝒳` are relatively étale (Stacks 04XB). -/
theorem isEtale_spaceModuliComparison (hg : Space.IsEtale B S hS g.hom)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS h.hom.hom) (he : IsEtale B S hS h) :
    IsEtale B S hS (spaceModuliComparison B S hS h f f' g hcomm) :=
  AlgebraicStacks.isEtale_of_isRelativelyEtale B S hS _
    (isRelativelyEtale_of_comp B S hS (spaceModuliComparison B S hS h f f' g hcomm).hom
      (spaceModuliBaseChange B S hS f g).snd.hom (isRelativelyEtale_of_isEtale B S hS h hrep he)
      (isRelativelyEtale_spaceModuliBaseChange_snd B S hS f g hg))

/-- **Fullness on geometric fibres.** If `h` is bijective on vertical automorphism groups and two
objects of `𝒳'` over the spectrum of an algebraically closed field with the same image in `M'`
are isomorphic over the identity, then the comparison `𝒳' ⟶ M' ×_M 𝒳` is full on the fibres
over that spectrum. -/
theorem full_geometricFibreFunctor_spaceModuliComparison
    (hAut : ∀ a, Function.Surjective (automorphismGroupMap B S hS h a))
    (hinj' : ∀ (k : Type u) [Field k] [IsAlgClosed k] (V : BigFppfOver B S hS),
      ((BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k)) →
      ∀ (x₁ x₂ : 𝒳'.val.val.obj), 𝒳'.val.val.p.obj x₁ = V → 𝒳'.val.val.p.obj x₂ = V →
        f'.hom.hom.obj x₁ = f'.hom.hom.obj x₂ → ∃ α : x₁ ⟶ x₂, 𝒳'.val.val.p.IsHomLift (𝟙 V) α)
    (k : Type u) [Field k] [IsAlgClosed k] (V : BigFppfOver B S hS)
    (hV : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k)) :
    (geometricFibreFunctor B S hS (spaceModuliComparison B S hS h f f' g hcomm) V).Full := by
  constructor
  intro a₁ a₂ Φ
  have hΦ := Φ.2
  have ha : (fibredCategory B S hS M'.obj).val.p.IsHomLift (𝟙 V) Φ.1.a :=
    Functor.isHomLift_map_of_comp_eq (p := (spaceModuliBaseChange B S hS f g).pt.val.val.p)
      TwoFibreProductOver.fst_comp_eq (𝟙 V) Φ.1
  have hb : 𝒳.val.val.p.IsHomLift (𝟙 V) Φ.1.b :=
    Functor.isHomLift_map_of_comp_eq (p := (spaceModuliBaseChange B S hS f g).pt.val.val.p)
      TwoFibreProductOver.snd_comp_eq (𝟙 V) Φ.1
  have hx : f'.hom.hom.obj a₁.1 = f'.hom.hom.obj a₂.1 :=
    fibredCategory_obj_eq_of_isHomLift_id B S hS
      ((Functor.congr_obj f'.hom.hom.w a₁.1).trans a₁.2)
      ((Functor.congr_obj f'.hom.hom.w a₂.1).trans a₂.2) Φ.1.a ha
  obtain ⟨β, hβ⟩ := hinj' k V hV a₁.1 a₂.1 a₁.2 a₂.2 hx
  have hgpd := Functor.IsFiberedInGroupoids.fiber_isGroupoid 𝒳.val.isFiberedInGroupoids V
  have : IsIso (h.hom.hom.map β) := Functor.isIso_of_fiber_isGroupoid hgpd _
    (Functor.isHomLift_map_of_comp_eq h.hom.hom.w (𝟙 V) β)
  let c : h.hom.hom.obj a₂.1 ⟶ h.hom.hom.obj a₂.1 := inv (h.hom.hom.map β) ≫ Φ.1.b
  have hc : 𝒳.val.val.p.IsHomLift (𝟙 V) c :=
    @IsHomLift.comp_of_lift_id _ _ _ _ 𝒳.val.val.p V _ _ _ (inv (h.hom.hom.map β)) Φ.1.b
      inferInstance hb
  have : IsIso c := Functor.isIso_of_fiber_isGroupoid hgpd _ hc
  let cA : 𝒳.val.val.p.verticalAut (h.hom.hom.obj a₂.1) :=
    ⟨Aut.of (asIso c), (Functor.mem_verticalAut_iff _ _).2 (by
      show 𝒳.val.val.p.map c = _
      rw [IsHomLift.fac' 𝒳.val.val.p (𝟙 V) c]
      simp)⟩
  obtain ⟨γ, hγ⟩ := hAut a₂.1 cA
  have hγc : h.hom.hom.map (γ : Aut a₂.1).asIso.hom = c :=
    congrArg (fun x => x.1.asIso.hom) hγ
  have hγV : 𝒳'.val.val.p.IsHomLift (𝟙 V) (γ : Aut a₂.1).asIso.hom := by
    refine IsHomLift.of_fac' _ _ _ a₂.2 a₂.2 ?_
    rw [Functor.verticalAut.cond γ]
    simp
  let α : a₁.1 ⟶ a₂.1 := β ≫ (γ : Aut a₂.1).asIso.hom
  have hα : 𝒳'.val.val.p.IsHomLift (𝟙 V) α :=
    @IsHomLift.comp_of_lift_id _ _ _ _ 𝒳'.val.val.p V _ _ _ β (γ : Aut a₂.1).asIso.hom hβ hγV
  have hαb : h.hom.hom.map α = Φ.1.b := by
    show h.hom.hom.map (β ≫ (γ : Aut a₂.1).asIso.hom) = Φ.1.b
    rw [Functor.map_comp, hγc]
    exact IsIso.hom_inv_id_assoc (h.hom.hom.map β) Φ.1.b
  have hM'set : (fibredCategory B S hS M'.obj).val.p.IsFiberedInSetoids :=
    PresheafOfCategories.isFiberedInSetoids_discreteProjection M'.obj
  have hαa : f'.hom.hom.map α = Φ.1.a :=
    Functor.hom_unique_of_isFiberedInSetoids (q := (fibredCategory B S hS M'.obj).val.p)
      (𝟙 V) _ _ (Functor.isHomLift_map_of_comp_eq f'.hom.hom.w (𝟙 V) α) ha
  exact ⟨⟨α, hα⟩, Subtype.ext (TwoFibreProductOver.Hom.ext' hαa hαb)⟩

/-- **Essential surjectivity on geometric fibres.** If `f` is injective on isomorphism classes of
objects over the spectrum of an algebraically closed field and `f'` is surjective onto the points
of `M'` with values in it, then the comparison `𝒳' ⟶ M' ×_M 𝒳` is essentially surjective on the
fibres over that spectrum. -/
theorem essSurj_geometricFibreFunctor_spaceModuliComparison
    (hinj : ∀ (k : Type u) [Field k] [IsAlgClosed k] (V : BigFppfOver B S hS),
      ((BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k)) →
      ∀ (x₁ x₂ : 𝒳.val.val.obj), 𝒳.val.val.p.obj x₁ = V → 𝒳.val.val.p.obj x₂ = V →
        f.hom.hom.obj x₁ = f.hom.hom.obj x₂ → ∃ α : x₁ ⟶ x₂, 𝒳.val.val.p.IsHomLift (𝟙 V) α)
    (hsurj' : ∀ (k : Type u) [Field k] [IsAlgClosed k] (V : BigFppfOver B S hS),
      ((BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k)) →
      ∀ n : M'.obj.obj (op V), ∃ (x : 𝒳'.val.val.obj) (_ : 𝒳'.val.val.p.obj x = V),
        f'.hom.hom.obj x = (⟨V, Discrete.mk n⟩ : (fibredCategory B S hS M'.obj).val.obj))
    (k : Type u) [Field k] [IsAlgClosed k] (V : BigFppfOver B S hS)
    (hV : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k)) :
    (geometricFibreFunctor B S hS (spaceModuliComparison B S hS h f f' g hcomm) V).EssSurj := by
  constructor
  rintro ⟨Q, hQ⟩
  have hQb : Q.base = V := hQ
  subst hQb
  set n := PresheafOfCategories.elementOf M'.obj Q.hx
  obtain ⟨y', hy', hfy'⟩ := hsurj' k Q.base hV n
  have hxQ : Q.x = (⟨Q.base, Discrete.mk n⟩ : (fibredCategory B S hS M'.obj).val.obj) :=
    PresheafOfCategories.obj_eq_of_elementOf_eq Q.hx rfl rfl
  have hgf : (associatedMap B S hS g.hom).1.hom.obj Q.x = f.hom.hom.obj Q.y :=
    fibredCategory_obj_eq_of_isHomLift_id B S hS
      ((Functor.congr_obj (associatedMap B S hS g.hom).1.hom.w Q.x).trans Q.hx)
      ((Functor.congr_obj f.hom.hom.w Q.y).trans Q.hy) Q.iso.hom Q.vertical
  have h1 : f.hom.hom.obj (h.hom.hom.obj y') = f.hom.hom.obj Q.y := by
    have e1 : f.hom.hom.obj (h.hom.hom.obj y') =
        (associatedMap B S hS g.hom).1.hom.obj (f'.hom.hom.obj y') :=
      (congrArg (fun F => F.hom.obj y') hcomm).symm
    rw [e1, hfy', ← hxQ, hgf]
  obtain ⟨β, hβ⟩ := hinj k Q.base hV (h.hom.hom.obj y') Q.y
    ((Functor.congr_obj h.hom.hom.w y').trans hy') Q.hy h1
  have hMset : (fibredCategory B S hS M.obj).val.p.IsFiberedInSetoids :=
    PresheafOfCategories.isFiberedInSetoids_discreteProjection M.obj
  have hxy : f'.hom.hom.obj y' = Q.x := hfy'.trans hxQ.symm
  have ha : (fibredCategory B S hS M'.obj).val.p.IsHomLift (eqToHom hy' ≫ 𝟙 Q.base)
      (eqToHom hxy) :=
    @IsHomLift.lift_eqToHom_comp _ _ _ _ (fibredCategory B S hS M'.obj).val.p _ _ _ _
      (𝟙 Q.base) (eqToHom hxy)
      (IsHomLift.eqToHom_domain_lift_id hxy ((Functor.congr_obj f'.hom.hom.w y').trans hy')) _ hy'
  have hb : 𝒳.val.val.p.IsHomLift (eqToHom hy' ≫ 𝟙 Q.base) β := inferInstance
  let m : (CatFiberedInGroupoids.homFunctor
      (spaceModuliComparison B S hS h f f' g hcomm).hom).obj y' ⟶ Q :=
    ChartBaseChange.twoFibreProductHomOfSetoids
      (p𝒮 := (fibredCategory B S hS M.obj).val.p) (associatedMap B S hS g.hom).1.hom.w
      f.hom.hom.w (eqToHom hy' ≫ 𝟙 Q.base) (eqToHom hxy) β ha hb
  have hm : (spaceModuliBaseChange B S hS f g).pt.val.val.p.IsHomLift (𝟙 Q.base) m :=
    IsHomLift.of_fac _ _ _ hy' rfl (by
      show 𝟙 Q.base = eqToHom hy'.symm ≫ (eqToHom hy' ≫ 𝟙 Q.base) ≫ eqToHom rfl
      simp)
  let mF : (geometricFibreFunctor B S hS (spaceModuliComparison B S hS h f f' g hcomm)
      Q.base).obj ⟨y', hy'⟩ ⟶ ⟨Q, hQ⟩ := ⟨m, hm⟩
  have : IsIso mF := (Functor.IsFiberedInGroupoids.fiber_isGroupoid
    (spaceModuliBaseChange B S hS f g).pt.val.isFiberedInGroupoids Q.base).all_isIso mF
  exact ⟨⟨y', hy'⟩, ⟨asIso mF⟩⟩

/-- **A cartesian criterion over algebraic spaces** (the criterion of the proof of Stacks 0DUT,
used again in the proof of Stacks 0DUV). Let

```
𝒳' ---h---> 𝒳
 |f'         |f
 v           v
 M' ---g---> M
```

be a commutative square in which `h` is étale and induces isomorphisms between automorphism groups
at every point (Stacks 0DTW), `g` is an étale morphism of algebraic spaces, and over the spectrum
of any algebraically closed field `f` is injective on isomorphism classes while `f'` is bijective
from isomorphism classes onto points of `M'`. Then the square is a 2-fibre product.

The comparison `𝒳' ⟶ M' ×_M 𝒳` is representable and étale (both `h` and the projection to `𝒳`
are), full on geometric fibres (by the bijection on automorphism groups and injectivity of `f'`)
hence universally injective (Stacks 0CPN), essentially surjective on geometric fibres (by
surjectivity of `f'` and injectivity of `f`) hence surjective, so it is an equivalence by Stacks
05W5, as in the proof of Stacks 0DUD. -/
theorem nonempty_isTwoFibreProduct_spaceModuliSquare
    (he : IsEtale B S hS h)
    (hauto : ∀ q : points B S hS 𝒳'.val.val 𝒳'.val.isFiberedInGroupoids,
      InducesIsomorphismAt B S hS h q)
    (hg : Space.IsEtale B S hS g.hom)
    (hinj : ∀ (k : Type u) [Field k] [IsAlgClosed k] (V : BigFppfOver B S hS),
      ((BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k)) →
      ∀ (x₁ x₂ : 𝒳.val.val.obj), 𝒳.val.val.p.obj x₁ = V → 𝒳.val.val.p.obj x₂ = V →
        f.hom.hom.obj x₁ = f.hom.hom.obj x₂ → ∃ α : x₁ ⟶ x₂, 𝒳.val.val.p.IsHomLift (𝟙 V) α)
    (hinj' : ∀ (k : Type u) [Field k] [IsAlgClosed k] (V : BigFppfOver B S hS),
      ((BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k)) →
      ∀ (x₁ x₂ : 𝒳'.val.val.obj), 𝒳'.val.val.p.obj x₁ = V → 𝒳'.val.val.p.obj x₂ = V →
        f'.hom.hom.obj x₁ = f'.hom.hom.obj x₂ → ∃ α : x₁ ⟶ x₂, 𝒳'.val.val.p.IsHomLift (𝟙 V) α)
    (hsurj' : ∀ (k : Type u) [Field k] [IsAlgClosed k] (V : BigFppfOver B S hS),
      ((BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k)) →
      ∀ n : M'.obj.obj (op V), ∃ (x : 𝒳'.val.val.obj) (_ : 𝒳'.val.val.p.obj x = V),
        f'.hom.hom.obj x = (⟨V, Discrete.mk n⟩ : (fibredCategory B S hS M'.obj).val.obj)) :
    Nonempty (Bicategory.IsTwoFibreProduct (spaceModuliSquare B S hS h f f' g hcomm)) := by
  obtain ⟨Ein⟩ := inertiaPullbackComparison_isEquivalenceOver_of_inducesIsomorphismAt B S hS h
    (isUnramified_of_isEtale B S hS he) hauto
  have := Ein.isEquivalence
  have hAut : ∀ a, Function.Surjective (automorphismGroupMap B S hS h a) := fun a =>
    (Functor.bijective_verticalAutMap 𝒳'.val.val.p 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor h.hom) (CatFiberedInGroupoids.homFunctor_comp_p h.hom)
      a).2
  have hrep := AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_isEtale_of_inducesIsomorphismAt
    h he hauto
  let φ := spaceModuliComparison B S hS h f f' g hcomm
  have hΔ := isSurjective_relativeDiagonal_of_liftsTwoArrowsAtGeometricPoints B S hS φ
    fun k _ _ V hV => exists_isHomLift_map_eq_of_fiberMap_full B S hS φ
      (full_geometricFibreFunctor_spaceModuliComparison B S hS h f f' g hcomm hAut hinj') k V hV
  have hequiv := isEquivalence_of_isEtale_of_universallyInjective_of_isSurjective B S hS φ
    (isRepresentableByAlgebraicSpaces_spaceModuliComparison B S hS h f f' g hcomm hg hrep)
    (isEtale_spaceModuliComparison B S hS h f f' g hcomm hg hrep he)
    (universallyInjective_of_isSurjective_relativeDiagonal B S hS φ hΔ)
    (isSurjective_of_fiberMap_essSurj B S hS φ
      (essSurj_geometricFibreFunctor_spaceModuliComparison B S hS h f f' g hcomm hinj hsurj'))
  exact ⟨Bicategory.isTwoFibreProduct_of_isEquivalence_to
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _)
    (CatFiberedInGroupoids.preHomTwoFibreProductSquare.{u, u, u + 1, u + 1} _ _ _) hequiv⟩

end Criterion

end AlgebraicGeometry.Stack

end
