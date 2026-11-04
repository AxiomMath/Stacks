module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.RimSchlessinger.Basic

/-!
# Condition (RS) from small extensions

For a category cofibered in groupoids over the category `𝒞_Λ` of Artinian local
`Λ`-algebras with residue field `k`, it is enough to verify condition (RS) on cospans
whose second morphism in the base is a small extension.

The proof factors an arbitrary surjection in `𝒞_Λ` into small extensions and then pastes
the resulting pullback squares one on top of the other.

## Main results

* `Deformation.satisfiesRS_of_small_extensions`: condition (RS) follows from its
  restriction to cospans whose second base morphism is a small extension.

## Implementation notes

As in the definition of condition (RS), the required fibre product is expressed by a
pullback cone in the cofibered category whose image in `𝒞_Λ` is also limiting. A small
extension is imposed on the underlying ring homomorphism of the second base morphism.

The inductive step pushes the source of the cospan forward along the first small extension
of the factorization, descends the cospan arrow through that pushforward, and pastes the
pullback square obtained for the shorter factorization onto the square supplied by the
hypothesis.

## References

* [Stacks Project, Tag 06J4](https://stacks.math.columbia.edu/tag/06J4)
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory CategoryTheory.Limits

universe u v w u₁ v₁ u₂ v₂ u₃ v₃

variable {F : Type u₁} [Category.{v₁} F] {C : Type u₂} [Category.{v₂} C] {p : F ⥤ C}

/-- The vertical paste of two pullback cones. -/
private def pastePullbackCones {X₁ X₂ X Y : C} {f₁ : X₁ ⟶ X} {g : Y ⟶ X} {h : X₂ ⟶ Y}
    (c₁ : PullbackCone f₁ g) (c₂ : PullbackCone c₁.snd h) :
    PullbackCone f₁ (h ≫ g) :=
  c₁.pasteVert c₂ rfl

private def isLimit_pastePullbackCones
    {X₁ X₂ X Y : C} {f₁ : X₁ ⟶ X} {g : Y ⟶ X} {h : X₂ ⟶ Y}
    (c₁ : PullbackCone f₁ g) (c₂ : PullbackCone c₁.snd h)
    (hc₁ : IsLimit c₁) (hc₂ : IsLimit c₂) :
    IsLimit (pastePullbackCones c₁ c₂) := by
  simpa [pastePullbackCones] using
    (CategoryTheory.Limits.pasteVertIsPullback (t₁ := c₁) (t₂ := c₂) rfl hc₁ hc₂)

/-- Transport a pullback cone along an equality of the second leg of the cospan. -/
private def changePullbackConeRight {X₁ X₂ X : C} {f₁ : X₁ ⟶ X} {g h : X₂ ⟶ X}
    (e : g = h) (c : PullbackCone f₁ g) : PullbackCone f₁ h :=
  PullbackCone.mk c.fst c.snd (e ▸ c.condition)

private def isLimit_changePullbackConeRight {X₁ X₂ X : C} {f₁ : X₁ ⟶ X} {g h : X₂ ⟶ X}
    (e : g = h) (c : PullbackCone f₁ g) (hc : IsLimit c) :
    IsLimit (changePullbackConeRight e c) := by
  cases e
  exact IsLimit.ofIsoLimit hc (PullbackCone.eta c)

private def map_changePullbackConeRight {D : Type u₃} [Category.{v₃} D]
    (P : C ⥤ D) {X₁ X₂ X : C} {f₁ : X₁ ⟶ X} {g h : X₂ ⟶ X}
    (e : g = h) (c : PullbackCone f₁ g) :
    (changePullbackConeRight e c).map P ≅
      changePullbackConeRight (congrArg (fun q => P.map q) e) (c.map P) :=
  PullbackCone.ext (Iso.refl _) (Category.id_comp _).symm
    (Category.id_comp _).symm

private lemma isIso_lift_of_isIso_base (hp : IsCofiberedInGroupoids p) {x y : F} (φ : x ⟶ y)
    [IsIso (p.map φ)] : IsIso φ := by
  have := IsHomLift.map p φ
  have := isStronglyCocartesian_of_isCofiberedInGroupoids hp (p.map φ) φ inferInstance
  exact Functor.IsStronglyCocartesian.isIso_of_base_isIso p (p.map φ) φ

private noncomputable def isLimit_map_rightIsoPullbackCone {D : Type u₃} [Category.{v₃} D]
    (P : C ⥤ D) {X₁ X₂ X : C} (f₁ : X₁ ⟶ X) (f₂ : X₂ ⟶ X) [IsIso f₂] :
    IsLimit ((pullbackConeOfRightIso f₁ f₂).map P) := by
  let : IsIso (P.map f₂) := Functor.map_isIso P f₂
  have hc : IsLimit (pullbackConeOfRightIso (P.map f₁) (P.map f₂)) :=
    pullbackConeOfRightIsoIsLimit (P.map f₁) (P.map f₂)
  have hcone : (pullbackConeOfRightIso f₁ f₂).map P ≅
      pullbackConeOfRightIso (P.map f₁) (P.map f₂) :=
    PullbackCone.ext (Iso.refl _)
      (by
        change P.map (𝟙 X₁) = 𝟙 (P.obj X₁) ≫ 𝟙 (P.obj X₁)
        simp)
      (by
        change P.map (f₁ ≫ inv f₂) = 𝟙 (P.obj X₁) ≫ (P.map f₁ ≫ inv (P.map f₂))
        simp [Functor.map_comp, Functor.map_inv])
  exact IsLimit.ofIsoLimit hc hcone.symm

private lemma smallExtension_congr_eqToHom
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A B C' D : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hA : A = C') (hD : D = B) (f : A ⟶ B) (g : C' ⟶ D)
    (hfg : f = eqToHom hA ≫ g ≫ eqToHom hD) :
    InfinitesimalLifting.IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom) ↔
      InfinitesimalLifting.IsSmallExtension (CommRingCat.ofHom g.hom.toRingHom) := by
  cases hA
  cases hD
  simpa using congrArg
    (fun q : A ⟶ B => InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom q.hom.toRingHom)) hfg

/-- The inductive core of Tag 06J4: a cospan whose second base morphism factors as a
composable chain of small extensions has the pullback cone required by (RS). -/
private theorem exists_pullback_for_factor
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p)
    (hsmall : ∀ {x₁ x₂ x : F} (f₁ : x₁ ⟶ x) (f₂ : x₂ ⟶ x),
      InfinitesimalLifting.IsSmallExtension (CommRingCat.ofHom (p.map f₂).hom.toRingHom) →
        ∃ c : PullbackCone f₁ f₂, Nonempty (IsLimit c) ∧ Nonempty (IsLimit (c.map p))) :
    ∀ (n : ℕ) (D : ComposableArrows (ArtinianLocalAlgCat.{u, v, w} Λ k) n)
      {x₁ x₂ x : F} (f₁ : x₁ ⟶ x) (f₂ : x₂ ⟶ x)
      (e : D.right ≅ p.obj x) (hleft : D.left = p.obj x₂)
      (hf : eqToHom hleft.symm ≫ D.hom ≫ e.hom = p.map f₂),
      (hedge : ∀ (i : ℕ) (hi : i < n),
        InfinitesimalLifting.IsSmallExtension
          (CommRingCat.ofHom (D.map' i (i + 1)).hom.toRingHom)) →
      ∃ c : PullbackCone f₁ f₂, Nonempty (IsLimit c) ∧ Nonempty (IsLimit (c.map p)) := by
  intro n
  induction n with
  | zero =>
      intro D x₁ x₂ x f₁ f₂ e hleft hf hedge
      have : IsIso D.hom := by
        dsimp [ComposableArrows.hom]
        infer_instance
      have : IsIso (p.map f₂) := by
        rw [← hf]
        infer_instance
      have : IsIso f₂ := isIso_lift_of_isIso_base hp f₂
      let c := pullbackConeOfRightIso f₁ f₂
      have hc : IsLimit c := pullbackConeOfRightIsoIsLimit f₁ f₂
      have hbase : IsLimit (c.map p) := by
        simpa [c] using isLimit_map_rightIsoPullbackCone p f₁ f₂
      exact ⟨c, ⟨hc⟩, ⟨hbase⟩⟩
  | succ n ih =>
      intro D x₁ x₂ x f₁ f₂ e hleft hf hedge
      let g₀ := D.map' 0 1
      let D' := D.δ₀
      have hfactor : D.hom = g₀ ≫ D'.hom := by
        show D.map' 0 (n + 1) = D.map' 0 1 ≫ D.map' 1 (n + 1)
        exact ComposableArrows.map'_comp D 0 1 (n + 1)
      have hψ : p.IsHomLift (D.hom ≫ e.hom) f₂ := by
        have hcomp : D.hom ≫ e.hom = eqToHom hleft ≫ p.map f₂ := by
          rw [← hf]
          simp
        exact hcomp.symm ▸ (inferInstance : p.IsHomLift (eqToHom hleft ≫ p.map f₂) f₂)
      let u := chosenPushforwardMap hp g₀ x₂ hleft.symm
      have := chosenPushforwardMap_lift hp g₀ x₂ hleft.symm
      have hψ' : p.IsHomLift (g₀ ≫ (D'.hom ≫ e.hom)) f₂ := by
        have hbase : g₀ ≫ (D'.hom ≫ e.hom) = D.hom ≫ e.hom := by
          calc
            g₀ ≫ (D'.hom ≫ e.hom) = (g₀ ≫ D'.hom) ≫ e.hom :=
              (Category.assoc g₀ D'.hom e.hom).symm
            _ = D.hom ≫ e.hom := congrArg (fun q => q ≫ e.hom) hfactor.symm
        exact hbase.symm ▸ hψ
      let v := pushforwardDesc hp g₀ (D'.hom ≫ e.hom) x₂ x hleft.symm f₂ hψ'
      have hv : p.IsHomLift (D'.hom ≫ e.hom) v :=
        pushforwardDesc_lift hp g₀ (D'.hom ≫ e.hom) x₂ x hleft.symm f₂ hψ'
      have hfac : u ≫ v = f₂ :=
        pushforwardDesc_fac hp g₀ (D'.hom ≫ e.hom) x₂ x hleft.symm f₂ hψ'
      have hleft' : D'.left = p.obj (pushforwardObj hp g₀ x₂ hleft.symm) :=
        (IsHomLift.codomain_eq p g₀ u).symm
      have hf' : eqToHom hleft'.symm ≫ D'.hom ≫ e.hom = p.map v := by
        simpa [hleft'] using (IsHomLift.fac' p (D'.hom ≫ e.hom) v).symm
      obtain ⟨c₁, hc₁, hpc₁⟩ := ih D' f₁ v e hleft' hf' (fun i _ => hedge (i + 1) (by omega))
      have hs : InfinitesimalLifting.IsSmallExtension
          (CommRingCat.ofHom (p.map u).hom.toRingHom) :=
        (smallExtension_congr_eqToHom (IsHomLift.domain_eq p g₀ u).symm
          (IsHomLift.codomain_eq p g₀ u) g₀ (p.map u) (IsHomLift.fac p g₀ u)).mp
          (hedge 0 (by omega))
      obtain ⟨c₂, hc₂, hpc₂⟩ := hsmall c₁.snd u hs
      let c₀ := pastePullbackCones c₁ c₂
      let c := changePullbackConeRight hfac c₀
      have hc₀ : IsLimit c₀ := isLimit_pastePullbackCones c₁ c₂ hc₁.some hc₂.some
      have hc : IsLimit c := isLimit_changePullbackConeRight hfac c₀ hc₀
      have hmapfac : p.map (u ≫ v) = p.map f₂ := congrArg (fun q => p.map q) hfac
      have hcomp : p.map (u ≫ v) = p.map u ≫ p.map v := p.map_comp u v
      have hbase : IsLimit (changePullbackConeRight hmapfac
          (changePullbackConeRight hcomp.symm
            (pastePullbackCones (c₁.map p) (c₂.map p)))) :=
        isLimit_changePullbackConeRight hmapfac _
          (isLimit_changePullbackConeRight hcomp.symm _
            (isLimit_pastePullbackCones (c₁.map p) (c₂.map p) hpc₁.some hpc₂.some))
      refine ⟨c, ⟨hc⟩, ?_⟩
      have hcone₁ : c.map p ≅ changePullbackConeRight hmapfac (c₀.map p) :=
        map_changePullbackConeRight p hfac c₀
      have hcone₂ : changePullbackConeRight hmapfac (c₀.map p) ≅
          changePullbackConeRight hmapfac
            (changePullbackConeRight hcomp.symm
              (pastePullbackCones (c₁.map p) (c₂.map p))) :=
        PullbackCone.ext (Iso.refl _)
          (by
            show p.map c₀.fst = 𝟙 _ ≫ (p.map c₂.fst ≫ p.map c₁.fst)
            rw [Category.id_comp]
            show p.map (c₂.fst ≫ c₁.fst) = p.map c₂.fst ≫ p.map c₁.fst
            exact p.map_comp _ _)
          (by
            show p.map c₀.snd = 𝟙 _ ≫ p.map c₂.snd
            rw [Category.id_comp]
            rfl)
      exact ⟨IsLimit.ofIsoLimit hbase (hcone₁.trans hcone₂).symm⟩

/-- **Stacks Project, Tag 06J4.** To verify condition (RS) for a category cofibered in
groupoids, it suffices to consider cospans whose second base morphism is a small
extension. -/
@[stacks 06J4]
public theorem satisfiesRS_of_small_extensions
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p)
    (hsmall : ∀ {x₁ x₂ x : F} (f₁ : x₁ ⟶ x) (f₂ : x₂ ⟶ x),
      InfinitesimalLifting.IsSmallExtension
          (CommRingCat.ofHom (p.map f₂).hom.toRingHom) →
        ∃ c : PullbackCone f₁ f₂,
          (Nonempty (IsLimit c) ∧ Nonempty (IsLimit (c.map p)))) :
    SatisfiesRS p := by
  show IsCofiberedInGroupoids p ∧ _
  refine ⟨hp, ?_⟩
  intro x₁ x₂ x f₁ f₂ hf₂
  obtain ⟨n, D, hleft, e, hfac, hedge⟩ :=
    surjective_factors_into_smallExtensions (p.map f₂) hf₂
  exact exists_pullback_for_factor hp hsmall n D f₁ f₂ e hleft hfac hedge

end

end Deformation
