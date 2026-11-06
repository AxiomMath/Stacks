module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Groupoid.Basic
public import StacksFrontier.Deformation.Groupoid.Smooth
public import StacksFrontier.Deformation.RimSchlessinger.Basic

/-!
# Condition (RS) for the quotient of a smooth groupoid in functors

If a groupoid in functors on the category of Artinian local algebras is smooth and its functors
of objects and of arrows both satisfy condition (RS), then so does its quotient — the
Grothendieck construction of the pointwise groupoids, with its canonical projection to the base
category.

The proof is the source's. Given a cospan in the quotient over a cospan of algebras whose
second map is surjective, smoothness lets one replace the second leg by one whose target agrees
with the first on the nose; the fibre product of the underlying objects is then furnished by
(RS) for the object functor, and (RS) for the arrow functor identifies the fibre of the
connecting arrow, which is what makes the resulting square a pullback in the quotient.

## Main results

* `Deformation.quotient_satisfiesRS`: condition (RS) descends to the quotient of a smooth
  groupoid in functors.

## Implementation notes

The functors of objects and of arrows are viewed as categories of elements over the category of
Artinian local algebras, so that (RS) for them is literally condition (RS) for a functor to the
base. Two auxiliary statements isolate what (RS) gives for a category of elements: that a
compatible pair of elements comes from an element of the pullback, and that such an element is
unique.

## References

* [Stacks Project, Tag 06KT](https://stacks.math.columbia.edu/tag/06KT)
-/

@[expose] public section

namespace Deformation

/-! ### Condition (RS) for quotients of smooth groupoids in functors -/

section
open CategoryTheory CategoryTheory.Limits

universe u v w u₁

private theorem liftSourceArrow
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {G : GroupoidInFunctors (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    (hG : GroupoidInFunctors.IsSmooth G)
    {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A)
    (hf : Function.Surjective f.hom) (x : G.objects.obj B) (a : G.arrows.obj A)
    (ha : G.source.app A a = G.objects.map f x) :
    ∃ a' : G.arrows.obj B, G.arrows.map f a' = a ∧ G.source.app B a' = x := by
  let pU := Functor.Elements.π G.objects
  let pR := Functor.Elements.π G.arrows
  let φ := elementsBasedFunctor G.source
  let xU : G.objects.Elements := G.objects.elementsMk B x
  let xR : G.arrows.Elements := G.arrows.elementsMk A a
  let y : G.objects.Elements := G.objects.elementsMk A (G.source.app A a)
  let g : xU ⟶ φ.toFunctor.obj xR :=
    Functor.Elements.homMk (x := xU) (y := y) f (by
      show G.objects.map f x = G.source.app A a; exact ha.symm)
  have hg : (BasedCategory.ofFunctor pU).p.IsHomLift f g := by
    show pU.IsHomLift (pU.map g) g
    simpa [pU, Functor.Elements.π] using (IsHomLift.map (p := pU) g)
  obtain ⟨x', h, c, hh, hc, _⟩ := hG.1 f hf xU xR g hg
  rcases x' with @⟨B', a'⟩
  let _ : pR.IsHomLift f h := hh
  have hB : B' = B := IsHomLift.domain_eq (p := pR) f h
  cases hB
  let _ : pU.IsHomLift (𝟙 B) c := hc
  have hcbase : c.hom = 𝟙 B := by
    have hfac := IsHomLift.fac (p := pU) (𝟙 B) c
    change 𝟙 B = pU.map c at hfac
    simpa [pU, Functor.Elements.π] using hfac.symm
  have hbase : h.hom = f := by
    have hfac := IsHomLift.fac (p := pR) f h
    change f = pR.map h at hfac
    simpa [pR, Functor.Elements.π] using hfac.symm
  have hsource : G.source.app B a' = x := by
    have hcprop := c.map_val
    change G.objects.map c.hom (G.source.app B a') = x at hcprop
    rw [hcbase] at hcprop
    exact (G.objects.map_id_apply B (G.source.app B a')).symm.trans hcprop
  refine ⟨a', ?_, hsource⟩
  rw [← hbase, h.map_val]

/-- Under (RS) for the category of elements of `F`, a compatible pair of elements comes from a
unique element of `F` at the pullback. -/
private theorem elementsPullback_existsUnique
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type u₁)
    (hF : SatisfiesRS (Functor.Elements.π F))
    {A₁ A₂ A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (hf₂ : Function.Surjective f₂.hom)
    (c : PullbackCone f₁ f₂) (hc : IsLimit c)
    (x₁ : F.obj A₁) (x₂ : F.obj A₂) (x : F.obj A)
    (hx₁ : F.map f₁ x₁ = x) (hx₂ : F.map f₂ x₂ = x) :
    ∃! z : F.obj c.pt, F.map c.fst z = x₁ ∧ F.map c.snd z = x₂ := by
  let p := Functor.Elements.π F
  let X₁ : F.Elements := F.elementsMk A₁ x₁
  let X₂ : F.Elements := F.elementsMk A₂ x₂
  let X : F.Elements := F.elementsMk A x
  let q₁ : X₁ ⟶ X := Functor.Elements.homMk (x := X₁) (y := X) f₁ hx₁
  let q₂ : X₂ ⟶ X := Functor.Elements.homMk (x := X₂) (y := X) f₂ hx₂
  have hf₂' : Function.Surjective (p.map q₂).hom := hf₂
  obtain ⟨cE, hE⟩ := hF.2 q₁ q₂ hf₂'
  rcases hE with ⟨⟨hlimE⟩, ⟨hlimB⟩⟩
  let cB : PullbackCone f₁ f₂ := cE.map p
  let e : cB.pt ≅ c.pt := hlimB.conePointUniqueUpToIso hc
  have he₁ : e.hom ≫ c.fst = cB.fst := by
    exact IsLimit.conePointUniqueUpToIso_hom_comp hlimB hc WalkingCospan.left
  have he₂ : e.hom ≫ c.snd = cB.snd := by
    exact IsLimit.conePointUniqueUpToIso_hom_comp hlimB hc WalkingCospan.right
  have hinv : ∀ z : F.obj c.pt, F.map c.fst z = x₁ → F.map c.snd z = x₂ →
      F.map e.inv z = cE.pt.val := by
    intro z hz₁ hz₂
    let Z : F.Elements := F.elementsMk c.pt z
    let s : PullbackCone q₁ q₂ :=
      PullbackCone.mk (Functor.Elements.homMk (x := Z) (y := X₁) c.fst hz₁)
      (Functor.Elements.homMk (x := Z) (y := X₂) c.snd hz₂) (Functor.Elements.hom_ext c.condition)
    let m : Z ⟶ cE.pt := hlimE.lift s
    have hbase : m.hom = e.inv := by
      apply PullbackCone.IsLimit.hom_ext hlimB
      · exact (congrArg (fun q : Z ⟶ X₁ => q.hom) (hlimE.fac s WalkingCospan.left)).trans
          (by rw [Iso.eq_inv_comp]; exact he₁)
      · exact (congrArg (fun q : Z ⟶ X₂ => q.hom) (hlimE.fac s WalkingCospan.right)).trans
          (by rw [Iso.eq_inv_comp]; exact he₂)
    have hp := m.map_val
    change F.map m.hom z = cE.pt.val at hp
    rwa [hbase] at hp
  refine ⟨F.map e.hom cE.pt.val, ⟨?_, ?_⟩, fun z hz => ?_⟩
  · exact (F.map_comp_apply _ _ _).symm.trans
      ((congrArg (fun g => F.map g cE.pt.val) he₁).trans (cE.fst.map_val))
  · exact (F.map_comp_apply _ _ _).symm.trans
      ((congrArg (fun g => F.map g cE.pt.val) he₂).trans (cE.snd.map_val))
  · rw [← hinv z hz.1 hz.2]
    simp [← F.map_comp_apply]

/-- The quotient of a smooth groupoid in functors whose object and arrow functors satisfy
condition (RS) also satisfies condition (RS). -/
@[stacks 06KT]
public theorem quotient_satisfiesRS
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (G : GroupoidInFunctors (ArtinianLocalAlgCat.{u, v, w} Λ k))
    (hG : GroupoidInFunctors.IsSmooth G)
    (hU : SatisfiesRS (Functor.Elements.π G.objects))
    (hR : SatisfiesRS (Functor.Elements.π G.arrows)) :
    SatisfiesRS (Grothendieck.forget (evaluationFunctor G)) := by
  let _ (A : ArtinianLocalAlgCat.{u, v, w} Λ k) :
      Groupoid (G.objects.obj A) := G.evaluationGroupoid A
  refine ⟨quotientProjection_cofibered G, ?_⟩
  intro X₁ X₂ X f₁ f₂ hf₂
  rcases X₁ with ⟨A₁, x₁⟩
  rcases X₂ with ⟨A₂, x₂⟩
  rcases X with ⟨A, x⟩
  let δ : (evaluationMap G f₂.base).obj x₂ ⟶
      (evaluationMap G f₁.base).obj x₁ := f₂.fiber ≫ Groupoid.inv f₁.fiber
  let d := (G.evaluationArrowEquiv A
    ((evaluationMap G f₂.base).obj x₂)
    ((evaluationMap G f₁.base).obj x₁) δ).1
  have hds : G.source.app A d = G.objects.map f₂.base x₂ :=
    (G.evaluationArrowEquiv A _ _ δ).2.1
  have hdt : G.target.app A d = G.objects.map f₁.base x₁ :=
    (G.evaluationArrowEquiv A _ _ δ).2.2
  obtain ⟨a₂', ha₂', hsource₂'⟩ :=
    liftSourceArrow hG f₂.base hf₂ x₂ d hds
  have htarget₂' : G.objects.map f₂.base (G.target.app A₂ a₂') =
      G.objects.map f₁.base x₁ := by
    rw [← G.target.naturality_apply f₂.base a₂', ha₂', hdt]
  let U₁ : G.objects.Elements := G.objects.elementsMk A₁ x₁
  let U₂ : G.objects.Elements := G.objects.elementsMk A₂ (G.target.app A₂ a₂')
  let U : G.objects.Elements := G.objects.elementsMk A (G.objects.map f₁.base x₁)
  let q₁ : U₁ ⟶ U := Functor.Elements.homMk (x := U₁) (y := U) f₁.base rfl
  let q₂ : U₂ ⟶ U := Functor.Elements.homMk (x := U₂) (y := U) f₂.base htarget₂'
  have hf₂' : Function.Surjective ((Functor.Elements.π G.objects).map q₂).hom := by
    show Function.Surjective f₂.base.hom
    exact hf₂
  obtain ⟨cU, hcU⟩ := hU.2 q₁ q₂ hf₂'
  rcases hcU with ⟨⟨hlimU⟩, ⟨hlimBaseU⟩⟩
  let P := cU.pt.obj
  let zP := cU.pt.val
  let Y : Grothendieck (evaluationFunctor G) := ⟨P, zP⟩
  let v₁ := cU.fst
  let v₂ := cU.snd
  have hv₁ : G.objects.map v₁.hom zP = x₁ := v₁.map_val
  have hv₂ : G.objects.map v₂.hom zP = G.target.app A₂ a₂' := v₂.map_val
  let β₂ : x₂ ⟶ G.target.app A₂ a₂' :=
    (G.evaluationArrowEquiv A₂ x₂ (G.target.app A₂ a₂')).symm
      ⟨a₂', hsource₂', rfl⟩
  let m₁ : Y ⟶ ⟨A₁, x₁⟩ :=
    { base := v₁.hom, fiber := eqToHom hv₁ }
  let m₂ : Y ⟶ ⟨A₂, x₂⟩ :=
    { base := v₂.hom, fiber := eqToHom hv₂ ≫ Groupoid.inv β₂ }
  have hβmap : (evaluationMap G f₂.base).map β₂ ≫
      eqToHom htarget₂' = δ := by
    have ht := htarget₂'
    let γ := (evaluationMap G f₂.base).map β₂ ≫ eqToHom ht
    have hval : (G.evaluationArrowEquiv A
      ((evaluationMap G f₂.base).obj x₂)
      ((evaluationMap G f₁.base).obj x₁) γ).1 = d :=
      calc
        _ = (G.evaluationArrowEquiv A
            ((evaluationMap G f₂.base).obj x₂)
            ((evaluationMap G f₂.base).obj (G.target.app A₂ a₂'))
            ((evaluationMap G f₂.base).map β₂)).1 := by
              simpa [γ] using evaluationArrowEquiv_val_transport G A rfl ht
                ((evaluationMap G f₂.base).map β₂)
        _ = G.arrows.map f₂.base a₂' := by
              simpa [β₂] using (evaluationMap_map_arrow G f₂.base β₂)
        _ = d := ha₂'
    have hδ : (G.evaluationArrowEquiv A
        ((evaluationMap G f₂.base).obj x₂)
        ((evaluationMap G f₁.base).obj x₁) δ).1 = d := rfl
    exact (G.evaluationArrowEquiv A
      ((evaluationMap G f₂.base).obj x₂)
      ((evaluationMap G f₁.base).obj x₁)).injective (Subtype.ext (hval.trans hδ.symm))
  have hβmapFun :
      ((evaluationFunctor G).map f₂.base).toFunctor.map β₂ ≫
        eqToHom htarget₂' = δ := hβmap
  have hinvβmap : eqToHom htarget₂'.symm ≫
      (evaluationMap G f₂.base).map (Groupoid.inv β₂) = Groupoid.inv δ := by
    calc
      _ = Groupoid.inv ((evaluationMap G f₂.base).map β₂ ≫
          eqToHom htarget₂') := by simp
      _ = Groupoid.inv δ := congrArg Groupoid.inv hβmap
  have hinvβmap' : eqToHom htarget₂'.symm ≫
      ((evaluationFunctor G).map f₂.base).toFunctor.map (Groupoid.inv β₂) =
      Groupoid.inv δ := hinvβmap
  have hδcomp : Groupoid.inv δ ≫ f₂.fiber = f₁.fiber := by
    dsimp [δ]
    simp [Category.assoc]
  have hbase : v₁.hom ≫ f₁.base = v₂.hom ≫ f₂.base := by
    have h := congrArg (fun q : cU.pt ⟶ U => q.hom) cU.condition
    simpa [q₁, q₂, v₁, v₂] using h
  have hright : eqToHom htarget₂'.symm ≫
        ((evaluationFunctor G).map f₂.base).toFunctor.map (Groupoid.inv β₂) ≫
        f₂.fiber = f₁.fiber := by
    rw [← Category.assoc, hinvβmap']
    exact hδcomp
  have hcomm : m₁ ≫ f₁ = m₂ ≫ f₂ := by
    apply Grothendieck.ext _ _ hbase
    simp only [Grothendieck.comp_fiber, m₁, m₂, Functor.map_comp,
      eqToHom_map, Category.assoc]
    simp only [eqToHom_trans_assoc]
    apply (eqToHom_comp_iff _ _ _).2
    simp only [eqToHom_trans_assoc]
    rw [hright]
  let c : PullbackCone f₁ f₂ := PullbackCone.mk m₁ m₂ hcomm
  have hcbase : c.map (Grothendieck.forget (evaluationFunctor G)) ≅
      cU.map (Functor.Elements.π G.objects) := by
    refine PullbackCone.ext (Iso.refl _) ?_ ?_
    · show v₁.hom = 𝟙 P ≫ v₁.hom
      rw [Category.id_comp]
    · show v₂.hom = 𝟙 P ≫ v₂.hom
      rw [Category.id_comp]
  have hcbaseLim : IsLimit
      (c.map (Grothendieck.forget (evaluationFunctor G))) :=
    hlimBaseU.ofIsoLimit hcbase.symm
  refine ⟨c, ⟨⟨?_⟩, ⟨hcbaseLim⟩⟩⟩
  have hmed : ∀ s : PullbackCone f₁ f₂, ∃ t : s.pt ⟶ c.pt,
      t ≫ c.fst = s.fst ∧ t ≫ c.snd = s.snd := by
    intro s
    let B := s.pt.base
    let z := s.pt.fiber
    let _ : Groupoid (G.objects.obj B) := G.evaluationGroupoid B
    let a₁B := (G.evaluationArrowEquiv A₁
      ((evaluationMap G s.fst.base).obj z) x₁ s.fst.fiber).1
    let θ₂ := s.snd.fiber ≫ β₂
    let a₂B := (G.evaluationArrowEquiv A₂
      ((evaluationMap G s.snd.base).obj z)
      (G.target.app A₂ a₂') θ₂).1
    have hcompFiber := Grothendieck.congr s.condition
    rw [Grothendieck.comp_fiber] at hcompFiber
    rw [Grothendieck.comp_fiber s.snd f₂] at hcompFiber
    have hbaseEq : s.fst.base ≫ f₁.base = s.snd.base ≫ f₂.base :=
      congrArg (fun q => q.base) s.condition
    let srcC := G.objects.map (s.fst.base ≫ f₁.base) z
    let src₁ := G.objects.map f₁.base (G.objects.map s.fst.base z)
    let src₂ := G.objects.map f₂.base (G.objects.map s.snd.base z)
    have hcommon₁ : srcC = src₁ := by
      dsimp [srcC, src₁]
      exact G.objects.map_comp_apply _ _ _
    have hcommon₂ : srcC = src₂ := by
      dsimp [srcC, src₂]
      calc
        _ = G.objects.map (s.snd.base ≫ f₂.base) z :=
          congrArg (fun f => G.objects.map f z) hbaseEq
        _ = _ := G.objects.map_comp_apply _ _ _
    let φ₁ := ((evaluationFunctor G).map f₁.base).toFunctor.map s.fst.fiber
    let φ₂ := ((evaluationFunctor G).map f₂.base).toFunctor.map s.snd.fiber
    have hcompFiber' : (eqToHom hcommon₁ ≫ φ₁) ≫ f₁.fiber =
        (eqToHom hcommon₂ ≫ φ₂) ≫ f₂.fiber := by
      unfold φ₁ φ₂
      simp only [← Category.assoc, eqToHom_trans] at hcompFiber
      change (eqToHom hcommon₁ ≫
          ((evaluationFunctor G).map f₁.base).toFunctor.map s.fst.fiber) ≫ f₁.fiber =
        (eqToHom hcommon₂ ≫
          ((evaluationFunctor G).map f₂.base).toFunctor.map s.snd.fiber) ≫ f₂.fiber
        at hcompFiber
      exact hcompFiber
    have hθmap : φ₂ ≫
        ((evaluationFunctor G).map f₂.base).toFunctor.map β₂ =
          ((evaluationFunctor G).map f₂.base).toFunctor.map θ₂ := by
      rw [Functor.map_comp]
    have hcancel : eqToHom hcommon₁ ≫ φ₁ = eqToHom hcommon₂ ≫ φ₂ ≫
        ((evaluationFunctor G).map f₂.base).toFunctor.map β₂ ≫
          eqToHom htarget₂' := by
      calc
        eqToHom hcommon₁ ≫ φ₁ =
            (eqToHom hcommon₁ ≫ φ₁ ≫ f₁.fiber) ≫ Groupoid.inv f₁.fiber := by
              simp [Category.assoc]
        _ = (eqToHom hcommon₂ ≫ φ₂ ≫ f₂.fiber) ≫ Groupoid.inv f₁.fiber := by
              have hh := congrArg (fun q => q ≫ Groupoid.inv f₁.fiber) hcompFiber'
              simpa only [← Category.assoc] using hh
        _ = eqToHom hcommon₂ ≫ φ₂ ≫ δ := by simp [δ, Category.assoc]
        _ = eqToHom hcommon₂ ≫ φ₂ ≫
            (((evaluationFunctor G).map f₂.base).toFunctor.map β₂ ≫
              eqToHom htarget₂') := by rw [← hβmapFun]
    have hcancel' : eqToHom hcommon₁ ≫ φ₁ =
        eqToHom hcommon₂ ≫
          ((evaluationFunctor G).map f₂.base).toFunctor.map θ₂ ≫
            eqToHom htarget₂' := by
      calc
        _ = eqToHom hcommon₂ ≫ φ₂ ≫
            ((evaluationFunctor G).map f₂.base).toFunctor.map β₂ ≫
              eqToHom htarget₂' := hcancel
        _ = eqToHom hcommon₂ ≫
            ((evaluationFunctor G).map f₂.base).toFunctor.map θ₂ ≫
              eqToHom htarget₂' := by
                simpa [Category.assoc] using congrArg
                  (fun q => eqToHom hcommon₂ ≫ q ≫ eqToHom htarget₂') hθmap
    have hraw : G.arrows.map f₁.base a₁B = G.arrows.map f₂.base a₂B := by
      have hv := congrArg (fun q => (G.evaluationArrowEquiv A srcC
        ((evaluationMap G f₁.base).obj x₁) q).1) hcancel'
      have hv₁ : (G.evaluationArrowEquiv A srcC
          ((evaluationMap G f₁.base).obj x₁)
          (eqToHom hcommon₁ ≫ φ₁)).1 =
          (G.evaluationArrowEquiv A src₁
            ((evaluationMap G f₁.base).obj x₁) φ₁).1 := by
        simpa [evaluationFunctor, evaluationMap] using
          evaluationArrowEquiv_eqToHom_comp G A hcommon₁ φ₁
      have hv₂ : (G.evaluationArrowEquiv A srcC
          ((evaluationMap G f₁.base).obj x₁)
          (eqToHom hcommon₂ ≫
            ((evaluationFunctor G).map f₂.base).toFunctor.map θ₂ ≫
              eqToHom htarget₂')).1 =
          (G.evaluationArrowEquiv A src₂
            ((evaluationMap G f₂.base).obj (G.target.app A₂ a₂'))
            (((evaluationFunctor G).map f₂.base).toFunctor.map θ₂)).1 := by
        simpa [evaluationFunctor, evaluationMap,
          Category.assoc] using evaluationArrowEquiv_val_transport G A
            hcommon₂.symm htarget₂'
            (((evaluationFunctor G).map f₂.base).toFunctor.map θ₂)
      calc
        G.arrows.map f₁.base a₁B =
            (G.evaluationArrowEquiv A src₁
              ((evaluationMap G f₁.base).obj x₁) φ₁).1 := by
                show G.arrows.map f₁.base a₁B =
                  (G.evaluationArrowEquiv A
                    ((evaluationMap G f₁.base).obj
                      ((evaluationMap G s.fst.base).obj z))
                    ((evaluationMap G f₁.base).obj x₁)
                    ((evaluationMap G f₁.base).map s.fst.fiber)).1
                exact (evaluationMap_map_arrow G f₁.base s.fst.fiber).symm
        _ = (G.evaluationArrowEquiv A srcC
            ((evaluationMap G f₁.base).obj x₁)
            (eqToHom hcommon₁ ≫ φ₁)).1 := hv₁.symm
        _ = (G.evaluationArrowEquiv A srcC
            ((evaluationMap G f₁.base).obj x₁)
            (eqToHom hcommon₂ ≫
              ((evaluationFunctor G).map f₂.base).toFunctor.map θ₂ ≫
                eqToHom htarget₂')).1 := hv
        _ = (G.evaluationArrowEquiv A src₂
            ((evaluationMap G f₂.base).obj (G.target.app A₂ a₂'))
            (((evaluationFunctor G).map f₂.base).toFunctor.map θ₂)).1 := hv₂
        _ = G.arrows.map f₂.base a₂B := by
              show (G.evaluationArrowEquiv A
                  ((evaluationMap G f₂.base).obj
                    ((evaluationMap G s.snd.base).obj z))
                  ((evaluationMap G f₂.base).obj (G.target.app A₂ a₂'))
                  ((evaluationMap G f₂.base).map θ₂)).1 =
                G.arrows.map f₂.base
                  ((G.evaluationArrowEquiv A₂
                    ((evaluationMap G s.snd.base).obj z)
                    (G.target.app A₂ a₂') θ₂).1)
              exact evaluationMap_map_arrow G f₂.base θ₂
    let cBase : PullbackCone f₁.base f₂.base :=
      c.map (Grothendieck.forget (evaluationFunctor G))
    let w := PullbackCone.IsLimit.lift hcbaseLim s.fst.base s.snd.base hbaseEq
    have hw₁ : w ≫ v₁.hom = s.fst.base := by
      have hh := PullbackCone.IsLimit.lift_fst hcbaseLim s.fst.base s.snd.base hbaseEq
      change w ≫ v₁.hom = s.fst.base at hh
      exact hh
    have hw₂ : w ≫ v₂.hom = s.snd.base := by
      have hh := PullbackCone.IsLimit.lift_snd hcbaseLim s.fst.base s.snd.base hbaseEq
      change w ≫ v₂.hom = s.snd.base at hh
      exact hh
    let aCommon := G.arrows.map f₁.base a₁B
    obtain ⟨bP, hb₁, hb₂⟩ := (elementsPullback_existsUnique G.arrows hR
      f₁.base f₂.base hf₂ cBase hcbaseLim a₁B a₂B aCommon rfl hraw.symm).exists
    have hsource₁ : G.source.app A₁ a₁B = G.objects.map s.fst.base z :=
      (G.evaluationArrowEquiv A₁ ((evaluationMap G s.fst.base).obj z)
        x₁ s.fst.fiber).2.1
    have hsource₂ : G.source.app A₂ a₂B = G.objects.map s.snd.base z :=
      (G.evaluationArrowEquiv A₂
        ((evaluationMap G s.snd.base).obj z)
        (G.target.app A₂ a₂') θ₂).2.1
    have htarget₁ : G.target.app A₁ a₁B = x₁ :=
      (G.evaluationArrowEquiv A₁ ((evaluationMap G s.fst.base).obj z)
        x₁ s.fst.fiber).2.2
    have htarget₂ : G.target.app A₂ a₂B = G.target.app A₂ a₂' :=
      (G.evaluationArrowEquiv A₂
        ((evaluationMap G s.snd.base).obj z)
        (G.target.app A₂ a₂') θ₂).2.2
    have hnat : ∀ (N : G.arrows ⟶ G.objects) {A' : ArtinianLocalAlgCat.{u, v, w} Λ k}
        (g : P ⟶ A') (a : G.arrows.obj A'), G.arrows.map g bP = a →
        G.objects.map g (N.app P bP) = N.app A' a := fun N _ g a h =>
      (N.naturality_apply g bP).symm.trans (by rw [h])
    have hcomp : ∀ {A' : ArtinianLocalAlgCat.{u, v, w} Λ k} (g : P ⟶ A') (h : B ⟶ A'),
        w ≫ g = h → G.objects.map g (G.objects.map w z) = G.objects.map h z := fun g h e =>
      (G.objects.map_comp_apply w g z).symm.trans (by rw [e])
    have hsource₁P := (hnat G.source v₁.hom _ hb₁).trans hsource₁
    have hsource₂P := (hnat G.source v₂.hom _ hb₂).trans hsource₂
    have hsource₁w := hcomp v₁.hom _ hw₁
    have hsource₂w := hcomp v₂.hom _ hw₂
    have hsourceP : G.source.app P bP = G.objects.map w z :=
      (elementsPullback_existsUnique G.objects hU f₁.base f₂.base hf₂ cBase hcbaseLim
        (G.objects.map s.fst.base z) (G.objects.map s.snd.base z) srcC
        hcommon₁.symm hcommon₂.symm).unique ⟨hsource₁P, hsource₂P⟩ ⟨hsource₁w, hsource₂w⟩
    have htarget₁P := (hnat G.target v₁.hom _ hb₁).trans htarget₁
    have htarget₂P := (hnat G.target v₂.hom _ hb₂).trans htarget₂
    have htargetP : G.target.app P bP = zP :=
      (elementsPullback_existsUnique G.objects hU f₁.base f₂.base hf₂ cBase hcbaseLim
        x₁ (G.target.app A₂ a₂') (G.objects.map f₁.base x₁) rfl htarget₂').unique
        ⟨htarget₁P, htarget₂P⟩ ⟨hv₁, hv₂⟩
    let b : ((evaluationFunctor G).map w).toFunctor.obj z ⟶ zP :=
      (G.evaluationArrowEquiv P (G.objects.map w z) zP).symm ⟨bP, hsourceP, htargetP⟩
    have hfib : ∀ {A' : ArtinianLocalAlgCat.{u, v, w} Λ k} (v : P ⟶ A') (u : B ⟶ A')
        (y : G.objects.obj A') (θ : (evaluationMap G u).obj z ⟶ y)
        (hu : G.objects.map v (G.objects.map w z) = G.objects.map u z)
        (hy : G.objects.map v zP = y),
        G.arrows.map v bP = (G.evaluationArrowEquiv A' _ _ θ).1 →
        ((evaluationFunctor G).map v).toFunctor.map b = eqToHom hu ≫ θ ≫ eqToHom hy.symm := by
      intro A' v u y θ hu hy hθ
      refine hom_eq_transport G A' hu hy ((evaluationMap G v).map b) θ
        ((evaluationMap_map_arrow G v b).trans ?_)
      exact (congrArg (G.arrows.map v) (congrArg Subtype.val
        (Equiv.apply_symm_apply (G.evaluationArrowEquiv P (G.objects.map w z) zP) _))).trans hθ
    have hfiber₁' := hfib v₁.hom _ _ s.fst.fiber hsource₁w hv₁ hb₁
    have hfiber₂' := hfib v₂.hom _ _ θ₂ hsource₂w hv₂ hb₂
    let t : s.pt ⟶ c.pt := ⟨w, b⟩
    refine ⟨t, ?_, ?_⟩
    · apply Grothendieck.ext _ _ hw₁
      simp only [Grothendieck.comp_fiber, t, c, m₁]
      dsimp [c, t, m₁]
      apply (eqToHom_comp_iff _ _ _).2
      apply (eqToHom_comp_iff _ _ _).2
      calc
        _ = (eqToHom hsource₁w ≫ s.fst.fiber ≫ eqToHom hv₁.symm) ≫
              eqToHom hv₁ := congrArg (fun f => f ≫ eqToHom hv₁) hfiber₁'
        _ = eqToHom hsource₁w ≫ s.fst.fiber := by
              simp [Category.assoc]
        _ = _ := by
              simp only [eqToHom_trans_assoc]
              rfl
    · apply Grothendieck.ext _ _ hw₂
      simp only [Grothendieck.comp_fiber, t, c, m₂]
      dsimp [c, t, m₂]
      apply (eqToHom_comp_iff _ _ _).2
      apply (eqToHom_comp_iff _ _ _).2
      calc
        _ = (eqToHom hsource₂w ≫ s.snd.fiber ≫ β₂ ≫ eqToHom hv₂.symm) ≫
              eqToHom hv₂ ≫ Groupoid.inv β₂ :=
                congrArg (fun f => f ≫ eqToHom hv₂ ≫ Groupoid.inv β₂)
                  (by
                    convert hfiber₂' using 1
                    simp only [θ₂, z, evaluationFunctor, Category.assoc]
                    rfl)
        _ = eqToHom hsource₂w ≫ s.snd.fiber := by
              simp [Category.assoc]
        _ = _ := by
              simp only [eqToHom_trans_assoc]
              rfl
  refine CategoryTheory.Limits.PullbackCone.IsLimit.mk
    (f := f₁) (g := f₂) c.condition (fun s => Classical.choose (hmed s)) ?_ ?_ ?_
  · intro s
    exact (Classical.choose_spec (hmed s)).1
  · intro s
    exact (Classical.choose_spec (hmed s)).2
  · intro s m hm₁ hm₂
    let t := Classical.choose (hmed s)
    have ht := Classical.choose_spec (hmed s)
    have ht₁ : t ≫ c.fst = s.fst := ht.1
    have ht₂ : t ≫ c.snd = s.snd := ht.2
    have hmB₁ : m.base ≫ c.fst.base = s.fst.base := congrArg (fun q => q.base) hm₁
    have hmB₂ : m.base ≫ c.snd.base = s.snd.base := congrArg (fun q => q.base) hm₂
    have htB₁ : t.base ≫ c.fst.base = s.fst.base := congrArg (fun q => q.base) ht₁
    have htB₂ : t.base ≫ c.snd.base = s.snd.base := congrArg (fun q => q.base) ht₂
    have hbase : m.base = t.base :=
      PullbackCone.IsLimit.hom_ext hcbaseLim (hmB₁.trans htB₁.symm) (hmB₂.trans htB₂.symm)
    let cBase : PullbackCone f₁.base f₂.base :=
      c.map (Grothendieck.forget (evaluationFunctor G))
    apply Grothendieck.ext _ _ hbase
    apply (eqToHom_comp_iff _ _ _).2
    let aM := (G.evaluationArrowEquiv c.pt.base
      (((evaluationFunctor G).map m.base).toFunctor.obj s.pt.fiber)
      c.pt.fiber m.fiber).1
    let aT := (G.evaluationArrowEquiv c.pt.base
      (((evaluationFunctor G).map t.base).toFunctor.obj s.pt.fiber)
      c.pt.fiber t.fiber).1
    have hraw : ∀ {Y : Grothendieck (evaluationFunctor G)} (g : c.pt ⟶ Y), m ≫ g = t ≫ g →
        G.arrows.map g.base aM = G.arrows.map g.base aT := by
      intro Y g hg
      have hgF := Grothendieck.congr hg
      simp only [Grothendieck.comp_fiber] at hgF
      simp only [eqToHom_trans_assoc] at hgF
      have htemp := (eqToHom_comp_iff _ _ _).1 hgF
      simp only [eqToHom_trans_assoc] at htemp
      simp only [evaluationFunctor_obj, Cat.of_α] at htemp
      rw [← Category.assoc] at htemp
      have hmap := (cancel_mono g.fiber).mp htemp
      simp only [evaluationFunctor_obj, Cat.of_α] at hmap
      let hsrc :
          ((evaluationFunctor G).map g.base).toFunctor.obj
            (((evaluationFunctor G).map t.base).toFunctor.obj s.pt.fiber) =
          ((evaluationFunctor G).map g.base).toFunctor.obj
            (((evaluationFunctor G).map m.base).toFunctor.obj s.pt.fiber) :=
        congrArg (fun q : s.pt.base ⟶ c.pt.base =>
          ((evaluationFunctor G).map g.base).toFunctor.obj
            (((evaluationFunctor G).map q).toFunctor.obj s.pt.fiber)) hbase.symm
      calc
        G.arrows.map g.base aM =
            (G.evaluationArrowEquiv Y.base
              (((evaluationFunctor G).map g.base).toFunctor.obj
                (((evaluationFunctor G).map m.base).toFunctor.obj s.pt.fiber))
              (((evaluationFunctor G).map g.base).toFunctor.obj c.pt.fiber)
              (((evaluationFunctor G).map g.base).toFunctor.map m.fiber)).1 := by
                simpa [aM, evaluationFunctor] using
                  (evaluationMap_map_arrow G g.base m.fiber).symm
        _ = (G.evaluationArrowEquiv Y.base
              (((evaluationFunctor G).map g.base).toFunctor.obj
                (((evaluationFunctor G).map m.base).toFunctor.obj s.pt.fiber))
              (((evaluationFunctor G).map g.base).toFunctor.obj c.pt.fiber)
              (eqToHom _ ≫
                ((evaluationFunctor G).map g.base).toFunctor.map t.fiber)).1 :=
                congrArg (fun q =>
                  (G.evaluationArrowEquiv Y.base _ _ q).1) hmap
        _ = (G.evaluationArrowEquiv Y.base
              (((evaluationFunctor G).map g.base).toFunctor.obj
                (((evaluationFunctor G).map t.base).toFunctor.obj s.pt.fiber))
              (((evaluationFunctor G).map g.base).toFunctor.obj c.pt.fiber)
              (((evaluationFunctor G).map g.base).toFunctor.map t.fiber)).1 :=
                evaluationArrowEquiv_eqToHom_comp G Y.base hsrc.symm
                  (((evaluationFunctor G).map g.base).toFunctor.map t.fiber)
        _ = G.arrows.map g.base aT := by
                simpa [aT, evaluationFunctor] using
                  evaluationMap_map_arrow G g.base t.fiber
    have hraw₁ := hraw c.fst (hm₁.trans ht₁.symm)
    have hraw₂ := hraw c.snd (hm₂.trans ht₂.symm)
    let a₁ := G.arrows.map c.fst.base aM
    let a₂ := G.arrows.map c.snd.base aM
    let a := G.arrows.map (c.snd.base ≫ f₂.base) aM
    have ha₁ : G.arrows.map f₁.base a₁ = a := by
      dsimp [a₁, a]
      calc
        G.arrows.map f₁.base (G.arrows.map c.fst.base aM) =
            G.arrows.map (c.fst.base ≫ f₁.base) aM := by
              rw [G.arrows.map_comp_apply]
        _ = G.arrows.map (c.snd.base ≫ f₂.base) aM :=
              congrArg (fun q => G.arrows.map q aM) cBase.condition
    have ha₂ : G.arrows.map f₂.base a₂ = a := by
      dsimp [a₂, a]
      rw [G.arrows.map_comp_apply]
    have hArrow := (elementsPullback_existsUnique G.arrows hR f₁.base f₂.base hf₂
      cBase hcbaseLim a₁ a₂ a ha₁ ha₂).unique ⟨rfl, rfl⟩ ⟨hraw₁.symm, hraw₂.symm⟩
    have hfiber := hom_eq_transport G c.pt.base (by
      exact congrArg (fun q : s.pt.base ⟶ c.pt.base =>
        ((evaluationFunctor G).map q).toFunctor.obj s.pt.fiber) hbase)
      rfl m.fiber t.fiber hArrow
    simpa [aM, aT, evaluationFunctor] using hfiber

end

end Deformation
