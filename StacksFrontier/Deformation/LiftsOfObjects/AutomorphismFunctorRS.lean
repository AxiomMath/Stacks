module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Functor
public import StacksFrontier.Deformation.RimSchlessinger.Basic

/-!
# Condition (RS) for automorphism functors

For an object `x` of a category cofibered in groupoids over `𝒞_Λ` satisfying condition (RS),
the set-valued automorphism functor of `x` on the undercategory `p(x)/𝒞_Λ` also satisfies
condition (RS): it takes a fibre square with surjective second leg to a fibre square of sets.

The argument is the source's. Condition (RS) for `p` produces a pullback of the chosen
pushforwards of `x`, which the universal property identifies with the chosen pushforward over
the fibre product of the base. A compatible pair of automorphisms of the two factors then glues
to a unique automorphism of that pushforward, by the universal property of the pullback, and
the glued morphism lies over the identity because each factor does.

## Main definitions

* `Deformation.SatisfiesRSUnder`: condition (RS) for a set-valued functor on the undercategory
  of a fixed object of `𝒞_Λ`.

## Main results

* `Deformation.automorphismFunctor_satisfiesRS`: the automorphism functor of an object of a
  category over `𝒞_Λ` satisfying (RS) satisfies (RS).

## Implementation notes

The set-valued form of (RS) is expressed as preservation of every pullback cone whose second
leg is surjective; this is the form in which the source uses it. The object of the fibre
category over `A` is represented by `x` together with its image `p.obj x`, and the chosen
pushforwards supply the functor on the undercategory of that image.

## References

* [Stacks Project, Tag 06JU](https://stacks.math.columbia.edu/tag/06JU)
-/

@[expose] public section

namespace Deformation

/-! ### Condition (RS) for a functor on an undercategory -/

section
open CategoryTheory CategoryTheory.Limits

universe u v w u₁ v₁ u₂ v₂

/-- Condition (RS) for a set-valued functor on the category of Artinian local
algebras under a fixed algebra: pullbacks along surjections are preserved. -/
public def SatisfiesRSUnder
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
    (G : Under A ⥤ Type v₁) : Prop :=
  ∀ {A₁ A₂ B : Under A} (f₁ : A₁ ⟶ B) (f₂ : A₂ ⟶ B),
    Function.Surjective f₂.right.hom →
      ∀ (c : PullbackCone f₁ f₂), Nonempty (IsLimit c) →
        Nonempty (IsLimit (c.map G))

/-- The automorphism functor of an object in a category cofibered in groupoids
satisfying (RS) itself satisfies (RS). -/
@[stacks 06JU]
public theorem automorphismFunctor_satisfiesRS
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : SatisfiesRS p) (x : F)
    (P : ChosenPushforwardsAt p x) :
    SatisfiesRSUnder (p.obj x) (automorphismFunctor P) := by
  classical
  intro A₁ A₂ B f₁ f₂ hf₂ c hc
  rcases hc with ⟨hc⟩
  let F₁ := P.map f₁
  let F₂ := P.map f₂
  let hA₁ := (P.obj A₁).2
  let hA₂ := (P.obj A₂).2
  let hB := (P.obj B).2
  let hT := (P.obj c.pt).2
  have hF₁ := IsHomLift.fac' p f₁.right F₁
  have hF₂ := IsHomLift.fac' p f₂.right F₂
  have hf₂' : Function.Surjective (p.map F₂).hom := by
    have hA₂surj : Function.Surjective (eqToHom hA₂).hom := by
      intro a
      refine ⟨(eqToHom hA₂.symm).hom a, ?_⟩
      have hc : eqToHom hA₂.symm ≫ eqToHom hA₂ = 𝟙 _ := by simp
      exact congrArg (fun f => f.hom a) hc
    have hBsurj : Function.Surjective (eqToHom hB.symm).hom := by
      intro b
      refine ⟨(eqToHom hB).hom b, ?_⟩
      have hc : eqToHom hB ≫ eqToHom hB.symm = 𝟙 _ := by simp
      exact congrArg (fun f => f.hom b) hc
    rw [hF₂]
    change Function.Surjective (fun a =>
      (eqToHom hB.symm).hom (f₂.right.hom ((eqToHom hA₂).hom a)))
    exact hBsurj.comp (hf₂.comp hA₂surj)
  obtain ⟨d, ⟨hd⟩, ⟨hdp⟩⟩ := hp.2 F₁ F₂ hf₂'
  let s₀ : PullbackCone F₁ F₂ :=
    PullbackCone.mk (P.inclusion A₁) (P.inclusion A₂) (by
      rw [P.inclusion_map f₁, P.inclusion_map f₂])
  let m : x ⟶ d.pt := hd.lift s₀
  have hm : ∀ (A' : Under (p.obj x)) (π : d.pt ⟶ (P.obj A').1), m ≫ π = P.inclusion A' →
      p.map m ≫ p.map π = A'.hom ≫ eqToHom (P.obj A').2.symm := by
    intro A' π h
    let _ := P.inclusion_cocartesian A'
    rw [← Functor.map_comp, h]
    simpa using IsHomLift.fac' p A'.hom (P.inclusion A')
  have hm₁ := hm A₁ d.fst (hd.fac s₀ WalkingCospan.left)
  have hm₂ := hm A₂ d.snd (hd.fac s₀ WalkingCospan.right)
  let dU : Under (p.obj x) := Under.mk (p.map m)
  have hm₁' : p.map m ≫ (p.map d.fst ≫ eqToHom hA₁) = A₁.hom := by
    rw [← Category.assoc, hm₁]
    simp
  have hm₂' : p.map m ≫ (p.map d.snd ≫ eqToHom hA₂) = A₂.hom := by
    rw [← Category.assoc, hm₂]
    simp
  let q₁ : dU ⟶ A₁ := Under.homMk (p.map d.fst ≫ eqToHom hA₁) hm₁'
  let q₂ : dU ⟶ A₂ := Under.homMk (p.map d.snd ≫ eqToHom hA₂) hm₂'
  have hq : q₁ ≫ f₁ = q₂ ≫ f₂ := by
    apply Under.UnderMorphism.ext
    change (p.map d.fst ≫ eqToHom hA₁) ≫ f₁.right =
      (p.map d.snd ≫ eqToHom hA₂) ≫ f₂.right
    have hdcond := congrArg (fun z => p.map z) d.condition
    rw [Functor.map_comp, Functor.map_comp] at hdcond
    calc
      (p.map d.fst ≫ eqToHom hA₁) ≫ f₁.right =
          p.map d.fst ≫ p.map F₁ ≫ eqToHom hB := by
            rw [Category.assoc, hF₁]
            simp [Category.assoc]
      _ = p.map d.snd ≫ p.map F₂ ≫ eqToHom hB :=
            congrArg (fun z => z ≫ eqToHom hB) hdcond
      _ = (p.map d.snd ≫ eqToHom hA₂) ≫ f₂.right := by
            rw [Category.assoc, hF₂]
            simp [Category.assoc]
  let dC : PullbackCone f₁ f₂ := PullbackCone.mk q₁ q₂ hq
  let u : dU ⟶ c.pt := hc.lift dC
  have hcFcond : P.map c.fst ≫ F₁ = P.map c.snd ≫ F₂ := by
    rw [← P.map_comp, ← P.map_comp, c.condition]
  let cF : PullbackCone F₁ F₂ :=
    PullbackCone.mk (P.map c.fst) (P.map c.snd) hcFcond
  let e : (P.obj c.pt).1 ⟶ d.pt := hd.lift cF
  have he₁ : e ≫ d.fst = P.map c.fst := hd.fac cF WalkingCospan.left
  have he₂ : e ≫ d.snd = P.map c.snd := hd.fac cF WalkingCospan.right
  have hme : P.inclusion c.pt ≫ e = m := by
    apply PullbackCone.IsLimit.hom_ext hd
    · rw [Category.assoc, he₁, P.inclusion_map c.fst]
      exact (hd.fac s₀ WalkingCospan.left).symm
    · rw [Category.assoc, he₂, P.inclusion_map c.snd]
      exact (hd.fac s₀ WalkingCospan.right).symm
  let v : c.pt ⟶ dU := Under.homMk (eqToHom hT.symm ≫ p.map e) (by
    have h : p.map (P.inclusion c.pt) ≫ p.map e = p.map m := by
      simpa only [Functor.map_comp] using congrArg (fun g => p.map g) hme
    let _ := P.inclusion_cocartesian c.pt
    have hi := IsHomLift.fac' p c.pt.hom (P.inclusion c.pt)
    have hi' : p.map (P.inclusion c.pt) = c.pt.hom ≫ eqToHom hT.symm := by
      simpa using hi
    rw [← Category.assoc, ← hi']
    exact h)
  have hu₁ : u.right ≫ c.fst.right = p.map d.fst ≫ eqToHom hA₁ :=
    congrArg Under.Hom.right (hc.fac dC WalkingCospan.left)
  have hu₂ : u.right ≫ c.snd.right = p.map d.snd ≫ eqToHom hA₂ :=
    congrArg Under.Hom.right (hc.fac dC WalkingCospan.right)
  have hproj : ∀ {A' : Under (p.obj x)} (g : c.pt ⟶ A') (π : d.pt ⟶ (P.obj A').1),
      e ≫ π = P.map g → u.right ≫ g.right = p.map π ≫ eqToHom (P.obj A').2 →
      u.right ≫ (eqToHom hT.symm ≫ p.map e) ≫ p.map π = p.map π ∧
        (eqToHom hT.symm ≫ p.map e) ≫ u.right ≫ g.right = g.right := by
    intro A' g π he hu
    have hbase : p.map (P.map g) = eqToHom hT ≫ g.right ≫ eqToHom (P.obj A').2.symm := by
      let _ := P.map_cocartesian g
      exact IsHomLift.fac' p g.right (P.map g)
    constructor
    · rw [Category.assoc, ← Functor.map_comp, he, hbase]
      simp [reassoc_of% hu]
    · rw [hu, Category.assoc, ← Functor.map_comp_assoc, he, hbase]
      simp
  have hp₁ := hproj c.fst d.fst he₁ hu₁
  have hp₂ := hproj c.snd d.snd he₂ hu₂
  have hdu : u ≫ v = 𝟙 dU :=
    Under.UnderMorphism.ext (PullbackCone.IsLimit.hom_ext hdp hp₁.1 hp₂.1)
  have hvc : v ≫ u = 𝟙 c.pt :=
    PullbackCone.IsLimit.hom_ext hc (Under.UnderMorphism.ext hp₁.2) (Under.UnderMorphism.ext hp₂.2)
  let eBase : p.obj (P.obj c.pt).1 ≅ p.obj d.pt :=
    { hom := p.map e
      inv := u.right ≫ eqToHom hT.symm
      hom_inv_id := by
        have h := congrArg (fun q => Under.Hom.right q) hvc
        have hh : (eqToHom hT.symm ≫ p.map e) ≫ u.right = 𝟙 c.pt.right := by
          simpa [v, Category.assoc] using h
        change p.map e ≫ (u.right ≫ eqToHom hT.symm) = 𝟙 _
        calc
          p.map e ≫ (u.right ≫ eqToHom hT.symm) =
              eqToHom hT ≫ ((eqToHom hT.symm ≫ p.map e) ≫ u.right) ≫ eqToHom hT.symm := by
                simp [Category.assoc]
          _ = eqToHom hT ≫ (𝟙 c.pt.right) ≫ eqToHom hT.symm := by rw [hh]
          _ = 𝟙 _ := by simp
      inv_hom_id := by
        have h := congrArg (fun q => Under.Hom.right q) hdu
        change (u.right ≫ eqToHom hT.symm) ≫ p.map e = 𝟙 _
        simpa [v, dU, Category.assoc] using h }
  have hE : IsIso e := by
    have : IsIso (p.map e) := ⟨eBase.inv, eBase.hom_inv_id, eBase.inv_hom_id⟩
    have : p.IsHomLift (p.map e) e := inferInstance
    have : p.IsStronglyCocartesian (p.map e) e :=
      isStronglyCocartesian_of_isCofiberedInGroupoids hp.1 (p.map e) e inferInstance
    exact Functor.IsStronglyCocartesian.isIso_of_base_isIso p (p.map e) e
  let eIso : (P.obj c.pt).1 ≅ d.pt := asIso e
  have i : cF ≅ d := PullbackCone.ext eIso he₁.symm he₂.symm
  have hcf : IsLimit cF := hd.ofIsoLimit i.symm
  have ip : cF.map p ≅ d.map p := PullbackCone.ext (p.mapIso eIso)
    (by
      change p.map (P.map c.fst) = p.map e ≫ p.map d.fst
      rw [← Functor.map_comp, he₁])
    (by
      change p.map (P.map c.snd) = p.map e ≫ p.map d.snd
      rw [← Functor.map_comp, he₂])
  have hcfp : IsLimit (cF.map p) := hdp.ofIsoLimit ip.symm
  let glueCondition (a₁ : Aut (P.obj A₁)) (a₂ : Aut (P.obj A₂))
      (ha : P.transportAut f₁ a₁ = P.transportAut f₂ a₂) :
      (cF.fst ≫ a₁.asIso.hom.val) ≫ F₁ = (cF.snd ≫ a₂.asIso.hom.val) ≫ F₂ := by
    let b₁ := P.transportHom f₁ a₁
    let b₂ := P.transportHom f₂ a₂
    have hb : b₁ = b₂ := congrArg (fun z : Aut (P.obj B) => z.asIso.hom.val) ha
    calc
      (cF.fst ≫ a₁.asIso.hom.val) ≫ F₁ = cF.fst ≫ (F₁ ≫ b₁) := by
        rw [Category.assoc, ← P.map_transportHom]
      _ = cF.snd ≫ (F₂ ≫ b₂) := by rw [reassoc_of% cF.condition, hb]
      _ = (cF.snd ≫ a₂.asIso.hom.val) ≫ F₂ := by
        rw [Category.assoc, ← P.map_transportHom]
  let glue (a₁ : Aut (P.obj A₁)) (a₂ : Aut (P.obj A₂))
      (ha : P.transportAut f₁ a₁ = P.transportAut f₂ a₂) : Aut (P.obj c.pt) := by
    let hcond := glueCondition a₁ a₂ ha
    let t : PullbackCone F₁ F₂ :=
      PullbackCone.mk (cF.fst ≫ a₁.asIso.hom.val) (cF.snd ≫ a₂.asIso.hom.val) hcond
    let z : cF.pt ⟶ cF.pt := hcf.lift t
    have hz₁ : z ≫ cF.fst = cF.fst ≫ a₁.asIso.hom.val := hcf.fac t WalkingCospan.left
    have hz₂ : z ≫ cF.snd = cF.snd ≫ a₂.asIso.hom.val := hcf.fac t WalkingCospan.right
    have haInv : P.transportAut f₁ a₁⁻¹ = P.transportAut f₂ a₂⁻¹ := by
      calc
        P.transportAut f₁ a₁⁻¹ = (P.transportAut f₁ a₁)⁻¹ :=
          (P.transportAutHom f₁).map_inv a₁
        _ = (P.transportAut f₂ a₂)⁻¹ := congrArg Inv.inv ha
        _ = P.transportAut f₂ a₂⁻¹ := ((P.transportAutHom f₂).map_inv a₂).symm
    let t' : PullbackCone F₁ F₂ :=
      PullbackCone.mk (cF.fst ≫ (a₁⁻¹).asIso.hom.val) (cF.snd ≫ (a₂⁻¹).asIso.hom.val)
        (glueCondition a₁⁻¹ a₂⁻¹ haInv)
    let z' : cF.pt ⟶ cF.pt := hcf.lift t'
    have hz₁' : z' ≫ cF.fst = cF.fst ≫ (a₁⁻¹).asIso.hom.val := hcf.fac t' WalkingCospan.left
    have hz₂' : z' ≫ cF.snd = cF.snd ≫ (a₂⁻¹).asIso.hom.val := hcf.fac t' WalkingCospan.right
    have hfib : ∀ {S : ArtinianLocalAlgCat.{u, v, w} Λ k} {X : p.Fiber S} (φ : X ⟶ X),
        p.map φ.val = 𝟙 (p.obj X.1) := fun {S} _ φ => by
      let _ : p.IsHomLift (𝟙 S) φ.val := φ.2
      simpa using IsHomLift.fac' p (𝟙 S) φ.val
    have hlift : ∀ (w : cF.pt ⟶ cF.pt) (b₁ : P.obj A₁ ⟶ P.obj A₁) (b₂ : P.obj A₂ ⟶ P.obj A₂),
        w ≫ cF.fst = cF.fst ≫ b₁.val → w ≫ cF.snd = cF.snd ≫ b₂.val →
        p.IsHomLift (𝟙 c.pt.right) w := by
      intro w b₁ b₂ h₁ h₂
      have leg : ∀ {S} {X : p.Fiber S} (π : cF.pt ⟶ X.1) (b : X ⟶ X), w ≫ π = π ≫ b.val →
          p.map w ≫ p.map π = 𝟙 _ ≫ p.map π := fun π b h => by
        rw [← Functor.map_comp, h, Functor.map_comp, hfib b, Category.comp_id, Category.id_comp]
      have hw : p.map w = 𝟙 _ :=
        PullbackCone.IsLimit.hom_ext hcfp (leg _ b₁ h₁) (leg _ b₂ h₂)
      have hfac : p.map w = eqToHom hT ≫ 𝟙 c.pt.right ≫ eqToHom hT.symm := by
        rw [hw, Category.id_comp, eqToHom_trans, eqToHom_refl]
        rfl
      exact IsHomLift.of_fac' p (𝟙 c.pt.right) w hT hT hfac
    let zm : P.obj c.pt ⟶ P.obj c.pt := ⟨z, hlift z a₁.asIso.hom a₂.asIso.hom hz₁ hz₂⟩
    let zm' : P.obj c.pt ⟶ P.obj c.pt := ⟨z', hlift z' a₁⁻¹.asIso.hom a₂⁻¹.asIso.hom hz₁' hz₂'⟩
    have hinv : ∀ {S} {X : p.Fiber S} (a : Aut X), a.asIso.hom.val ≫ (a⁻¹).asIso.hom.val = 𝟙 X.1 :=
      fun a => congrArg (fun g => Functor.Fiber.fiberInclusion.map g) a.asIso.hom_inv_id
    have hinv' : ∀ {S} {X : p.Fiber S} (a : Aut X), (a⁻¹).asIso.hom.val ≫ a.asIso.hom.val = 𝟙 X.1 :=
      fun a => congrArg (fun g => Functor.Fiber.fiberInclusion.map g) (a⁻¹).asIso.hom_inv_id
    have hcomp : ∀ {X : F} (w w' : cF.pt ⟶ cF.pt) (π : cF.pt ⟶ X) (b b' : X ⟶ X),
        w ≫ π = π ≫ b → w' ≫ π = π ≫ b' → b ≫ b' = 𝟙 X → (w ≫ w') ≫ π = 𝟙 cF.pt ≫ π :=
      fun w w' π b b' h h' hb => by
        rw [Category.assoc, h', ← Category.assoc, h, Category.assoc, hb, Category.comp_id,
          Category.id_comp]
    have hzz' : zm ≫ zm' = 𝟙 (P.obj c.pt) :=
      Functor.Fiber.hom_ext (PullbackCone.IsLimit.hom_ext hcf
        (hcomp z z' _ _ _ hz₁ hz₁' (hinv a₁)) (hcomp z z' _ _ _ hz₂ hz₂' (hinv a₂)))
    have hz'z : zm' ≫ zm = 𝟙 (P.obj c.pt) :=
      Functor.Fiber.hom_ext (PullbackCone.IsLimit.hom_ext hcf
        (hcomp z' z _ _ _ hz₁' hz₁ (hinv' a₁)) (hcomp z' z _ _ _ hz₂' hz₂ (hinv' a₂)))
    exact .of ⟨zm, zm', hzz', hz'z⟩
  have glue_aux : ∀ {A' : Under (p.obj x)} (g : c.pt ⟶ A') (a' : Aut (P.obj A'))
      (G : Aut (P.obj c.pt)), G.asIso.hom.val ≫ P.map g = P.map g ≫ a'.asIso.hom.val →
      P.transportAut g G = a' := by
    intro A' g a' G h
    apply Aut.ext
    apply Iso.ext
    apply Functor.Fiber.hom_ext
    let _ := P.map_cocartesian g
    change P.transportHom g G = a'.asIso.hom.val
    let _ : p.IsHomLift (𝟙 A'.right) (P.transportHom g G) := P.transportHom_isHomLift g G
    let _ : p.IsHomLift (𝟙 A'.right) a'.asIso.hom.val := a'.asIso.hom.2
    apply Functor.IsStronglyCocartesian.ext p g.right (P.map g) (𝟙 A'.right)
    exact (P.map_transportHom g G).trans h
  have glue_fst (a₁ : Aut (P.obj A₁)) (a₂ : Aut (P.obj A₂))
      (ha : P.transportAut f₁ a₁ = P.transportAut f₂ a₂) :
      P.transportAut c.fst (glue a₁ a₂ ha) = a₁ :=
    glue_aux c.fst a₁ _ (by
      simpa [glue, cF, PullbackCone.mk] using hcf.fac (PullbackCone.mk (cF.fst ≫ a₁.asIso.hom.val)
        (cF.snd ≫ a₂.asIso.hom.val) (glueCondition a₁ a₂ ha)) WalkingCospan.left)
  have glue_snd (a₁ : Aut (P.obj A₁)) (a₂ : Aut (P.obj A₂))
      (ha : P.transportAut f₁ a₁ = P.transportAut f₂ a₂) :
      P.transportAut c.snd (glue a₁ a₂ ha) = a₂ :=
    glue_aux c.snd a₂ _ (by
      simpa [glue, cF, PullbackCone.mk] using hcf.fac (PullbackCone.mk (cF.fst ≫ a₁.asIso.hom.val)
        (cF.snd ≫ a₂.asIso.hom.val) (glueCondition a₁ a₂ ha)) WalkingCospan.right)
  have unique_aux : ∀ {A' : Under (p.obj x)} (g : c.pt ⟶ A') (a b : Aut (P.obj c.pt))
      (a' : Aut (P.obj A')), P.transportAut g a = a' → P.transportAut g b = a' →
      a.asIso.hom.val ≫ P.map g = b.asIso.hom.val ≫ P.map g := by
    intro A' g a b a' ha hb
    have hab : P.transportHom g a = P.transportHom g b := by
      simpa [ChosenPushforwardsAt.transportAut] using
        congrArg (fun q : Aut (P.obj A') => q.asIso.hom.val) (ha.trans hb.symm)
    exact (P.map_transportHom g a).symm.trans
      ((congrArg (P.map g ≫ ·) hab).trans (P.map_transportHom g b))
  refine ⟨?_⟩
  refine PullbackCone.isLimitAux' (c.map (automorphismFunctor P)) ?_
  intro s
  have hs (z : s.pt) : P.transportAut f₁ (s.fst z) = P.transportAut f₂ (s.snd z) := by
    simpa [automorphismFunctor, ChosenPushforwardsAt.transportAutHom] using
      congrArg (fun f => f z) s.condition
  let liftMap : s.pt ⟶ (c.map (automorphismFunctor P)).pt :=
    ↾fun z => glue (s.fst z) (s.snd z) (hs z)
  refine ⟨liftMap, ?_, ?_, ?_⟩
  · exact ConcreteCategory.hom_ext _ _ fun z => glue_fst (s.fst z) (s.snd z) (hs z)
  · exact ConcreteCategory.hom_ext _ _ fun z => glue_snd (s.fst z) (s.snd z) (hs z)
  · intro l hl₁ hl₂
    apply ConcreteCategory.hom_ext
    intro z
    apply Aut.ext
    apply Iso.ext
    apply Functor.Fiber.hom_ext
    apply PullbackCone.IsLimit.hom_ext hcf
    · exact unique_aux c.fst _ _ _ (congrArg (fun f => f z) hl₁)
        (glue_fst (s.fst z) (s.snd z) (hs z))
    · exact unique_aux c.snd _ _ _ (congrArg (fun f => f z) hl₂)
        (glue_snd (s.fst z) (s.snd z) (hs z))

end

end Deformation
