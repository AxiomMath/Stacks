module

public import StacksFrontier.Deformation.Artin.Infinitesimal.AugmentedLiftClasses

/-!
# Lift classes relative to a lift, and (RS*) over a thickened base

Let `𝒳` be a category fibred in groupoids over the big fppf site of `S`, let `x` be an object of
`𝒳` over `Spec A`, and let `Q` be an `S`-algebra augmented to `A`. A lift `y` of `x` to `Spec Q`
lets one regard `S`-algebras augmented to `Q` as algebras augmented to `A`, and turns every lift
of `y` into a lift of `x` by composing with the arrow `x → y`; this is compatible with pullback.

The point of the construction is condition (RS*) for a fibre product `L = T ×_Q A₀` taken over
`Q` rather than over `A`: if `T → Q` is surjective with square-zero kernel and a lift class of
`x` over `T` and one over `A₀` have the same restriction to `Q`, then both come from one lift
class over `L`. This is the last step of the proof of Stacks 0CYF, applied to
`lim Rₙ = R̃ ×_{A[M]} A`.

## Main definitions

* `Deformation.Artin.AugmentedSiteRing.restrict` — an algebra augmented to `Q`, regarded as
  augmented to `A`.
* `Deformation.Artin.AugmentedSiteRing.relative` — an algebra augmented to `A` with a map to `Q`,
  regarded as augmented to `Q`.
* `Deformation.Artin.AugmentedSiteRing.compareClass` — the lift classes of `y` mapped to lift
  classes of `x`.

## Main results

* `Deformation.Artin.AugmentedSiteRing.compareClass_map` — compatibility with pullback.
* `Deformation.Artin.AugmentedSiteRing.exists_classes_map_eq_of_isPullback` — (RS*) for a fibre
  product over `Q`, on lift classes of `x`.

## References

* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
* [Stacks Project, Tag 0CYF](https://stacks.math.columbia.edu/tag/0CYF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace Deformation.Artin

section Generic

variable {C : Type*} [Category C] {X : Type*} [Category X] (p : X ⥤ C)

/-- A lift of `x` along `g` lies over `g`. -/
public theorem isHomLift_of_underPostFiber {x : X} {P U : C} (hx : p.obj x = P) {g : P ⟶ U}
    (a : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ g))) : p.IsHomLift g a.1.hom := by
  have hy : p.obj a.1.right = U := congrArg Under.right a.2
  apply IsHomLift.of_fac p g a.1.hom hx hy
  have hw := Under.w (eqToHom a.2)
  simp only [Under.eqToHom_right] at hw
  change p.map a.1.hom ≫ eqToHom hy = eqToHom hx ≫ g at hw
  rw [hw]
  simp

/-- A lift of `x` along `g`, given by an arrow of `X` over `g`. -/
public def underPostFiberMk {x b : X} {P U : C} (hx : p.obj x = P) {g : P ⟶ U}
    (φ : x ⟶ b) [p.IsHomLift g φ] : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ g)) :=
  ⟨Under.mk φ, by
    refine StructuredArrow.obj_ext _ _ (IsHomLift.codomain_eq p g φ) ?_
    change p.map φ ≫ eqToHom (IsHomLift.codomain_eq p g φ) = eqToHom hx ≫ g
    rw [IsHomLift.fac' p g φ]
    simp⟩

end Generic

namespace AugmentedSiteRing

variable {A A' : Type u} [CommRing A] [CommRing A']
  {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  {toS' : Spec (.of A') ⟶ S} {hA' : B.Contains (Spec (.of A'))}

/-- An `S`-algebra augmented to `A` together with a factorization of its augmentation through
`A'`, regarded as augmented to `A'`. -/
public def relative (T : AugmentedSiteRing A B S hS toS hA)
    (δ : algebraOver A' B S hS toS' hA' ⟶ Over.mk T.structureMap)
    (φ : T.ring →+* A') (hφ : B.inclusion.map δ.left = Spec.map (CommRingCat.ofHom φ)) :
    AugmentedSiteRing A' B S hS toS' hA' where
  ring := T.ring
  contains := T.contains
  structureMap := T.structureMap
  aug := φ
  arrow := δ
  arrow_eq := hφ

/-- A morphism of algebras augmented to `A` and factored through `A'`, compatible with the
factorizations, regarded as one of algebras augmented to `A'`. -/
public def Hom.relative {T L : AugmentedSiteRing A B S hS toS hA}
    {δ : algebraOver A' B S hS toS' hA' ⟶ Over.mk T.structureMap} {φ : T.ring →+* A'}
    {hφ : B.inclusion.map δ.left = Spec.map (CommRingCat.ofHom φ)}
    {κ : algebraOver A' B S hS toS' hA' ⟶ Over.mk L.structureMap} {ψ : L.ring →+* A'}
    {hψ : B.inclusion.map κ.left = Spec.map (CommRingCat.ofHom ψ)}
    (l : Hom L T) (hl : δ ≫ l.right = κ) :
    Hom (relative L κ ψ hψ) (relative T δ φ hφ) :=
  Under.homMk l.right hl

variable (s : algebraOver A B S hS toS hA ⟶ algebraOver A' B S hS toS' hA')

section

variable {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {x : X}
  {hx : p.obj x = algebraOver A B S hS toS hA}

/-- A lift `y` of `x` to `Spec A'` lies over `Spec A'`. -/
public theorem obj_eq_of_lift (e : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ s))) :
    p.obj e.1.right = algebraOver A' B S hS toS' hA' :=
  congrArg Under.right e.2

end

variable (q : A' →+* A) (hs : B.inclusion.map s.left = Spec.map (CommRingCat.ofHom q))

include hs

/-- An `S`-algebra augmented to `A'`, regarded as augmented to `A` through `A' → A`. -/
public def restrict (D : AugmentedSiteRing A' B S hS toS' hA') :
    AugmentedSiteRing A B S hS toS hA where
  ring := D.ring
  contains := D.contains
  structureMap := D.structureMap
  aug := q.comp D.aug
  arrow := s ≫ D.arrow
  arrow_eq := by
    rw [Over.comp_left, Functor.map_comp, hs, D.arrow_eq]
    exact (Spec.map_comp (CommRingCat.ofHom D.aug) (CommRingCat.ofHom q)).symm

/-- A morphism of algebras augmented to `A'`, regarded as one of algebras augmented to `A`. -/
public def Hom.restrict {D E : AugmentedSiteRing A' B S hS toS' hA'} (f : Hom D E) :
    Hom (restrict s q hs D) (restrict s q hs E) :=
  Under.homMk f.right (by
    change (s ≫ E.arrow) ≫ f.right = s ≫ D.arrow
    rw [Category.assoc]
    exact congrArg (s ≫ ·) (Under.w f))

/-- The identification of the restriction of a relative algebra with the original one. -/
public def relativeHom (T : AugmentedSiteRing A B S hS toS hA)
    (δ : algebraOver A' B S hS toS' hA' ⟶ Over.mk T.structureMap)
    (φ : T.ring →+* A') (hφ : B.inclusion.map δ.left = Spec.map (CommRingCat.ofHom φ))
    (hδ : s ≫ δ = T.arrow) :
    Hom (restrict s q hs (relative T δ φ hφ)) T :=
  Under.homMk (𝟙 _) (by
    change T.arrow ≫ 𝟙 _ = s ≫ δ
    rw [Category.comp_id, hδ])

variable {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {x : X}
  {hx : p.obj x = algebraOver A B S hS toS hA}

variable (e : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ s)))

/-- The lift of `x` attached to a lift of `y`, by composing with `x → y`. -/
public def compareObj (D : AugmentedSiteRing A' B S hS toS' hA')
    (d : (Under.post p).Fiber (Under.mk (eqToHom (obj_eq_of_lift s e) ≫ D.arrow))) :
    (Under.post p).Fiber (Under.mk (eqToHom hx ≫ (restrict s q hs D).arrow)) :=
  haveI : p.IsHomLift s e.1.hom := isHomLift_of_underPostFiber p hx e
  haveI : p.IsHomLift D.arrow d.1.hom := isHomLift_of_underPostFiber p (obj_eq_of_lift s e) d
  haveI : p.IsHomLift (restrict s q hs D).arrow (e.1.hom ≫ d.1.hom) :=
    inferInstanceAs (p.IsHomLift (s ≫ D.arrow) (e.1.hom ≫ d.1.hom))
  underPostFiberMk p hx (g := (restrict s q hs D).arrow) (e.1.hom ≫ d.1.hom)

/-- The morphism underlying `compareObj s q hs e D d` is the composite `e.1.hom ≫ d.1.hom`. -/
theorem compareObj_hom (D : AugmentedSiteRing A' B S hS toS' hA')
    (d : (Under.post p).Fiber (Under.mk (eqToHom (obj_eq_of_lift s e) ≫ D.arrow))) :
    (compareObj s q hs e D d).1.hom = e.1.hom ≫ d.1.hom := rfl

/-- Lift classes of `y` mapped to lift classes of `x`. -/
public def compareClass (hp : p.IsFiberedInGroupoids) (D : AugmentedSiteRing A' B S hS toS' hA') :
    classes p e.1.right (obj_eq_of_lift s e) D → classes p x hx (restrict s q hs D) :=
  Quotient.lift (fun d => Quotient.mk _ (compareObj s q hs e D d)) (by
    rintro d d' ⟨i⟩
    have hi : p.IsHomLift (𝟙 (Over.mk (restrict s q hs D).structureMap)) i.inv.1.right :=
      underPost_isHomLift_right p (𝟙 _) i.inv.1 i.inv.2
    have hφ : p.IsStronglyCartesian (𝟙 (Over.mk (restrict s q hs D).structureMap))
        i.inv.1.right :=
      hp.isStronglyCartesian_homLift _ _
    have h := map_eq_of_lift p x hx hp (𝟙 (restrict s q hs D).under)
      (compareObj s q hs e D d) (compareObj s q hs e D d') i.inv.1.right hφ (by
        change (e.1.hom ≫ d'.1.hom) ≫ i.inv.1.right = e.1.hom ≫ d.1.hom
        rw [Category.assoc, Under.w i.inv.1])
    rwa [map_id] at h)

/-- `compareClass` sends the class of a lift `d` to the class of `compareObj s q hs e D d`. -/
theorem compareClass_mk (hp : p.IsFiberedInGroupoids) (D : AugmentedSiteRing A' B S hS toS' hA')
    (d : (Under.post p).Fiber (Under.mk (eqToHom (obj_eq_of_lift s e) ≫ D.arrow))) :
    compareClass s q hs e hp D (Quotient.mk _ d) = Quotient.mk _ (compareObj s q hs e D d) := rfl

/-- The comparison of lift classes is compatible with pullback. -/
public theorem compareClass_map (hp : p.IsFiberedInGroupoids)
    {D E : AugmentedSiteRing A' B S hS toS' hA'}
    (f : Hom D E) (z : classes p e.1.right (obj_eq_of_lift s e) D) :
    map p x hx hp (Hom.restrict s q hs f) (compareClass s q hs e hp D z) =
      compareClass s q hs e hp E (map p e.1.right (obj_eq_of_lift s e) hp f z) := by
  induction z using Quotient.ind with
  | _ d =>
    obtain ⟨d', φ, hφ, hw, hmap⟩ := representative_map p e.1.right (obj_eq_of_lift s e) hp f d
    rw [hmap, compareClass_mk, compareClass_mk]
    exact map_eq_of_lift p x hx hp (Hom.restrict s q hs f) (compareObj s q hs e D d)
      (compareObj s q hs e E d') φ hφ (by
        change (e.1.hom ≫ d'.1.hom) ≫ φ = e.1.hom ≫ d.1.hom
        rw [Category.assoc, hw])

end AugmentedSiteRing

namespace AugmentedSiteRing

variable {A : Type u} [CommRing A]
  {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {x : X}
  {hx : p.obj x = algebraOver A B S hS toS hA}

/-- **Condition (RS*) for a fibre product over `Q`, on lift classes.** Let `L = A₀ ×_Q T` be a
fibre product of algebras augmented to `A`, formed over a third such algebra `Q`, with `T → Q`
surjective with square-zero kernel. If a lift class of `x` over `T` and one over `A₀` have the
same restriction to `Q`, then both are restrictions of one lift class over `L`. -/
public theorem exists_classes_map_eq_of_isPullback (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS p hp)
    {Q T A₀ L : AugmentedSiteRing A B S hS toS hA}
    (δ : Hom T Q) (φδ : T.ring →+* Q.ring)
    (hφδ : B.inclusion.map δ.right.left = Spec.map (CommRingCat.ofHom φδ))
    (ι : Hom A₀ Q) (φι : A₀.ring →+* Q.ring)
    (hφι : B.inclusion.map ι.right.left = Spec.map (CommRingCat.ofHom φι))
    (κ : Hom L Q) (φκ : L.ring →+* Q.ring)
    (hφκ : B.inclusion.map κ.right.left = Spec.map (CommRingCat.ofHom φκ))
    (l₁ : Hom L T) (l₂ : Hom L A₀) (h₁ : δ ≫ l₁ = κ) (h₂ : ι ≫ l₂ = κ)
    (hpb : IsPullback
      ((BigFppfOver.toScheme B S hS).map l₂.right).appTop
      ((BigFppfOver.toScheme B S hS).map l₁.right).appTop
      (Spec.map (CommRingCat.ofHom φι)).appTop
      (Spec.map (CommRingCat.ofHom φδ)).appTop)
    (hsurj : Function.Surjective φδ) (hsq : (RingHom.ker φδ) ^ 2 = ⊥)
    (η : classes p x hx T) (c : classes p x hx A₀)
    (h : map p x hx hp δ η = map p x hx hp ι c) :
    ∃ ξ : classes p x hx L, map p x hx hp l₁ ξ = η ∧ map p x hx hp l₂ ξ = c := by
  induction η using Quotient.ind with
  | _ e₀ =>
  induction c using Quotient.ind with
  | _ d₀ =>
  obtain ⟨e, φ, hφ, hwe, hme⟩ := representative_map p x hx hp δ e₀
  obtain ⟨d, ψ, hψ, hwd, hmd⟩ := representative_map p x hx hp ι d₀
  rw [hme, hmd] at h
  obtain ⟨θ⟩ := Quotient.exact h
  let s : algebraOver A B S hS toS hA ⟶
      algebraOver Q.ring B S hS (B.inclusion.map Q.structureMap) Q.contains := Q.arrow
  have hs : B.inclusion.map s.left = Spec.map (CommRingCat.ofHom Q.aug) := Q.arrow_eq
  let y := e.1.right
  have hy : p.obj y = algebraOver Q.ring B S hS (B.inclusion.map Q.structureMap) Q.contains :=
    obj_eq_of_lift s e
  let DT := relative T δ.right φδ hφδ
  let DA := relative A₀ ι.right φι hφι
  let DL := relative L κ.right φκ hφκ
  have : p.IsHomLift DT.arrow φ := hφ.toIsHomLift
  have : p.IsHomLift DA.arrow ψ := hψ.toIsHomLift
  have : p.IsHomLift (𝟙 (algebraOver Q.ring B S hS (B.inclusion.map Q.structureMap) Q.contains))
      θ.hom.1.right :=
    underPost_isHomLift_right p (𝟙 _) θ.hom.1 θ.hom.2
  let zT : (Under.post p).Fiber (Under.mk (eqToHom hy ≫ DT.arrow)) :=
    underPostFiberMk p hy (g := DT.arrow) φ
  let zA : (Under.post p).Fiber (Under.mk (eqToHom hy ≫ DA.arrow)) :=
    underPostFiberMk p hy (g := DA.arrow) (θ.hom.1.right ≫ ψ)
  obtain ⟨t, ht⟩ :=
    (pair_bijective p y hy hp hRS DA DT DL (Hom.relative l₂ (by rw [← h₂]; rfl))
      (Hom.relative l₁ (by rw [← h₁]; rfl)) hpb hsurj hsq).2 (Quotient.mk _ zA, Quotient.mk _ zT)
  let ρL := relativeHom s Q.aug hs L κ.right φκ hφκ (Under.w κ)
  have key : ∀ (M : AugmentedSiteRing A B S hS toS hA) (μ : Hom M Q) (φμ : M.ring →+* Q.ring)
      (hφμ : B.inclusion.map μ.right.left = Spec.map (CommRingCat.ofHom φμ)) (l : Hom L M)
      (hl : μ.right ≫ l.right = κ.right) (m₀ : (Under.post p).Fiber
        (Under.mk (eqToHom hx ≫ M.arrow)))
      (z : (Under.post p).Fiber (Under.mk (eqToHom hy ≫ (relative M μ.right φμ hφμ).arrow)))
      (g : m₀.1.right ⟶ z.1.right) (hg : p.IsHomLift (𝟙 (Over.mk M.structureMap)) g)
      (hz : m₀.1.hom ≫ g = e.1.hom ≫ z.1.hom) (t : classes p y hy DL),
      map p y hy hp (Hom.relative l hl) t = Quotient.mk _ z →
      map p x hx hp l (map p x hx hp ρL (compareClass s Q.aug hs e hp DL t)) =
        Quotient.mk _ m₀ := by
    intro M μ φμ hφμ l hl m₀ z g hg hz t htz
    let ρM := relativeHom s Q.aug hs M μ.right φμ hφμ (Under.w μ)
    have hcomp : l ≫ ρL = ρM ≫ Hom.restrict s Q.aug hs (Hom.relative l hl) := by
      apply Under.UnderMorphism.ext
      change l.right ≫ 𝟙 _ = 𝟙 _ ≫ l.right
      rw [Category.comp_id, Category.id_comp]
    rw [← map_comp, hcomp, map_comp]
    refine (congrArg (map p x hx hp ρM) (compareClass_map s Q.aug hs e hp _ t)).trans ?_
    refine (congrArg (fun w => map p x hx hp ρM (compareClass s Q.aug hs e hp _ w)) htz).trans ?_
    have : p.IsHomLift ρM.right g := hg
    have hst : p.IsStronglyCartesian ρM.right g := hp.isStronglyCartesian_homLift _ _
    exact map_eq_of_lift p x hx hp ρM (compareObj s Q.aug hs e _ z) m₀ g hst hz
  refine ⟨map p x hx hp ρL (compareClass s Q.aug hs e hp DL t), ?_, ?_⟩
  · exact key T δ φδ hφδ l₁ (by rw [← h₁]; rfl) e₀ zT (𝟙 _)
      (IsHomLift.id (p := p) (by exact congrArg Under.right e₀.2))
      ((Category.comp_id _).trans hwe.symm) t (congrArg Prod.snd ht)
  · exact key A₀ ι φι hφι l₂ (by rw [← h₂]; rfl) d₀ zA (𝟙 _)
      (IsHomLift.id (p := p) (by exact congrArg Under.right d₀.2))
      ((Category.comp_id _).trans
        (by
          rw [← hwd]
          change _ = e.1.hom ≫ θ.hom.1.right ≫ ψ
          rw [← Category.assoc, Under.w θ.hom.1])) t
      (congrArg Prod.fst ht)

end AugmentedSiteRing

end Deformation.Artin
