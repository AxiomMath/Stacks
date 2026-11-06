module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Artin.Infinitesimal.AutomorphismFunctor

/-!
# The transition on lifts over a trivial square-zero extension along a ring map

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S`, let `A` and
`C` be `S`-algebras whose spectra lie in the site, let `x` be an object of `𝒳` over `Spec A`
and let `y` be an object of `𝒳` over `Spec C` together with a morphism `y ⟶ x` lying over
`Spec C ⟶ Spec A`. Given a ring map `f : A ⟶ C`, an `A`-module `M`, a `C`-module `N` and an
`f`-semilinear map `M ⟶ N`, the ring map

`A[M] ⟶ C[N]`, `(a, m) ↦ (f a, ψ m)`

induces a morphism `Spec C[N] ⟶ Spec A[M]` under which lifts of `x` over `Spec A[M]` pull
back to lifts of `y` over `Spec C[N]`. This file constructs that pullback, shows that it is
single-valued on isomorphism classes, and so produces the induced map on classes of lifts.

These are the statements that `StacksFrontier.Deformation.Artin.Obstruction.NaiveTheory` and
`StacksFrontier.Deformation.Artin.Obstruction.FieldCohomology` carry for a pair of
`Deformation.Artin.ChartedObject`s, which additionally fix an affine chart `Spec Λ ⊆ S` that
both algebras map into. Nothing in the construction uses the chart, so everything here is
stated for a pair of objects over rings of the site directly; the charted statements are
definitionally these ones.

## Main definitions

* `Deformation.Artin.IsSiteSquareZeroBaseMap` — the morphism `Spec C[N] ⟶ Spec A[M]` of the
  site determined by `f` and `ψ`, pinned down by the ring map it is the spectrum of.
* `Deformation.Artin.squareZeroLiftOver` — the lifts of `x` over `Spec A[M]`, together with
  their identification with `x` after restriction to `Spec A`.
* `Deformation.Artin.IsSiteSquareZeroLiftBaseChange` — the relation "the class `b` of lifts of
  `y` over `C[N]` is the pullback of the class `a` of lifts of `x` over `A[M]`".
* `Deformation.Artin.siteSquareZeroLiftBaseChange` — the pullback of a single lift, with the
  cartesian arrow that exhibits it.
* `Deformation.Artin.siteSquareZeroLiftBaseChangeMap` — the induced map on isomorphism classes
  of lifts.

## Main results

* `Deformation.Artin.eq_of_isSiteSquareZeroLiftBaseChange` — the relation is single-valued, so
  the induced map on classes is determined by it.
* `Deformation.Artin.isSiteSquareZeroLiftBaseChange_siteSquareZeroLiftBaseChangeMap` — the
  induced map has the defining property.

## References

* [Stacks Project, Tag 07YA](https://stacks.math.columbia.edu/tag/07YA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace Deformation.Artin

/-! ### The morphism of trivial square-zero extensions along a ring map -/

section SiteBaseMap

variable {A C : Type u} [CommRing A] [CommRing C] (B : BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (toSC : Spec (.of C) ⟶ S)

/-- The ring map `A[M] ⟶ C[N]` of trivial square-zero extensions determined by a ring map
`f : A ⟶ C` and an `f`-semilinear map `M ⟶ N` of coefficients, together with the morphism of
spectra over `S` it induces: the base of the transition maps of Stacks 07YA. -/
public def IsSiteSquareZeroBaseMap (f : A →+* C)
    {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (g : squareZeroOver C B S hS toSC N ⟶ squareZeroOver A B S hS toS M) : Prop :=
  ∃ e : TrivSqZeroExt A M.obj →+* TrivSqZeroExt C N.obj,
    (∀ z : TrivSqZeroExt A M.obj, e z = (f z.fst, ψ z.snd)) ∧
      (BigFppfOver.toScheme B S hS).map g = Spec.map (CommRingCat.ofHom e)

/-- The morphism `Spec C[N] ⟶ Spec A[M]` of a transition of Stacks 07YA is determined by the
ring map and the semilinear map of coefficients it is built from. -/
public theorem eq_of_isSiteSquareZeroBaseMap {f : A →+* C}
    {M : SiteModule A B} {N : SiteModule C B}
    {ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj}
    {g g' : squareZeroOver C B S hS toSC N ⟶ squareZeroOver A B S hS toS M}
    (hg : IsSiteSquareZeroBaseMap B S hS toS toSC f ψ g)
    (hg' : IsSiteSquareZeroBaseMap B S hS toS toSC f ψ g') : g = g' := by
  obtain ⟨e, he, hge⟩ := hg
  obtain ⟨e', he', hge'⟩ := hg'
  have hee : e = e' := RingHom.ext fun z => (he z).trans (he' z).symm
  have hgg : (BigFppfOver.toScheme B S hS).map g = (BigFppfOver.toScheme B S hS).map g' := by
    rw [hge, hge', hee]
  exact Over.OverMorphism.ext (ObjectProperty.hom_ext _ hgg)

end SiteBaseMap

/-! ### Lifts over a trivial square-zero extension -/

section LiftsOver

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)

/-- Lifts of `x` to `Spec A[M]`, together with their identification with `x` after
restriction to `Spec A`. -/
public abbrev squareZeroLiftOver (M : SiteModule A B) : Type _ :=
  (Under.post p).Fiber (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M))

end LiftsOver

/-! ### The transition on classes of lifts along a ring map -/

section SiteLiftBaseChange

open CategoryTheory.Functor

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor

variable {A C : Type u} [CommRing A] [CommRing C] (B : BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
  (toSC : Spec (.of C) ⟶ S) (hC : B.Contains (Spec (.of C)))
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x y : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)
  (hy : p.obj y = algebraOver C B S hS toSC hC)
  (φ₀ : y ⟶ x) (f : A →+* C)
  {M : SiteModule A B} {N : SiteModule C B}
  (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)

/-- The structure arrow of a lift of `x` over `Spec A[M]` lies over the square-zero immersion
`Spec A ⟶ Spec A[M]` that `x` is a lift along.

This is the statement of `Deformation.Artin.isHomLift_fiberUnder_hom` at the objects of this
file, where it is needed below the module that carries the general one. -/
public theorem isHomLift_squareZeroLiftOver_hom
    (a : squareZeroLiftOver A B S hS toS hA p x hx M) :
    p.IsHomLift (squareZeroArrow A B S hS toS hA M) a.1.hom := by
  have hr : p.obj a.1.right = squareZeroOver A B S hS toS M := congrArg Under.right a.2
  apply IsHomLift.of_fac p (squareZeroArrow A B S hS toS hA M) a.1.hom hx hr
  have hw := Under.w (eqToHom a.2)
  simp only [Under.eqToHom_right] at hw
  change p.map a.1.hom ≫ eqToHom hr = eqToHom hx ≫ squareZeroArrow A B S hS toS hA M at hw
  rw [hw]
  simp

/-- Comparison maps `ι : u ⟶ v` and `ι' : v ⟶ u` between the sources of two arrows over the
same arrow, compatible with mutually inverse maps of the targets, are inverse when `φ₁` is
cartesian. -/
private theorem comp_eq_id_of_isCartesian {𝒳 𝒮 : Type*} [Category 𝒳] [Category 𝒮]
    (p : 𝒳 ⥤ 𝒮) {R S : 𝒮} {u v w w' : 𝒳} (g : R ⟶ S) {φ₁ : u ⟶ w} {φ₂ : v ⟶ w'}
    [p.IsCartesian g φ₁] {ι : u ⟶ v} {ι' : v ⟶ u} [p.IsHomLift (𝟙 R) ι] [p.IsHomLift (𝟙 R) ι']
    {s : w ⟶ w'} {t : w' ⟶ w} (hu : p.obj u = R) (h : ι ≫ φ₂ = φ₁ ≫ s)
    (h' : ι' ≫ φ₁ = φ₂ ≫ t) (hst : s ≫ t = 𝟙 w) : ι ≫ ι' = 𝟙 u := by
  have := IsHomLift.id (p := p) hu
  refine Functor.IsCartesian.ext p g φ₁ _ _ ?_
  rw [Category.id_comp, Category.assoc, h', ← Category.assoc, h, Category.assoc, hst,
    Category.comp_id]

/-- The transition of Stacks 07YA on lifts across a ring map: the class `b` of lifts of `y`
over `C[N]` is the pullback of the class `a` of lifts of `x` over `A[M]` along the morphism
`Spec C[N] ⟶ Spec A[M]` induced by `A ⟶ C` and `M ⟶ N`, compatibly with `y ⟶ x`. -/
public def IsSiteSquareZeroLiftBaseChange
    (a : squareZeroLiftClasses A B S hS toS hA p x hx M)
    (b : squareZeroLiftClasses C B S hS toSC hC p y hy N) : Prop :=
  ∃ (a' : squareZeroLiftOver A B S hS toS hA p x hx M)
    (b' : squareZeroLiftOver C B S hS toSC hC p y hy N),
    Quotient.mk _ a' = a ∧ Quotient.mk _ b' = b ∧
      ∃ g : squareZeroOver C B S hS toSC N ⟶ squareZeroOver A B S hS toS M,
        IsSiteSquareZeroBaseMap B S hS toS toSC f ψ g ∧
          ∃ φ : b'.1.right ⟶ a'.1.right,
            p.IsStronglyCartesian g φ ∧ b'.1.hom ≫ φ = φ₀ ≫ a'.1.hom

variable (hp : p.IsFiberedInGroupoids)
  (specMap : algebraOver C B S hS toSC hC ⟶ algebraOver A B S hS toS hA)
  (hφ₀ : p.IsHomLift specMap φ₀)
  (g : squareZeroOver C B S hS toSC N ⟶ squareZeroOver A B S hS toS M)
  (hsq : specMap ≫ squareZeroArrow A B S hS toS hA M =
    squareZeroArrow C B S hS toSC hC N ≫ g)

include hp hφ₀ hsq in
/-- The pullback of a lift of `x` over `Spec A[M]` along `Spec C[N] ⟶ Spec A[M]`, as a lift of
`y` over `Spec C[N]`: the chosen strongly cartesian pullback, whose structure arrow out of `y`
is supplied by the universal property applied to `y ⟶ x ⟶ x'`. -/
public def siteSquareZeroLiftBaseChange (a : squareZeroLiftOver A B S hS toS hA p x hx M) :
    { b : squareZeroLiftOver C B S hS toSC hC p y hy N // ∃ ρ : b.1.right ⟶ a.1.right,
      p.IsStronglyCartesian g ρ ∧ b.1.hom ≫ ρ = φ₀ ≫ a.1.hom } := by
  letI : p.IsFibered := hp.isFibered
  have hah : p.IsHomLift (squareZeroArrow A B S hS toS hA M) a.1.hom :=
    isHomLift_squareZeroLiftOver_hom B S hS toS hA p x hx a
  have hcomp : p.IsHomLift (squareZeroArrow C B S hS toSC hC N ≫ g) (φ₀ ≫ a.1.hom) := by
    rw [← hsq]
    have := hφ₀
    have := hah
    infer_instance
  have hfac : squareZeroArrow C B S hS toSC hC N ≫ g =
      squareZeroArrow C B S hS toSC hC N ≫ g := rfl
  let xa : p.Fiber (squareZeroOver A B S hS toS M) := ⟨a.1.right, congrArg Under.right a.2⟩
  let ρ := (Functor.chosenPullbacks p).map g xa
  have hρ : p.IsStronglyCartesian g ρ := (Functor.chosenPullbacks p).isStronglyCartesian g xa
  have hhomlift : p.IsHomLift (squareZeroArrow C B S hS toSC hC N)
      (Functor.IsStronglyCartesian.map p g ρ hfac (φ₀ ≫ a.1.hom)) :=
    Functor.IsStronglyCartesian.map_isHomLift p g ρ hfac _
  refine ⟨⟨Under.mk (Functor.IsStronglyCartesian.map p g ρ hfac (φ₀ ≫ a.1.hom)),
    StructuredArrow.obj_ext _ _ ((Functor.chosenPullbacks p).obj g xa).2 ?_⟩,
    ρ, hρ, Functor.IsStronglyCartesian.fac p g ρ hfac _⟩
  change p.map (Functor.IsStronglyCartesian.map p g ρ hfac (φ₀ ≫ a.1.hom)) ≫
      eqToHom ((Functor.chosenPullbacks p).obj g xa).2 =
    eqToHom hy ≫ squareZeroArrow C B S hS toSC hC N
  rw [IsHomLift.fac' p (squareZeroArrow C B S hS toSC hC N) _,
    Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

include hp hφ₀ hsq in
/-- The pullback of a lift along `Spec C[N] ⟶ Spec A[M]` realizes the transition of
Stacks 07YA on the classes of the two lifts. -/
public theorem isSiteSquareZeroLiftBaseChange_siteSquareZeroLiftBaseChange
    (hg : IsSiteSquareZeroBaseMap B S hS toS toSC f ψ g)
    (a : squareZeroLiftOver A B S hS toS hA p x hx M) :
    IsSiteSquareZeroLiftBaseChange B S hS toS hA toSC hC p x y hx hy φ₀ f ψ
      (Quotient.mk _ a)
      (Quotient.mk _ (siteSquareZeroLiftBaseChange B S hS toS hA toSC hC p x y hx hy φ₀
        hp specMap hφ₀ g hsq a).1) :=
  ⟨a, (siteSquareZeroLiftBaseChange B S hS toS hA toSC hC p x y hx hy φ₀
      hp specMap hφ₀ g hsq a).1, rfl, rfl, g, hg,
    (siteSquareZeroLiftBaseChange B S hS toS hA toSC hC p x y hx hy φ₀
      hp specMap hφ₀ g hsq a).2.choose,
    (siteSquareZeroLiftBaseChange B S hS toS hA toSC hC p x y hx hy φ₀
      hp specMap hφ₀ g hsq a).2.choose_spec.1,
    (siteSquareZeroLiftBaseChange B S hS toS hA toSC hC p x y hx hy φ₀
      hp specMap hφ₀ g hsq a).2.choose_spec.2⟩

/-- **The transition of Stacks 07YA on lift classes is single-valued.** Two classes of lifts of
`y` over `C[N]` which are both pullbacks of one class of lifts of `x` over `A[M]` along the
morphism induced by `A ⟶ C` and `M ⟶ N` coincide. -/
public theorem eq_of_isSiteSquareZeroLiftBaseChange
    {a : squareZeroLiftClasses A B S hS toS hA p x hx M}
    {b b' : squareZeroLiftClasses C B S hS toSC hC p y hy N}
    (hb : IsSiteSquareZeroLiftBaseChange B S hS toS hA toSC hC p x y hx hy φ₀ f ψ a b)
    (hb' : IsSiteSquareZeroLiftBaseChange B S hS toS hA toSC hC p x y hx hy φ₀ f ψ a b') :
    b = b' := by
  obtain ⟨a₁, b₁, ha₁, hb₁, g₁, hg₁, φ₁, hφ₁, hc₁⟩ := hb
  obtain ⟨a₂, b₂, ha₂, hb₂, g₂, hg₂, φ₂, hφ₂, hc₂⟩ := hb'
  rw [eq_of_isSiteSquareZeroBaseMap B S hS toS toSC hg₂ hg₁] at hφ₂
  obtain ⟨α⟩ := Quotient.exact (ha₁.trans ha₂.symm)
  subst hb₁
  subst hb₂
  have hβh : p.IsHomLift (𝟙 (squareZeroOver A B S hS toS M)) α.hom.1.right :=
    underPost_isHomLift_right p (𝟙 _) α.hom.1 α.hom.2
  have hβi : p.IsHomLift (𝟙 (squareZeroOver A B S hS toS M)) α.inv.1.right :=
    underPost_isHomLift_right p (𝟙 _) α.inv.1 α.inv.2
  have hβhi : α.hom.1.right ≫ α.inv.1.right = 𝟙 a₁.1.right :=
    congrArg (fun m : a₁ ⟶ a₁ => m.1.right) α.hom_inv_id
  have hβih : α.inv.1.right ≫ α.hom.1.right = 𝟙 a₂.1.right :=
    congrArg (fun m : a₂ ⟶ a₂ => m.1.right) α.inv_hom_id
  have hwh : a₁.1.hom ≫ α.hom.1.right = a₂.1.hom := Under.w α.hom.1
  have hwi : a₂.1.hom ≫ α.inv.1.right = a₁.1.hom := Under.w α.inv.1
  have hlift₁ : p.IsHomLift g₁ (φ₁ ≫ α.hom.1.right) := inferInstance
  have hlift₂ : p.IsHomLift g₁ (φ₂ ≫ α.inv.1.right) := inferInstance
  let ι := Functor.IsCartesian.map p g₁ φ₂ (φ₁ ≫ α.hom.1.right)
  let ι' := Functor.IsCartesian.map p g₁ φ₁ (φ₂ ≫ α.inv.1.right)
  have hιlift : p.IsHomLift (𝟙 (squareZeroOver C B S hS toSC N)) ι :=
    Functor.IsCartesian.map_isHomLift p g₁ φ₂ _
  have hι'lift : p.IsHomLift (𝟙 (squareZeroOver C B S hS toSC N)) ι' :=
    Functor.IsCartesian.map_isHomLift p g₁ φ₁ _
  have hιfac : ι ≫ φ₂ = φ₁ ≫ α.hom.1.right := Functor.IsCartesian.fac p g₁ φ₂ _
  have hι'fac : ι' ≫ φ₁ = φ₂ ≫ α.inv.1.right := Functor.IsCartesian.fac p g₁ φ₁ _
  have hsa₁ : p.IsHomLift (squareZeroArrow C B S hS toSC hC N) b₁.1.hom :=
    isHomLift_squareZeroLiftOver_hom B S hS toSC hC p y hy b₁
  have hsa₂ : p.IsHomLift (squareZeroArrow C B S hS toSC hC N) b₂.1.hom :=
    isHomLift_squareZeroLiftOver_hom B S hS toSC hC p y hy b₂
  have hιι' : ι ≫ ι' = 𝟙 b₁.1.right :=
    comp_eq_id_of_isCartesian p g₁ (congrArg Under.right b₁.2) hιfac hι'fac hβhi
  have hι'ι : ι' ≫ ι = 𝟙 b₂.1.right :=
    comp_eq_id_of_isCartesian p g₁ (congrArg Under.right b₂.2) hι'fac hιfac hβih
  have hunder : b₁.1.hom ≫ ι = b₂.1.hom := by
    refine Functor.IsStronglyCartesian.ext p g₁ φ₂
      (squareZeroArrow C B S hS toSC hC N) ?_
    rw [Category.assoc, hιfac, ← Category.assoc, hc₁, Category.assoc, hwh, hc₂]
  refine Quotient.sound ⟨Functor.Fiber.isoMk
    (Under.isoMk ⟨ι, ι', hιι', hι'ι⟩ hunder) ?_⟩
  refine IsHomLift.of_fac' (Under.post p) (𝟙 _) _ b₁.2 b₂.2 ?_
  apply Under.UnderMorphism.ext
  simp only [Under.comp_right, Under.eqToHom_right, Under.id_right]
  exact IsHomLift.fac' p (𝟙 (squareZeroOver C B S hS toSC N)) ι

include hp hφ₀ hsq in
/-- **The transition of Stacks 07YA on lift classes.** Pullback along the morphism
`Spec C[N] ⟶ Spec A[M]` induced by a ring map `A ⟶ C` and an `A`-semilinear map `M ⟶ N` of
coefficients, on isomorphism classes of lifts. -/
public def siteSquareZeroLiftBaseChangeMap
    (hg : IsSiteSquareZeroBaseMap B S hS toS toSC f ψ g)
    (a : squareZeroLiftClasses A B S hS toS hA p x hx M) :
    squareZeroLiftClasses C B S hS toSC hC p y hy N :=
  Quotient.lift (fun a' => Quotient.mk _ (siteSquareZeroLiftBaseChange B S hS toS hA toSC hC
      p x y hx hy φ₀ hp specMap hφ₀ g hsq a').1)
    (fun a₁ a₂ hab => eq_of_isSiteSquareZeroLiftBaseChange B S hS toS hA toSC hC
      p x y hx hy φ₀ f ψ
      (isSiteSquareZeroLiftBaseChange_siteSquareZeroLiftBaseChange B S hS toS hA toSC hC
        p x y hx hy φ₀ f ψ hp specMap hφ₀ g hsq hg a₁)
      ((Quotient.sound hab ▸
        isSiteSquareZeroLiftBaseChange_siteSquareZeroLiftBaseChange B S hS toS hA toSC hC
          p x y hx hy φ₀ f ψ hp specMap hφ₀ g hsq hg a₂ :
          IsSiteSquareZeroLiftBaseChange B S hS toS hA toSC hC p x y hx hy φ₀ f ψ
            (Quotient.mk _ a₁) _))) a

include hp hφ₀ hsq in
/-- The transition of Stacks 07YA on lift classes has its defining property. -/
public theorem isSiteSquareZeroLiftBaseChange_siteSquareZeroLiftBaseChangeMap
    (hg : IsSiteSquareZeroBaseMap B S hS toS toSC f ψ g)
    (a : squareZeroLiftClasses A B S hS toS hA p x hx M) :
    IsSiteSquareZeroLiftBaseChange B S hS toS hA toSC hC p x y hx hy φ₀ f ψ a
      (siteSquareZeroLiftBaseChangeMap B S hS toS hA toSC hC p x y hx hy φ₀ f ψ
        hp specMap hφ₀ g hsq hg a) := by
  induction a using Quotient.ind with
  | _ a =>
    exact isSiteSquareZeroLiftBaseChange_siteSquareZeroLiftBaseChange B S hS toS hA
      toSC hC p x y hx hy φ₀ f ψ hp specMap hφ₀ g hsq hg a

/-- The transition of Stacks 07YA on infinitesimal automorphisms across a ring map: a
cartesian arrow exhibiting the trivial lift of `y` over `C[N]` as the pullback of the trivial
lift of `x` over `A[M]` conjugates the automorphism `θ'` into `θ`. -/
public def IsSiteInfinitesimalAutomorphismBaseChange
    (θ : trivialDeformation A B S hS toS hA p x hx hp M ⟶
      trivialDeformation A B S hS toS hA p x hx hp M)
    (θ' : trivialDeformation C B S hS toSC hC p y hy hp N ⟶
      trivialDeformation C B S hS toSC hC p y hy hp N) : Prop :=
  ∃ g : squareZeroOver C B S hS toSC N ⟶ squareZeroOver A B S hS toS M,
    IsSiteSquareZeroBaseMap B S hS toS toSC f ψ g ∧
      ∃ ρ : (trivialDeformation C B S hS toSC hC p y hy hp N).1.right ⟶
          (trivialDeformation A B S hS toS hA p x hx hp M).1.right,
        p.IsStronglyCartesian g ρ ∧
          (trivialDeformation C B S hS toSC hC p y hy hp N).1.hom ≫ ρ =
              φ₀ ≫ (trivialDeformation A B S hS toS hA p x hx hp M).1.hom ∧
            θ'.1.right ≫ ρ = ρ ≫ θ.1.right

end SiteLiftBaseChange

end Deformation.Artin
