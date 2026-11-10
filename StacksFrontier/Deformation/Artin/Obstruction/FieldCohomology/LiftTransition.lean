module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.IntoField
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveTheory
public import StacksFrontier.Deformation.Artin.Obstruction.FieldCohomology.BaseChangeSquare

/-!
# The transitions of Stacks 07YA on lift classes and Stacks 07YT

Uniqueness, construction and bijectivity of the transition of Stacks 07YA on lift classes, and
Stacks 07YT from the Rim–Schlessinger input with only the infinitesimal-automorphism step assumed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace Deformation.Artin

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] CategoryTheory.Limits.CategoricalPullback.π₁

/-! ### Uniqueness of the transitions of Stacks 07YA -/

section BaseChangeUniqueness

open CategoryTheory.Functor

/-- The structure arrow of a lift of `x` along an arrow `f` out of the base of `x` lies over
`f`. -/
public theorem isHomLift_fiberUnder_hom {C : Type*} [Category C] {D : Type*} [Category D]
    (q : D ⥤ C) {U V : C} (f : U ⟶ V) (x : q.Fiber U)
    (t : (Under.post q).Fiber (Under.mk (eqToHom x.2 ≫ f))) :
    q.IsHomLift f t.1.hom := by
  have hy : q.obj t.1.right = V := congrArg Under.right t.2
  apply IsHomLift.of_fac q f t.1.hom x.2 hy
  have hw := Under.w (eqToHom t.2)
  simp only [Under.eqToHom_right] at hw
  change q.map t.1.hom ≫ eqToHom hy = eqToHom x.2 ≫ f at hw
  rw [hw]
  simp

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {c : AffineChart S}

/-- The morphism `Spec C[N] ⟶ Spec A[M]` of a transition of Stacks 07YA is determined by the
ring map and the semilinear map of coefficients it is built from. -/
public theorem eq_of_isSquareZeroBaseMap {P Q : ChartedObject B S hS p c}
    {f : P.ring →+* Q.ring} {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
    {ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj}
    {g g' : Q.squareZeroBase N ⟶ P.squareZeroBase M}
    (hg : IsSquareZeroBaseMap f ψ g) (hg' : IsSquareZeroBaseMap f ψ g') : g = g' := by
  obtain ⟨e, he, hge⟩ := hg
  obtain ⟨e', he', hge'⟩ := hg'
  have hee : e = e' := RingHom.ext fun z => (he z).trans (he' z).symm
  have hgg : (BigFppfOver.toScheme B S hS).map g = (BigFppfOver.toScheme B S hS).map g' := by
    rw [hge, hge', hee]
  exact Over.OverMorphism.ext (ObjectProperty.hom_ext _ hgg)

/-- **The transition of Stacks 07YA on lift classes is single-valued.** Two classes of lifts of
`y` over `C[N]` which are both pullbacks of one class of lifts of `x` over `A[M]` along the
morphism induced by `A ⟶ C` and `M ⟶ N` coincide. -/
public theorem eq_of_isSquareZeroLiftBaseChange {P Q : ChartedObject B S hS p c}
    (h : AffineObject.Hom P.obj Q.obj) (f : P.ring →+* Q.ring)
    {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    {a : P.liftClasses M} {b b' : Q.liftClasses N}
    (hb : IsSquareZeroLiftBaseChange h f ψ a b)
    (hb' : IsSquareZeroLiftBaseChange h f ψ a b') : b = b' := by
  obtain ⟨a₁, b₁, ha₁, hb₁, g₁, hg₁, φ₁, hφ₁, hc₁⟩ := hb
  obtain ⟨a₂, b₂, ha₂, hb₂, g₂, hg₂, φ₂, hφ₂, hc₂⟩ := hb'
  rw [eq_of_isSquareZeroBaseMap hg₂ hg₁] at hφ₂
  obtain ⟨α⟩ := Quotient.exact (ha₁.trans ha₂.symm)
  subst hb₁
  subst hb₂
  have hβh : p.IsHomLift (𝟙 (P.squareZeroBase M)) α.hom.1.right :=
    underPost_isHomLift_right p (𝟙 _) α.hom.1 α.hom.2
  have hβi : p.IsHomLift (𝟙 (P.squareZeroBase M)) α.inv.1.right :=
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
  have hιlift : p.IsHomLift (𝟙 (Q.squareZeroBase N)) ι :=
    Functor.IsCartesian.map_isHomLift p g₁ φ₂ _
  have hι'lift : p.IsHomLift (𝟙 (Q.squareZeroBase N)) ι' :=
    Functor.IsCartesian.map_isHomLift p g₁ φ₁ _
  have hιfac : ι ≫ φ₂ = φ₁ ≫ α.hom.1.right := Functor.IsCartesian.fac p g₁ φ₂ _
  have hι'fac : ι' ≫ φ₁ = φ₂ ≫ α.inv.1.right := Functor.IsCartesian.fac p g₁ φ₁ _
  have hid₁ : p.IsHomLift (𝟙 (Q.squareZeroBase N)) (𝟙 b₁.1.right) :=
    IsHomLift.id (congrArg Under.right b₁.2)
  have hid₂ : p.IsHomLift (𝟙 (Q.squareZeroBase N)) (𝟙 b₂.1.right) :=
    IsHomLift.id (congrArg Under.right b₂.2)
  have hsa₁ : p.IsHomLift
      (squareZeroArrow Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem N) b₁.1.hom :=
    isHomLift_fiberUnder_hom p _ Q.obj.obj b₁
  have hsa₂ : p.IsHomLift
      (squareZeroArrow Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem N) b₂.1.hom :=
    isHomLift_fiberUnder_hom p _ Q.obj.obj b₂
  have hιι' : ι ≫ ι' = 𝟙 b₁.1.right := by
    refine Functor.IsCartesian.ext p g₁ φ₁ _ _ ?_
    rw [Category.id_comp, Category.assoc, hι'fac, ← Category.assoc, hιfac, Category.assoc,
      hβhi, Category.comp_id]
  have hι'ι : ι' ≫ ι = 𝟙 b₂.1.right := by
    refine Functor.IsCartesian.ext p g₁ φ₂ _ _ ?_
    rw [Category.id_comp, Category.assoc, hιfac, ← Category.assoc, hι'fac, Category.assoc,
      hβih, Category.comp_id]
  have hunder : b₁.1.hom ≫ ι = b₂.1.hom := by
    refine Functor.IsStronglyCartesian.ext p g₁ φ₂
      (squareZeroArrow Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem N) ?_
    rw [Category.assoc, hιfac, ← Category.assoc, hc₁, Category.assoc, hwh, hc₂]
  refine Quotient.sound ⟨Functor.Fiber.isoMk
    (Under.isoMk ⟨ι, ι', hιι', hι'ι⟩ hunder) ?_⟩
  refine IsHomLift.of_fac' (Under.post p) (𝟙 _) _ b₁.2 b₂.2 ?_
  apply Under.UnderMorphism.ext
  simp only [Under.comp_right, Under.eqToHom_right, Under.id_right]
  exact IsHomLift.fac' p (𝟙 (Q.squareZeroBase N)) ι

/-- **The transition of Stacks 07YA on lift classes is pinned down by its defining property.**
If one map on tangent spaces realizing the transition is a bijection, then every map realizing
it is that same bijection. -/
public theorem bijective_of_bijective_squareZeroLiftBaseChange
    (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
    {P Q : ChartedObject B S hS p c} (h : AffineObject.Hom P.obj Q.obj)
    (f : P.ring →+* Q.ring)
    {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    {τ₀ τ : ((P.tangent hp hRS).functor.obj M : Type (max (u + 1) v w)) →
      ((Q.tangent hp hRS).functor.obj N : Type (max (u + 1) v w))}
    (hτ₀ : ∀ a, IsSquareZeroLiftBaseChange h f ψ
      ((P.tangent hp hRS).liftEquiv M a) ((Q.tangent hp hRS).liftEquiv N (τ₀ a)))
    (hbij : Function.Bijective τ₀)
    (hτ : ∀ a, IsSquareZeroLiftBaseChange h f ψ
      ((P.tangent hp hRS).liftEquiv M a) ((Q.tangent hp hRS).liftEquiv N (τ a))) :
    Function.Bijective τ := by
  have heq : τ = τ₀ := funext fun a =>
    ((Q.tangent hp hRS).liftEquiv N).injective
      (eq_of_isSquareZeroLiftBaseChange h f ψ (hτ a) (hτ₀ a))
  exact heq ▸ hbij

end BaseChangeUniqueness

/-! ### The canonical transition of Stacks 07YA on lift classes -/

section CanonicalLiftTransition

open CategoryTheory.Functor

/-- The composite of a lift of `f` and a lift of `g` lifts `f ≫ g`, with the two lifts given as
explicit arguments rather than found by instance search. -/
public theorem isHomLift_comp {C : Type*} [Category C] {D : Type*} [Category D] (q : D ⥤ C)
    {R T W : C} {a b d : D} {f : R ⟶ T} {g : T ⟶ W} {φ : a ⟶ b} {χ : b ⟶ d}
    (hφ : q.IsHomLift f φ) (hχ : q.IsHomLift g χ) : q.IsHomLift (f ≫ g) (φ ≫ χ) :=
  have := hφ
  have := hχ
  inferInstance

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {c : AffineChart S}
  (hp : p.IsFiberedInGroupoids) {P Q : ChartedObject B S hS p c}
  (h : AffineObject.Hom P.obj Q.obj) (f : P.ring →+* Q.ring)
  {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
  (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
  (g : Q.squareZeroBase N ⟶ P.squareZeroBase M)
  (hsq : h.alg.specMap ≫
      squareZeroArrow P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem M =
    squareZeroArrow Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem N ≫ g)

include hp hsq in
/-- The pullback of a lift of `x` over `Spec A[M]` along `Spec C[N] ⟶ Spec A[M]`, as a lift of
`y` over `Spec C[N]`: the chosen strongly cartesian pullback, whose structure arrow out of `y`
is supplied by the universal property applied to `y ⟶ x ⟶ x'`. -/
public def squareZeroLiftBaseChange (a : P.liftOver M) :
    { b : Q.liftOver N // ∃ ρ : b.1.right ⟶ a.1.right,
      p.IsStronglyCartesian g ρ ∧ b.1.hom ≫ ρ = h.objMap ≫ a.1.hom } := by
  letI : p.IsFibered := hp.isFibered
  have hha : p.IsHomLift h.alg.specMap h.objMap := h.objMap_isHomLift
  have hah : p.IsHomLift
      (squareZeroArrow P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem M) a.1.hom :=
    isHomLift_fiberUnder_hom p _ P.obj.obj a
  have hcomp : p.IsHomLift
      (squareZeroArrow Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem N ≫ g)
      (h.objMap ≫ a.1.hom) := by
    rw [← hsq]
    exact isHomLift_comp p hha hah
  have hfac : squareZeroArrow Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem N ≫ g =
      squareZeroArrow Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem N ≫ g := rfl
  let xa : p.Fiber (P.squareZeroBase M) := ⟨a.1.right, congrArg Under.right a.2⟩
  let ρ := (Functor.chosenPullbacks p).map g xa
  have hρ : p.IsStronglyCartesian g ρ := (Functor.chosenPullbacks p).isStronglyCartesian g xa
  have hhomlift : p.IsHomLift
      (squareZeroArrow Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem N)
      (Functor.IsStronglyCartesian.map p g ρ hfac (h.objMap ≫ a.1.hom)) :=
    Functor.IsStronglyCartesian.map_isHomLift p g ρ hfac _
  refine ⟨⟨Under.mk (Functor.IsStronglyCartesian.map p g ρ hfac (h.objMap ≫ a.1.hom)),
    StructuredArrow.obj_ext _ _ ((Functor.chosenPullbacks p).obj g xa).2 ?_⟩,
    ρ, hρ, Functor.IsStronglyCartesian.fac p g ρ hfac _⟩
  change p.map (Functor.IsStronglyCartesian.map p g ρ hfac (h.objMap ≫ a.1.hom)) ≫
      eqToHom ((Functor.chosenPullbacks p).obj g xa).2 =
    eqToHom Q.obj.obj.2 ≫ squareZeroArrow Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem N
  rw [IsHomLift.fac' p
    (squareZeroArrow Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem N) _,
    Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  rfl

include hp hsq in
/-- The pullback of a lift along `Spec C[N] ⟶ Spec A[M]` realizes the transition of
Stacks 07YA on the classes of the two lifts. -/
public theorem isSquareZeroLiftBaseChange_squareZeroLiftBaseChange
    (hg : IsSquareZeroBaseMap f ψ g) (a : P.liftOver M) :
    IsSquareZeroLiftBaseChange h f ψ (Quotient.mk _ a)
      (Quotient.mk _ (squareZeroLiftBaseChange hp h g hsq a).1) :=
  ⟨a, (squareZeroLiftBaseChange hp h g hsq a).1, rfl, rfl, g, hg,
    (squareZeroLiftBaseChange hp h g hsq a).2.choose,
    (squareZeroLiftBaseChange hp h g hsq a).2.choose_spec.1,
    (squareZeroLiftBaseChange hp h g hsq a).2.choose_spec.2⟩

include hp hsq in
/-- **The transition of Stacks 07YA on lift classes.** Pullback along the morphism
`Spec C[N] ⟶ Spec A[M]` induced by a ring map `A ⟶ C` and an `A`-semilinear map `M ⟶ N` of
coefficients, on isomorphism classes of lifts. -/
public def squareZeroLiftBaseChangeMap (hg : IsSquareZeroBaseMap f ψ g)
    (a : P.liftClasses M) : Q.liftClasses N :=
  Quotient.lift (fun a' => Quotient.mk _ (squareZeroLiftBaseChange hp h g hsq a').1)
    (fun a₁ a₂ hab => eq_of_isSquareZeroLiftBaseChange h f ψ
      (isSquareZeroLiftBaseChange_squareZeroLiftBaseChange hp h f ψ g hsq hg a₁)
      ((Quotient.sound hab ▸
        isSquareZeroLiftBaseChange_squareZeroLiftBaseChange hp h f ψ g hsq hg a₂ :
          IsSquareZeroLiftBaseChange h f ψ (Quotient.mk _ a₁) _))) a

include hp hsq in
/-- The transition of Stacks 07YA on lift classes has its defining property. -/
public theorem isSquareZeroLiftBaseChange_squareZeroLiftBaseChangeMap
    (hg : IsSquareZeroBaseMap f ψ g) (a : P.liftClasses M) :
    IsSquareZeroLiftBaseChange h f ψ a (squareZeroLiftBaseChangeMap hp h f ψ g hsq hg a) := by
  induction a using Quotient.ind with
  | _ a => exact isSquareZeroLiftBaseChange_squareZeroLiftBaseChange hp h f ψ g hsq hg a

include hp hsq in
/-- **The tangent hypothesis of Stacks 07YT reduces to one bijectivity statement.** If the
transition of Stacks 07YA on lift classes is bijective, then every map of tangent spaces
realizing it is bijective. -/
public theorem bijective_of_bijective_squareZeroLiftBaseChangeMap
    (hRS : SatisfiesRSStar B S hS p hp) (hg : IsSquareZeroBaseMap f ψ g)
    (hbij : Function.Bijective (squareZeroLiftBaseChangeMap hp h f ψ g hsq hg))
    {τ : ((P.tangent hp hRS).functor.obj M : Type (max (u + 1) v w)) →
      ((Q.tangent hp hRS).functor.obj N : Type (max (u + 1) v w))}
    (hτ : ∀ a, IsSquareZeroLiftBaseChange h f ψ
      ((P.tangent hp hRS).liftEquiv M a) ((Q.tangent hp hRS).liftEquiv N (τ a))) :
    Function.Bijective τ := by
  refine bijective_of_bijective_squareZeroLiftBaseChange hp hRS h f ψ
    (τ₀ := fun a => ((Q.tangent hp hRS).liftEquiv N).symm
      (squareZeroLiftBaseChangeMap hp h f ψ g hsq hg ((P.tangent hp hRS).liftEquiv M a)))
    (fun a => ?_) (((Q.tangent hp hRS).liftEquiv N).symm.bijective.comp
      (hbij.comp ((P.tangent hp hRS).liftEquiv M).bijective)) hτ
  rw [Equiv.apply_symm_apply]
  exact isSquareZeroLiftBaseChange_squareZeroLiftBaseChangeMap hp h f ψ g hsq hg _

end CanonicalLiftTransition

/-! ### The square-zero base map of a morphism of charted objects -/

section ChartedBaseMap

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {c : AffineChart S}
  {P Q : ChartedObject B S hS p c} (h : AffineObject.Hom P.obj Q.obj)
  (f : P.ring →+* Q.ring) (halg : f = h.alg.ringMap)

include halg in
/-- The structure morphism of the target of a morphism of charted objects is the structure
morphism of the source precomposed with the spectrum of the ring map. -/
public theorem specMap_toScheme_comp :
    Spec.map (CommRingCat.ofHom f) ≫ P.obj.alg.toScheme = Q.obj.alg.toScheme := by
  have h1 := congrArg (fun t => B.inclusion.map t) (Over.w h.alg.specMap)
  simp only [Functor.map_comp] at h1
  rw [halg, ← h.alg.specMap_spec]
  exact h1

include halg in
/-- The morphism of spectra carried by a morphism of charted objects is the morphism of objects
over `S` determined by the ring map. -/
public theorem specMap_eq_algebraOverMap :
    h.alg.specMap = algebraOverMapOfRingHom f B S hS P.obj.alg.toScheme Q.obj.alg.toScheme
      P.obj.alg.mem Q.obj.alg.mem (specMap_toScheme_comp h f halg) := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change B.inclusion.map h.alg.specMap.left = Spec.map (CommRingCat.ofHom f)
  rw [h.alg.specMap_spec, halg]

include halg in
/-- The two square-zero immersions, the morphism of charted objects and the induced morphism of
trivial square-zero extensions form a commutative square. -/
public theorem specMap_comp_squareZeroArrow (M : SiteModule P.ring B) (N : SiteModule Q.ring B)
    (ψ : (M.obj : Type u) →+ (N.obj : Type u))
    (hψ : ∀ (a : P.ring) (m : M.obj), ψ (a • m) = f a • ψ m) :
    h.alg.specMap ≫ squareZeroArrow P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem M =
      squareZeroArrow Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem N ≫
        squareZeroOverBaseMap f B S hS P.obj.alg.toScheme Q.obj.alg.toScheme
          (specMap_toScheme_comp h f halg) M N ψ hψ := by
  rw [specMap_eq_algebraOverMap h f halg]
  exact algebraOverMap_comp_squareZeroArrow f B S hS P.obj.alg.toScheme Q.obj.alg.toScheme
    P.obj.alg.mem Q.obj.alg.mem (specMap_toScheme_comp h f halg) M N ψ hψ

include halg in
/-- The morphism `Spec C[N] ⟶ Spec A[M]` induced by a ring map and a semilinear map of
coefficients is a square-zero base map of Stacks 07YA. -/
public theorem isSquareZeroBaseMap_squareZeroOverBaseMap {M : SiteModule P.ring B}
    {N : SiteModule Q.ring B} (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) :
    IsSquareZeroBaseMap f ψ
      (squareZeroOverBaseMap f B S hS P.obj.alg.toScheme Q.obj.alg.toScheme
        (specMap_toScheme_comp h f halg) M N (restrictScalarsAddHom f ψ)
        (restrictScalarsAddHom_smul f ψ)) :=
  ⟨squareZeroRingBaseMap f (restrictScalarsAddHom f ψ) (restrictScalarsAddHom_smul f ψ),
    fun _ => rfl, rfl⟩

end ChartedBaseMap

/-! ### Stacks 07YT from one Rim–Schlessinger bijection on lift classes -/

section FieldBaseChangeOfBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {c : AffineChart S}

/-- **Stacks 07YT with the Rim–Schlessinger step on lift classes reduced to one bijectivity
statement.** The tangent hypothesis of
`Deformation.Artin.bijective_homologyFunctor_map_naiveObstructionFieldBaseChangeMap` asks every
map realizing the transition of Stacks 07YA to be bijective; since the transition is realized
by the explicit pullback map on lift classes and is single-valued, it is enough that that one
map be bijective. -/
public theorem bijective_homologyFunctor_map_naiveObstructionFieldBaseChangeMap_of_bijective
    {hp : p.IsFiberedInGroupoids} {hRS : SatisfiesRSStar B S hS p hp}
    (nob : NaiveObstructionTheory B S hS p hp hRS c)
    (P Q : ChartedObject B S hS p c) (h : AffineObject.Hom P.obj Q.obj)
    [Algebra P.ring Q.ring] [IsScalarTower c.ring P.ring Q.ring]
    (halg : algebraMap P.ring Q.ring = h.alg.ringMap)
    {k : Type u} [Field k] (g : Q.ring →+* k)
    (hM : IsSiteModule P.ring B
      ((ModuleCat.restrictScalars (g.comp (algebraMap P.ring Q.ring))).obj
        (ModuleCat.of k (ULift.{u} k))))
    (hN : IsSiteModule Q.ring B
      ((ModuleCat.restrictScalars g).obj (ModuleCat.of k (ULift.{u} k))))
    (gb : Q.squareZeroBase (fieldSiteModule Q.ring B g hN) ⟶
      P.squareZeroBase (fieldSiteModule P.ring B (g.comp (algebraMap P.ring Q.ring)) hM))
    (hgb : IsSquareZeroBaseMap (algebraMap P.ring Q.ring)
      (fieldSiteModuleComparison (algebraMap P.ring Q.ring) B g hM hN) gb)
    (hsq : h.alg.specMap ≫ squareZeroArrow P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem
          (fieldSiteModule P.ring B (g.comp (algebraMap P.ring Q.ring)) hM) =
        squareZeroArrow Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem
          (fieldSiteModule Q.ring B g hN) ≫ gb)
    (hbij : Function.Bijective (squareZeroLiftBaseChangeMap hp h (algebraMap P.ring Q.ring)
      (fieldSiteModuleComparison (algebraMap P.ring Q.ring) B g hM hN) gb hsq hgb))
    (hinf : ∀ σ : ((P.infAut hp hRS).functor.obj
          (fieldSiteModule P.ring B (g.comp (algebraMap P.ring Q.ring)) hM) : Type w) →
        ((Q.infAut hp hRS).functor.obj (fieldSiteModule Q.ring B g hN) : Type w),
      (∀ θ, IsInfinitesimalAutomorphismBaseChange hp h (algebraMap P.ring Q.ring)
        (fieldSiteModuleComparison (algebraMap P.ring Q.ring) B g hM hN)
        ((P.infAut hp hRS).autEquiv _ θ) ((Q.infAut hp hRS).autEquiv _ (σ θ))) →
      Function.Bijective σ) :
    Function.Bijective ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
        (naiveObstructionFieldBaseChangeMap nob P Q h halg g)).hom ∧
      Function.Bijective ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 1).map
        (naiveObstructionFieldBaseChangeMap nob P Q h halg g)).hom :=
  bijective_homologyFunctor_map_naiveObstructionFieldBaseChangeMap nob P Q h halg g hM hN
    (fun _ hτ => bijective_of_bijective_squareZeroLiftBaseChangeMap hp h
      (algebraMap P.ring Q.ring)
      (fieldSiteModuleComparison (algebraMap P.ring Q.ring) B g hM hN) gb hsq hRS hgb hbij hτ)
    hinf

end FieldBaseChangeOfBijective

/-! ### Changing the base point of an iso-fibre -/

section IsoFiberCongrBase

open CategoryTheory.Functor

variable {C₁ C₂ : Type*} [Category C₁] [Category C₂] (F : C₁ ⥤ C₂) {w w' : C₂} (e : w ≅ w')

/-- Composing the structure arrow with an isomorphism of base points identifies the iso-fibres
of a functor over the two points. -/
public def isoFiberCongrBase : IsoFiber F w ⥤ IsoFiber F w' where
  obj t :=
    ⟨CostructuredArrow.mk (t.obj.hom ≫ e.hom),
      have : IsIso t.obj.hom := t.property
      show IsIso (t.obj.hom ≫ e.hom) from inferInstance⟩
  map {s t} m :=
    ObjectProperty.homMk (CostructuredArrow.homMk m.hom.left (by
      change F.map m.hom.left ≫ t.obj.hom ≫ e.hom = s.obj.hom ≫ e.hom
      rw [← Category.assoc, CostructuredArrow.w m.hom]))
  map_id _ := ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ rfl)
  map_comp _ _ := ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ rfl)

/-- The change-of-base-point comparison is faithful. -/
public theorem isoFiberCongrBase_faithful : (isoFiberCongrBase F e).Faithful where
  map_injective {_ _} _ _ hmn :=
    ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (congrArg (fun z => z.hom.left) hmn))

/-- The change-of-base-point comparison is full. -/
public theorem isoFiberCongrBase_full : (isoFiberCongrBase F e).Full where
  map_surjective {s t} ν := by
    have hν : F.map ν.hom.left ≫ t.obj.hom ≫ e.hom = s.obj.hom ≫ e.hom :=
      CostructuredArrow.w ν.hom
    refine ⟨ObjectProperty.homMk (CostructuredArrow.homMk ν.hom.left
      ((cancel_mono e.hom).mp ?_)), ?_⟩
    · rwa [Category.assoc]
    · exact ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ rfl)

/-- The change-of-base-point comparison hits every object: compose the structure arrow with the
inverse isomorphism. -/
public theorem isoFiberCongrBase_surjective :
    Function.Surjective (isoFiberCongrBase F e).obj := by
  intro u
  have hu : IsIso u.obj.hom := u.property
  refine ⟨⟨CostructuredArrow.mk (u.obj.hom ≫ e.inv),
    show IsIso (u.obj.hom ≫ e.inv) from inferInstance⟩, ?_⟩
  refine IsoFiber.ext rfl (heq_of_eq ?_)
  change (u.obj.hom ≫ e.inv) ≫ e.hom = u.obj.hom
  rw [Category.assoc, e.inv_hom_id, Category.comp_id]

/-- Changing the base point of an iso-fibre along an isomorphism is a bijection on isomorphism
classes. -/
public theorem bijective_isoClassMap_isoFiberCongrBase :
    Function.Bijective (isoClassMap (isoFiberCongrBase F e)) :=
  have := isoFiberCongrBase_full F e
  have := isoFiberCongrBase_faithful F e
  isoClassMap_bijective _ (isoFiberCongrBase_surjective F e)

end IsoFiberCongrBase

/-! ### The (RS*) comparison on lifts is pullback along the other leg -/

section SquareLiftFac

open CategoryTheory.Limits CategoryTheory.Functor

/- `Fiber.fiberInclusion` and `ChoiceOfPullbacks.pullbackFunctor` are plain definitions, so a
goal mentioning the image of a chosen pullback in the ambient category is not type-correct at
the `implicit` transparency level, and `rw`/`simp` refuse it. -/
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor

variable {C : Type*} [Category C] {D : Type*} [Category D] (p : D ⥤ C)
  (c : p.ChoiceOfPullbacks) {U V W Z : C} (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z)
  (h : f ≫ i = g ≫ j)

/-- The structural isomorphism of an object of an iso-fibre factors the chosen pullback arrow
through the arrow attached to that object. -/
private theorem fiberInclusion_hom_comp_isoFiberArrow {U' V' : C} (f' : U' ⟶ V')
    (y : p.Fiber U') (u : IsoFiber (c.pullbackFunctor f') y) :
    Fiber.fiberInclusion.map u.obj.hom ≫ isoFiberArrow p c f' y u = c.map f' u.obj.left := by
  have hu : IsIso u.obj.hom := u.property
  change Fiber.fiberInclusion.map u.obj.hom ≫
    Fiber.fiberInclusion.map (inv u.obj.hom) ≫ c.map f' u.obj.left = _
  rw [← Category.assoc, ← Fiber.fiberInclusion.map_comp, IsIso.hom_inv_id,
    Fiber.fiberInclusion.map_id, Category.id_comp]

/-- The comparison of the chosen pullback along a composite with the iterated chosen pullback,
read in the inverse direction. -/
private theorem fiberInclusion_objCompIso_inv_fac {W' V' U' : C} (g' : W' ⟶ V') (f' : V' ⟶ U')
    (y : p.Fiber U') :
    Fiber.fiberInclusion.map (c.objCompIso g' f' y).inv ≫ c.map (g' ≫ f') y =
      c.map g' (c.obj f' y) ≫ c.map f' y := by
  rw [← c.objCompIso_hom_fac g' f' y, ← Category.assoc, ← Fiber.fiberInclusion.map_comp,
    Iso.inv_hom_id, Fiber.fiberInclusion.map_id, Category.id_comp]

/-- The chosen pullbacks along two equal arrows of the base are compared by the induced
transport. -/
private theorem fiberInclusion_eqToIso_fac {m n : U ⟶ Z} (hmn : m = n) (y : p.Fiber Z) :
    Fiber.fiberInclusion.map ((eqToIso (congrArg c.pullbackFunctor hmn)).hom.app y) ≫
      c.map n y = c.map m y := by
  subst hmn
  change 𝟙 _ ≫ c.map m y = c.map m y
  exact Category.id_comp _

/-- The comparison isomorphism of a commutative square identifies the two iterated chosen
pullbacks of an object over the fourth corner, compatibly with the two cartesian arrows. -/
private theorem fiberInclusion_comparison_fac (y : p.Fiber Z)
    (κ : (c.pullbackFunctor f).obj (c.obj i y) ≅ (c.pullbackFunctor g).obj (c.obj j y))
    (hκ : κ.hom = (c.objCompIso f i y).inv ≫
      (eqToIso (congrArg c.pullbackFunctor h)).hom.app y ≫ (c.objCompIso g j y).hom) :
    Fiber.fiberInclusion.map κ.hom ≫ c.map g (c.obj j y) ≫ c.map j y =
      c.map f (c.obj i y) ≫ c.map i y := by
  rw [hκ, Fiber.fiberInclusion.map_comp, Fiber.fiberInclusion.map_comp, Category.assoc,
    Category.assoc, c.objCompIso_hom_fac, fiberInclusion_eqToIso_fac p c h y,
    fiberInclusion_objCompIso_inv_fac p c f i y]

/-- Cancelling an isomorphism on the left of a composite: the rearrangement behind the
identification of the (RS*) comparison with pullback along the other leg. -/
private theorem comp_eq_of_fac {E : Type*} [Category E] {a₁ a₂ a₃ a₄ a₅ a₆ a₇ : E}
    (σ : a₁ ⟶ a₂) [IsIso σ] {α : a₂ ⟶ a₃} {M : a₁ ⟶ a₃} {N : a₃ ⟶ a₄} {ρ : a₂ ⟶ a₅}
    {β : a₅ ⟶ a₄} {κi : a₁ ⟶ a₆} {κh : a₆ ⟶ a₁} {μ : a₆ ⟶ a₂} {ν : a₆ ⟶ a₇}
    {θ : a₇ ⟶ a₅} {ξ : a₇ ⟶ a₄}
    (hα : σ ≫ α = M) (hσ : σ = κi ≫ μ) (hμ : μ ≫ ρ = ν ≫ θ) (hθ : θ ≫ β = ξ)
    (hκ : κh ≫ M ≫ N = ν ≫ ξ) (hκi : κi ≫ κh = 𝟙 a₁) :
    α ≫ N = ρ ≫ β := by
  refine (cancel_epi σ).mp ?_
  calc σ ≫ α ≫ N = (σ ≫ α) ≫ N := (Category.assoc _ _ _).symm
    _ = M ≫ N := by rw [hα]
    _ = (κi ≫ κh) ≫ M ≫ N := by rw [hκi, Category.id_comp]
    _ = κi ≫ κh ≫ M ≫ N := Category.assoc _ _ _
    _ = κi ≫ ν ≫ ξ := by rw [hκ]
    _ = κi ≫ ν ≫ θ ≫ β := by rw [hθ]
    _ = κi ≫ (ν ≫ θ) ≫ β := by rw [Category.assoc]
    _ = κi ≫ (μ ≫ ρ) ≫ β := by rw [hμ]
    _ = (κi ≫ μ) ≫ ρ ≫ β := by rw [Category.assoc, Category.assoc]
    _ = σ ≫ ρ ≫ β := by rw [hσ]

/-- The structural isomorphism of the lift produced by the (RS*) comparison: the comparison
isomorphism of the square, followed by the pullback along the first leg of the structural
isomorphism of the given lift. -/
public theorem squareLiftEquivalence_functor_obj_hom
    (hE : (fiberSquareComparison p c f g i j h).IsEquivalence) (x : p.Fiber V)
    (t : IsoFiber (c.pullbackFunctor i) x) :
    ((squareLiftEquivalence p c f g i j h hE x).functor.obj t).obj.hom =
      ((fiberSquareComparison p c f g i j h).obj t.obj.left).iso.inv ≫
        c.homMap f t.obj.hom := by
  have hraw : ((squareLiftEquivalence p c f g i j h hE x).functor.obj t).obj.hom =
      ((fiberSquareComparison p c f g i j h).obj t.obj.left).iso.inv ≫
        c.homMap f ((𝟙 _ ≫ 𝟙 _) ≫ t.obj.hom ≫ 𝟙 x) := rfl
  refine hraw.trans ?_
  congr 1
  refine congrArg (c.homMap f) ?_
  simp only [Category.id_comp]
  exact Category.comp_id _

/-- **The (RS*) comparison on lifts is pullback along the other leg.** The arrow of the lift of
`x|_U` over `W` produced by the comparison, followed by the chosen pullback along `j`, is the
restriction arrow of `x` to `U` followed by the arrow of the given lift of `x` over `Z`. -/
public theorem isoFiberArrow_squareLiftEquivalence_fac
    (hE : (fiberSquareComparison p c f g i j h).IsEquivalence) (x : p.Fiber V)
    (t : IsoFiber (c.pullbackFunctor i) x) :
    isoFiberArrow p c g ((c.pullbackFunctor f).obj x)
          ((squareLiftEquivalence p c f g i j h hE x).functor.obj t) ≫
        c.map j t.obj.left =
      c.map f x ≫ isoFiberArrow p c i x t := by
  have hsiso : IsIso ((squareLiftEquivalence p c f g i j h hE x).functor.obj t).obj.hom :=
    ((squareLiftEquivalence p c f g i j h hE x).functor.obj t).property
  exact comp_eq_of_fac (Fiber.fiberInclusion.map
      ((squareLiftEquivalence p c f g i j h hE x).functor.obj t).obj.hom)
    (fiberInclusion_hom_comp_isoFiberArrow p c g ((c.pullbackFunctor f).obj x)
      ((squareLiftEquivalence p c f g i j h hE x).functor.obj t))
    ((congrArg (fun z => Fiber.fiberInclusion.map z)
      (squareLiftEquivalence_functor_obj_hom p c f g i j h hE x t)).trans
        (Fiber.fiberInclusion.map_comp _ _))
    (c.homMap_fac f t.obj.hom) (fiberInclusion_hom_comp_isoFiberArrow p c i x t)
    (fiberInclusion_comparison_fac p c f g i j h t.obj.left
      ((fiberSquareComparison p c f g i j h).obj t.obj.left).iso rfl)
    (((Fiber.fiberInclusion.map_comp _ _).symm.trans
      (congrArg (fun z => Fiber.fiberInclusion.map z)
        ((fiberSquareComparison p c f g i j h).obj t.obj.left).iso.inv_hom_id)).trans
          (Fiber.fiberInclusion.map_id _))

/-- Cancelling an isomorphism which factors through a second object: the rearrangement behind
reading the (RS*) comparison at an arbitrary cartesian lift. -/
private theorem comp_eq_of_fac' {E : Type*} [Category E] {b₁ b₂ b₃ b₄ b₅ b₆ : E}
    (σ' : b₁ ⟶ b₃) [IsIso σ'] {σ : b₁ ⟶ b₂} {ε : b₂ ⟶ b₃} {αs : b₂ ⟶ b₄} {αu : b₃ ⟶ b₄}
    {M : b₁ ⟶ b₄} {N : b₄ ⟶ b₅} {ρ : b₂ ⟶ b₆} {δ : b₃ ⟶ b₆} {β : b₆ ⟶ b₅}
    (hσ' : σ' = σ ≫ ε) (hs : σ ≫ αs = M) (hu : σ' ≫ αu = M) (hfac : αs ≫ N = ρ ≫ β)
    (hε : ε ≫ δ = ρ) : αu ≫ N = δ ≫ β := by
  refine (cancel_epi σ').mp ?_
  calc σ' ≫ αu ≫ N = (σ' ≫ αu) ≫ N := (Category.assoc _ _ _).symm
    _ = M ≫ N := by rw [hu]
    _ = (σ ≫ αs) ≫ N := by rw [hs]
    _ = σ ≫ αs ≫ N := Category.assoc _ _ _
    _ = σ ≫ ρ ≫ β := by rw [hfac]
    _ = σ ≫ (ε ≫ δ) ≫ β := by rw [hε]
    _ = (σ ≫ ε) ≫ δ ≫ β := by rw [Category.assoc, Category.assoc]
    _ = σ' ≫ δ ≫ β := by rw [hσ']

/-- **The (RS*) comparison on lifts, read at an arbitrary cartesian lift of the base point.**
If `η : y ⟶ x` is a cartesian arrow over the first leg, the lift of `y` over `W` carried by the
comparison, followed by the chosen pullback along the other leg, is `η` followed by the arrow of
the given lift of `x` over `Z`. -/
public theorem isoFiberArrow_isoFiberCongrBase_squareLiftEquivalence_fac
    (hE : (fiberSquareComparison p c f g i j h).IsEquivalence) (x : p.Fiber V) (y : p.Fiber U)
    (η : y.1 ⟶ x.1) (hη : p.IsCartesian f η) (t : IsoFiber (c.pullbackFunctor i) x) :
    isoFiberArrow p c g y
          ((isoFiberCongrBase (c.pullbackFunctor g)
              (fiberIsoOfCartesian f (c.map f x) η inferInstance hη)).obj
            ((squareLiftEquivalence p c f g i j h hE x).functor.obj t)) ≫
        c.map j t.obj.left =
      η ≫ isoFiberArrow p c i x t := by
  have hsiso : IsIso ((squareLiftEquivalence p c f g i j h hE x).functor.obj t).obj.hom :=
    ((squareLiftEquivalence p c f g i j h hE x).functor.obj t).property
  have huiso : IsIso ((isoFiberCongrBase (c.pullbackFunctor g)
      (fiberIsoOfCartesian f (c.map f x) η inferInstance hη)).obj
        ((squareLiftEquivalence p c f g i j h hE x).functor.obj t)).obj.hom :=
    ((isoFiberCongrBase (c.pullbackFunctor g)
      (fiberIsoOfCartesian f (c.map f x) η inferInstance hη)).obj
        ((squareLiftEquivalence p c f g i j h hE x).functor.obj t)).property
  exact comp_eq_of_fac' (Fiber.fiberInclusion.map ((isoFiberCongrBase (c.pullbackFunctor g)
      (fiberIsoOfCartesian f (c.map f x) η inferInstance hη)).obj
        ((squareLiftEquivalence p c f g i j h hE x).functor.obj t)).obj.hom)
    (Fiber.fiberInclusion.map_comp
      ((squareLiftEquivalence p c f g i j h hE x).functor.obj t).obj.hom
      (fiberIsoOfCartesian f (c.map f x) η inferInstance hη).hom)
    (fiberInclusion_hom_comp_isoFiberArrow p c g ((c.pullbackFunctor f).obj x)
      ((squareLiftEquivalence p c f g i j h hE x).functor.obj t))
    (fiberInclusion_hom_comp_isoFiberArrow p c g y
      ((isoFiberCongrBase (c.pullbackFunctor g)
        (fiberIsoOfCartesian f (c.map f x) η inferInstance hη)).obj
          ((squareLiftEquivalence p c f g i j h hE x).functor.obj t)))
    (isoFiberArrow_squareLiftEquivalence_fac p c f g i j h hE x t)
    (fiberIsoOfCartesian_hom_fac f (c.map f x) η inferInstance hη)

end SquareLiftFac

/-! ### Bijectivity of the transition of Stacks 07YA at a semilinear bijection -/

section BaseChangeBijective

open CategoryTheory.Functor

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {c : AffineChart S}

/-- A bijection with the defining property of the transition of Stacks 07YA on lift classes is
that transition, which is therefore bijective. -/
private theorem bijective_of_isSquareZeroLiftBaseChange (hp : p.IsFiberedInGroupoids)
    {P Q : ChartedObject B S hS p c} (h : AffineObject.Hom P.obj Q.obj)
    (f : P.ring →+* Q.ring) {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (g : Q.squareZeroBase N ⟶ P.squareZeroBase M)
    (hsq : h.alg.specMap ≫ squareZeroArrow P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem M =
      squareZeroArrow Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem N ≫ g)
    (hg : IsSquareZeroBaseMap f ψ g) {T : Type*} (e : T ≃ P.liftClasses M)
    (β : T ≃ Q.liftClasses N)
    (hβ : ∀ u, IsSquareZeroLiftBaseChange h f ψ (e u) (β u)) :
    Function.Bijective (squareZeroLiftBaseChangeMap hp h f ψ g hsq hg) := by
  have heq : squareZeroLiftBaseChangeMap hp h f ψ g hsq hg = fun a => β (e.symm a) := by
    funext a
    refine eq_of_isSquareZeroLiftBaseChange h f ψ
      (isSquareZeroLiftBaseChange_squareZeroLiftBaseChangeMap hp h f ψ g hsq hg a) ?_
    have h2 := hβ (e.symm a)
    rwa [Equiv.apply_symm_apply] at h2
  rw [heq]
  exact β.bijective.comp e.symm.bijective

/-- Bijectivity of the transition of Stacks 07YA on lift classes, from the (RS*) equivalence at
the square `A[M] = A ×_C C[N]` together with a cartesian arrow `y ⟶ x` over `Spec C ⟶ Spec A`. -/
private theorem bijective_squareZeroLiftBaseChangeMap_of_isEquivalence
    (hp : p.IsFiberedInGroupoids)
    {P Q : ChartedObject B S hS p c} (h : AffineObject.Hom P.obj Q.obj)
    (f : P.ring →+* Q.ring) {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (g : Q.squareZeroBase N ⟶ P.squareZeroBase M)
    (hsq : h.alg.specMap ≫ squareZeroArrow P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem M =
      squareZeroArrow Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem N ≫ g)
    (hg : IsSquareZeroBaseMap f ψ g)
    (fa : algebraOver Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem ⟶
      algebraOver P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem)
    (hfa : p.IsCartesian fa h.objMap)
    (hcomm : fa ≫ squareZeroArrow P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem M =
      squareZeroArrow Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem N ≫ g)
    (hE : letI : p.IsFibered := hp.isFibered
      (fiberSquareComparison p (Functor.chosenPullbacks p) fa
        (squareZeroArrow Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem N)
        (squareZeroArrow P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem M) g
        hcomm).IsEquivalence) :
    Function.Bijective (squareZeroLiftBaseChangeMap hp h f ψ g hsq hg) := by
  let : p.IsFibered := hp.isFibered
  have hcart : p.IsStronglyCartesian fa
      ((Functor.chosenPullbacks p).map fa ⟨P.point, P.obj.obj.2⟩) :=
    (Functor.chosenPullbacks p).isStronglyCartesian fa _
  refine bijective_of_isSquareZeroLiftBaseChange hp h f ψ g hsq hg
    (isoFiberUnderClassesEquiv p hp (Functor.chosenPullbacks p)
      (squareZeroArrow P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem M)
      ⟨P.point, P.obj.obj.2⟩)
    (Equiv.trans
      (Equiv.ofBijective _ (isoClassMap_bijective_of_essSurj
        (squareLiftEquivalence p (Functor.chosenPullbacks p) fa
          (squareZeroArrow Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem N)
          (squareZeroArrow P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem M) g hcomm hE
          ⟨P.point, P.obj.obj.2⟩).functor))
      (Equiv.trans
        (Equiv.ofBijective _ (bijective_isoClassMap_isoFiberCongrBase
          ((Functor.chosenPullbacks p).pullbackFunctor
            (squareZeroArrow Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem N))
          (fiberIsoOfCartesian fa ((Functor.chosenPullbacks p).map fa ⟨P.point, P.obj.obj.2⟩)
            h.objMap inferInstance hfa)))
        (isoFiberUnderClassesEquiv p hp (Functor.chosenPullbacks p)
          (squareZeroArrow Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem N)
          ⟨Q.point, Q.obj.obj.2⟩)))
    ?_
  intro u
  induction u using Quotient.ind with
  | _ t =>
    exact ⟨isoFiberToUnderObj p (Functor.chosenPullbacks p) _ _ t,
      isoFiberToUnderObj p (Functor.chosenPullbacks p) _ _ _, rfl, rfl, g, hg,
      (Functor.chosenPullbacks p).map g _,
      (Functor.chosenPullbacks p).isStronglyCartesian g _,
      isoFiberArrow_isoFiberCongrBase_squareLiftEquivalence_fac p (Functor.chosenPullbacks p)
        fa (squareZeroArrow Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem N)
        (squareZeroArrow P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem M) g hcomm hE
        ⟨P.point, P.obj.obj.2⟩ ⟨Q.point, Q.obj.obj.2⟩ h.objMap hfa t⟩


/-- **The transition of Stacks 07YA on lift classes is bijective at a semilinear bijection of
coefficients.** This is the Rim–Schlessinger input of Stacks 07YT: the trivial square-zero
extension `A[M]` is the fibre product `A ×_C C[N]`, with the square-zero surjection
`C[N] ⟶ C` on one side, so (RS*) identifies the lifts of `x` over `Spec A[M]` with the lifts of
`y` over `Spec C[N]`. -/
public theorem bijective_squareZeroLiftBaseChangeMap (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS p hp)
    {P Q : ChartedObject B S hS p c} (h : AffineObject.Hom P.obj Q.obj)
    (f : P.ring →+* Q.ring) (halg : f = h.alg.ringMap)
    {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (hψ : Function.Bijective (restrictScalarsAddHom f ψ))
    (g : Q.squareZeroBase N ⟶ P.squareZeroBase M)
    (hsq : h.alg.specMap ≫ squareZeroArrow P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem M =
      squareZeroArrow Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem N ≫ g)
    (hg : IsSquareZeroBaseMap f ψ g) :
    Function.Bijective (squareZeroLiftBaseChangeMap hp h f ψ g hsq hg) := by
  obtain rfl : g = squareZeroOverBaseMap f B S hS P.obj.alg.toScheme Q.obj.alg.toScheme
      (specMap_toScheme_comp h f halg) M N (restrictScalarsAddHom f ψ)
      (restrictScalarsAddHom_smul f ψ) :=
    eq_of_isSquareZeroBaseMap hg (isSquareZeroBaseMap_squareZeroOverBaseMap h f halg ψ)
  have hlift : p.IsHomLift (algebraOverMapOfRingHom f B S hS P.obj.alg.toScheme Q.obj.alg.toScheme
      P.obj.alg.mem Q.obj.alg.mem (specMap_toScheme_comp h f halg)) h.objMap :=
    specMap_eq_algebraOverMap h f halg ▸ h.objMap_isHomLift
  exact bijective_squareZeroLiftBaseChangeMap_of_isEquivalence hp h f ψ _ hsq hg
    (algebraOverMapOfRingHom f B S hS P.obj.alg.toScheme Q.obj.alg.toScheme P.obj.alg.mem
      Q.obj.alg.mem (specMap_toScheme_comp h f halg))
    (hp.isStronglyCartesian_homLift _ _).isCartesian_of_isStronglyCartesian
    (algebraOverMap_comp_squareZeroArrow f B S hS P.obj.alg.toScheme Q.obj.alg.toScheme
      P.obj.alg.mem Q.obj.alg.mem (specMap_toScheme_comp h f halg) M N
      (restrictScalarsAddHom f ψ) (restrictScalarsAddHom_smul f ψ))
    (baseChangeSquare_isEquivalence f B S hS P.obj.alg.toScheme Q.obj.alg.toScheme
      P.obj.alg.mem Q.obj.alg.mem (specMap_toScheme_comp h f halg) M N
      (restrictScalarsAddHom f ψ) (restrictScalarsAddHom_smul f ψ) p hp hRS hψ)

end BaseChangeBijective

/-! ### Stacks 07YT with only the infinitesimal-automorphism step assumed -/

section FieldBaseChange

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {c : AffineChart S}

/-- A morphism of modules into a restriction of scalars which is an isomorphism is bijective on
the underlying additive groups. -/
public theorem bijective_restrictScalarsAddHom_of_isIso {A A' : Type u} [CommRing A]
    [CommRing A'] (f : A →+* A') {M : ModuleCat.{u} A} {N : ModuleCat.{u} A'}
    (ψ : M ⟶ (ModuleCat.restrictScalars f).obj N) [IsIso ψ] :
    Function.Bijective (restrictScalarsAddHom f ψ) :=
  (ConcreteCategory.isIso_iff_bijective ψ).mp inferInstance

/-- **Stacks 07YT, with only the Rim–Schlessinger step on infinitesimal automorphisms
assumed.** Let `y ⟶ x` lie over a ring map `A ⟶ B` of charted objects of a naive obstruction
theory and let `k` be a `B`-algebra which is a field. If the transition of Stacks 07YA on
infinitesimal automorphisms with coefficients in `k` is bijective, then the functoriality map
`E_x ⟶ E_y` induces bijections `H^i(E_x ⊗^L_A k) ⟶ H^i(E_y ⊗^L_B k)` for `i = 0, 1`. -/
public theorem bijective_homologyFunctor_map_naiveObstructionFieldBaseChangeMap_of_infAut
    {hp : p.IsFiberedInGroupoids} {hRS : SatisfiesRSStar B S hS p hp}
    (nob : NaiveObstructionTheory B S hS p hp hRS c)
    (P Q : ChartedObject B S hS p c) (h : AffineObject.Hom P.obj Q.obj)
    [Algebra P.ring Q.ring] [IsScalarTower c.ring P.ring Q.ring]
    (halg : algebraMap P.ring Q.ring = h.alg.ringMap)
    {k : Type u} [Field k] (g : Q.ring →+* k)
    (hM : IsSiteModule P.ring B
      ((ModuleCat.restrictScalars (g.comp (algebraMap P.ring Q.ring))).obj
        (ModuleCat.of k (ULift.{u} k))))
    (hN : IsSiteModule Q.ring B
      ((ModuleCat.restrictScalars g).obj (ModuleCat.of k (ULift.{u} k))))
    (hinf : ∀ σ : ((P.infAut hp hRS).functor.obj
          (fieldSiteModule P.ring B (g.comp (algebraMap P.ring Q.ring)) hM) : Type w) →
        ((Q.infAut hp hRS).functor.obj (fieldSiteModule Q.ring B g hN) : Type w),
      (∀ θ, IsInfinitesimalAutomorphismBaseChange hp h (algebraMap P.ring Q.ring)
        (fieldSiteModuleComparison (algebraMap P.ring Q.ring) B g hM hN)
        ((P.infAut hp hRS).autEquiv _ θ) ((Q.infAut hp hRS).autEquiv _ (σ θ))) →
      Function.Bijective σ) :
    Function.Bijective ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
        (naiveObstructionFieldBaseChangeMap nob P Q h halg g)).hom ∧
      Function.Bijective ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 1).map
        (naiveObstructionFieldBaseChangeMap nob P Q h halg g)).hom :=
  bijective_homologyFunctor_map_naiveObstructionFieldBaseChangeMap_of_bijective nob P Q h halg g
    hM hN _
    (isSquareZeroBaseMap_squareZeroOverBaseMap h (algebraMap P.ring Q.ring) halg
      (fieldSiteModuleComparison (algebraMap P.ring Q.ring) B g hM hN))
    (specMap_comp_squareZeroArrow h (algebraMap P.ring Q.ring) halg _ _
      (restrictScalarsAddHom (algebraMap P.ring Q.ring)
        (fieldSiteModuleComparison (algebraMap P.ring Q.ring) B g hM hN))
      (restrictScalarsAddHom_smul (algebraMap P.ring Q.ring)
        (fieldSiteModuleComparison (algebraMap P.ring Q.ring) B g hM hN)))
    (bijective_squareZeroLiftBaseChangeMap hp hRS h (algebraMap P.ring Q.ring) halg
      (fieldSiteModuleComparison (algebraMap P.ring Q.ring) B g hM hN)
      (bijective_restrictScalarsAddHom_of_isIso (algebraMap P.ring Q.ring) _) _ _ _)
    hinf

end FieldBaseChange

end Deformation.Artin

end
