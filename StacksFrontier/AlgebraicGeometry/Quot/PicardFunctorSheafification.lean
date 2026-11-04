module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackCategory
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids

/-!
# The relative Picard functor is the sheafification of the Picard stack's isomorphism classes

In Situation 0D25 — a morphism `f : X ⟶ B` of algebraic spaces over a scheme `S` — the relative
Picard functor `Pic_{X/B}` is by definition the fppf sheafification of the presheaf
`T ↦ Pic(X_T)` on the schemes over the base
(`AlgebraicGeometry.Space.PicardSituation.picardFunctor`).  Stacks 0D26 identifies the presheaf
being sheafified differently: it is the presheaf of isomorphism classes of *objects of the fibre
categories of the Picard stack*, `T ↦ Ob(Picardstack_{X/B, T})/≅`.  This file proves that, and
deduces that `Pic_{X/B}` is the sheafification of the latter presheaf.

The two presheaves are the same because the fibre category of `Picardstack_{X/B}` over a test
scheme `T` is the groupoid of invertible modules on `X_T`: an object of
`AlgebraicGeometry.Space.PicardObject` lying over `T` is an invertible module on `X_T`, and a
morphism of the fibre is an isomorphism `(X_{𝟙 T})^*L' ⟶ L`, so two objects of the fibre are
isomorphic exactly when their invertible modules are.

## Main definitions

* `AlgebraicGeometry.Space.PicardSituation.objectPicardClass` and
  `AlgebraicGeometry.Space.PicardSituation.fibrePicardClass`: the class in `Pic(X_T)` of the
  invertible module of an object of `Picardstack_{X/B}` lying over `T`, and of an object of the
  fibre `Picardstack_{X/B, T}`.
* `AlgebraicGeometry.Space.PicardSituation.fibreIsoClassEquiv`: **the identification
  `Ob(Picardstack_{X/B, T})/≅ = Pic(X_T)`**, sending the class of an object of the fibre to the
  class of its invertible module.
* `AlgebraicGeometry.Space.PicardSituation.isoClassPresheafIsoPicardPresheaf`: **the
  identification of the presheaf `T ↦ Ob(Picardstack_{X/B, T})/≅` with the presheaf
  `T ↦ Pic(X_T)`**, that is of `CategoryTheory.Functor.isoClassPresheaf` of the projection of the
  Picard stack with `AlgebraicGeometry.Space.PicardSituation.picardPresheaf`.
* `AlgebraicGeometry.Space.PicardSituation.toPicardFunctorOfIsoClasses`: the canonical map from
  the presheaf of isomorphism classes of objects of the fibres of the Picard stack to
  `Pic_{X/B}`.

## Main results

* `AlgebraicGeometry.Space.PicardSituation.isIso_sheafifyLift_toPicardFunctorOfIsoClasses`:
  **Stacks 0D26**, the relative Picard functor is the fppf sheafification of
  `T ↦ Ob(Picardstack_{X/B, T})/≅`: the map it receives from that presheaf lifts to an
  isomorphism from the sheafification.
* `AlgebraicGeometry.Space.PicardSituation.fibrePicardClass_eq_of_hom`: objects of one fibre of
  the Picard stack joined by a morphism of that fibre have the same Picard class.
* `AlgebraicGeometry.Space.PicardSituation.exists_hom_of_objectPicardClass_eq`: the converse, two
  objects of the Picard stack lying over one test scheme whose invertible modules have the same
  Picard class are joined by a morphism of that fibre.
* `AlgebraicGeometry.Space.PicardSituation.fibreIsoClassEquiv_naturality`: restriction of
  isomorphism classes along a morphism of test schemes is the pullback of Picard classes.
* `AlgebraicGeometry.Space.PicardSituation.isGroupoid_fiber_picardProjection`: every fibre of the
  Picard stack is a groupoid, so a morphism of a fibre is automatically invertible.

## Implementation notes

The category `Picardstack_{X/B}` of Section 0372 is `AlgebraicGeometry.Space.picardCategory` at a
pseudofunctoriality datum of Stacks 03LU, and that datum is inhabited with no hypothesis by
`AlgebraicGeometry.Space.modulePushforwardCoherence`; every declaration below is taken at that
value.

For a fibred category `𝒮`, the presheaf `T ↦ Ob(𝒮_T)/≅` is
`CategoryTheory.Functor.isoClassPresheaf`, whose restriction maps are given by a choice of
pullbacks. By `CategoryTheory.Functor.isoClassMk_eq_pullbackFiber_of_isCartesian` the class of
the domain of any cartesian lift is the restriction, and in a category fibred in groupoids every
lift is cartesian, so the restriction maps are computed with the geometric pullback
`AlgebraicGeometry.Space.PicardSituation.pullbackObject`, the inverse image of the invertible
module along `X_g : X_U ⟶ X_T`.

An object of the fibre over `T` is an object `A` of `Picardstack_{X/B}` together with an equality
`A.T = T` of test schemes, and `Pic(X_{A.T})` is only *equal* to `Pic(X_T)`, so the class of the
invertible module of `A` is carried into `Pic(X_T)` along that equality.

## References

* [Stacks Project, Tag 0D26](https://stacks.math.columbia.edu/tag/0D26)
* [Stacks Project, Tag 0D25](https://stacks.math.columbia.edu/tag/0D25)
* [Stacks Project, Section 0372](https://stacks.math.columbia.edu/tag/0372)
* [Stacks Project, Tag 04SC](https://stacks.math.columbia.edu/tag/04SC)
* [Stacks Project, Tag 003V](https://stacks.math.columbia.edu/tag/003V)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace PicardSituation

variable (s : PicardSituation B S hS)

/-! ### The projection of the Picard stack as a fibred category -/

/-- The category `Picardstack_{X/B}` of Section 0372, at the pseudofunctoriality datum of
Stacks 03LU proved by `AlgebraicGeometry.Space.modulePushforwardCoherence`. -/
local instance picardObjectCategory (s : PicardSituation B S hS) :
    Category.{u + 1} (PicardObject s) :=
  picardCategory (modulePushforwardCoherence B S hS) s

/-- **The projection of `Picardstack_{X/B}` to the test schemes over the base is fibred in
groupoids**, at the pseudofunctoriality datum of Stacks 03LU proved by
`AlgebraicGeometry.Space.modulePushforwardCoherence`. -/
theorem isFiberedInGroupoids_picardProjection :
    (picardProjection (modulePushforwardCoherence B S hS) s).IsFiberedInGroupoids :=
  picardProjection_isFiberedInGroupoids_schemesOver (modulePushforwardCoherence B S hS)
    (picardCategoryData (modulePushforwardCoherence B S hS) s)

/-- **The projection of `Picardstack_{X/B}` to the test schemes over the base is a fibred
category**, so the presheaf of isomorphism classes of objects of its fibres exists. -/
instance isFibered_picardProjection :
    (picardProjection (modulePushforwardCoherence B S hS) s).IsFibered :=
  (isFiberedInGroupoids_picardProjection s).isFibered

/-- **Every fibre of `Picardstack_{X/B}` is a groupoid**: this is Stacks 003V for a category
fibred in groupoids. -/
theorem isGroupoid_fiber_picardProjection (T : s.SchemesOver) :
    IsGroupoid ((picardProjection (modulePushforwardCoherence B S hS) s).Fiber T) :=
  (isFiberedInGroupoids_picardProjection s).fiber_isGroupoid T

/-- **The morphism `AlgebraicGeometry.Space.PicardSituation.pullbackHom` from the pullback of an
object of `Picardstack_{X/B}` to that object lies over the morphism of test schemes it is formed
from.** -/
theorem isHomLift_pullbackHom (A : PicardObject s) {V : s.SchemesOver} (h : V ⟶ A.T) :
    (picardProjection (modulePushforwardCoherence B S hS) s).IsHomLift h (pullbackHom A h) := by
  exact inferInstanceAs ((picardProjection (modulePushforwardCoherence B S hS) s).IsHomLift
    ((picardProjection (modulePushforwardCoherence B S hS) s).map (pullbackHom A h))
    (pullbackHom A h))

/-! ### The Picard class of an object of a fibre -/

/-- The class in `Pic(X_T)` of the invertible module of an object `A` of `Picardstack_{X/B}`
lying over the test scheme `T`, carried along the equality `A.T = T` of test schemes. -/
def objectPicardClass {T : s.SchemesOver} (A : PicardObject s) (h : A.T = T) : s.picardAt T :=
  cast (congrArg (fun U ↦ s.picardAt U) h)
    (picardClass (s.baseChange A.T) A.lineBundle A.invertible)

/-- At an object whose test scheme is `T` by construction the transport is the identity: the
class is the Picard class of the invertible module. -/
@[simp]
theorem objectPicardClass_mk (T : s.SchemesOver)
    (L : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2)
    (hL : IsInvertibleModule (s.baseChange T) L) :
    objectPicardClass s ⟨T, L, hL⟩ rfl = picardClass (s.baseChange T) L hL :=
  rfl

/-- The class in `Pic(X_T)` of the invertible module of an object of the fibre
`Picardstack_{X/B, T}`. -/
def fibrePicardClass {T : s.SchemesOver}
    (A : (picardProjection (modulePushforwardCoherence B S hS) s).Fiber T) : s.picardAt T :=
  objectPicardClass s A.1 A.2

/-- Two objects of `Picardstack_{X/B}` lying over one test scheme `T` may be taken to be
`⟨T, L, hL⟩` and `⟨T, L', hL'⟩`, with the equalities of test schemes `rfl`. -/
private theorem picardObject_pair_cases {T : s.SchemesOver}
    {P : ∀ A C : PicardObject s, A.T = T → C.T = T → Prop} (A C : PicardObject s)
    (hA : A.T = T) (hC : C.T = T)
    (h : ∀ L hL L' hL', P ⟨T, L, hL⟩ ⟨T, L', hL'⟩ rfl rfl) : P A C hA hC := by
  obtain ⟨TA, L, hL⟩ := A
  obtain ⟨TC, L', hL'⟩ := C
  change TA = T at hA
  change TC = T at hC
  subst hA
  subst hC
  exact h L hL L' hL'

/-- **Objects of one fibre of `Picardstack_{X/B}` joined by a morphism of that fibre have the
same Picard class.** -/
theorem objectPicardClass_eq_of_hom {T : s.SchemesOver} {A C : PicardObject s} (hA : A.T = T)
    (hC : C.T = T) (m : PicardHom A C) (hm : m.base = eqToHom hA ≫ eqToHom hC.symm) :
    objectPicardClass s A hA = objectPicardClass s C hC := by
  revert m hm
  apply picardObject_pair_cases s A C hA hC
  intro L hL L' hL' m hm
  simp only [eqToHom_refl, Category.comp_id] at hm
  have := m.isIso_fibre
  have key : picardPullback (baseChangeMap s.f m.base) (picardClass _ L' hL') =
      picardClass _ L hL := by
    rw [picardPullback_picardClass]
    exact (picardClass_eq_picardClass_iff _ _ _ _ _).2 ⟨asIso m.fibre⟩
  rw [hm] at key
  simp only [objectPicardClass_mk]
  exact key.symm.trans <|
    s.picardMap_id (modulePushforwardCoherence B S hS) _ (picardClass _ L' hL')

/-- **Objects of one fibre of `Picardstack_{X/B}` joined by a morphism of that fibre have the
same Picard class**, stated for objects of the fibre. -/
theorem fibrePicardClass_eq_of_hom {T : s.SchemesOver}
    {A C : (picardProjection (modulePushforwardCoherence B S hS) s).Fiber T} (m : A ⟶ C) :
    fibrePicardClass s A = fibrePicardClass s C := by
  refine objectPicardClass_eq_of_hom s A.2 C.2 m.1 ?_
  have h : (picardProjection (modulePushforwardCoherence B S hS) s).map
      (Functor.Fiber.fiberInclusion.map m) = eqToHom A.2 ≫ 𝟙 T ≫ eqToHom C.2.symm :=
    IsHomLift.fac' _ (𝟙 T) _
  rwa [Category.id_comp] at h

/-- **Two objects of `Picardstack_{X/B}` lying over one test scheme whose invertible modules have
the same Picard class are joined by a morphism of that fibre.** -/
theorem exists_hom_of_objectPicardClass_eq {T : s.SchemesOver} (A C : PicardObject s)
    (hA : A.T = T) (hC : C.T = T)
    (h : objectPicardClass s A hA = objectPicardClass s C hC) :
    ∃ m : PicardHom A C, m.base = eqToHom hA ≫ eqToHom hC.symm := by
  revert h
  apply picardObject_pair_cases s A C hA hC
  intro L hL L' hL' h
  simp only [objectPicardClass_mk] at h
  obtain ⟨e⟩ := (picardClass_eq_picardClass_iff _ _ _ _ _).1 h
  simp only [eqToHom_refl, Category.id_comp]
  exact ⟨⟨𝟙 _, (baseChangeIdComparison (modulePushforwardCoherence B S hS) s.f _).hom.app L' ≫
    e.inv, inferInstance⟩, rfl⟩

/-! ### The isomorphism classes of objects of a fibre -/

/-- **`Ob(Picardstack_{X/B, T})/≅` is `Pic(X_T)`.** The isomorphism class of an object of the
fibre of the Picard stack over `T` goes to the class in `Pic(X_T)` of its invertible module. -/
@[stacks 0D26 "ONLY the identification of Ob(Picardstack_{X/B,T})/≅ with Pic(X_T) at one test \
scheme; the sheafification statement is \
isIso_sheafifyLift_toPicardFunctorOfIsoClasses"]
def fibreIsoClassEquiv (T : s.SchemesOver) :
    _root_.Quotient (isIsomorphicSetoid
        ((picardProjection (modulePushforwardCoherence B S hS) s).Fiber T)) ≃ s.picardAt T :=
  Equiv.ofBijective
    (_root_.Quotient.lift (fibrePicardClass s) fun _ _ hab ↦
      fibrePicardClass_eq_of_hom s ((Functor.isIsomorphicSetoid_r_iff _ _).1 hab).some.hom)
    ⟨by
      intro c d hcd
      induction c using _root_.Quotient.ind with
      | _ A =>
        induction d using _root_.Quotient.ind with
        | _ C =>
          refine _root_.Quotient.sound ((Functor.isIsomorphicSetoid_r_iff _ _).2 ?_)
          obtain ⟨m, hmb⟩ := exists_hom_of_objectPicardClass_eq s A.1 C.1 A.2 C.2 hcd
          have : (picardProjection (modulePushforwardCoherence B S hS) s).IsHomLift (𝟙 T) m :=
            IsHomLift.of_fac' _ (𝟙 T) m A.2 C.2 (by rw [Category.id_comp]; exact hmb)
          have mf : A ⟶ C :=
            Functor.Fiber.homMk (picardProjection (modulePushforwardCoherence B S hS) s) T m
          have := (isGroupoid_fiber_picardProjection s T).all_isIso mf
          exact ⟨asIso mf⟩, by
      intro x
      obtain ⟨L, hL, rfl⟩ := exists_picardClass (s.baseChange T) x
      exact ⟨_root_.Quotient.mk _ ⟨⟨T, L, hL⟩, rfl⟩, rfl⟩⟩

/-- The identification `Ob(Picardstack_{X/B, T})/≅ = Pic(X_T)` sends the class of an object of
the fibre to the Picard class of its invertible module. -/
@[simp]
theorem fibreIsoClassEquiv_apply (T : s.SchemesOver)
    (A : (picardProjection (modulePushforwardCoherence B S hS) s).Fiber T) :
    s.fibreIsoClassEquiv T (_root_.Quotient.mk _ A) = fibrePicardClass s A :=
  rfl

/-- **Restriction of isomorphism classes along a morphism of test schemes is the pullback of
Picard classes.** The class of an object of the fibre over `T` restricts, along `g : U ⟶ T`, to
the class of the geometric pullback `AlgebraicGeometry.Space.PicardSituation.pullbackObject` of
that object. -/
theorem fibreIsoClassEquiv_naturality {U T : s.SchemesOver} (g : U ⟶ T)
    (c : _root_.Quotient (isIsomorphicSetoid
      ((picardProjection (modulePushforwardCoherence B S hS) s).Fiber T))) :
    s.fibreIsoClassEquiv U
        ((picardProjection (modulePushforwardCoherence B S hS) s).isoClassPresheaf.map g.op c) =
      s.picardMap g (s.fibreIsoClassEquiv T c) := by
  induction c using _root_.Quotient.ind with
  | _ A =>
    obtain ⟨⟨TA, L, hL⟩, hA⟩ := A
    change TA = T at hA
    subst hA
    have hlift := isHomLift_pullbackHom s (⟨TA, L, hL⟩ : PicardObject s) g
    have hcart : (picardProjection (modulePushforwardCoherence B S hS) s).IsCartesian g
        (pullbackHom (⟨TA, L, hL⟩ : PicardObject s) g) :=
      have := (isFiberedInGroupoids_picardProjection s).isStronglyCartesian_homLift g
        (pullbackHom (⟨TA, L, hL⟩ : PicardObject s) g)
      inferInstance
    exact (congrArg (s.fibreIsoClassEquiv U)
      (Functor.isoClassMk_eq_pullbackFiber_of_isCartesian g _
        (⟨pullbackObject (⟨TA, L, hL⟩ : PicardObject s) g, rfl⟩ :
          (picardProjection (modulePushforwardCoherence B S hS) s).Fiber U) _
        hlift hcart).symm).trans
      (picardPullback_picardClass (baseChangeMap s.f g) L hL).symm

/-! ### The sheafification -/

/-- **The presheaf `T ↦ Ob(Picardstack_{X/B, T})/≅` is the presheaf `T ↦ Pic(X_T)`.** At each
test scheme it is `AlgebraicGeometry.Space.PicardSituation.fibreIsoClassEquiv`. -/
@[stacks 0D26 "ONLY the identification of the presheaf T ↦ Ob(Picardstack_{X/B,T})/≅ with the \
presheaf T ↦ Pic(X_T); the sheafification statement is \
isIso_sheafifyLift_toPicardFunctorOfIsoClasses"]
def isoClassPresheafIsoPicardPresheaf :
    (picardProjection (modulePushforwardCoherence B S hS) s).isoClassPresheaf ≅
      s.picardPresheaf :=
  NatIso.ofComponents (fun T ↦ (s.fibreIsoClassEquiv T.unop).toIso) (by
    intro T T' g
    apply ConcreteCategory.hom_ext
    intro c
    exact s.fibreIsoClassEquiv_naturality g.unop c)

/-- The canonical map from the presheaf `T ↦ Ob(Picardstack_{X/B, T})/≅` of isomorphism classes
of objects of the fibres of the Picard stack to the relative Picard functor: the identification
with `T ↦ Pic(X_T)`, followed by the unit of the sheafification. -/
def toPicardFunctorOfIsoClasses :
    (picardProjection (modulePushforwardCoherence B S hS) s).isoClassPresheaf ⟶ s.picardFunctor :=
  s.isoClassPresheafIsoPicardPresheaf.hom ≫ s.toPicardFunctor

/-- In Situation 0D25 the relative Picard functor `Pic_{X/B}` is the fppf
sheafification of the presheaf `T ↦ Ob(Picardstack_{X/B, T})/≅` of isomorphism classes of objects
of the fibre categories of the Picard stack: `Pic_{X/B}` is an fppf sheaf
(`AlgebraicGeometry.Space.PicardSituation.isSheaf_picardFunctor`) and the canonical map
`AlgebraicGeometry.Space.PicardSituation.toPicardFunctorOfIsoClasses` from that presheaf into it
factors through the sheafification by an isomorphism. -/
@[stacks 0D26 "the relative Picard functor is the fppf sheafification of the presheaf of \
isomorphism classes of objects of the fibres of the Picard stack"]
theorem isIso_sheafifyLift_toPicardFunctorOfIsoClasses :
    IsIso (sheafifyLift s.fppfTopology s.toPicardFunctorOfIsoClasses s.isSheaf_picardFunctor) := by
  have key : sheafifyMap s.fppfTopology s.isoClassPresheafIsoPicardPresheaf.hom =
      sheafifyLift s.fppfTopology s.toPicardFunctorOfIsoClasses s.isSheaf_picardFunctor :=
    sheafifyLift_unique s.fppfTopology s.toPicardFunctorOfIsoClasses s.isSheaf_picardFunctor _
      (toSheafify_naturality s.fppfTopology s.isoClassPresheafIsoPicardPresheaf.hom).symm
  rw [← key, ← sheafification_map]
  exact Functor.map_isIso _ _

end PicardSituation

end AlgebraicGeometry.Space

end
