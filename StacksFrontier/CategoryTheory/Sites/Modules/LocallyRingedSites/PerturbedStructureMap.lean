module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackPresentationTransport
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.ToposHomUnitsSquare
public import StacksFrontier.CategoryTheory.Sites.Modules.RingSheafAddDerivation

/-!
# Perturbing the structure map of a locally ringed morphism by a derivation

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi and let `δ` be a derivation
along its inverse-image structure map `f⁻¹𝒪_D ⟶ 𝒪_C` whose values multiply to zero, in the sense
of `Stacks.Sites.RingSheafDerivation`.  The sum `f♯ + δ` is again a map of sheaves of rings
(`Stacks.Sites.RingSheafDerivation.add`), so it is the structure map of another morphism of
ringed topoi with the same underlying morphism of topoi.  **That morphism is locally ringed as
soon as `f` is**, and conversely.

The reason is entirely local: a section of `𝒪_C` is invertible exactly when its translate by a
square-zero section is, so the two structure maps have the same subsheaf of sections pulling back
to units, and a cartesian units square for one is a cartesian units square for the other.

This is the step the proof of [Stacks Project, Tag 05ZN] calls "immediate from the definition,
the fact that `(f, f♯)` is already such a morphism, the commutativity of the square and the local
nilpotence of the kernels of `i_X♯` and `i_Y♯`", and it is the hypothesis that
[Stacks Project, Tag 04D0] needs of the modified structure map `α = (a')♯ + D`.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.ofInverseImageSharp`: the morphism of ringed topoi with a
  prescribed morphism of topoi and a prescribed *inverse-image* structure map `f⁻¹𝒪_D ⟶ 𝒪_C`.
  The field of `AlgebraicGeometry.RingedToposHom` is the direct-image form, so this transposes
  along the adjunction; `ofInverseImageSharp_fSharpInverseImage` says that the inverse-image form
  of the result is the given map.

## Main results

* `AlgebraicGeometry.RingedTopos.isUnit_add_iff_of_mul_self_eq_zero`: a section is invertible
  exactly when its translate by a section of square zero is.
* `AlgebraicGeometry.RingedTopos.reflectsUnitsObj_sections_iff`: reflecting units at the functor
  of sections over an object of the site is the sectionwise statement that a section is
  invertible as soon as its image is.
* `AlgebraicGeometry.RingedTopos.isIso_of_isIso_sections`: the functors of sections over the
  objects of the site are jointly conservative on sheaves of types, so they are an admissible
  family for `AlgebraicGeometry.RingedTopos.isPullback_unitsSquare_of_family`.
* `AlgebraicGeometry.RingedToposHom.isLocallyRinged_add`: **the perturbation theorem.**  If `f`
  is locally ringed then so is the morphism of ringed topoi whose inverse-image structure map is
  `f♯ + δ`.
* `AlgebraicGeometry.RingedToposHom.isLocallyRinged_of_isLocallyRinged_add`: the converse, by the
  same argument applied to `-δ`.

## Implementation notes

The family used for `AlgebraicGeometry.RingedTopos.isPullback_unitsSquare_of_family` is the family
of *sections* functors, not the family of fibres at a conservative family of points.  Both are
admissible, and the fibres are what
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_isLocallyRinged` uses; here the sections are
preferable because the perturbation is given as a sectionwise family to begin with, so with the
sections functors the hypothesis of the criterion is an elementary statement about ring elements
and needs no transport of either the ring structure or the square-zero condition to a fibre.

`AlgebraicGeometry.RingedTopos.reflectsUnitsObj_sections_iff` is `Iff.rfl`: `IsUnit a` *is*
`∃ u : Aˣ, ↑u = a`, and `AlgebraicGeometry.RingedTopos.toUnitsSection` and
`AlgebraicGeometry.RingedTopos.toRingSection` are the identity, so reflecting units at a sections
functor already is the sectionwise implication.

## References

* [Stacks Project, Tag 04HA](https://stacks.math.columbia.edu/tag/04HA)
* [Stacks Project, Tag 04H9](https://stacks.math.columbia.edu/tag/04H9)
* [Stacks Project, Tag 05ZN](https://stacks.math.columbia.edu/tag/05ZN)
* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward

universe t w v u v' u'

namespace AlgebraicGeometry

namespace RingedTopos

/-! ### A square-zero perturbation does not change invertibility -/

/-- **A square-zero perturbation of a unit is a unit.**  If `n * n = 0` then `a + n` is
invertible as soon as `a` is: the inverse is `a⁻¹ (1 - a⁻¹ n)`. -/
theorem isUnit_add_of_mul_self_eq_zero {A : Type*} [CommRing A] {a n : A}
    (hn : n * n = 0) (ha : IsUnit a) : IsUnit (a + n) :=
  IsNilpotent.isUnit_add_left_of_commute ⟨2, (pow_two n).trans hn⟩ ha (Commute.all n a)

/-- **A square-zero perturbation does not change invertibility.**  If `n * n = 0` then `a + n` is
invertible exactly when `a` is; the converse direction is the forward one applied to `-n`. -/
theorem isUnit_add_iff_of_mul_self_eq_zero {A : Type*} [CommRing A] {a n : A}
    (hn : n * n = 0) : IsUnit (a + n) ↔ IsUnit a :=
  ⟨fun h => add_neg_cancel_right a n ▸
    isUnit_add_of_mul_self_eq_zero ((neg_mul_neg n n).trans hn) h,
    isUnit_add_of_mul_self_eq_zero hn⟩

/-! ### Reflecting units at the sections over an object -/

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O₁ O₂ : Sheaf J CommRingCat.{w}}

/-- **Reflecting units at the sections over an object is the sectionwise statement.**  A section
of `O₁` over `U` lifts through the units subsheaf exactly when it is invertible, so reflecting
units for the functor of sections over `U` says that a section is invertible as soon as its
image under `φ` is. -/
theorem reflectsUnitsObj_sections_iff (φ : O₁ ⟶ O₂) (U : Cᵒᵖ) :
    ReflectsUnitsObj (Sheaf.sectionsFunctor J U) φ ↔
      ∀ a : O₁.obj.obj U, IsUnit ((φ.hom.app U).hom a) → IsUnit a :=
  Iff.rfl

/-- **The sections functors are jointly conservative on sheaves of types.**  A morphism of
sheaves of types which is invertible on the sections over every object of the site is
invertible, because the inclusion of sheaves into presheaves is fully faithful. -/
theorem isIso_of_isIso_sections {F G : Sheaf J (Type w)} (ψ : F ⟶ G)
    (h : ∀ U : Cᵒᵖ, IsIso ((Sheaf.sectionsFunctor J U).map ψ)) : IsIso ψ := by
  have : ∀ U : Cᵒᵖ, IsIso (ψ.hom.app U) := h
  have : IsIso ((sheafToPresheaf J (Type w)).map ψ) := NatIso.isIso_of_isIso_app ψ.hom
  exact isIso_of_fully_faithful (F := sheafToPresheaf J (Type w)) ψ

end RingedTopos

namespace RingedToposHom

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget CommRingCat.{w})]
  [Y.J.HasSheafCompose (forget CommRingCat.{w})]

/-- The morphism of ringed topoi with a prescribed morphism of topoi and a prescribed
*inverse-image* structure map.  The field of `AlgebraicGeometry.RingedToposHom` is the
direct-image form `𝒪_D ⟶ f_*𝒪_C`, so this transposes along the adjunction of
`Stacks.Sheaves.ToposPushforward.commRingImageAdjunction`. -/
noncomputable abbrev ofInverseImageSharp (φ : MorphismOfTopoi X.Topos Y.Topos)
    (α : (inverseImageCommRingFunctor φ).obj Y.O ⟶ X.O) : RingedToposHom X Y :=
  { toToposHom := φ
    fSharp := (commRingImageAdjunction φ).homEquiv Y.O X.O α }

omit [X.J.HasSheafCompose (forget CommRingCat.{w})]
    [Y.J.HasSheafCompose (forget CommRingCat.{w})] in
/-- The underlying morphism of topoi of
`AlgebraicGeometry.RingedToposHom.ofInverseImageSharp` is the given one. -/
@[simp]
theorem ofInverseImageSharp_toToposHom (φ : MorphismOfTopoi X.Topos Y.Topos)
    (α : (inverseImageCommRingFunctor φ).obj Y.O ⟶ X.O) :
    (ofInverseImageSharp φ α).toToposHom = φ := rfl

omit [X.J.HasSheafCompose (forget CommRingCat.{w})]
    [Y.J.HasSheafCompose (forget CommRingCat.{w})] in
/-- **The inverse-image structure map of
`AlgebraicGeometry.RingedToposHom.ofInverseImageSharp` is the given one.**  This is the defining
property, and it is the only thing a consumer needs of the construction. -/
@[simp]
theorem ofInverseImageSharp_fSharpInverseImage (φ : MorphismOfTopoi X.Topos Y.Topos)
    (α : (inverseImageCommRingFunctor φ).obj Y.O ⟶ X.O) :
    (ofInverseImageSharp φ α).fSharpInverseImage = α :=
  ((commRingImageAdjunction φ).homEquiv Y.O X.O).symm_apply_apply α

/-! ### The perturbation theorem -/

variable (f : RingedToposHom X Y)

omit [X.J.HasSheafCompose (forget CommRingCat.{w})]
    [Y.J.HasSheafCompose (forget CommRingCat.{w})] in
/-- **Prescribing a morphism's own inverse-image structure map returns the morphism.**  So
`AlgebraicGeometry.RingedToposHom.ofInverseImageSharp` is a section of
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage` at a fixed morphism of topoi, and the two
transposes are inverse to one another. -/
theorem ofInverseImageSharp_fSharpInverseImage_self :
    ofInverseImageSharp f.toToposHom f.fSharpInverseImage = f := by
  obtain ⟨φ, s⟩ := f
  exact congrArg (fun t => (⟨φ, t⟩ : RingedToposHom X Y))
    (((commRingImageAdjunction φ).homEquiv Y.O X.O).apply_symm_apply s)

omit [X.J.HasSheafCompose (forget CommRingCat.{w})]
    [Y.J.HasSheafCompose (forget CommRingCat.{w})] in
/-- **The zero derivation does not move the morphism.**  Perturbing `f` by the zero derivation
returns `f` itself; for [Stacks Project, Tag 04D0] this is the statement that the map `θ = 0`
returns the morphism of thickenings `a'` it modifies. -/
theorem ofInverseImageSharp_zero_add :
    ofInverseImageSharp f.toToposHom
        (0 : Stacks.Sites.RingSheafDerivation f.fSharpInverseImage).add = f :=
  (congrArg (ofInverseImageSharp f.toToposHom)
    (Stacks.Sites.RingSheafDerivation.add_zero_eq (f := f.fSharpInverseImage))).trans
      (ofInverseImageSharp_fSharpInverseImage_self f)

/-- **A morphism of ringed topoi whose inverse-image structure map reflects units sectionwise is
locally ringed.**  This is `AlgebraicGeometry.RingedToposHom.isLocallyRinged_of_reflectsUnitsObj`
at the family of sections functors, whose joint conservativity is
`AlgebraicGeometry.RingedTopos.isIso_of_isIso_sections`. -/
theorem isLocallyRinged_of_isUnit
    [HasPullback (RingedTopos.unitsιOf X.O)
      (RingedTopos.forgetRingMap f.fSharpInverseImage)]
    (h : ∀ (U : X.Cᵒᵖ) (a : ((inverseImageCommRingFunctor f.toToposHom).obj Y.O).obj.obj U),
      IsUnit ((f.fSharpInverseImage.hom.app U).hom a) → IsUnit a) :
    f.IsLocallyRinged :=
  f.isLocallyRinged_of_reflectsUnitsObj (ι := X.Cᵒᵖ)
    (fun U => Sheaf.sectionsFunctor X.J U) (fun _ => inferInstance)
    (fun {_ _} ψ hψ => RingedTopos.isIso_of_isIso_sections ψ hψ)
    fun U => (RingedTopos.reflectsUnitsObj_sections_iff f.fSharpInverseImage U).2 (h U)

/-- **A locally ringed morphism of ringed topoi reflects units sectionwise.**  This is
`AlgebraicGeometry.RingedToposHom.reflectsUnitsObj_of_isLocallyRinged` at a sections functor,
read through `AlgebraicGeometry.RingedTopos.reflectsUnitsObj_sections_iff`. -/
theorem isUnit_of_isUnit_fSharpInverseImage (hf : f.IsLocallyRinged) (U : X.Cᵒᵖ)
    (a : ((inverseImageCommRingFunctor f.toToposHom).obj Y.O).obj.obj U)
    (ha : IsUnit ((f.fSharpInverseImage.hom.app U).hom a)) : IsUnit a :=
  (RingedTopos.reflectsUnitsObj_sections_iff f.fSharpInverseImage U).1
    (f.reflectsUnitsObj_of_isLocallyRinged hf (Sheaf.sectionsFunctor X.J U)) a ha

/-- If `g` differs from the inverse-image structure map of a locally ringed `f` by a square-zero
section at `a`, then `a` is invertible as soon as its image under `g` is. -/
private theorem isUnit_of_isUnit_of_eq_add (hf : f.IsLocallyRinged)
    (g : (inverseImageCommRingFunctor f.toToposHom).obj Y.O ⟶ X.O) (U : X.Cᵒᵖ)
    (a : ((inverseImageCommRingFunctor f.toToposHom).obj Y.O).obj.obj U) {n : X.O.obj.obj U}
    (hn : n * n = 0) (hg : (g.hom.app U).hom a = (f.fSharpInverseImage.hom.app U).hom a + n)
    (ha : IsUnit ((g.hom.app U).hom a)) : IsUnit a :=
  f.isUnit_of_isUnit_fSharpInverseImage hf U a
    ((RingedTopos.isUnit_add_iff_of_mul_self_eq_zero hn).1 (hg ▸ ha))

/-- **The perturbation theorem.**  If `f` is a locally ringed morphism of ringed topoi and `δ` is
a derivation along its inverse-image structure map whose values multiply to zero, then the
morphism of ringed topoi with the same underlying morphism of topoi and inverse-image structure
map `f♯ + δ` is again locally ringed.

A section of `𝒪_C` is invertible exactly when its translate by a square-zero section is
(`AlgebraicGeometry.RingedTopos.isUnit_add_iff_of_mul_self_eq_zero`), so the sectionwise
criterion for `f♯ + δ` is the one for `f♯`. -/
theorem isLocallyRinged_add (hf : f.IsLocallyRinged)
    (δ : Stacks.Sites.RingSheafDerivation f.fSharpInverseImage)
    [HasPullback (RingedTopos.unitsιOf X.O)
      (RingedTopos.forgetRingMap (ofInverseImageSharp f.toToposHom δ.add).fSharpInverseImage)] :
    (ofInverseImageSharp f.toToposHom δ.add).IsLocallyRinged := by
  refine isLocallyRinged_of_isUnit _ fun U a ha => ?_
  rw [ofInverseImageSharp_fSharpInverseImage] at ha
  exact isUnit_of_isUnit_of_eq_add _ hf δ.add U a (δ.mul_eq_zero U a a) (δ.add_apply U a) ha

/-- **The converse of the perturbation theorem.**  If the morphism of ringed topoi with
inverse-image structure map `f♯ + δ` is locally ringed then so is `f`, by
`AlgebraicGeometry.RingedTopos.isUnit_add_iff_of_mul_self_eq_zero` in the other direction. -/
theorem isLocallyRinged_of_isLocallyRinged_add
    (δ : Stacks.Sites.RingSheafDerivation f.fSharpInverseImage)
    (hadd : (ofInverseImageSharp f.toToposHom δ.add).IsLocallyRinged)
    [HasPullback (RingedTopos.unitsιOf X.O)
      (RingedTopos.forgetRingMap f.fSharpInverseImage)] :
    f.IsLocallyRinged := by
  refine isLocallyRinged_of_isUnit _ fun U a ha => ?_
  refine isUnit_of_isUnit_fSharpInverseImage _ hadd U a ?_
  rw [ofInverseImageSharp_fSharpInverseImage, δ.add_apply U a]
  exact (RingedTopos.isUnit_add_iff_of_mul_self_eq_zero (δ.mul_eq_zero U a a)).2 ha

/-! ### Transferring the locally ringed condition along a map with square zero kernel -/

/-- **A second structure map agreeing with a locally ringed one after a map whose kernel has
square zero is again locally ringed.**  Here the hypothesis is an equality of *morphisms* in the
direct-image form, so a consumer never has to read either structure map on sections of an inverse
image sheaf.

This is `AlgebraicGeometry.RingedToposHom.isLocallyRinged_add` with the perturbation presented
differently: instead of a `Stacks.Sites.RingSheafDerivation` along the inverse-image structure
map, the datum is a map `q : 𝒪_C ⟶ P` whose sectionwise kernel has square zero together with the
commuting triangle `f♯ ≫ q_* = t ≫ q_*`.  For [Stacks Project, Tag 04D0] the map `q` is the
structure map `i_X^♯` of the closed immersion of the first order thickening, whose sectionwise
kernel is the defining ideal and so has square zero, and the triangle is the source's equation
`i_X^♯ ∘ α = a^♯ ∘ i_Y^♯`.  So the locally ringed condition and that equation have a single
input. -/
theorem isLocallyRinged_of_fSharp_comp_eq (hf : f.IsLocallyRinged)
    (t : Y.O ⟶ (pushforwardCommRingFunctor f.toToposHom).obj X.O)
    {P : Sheaf X.J CommRingCat.{w}} (q : X.O ⟶ P)
    (hq : ∀ (U : X.Cᵒᵖ) (x : X.O.obj.obj U), (q.hom.app U).hom x = 0 → x * x = 0)
    (h : f.fSharp ≫ (pushforwardCommRingFunctor f.toToposHom).map q =
      t ≫ (pushforwardCommRingFunctor f.toToposHom).map q)
    [HasPullback (RingedTopos.unitsιOf X.O)
      (RingedTopos.forgetRingMap (⟨f.toToposHom, t⟩ : RingedToposHom X Y).fSharpInverseImage)] :
    (⟨f.toToposHom, t⟩ : RingedToposHom X Y).IsLocallyRinged := by
  have hinv : f.fSharpInverseImage ≫ q =
      (⟨f.toToposHom, t⟩ : RingedToposHom X Y).fSharpInverseImage ≫ q := by
    have h₁ := (commRingImageAdjunction f.toToposHom).homEquiv_naturality_right_symm f.fSharp q
    have h₂ := (commRingImageAdjunction f.toToposHom).homEquiv_naturality_right_symm t q
    exact h₁.symm.trans ((congrArg
      ((commRingImageAdjunction f.toToposHom).homEquiv Y.O P).symm h).trans h₂)
  refine isLocallyRinged_of_isUnit _ fun U a ha => ?_
  set g := (⟨f.toToposHom, t⟩ : RingedToposHom X Y).fSharpInverseImage
  have hdiff : (q.hom.app U).hom ((g.hom.app U).hom a - (f.fSharpInverseImage.hom.app U).hom a)
      = 0 := by
    rw [map_sub]
    exact sub_eq_zero_of_eq
      (ConcreteCategory.congr_hom (congrArg (fun r => r.hom.app U) hinv.symm) a)
  exact isUnit_of_isUnit_of_eq_add _ hf g U a (hq U _ hdiff) (by rw [add_sub_cancel]) ha

end RingedToposHom

end AlgebraicGeometry

end
