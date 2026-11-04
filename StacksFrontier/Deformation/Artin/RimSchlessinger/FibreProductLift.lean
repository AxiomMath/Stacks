module

public import StacksFrontier.AlgebraicGeometry.Pushout.Affine
public import StacksFrontier.Deformation.Artin.Infinitesimal.TangentFunctor

/-!
# Condition (RS*) at the fibre-product shape

`Deformation.Artin.SatisfiesRSStar` asserts that a comparison functor
`Deformation.Artin.fiberSquareComparison` is an equivalence. Its consumers so far use that
equivalence on the *iso-fibre over a fixed object* —
`Deformation.Artin.squareZeroProd_isEquivalence`,
`Deformation.Artin.baseChangeSquare_isEquivalence` and
`Deformation.Artin.exists_squareZeroLiftEquivalence` all fix one object of the fibre over the
small corner and compare its lifts. This file extracts instead the *essential surjectivity* of
the comparison, which is the half of the equivalence that produces a new object: a family over
`Spec A`, a family over `Spec C'` and an identification of their restrictions to `Spec C` glue
to a family over `Spec (A ×_C C')`.

Essential surjectivity yields a *lift*, not a class: the output is an object of the fibre over
the fourth corner together with isomorphisms identifying its two chosen restrictions with the
two given families. There is no obstruction class in the statement.

## Main results

* `Deformation.Artin.exists_fiber_of_fiberSquareComparison_essSurj` — the gluing property for an
  arbitrary commutative square in the base whose comparison functor is essentially surjective.
* `Deformation.Artin.exists_fiber_of_satisfiesRSStar` — the same at a square of the big affine
  fppf site satisfying the hypotheses of (RS*), with the equivalence supplied by (RS*).
* `Deformation.Artin.nonempty_underFiber_of_satisfiesRSStar` — the glued family read as an
  inhabitant of the category of lifts of condition (iii) of [Stacks, Tag 07YX], which is the
  shape the hypotheses of [Stacks, Tag 07YM] are written with.
* `Deformation.Artin.specMap_appTop_isPullback` — a cartesian square of commutative rings induces
  a cartesian square of the global sections of the spectra, which is the form the pullback
  hypothesis of (RS*) is stated in. Together with
  `Stacks.Pushout.isPullback_ofHom_pullback` this discharges that hypothesis at a fibre product
  of rings.

## Implementation notes

The three main statements are separated so that the only one mentioning the site is the middle
one: the gluing property is a statement about an arbitrary functor with a choice of pullbacks,
and reading the result as an inhabitant of the category of lifts is
`Deformation.Artin.isoFiberToUnderObj` applied to the isomorphism identifying the first chosen
restriction with the given family.

`Deformation.Artin.nonempty_underFiber_of_satisfiesRSStar` takes the arrow of the site under
which the lift is formed as a separate argument together with an equation identifying it with
the image of the leg of the square. A consumer carries that arrow in whatever presentation its
deformation situation provides — for the thickening of
`Deformation.Artin.squareZeroThickeningOfMkLe` it is the structure arrow of the thickening —
and rewriting underneath `Deformation.Artin.underFiber_right_obj` is not available, since an
`eqToHom` whose implicit arguments mention an element of a fibre has an ill-typed motive at
`implicit` transparency.

## References

* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
* [Stacks Project, Tag 07YX](https://stacks.math.columbia.edu/tag/07YX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Deformation.Artin

/-! ### Global sections of a cartesian square of spectra -/

section Sections

universe u

/-- A cartesian square of commutative rings stays cartesian after taking global sections of
the spectra: the four comparison isomorphisms `Scheme.ΓSpecIso` identify the two squares. This
is the shape in which the pullback hypothesis of `Deformation.Artin.SatisfiesRSStar` is
stated. -/
public theorem specMap_appTop_isPullback {P R T Q : CommRingCat.{u}}
    {a : P ⟶ R} {b : P ⟶ T} {f : R ⟶ Q} {g : T ⟶ Q} (h : IsPullback a b f g) :
    IsPullback (Spec.map a).appTop (Spec.map b).appTop
      (Spec.map f).appTop (Spec.map g).appTop := by
  apply h.of_iso' (Scheme.ΓSpecIso P) (Scheme.ΓSpecIso R) (Scheme.ΓSpecIso T)
    (Scheme.ΓSpecIso Q)
  all_goals exact (Scheme.ΓSpecIso_naturality _).symm

/-- The concrete fibre product of rings meets the hypothesis above: `Spec (A ×_C C')` has the
global sections of the four spectra in a cartesian square, with no hypothesis on either map.
Recorded as an `example` because the comparison isomorphisms stay behind
`Deformation.Artin.specMap_appTop_isPullback`: spelling them out in a statement at a concrete
fibre product sends the kernel looking for the limit cone. -/
example {A C' C : Type u} [CommRing A] [CommRing C'] [CommRing C]
    (α : A →+* C) (β : C' →+* C) :
    IsPullback (Spec.map (CommRingCat.ofHom (α.pullbackFst β))).appTop
      (Spec.map (CommRingCat.ofHom (α.pullbackSnd β))).appTop
      (Spec.map (CommRingCat.ofHom α)).appTop
      (Spec.map (CommRingCat.ofHom β)).appTop :=
  specMap_appTop_isPullback (Stacks.Pushout.isPullback_ofHom_pullback α β)

end Sections

/-! ### Gluing two families along an identification of their restrictions -/

section Glue

open Functor

universe v₁ v₂ u₁ u₂

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor
  CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
  CategoryTheory.Limits.CategoricalPullback.π₁
  CategoryTheory.Limits.CategoricalPullback.π₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable (q : D ⥤ C) (c : q.ChoiceOfPullbacks)
variable {U V W Z : C} (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z)
variable (w : f ≫ i = g ≫ j)

/-- **Gluing along an identification of restrictions.** When the comparison functor of a
commutative square in the base is essentially surjective, an object of the fibre over the
second corner and an object of the fibre over the third corner whose chosen restrictions to
the first corner are identified come from an object of the fibre over the fourth corner: the
two chosen restrictions of that object are isomorphic to the two given ones, compatibly with
the given identification. -/
public theorem exists_fiber_of_fiberSquareComparison_essSurj
    [(fiberSquareComparison q c f g i j w).EssSurj]
    (x : q.Fiber V) (y : q.Fiber W)
    (e : (c.pullbackFunctor f).obj x ≅ (c.pullbackFunctor g).obj y) :
    ∃ (z : q.Fiber Z) (ex : (c.pullbackFunctor i).obj z ≅ x)
      (ey : (c.pullbackFunctor j).obj z ≅ y),
      (c.pullbackFunctor f).map ex.hom ≫ e.hom =
        ((fiberSquareComparison q c f g i j w).obj z).iso.hom ≫
          (c.pullbackFunctor g).map ey.hom := by
  obtain ⟨z, ⟨κ⟩⟩ := Functor.EssSurj.mem_essImage
    (fiberSquareComparison q c f g i j w) ⟨x, y, e⟩
  exact ⟨z, (CategoricalPullback.π₁ _ _).mapIso κ, (CategoricalPullback.π₂ _ _).mapIso κ, κ.hom.w⟩

end Glue

/-! ### The gluing property supplied by (RS*) -/

section Site

open Functor

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X : Type w} [Category X] {p : X ⥤ BigFppfOver B S hS}

/-- **(RS\* ) at the fibre-product shape.** For a square of the big affine fppf site which is a
fibre product on global sections and whose second leg is a surjection with square-zero kernel,
condition (RS*) glues a family over the second corner and a family over the third corner whose
chosen restrictions to the first corner are identified into a family over the fourth corner.

This is the essential-surjectivity half of (RS*). The existing consumers of
`Deformation.Artin.SatisfiesRSStar` use the equivalence on the iso-fibre over a fixed object,
which compares the lifts of one family; this produces a new family instead. -/
public theorem exists_fiber_of_satisfiesRSStar
    (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
    (U V W Z : BigAffineFppf B S hS)
    (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j)
    (hpb : IsPullback ((BigAffineFppf.toScheme B S hS).map i).appTop
      ((BigAffineFppf.toScheme B S hS).map j).appTop
      ((BigAffineFppf.toScheme B S hS).map f).appTop
      ((BigAffineFppf.toScheme B S hS).map g).appTop)
    (hsurj : Function.Surjective
      (((BigAffineFppf.toScheme B S hS).map g).appTop.hom))
    (hsq : RingHom.ker (((BigAffineFppf.toScheme B S hS).map g).appTop.hom) ^ 2 = ⊥) :
    letI : p.IsFibered := hp.isFibered
    let c := Functor.chosenPullbacks p
    let ι := BigAffineFppf.inclusion B S hS
    ∀ (x : p.Fiber (ι.obj V)) (y : p.Fiber (ι.obj W))
      (e : (c.pullbackFunctor (ι.map f)).obj x ≅ (c.pullbackFunctor (ι.map g)).obj y),
      ∃ (z : p.Fiber (ι.obj Z)) (ex : (c.pullbackFunctor (ι.map i)).obj z ≅ x)
        (ey : (c.pullbackFunctor (ι.map j)).obj z ≅ y),
        (c.pullbackFunctor (ι.map f)).map ex.hom ≫ e.hom =
          ((fiberSquareComparison p c (ι.map f) (ι.map g) (ι.map i) (ι.map j)
            (by simpa only [Functor.map_comp] using congrArg ι.map h)).obj z).iso.hom ≫
            (c.pullbackFunctor (ι.map g)).map ey.hom := by
  let : p.IsFibered := hp.isFibered
  intro c ι x y e
  let : (fiberSquareComparison p c (ι.map f) (ι.map g) (ι.map i) (ι.map j)
      (by simpa only [Functor.map_comp] using congrArg ι.map h)).IsEquivalence :=
    hRS U V W Z f g i j h hpb hsurj hsq
  exact exists_fiber_of_fiberSquareComparison_essSurj p c (ι.map f) (ι.map g)
    (ι.map i) (ι.map j) _ x y e

/-- **The glued family as a lift of the first one.** Reading the output of
`Deformation.Artin.exists_fiber_of_satisfiesRSStar` through
`Deformation.Artin.isoFiberToUnderObj`: the family over the second corner acquires a lift
across the leg to the fourth corner, in the shape the hypotheses of [Stacks, Tag 07YM] speak,
namely non-emptiness of the fibre of `CategoryTheory.Under.post p` over that leg. -/
public theorem nonempty_underFiber_of_satisfiesRSStar
    (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
    (U V W Z : BigAffineFppf B S hS)
    (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j)
    (hpb : IsPullback ((BigAffineFppf.toScheme B S hS).map i).appTop
      ((BigAffineFppf.toScheme B S hS).map j).appTop
      ((BigAffineFppf.toScheme B S hS).map f).appTop
      ((BigAffineFppf.toScheme B S hS).map g).appTop)
    (hsurj : Function.Surjective
      (((BigAffineFppf.toScheme B S hS).map g).appTop.hom))
    (hsq : RingHom.ker (((BigAffineFppf.toScheme B S hS).map g).appTop.hom) ^ 2 = ⊥) :
    letI : p.IsFibered := hp.isFibered
    let c := Functor.chosenPullbacks p
    let ι := BigAffineFppf.inclusion B S hS
    ∀ (x : p.Fiber (ι.obj V)) (y : p.Fiber (ι.obj W))
      (_ : (c.pullbackFunctor (ι.map f)).obj x ≅ (c.pullbackFunctor (ι.map g)).obj y)
      (ν : ι.obj V ⟶ ι.obj Z) (_ : ι.map i = ν),
      Nonempty ((Under.post p).Fiber (Under.mk (eqToHom x.2 ≫ ν))) := by
  let : p.IsFibered := hp.isFibered
  rintro c ι x y e ν rfl
  obtain ⟨z, ex, -, -⟩ :=
    exists_fiber_of_satisfiesRSStar hp hRS U V W Z f g i j h hpb hsurj hsq x y e
  exact ⟨isoFiberToUnderObj p c (ι.map i) x ⟨CostructuredArrow.mk ex.hom, ex.isIso_hom⟩⟩

end Site

end Deformation.Artin
