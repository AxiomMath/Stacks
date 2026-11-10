module

public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityFieldVersalLift

/-!
# Restriction of a family along a ring map, and reading an algebra map off an arrow

The direction `(1) ⇒ (2)` of [Stacks, Tag 07YM] in degree `-1` crosses between two
vocabularies in both directions. Versality is a lifting property for arrows of the fibred
category `p : 𝒳 ⟶ (Sch/S)_{fppf}` lying over prescribed morphisms of schemes
(`Deformation.Artin.LiftsAtResiduePoint`), whereas the algebra of the argument — the small
extension `A' ⧸ (𝔭') ^ n ⟶ A ⧸ 𝔭 ^ n` and the section it is to be given — lives in rings. This
file supplies the two crossings.

*Restriction.* Given `x` over `Spec A` and a ring map `φ : A → C` whose spectrum lies over
`S` and whose source scheme occurs in the site, the restriction `x|_{Spec C}` is the chosen
pullback of `x` along the site morphism `Spec C ⟶ Spec A` that `φ` determines
(`Deformation.Artin.algebraOverMapOfRingHom`). It lies over `Spec C` and its structure arrow
has underlying morphism of schemes `Spec φ`. Nothing is assumed about `φ` beyond
compatibility with the structure morphisms; in particular it is not asked to be surjective,
local, or a map of Artinian rings, which is what distinguishes this from
`Deformation.Artin.squareZeroArtinianObj` and
`Deformation.Artin.exists_extends_of_liftsAtResiduePoint`, both of which are written for the
dual numbers `TrivSqZeroExt k M` of a field.

*Reading off an algebra map.* Conversely an arrow `b : z ⟶ x` of `𝒳` from an object over
`Spec C` to `x` has an underlying morphism of schemes `Spec C ⟶ Spec A` over `S`, which — both
ends being affine and `Scheme.Spec` fully faithful — is the spectrum of a unique ring map
`A → C`, and lying over `S` makes that ring map a `Λ`-algebra homomorphism for any `Λ`
through which both structure morphisms factor.

## Main definitions

* `Deformation.Artin.restrictAlong` — the restriction `x|_{Spec C}`, with
  `Deformation.Artin.restrictAlong_obj` placing it over `Spec C` and
  `Deformation.Artin.restrictAlongArrow` its structure arrow to `x`.
* `Deformation.Artin.ringHom_of_schemeMap` — the ring map `A → C` underlying a morphism of
  schemes `Spec C ⟶ Spec A`; `Deformation.Artin.algHom_of_schemeMap` the same read as a
  `Λ`-algebra homomorphism when the morphism lies over `Spec Λ`, and
  `Deformation.Artin.algHom_of_schemeMap_over` when it lies over `S` through a monomorphic
  `Spec Λ ⟶ S`.

## Main results

* `Deformation.Artin.schemeMap_restrictAlongArrow` and
  `Deformation.Artin.schemeMap_restrictAlongArrow_mk` — the structure arrow of the restriction
  has underlying morphism of schemes `Spec φ`, at an arbitrary presentation of the two bases
  over `S` and at the canonical one.
* `Deformation.Artin.exists_unique_schemeMap_eq_of_square` — the arrow of a commuting square:
  if `a : y ⟶ x'` and `r : z ⟶ x'` are arrows whose underlying morphisms of schemes make a
  commuting triangle with a morphism `f` of the base, and `r` is cartesian, then `f` is the
  underlying morphism of a unique `y ⟶ z` over `x'`.
* `Deformation.Artin.lift_obj` and `Deformation.Artin.isHomLift_lift_hom` — the unpacking of an
  inhabitant of the category of lifts of condition (iii) of [Stacks, Tag 07YX] into the object
  it lies over and the fact that its structure arrow lies over the thickening, with
  `Deformation.Artin.schemeMap_lift_hom` the resulting morphism of schemes.
* `Deformation.Artin.specMap_ringHom_of_schemeMap`,
  `Deformation.Artin.specMap_algHom_of_schemeMap` and
  `Deformation.Artin.specMap_algHom_of_schemeMap_over` — the ring map, respectively algebra
  map, read off a morphism of schemes has that morphism as its spectrum.

Two `example`s record that the two readers meet the interfaces they are built for: the
restriction lands in the shape `Deformation.Artin.LiftsAtResiduePoint` consumes, and every
arrow of the total category between two objects presented over `S` through `Spec Λ` yields a
`Λ`-algebra homomorphism with that arrow's base as its spectrum.

## Implementation notes

The identifications of the two bases are read off `CategoryTheory.Functor.IsHomLift` through
`Deformation.Artin.schemeMap_eq_of_isHomLift` rather than rewritten: an `eqToHom` whose
implicit arguments mention an element `⟨x, hx⟩` of a fibre has an ill-typed motive at
`implicit` transparency, so no rewrite under it is available. For the same reason
`Deformation.Artin.restrictAlong` is a plain definition with an `rfl` lemma for its image under
`p`, rather than an existential statement: the existential would have to be re-elaborated under
the quantifiers its consumers carry.

The `Λ`-linearity of `Deformation.Artin.algHom_of_schemeMap` is `Scheme.Spec`'s faithfulness
applied to the factorization of the morphism through `Spec Λ`, not a computation with
`Scheme.Spec`'s unit; the statement therefore takes the two factorizations as hypotheses and
needs no algebra instance relating `A` and `C`.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
* [Stacks Project, Tag 02XN](https://stacks.math.columbia.edu/tag/02XN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

universe u v w

/-! ### Restriction of a family along a ring map -/

section Restriction

variable {A C : Type u} [CommRing A] [CommRing C] (φ : A →+* C)
  (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (toSC : Spec (.of C) ⟶ S)
  (hA : B.Contains (Spec (.of A))) (hC : B.Contains (Spec (.of C)))
  (hφ : Spec.map (CommRingCat.ofHom φ) ≫ toS = toSC)
variable {Y : Type v} [Category.{w} Y] (p : Y ⥤ BigFppfOver B S hS) [p.IsFibered]
  (x : Y) (hx : p.obj x = algebraOver A B S hS toS hA)

/-- The morphism of schemes underlying `Deformation.Artin.algebraOverMapOfRingHom` is the
spectrum of the ring map it is built from. -/
public theorem toScheme_map_algebraOverMapOfRingHom :
    (BigFppfOver.toScheme B S hS).map
        (algebraOverMapOfRingHom φ B S hS toS toSC hA hC hφ) =
      Spec.map (CommRingCat.ofHom φ) := rfl

/-- **The restriction `x|_{Spec C}`.** For a ring map `φ : A → C` compatible with the
structure morphisms, this is the chosen pullback of `x` along the morphism
`Spec C ⟶ Spec A` of the site that `φ` determines. -/
public def restrictAlong : Y :=
  ((Functor.chosenPullbacks p).obj
    (algebraOverMapOfRingHom φ B S hS toS toSC hA hC hφ) ⟨x, hx⟩).1

/-- The restriction lies over `Spec C`. -/
public theorem restrictAlong_obj :
    p.obj (restrictAlong φ B S hS toS toSC hA hC hφ p x hx) =
      algebraOver C B S hS toSC hC :=
  ((Functor.chosenPullbacks p).obj
    (algebraOverMapOfRingHom φ B S hS toS toSC hA hC hφ) ⟨x, hx⟩).2

/-- The structure arrow of the restriction: the chosen cartesian lift of `Spec φ` at `x`. -/
public def restrictAlongArrow : restrictAlong φ B S hS toS toSC hA hC hφ p x hx ⟶ x :=
  (Functor.chosenPullbacks p).map
    (algebraOverMapOfRingHom φ B S hS toS toSC hA hC hφ) ⟨x, hx⟩

/-- The structure arrow of the restriction is strongly cartesian over the morphism of the
site that `φ` determines. -/
public instance isStronglyCartesian_restrictAlongArrow :
    p.IsStronglyCartesian (algebraOverMapOfRingHom φ B S hS toS toSC hA hC hφ)
      (restrictAlongArrow φ B S hS toS toSC hA hC hφ p x hx) :=
  (Functor.chosenPullbacks p).isStronglyCartesian
    (algebraOverMapOfRingHom φ B S hS toS toSC hA hC hφ) ⟨x, hx⟩

/-- **The morphism of schemes underlying the structure arrow of the restriction is
`Spec φ`.** Stated with the two identifications of the bases as arguments, so that it can be
used at whichever presentation of `Spec C` and `Spec A` over `S` the consumer carries. -/
public theorem schemeMap_restrictAlongArrow {Z W : Over S}
    (hz : (p ⋙ Over.post B.inclusion).obj
      (restrictAlong φ B S hS toS toSC hA hC hφ p x hx) = Z)
    (hw : (p ⋙ Over.post B.inclusion).obj x = W)
    (eZ : Z.left = Spec (.of C)) (eW : Spec (.of A) = W.left) :
    schemeMap (p ⋙ Over.post B.inclusion) hz hw
        (restrictAlongArrow φ B S hS toS toSC hA hC hφ p x hx) =
      eqToHom eZ ≫ Spec.map (CommRingCat.ofHom φ) ≫ eqToHom eW := by
  have : p.IsHomLift (algebraOverMapOfRingHom φ B S hS toS toSC hA hC hφ)
      (restrictAlongArrow φ B S hS toS toSC hA hC hφ p x hx) :=
    (isStronglyCartesian_restrictAlongArrow φ B S hS toS toSC hA hC hφ p x hx).toIsHomLift
  rw [schemeMap_eq_of_isHomLift B S hS p
    (algebraOverMapOfRingHom φ B S hS toS toSC hA hC hφ)
    (restrictAlongArrow φ B S hS toS toSC hA hC hφ p x hx) hz hw eZ eW,
    toScheme_map_algebraOverMapOfRingHom φ B S hS toS toSC hA hC hφ]
  rfl

/-- The restriction lies over `Spec C`, read in the slice over `S`. -/
public theorem restrictAlong_objS :
    (p ⋙ Over.post B.inclusion).obj
        (restrictAlong φ B S hS toS toSC hA hC hφ p x hx) = Over.mk toSC := by
  change (Over.post B.inclusion).obj
    (p.obj (restrictAlong φ B S hS toS toSC hA hC hφ p x hx)) = _
  rw [restrictAlong_obj φ B S hS toS toSC hA hC hφ p x hx]
  rfl

/-- **The bridge from a ring map to an arrow of the fibred category.** For a ring map
`φ : A → C` compatible with the structure morphisms, the restriction
`Deformation.Artin.restrictAlong` is an object lying over `Spec C` whose structure arrow to
`x` has underlying morphism of schemes exactly `Spec φ`.

This is the shape `Deformation.Artin.LiftsAtResiduePoint` consumes, with the two bases
presented as objects of the slice over `S`. -/
@[stacks 07YM "the restriction of x along a ring map, over Spec of that map"]
public theorem schemeMap_restrictAlongArrow_mk
    (hw : (p ⋙ Over.post B.inclusion).obj x = Over.mk toS) :
    schemeMap (p ⋙ Over.post B.inclusion)
        (restrictAlong_objS φ B S hS toS toSC hA hC hφ p x hx) hw
        (restrictAlongArrow φ B S hS toS toSC hA hC hφ p x hx) =
      Spec.map (CommRingCat.ofHom φ) := by
  rw [schemeMap_restrictAlongArrow φ B S hS toS toSC hA hC hφ p x hx
    (restrictAlong_objS φ B S hS toS toSC hA hC hφ p x hx) hw rfl rfl]
  simp

/-- A sanity check that the restriction lands in the shape
`Deformation.Artin.LiftsAtResiduePoint` consumes. That property asks for an object lying over
`Spec` of an algebra over the deformation base `Λ`, presented as `Over.mk (Spec (Λ → C) ≫ iΛ)`,
together with an arrow whose underlying morphism of schemes is the spectrum of the ring map.
The restriction along a `Λ`-algebra homomorphism supplies exactly that: the compatibility with
the structure morphisms, which is the only hypothesis
`Deformation.Artin.restrictAlong` takes, is `AlgHom.commutes`. -/
example {Λ : Type u} [CommRing Λ] {A C : Type u} [CommRing A] [CommRing C]
    [Algebra Λ A] [Algebra Λ C] (ψ : A →ₐ[Λ] C)
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (iΛ : Spec (.of Λ) ⟶ S)
    (hA : B.Contains (Spec (.of A))) (hC : B.Contains (Spec (.of C)))
    {Y : Type v} [Category.{w} Y] (p : Y ⥤ BigFppfOver B S hS) [p.IsFibered] (x : Y)
    (hx : p.obj x = algebraOver A B S hS
      (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) hA) :
    ∃ (y : Y) (hy : (p ⋙ Over.post B.inclusion).obj y =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ C)) ≫ iΛ))
      (hxS : (p ⋙ Over.post B.inclusion).obj x =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ))
      (a : y ⟶ x),
      schemeMap (p ⋙ Over.post B.inclusion) hy hxS a =
        Spec.map (CommRingCat.ofHom ψ.toRingHom) := by
  have hψ : CommRingCat.ofHom (algebraMap Λ A) ≫ CommRingCat.ofHom ψ.toRingHom =
      CommRingCat.ofHom (algebraMap Λ C) := by
    apply CommRingCat.hom_ext
    ext l
    exact ψ.commutes l
  have hφ : Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) =
      Spec.map (CommRingCat.ofHom (algebraMap Λ C)) ≫ iΛ := by
    rw [← Category.assoc, ← Spec.map_comp, hψ]
  have hxS : (p ⋙ Over.post B.inclusion).obj x =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) := by
    change (Over.post B.inclusion).obj (p.obj x) = _
    rw [hx]
    rfl
  exact ⟨_, _, hxS, _, schemeMap_restrictAlongArrow_mk ψ.toRingHom B S hS _ _ hA hC hφ p x hx hxS⟩

end Restriction

/-! ### The arrow supplied by a commuting square -/

section Square

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Y : Type v} [Category.{w} Y] (p : Y ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

include hp in
/-- **The arrow of a commuting square.** Let `a : y ⟶ x'` be any arrow and let `r : z ⟶ x'` be
a cartesian arrow, and suppose a morphism `f : Z.left ⟶ W.left` of the base over `S`
completes the triangle of underlying morphisms of schemes. Then `f` is the underlying morphism
of schemes of a unique arrow `y ⟶ z` composing with `r` to `a`.

In the direction `(1) ⇒ (2)` of [Stacks, Tag 07YM] this is what produces the arrow
`x|_{A ⧸ 𝔭 ^ n} ⟶ x'|_{A' ⧸ (𝔭') ^ n}` over `Spec(A' ⧸ (𝔭') ^ n) ⟶ Spec(A ⧸ 𝔭 ^ n)`: `r` is
the structure arrow of the second restriction, which
`Deformation.Artin.isStronglyCartesian_restrictAlongArrow` makes cartesian, `a` is the first
restriction followed by the lift `x ⟶ x'`, and the commuting triangle is the commuting square
of rings `A' → A → A ⧸ 𝔭 ^ n` and `A' → A' ⧸ (𝔭') ^ n → A ⧸ 𝔭 ^ n`. -/
public theorem exists_unique_schemeMap_eq_of_square
    {y z x' : Y} {Z W V : Over S}
    (hy : (p ⋙ Over.post B.inclusion).obj y = Z)
    (hz : (p ⋙ Over.post B.inclusion).obj z = W)
    (hx' : (p ⋙ Over.post B.inclusion).obj x' = V)
    (r : z ⟶ x') (a : y ⟶ x') (f : Z.left ⟶ W.left)
    (hf : f ≫ W.hom = Z.hom)
    (hsquare : f ≫ schemeMap (p ⋙ Over.post B.inclusion) hz hx' r =
      schemeMap (p ⋙ Over.post B.inclusion) hy hx' a) :
    ∃! i : y ⟶ z, schemeMap (p ⋙ Over.post B.inclusion) hy hz i = f ∧ i ≫ r = a :=
  factor_through_cartesian_schemeMap B S hS p hp hy hz hx' r a f hf hsquare

end Square

/-! ### Unpacking an inhabitant of the category of lifts -/

section Unpack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Y : Type v} [Category.{w} Y] (p : Y ⥤ BigFppfOver B S hS)
  {x : Y} {U W : BigFppfOver B S hS} (hx : p.obj x = U) (ν : U ⟶ W)
  (w : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ ν)))

/-- **The object a lift lies over.** Condition (iii) of [Stacks, Tag 07YX] asserts the
existence of a lift of `x` across a thickening `ν` as the non-emptiness of the fibre of
`CategoryTheory.Under.post p` over the arrow `ν`. An inhabitant of that fibre is an arrow
`x ⟶ x'` of the total category; this reads off the object `x'` lies over, which is the target
of `ν`.

This is the first half of the unpacking that the direction `(1) ⇒ (2)` of
[Stacks, Tag 07YM] performs on the lift that hypothesis (i) supplies: having obtained from
condition (iii) an inhabitant of the fibre, what the rest of the argument consumes is the
pair of an object of the total category and a proof that it lies over `Spec A'`. -/
public theorem lift_obj : p.obj w.1.right = W :=
  congrArg Comma.right w.2

/-- **The structure arrow of a lift lies over the thickening.** The second half of the
unpacking: the arrow `x ⟶ x'` carried by an inhabitant of the category of lifts lies over the
arrow `ν` of the site, which is what every statement about its underlying morphism of schemes
needs. -/
public instance isHomLift_lift_hom : p.IsHomLift ν w.1.hom := by
  refine IsHomLift.of_fac' p ν w.1.hom hx (lift_obj B S hS p hx ν w) ?_
  have hhom : p.map w.1.hom ≫ eqToHom (lift_obj B S hS p hx ν w) = eqToHom hx ≫ ν :=
    under_hom_comp_eqToHom w.2
  calc p.map w.1.hom
      = (p.map w.1.hom ≫ eqToHom (lift_obj B S hS p hx ν w)) ≫
          eqToHom (lift_obj B S hS p hx ν w).symm := by simp
    _ = (eqToHom hx ≫ ν) ≫ eqToHom (lift_obj B S hS p hx ν w).symm :=
        congrArg (fun t => t ≫ eqToHom (lift_obj B S hS p hx ν w).symm) hhom
    _ = eqToHom hx ≫ ν ≫ eqToHom (lift_obj B S hS p hx ν w).symm := Category.assoc _ _ _

/-- **The morphism of schemes underlying the structure arrow of a lift** is the one underlying
the thickening it lies over. Stated with the two identifications of the bases as arguments, so
that it can be used at whichever presentation over `S` the consumer carries. -/
public theorem schemeMap_lift_hom {Z W' : Over S}
    (hz : (p ⋙ Over.post B.inclusion).obj x = Z)
    (hw : (p ⋙ Over.post B.inclusion).obj w.1.right = W')
    (eZ : Z.left = (BigFppfOver.toScheme B S hS).obj U)
    (eW : (BigFppfOver.toScheme B S hS).obj W = W'.left) :
    schemeMap (p ⋙ Over.post B.inclusion) hz hw w.1.hom =
      eqToHom eZ ≫ (BigFppfOver.toScheme B S hS).map ν ≫ eqToHom eW :=
  schemeMap_eq_of_isHomLift B S hS p ν w.1.hom hz hw eZ eW

end Unpack

/-! ### Reading a ring map off a morphism of affine schemes -/

section ReadOff

variable {A C : Type u} [CommRing A] [CommRing C]

/-- The ring map `A → C` underlying a morphism of schemes `Spec C ⟶ Spec A`: the functor
`Scheme.Spec` is fully faithful, so every such morphism is the spectrum of a unique map of
rings. -/
public def ringHom_of_schemeMap (g : Spec (.of C) ⟶ Spec (.of A)) : A →+* C :=
  (Scheme.Spec.preimage g).unop.hom

/-- The spectrum of the ring map read off a morphism of affine schemes is that morphism. -/
@[simp] public theorem specMap_ringHom_of_schemeMap (g : Spec (.of C) ⟶ Spec (.of A)) :
    Spec.map (CommRingCat.ofHom (ringHom_of_schemeMap g)) = g :=
  Scheme.Spec.map_preimage g

/-- Two morphisms of affine schemes with the same underlying ring map are equal. -/
public theorem ringHom_of_schemeMap_injective {g g' : Spec (.of C) ⟶ Spec (.of A)}
    (h : ringHom_of_schemeMap g = ringHom_of_schemeMap g') : g = g' := by
  rw [← specMap_ringHom_of_schemeMap g, ← specMap_ringHom_of_schemeMap g', h]

/-- The ring map read off the spectrum of a ring map is that ring map. -/
@[simp] public theorem ringHom_of_schemeMap_specMap (ψ : A →+* C) :
    ringHom_of_schemeMap (Spec.map (CommRingCat.ofHom ψ)) = ψ :=
  congrArg (fun t : (CommRingCat.of A ⟶ CommRingCat.of C)ᵒᵖ => t.unop.hom)
    (Scheme.Spec.preimage_map (CommRingCat.ofHom ψ).op)

variable (Λ : Type u) [CommRing Λ] [Algebra Λ A] [Algebra Λ C]

/-- **The `Λ`-algebra map underlying an arrow over `Spec Λ`.** A morphism of schemes
`Spec C ⟶ Spec A` whose composite with the structure morphism of `Spec A` over `Spec Λ` is the
structure morphism of `Spec C` is the spectrum of a `Λ`-algebra homomorphism `A →ₐ[Λ] C`.

This is the reader that the direction `(1) ⇒ (2)` of [Stacks, Tag 07YM] applies to the arrow
versality supplies: the base of that arrow lies over `S`, hence over the affine open
`Spec Λ ⟶ S` through which the two structure morphisms factor, and `Λ`-linearity is exactly
that factorization read through the faithfulness of `Scheme.Spec`. -/
public def algHom_of_schemeMap (g : Spec (.of C) ⟶ Spec (.of A))
    (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap Λ A)) =
      Spec.map (CommRingCat.ofHom (algebraMap Λ C))) : A →ₐ[Λ] C where
  toRingHom := ringHom_of_schemeMap g
  commutes' l := by
    have h : CommRingCat.ofHom (algebraMap Λ A) ≫
        CommRingCat.ofHom (ringHom_of_schemeMap g) =
        CommRingCat.ofHom (algebraMap Λ C) := by
      apply Spec.map_injective
      rw [Spec.map_comp, specMap_ringHom_of_schemeMap]
      exact hg
    exact congrArg (fun t : CommRingCat.of Λ ⟶ CommRingCat.of C => t.hom l) h

/-- The algebra map read off a morphism of affine schemes over `Spec Λ` is, as a ring map,
the one `Deformation.Artin.ringHom_of_schemeMap` reads off. -/
public theorem algHom_of_schemeMap_toRingHom (g : Spec (.of C) ⟶ Spec (.of A))
    (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap Λ A)) =
      Spec.map (CommRingCat.ofHom (algebraMap Λ C))) :
    (algHom_of_schemeMap Λ g hg).toRingHom = ringHom_of_schemeMap g := rfl

/-- The spectrum of the algebra map read off a morphism of affine schemes over `Spec Λ` is
that morphism. -/
@[simp] public theorem specMap_algHom_of_schemeMap (g : Spec (.of C) ⟶ Spec (.of A))
    (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap Λ A)) =
      Spec.map (CommRingCat.ofHom (algebraMap Λ C))) :
    Spec.map (CommRingCat.ofHom (algHom_of_schemeMap Λ g hg).toRingHom) = g :=
  specMap_ringHom_of_schemeMap g

end ReadOff

/-! ### Reading an algebra map off an arrow of the fibred category -/

section ReadOffArrow

variable {Λ A C : Type u} [CommRing Λ] [CommRing A] [CommRing C]
  [Algebra Λ A] [Algebra Λ C] {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S) [Mono iΛ]

/-- **The algebra map underlying an arrow over the base.** A morphism of schemes
`Spec C ⟶ Spec A` over `S` between two spectra whose structure morphisms both factor through a
*monomorphic* `Spec Λ ⟶ S` is the spectrum of a `Λ`-algebra homomorphism `A →ₐ[Λ] C`.

The monomorphism hypothesis is what turns "lies over `S`" into "lies over `Spec Λ`", and it is
the only thing the argument of [Stacks, Tag 07YM] uses of the affine open `Spec Λ ⟶ S` that
tag's hypotheses present as an open immersion. -/
public def algHom_of_schemeMap_over (g : Spec (.of C) ⟶ Spec (.of A))
    (hg : g ≫ (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) =
      Spec.map (CommRingCat.ofHom (algebraMap Λ C)) ≫ iΛ) : A →ₐ[Λ] C :=
  algHom_of_schemeMap Λ g ((cancel_mono iΛ).mp (by rw [Category.assoc]; exact hg))

/-- The spectrum of `Deformation.Artin.algHom_of_schemeMap_over` is the morphism it is read
off. -/
@[simp] public theorem specMap_algHom_of_schemeMap_over (g : Spec (.of C) ⟶ Spec (.of A))
    (hg : g ≫ (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) =
      Spec.map (CommRingCat.ofHom (algebraMap Λ C)) ≫ iΛ) :
    Spec.map (CommRingCat.ofHom (algHom_of_schemeMap_over iΛ g hg).toRingHom) = g :=
  specMap_ringHom_of_schemeMap g

variable (B : BigFppfSite.{u}) (hS : B.Contains S)
  {Y : Type v} [Category.{w} Y] (p : Y ⥤ BigFppfOver B S hS)

/-- A sanity check that the reader fits the arrow versality supplies. An arrow `b : z ⟶ x` of
the total category whose source lies over `Spec C` and whose target lies over `Spec A`, both
presented over `S` through `Spec Λ`, determines a `Λ`-algebra homomorphism `A →ₐ[Λ] C` whose
spectrum is the morphism of schemes `b` lies over: the compatibility
`Deformation.Artin.algHom_of_schemeMap_over` asks for is
`Deformation.Artin.schemeMap_over`, which holds of every arrow. -/
example {z x : Y}
    (hz : (p ⋙ Over.post B.inclusion).obj z =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ C)) ≫ iΛ))
    (hx : (p ⋙ Over.post B.inclusion).obj x =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ))
    (b : z ⟶ x) :
    ∃ σ : A →ₐ[Λ] C, Spec.map (CommRingCat.ofHom σ.toRingHom) =
      schemeMap (p ⋙ Over.post B.inclusion) hz hx b :=
  ⟨algHom_of_schemeMap_over iΛ _
      (schemeMap_over (p ⋙ Over.post B.inclusion) hz hx b),
    specMap_algHom_of_schemeMap_over iΛ _ _⟩

end ReadOffArrow

end Deformation.Artin
