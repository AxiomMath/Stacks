module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.Main
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoAffineCover
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoAtlasReduction
public import StacksFrontier.AlgebraicGeometry.Thickenings.SquareZeroPerturbation
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.StalkReflectsUnits
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.ToposHomUnitsSquare

/-!
# Isomorphisms of small étale ringed topoi of algebraic spaces

Stacks 05YZ says that an isomorphism

```
  (g, g♯) : (Sh(X_étale), 𝒪_X) ⟶ (Sh(Y_étale), 𝒪_Y)
```

of the small étale ringed topoi of two algebraic spaces over `ℤ` comes from a unique morphism
`f : X ⟶ Y` of algebraic spaces, in the sense that `(g, g♯)` is 2-isomorphic to
`(f_small, f♯)`, and that `f` is an isomorphism of algebraic spaces.  Its proof is two steps:
*first* that `(g, g♯)` is a morphism of **locally** ringed topoi, which the source settles by
Stacks 04H9 ("as it is an isomorphism this is clear"), and *then* Stacks 04KL, which recovers
`f` from a locally ringed morphism of small étale ringed topoi.  The source leaves the last
clause implicit; here it is Stacks 04KL applied to the inverse of `(g, g♯)`, together with the
uniqueness of Stacks 04M6.

The first step needs nothing about étale sites, algebraic spaces or points.  By Stacks 04HA the
assertion is that the square

```
  g⁻¹(𝒪_Y^*) ---> 𝒪_X^*
      |             |
      v             v
  g⁻¹(𝒪_Y)  ---> 𝒪_X
```

of units subsheaves is cartesian, and by Stacks 04KR that square is the units square of the
morphism `g⁻¹𝒪_Y ⟶ 𝒪_X` of sheaves of commutative rings on the site of `X`.  When that
morphism is an isomorphism so are both horizontal maps of the square, and a commuting square
whose two horizontal maps are isomorphisms is cartesian.

For the last clause, let `f'` be the morphism inducing the inverse `g'` of `(g, g♯)`.  The round
trip `g ∘ g'` is 2-isomorphic to `(𝟙 Y)_small` — its direct image is identified with the
identity functor by the unit of `g⁻¹ ⊣ g_*`, and its structure map is that unit — while
pasting the two given 2-isomorphisms with the composition law of Stacks 03G8 makes it
2-isomorphic to `(f' ≫ f)_small`.  By Stacks 04M6, `f' ≫ f = 𝟙 Y`.  The same argument for `g'`
and its inverse gives a left inverse of `f'`, so `f'` is invertible with inverse `f`.

## Main results

* `AlgebraicGeometry.RingedTopos.isPullback_unitsSquare_of_isIso`: the units square of an
  isomorphism of sheaves of commutative rings is cartesian.
* `AlgebraicGeometry.RingedToposHom.isLocallyRinged_of_isIso_fSharpInverseImage`: a morphism of
  ringed topoi whose inverse-image structure map `g⁻¹𝒪_Y ⟶ 𝒪_X` is an isomorphism is locally
  ringed.
* `AlgebraicGeometry.RingedToposHom.isLocallyRinged_of_isEquivalence_of_isIso_fSharp`: the same
  with the hypothesis in the shape "`(g, g♯)` is an isomorphism of ringed topoi", namely that
  the direct image is an equivalence and `g♯` is an isomorphism.
* `AlgebraicGeometry.Space.isLocallyRinged_of_smallEtaleRingedToposIso`: that statement at the
  small étale ringed topoi of two algebraic spaces.
* `AlgebraicGeometry.Space.compInverseTwoIso`: the round trip along an isomorphism of small
  étale ringed topoi is 2-isomorphic to the morphism of small étale ringed topoi of `𝟙 Y`.
* `AlgebraicGeometry.Space.isIso_of_twoIso_of_inverse`: a morphism of algebraic spaces inducing
  an isomorphism of small étale ringed topoi whose inverse (and the inverse of that) is induced
  by a morphism of algebraic spaces is an isomorphism.
* `AlgebraicGeometry.Space.existsUnique_spaceHom_twoIso_of_smallEtaleRingedToposIso`:
  **Stacks 05YZ**.

## The sections-to-fibres bridge for a perturbed structure map

The transfer theorem
`AlgebraicGeometry.RingedToposHom.isLocallyRinged_of_isNilpotent_sub_fSharpInverseImage` — a
morphism of ringed topoi whose structure map differs by a nilpotent from one which reflects
units is locally ringed — reads its nilpotency hypothesis at the **fibres** of the points of the
site, while a square-zero perturbation of a structure map (Stacks 0618, Stacks 04D0) presents
itself at the **sections**.  The following close that gap.

* `AlgebraicGeometry.RingedTopos.isNilpotent_sub_sheafFiber_map_of_sections`: **the bridge.**
  Two morphisms of sheaves of commutative rings whose difference is nilpotent on every section
  have fibres whose difference is nilpotent on every element, at every point of the site.  Every
  element of the fibre is a germ, the fibre of a morphism carries a germ to the germ of the image
  section, and the germ map is a ring homomorphism, so the difference of the fibre values is the
  germ of the difference of the section values.
* `AlgebraicGeometry.RingedTopos.reflectsUnitsObj_sheafFiber_of_isNilpotent_sub_sections`: the
  reflection-of-units transfer at one point with its hypothesis at the sections.
* `AlgebraicGeometry.RingedTopos.isNilpotent_sub_app_apply_of_forgetCommRingSheaf`: the same
  hypothesis read on the underlying sheaves of rings, where the square-zero machinery proves it.
* `AlgebraicGeometry.RingedToposHom.isLocallyRinged_of_isNilpotent_sub_sections_family`,
  `AlgebraicGeometry.RingedToposHom.isLocallyRinged_of_isNilpotent_sub_ringSections_family` and
  `AlgebraicGeometry.RingedToposHom.isLocallyRinged_of_sq_eq_zero_sub_sections_family`: the
  transfer theorem with its nilpotency hypothesis at the sections — of sheaves of commutative
  rings, of the underlying sheaves of rings, and in the square-zero form respectively — and with
  the points ranging over an arbitrary indexed **family** rather than over all points of the
  site.  The family-indexed form is what admits a discharged conservativity hypothesis.
* `AlgebraicGeometry.Space.isLocallyRinged_of_isNilpotent_sub_sections_smallEtale`: that
  statement at the small étale ringed topoi of two algebraic spaces, with the conservativity
  hypothesis **discharged** by `AlgebraicGeometry.Space.isConservativeFamily_etaleSitePoint`.

The square-zero form is the one Stacks 0618 and Stacks 04D0 supply: the difference of a
structure map and its modification by a derivation is `ι ∘ D ∘ q`, a section of a square-zero
ideal, by `Stacks.Sites.derivationActionHom_app_apply`, and its nilpotency is
`Stacks.Sites.isNilpotent_sub_derivationActionHom_app_apply`.  What is *not* done here is the
instantiation at `AlgebraicGeometry.Space.conormalSourceDerivationActionHom`: the conormal ideal
is an ideal of `i^{-1}𝒪_{X'}` on the small étale site of the closed subspace `X`, so using it as
an ideal of the structure sheaf of a ringed topos asks for that pair to be presented as
`(Sh(X'_étale), 𝒪_{X'})`, which is the content of Stacks 05ZM
(`AlgebraicGeometry.Space.thickeningFundamentalHom` and
`AlgebraicGeometry.Space.isIso_thickeningFundamentalHom_fSharp`) and is not transported here.
That transport is
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/ConormalAmbientSquareZeroValues.lean`, which
carries the conormal ideal onto the site of `X'` and instantiates
`AlgebraicGeometry.Space.isLocallyRinged_of_isNilpotent_sub_sections_smallEtale` at it.

## Implementation notes

`AlgebraicGeometry.RingedTopos.unitsMapOf` is made functorial first
(`AlgebraicGeometry.RingedTopos.unitsMapOf_id` and
`AlgebraicGeometry.RingedTopos.unitsMapOf_comp`, both of which hold on sections), so that it
carries an isomorphism to an isomorphism.

An isomorphism of ringed topoi is spelled, as everywhere in this development, as a morphism of
ringed topoi whose direct image is an equivalence and whose structure map `g♯` is an
isomorphism; its inverse is `AlgebraicGeometry.RingedToposHom.inverse`.  Stacks states 05YZ for
algebraic spaces over `ℤ`, i.e. over the terminal scheme `Spec (ULift ℤ)` of the big fppf site,
and this matters: over a general base `S` an automorphism of `S` induces an isomorphism of
small étale ringed topoi that is not induced by any morphism over `S`.

## References

* [Stacks Project, Tag 05YZ](https://stacks.math.columbia.edu/tag/05YZ)
* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
* [Stacks Project, Tag 04M6](https://stacks.math.columbia.edu/tag/04M6)
* [Stacks Project, Tag 04H9](https://stacks.math.columbia.edu/tag/04H9)
* [Stacks Project, Tag 04HA](https://stacks.math.columbia.edu/tag/04HA)
* [Stacks Project, Tag 04KR](https://stacks.math.columbia.edu/tag/04KR)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u v' u'

namespace AlgebraicGeometry.RingedTopos

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O₁ O₂ O₃ : Sheaf J CommRingCat.{w}}

/-- The map of units subsheaves induced by the identity is the identity. -/
theorem unitsMapOf_id (O : Sheaf J CommRingCat.{w}) :
    unitsMapOf (𝟙 O) = 𝟙 (unitsOf O) :=
  Sheaf.hom_ext_sections fun _ _ ↦ Units.ext rfl

/-- The map of units subsheaves induced by a composite is the composite of the induced maps. -/
theorem unitsMapOf_comp (φ : O₁ ⟶ O₂) (ψ : O₂ ⟶ O₃) :
    unitsMapOf (φ ≫ ψ) = unitsMapOf φ ≫ unitsMapOf ψ :=
  Sheaf.hom_ext_sections fun _ _ ↦ Units.ext rfl

/-- **An isomorphism of sheaves of commutative rings induces an isomorphism of their units
subsheaves.** The inverse is the map induced by the inverse. -/
instance isIso_unitsMapOf (φ : O₁ ⟶ O₂) [IsIso φ] : IsIso (unitsMapOf φ) :=
  ⟨unitsMapOf (inv φ), by
      rw [← unitsMapOf_comp, IsIso.hom_inv_id, unitsMapOf_id], by
      rw [← unitsMapOf_comp, IsIso.inv_hom_id, unitsMapOf_id]⟩

/-- **The units square of an isomorphism of sheaves of commutative rings is cartesian.** Both
horizontal maps of the square are isomorphisms, and a commuting square whose two horizontal
maps are isomorphisms is cartesian. -/
theorem isPullback_unitsSquare_of_isIso (φ : O₁ ⟶ O₂) [IsIso φ] :
    IsPullback (unitsMapOf φ) (unitsιOf O₁) (unitsιOf O₂) (forgetRingMap φ) :=
  IsPullback.of_horiz_isIso ⟨unitsMapOf_comp_unitsιOf φ⟩

section NilpotentSub

variable [LocallySmall.{w} C] [J.HasSheafCompose (forget RingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- **Reflection of units at a point is unchanged by a nilpotent perturbation of the map.** If
two morphisms `φ, ψ : O₁ ⟶ O₂` of sheaves of commutative rings have fibres at `Φ` differing by
a nilpotent on every element, and the fibre functor of `Φ` reflects units for `φ`, then it
reflects units for `ψ` as well.

Nothing is proved here.  Reflection of units by the set-valued fibre functor is locality of the
fibre ring map, in both directions, by
`AlgebraicGeometry.RingedTopos.isLocalHom_sheafFiber_iff_reflectsUnitsObj`; and a ring map
differing from a local one by nilpotents is local, by
`Stacks.Thickenings.SquareZeroPerturbation.isLocalHom_of_isNilpotent_sub`, whose content is that
a unit plus a nilpotent is a unit.  The statement is the composite of those two, and it is the
form in which "a map agreeing with a locally ringed one modulo a square-zero ideal is locally
ringed" is available at a point of a site: a square-zero section is nilpotent with exponent 2.

The hypothesis is read on the *fibres*, not on the sections.  Deducing it from a sectionwise
square-zero condition needs every element of the fibre to be a germ and the fibre ring structure
to be the transported one; neither step is taken here. -/
theorem reflectsUnitsObj_sheafFiber_of_isNilpotent_sub (Φ : J.Point.{w}) (φ ψ : O₁ ⟶ O₂)
    (hnil : ∀ a, IsNilpotent (((Φ.sheafFiber (A := CommRingCat.{w})).map φ).hom a -
      ((Φ.sheafFiber (A := CommRingCat.{w})).map ψ).hom a))
    (h : ReflectsUnitsObj (Φ.sheafFiber (A := Type w)) φ) :
    ReflectsUnitsObj (Φ.sheafFiber (A := Type w)) ψ :=
  reflectsUnitsObj_sheafFiber_of_isLocalHom Φ ψ
    (Stacks.Thickenings.SquareZeroPerturbation.isLocalHom_of_isNilpotent_sub
      ((Φ.sheafFiber (A := CommRingCat.{w})).map φ).hom
      ((Φ.sheafFiber (A := CommRingCat.{w})).map ψ).hom hnil
      (isLocalHom_sheafFiber_of_reflectsUnitsObj Φ φ h))

omit [J.HasSheafCompose (forget RingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **Nilpotency of the difference of two morphisms of sheaves of commutative rings at a fibre,
from nilpotency at the sections.**  If `φ, ψ : O₁ ⟶ O₂` differ by a nilpotent on every section
over every object of the site, then their fibres at every point of the site differ by a
nilpotent on every element of the fibre.

This is the bridge the fibre-level transfer theorems need.  Every element of the fibre is a germ
(`CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_jointly_surjective`, applicable
because the forgetful functor of commutative rings preserves filtered colimits), the fibre of a
morphism carries a germ to the germ of the image section
(`CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_naturality`), and the germ map is a
ring homomorphism, so the difference of the two fibre values is the germ of the difference of the
two section values, which is nilpotent with the same exponent. -/
theorem isNilpotent_sub_sheafFiber_map_of_sections (Φ : J.Point.{w}) (φ ψ : O₁ ⟶ O₂)
    (hnil : ∀ (V : Cᵒᵖ) (x : ToType (O₁.obj.obj V)),
      IsNilpotent (φ.hom.app V x - ψ.hom.app V x))
    (a : ↥((Φ.sheafFiber (A := CommRingCat.{w})).obj O₁)) :
    IsNilpotent (((Φ.sheafFiber (A := CommRingCat.{w})).map φ).hom a -
      ((Φ.sheafFiber (A := CommRingCat.{w})).map ψ).hom a) := by
  obtain ⟨U, z, p, hp⟩ := Φ.toPresheafFiber_jointly_surjective (P := O₁.obj)
    (show ToType ((Φ.presheafFiber (A := CommRingCat.{w})).obj O₁.obj) from a)
  subst hp
  show IsNilpotent
      (((Φ.presheafFiber (A := CommRingCat.{w})).map φ.hom).hom
          ((Φ.toPresheafFiber U z O₁.obj).hom p) -
        ((Φ.presheafFiber (A := CommRingCat.{w})).map ψ.hom).hom
          ((Φ.toPresheafFiber U z O₁.obj).hom p))
  have h : ∀ χ : O₁ ⟶ O₂, ((Φ.presheafFiber (A := CommRingCat.{w})).map χ.hom).hom
        ((Φ.toPresheafFiber U z O₁.obj).hom p) =
      (Φ.toPresheafFiber U z O₂.obj).hom ((χ.hom.app (Opposite.op U)).hom p) := fun χ ↦
    ConcreteCategory.congr_hom (Φ.toPresheafFiber_naturality χ.hom U z) p
  rw [h φ, h ψ, ← map_sub]
  exact (hnil (Opposite.op U) p).map (Φ.toPresheafFiber U z O₂.obj).hom

/-- **Reflection of units at a point is unchanged by a perturbation which is nilpotent on
sections.**  The hypothesis of
`AlgebraicGeometry.RingedTopos.reflectsUnitsObj_sheafFiber_of_isNilpotent_sub` read at the
sections rather than at the fibres, which is the form in which a square-zero perturbation of a
morphism of sheaves of rings presents itself. -/
theorem reflectsUnitsObj_sheafFiber_of_isNilpotent_sub_sections (Φ : J.Point.{w})
    (φ ψ : O₁ ⟶ O₂)
    (hnil : ∀ (V : Cᵒᵖ) (x : ToType (O₁.obj.obj V)),
      IsNilpotent (φ.hom.app V x - ψ.hom.app V x))
    (h : ReflectsUnitsObj (Φ.sheafFiber (A := Type w)) φ) :
    ReflectsUnitsObj (Φ.sheafFiber (A := Type w)) ψ :=
  reflectsUnitsObj_sheafFiber_of_isNilpotent_sub Φ φ ψ
    (isNilpotent_sub_sheafFiber_map_of_sections Φ φ ψ hnil) h

omit [J.HasSheafCompose (forget RingCat.{w})] [LocallySmall.{w} C] in
/-- **Nilpotency of the difference on sections is unchanged by forgetting commutativity.**  The
sections of a morphism of sheaves of commutative rings and of its underlying morphism of sheaves
of rings are the same function of the same sections, so the two readings of the hypothesis
"the difference is nilpotent on sections" are one statement.

This is the step that lets `Stacks.Sites.isNilpotent_sub_derivationActionHom_app_apply`, which is
proved for a morphism of sheaves of **rings**, discharge the hypothesis of
`AlgebraicGeometry.RingedToposHom.isLocallyRinged_of_isNilpotent_sub_sections_family`, which is
read on sheaves of **commutative** rings. -/
theorem isNilpotent_sub_app_apply_of_forgetCommRingSheaf (φ ψ : O₁ ⟶ O₂) (V : Cᵒᵖ)
    (x : ToType (O₁.obj.obj V))
    (h : IsNilpotent (((Stacks.forgetCommRingSheaf J).map φ).hom.app V x -
      ((Stacks.forgetCommRingSheaf J).map ψ).hom.app V x)) :
    IsNilpotent (φ.hom.app V x - ψ.hom.app V x) := h

end NilpotentSub

end AlgebraicGeometry.RingedTopos

namespace AlgebraicGeometry.RingedToposHom

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget CommRingCat.{w})]
  [Y.J.HasSheafCompose (forget CommRingCat.{w})]
  (f : RingedToposHom X Y)

/-- **A morphism of ringed topoi whose inverse-image structure map `f⁻¹𝒪_Y ⟶ 𝒪_X` is an
isomorphism is a morphism of locally ringed topoi.**

By Stacks 04KR the units square of Stacks 04HA is the units square of that morphism of sheaves
of commutative rings on the site of the source, and
`AlgebraicGeometry.RingedTopos.isPullback_unitsSquare_of_isIso` makes the latter cartesian.
Nothing is assumed of the underlying morphism of topoi. -/
theorem isLocallyRinged_of_isIso_fSharpInverseImage [IsIso f.fSharpInverseImage] :
    f.IsLocallyRinged := by
  have hsq := RingedTopos.isPullback_unitsSquare_of_isIso f.fSharpInverseImage
  refine ⟨f.unitsComparison.hom ≫ RingedTopos.unitsMapOf f.fSharpInverseImage, ?_⟩
  refine hsq.of_iso f.unitsComparison.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).trans (Iso.inv_hom_id_assoc _ _).symm
  · exact (Category.comp_id _).trans (unitsComparison_inv_comp f).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans
      ((forgetRing_map_fSharpInverseImage_eq_fSharpSet f).trans (Category.id_comp _).symm)

/-- **An isomorphism of ringed topoi is a morphism of locally ringed topoi.** The hypothesis is
that `(f, f♯)` is invertible: the direct image is an equivalence and `f♯ : 𝒪_Y ⟶ f_*𝒪_X` is an
isomorphism.  Then so is its inverse-image form `f⁻¹𝒪_Y ⟶ 𝒪_X`, by
`AlgebraicGeometry.RingedToposHom.isIso_fSharpInverseImage`, and
`AlgebraicGeometry.RingedToposHom.isLocallyRinged_of_isIso_fSharpInverseImage` applies. -/
theorem isLocallyRinged_of_isEquivalence_of_isIso_fSharp
    [f.toToposHom.pushforward.IsEquivalence] [IsIso f.fSharp] :
    f.IsLocallyRinged :=
  isLocallyRinged_of_isIso_fSharpInverseImage f

/-- **A morphism of ringed topoi whose structure map differs by a nilpotent from one which
reflects units is locally ringed.**  Let `g : X ⟶ Y` be a morphism of ringed topoi and let `φ`
be a second morphism `g⁻¹𝒪_Y ⟶ 𝒪_X` of sheaves of commutative rings on the site of `X` — the
*unperturbed* structure map, read on the same site and along the same morphism of topoi, as it
is for a structure map modified by a derivation.  If the fibre functor at every point of the
site of `X` reflects units for `φ`, and at every point the two fibre ring maps differ by a
nilpotent, then `g` is locally ringed.

This transfer is not otherwise available: Stacks 04HA is a condition on the *units square*,
and the only other morphism-level transfer,
`AlgebraicGeometry.RingedToposHom.isLocallyRinged_of_isIso_fSharpInverseImage`, needs the
structure map to be an isomorphism, which a perturbed one is not.  The content is that a unit
plus a nilpotent is a unit, read at the fibres; a section of a square-zero ideal is nilpotent
with exponent 2, so this covers the square-zero case.

The hypothesis `hφ` is what `AlgebraicGeometry.RingedToposHom.reflectsUnitsObj_of_isLocallyRinged`
supplies from a locally ringed morphism whose underlying morphism of topoi is the *same term* as
`g.toToposHom`; for two morphisms of ringed topoi whose underlying morphisms of topoi are merely
equal the two spellings of `g⁻¹𝒪_Y` differ, and no transport is made here.  `hcons` is the
conservativity of the family of all points of the site of `X`, taken as a hypothesis in the form
it is used, as in `AlgebraicGeometry.RingedTopos.isPullback_unitsSquare_of_family`. -/
@[sga "4 IV 13.9" "c)"]
theorem isLocallyRinged_of_isNilpotent_sub_fSharpInverseImage [LocallySmall.{w} X.C]
    (φ : (Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor
        f.toToposHom).obj Y.O ⟶ X.O)
    (hφ : ∀ Φ : X.J.Point.{w},
      RingedTopos.ReflectsUnitsObj (Φ.sheafFiber (A := Type w)) φ)
    (hnil : ∀ (Φ : X.J.Point.{w}) a,
      IsNilpotent (((Φ.sheafFiber (A := CommRingCat.{w})).map φ).hom a -
        ((Φ.sheafFiber (A := CommRingCat.{w})).map f.fSharpInverseImage).hom a))
    [HasPullback (RingedTopos.unitsιOf X.O)
      (RingedTopos.forgetRingMap f.fSharpInverseImage)]
    (hcons : ∀ {F G : Sheaf X.J (Type w)} (θ : F ⟶ G),
      (∀ Φ : X.J.Point.{w}, IsIso ((Φ.sheafFiber (A := Type w)).map θ)) → IsIso θ) :
    f.IsLocallyRinged :=
  isLocallyRinged_of_reflectsUnitsObj f (fun Φ : X.J.Point.{w} ↦ Φ.sheafFiber (A := Type w))
    (fun _ ↦ inferInstance) hcons
    fun Φ ↦ RingedTopos.reflectsUnitsObj_sheafFiber_of_isNilpotent_sub Φ φ
      f.fSharpInverseImage (hnil Φ) (hφ Φ)

/-- **A morphism of ringed topoi whose structure map differs by a nilpotent *on sections* from
one which reflects units at a conservative family of points is locally ringed.**

This is `AlgebraicGeometry.RingedToposHom.isLocallyRinged_of_isNilpotent_sub_fSharpInverseImage`
with its two point-indexed hypotheses moved to the form in which they are actually available:
the nilpotency is read at the **sections**, where a square-zero perturbation of a structure map
presents itself, and the points range over an arbitrary indexed **family** rather than over all
points of the site, so that a proved conservativity statement for a specific family — for the
small étale site of an algebraic space, the geometric points — can discharge `hcons`.

The passage from sections to fibres is
`AlgebraicGeometry.RingedTopos.isNilpotent_sub_sheafFiber_map_of_sections`; note that the
sections hypothesis does not mention the point, so one hypothesis serves every member of the
family.

**No `@[stacks]` attribute.**  This is a step inside the proof of [Stacks Project, Tag 04HA]
rather than a clause of it at the tag's own hypotheses: it carries the unperturbed structure map
`φ` and its units reflection, the nilpotency of the difference, a `HasPullback` instance for the
units square, and the conservativity of the chosen family. -/
@[sga "4 IV 13.9" "c)"]
theorem isLocallyRinged_of_isNilpotent_sub_sections_family [LocallySmall.{w} X.C]
    {ι : Type*} (pt : ι → X.J.Point.{w})
    (φ : (Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor
        f.toToposHom).obj Y.O ⟶ X.O)
    (hφ : ∀ i, RingedTopos.ReflectsUnitsObj ((pt i).sheafFiber (A := Type w)) φ)
    (hnil : ∀ (V : X.Cᵒᵖ) (x : ToType
        (((Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor
          f.toToposHom).obj Y.O).obj.obj V)),
      IsNilpotent (φ.hom.app V x - f.fSharpInverseImage.hom.app V x))
    [HasPullback (RingedTopos.unitsιOf X.O)
      (RingedTopos.forgetRingMap f.fSharpInverseImage)]
    (hcons : ∀ {F G : Sheaf X.J (Type w)} (θ : F ⟶ G),
      (∀ i, IsIso (((pt i).sheafFiber (A := Type w)).map θ)) → IsIso θ) :
    f.IsLocallyRinged :=
  isLocallyRinged_of_reflectsUnitsObj f (fun i ↦ (pt i).sheafFiber (A := Type w))
    (fun _ ↦ inferInstance) hcons
    fun i ↦ RingedTopos.reflectsUnitsObj_sheafFiber_of_isNilpotent_sub_sections (pt i) φ
      f.fSharpInverseImage hnil (hφ i)

/-- **The same with the nilpotency read on the underlying sheaves of rings.**  The sections of a
morphism of sheaves of commutative rings and of the underlying morphism of sheaves of rings are
the same function, so this is the same hypothesis; it is stated separately because the
square-zero machinery of
`StacksFrontier/AlgebraicGeometry/Spaces/LiftDifferenceDescent.lean` — in particular
`Stacks.Sites.isNilpotent_sub_derivationActionHom_app_apply`, which is what a structure map
modified by a derivation into a square-zero ideal supplies — is proved for morphisms of sheaves
of **rings**, whose source and target here are
`Stacks.SheafOfModules.Tensor.ringSheaf ((f⁻¹ applied to) Y.O)` and
`Stacks.SheafOfModules.Tensor.ringSheaf X.O`.  The first of
those is the inverse image of sheaves of rings on the nose, by
`Stacks.Sheaves.ToposPullback.forgetCommRingSheaf_pullbackCommRingSheaf`.

No `@[stacks]` attribute, for the reasons recorded on
`AlgebraicGeometry.RingedToposHom.isLocallyRinged_of_isNilpotent_sub_sections_family`. -/
theorem isLocallyRinged_of_isNilpotent_sub_ringSections_family [LocallySmall.{w} X.C]
    {ι : Type*} (pt : ι → X.J.Point.{w})
    (φ : (Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor
        f.toToposHom).obj Y.O ⟶ X.O)
    (hφ : ∀ i, RingedTopos.ReflectsUnitsObj ((pt i).sheafFiber (A := Type w)) φ)
    (hnil : ∀ (V : X.Cᵒᵖ) (x : ToType ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)
        ((Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor
          f.toToposHom).obj Y.O)).obj.obj V)),
      IsNilpotent (((Stacks.forgetCommRingSheaf X.J).map φ).hom.app V x -
        ((Stacks.forgetCommRingSheaf X.J).map f.fSharpInverseImage).hom.app V x))
    [HasPullback (RingedTopos.unitsιOf X.O)
      (RingedTopos.forgetRingMap f.fSharpInverseImage)]
    (hcons : ∀ {F G : Sheaf X.J (Type w)} (θ : F ⟶ G),
      (∀ i, IsIso (((pt i).sheafFiber (A := Type w)).map θ)) → IsIso θ) :
    f.IsLocallyRinged :=
  isLocallyRinged_of_isNilpotent_sub_sections_family f pt φ hφ
    (fun V x ↦ RingedTopos.isNilpotent_sub_app_apply_of_forgetCommRingSheaf φ
      f.fSharpInverseImage V x (hnil V x)) hcons

/-- **A morphism of ringed topoi whose structure map agrees with a units-reflecting one modulo a
square-zero ideal is locally ringed.**  A section of a square-zero ideal is nilpotent with
exponent two, so this is
`AlgebraicGeometry.RingedToposHom.isLocallyRinged_of_isNilpotent_sub_sections_family` at the
hypothesis in which the square-zero condition of [Stacks Project, Tag 0618] and
[Stacks Project, Tag 04D0] presents itself.  No `@[stacks]` attribute, for the reasons recorded
there. -/
theorem isLocallyRinged_of_sq_eq_zero_sub_sections_family [LocallySmall.{w} X.C]
    {ι : Type*} (pt : ι → X.J.Point.{w})
    (φ : (Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor
        f.toToposHom).obj Y.O ⟶ X.O)
    (hφ : ∀ i, RingedTopos.ReflectsUnitsObj ((pt i).sheafFiber (A := Type w)) φ)
    (hsq : ∀ (V : X.Cᵒᵖ) (x : ToType
        (((Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor
          f.toToposHom).obj Y.O).obj.obj V)),
      (φ.hom.app V x - f.fSharpInverseImage.hom.app V x) ^ 2 = 0)
    [HasPullback (RingedTopos.unitsιOf X.O)
      (RingedTopos.forgetRingMap f.fSharpInverseImage)]
    (hcons : ∀ {F G : Sheaf X.J (Type w)} (θ : F ⟶ G),
      (∀ i, IsIso (((pt i).sheafFiber (A := Type w)).map θ)) → IsIso θ) :
    f.IsLocallyRinged :=
  isLocallyRinged_of_isNilpotent_sub_sections_family f pt φ hφ
    (fun V x ↦ ⟨2, hsq V x⟩) hcons

end AlgebraicGeometry.RingedToposHom

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **An isomorphism of small étale ringed topoi is a morphism of locally ringed topoi.** An
isomorphism `(g, g♯) : (Sh(X_étale), 𝒪_X) ⟶ (Sh(Y_étale), 𝒪_Y)` of the small étale ringed topoi
of two algebraic spaces has a cartesian square of units subsheaves.

This is the step the proof of Stacks 05YZ discharges with Stacks 04H9 and the words "as it is
an isomorphism this is clear": the hypothesis on `g♯` makes `g⁻¹𝒪_Y ⟶ 𝒪_X` an isomorphism,
and then both horizontal maps of the units square are isomorphisms. -/
theorem isLocallyRinged_of_smallEtaleRingedToposIso
    (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    [g.toToposHom.pushforward.IsEquivalence] [IsIso g.fSharp] :
    g.IsLocallyRinged :=
  RingedToposHom.isLocallyRinged_of_isEquivalence_of_isIso_fSharp g

/-- **A morphism of the small étale ringed topoi of two algebraic spaces whose structure map
differs on sections by a nilpotent from one which reflects units at the geometric points is
locally ringed.**

This is
`AlgebraicGeometry.RingedToposHom.isLocallyRinged_of_isNilpotent_sub_sections_family` at the
small étale site of an algebraic space, where the conservativity hypothesis `hcons` **is
discharged** rather than carried: the geometric points of an algebraic space are a conservative
family of points of its small étale site, by
`AlgebraicGeometry.Space.isConservativeFamily_etaleSitePoint`.  That is why the family-indexed
form of the transfer theorem is the one proved: conservativity is proved for the geometric-point
family, not for the family of *all* points of the site.

The hypothesis `hφ` is what
`AlgebraicGeometry.RingedToposHom.reflectsUnitsObj_of_isLocallyRinged` supplies at each
`AlgebraicGeometry.Space.etaleSitePoint` from a locally ringed morphism of ringed topoi whose
underlying morphism of topoi is the *same term* as `g.toToposHom`; the fibre functor of a point
of a site is left exact, which is the instance that step needs.

**No `@[stacks]` attribute.**  Beyond the hypotheses of [Stacks Project, Tag 04HA] this carries
the unperturbed structure map `φ` with its units reflection, the nilpotency of the difference on
sections, and a `HasPullback` instance for the units square. -/
@[sga "4 IV 13.9" "(ii) ⇒ (i), special case"]
theorem isLocallyRinged_of_isNilpotent_sub_sections_smallEtale
    (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    (φ : (Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor g.toToposHom).obj
        (smallEtaleRingedTopos B S hS Y).O ⟶ (smallEtaleRingedTopos B S hS X).O)
    (hφ : ∀ x : GeometricPoint B S hS X.1,
      RingedTopos.ReflectsUnitsObj
        ((etaleSitePoint B S hS X.1 x X.2).sheafFiber (A := Type u)) φ)
    (hnil : ∀ (V : (SmallEtale B S hS X.1)ᵒᵖ) (s : ToType
        (((Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor
          g.toToposHom).obj (smallEtaleRingedTopos B S hS Y).O).obj.obj V)),
      IsNilpotent (φ.hom.app V s - g.fSharpInverseImage.hom.app V s))
    [HasPullback (RingedTopos.unitsιOf (smallEtaleRingedTopos B S hS X).O)
      (RingedTopos.forgetRingMap g.fSharpInverseImage)] :
    g.IsLocallyRinged :=
  RingedToposHom.isLocallyRinged_of_isNilpotent_sub_sections_family g
    (fun x ↦ etaleSitePoint B S hS X.1 x X.2) φ hφ hnil
    fun θ h ↦ isConservativeFamily_etaleSitePoint B S hS X.1 X.2 θ h

/-! ### The inverse of an isomorphism of small étale ringed topoi -/

section Inverse

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

/-- **The round trip `Y ⟶ X ⟶ Y` along an isomorphism of small étale ringed topoi is
2-isomorphic to the morphism of small étale ringed topoi of `𝟙 Y`.** Its direct image is
`g⁻¹ ⋙ g_*`, identified with the identity functor by the unit of `g⁻¹ ⊣ g_*`, and that with the
direct image along `𝟙 Y` by `AlgebraicGeometry.Space.smallEtaleDirectImageIdIso`; the structure
map of the round trip is the unit
(`AlgebraicGeometry.RingedToposHom.forgetRing_map_comp_inverse_fSharp`) and that of `𝟙 Y` is the
identification `AlgebraicGeometry.Space.structureSharpSet_id`. -/
noncomputable def compInverseTwoIso
    (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    [g.toToposHom.pushforward.IsEquivalence] [IsIso g.fSharp] :
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u} g g.inverse)
      (smallEtaleRingedToposHom B S hS (𝟙 Y)) where
  e := (asIso g.toToposHom.adj.unit).symm ≪≫ (smallEtaleDirectImageIdIso B S hS Y).symm
  commutes := by
    have h₁ : RingedToposHom.forgetFSharp
        (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u} g g.inverse) =
        g.toToposHom.adj.unit.app _ :=
      RingedToposHom.forgetRing_map_comp_inverse_fSharp g
    have h₂ : RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B S hS (𝟙 Y)) =
        (smallEtaleDirectImageIdIso B S hS Y).inv.app (structureSetSheaf B S hS Y) :=
      (forgetRing_map_fSharp B S hS (𝟙 Y)).trans (structureSharpSet_id B S hS Y)
    refine (congrArg₂ (· ≫ ·) h₁ rfl).trans (Eq.trans ?_ h₂.symm)
    exact (asIso g.toToposHom.adj.unit).hom_inv_id_app_assoc _ _

/-- If an isomorphism `(g, g♯)` of small étale ringed topoi is 2-isomorphic to `(f_small, f♯)`
and its inverse to `(f'_small, f'♯)`, then `(f' ≫ f)_small` is 2-isomorphic to `(𝟙 Y)_small`:
paste the two given 2-isomorphisms with the composition law
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_compTwoIso` and the round trip
`AlgebraicGeometry.Space.compInverseTwoIso`. -/
noncomputable def compTwoIsoIdOfInverse
    (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    [g.toToposHom.pushforward.IsEquivalence] [IsIso g.fSharp] {f : X ⟶ Y} {f' : Y ⟶ X}
    (s : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g (smallEtaleRingedToposHom B S hS f))
    (s' : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g.inverse
      (smallEtaleRingedToposHom B S hS f')) :
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} (smallEtaleRingedToposHom B S hS (f' ≫ f))
      (smallEtaleRingedToposHom B S hS (𝟙 Y)) :=
  (smallEtaleRingedToposHom_compTwoIso B S hS f' f).symm.trans
    ((s'.whiskerRight (smallEtaleRingedToposHom B S hS f)).symm.trans
      ((RingedToposHom.TwoIso.whiskerLeft g.inverse s).symm.trans
        (compInverseTwoIso B S hS g)))

/-- If an isomorphism `(g, g♯)` of small étale ringed topoi is 2-isomorphic to `(f_small, f♯)`
and its inverse to `(f'_small, f'♯)`, then `f' ≫ f = 𝟙 Y`: the two have 2-isomorphic morphisms
of small étale ringed topoi (`AlgebraicGeometry.Space.compTwoIsoIdOfInverse`), and a morphism
of algebraic spaces is determined by its 2-isomorphism class (Stacks 04M6,
`AlgebraicGeometry.Space.eq_of_smallEtaleRingedToposHom_twoIso`). -/
theorem comp_eq_id_of_twoIso_inverse
    (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    [g.toToposHom.pushforward.IsEquivalence] [IsIso g.fSharp] {f : X ⟶ Y} {f' : Y ⟶ X}
    (s : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g (smallEtaleRingedToposHom B S hS f))
    (s' : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g.inverse
      (smallEtaleRingedToposHom B S hS f')) :
    f' ≫ f = 𝟙 Y :=
  eq_of_smallEtaleRingedToposHom_twoIso B S hS _ _ (compTwoIsoIdOfInverse B S hS g s s')

/-- The inverse of an isomorphism of small étale ringed topoi is an isomorphism of ringed
topoi: its direct image is the inverse image of `g`, an equivalence. -/
instance isEquivalence_inverse_pushforward
    (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    [g.toToposHom.pushforward.IsEquivalence] [IsIso g.fSharp] :
    g.inverse.toToposHom.pushforward.IsEquivalence :=
  MorphismOfTopoi.isEquivalence_inverseImage g.toToposHom

/-- The structure map of the inverse of an isomorphism of small étale ringed topoi is an
isomorphism: it is the inverse of `g⁻¹𝒪_Y ⟶ 𝒪_X`. -/
instance isIso_inverse_fSharp
    (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    [g.toToposHom.pushforward.IsEquivalence] [IsIso g.fSharp] :
    IsIso g.inverse.fSharp :=
  have := RingedToposHom.isIso_fSharpInverseImage g
  inferInstanceAs (IsIso (inv g.fSharpInverseImage))

/-- **A morphism of algebraic spaces inducing an isomorphism of small étale ringed topoi is an
isomorphism**, as soon as the inverse of `(g, g♯)` and the inverse of that are induced by
morphisms of algebraic spaces.  With `f, f', f''` inducing `g`, its inverse and the inverse of
that, `f' ≫ f = 𝟙 Y` and `f'' ≫ f' = 𝟙 X` by
`AlgebraicGeometry.Space.comp_eq_id_of_twoIso_inverse`, so `f'` has a left and a right inverse,
which therefore agree, and `f` is its inverse. -/
theorem isIso_of_twoIso_of_inverse
    (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    [g.toToposHom.pushforward.IsEquivalence] [IsIso g.fSharp] {f : X ⟶ Y} {f' : Y ⟶ X}
    {f'' : X ⟶ Y}
    (s : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g (smallEtaleRingedToposHom B S hS f))
    (s' : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g.inverse
      (smallEtaleRingedToposHom B S hS f'))
    (s'' : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      g.inverse.inverse
      (smallEtaleRingedToposHom B S hS f'')) :
    IsIso f := by
  have h₁ : f' ≫ f = 𝟙 Y := comp_eq_id_of_twoIso_inverse B S hS g s s'
  have h₂ : f'' ≫ f' = 𝟙 X := comp_eq_id_of_twoIso_inverse B S hS _ s' s''
  have h₃ : f'' = f := by
    rw [← Category.comp_id f'', ← h₁, ← Category.assoc, h₂, Category.id_comp]
  exact ⟨f', h₃ ▸ h₂, h₁⟩

end Inverse

/-! ### Stacks 05YZ -/

/-- **Stacks 05YZ.** Let `X` and `Y` be algebraic spaces over `ℤ`, and let
`(g, g♯) : (Sh(X_étale), 𝒪_X) ⟶ (Sh(Y_étale), 𝒪_Y)` be an isomorphism of ringed topoi: its
direct image is an equivalence and `g♯ : 𝒪_Y ⟶ g_*𝒪_X` is an isomorphism.  Then there is a
unique morphism `f : X ⟶ Y` of algebraic spaces such that `(g, g♯)` is 2-isomorphic to
`(f_small, f♯)` — the morphism of small étale ringed topoi
`AlgebraicGeometry.Space.smallEtaleRingedToposHom` of Stacks 03G8, a 2-isomorphism being one of
Stacks 04IC — and that morphism is an isomorphism of algebraic spaces.

As in the source, the existence and uniqueness is Stacks 04KL
(`AlgebraicGeometry.Space.existsUnique_spaceHom_twoIso_of_isLocallyRinged`), applicable because
`(g, g♯)` is a morphism of locally ringed topoi
(`AlgebraicGeometry.Space.isLocallyRinged_of_smallEtaleRingedToposIso`).  For the last clause,
Stacks 04KL applied to the inverse of `(g, g♯)` and to the inverse of that gives `f'` and `f''`,
and `AlgebraicGeometry.Space.isIso_of_twoIso_of_inverse` shows that `f` is invertible. -/
@[stacks 05YZ]
theorem existsUnique_spaceHom_twoIso_of_smallEtaleRingedToposIso (B : BigFppfSite.{u})
    (hZ : B.Contains (Spec (CommRingCat.of (ULift.{u} ℤ))))
    {X Y : AlgebraicSpaces B (Spec (CommRingCat.of (ULift.{u} ℤ))) hZ}
    (g : RingedToposHom (smallEtaleRingedTopos B (Spec (CommRingCat.of (ULift.{u} ℤ))) hZ X)
      (smallEtaleRingedTopos B (Spec (CommRingCat.of (ULift.{u} ℤ))) hZ Y))
    [g.toToposHom.pushforward.IsEquivalence] [IsIso g.fSharp] :
    (∃! f : X ⟶ Y, Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g
      (smallEtaleRingedToposHom B (Spec (CommRingCat.of (ULift.{u} ℤ))) hZ f))) ∧
    ∀ f : X ⟶ Y, Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g
      (smallEtaleRingedToposHom B (Spec (CommRingCat.of (ULift.{u} ℤ))) hZ f)) → IsIso f := by
  obtain ⟨f', ⟨s'⟩, -⟩ := existsUnique_spaceHom_twoIso_of_isLocallyRinged B hZ g.inverse
    (isLocallyRinged_of_smallEtaleRingedToposIso B _ hZ g.inverse)
  obtain ⟨f'', ⟨s''⟩, -⟩ := existsUnique_spaceHom_twoIso_of_isLocallyRinged B hZ g.inverse.inverse
    (isLocallyRinged_of_smallEtaleRingedToposIso B _ hZ g.inverse.inverse)
  exact ⟨existsUnique_spaceHom_twoIso_of_isLocallyRinged B hZ g
      (isLocallyRinged_of_smallEtaleRingedToposIso B _ hZ g),
    fun _ ⟨s⟩ ↦ isIso_of_twoIso_of_inverse B _ hZ g s s' s''⟩

end AlgebraicGeometry.Space

end
