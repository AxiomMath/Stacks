module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposHom

/-!
# The structure sheaf on the spaces-étale site of an algebraic space

Let `X` be an algebraic space over a scheme `S`. Its *spaces-étale* site of Stacks 03G0 is the
category of algebraic spaces étale over `X`, with the jointly point-surjective families as its
coverings. This file proves that the presheaf assigning to such an object the ring `Γ(U, 𝒪_U)`
of global regular functions on its underlying algebraic space is a sheaf, and packages it as
the structure sheaf of that site.

The argument is the one that works on the big étale site, run on the smaller site. Global
regular functions on an algebraic space are its morphisms to the affine line
(`AlgebraicGeometry.Space.globalFunctionsHomEquiv`), so the structure presheaf is the presheaf
represented by the affine line, and the sheaf condition is subcanonicity. Morphisms into a
*representable* algebraic space descend along an étale covering of algebraic spaces by
`AlgebraicGeometry.Space.existsUnique_desc_of_etaleCovering_representable`, which needs no
input from Stacks 0APL; and a jointly point-surjective family in the spaces-étale site *is* an
étale covering, because a morphism between two algebraic spaces étale over `X` is étale.

Unlike the big étale site of Stacks 0DBX, the spaces-étale site needs no choice of a set-sized
collection of coverings, so nothing here is indexed by an
`AlgebraicGeometry.BigEtaleSpaceSite`: the statements are about `B`, `S`, `hS` and `X` alone.

The structure sheaf is then shown to be compatible with étale localization: for an étale
morphism `f : X ⟶ Y` of algebraic spaces, the equivalence of Stacks 04LY between the
spaces-étale site of `X` and the localization `Y_{spaces,étale}/X` of the spaces-étale site of
`Y` carries the restriction of `𝒪_Y` to `𝒪_X`, so the two ringed sites
`(X_{spaces,étale}, 𝒪_X)` and `(Y_{spaces,étale}/X, 𝒪_Y|_{Y_{spaces,étale}/X})` are identified.

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtale.structurePresheaf`: the presheaf of global regular
  functions on the spaces-étale site of `X`.
* `AlgebraicGeometry.Space.SpacesEtale.structureSheaf`: the same, as a sheaf of commutative
  rings.
* `AlgebraicGeometry.Space.spacesEtaleRingedTopos`: the ringed site
  `(X_{spaces,étale}, 𝒪_X)`.
* `AlgebraicGeometry.Space.spacesEtaleRingedToposOver`: the localized ringed site
  `(Y_{spaces,étale}/X, 𝒪_Y|_{Y_{spaces,étale}/X})` of an étale morphism `X ⟶ Y`.
* `AlgebraicGeometry.Space.spacesEtaleLocalizationRingedHom`: the morphism of ringed sites
  identifying the two.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.isEtale_toSpaces_map`: a morphism of the spaces-étale
  site is étale as a morphism of algebraic spaces.
* `AlgebraicGeometry.Space.SpacesEtale.isEtaleCovering_of_isCovering`: a covering family of
  the spaces-étale site is an étale covering of algebraic spaces.
* `AlgebraicGeometry.Space.SpacesEtale.isSheaf_yoneda`: the spaces-étale topology is
  subcanonical at representable algebraic spaces.
* `AlgebraicGeometry.Space.SpacesEtale.structurePresheaf_isSheaf`.
* `AlgebraicGeometry.Space.spacesEtaleLocalization_structureSheaf`: the localization
  equivalence of Stacks 04LY carries `𝒪_Y|_{Y_{spaces,étale}/X}` to `𝒪_X`.
* `AlgebraicGeometry.Space.isIso_spacesEtaleLocalizationRingedHom_fSharp` and
  `AlgebraicGeometry.Space.isEquivalence_spacesEtaleLocalizationRingedHom_u`: that morphism of
  ringed sites is an isomorphism.

## Implementation notes

**The structure sheaf itself carries no Stacks attribute, deliberately.** What is proved about
it is content of Stacks 0DF9, a *remark* of Chapter 73 (Topologies on Algebraic Spaces), which is
not registered here. Those declarations are untagged helpers, and a formalization of Stacks 0DF9
should be built from them rather than duplicating them. Stacks 04LZ, by
contrast, is an equation of Chapter 66 and is carried here, since its content beyond the
identification of sites of Stacks 04LY is exactly a statement about the structure sheaf.

An identification of ringed sites cannot be an equality in Lean, because the two underlying
categories `SpacesEtale B S hS X` and `Over (etaleObject B S hS f hf)` are different types; it
is presented, as the source presents a morphism of ringed topoi, by a continuous functor
between the underlying sites together with a map of structure sheaves, i.e. by an
`AlgebraicGeometry.RingedToposSiteHom`. That notion constrains only the universe of the
sections of the two structure sheaves and leaves the object and morphism universes of the two
sites independent, whereas `AlgebraicGeometry.RingedSite.Hom` would in addition force the
objects and the morphisms of both sites into a single universe. The *comparison of structure
sheaves* is nevertheless a genuine equality of sheaves, since the underlying algebraic space of
an object is unchanged by the localization equivalence, on the nose.

The chosen fibre product of two objects of the spaces-étale site is again étale over `X` and
is therefore an object of that site. The private `pbSpace` below packages it with its two
projections, and those projections are *the chosen* pullback projections of
`AlgebraicGeometry.AlgebraicSpaces.fiberProduct` — their images under
`AlgebraicGeometry.Space.SpacesEtale.toSpaces` are `pbP₁` and `pbP₂` by definition. That is
what the descent lemma asks for: the compatibility hypothesis of
`AlgebraicGeometry.Space.existsUnique_desc_of_etaleCovering_representable` is stated at that
particular fibre product, not at an arbitrary cone, so the general compatibility of the
family is applied at `pbSpace` and lands on the nose.

`structureSheaf_obj` and `structureSheaf_map` have no consumer in this file, deliberately:
they are the rewriting interface a ringed-site comparison needs, and they are the two `simp`
lemmas Stacks 0DF9 states alongside the structure sheaf.

## References

* [Stacks Project, Tag 0DF9](https://stacks.math.columbia.edu/tag/0DF9)
* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 041E](https://stacks.math.columbia.edu/tag/041E)
* [Stacks Project, Tag 04LY](https://stacks.math.columbia.edu/tag/04LY)
* [Stacks Project, Tag 04LZ](https://stacks.math.columbia.edu/tag/04LZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks in this presheaf category exceeds the default limit
/-- Presheaves of types on the big fppf site of `S` have pullbacks. Recorded here because
instance search for it times out at the default budget under this file's imports. -/
private instance hasPullbacksPresheaf : HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  inferInstance

/-- Any cospan of presheaves of types on the big fppf site of `S` has a limit, read off
`hasPullbacksPresheaf` so that instance search does not have to find it. -/
private instance (priority := high) hasLimitCospanPresheaf
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H) :
    HasLimit (cospan f g) :=
  (hasPullbacksPresheaf B S hS).has_limit (cospan f g)

/-! ### Morphisms of the spaces-étale site -/

/-- A morphism of the spaces-étale site of `X` is étale as a morphism of algebraic spaces:
both its source and its target are étale over `X`, and étaleness cancels. -/
theorem isEtale_toSpaces_map {A C : SpacesEtale B S hS X} (c : A ⟶ C) :
    IsEtale B S hS ((toSpaces B S hS X).map c).hom := by
  exact isEtale_of_isEtale_over B S hS
    ((toSpaces B S hS X).obj A).property
    ((toSpaces B S hS X).obj C).property X.property
    ((toSpaces B S hS X).map c).hom
    ((inclusion B S hS X).obj A).hom.hom
    ((inclusion B S hS X).obj C).hom.hom
    A.property C.property (congrArg (fun k => k.hom) (Over.w ((inclusion B S hS X).map c)))

/-- The structure morphism over `X` of the source of a morphism of the spaces-étale site
factors through that of its target. -/
theorem toSpaces_map_comp_structure {A C : SpacesEtale B S hS X} (c : A ⟶ C) :
    (toSpaces B S hS X).map c ≫ ((inclusion B S hS X).obj C).hom =
      ((inclusion B S hS X).obj A).hom :=
  Over.w ((inclusion B S hS X).map c)

variable {B S hS X}

/-! ### The chosen fibre product of two objects of the spaces-étale site -/

/-- The chosen fibre product of two morphisms of the spaces-étale site of `X`, as an algebraic
space over `S`. -/
private noncomputable abbrev pbObj {V A C : SpacesEtale B S hS X} (a : A ⟶ V) (c : C ⟶ V) :
    AlgebraicSpaces B S hS :=
  AlgebraicSpaces.fiberProduct B S hS ((toSpaces B S hS X).map a) ((toSpaces B S hS X).map c)

/-- The first projection of the chosen fibre product. -/
private noncomputable def pbP₁ {V A C : SpacesEtale B S hS X} (a : A ⟶ V) (c : C ⟶ V) :
    pbObj a c ⟶ (toSpaces B S hS X).obj A :=
  ObjectProperty.homMk
    (pullback.fst ((toSpaces B S hS X).map a).hom ((toSpaces B S hS X).map c).hom)

/-- The second projection of the chosen fibre product. -/
private noncomputable def pbP₂ {V A C : SpacesEtale B S hS X} (a : A ⟶ V) (c : C ⟶ V) :
    pbObj a c ⟶ (toSpaces B S hS X).obj C :=
  ObjectProperty.homMk
    (pullback.snd ((toSpaces B S hS X).map a).hom ((toSpaces B S hS X).map c).hom)

private theorem pbP_isPullback {V A C : SpacesEtale B S hS X} (a : A ⟶ V) (c : C ⟶ V) :
    IsPullback (pbP₁ a c) (pbP₂ a c) ((toSpaces B S hS X).map a)
      ((toSpaces B S hS X).map c) :=
  AlgebraicSpaces.isPullback_fiberProduct B S hS
    ((toSpaces B S hS X).map a) ((toSpaces B S hS X).map c)

/-- The chosen fibre product of two morphisms of the spaces-étale site of `X`, as an object
over `X`: its structure morphism is the first projection followed by the structure morphism of
the first factor. -/
private noncomputable def pbOver {V A C : SpacesEtale B S hS X} (a : A ⟶ V) (c : C ⟶ V) :
    Over X :=
  Over.mk (pbP₁ a c ≫ ((inclusion B S hS X).obj A).hom)

private theorem pbOver_isEtaleOver {V A C : SpacesEtale B S hS X} (a : A ⟶ V) (c : C ⟶ V) :
    IsEtaleOver B S hS X (pbOver a c) := by
  have hfst : IsEtale B S hS (pbP₁ a c).hom :=
    isEtale_of_isPullback B S hS _ _ _ _ (pbP_isPullback a c).flip
      (isEtale_toSpaces_map B S hS X c)
  exact isEtale_comp B S hS hfst A.property

/-- The second projection lands over `X`: both projections become the structure morphism of
the fibre product after composing with the structure morphisms of the two factors. This is the
statement that `pbSnd` below is a morphism over `X`, the right-hand side being `(pbOver a c).hom`
by definition. -/
private theorem pbP₂_comp_structure {V A C : SpacesEtale B S hS X} (a : A ⟶ V) (c : C ⟶ V) :
    pbP₂ a c ≫ ((inclusion B S hS X).obj C).hom =
      pbP₁ a c ≫ ((inclusion B S hS X).obj A).hom := by
  rw [← toSpaces_map_comp_structure B S hS X c, ← toSpaces_map_comp_structure B S hS X a,
    ← Category.assoc, ← Category.assoc, (pbP_isPullback a c).w]

/-- The chosen fibre product of two morphisms of the spaces-étale site of `X`, as an object of
that site. -/
private noncomputable def pbSpace {V A C : SpacesEtale B S hS X} (a : A ⟶ V) (c : C ⟶ V) :
    SpacesEtale B S hS X :=
  ⟨pbOver a c, pbOver_isEtaleOver a c⟩

/-- The first projection of the fibre product, as a morphism of the spaces-étale site. -/
private noncomputable def pbFst {V A C : SpacesEtale B S hS X} (a : A ⟶ V) (c : C ⟶ V) :
    pbSpace a c ⟶ A :=
  ObjectProperty.homMk (Over.homMk (pbP₁ a c) rfl)

/-- The second projection of the fibre product, as a morphism of the spaces-étale site. -/
private noncomputable def pbSnd {V A C : SpacesEtale B S hS X} (a : A ⟶ V) (c : C ⟶ V) :
    pbSpace a c ⟶ C :=
  ObjectProperty.homMk (Over.homMk (pbP₂ a c) (pbP₂_comp_structure a c))

private theorem pbSpace_isPullback {V A C : SpacesEtale B S hS X} (a : A ⟶ V) (c : C ⟶ V) :
    IsPullback (pbFst a c) (pbSnd a c) a c := by
  have hcommOver : (Over.homMk (pbP₁ a c) rfl :
        pbOver a c ⟶ (inclusion B S hS X).obj A) ≫ (inclusion B S hS X).map a =
      (Over.homMk (pbP₂ a c) (pbP₂_comp_structure a c) :
        pbOver a c ⟶ (inclusion B S hS X).obj C) ≫ (inclusion B S hS X).map c :=
    Over.OverMorphism.ext (pbP_isPullback a c).w
  have hw : pbFst a c ≫ a = pbSnd a c ≫ c :=
    (inclusion B S hS X).map_injective hcommOver
  refine IsPullback.of_map (inclusion B S hS X) hw ?_
  refine IsPullback.of_map (Over.forget X) hcommOver ?_
  exact pbP_isPullback a c

/-! ### Covering families of the spaces-étale site are étale coverings -/

variable (B S hS X)

/-- A jointly point-surjective family of the spaces-étale site of `X` is an étale covering of
algebraic spaces over `S`: every member is étale because a morphism between two algebraic
spaces étale over `X` is étale, and joint surjectivity on points is the covering condition
itself. -/
theorem isEtaleCovering_of_isCovering {V : SpacesEtale B S hS X}
    {I : Type (u + 1)} (Xi : I → SpacesEtale B S hS X) (f : ∀ i, Xi i ⟶ V)
    (hf : ∀ x : points B S hS ((toSpaces B S hS X).obj V).1, ∃ i, ∃ y,
      pointsMap B S hS ((toSpaces B S hS X).obj (Xi i)).1
        ((toSpaces B S hS X).map (f i)).hom y = x) :
    IsEtaleCovering B S hS (fun i => ((toSpaces B S hS X).obj (Xi i)).1)
      (fun i => ((toSpaces B S hS X).map (f i)).hom) := by
  refine ⟨((toSpaces B S hS X).obj V).property,
    fun i => ((toSpaces B S hS X).obj (Xi i)).property,
    fun i => isEtale_toSpaces_map B S hS X (f i),
    Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ((hf x).imp fun _ => Set.mem_range.mpr)⟩

/-! ### The spaces-étale topology is subcanonical at representable objects -/

/-- A presheaf represented by a representable algebraic space satisfies the sheaf condition
for a covering family of the spaces-étale site of `X`. -/
private theorem isSheafFor_yoneda_of_spacesEtaleCovering
    {V : SpacesEtale B S hS X} {I : Type (u + 1)} (Xi : I → SpacesEtale B S hS X)
    (f : ∀ i, Xi i ⟶ V)
    (hf : IsEtaleCovering B S hS (fun i => ((toSpaces B S hS X).obj (Xi i)).1)
      (fun i => ((toSpaces B S hS X).map (f i)).hom))
    (A : BigFppfOver B S hS) :
    Presieve.IsSheafFor
      ((toSpaces B S hS X).op ⋙ yoneda.obj (representedAlgebraicSpace B S hS A))
      (Presieve.ofArrows Xi f) := by
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  exact existsUnique_desc_of_etaleCovering_representable B S hS
    (fun i => (toSpaces B S hS X).map (f i)) hf A x (fun i j =>
      hx i j (pbSpace (f i) (f j)) (pbFst (f i) (f j)) (pbSnd (f i) (f j))
        (pbSpace_isPullback (f i) (f j)).w)

/-- The spaces-étale topology of `X` is subcanonical at representable objects: the presheaf
represented by a representable algebraic space is a sheaf. -/
theorem isSheaf_yoneda (A : BigFppfOver B S hS) :
    Presieve.IsSheaf (topology B S hS X)
      ((toSpaces B S hS X).op ⋙ yoneda.obj (representedAlgebraicSpace B S hS A)) := by
  rw [Precoverage.isSheaf_toGrothendieck_iff]
  intro V W g R hR
  obtain ⟨E, rfl, hE⟩ := hR
  have hcov : IsEtaleCovering B S hS (fun i => ((toSpaces B S hS X).obj (E.X i)).1)
      (fun i => ((toSpaces B S hS X).map (E.f i)).hom) :=
    isEtaleCovering_of_isCovering B S hS X E.X E.f hE
  have hpb (i : E.I₀) : IsPullback (pbFst g (E.f i)) (pbSnd g (E.f i)) g (E.f i) :=
    pbSpace_isPullback g (E.f i)
  have heq := Sieve.ofArrows_eq_pullback_of_isPullback E.f hpb
  rw [← heq]
  apply (Presieve.isSheafFor_iff_generate
    (Presieve.ofArrows (fun i => pbSpace g (E.f i)) (fun i => pbFst g (E.f i)))).1
  refine isSheafFor_yoneda_of_spacesEtaleCovering B S hS X _ _ ?_ A
  exact isEtaleCovering_fibreProduct B S hS
    (fun i => (toSpaces B S hS X).obj (E.X i))
    (fun i => (toSpaces B S hS X).map (E.f i))
    ((toSpaces B S hS X).map g) hcov

/-! ### The structure sheaf -/

/-- The structure presheaf on the spaces-étale site of `X`: its value at an algebraic space
`U` étale over `X` is the ring `Γ(U, 𝒪_U)` of global regular functions on `U`, and its
restriction maps are pullback of regular functions. -/
noncomputable abbrev structurePresheaf :
    (SpacesEtale B S hS X)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  (toSpaces B S hS X).op ⋙ globalFunctionsPresheaf B S hS

/-- Global regular functions satisfy étale descent on the spaces-étale site of `X`: the
structure presheaf is the presheaf represented by the affine line, and the spaces-étale
topology is subcanonical at representable objects. -/
theorem structurePresheaf_isSheaf :
    Presheaf.IsSheaf (topology B S hS X) (structurePresheaf B S hS X) := by
  apply (Presheaf.isSheaf_iff_isSheaf_forget (topology B S hS X)
    (structurePresheaf B S hS X) (forget CommRingCat.{u + 1})).2
  apply (isSheaf_iff_isSheaf_of_type _ _).2
  apply (Presieve.isSheaf_iff_of_nat_equiv
    (P₂ := (toSpaces B S hS X).op ⋙ yoneda.obj (affineLineSpace B S hS))
    (fun {U} => globalFunctionsHomEquiv B S hS ((toSpaces B S hS X).obj U))
    (fun {U V} f s =>
      globalFunctionsHomEquiv_natural B S hS ((toSpaces B S hS X).map f) s)).2
  exact isSheaf_yoneda B S hS X _

/-- The structure sheaf of rings on the spaces-étale site of `X`. -/
noncomputable def structureSheaf :
    Sheaf (topology B S hS X) CommRingCat.{u + 1} :=
  ⟨structurePresheaf B S hS X, structurePresheaf_isSheaf B S hS X⟩

/-- The value of the structure sheaf at an object of the spaces-étale site. -/
@[simp] theorem structureSheaf_obj (U : (SpacesEtale B S hS X)ᵒᵖ) :
    (structureSheaf B S hS X).obj.obj U =
      CommRingCat.of (globalFunctions' B S hS ((toSpaces B S hS X).obj U.unop).obj) := rfl

/-- The restriction maps of the structure sheaf are pullback of global regular functions. -/
@[simp] theorem structureSheaf_map {U V : (SpacesEtale B S hS X)ᵒᵖ} (f : U ⟶ V) :
    (structureSheaf B S hS X).obj.map f =
      CommRingCat.ofHom
        (globalFunctionsMap B S hS ((toSpaces B S hS X).map f.unop)) := rfl

end AlgebraicGeometry.Space.SpacesEtale

namespace AlgebraicGeometry.Space

/-! ### Étale localization of the ringed spaces-étale site -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The ringed site `(X_{spaces,étale}, 𝒪_X)` of an algebraic space `X`: its spaces-étale site
of Stacks 03G0, together with the sheaf of global regular functions. -/
noncomputable abbrev spacesEtaleRingedTopos (X : AlgebraicSpaces B S hS) : RingedTopos where
  C := SpacesEtale B S hS X
  J := SpacesEtale.topology B S hS X
  O := SpacesEtale.structureSheaf B S hS X

/-- The same ringed site as `AlgebraicGeometry.Space.spacesEtaleRingedTopos`, in the structure
that carries morphisms of ringed *sites* and hence the localization constructions of
Stacks 04J0 and 04J1. -/
noncomputable abbrev spacesEtaleRingedSite (X : AlgebraicSpaces B S hS) :
    RingedSite.{u + 1, u + 1, u + 1} where
  C := SpacesEtale B S hS X
  J := SpacesEtale.topology B S hS X
  O := SpacesEtale.structureSheaf B S hS X

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)

attribute [local instance] spacesEtaleLocalization_isContinuous

/-- The localized ringed site `(Y_{spaces,étale}/X, 𝒪_Y|_{Y_{spaces,étale}/X})` of an étale
morphism `f : X ⟶ Y`: the localization of the spaces-étale site of `Y` at the object `f`,
with the restriction of the structure sheaf of `Y`. -/
noncomputable abbrev spacesEtaleRingedToposOver : RingedTopos where
  C := Over (etaleObject B S hS f hf)
  J := (SpacesEtale.topology B S hS Y).over (etaleObject B S hS f hf)
  O := (SpacesEtale.structureSheaf B S hS Y).over (etaleObject B S hS f hf)

/-- The localization equivalence of Stacks 04LY does not change the underlying algebraic space:
an algebraic space étale over `X` and the corresponding object of `Y_{spaces,étale}/X` have the
same underlying algebraic space. -/
theorem spacesEtaleLocalization_toSpaces :
    (spacesEtaleLocalization B S hS f hf).functor ⋙
        Over.forget (etaleObject B S hS f hf) ⋙ SpacesEtale.toSpaces B S hS Y =
      SpacesEtale.toSpaces B S hS X := by
  rw [← Over.post_forget_eq_forget_comp (SpacesEtale.toSpaces B S hS Y)
    (etaleObject B S hS f hf)]
  change ((spacesEtaleLocalization B S hS f hf).functor ⋙
    Over.post (SpacesEtale.toSpaces B S hS Y)) ⋙ Over.forget X = _
  rw [spacesEtaleLocalization_slice B S hS f hf]
  rfl

/-- **Stacks 04LZ.** For an étale morphism `f : X ⟶ Y` of algebraic spaces, the structure sheaf
of the spaces-étale site of `X` is the restriction of the structure sheaf of `Y` along the
localization equivalence of Stacks 04LY: `𝒪_X = 𝒪_Y|_{Y_{spaces,étale}/X}`. -/
@[stacks 04LZ "the structure sheaves"]
theorem spacesEtaleLocalization_structureSheaf :
    ((spacesEtaleLocalization B S hS f hf).functor.sheafPushforwardContinuous
          CommRingCat.{u + 1} (SpacesEtale.topology B S hS X)
          ((SpacesEtale.topology B S hS Y).over (etaleObject B S hS f hf))).obj
        ((SpacesEtale.structureSheaf B S hS Y).over (etaleObject B S hS f hf)) =
      SpacesEtale.structureSheaf B S hS X :=
  ObjectProperty.FullSubcategory.ext <| congrArg
    (fun F : SpacesEtale B S hS X ⥤ AlgebraicSpaces B S hS ↦
      F.op ⋙ globalFunctionsPresheaf B S hS)
    (spacesEtaleLocalization_toSpaces B S hS f hf)

/-- **Stacks 04LZ.** For an étale morphism `f : X ⟶ Y` of algebraic spaces, the ringed site
`(X_{spaces,étale}, 𝒪_X)` is the localized ringed site
`(Y_{spaces,étale}/X, 𝒪_Y|_{Y_{spaces,étale}/X})`: the identification of sites of Stacks 04LY
matches the two structure sheaves. -/
@[stacks 04LZ "the identification of ringed sites"]
noncomputable def spacesEtaleLocalizationRingedHom :
    RingedToposSiteHom (spacesEtaleRingedToposOver B S hS f hf)
      (spacesEtaleRingedTopos B S hS X) where
  u := (spacesEtaleLocalization B S hS f hf).functor
  isContinuous := spacesEtaleLocalization_isContinuous B S hS f hf
  fSharp := eqToHom (spacesEtaleLocalization_structureSheaf B S hS f hf).symm

/-- The functor of sites underlying the identification of Stacks 04LZ is the localization
equivalence of Stacks 04LY. -/
@[simp]
theorem spacesEtaleLocalizationRingedHom_u :
    (spacesEtaleLocalizationRingedHom B S hS f hf).u =
      (spacesEtaleLocalization B S hS f hf).functor := rfl

/-- The structure map of the identification of Stacks 04LZ is the comparison of the two
structure sheaves. -/
@[simp]
theorem spacesEtaleLocalizationRingedHom_fSharp :
    (spacesEtaleLocalizationRingedHom B S hS f hf).fSharp =
      eqToHom (spacesEtaleLocalization_structureSheaf B S hS f hf).symm := rfl

/-- The structure map of the identification of Stacks 04LZ is an isomorphism. -/
theorem isIso_spacesEtaleLocalizationRingedHom_fSharp :
    IsIso (spacesEtaleLocalizationRingedHom B S hS f hf).fSharp := by
  rw [spacesEtaleLocalizationRingedHom_fSharp]
  exact (eqToIso (spacesEtaleLocalization_structureSheaf B S hS f hf).symm).isIso_hom

/-- The functor of sites underlying the identification of Stacks 04LZ is an equivalence. -/
theorem isEquivalence_spacesEtaleLocalizationRingedHom_u :
    (spacesEtaleLocalizationRingedHom B S hS f hf).u.IsEquivalence := by
  rw [spacesEtaleLocalizationRingedHom_u]
  infer_instance

end AlgebraicGeometry.Space

end
