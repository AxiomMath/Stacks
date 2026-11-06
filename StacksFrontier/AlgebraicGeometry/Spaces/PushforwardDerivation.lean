module

public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsMap

/-!
# The direct image of a derivation along a morphism of algebraic spaces

Let

```
X' --f--> X
|         |
p'        p
v         v
Y' --q--> Y
```

be a commutative square of algebraic spaces over a scheme `S`, and let `D : 𝒪_{X'} ⟶ M` be a
`Y'`-derivation with values in an `𝒪_{X'}`-module `M`.  This file builds the `Y`-derivation
```
  f_*D ∘ f♯ : 𝒪_X ⟶ f_*M
```
of `𝒪_X` with values in the direct image of `M`, and identifies it with precomposition by the
comparison map `c_f : f^*Ω_{X/Y} ⟶ Ω_{X'/Y'}` of Stacks 04CX under Equation 0619.

## Why this file exists

`AlgebraicGeometry.Space.pushforwardUniversalDerivation` of
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsMap.lean` is this construction for the
*universal* derivation `d_{X'/Y'}`, which is all Stacks 04CX needs.  The route to exactness at
the middle term of the conormal sequence of Stacks 05ZA recorded in the *What is not proved*
section of `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceDifferentials.lean` needs it for
a derivation with values in an arbitrary module: the clause says that the second arrow of that
sequence is a cokernel of the first, and testing a cokernel means quantifying over every target
module.  That record states the gap as *no declaration in this tree relates the `B`-derivations
of `i_*𝒪_Z` with values in `i_*M` to the `B`-derivations of `𝒪_Z` with values in `M`*; the
declarations below are that relation in the direction a factorization is built from.

Nothing is re-proved.  The additivity, the Leibniz rule and the vanishing on the base of
`f_*D ∘ f♯` are the general transport lemmas of the `Transport` section of
`SheafOfDifferentialsMap.lean` — `AlgebraicGeometry.Space.ringAddHom_comp_derivationHom`,
`AlgebraicGeometry.Space.ringMulHom_comp_derivationHom`,
`AlgebraicGeometry.Space.map_ringAddObj_derivationHom`,
`AlgebraicGeometry.Space.map_ringMulObj_derivationHom` and
`AlgebraicGeometry.Space.map_zeroDerivationHom` — applied at `D` instead of at `d_{X'/Y'}`;
those lemmas are already stated for an arbitrary morphism of the underlying sheaves of sets, so
the universal case was never the general one.
`AlgebraicGeometry.Space.pushforwardDerivation_universalDerivation` records that the
construction below *is* `pushforwardUniversalDerivation` at `D = d_{X'/Y'}`, by `rfl`, so the two
are one construction and not two.

## Main definitions

* `AlgebraicGeometry.Space.derivationHom`: a derivation read as a morphism of the underlying
  sheaves of sets, the form in which the direct image applies to it.  At the universal derivation
  this is `AlgebraicGeometry.Space.universalDerivationHom`, by
  `AlgebraicGeometry.Space.derivationHom_universalDerivation`.
* `AlgebraicGeometry.Space.pushforwardDerivationHom`: the composite `f_*D ∘ f♯`, on underlying
  sheaves of sets.
* `AlgebraicGeometry.Space.pushforwardDerivation`: **the direct image of a derivation** — the
  composite `f_*D ∘ f♯` as a `Y`-derivation of `𝒪_X` with values in `f_*M`.

## Main results

* `AlgebraicGeometry.Space.pushforwardDerivation_d`: the derivation really is the structure map
  of `f` followed by the direct image of `D`, on local sections.
* `AlgebraicGeometry.Space.pushforwardDerivation_universalDerivation`: at the universal
  derivation it is the derivation of Stacks 04CX.
* `AlgebraicGeometry.Space.derivationDirectImageEquiv_sheafOfDifferentialsMap_comp`:
  **precomposition with the comparison map of Stacks 04CX is the direct image of derivations.**
  Under Equation 0619 the morphism `c_f ≫ g : f^*Ω_{X/Y} ⟶ M` corresponds to the direct image of
  the `Y'`-derivation `g ∘ d_{X'/Y'}` of `𝒪_{X'}`.  This is what turns a statement about
  precomposition with `c_f` — such as the cokernel clause of Stacks 05ZA — into a statement about
  derivations.

## Implementation notes

**Why the vanishing clause is routed through the direct-image form of the structure map.**  The
`d_app` field of a derivation is a statement about `p♯ : p^{-1}𝒪_Y ⟶ 𝒪_X`, and the hypothesis
available about `f_*D ∘ f♯` is about the composite of *direct-image* structure maps, since the
square commutes.  The two forms are exchanged by
`AlgebraicGeometry.Space.structureSharpInverseImage_of_structureSharpSetComp` and
`AlgebraicGeometry.Space.structureSharpSetComp_of_structureSharpInverseImage`, exactly as in the
universal case; `AlgebraicGeometry.Space.structureSharpSet_comp_derivationHom` is the step at
which the commuting square is used, through `hr : r = p' ≫ q`.

**No separate pushed-forward zero morphism is introduced.**  The universal case names the
composite of the structure map with the direct image of the zero morphism
(`AlgebraicGeometry.Space.pushforwardZeroDerivationHom`); at a general target module the same
composite is written out where it occurs, so that nothing below is a second copy of that
definition.

**The universes** are those of the small étale site, `RingedSite.{u + 1, u, u}` with modules
`Modules.{u, u}`, as everywhere in this part of the development.  In particular the site
category has its objects in `Type (u + 1)` and its morphisms in `Type u`, so it is *not* a
`CategoryTheory.SmallCategory`; the general site-level bijection
`Stacks.Sheaves.Differentials.directImageDerivationEquiv` of
`StacksFrontier/CategoryTheory/Sites/Modules/DifferentialsInverseImage.lean:442`, which asks for
`[SmallCategory C]` and `[SmallCategory D]`, therefore does not apply here even after its
inverse-image ring sheaf is replaced by a direct-image one.

## No tag is registered

Stacks 04CX is the statement about the universal derivation, and it is registered where it is
proved, on `AlgebraicGeometry.Space.pushforwardUniversalDerivation` and
`AlgebraicGeometry.Space.sheafOfDifferentialsMap`; Equation 0619 is registered on
`AlgebraicGeometry.Space.derivationDirectImageEquiv`.  Generalizing a construction from the
universal derivation to an arbitrary one, and reading a composition as that construction, are
proof steps rather than clauses of a tag, so nothing is registered here.

## References

* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the comparison map of a
  commutative square and the derivation it is built from.
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619), the bijection between
  maps out of a pulled-back sheaf of differentials and derivations into a direct image.
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT), the sheaf of
  differentials and its universal derivation.
* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA), the conormal sequence,
  whose exactness at the middle term is what wants the generalization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf CategoryTheory.Functor

universe u

universe w₁ v₁ u₁

/-! Instance search for binary products of sheaves of sets tries the default-priority `HasLimit`
instances before the low-priority one through `HasLimitsOfShape`, and under the current imports
those time out; the shortcut instance below goes there directly. -/

local instance (priority := high) hasLimit_pair_sheafType {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} (X Y : Sheaf J (Type w₁)) : HasLimit (pair X Y) :=
  HasLimitsOfShape.has_limit _

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y X' Y' : AlgebraicSpaces B S hS}

/-- A derivation, read as a morphism of the underlying sheaves of sets. -/
noncomputable def derivationHom (p' : X' ⟶ Y') (M : Modules.{u, u} B S hS X'.1 X'.2)
    (D : PresheafOfModulesOfCommRing.Derivation' M.val (structureSharpInverseImage B S hS p').hom) :
    CategoryTheory.Sheaf.ringSheaf.{u, u, u + 1} (structureRingSheaf B S hS X') ⟶
      CategoryTheory.Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X') M :=
  CategoryTheory.Sheaf.unaryOpHom (fun _ a ↦ D.d a) (fun g a ↦ (D.d_map g a).symm)

/-- The universal derivation read as a morphism of underlying sheaves of sets is
`AlgebraicGeometry.Space.universalDerivationHom`. -/
theorem derivationHom_universalDerivation (p' : X' ⟶ Y') :
    derivationHom B S hS p' (sheafOfDifferentials B S hS p')
        (universalDerivation B S hS p') =
      universalDerivationHom B S hS p' :=
  rfl


section Pushforward

variable (p' : X' ⟶ Y') (M : Modules.{u, u} B S hS X'.1 X'.2)
  (D : PresheafOfModulesOfCommRing.Derivation' M.val (structureSharpInverseImage B S hS p').hom)

/-- Additivity of a derivation, as an identity of morphisms out of a product. -/
theorem ringAddHom_comp_derivationHom_eq :
    ringAddHom (structureRingSheaf B S hS X') ≫ derivationHom B S hS p' M D =
      prod.map (derivationHom B S hS p' M D) (derivationHom B S hS p' M D) ≫
        moduleAddHom (structureRingSheaf B S hS X') M :=
  ringAddHom_comp_derivationHom (derivationHom B S hS p' M D)
    (fun V a b ↦ _root_.map_add (D.d (X := V)) a b)

/-- The Leibniz rule for a derivation, as an identity of morphisms out of a product. -/
theorem ringMulHom_comp_derivationHom_eq :
    ringMulHom (structureRingSheaf B S hS X') ≫ derivationHom B S hS p' M D =
      prod.lift
          (prod.lift prod.fst (prod.snd ≫ derivationHom B S hS p' M D) ≫
            moduleSMulHom (structureRingSheaf B S hS X') M)
          (prod.lift prod.snd (prod.fst ≫ derivationHom B S hS p' M D) ≫
            moduleSMulHom (structureRingSheaf B S hS X') M) ≫
        moduleAddHom (structureRingSheaf B S hS X') M :=
  ringMulHom_comp_derivationHom (derivationHom B S hS p' M D)
    (fun V a b ↦ D.d_mul (X := V) a b)

/-- The composite `f_*D ∘ f♯ : 𝒪_X ⟶ f_*M` of the structure map of `f` with the direct image of
a derivation `D`, on underlying sheaves of sets. -/
noncomputable def pushforwardDerivationHom (f : X' ⟶ X) :
    CategoryTheory.Sheaf.ringSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) ⟶
      CategoryTheory.Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X)
        ((modulePushforward B S hS f).obj M) :=
  (sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map
      (structureSharp B S hS f) ≫
    (smallEtaleDirectImage B S hS f).map (derivationHom B S hS p' M D)

/-- The composite `f_*D ∘ f♯` is additive on sections. -/
theorem pushforwardDerivationHom_add (f : X' ⟶ X) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a b : (sectionsFunctor (SmallEtale.topology B S hS X.1) U).obj
      (structureSetSheaf B S hS X)) :
    (sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
        (pushforwardDerivationHom B S hS p' M D f) (a + b) =
      moduleAddObj (structureRingSheaf B S hS X') M
        (smallEtaleDirectImageSections B S hS f U)
        ((sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
          (pushforwardDerivationHom B S hS p' M D f) a)
        ((sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
          (pushforwardDerivationHom B S hS p' M D f) b) :=
  (congrArg ((smallEtaleDirectImageSections B S hS f U).map (derivationHom B S hS p' M D))
      (_root_.map_add ((structureSharp B S hS f).hom.app U).hom a b)).trans
    (map_ringAddObj_derivationHom (structureRingSheaf B S hS X') M
      (smallEtaleDirectImageSections B S hS f U)
      (derivationHom B S hS p' M D) (ringAddHom_comp_derivationHom_eq B S hS p' M D) _ _)

/-- The composite `f_*D ∘ f♯` satisfies the Leibniz rule on sections. -/
theorem pushforwardDerivationHom_mul (f : X' ⟶ X) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a b : (sectionsFunctor (SmallEtale.topology B S hS X.1) U).obj
      (structureSetSheaf B S hS X)) :
    (sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
        (pushforwardDerivationHom B S hS p' M D f) (a * b) =
      moduleAddObj (structureRingSheaf B S hS X') M
        (smallEtaleDirectImageSections B S hS f U)
        (moduleSMulObj (structureRingSheaf B S hS X') M
          (smallEtaleDirectImageSections B S hS f U)
          ((sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
            (structureSharpSet B S hS f) a)
          ((sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
            (pushforwardDerivationHom B S hS p' M D f) b))
        (moduleSMulObj (structureRingSheaf B S hS X') M
          (smallEtaleDirectImageSections B S hS f U)
          ((sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
            (structureSharpSet B S hS f) b)
          ((sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
            (pushforwardDerivationHom B S hS p' M D f) a)) :=
  (congrArg ((smallEtaleDirectImageSections B S hS f U).map (derivationHom B S hS p' M D))
      (_root_.map_mul ((structureSharp B S hS f).hom.app U).hom a b)).trans
    (map_ringMulObj_derivationHom (structureRingSheaf B S hS X') M
      (smallEtaleDirectImageSections B S hS f U)
      (derivationHom B S hS p' M D) (ringMulHom_comp_derivationHom_eq B S hS p' M D) _ _)

/-- A derivation and the zero morphism agree after the inverse-image form of the structure map
of `p'`: this is the vanishing clause of `D`. -/
theorem structureSharpInverseImageSet_comp_derivationHom :
    structureSharpInverseImageSet B S hS p' ≫ derivationHom B S hS p' M D =
      structureSharpInverseImageSet B S hS p' ≫
        zeroDerivationHom (structureRingSheaf B S hS X') M := by
  refine hom_ext_sections (fun V s ↦ ?_)
  rw [(sectionsFunctor (SmallEtale.topology B S hS X'.1) V).map_comp_apply,
    (sectionsFunctor (SmallEtale.topology B S hS X'.1) V).map_comp_apply]
  refine Eq.trans (D.d_app _) ?_
  exact (map_zeroDerivationHom (structureRingSheaf B S hS X') M
    (sectionsFunctor (SmallEtale.topology B S hS X'.1) V) _).symm

/-- Two morphisms out of `𝒪_{X'}` agree after the structure map of `f ≫ p` and its direct image
iff they agree after the structure map of `f` and its direct image, then those of `p`. -/
private theorem structureSharpSet_comp_map_eq_iff_comp (f : X' ⟶ X) (p : X ⟶ Y)
    {E : Sheaf (SmallEtale.topology B S hS X'.1) (Type u)}
    (ε ε' : structureSetSheaf B S hS X' ⟶ E) :
    structureSharpSet B S hS p ≫ (smallEtaleDirectImage B S hS p).map
        (structureSharpSet B S hS f ≫ (smallEtaleDirectImage B S hS f).map ε) =
      structureSharpSet B S hS p ≫ (smallEtaleDirectImage B S hS p).map
        (structureSharpSet B S hS f ≫ (smallEtaleDirectImage B S hS f).map ε') ↔
    structureSharpSet B S hS (f ≫ p) ≫ (smallEtaleDirectImage B S hS (f ≫ p)).map ε =
      structureSharpSet B S hS (f ≫ p) ≫ (smallEtaleDirectImage B S hS (f ≫ p)).map ε' := by
  rw [structureSharpSet_comp_map, structureSharpSet_comp_map]
  exact (Eq.congr (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
    (Iso.cancel_iso_inv_right _ _ ((smallToposMorphismTypeU_comp B S hS f p).app E))

/-- **The vanishing clause for a pushed-forward derivation, in direct-image form.**  If a
morphism `r : X' ⟶ Y` factors through `p'`, then `D` and the zero morphism agree after the
structure map of `r`. -/
theorem structureSharpSet_comp_derivationHom (q : Y' ⟶ Y) (r : X' ⟶ Y) (hr : r = p' ≫ q) :
    structureSharpSet B S hS r ≫
        (smallEtaleDirectImage B S hS r).map (derivationHom B S hS p' M D) =
      structureSharpSet B S hS r ≫ (smallEtaleDirectImage B S hS r).map
        (zeroDerivationHom (structureRingSheaf B S hS X') M) := by
  subst hr
  exact (structureSharpSet_comp_map_eq_iff_comp B S hS p' q _ _).mp (congrArg
    (fun m ↦ structureSharpSet B S hS q ≫ (smallEtaleDirectImage B S hS q).map m)
    (structureSharpSetComp_of_structureSharpInverseImage B S hS p' _ _
      (structureSharpInverseImageSet_comp_derivationHom B S hS p' M D)))

/-- **The vanishing clause for `f_*D ∘ f♯`, in direct-image form.** -/
theorem structureSharpSet_comp_pushforwardDerivationHom (f : X' ⟶ X) (p : X ⟶ Y) (q : Y' ⟶ Y)
    (hcomm : f ≫ p = p' ≫ q) :
    structureSharpSet B S hS p ≫ (smallEtaleDirectImage B S hS p).map
        (pushforwardDerivationHom B S hS p' M D f) =
      structureSharpSet B S hS p ≫ (smallEtaleDirectImage B S hS p).map
        (structureSharpSet B S hS f ≫ (smallEtaleDirectImage B S hS f).map
          (zeroDerivationHom (structureRingSheaf B S hS X') M)) :=
  (structureSharpSet_comp_map_eq_iff_comp B S hS f p _ _).mpr
    (structureSharpSet_comp_derivationHom B S hS p' M D q (f ≫ p) hcomm)

/-- **The vanishing clause for `f_*D ∘ f♯`.** -/
theorem structureSharpInverseImageSet_comp_pushforwardDerivationHom (f : X' ⟶ X) (p : X ⟶ Y)
    (q : Y' ⟶ Y) (hcomm : f ≫ p = p' ≫ q) :
    structureSharpInverseImageSet B S hS p ≫ pushforwardDerivationHom B S hS p' M D f =
      structureSharpInverseImageSet B S hS p ≫ (structureSharpSet B S hS f ≫
        (smallEtaleDirectImage B S hS f).map
          (zeroDerivationHom (structureRingSheaf B S hS X') M)) :=
  structureSharpInverseImage_of_structureSharpSetComp B S hS p _ _
    (structureSharpSet_comp_pushforwardDerivationHom B S hS p' M D f p q hcomm)

/-- **The pushed-forward derivation kills the image of `p♯`.** -/
theorem pushforwardDerivationHom_app_eq_zero (f : X' ⟶ X) (p : X ⟶ Y) (q : Y' ⟶ Y)
    (hcomm : f ≫ p = p' ≫ q) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : (sectionsFunctor (SmallEtale.topology B S hS X.1) U).obj
      ((smallEtaleRingedToposHom B S hS p).toToposHom.inverseImage.obj
        (structureSetSheaf B S hS Y))) :
    (sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
        (structureSharpInverseImageSet B S hS p ≫
          pushforwardDerivationHom B S hS p' M D f) a =
      moduleZeroObj (structureRingSheaf B S hS X') M
        (smallEtaleDirectImageSections B S hS f U) := by
  refine Eq.trans (congrArg
    (fun m ↦ (sectionsFunctor (SmallEtale.topology B S hS X.1) U).map m a)
    (structureSharpInverseImageSet_comp_pushforwardDerivationHom
      B S hS p' M D f p q hcomm)) ?_
  exact map_zeroDerivationHom (structureRingSheaf B S hS X') M
    (smallEtaleDirectImageSections B S hS f U) _

/-- **The direct image of a derivation.**  For a commutative square with top edge `f : X' ⟶ X`
and a `Y'`-derivation `D : 𝒪_{X'} ⟶ M`, the composite `f_*D ∘ f♯ : 𝒪_X ⟶ f_*M` is a
`Y`-derivation of `𝒪_X` with values in the direct image of `M`. -/
noncomputable def pushforwardDerivation (f : X' ⟶ X) (p : X ⟶ Y) (q : Y' ⟶ Y)
    (hcomm : f ≫ p = p' ≫ q) :
    PresheafOfModulesOfCommRing.Derivation' ((modulePushforward B S hS f).obj M).val
      (structureSharpInverseImage B S hS p).hom where
  d {U} := AddMonoidHom.mk'
    (fun t ↦ (pushforwardDerivationHom B S hS p' M D f).hom.app U t)
    (pushforwardDerivationHom_add B S hS p' M D f U)
  d_mul {U} a b := pushforwardDerivationHom_mul B S hS p' M D f U a b
  d_map {_U _V} g x :=
    (natTrans_app_map_apply (sectionsRestrict (J := SmallEtale.topology B S hS X.1) g)
      (pushforwardDerivationHom B S hS p' M D f) x).symm
  d_app {U} a := pushforwardDerivationHom_app_eq_zero B S hS p' M D f p q hcomm U a

/-- The direct image of a derivation is the structure map of `f` followed by the direct image of
the derivation, on local sections. -/
theorem pushforwardDerivation_d (f : X' ⟶ X) (p : X ⟶ Y) (q : Y' ⟶ Y)
    (hcomm : f ≫ p = p' ≫ q) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (t : (structureRingSheaf B S hS X).obj.obj U) :
    (pushforwardDerivation B S hS p' M D f p q hcomm).d t =
      (pushforwardDerivationHom B S hS p' M D f).hom.app U t :=
  rfl

/-- `AlgebraicGeometry.Space.pushforwardDerivationHom` written out. -/
theorem pushforwardDerivationHom_eq (f : X' ⟶ X) :
    pushforwardDerivationHom B S hS p' M D f =
      structureSharpSet B S hS f ≫
        (smallEtaleDirectImage B S hS f).map (derivationHom B S hS p' M D) :=
  rfl

end Pushforward

section Universal

variable (f : X' ⟶ X) (p : X ⟶ Y) (p' : X' ⟶ Y') (q : Y' ⟶ Y) (hcomm : f ≫ p = p' ≫ q)

/-- The direct image of the *universal* derivation is the derivation of Stacks 04CX. -/
theorem pushforwardDerivation_universalDerivation :
    pushforwardDerivation B S hS p' (sheafOfDifferentials B S hS p')
        (universalDerivation B S hS p') f p q hcomm =
      pushforwardUniversalDerivation B S hS f p p' q hcomm :=
  rfl

/-- **The direct image of a derivation computes the direct image of a morphism out of the sheaf
of differentials**, on local sections: `f_*g ∘ (f_*d_{X'/Y'} ∘ f♯)` is the direct image of the
derivation `g ∘ d_{X'/Y'}`. -/
theorem modulePushforward_map_comp_pushforwardUniversalDerivationHom
    (M : Modules.{u, u} B S hS X'.1 X'.2) (g : sheafOfDifferentials B S hS p' ⟶ M)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (t : (structureRingSheaf B S hS X).obj.obj U) :
    (((modulePushforward B S hS f).map g).val.app U).hom
        ((pushforwardUniversalDerivationHom B S hS f p').hom.app U t) =
      (pushforwardDerivationHom B S hS p' M
        ((universalDerivation B S hS p').postcomp g.val) f).hom.app U t := by
  have hd : universalDerivationHom B S hS p' ≫
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map g =
      derivationHom B S hS p' M ((universalDerivation B S hS p').postcomp g.val) :=
    CategoryTheory.Sheaf.hom_ext_sections fun _ _ ↦ rfl
  have key : pushforwardUniversalDerivationHom B S hS f p' ≫
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        ((modulePushforward B S hS f).map g) =
      pushforwardDerivationHom B S hS p' M
        ((universalDerivation B S hS p').postcomp g.val) f := by
    rw [pushforwardUniversalDerivationHom_eq, pushforwardDerivationHom_eq,
      moduleSheafFunctor_map_modulePushforward_map]
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine congrArg (fun m ↦ structureSharpSet B S hS f ≫ m) ?_
    refine Eq.trans ((smallEtaleDirectImage B S hS f).map_comp _ _).symm ?_
    exact congrArg (smallEtaleDirectImage B S hS f).map hd
  exact Sheaf.sections_congr key U t

/-- **Precomposition with the comparison map of Stacks 04CX is the direct image of
derivations.**  Under Equation 0619 the morphism `c_f ≫ g : f^*Ω_{X/Y} ⟶ M` corresponds to the
direct image `f_*(g ∘ d_{X'/Y'}) ∘ f♯` of the `Y'`-derivation `g ∘ d_{X'/Y'}` of `𝒪_{X'}`. -/
theorem derivationDirectImageEquiv_sheafOfDifferentialsMap_comp
    (M : Modules.{u, u} B S hS X'.1 X'.2) (g : sheafOfDifferentials B S hS p' ⟶ M) :
    derivationDirectImageEquiv B S hS f p M
        (sheafOfDifferentialsMap B S hS f p p' q hcomm ≫ g) =
      pushforwardDerivation B S hS p' M
        ((universalDerivation B S hS p').postcomp g.val) f p q hcomm := by
  apply PresheafOfModulesOfCommRing.Derivation.ext
  ext U t
  refine Eq.trans (congrArg
    (fun m ↦ ((m.val.app U).hom) ((universalDerivation B S hS p).d t))
    (Adjunction.homEquiv_naturality_right (modulePullbackAdjunction B S hS f)
      (sheafOfDifferentialsMap B S hS f p p' q hcomm) g)) ?_
  refine Eq.trans (congrArg (fun y ↦ (((modulePushforward B S hS f).map g).val.app U).hom y)
    (isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS f p p' q hcomm U t)) ?_
  exact modulePushforward_map_comp_pushforwardUniversalDerivationHom B S hS f p' M g U t

end Universal

end AlgebraicGeometry.Space

end
