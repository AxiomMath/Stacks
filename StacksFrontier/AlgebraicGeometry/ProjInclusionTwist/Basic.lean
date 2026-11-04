module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.TwistIso

/-!
# Tag 01NO's canonical twist comparison, as a named isomorphism

Tag 01NO's third assertion says that for an inclusion `U ⊆ V` of affine opens of the base of a
quasi-coherent graded algebra, the transported comparison map on the `n`-th twist is an
isomorphism. `Stacks.AlgebraicGeometry.RelativeProj.isIso_projInclusionTwistComposite`
proves the invertibility of that comparison **written out as a six-fold composite**, and records
that naming the composite in the hom-set and stating the invertibility of the name exhausts the
kernel's deterministic budget. This file discharges the named statement, by building the
comparison as a composite of *isomorphisms* and taking the named morphism to be its `hom`; that
is why the name lives here and not beside the composite.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistIso`: **the canonical
  isomorphism on the `n`-th twist**, the same six factors in the same order as the composite
  `Stacks.AlgebraicGeometry.RelativeProj.isIso_projInclusionTwistComposite` writes out, composed
  in `Iso`.
* `Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistMap`: its underlying morphism,
  and the library's only name for Tag 01NO's transported comparison map.

## Main results

* `Stacks.AlgebraicGeometry.ProjInclusionTwist.isIso_projInclusionTwistMap`: **the named
  comparison morphism is an isomorphism**, for every `n : ℤ` and every inclusion of affine opens
  of the base, with no hypothesis beyond that situation.
* `Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistMap_eq`: **the named comparison
  morphism is the tag's composite written out**, so the presentation below is not merely
  definitionally the tag's morphism by construction but provably so.
* `Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistMap_eq_split`: the same
  composite bracketed as the first three factors followed by the last three, which is the shape
  in which the comparison's action on a homogeneous global section is available.
* `Stacks.AlgebraicGeometry.ProjInclusionTwist.twistFactor₁_hom` through `twistFactor₆_hom`: the
  factor-by-factor identifications the previous items are assembled from.

## Why the comparison is built in `Iso` rather than in the hom-set

The six factors are the reassociation of
`Stacks.AlgebraicGeometry.RelativeProj.projInclusionMap`, three components of the
pseudofunctoriality isomorphisms `AlgebraicGeometry.Scheme.Modules.pullbackComp`,
`pullbackCongr` and `pullbackId`, and the functor image of the twist map of Tag 01MY's bundle,
which is invertible by
`Stacks.AlgebraicGeometry.TwistBaseChange.isIso_projMapData_twistMap_res_of_le_opens`. Each is
therefore already an isomorphism, so the composite can be formed in `Iso` and the invertibility
of its `hom` is `CategoryTheory.Iso.isIso_hom` — no conversion is requested of the kernel at all.

This is the difference that matters. Writing the same
composite in the hom-set and then asking for *any* conversion against a second presentation of
itself exhausts the kernel's deterministic budget: the equation
`(projInclusionTwistIso …).hom = (the composite written out with ≫)` is refused by `rfl` after
about two minutes of kernel time, and so is `IsIso` of the hom-set composite offered as a proof
of `IsIso` of the `Iso`-composite's `hom`, in either direction. The budget is spent comparing
two presentations of one morphism, not unfolding one definition — so splitting the declaration
cannot help, and the two do not merely "differ by one delta step" on a named definition: no
named definition need be involved.

## Faithfulness of the presentation, proved

`Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistMap_eq` proves that the comparison
map **is** the composite written out with `≫` — the same morphism whose invertibility
`Stacks.AlgebraicGeometry.RelativeProj.isIso_projInclusionTwistComposite` asserts. So the
`Iso` presentation is not merely believed to be the tag's morphism; the identification is
machine-checked, while the conversion that would check it directly is refused.

The way through is the same principle as above, applied to the proof rather than the statement.
`rfl` at these types forces the kernel to reduce the instance. *Applying* a general `rfl` lemma
does not: instantiating `CategoryTheory.Iso.symm_hom`, `CategoryTheory.Iso.app_inv`,
`CategoryTheory.Iso.app_hom`, `CategoryTheory.Iso.symm_inv`,
`CategoryTheory.Functor.mapIso_hom`, `CategoryTheory.asIso_hom` and `trans₆_hom` substitutes for
their variables and demands no reduction at all. Two conditions make it work and both were
needed:

* **every intermediate term is written out**, in its own named theorem, so that `Eq.trans` has no
  unification freedom. The single step
  `Eq.trans (Iso.symm_hom _) (Iso.app_inv _ _)` — with the middle term left to be inferred —
  times out, because the elaborator is free to pick the middle by reducing `Iso.app`, and the
  kernel then has to convert the other spelling against it. The same two lemmas, applied to two
  theorems whose statements pin the middle term, succeed in seconds.
* **the factors are composed with `comp_congr`, never with `rw`**, so no motive is abstracted
  over the offending term.

One asymmetry is worth recording, because it is not predictable from the
statements: `CategoryTheory.Iso.app_hom` applied to a component of
`AlgebraicGeometry.Scheme.Modules.pullbackComp` exhausts the budget, while
`CategoryTheory.Iso.app_inv` applied to a component of the same natural isomorphism does not.
Factor two is such a component and goes through `app_inv` in seconds; factor four needed the
`hom`, so it is spelled as the `symm` of the component of the `symm` — the same type — and
reached through `app_inv` and `CategoryTheory.Iso.symm_inv`. Factors five and six take `app_hom`
directly, on a `pullbackCongr` and a `pullbackId` component respectively, without trouble, so the
obstruction is specific to `pullbackComp`'s `hom`.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj

namespace Stacks.AlgebraicGeometry.ProjInclusionTwist

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj

universe u

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-! ### The six factors, named

Each factor is the `CategoryTheory.Iso.app` (resp. `CategoryTheory.Functor.mapIso`) of the
natural isomorphism (resp. functor and isomorphism) whose component (resp. functor image) is the
corresponding factor of the written-out composite of
`Stacks.AlgebraicGeometry.RelativeProj.isIso_projInclusionTwistComposite`, with
`CategoryTheory.Iso.symm` wherever that factor is an `inv`. They are named so that every
statement below is an application of small named constants rather than one large term. -/

/-- Factor one: the reassociation of `projInclusionMap`. -/
public abbrev twistFactor₁ (U V : S.Opens) (h : U ≤ V) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (n : ℤ) :=
  ((Scheme.Modules.pullbackCongr (projInclusionMap_eq_comp A U V h hU hV)).app
    (twistingSheaf (A.grading V) n)).symm

/-- Factor two: the pseudofunctoriality isomorphism for the factorisation of the morphism. -/
public abbrev twistFactor₂ (U V : S.Opens) (h : U ≤ V) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (n : ℤ) :=
  ((Scheme.Modules.pullbackComp (projInclusionTopSection A U V h hU hV)
    (projMapData (A.grading V) (A.grading U) (A.res h)).hom).app
      (twistingSheaf (A.grading V) n)).symm

/-- Factor three: the functor image of the twist map of Tag 01MY's bundle, which is an
isomorphism by
`Stacks.AlgebraicGeometry.TwistBaseChange.isIso_projMapData_twistMap_res_of_le_opens`. -/
public abbrev twistFactor₃ (U V : S.Opens) (h : U ≤ V) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (n : ℤ) :=
  (Scheme.Modules.pullback (projInclusionTopSection A U V h hU hV)).mapIso
    (@asIso _ _ _ _ ((projMapData (A.grading V) (A.grading U) (A.res h)).twistMap n)
      (Stacks.AlgebraicGeometry.TwistBaseChange.isIso_projMapData_twistMap_res_of_le_opens
        A.toGradedAlgebra (U := ⟨U, hU⟩) (V := ⟨V, hV⟩) h n))

/-- Factor four: the pseudofunctoriality isomorphism for the open-domain inclusion. Written as
the `symm` of the component of the `symm`, which has the same type as the component itself: see
the note on `twistFactor₄_hom` for why that spelling is the one whose `hom` can be identified
within the kernel's budget. -/
public abbrev twistFactor₄ (U V : S.Opens) (h : U ≤ V) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (n : ℤ) :=
  ((Scheme.Modules.pullbackComp (projInclusionTopSection A U V h hU hV)
    (mapDomain (A.grading V) (A.grading U) (A.res h)).ι).symm.app
      (twistingSheaf (A.grading U) n)).symm

/-- Factor five: the congruence isomorphism for the section identity. -/
public abbrev twistFactor₅ (U V : S.Opens) (h : U ≤ V) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (n : ℤ) :=
  (Scheme.Modules.pullbackCongr (projInclusionTopSection_ι A U V h hU hV)).app
    (twistingSheaf (A.grading U) n)

/-- Factor six: the pullback along the identity. -/
public abbrev twistFactor₆ (U : S.Opens) (n : ℤ) :=
  (Scheme.Modules.pullbackId (AlgebraicGeometry.Proj (A.grading U))).app
    (twistingSheaf (A.grading U) n)

/-- **Tag 01NO's canonical isomorphism on the `n`-th twist.** The twist map of Tag 01MY's bundle,
carried along the identification of the open domain with the whole projective spectrum by the
pseudofunctoriality isomorphisms of the pullback, with the reassociation of
`Stacks.AlgebraicGeometry.RelativeProj.projInclusionMap` as the leading factor — the same
six factors, in the same order, as the composite
`Stacks.AlgebraicGeometry.RelativeProj.isIso_projInclusionTwistComposite` writes out, composed as
isomorphisms. -/
public def projInclusionTwistIso (U V : S.Opens) (h : U ≤ V) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (n : ℤ) :
    (Scheme.Modules.pullback (projInclusionMap A U V h hU hV)).obj
        (twistingSheaf (A.grading V) n) ≅
      twistingSheaf (A.grading U) n :=
  twistFactor₁ A U V h hU hV n ≪≫ twistFactor₂ A U V h hU hV n ≪≫
    twistFactor₃ A U V h hU hV n ≪≫ twistFactor₄ A U V h hU hV n ≪≫
      twistFactor₅ A U V h hU hV n ≪≫ twistFactor₆ A U n

/-- **Tag 01NO's transported comparison map on the `n`-th twist**, as the underlying morphism of
`Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistIso`. -/
public def projInclusionTwistMap (U V : S.Opens) (h : U ≤ V) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (n : ℤ) :
    (Scheme.Modules.pullback (projInclusionMap A U V h hU hV)).obj
        (twistingSheaf (A.grading V) n) ⟶
      twistingSheaf (A.grading U) n :=
  (projInclusionTwistIso A U V h hU hV n).hom

/-- **Tag 01NO's transported comparison map on the `n`-th twist is an isomorphism**, for every
`n : ℤ` and for an arbitrary inclusion of affine opens of the base, with no hypothesis beyond
that situation. -/
@[stacks 01NO "canonical twist isomorphisms"]
public theorem isIso_projInclusionTwistMap (U V : S.Opens) (h : U ≤ V) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (n : ℤ) :
    IsIso (projInclusionTwistMap A U V h hU hV n) :=
  (projInclusionTwistIso A U V h hU hV n).isIso_hom

/-- The underlying morphism of the canonical isomorphism is the comparison map, by definition. -/
public theorem projInclusionTwistIso_hom (U V : S.Opens) (h : U ≤ V) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (n : ℤ) :
    (projInclusionTwistIso A U V h hU hV n).hom = projInclusionTwistMap A U V h hU hV n :=
  rfl

/-! ### The faithfulness equation

Each step below is an *application* of one of Mathlib's general `rfl` lemmas, never a `rfl` at
these types, and every intermediate term is written out so that `Eq.trans` has no unification
freedom. Instantiating a general lemma substitutes for its variables and demands no reduction;
asking for `rfl` at the instance demands that `AlgebraicGeometry.Scheme.Modules.pullbackCongr`,
which is `eqToIso (hf ▸ rfl)`, be reduced, and that exhausts the kernel's budget. -/

section General

variable {C : Type*} [Category C]

/-- `hom` of a six-fold composite of isomorphisms, at the level of variables. -/
public theorem trans₆_hom {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : C} (a₁ : X₀ ≅ X₁) (a₂ : X₁ ≅ X₂)
    (a₃ : X₂ ≅ X₃) (a₄ : X₃ ≅ X₄) (a₅ : X₄ ≅ X₅) (a₆ : X₅ ≅ X₆) :
    (a₁ ≪≫ a₂ ≪≫ a₃ ≪≫ a₄ ≪≫ a₅ ≪≫ a₆).hom =
      a₁.hom ≫ a₂.hom ≫ a₃.hom ≫ a₄.hom ≫ a₅.hom ≫ a₆.hom :=
  rfl

/-- Congruence for a composite, at the level of variables: used instead of `rw`, which abstracts
a motive over the offending term. -/
public theorem comp_congr {X Y Z : C} {a a' : X ⟶ Y} {b b' : Y ⟶ Z} (ha : a = a')
    (hb : b = b') : a ≫ b = a' ≫ b' :=
  (congrArg (fun z => z ≫ b) ha).trans (congrArg (fun z => a' ≫ z) hb)

/-- `(a ≫ b ≫ c) ≫ d = a ≫ b ≫ c ≫ d`, at the level of variables. This is the one
reassociation separating the right-associated six-fold composite of
`Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistMap_eq` from the `3 + 3`
bracketing in which the comparison's action on a homogeneous global section is computed; see
`Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistMap_eq_split`. -/
public theorem comp₃_comp {X₀ X₁ X₂ X₃ X₄ : C} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃)
    (d : X₃ ⟶ X₄) : (a ≫ b ≫ c) ≫ d = a ≫ b ≫ c ≫ d := by
  rw [Category.assoc, Category.assoc]

end General

variable (U V : S.Opens) (h : U ≤ V) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (n : ℤ)

/-- Factor one's `hom`, step one: `CategoryTheory.Iso.symm_hom`. -/
public theorem twistFactor₁_hom_aux : (twistFactor₁ A U V h hU hV n).hom =
    ((Scheme.Modules.pullbackCongr (projInclusionMap_eq_comp A U V h hU hV)).app
      (twistingSheaf (A.grading V) n)).inv :=
  Iso.symm_hom _

/-- Factor one's `hom`, step two: `CategoryTheory.Iso.app_inv`. -/
public theorem twistFactor₁_hom_app :
    ((Scheme.Modules.pullbackCongr (projInclusionMap_eq_comp A U V h hU hV)).app
        (twistingSheaf (A.grading V) n)).inv =
      (Scheme.Modules.pullbackCongr (projInclusionMap_eq_comp A U V h hU hV)).inv.app
        (twistingSheaf (A.grading V) n) :=
  Iso.app_inv _ _

/-- **Factor one's `hom` is the first factor of the tag's composite.** -/
public theorem twistFactor₁_hom : (twistFactor₁ A U V h hU hV n).hom =
    (Scheme.Modules.pullbackCongr (projInclusionMap_eq_comp A U V h hU hV)).inv.app
      (twistingSheaf (A.grading V) n) :=
  (twistFactor₁_hom_aux A U V h hU hV n).trans (twistFactor₁_hom_app A U V h hU hV n)

/-- Factor two's `hom`, step one: `CategoryTheory.Iso.symm_hom`. -/
public theorem twistFactor₂_hom_aux : (twistFactor₂ A U V h hU hV n).hom =
    ((Scheme.Modules.pullbackComp (projInclusionTopSection A U V h hU hV)
      (projMapData (A.grading V) (A.grading U) (A.res h)).hom).app
        (twistingSheaf (A.grading V) n)).inv :=
  Iso.symm_hom _

/-- Factor two's `hom`, step two: `CategoryTheory.Iso.app_inv`. -/
public theorem twistFactor₂_hom_app :
    ((Scheme.Modules.pullbackComp (projInclusionTopSection A U V h hU hV)
        (projMapData (A.grading V) (A.grading U) (A.res h)).hom).app
          (twistingSheaf (A.grading V) n)).inv =
      (Scheme.Modules.pullbackComp (projInclusionTopSection A U V h hU hV)
        (projMapData (A.grading V) (A.grading U) (A.res h)).hom).inv.app
          (twistingSheaf (A.grading V) n) :=
  Iso.app_inv _ _

/-- **Factor two's `hom` is the second factor of the tag's composite.** -/
public theorem twistFactor₂_hom : (twistFactor₂ A U V h hU hV n).hom =
    (Scheme.Modules.pullbackComp (projInclusionTopSection A U V h hU hV)
      (projMapData (A.grading V) (A.grading U) (A.res h)).hom).inv.app
        (twistingSheaf (A.grading V) n) :=
  (twistFactor₂_hom_aux A U V h hU hV n).trans (twistFactor₂_hom_app A U V h hU hV n)

/-- Factor three's `hom`, step one: `CategoryTheory.Functor.mapIso_hom`. -/
public theorem twistFactor₃_hom_aux : (twistFactor₃ A U V h hU hV n).hom =
    (Scheme.Modules.pullback (projInclusionTopSection A U V h hU hV)).map
      (@asIso _ _ _ _ ((projMapData (A.grading V) (A.grading U) (A.res h)).twistMap n)
        (Stacks.AlgebraicGeometry.TwistBaseChange.isIso_projMapData_twistMap_res_of_le_opens
          A.toGradedAlgebra (U := ⟨U, hU⟩) (V := ⟨V, hV⟩) h n)).hom :=
  Functor.mapIso_hom _ _

/-- Factor three's `hom`, step two: `CategoryTheory.asIso_hom` under the functor. -/
public theorem twistFactor₃_hom_asIso :
    (Scheme.Modules.pullback (projInclusionTopSection A U V h hU hV)).map
        (@asIso _ _ _ _ ((projMapData (A.grading V) (A.grading U) (A.res h)).twistMap n)
          (Stacks.AlgebraicGeometry.TwistBaseChange.isIso_projMapData_twistMap_res_of_le_opens
            A.toGradedAlgebra (U := ⟨U, hU⟩) (V := ⟨V, hV⟩) h n)).hom =
      (Scheme.Modules.pullback (projInclusionTopSection A U V h hU hV)).map
        ((projMapData (A.grading V) (A.grading U) (A.res h)).twistMap n) :=
  congrArg (fun z => (Scheme.Modules.pullback (projInclusionTopSection A U V h hU hV)).map z)
    (@asIso_hom _ _ _ _ ((projMapData (A.grading V) (A.grading U) (A.res h)).twistMap n)
      (Stacks.AlgebraicGeometry.TwistBaseChange.isIso_projMapData_twistMap_res_of_le_opens
        A.toGradedAlgebra (U := ⟨U, hU⟩) (V := ⟨V, hV⟩) h n))

/-- **Factor three's `hom` is the third factor of the tag's composite.** -/
public theorem twistFactor₃_hom : (twistFactor₃ A U V h hU hV n).hom =
    (Scheme.Modules.pullback (projInclusionTopSection A U V h hU hV)).map
      ((projMapData (A.grading V) (A.grading U) (A.res h)).twistMap n) :=
  (twistFactor₃_hom_aux A U V h hU hV n).trans (twistFactor₃_hom_asIso A U V h hU hV n)

/-- Factor four's `hom`, step one: `CategoryTheory.Iso.symm_hom`. -/
public theorem twistFactor₄_hom_aux : (twistFactor₄ A U V h hU hV n).hom =
    ((Scheme.Modules.pullbackComp (projInclusionTopSection A U V h hU hV)
      (mapDomain (A.grading V) (A.grading U) (A.res h)).ι).symm.app
        (twistingSheaf (A.grading U) n)).inv :=
  Iso.symm_hom _

/-- Factor four's `hom`, step two: `CategoryTheory.Iso.app_inv`. -/
public theorem twistFactor₄_hom_app :
    ((Scheme.Modules.pullbackComp (projInclusionTopSection A U V h hU hV)
        (mapDomain (A.grading V) (A.grading U) (A.res h)).ι).symm.app
          (twistingSheaf (A.grading U) n)).inv =
      (Scheme.Modules.pullbackComp (projInclusionTopSection A U V h hU hV)
        (mapDomain (A.grading V) (A.grading U) (A.res h)).ι).symm.inv.app
          (twistingSheaf (A.grading U) n) :=
  Iso.app_inv _ _

/-- Factor four's `hom`, step three: `CategoryTheory.Iso.symm_inv`, under the component. -/
public theorem twistFactor₄_hom_symm :
    (Scheme.Modules.pullbackComp (projInclusionTopSection A U V h hU hV)
        (mapDomain (A.grading V) (A.grading U) (A.res h)).ι).symm.inv.app
          (twistingSheaf (A.grading U) n) =
      (Scheme.Modules.pullbackComp (projInclusionTopSection A U V h hU hV)
        (mapDomain (A.grading V) (A.grading U) (A.res h)).ι).hom.app
          (twistingSheaf (A.grading U) n) :=
  congrArg (fun z => z.app (twistingSheaf (A.grading U) n))
    (Iso.symm_inv (Scheme.Modules.pullbackComp (projInclusionTopSection A U V h hU hV)
      (mapDomain (A.grading V) (A.grading U) (A.res h)).ι))

/-- **Factor four's `hom` is the fourth factor of the tag's composite.**

`CategoryTheory.Iso.app_hom` applied directly to the component of
`AlgebraicGeometry.Scheme.Modules.pullbackComp` exhausts the kernel's deterministic budget,
while `CategoryTheory.Iso.app_inv` applied to a component of the same natural isomorphism does
not, and the asymmetry is real: factor two is a component of a `pullbackComp` too and
goes through `app_inv` in seconds. So factor four is spelled as the `symm` of the component of
the `symm`, which has the same type, and its `hom` is reached through `app_inv`. -/
public theorem twistFactor₄_hom : (twistFactor₄ A U V h hU hV n).hom =
    (Scheme.Modules.pullbackComp (projInclusionTopSection A U V h hU hV)
      (mapDomain (A.grading V) (A.grading U) (A.res h)).ι).hom.app
        (twistingSheaf (A.grading U) n) :=
  ((twistFactor₄_hom_aux A U V h hU hV n).trans
    (twistFactor₄_hom_app A U V h hU hV n)).trans (twistFactor₄_hom_symm A U V h hU hV n)

/-- **Factor five's `hom` is the fifth factor of the tag's composite.** -/
public theorem twistFactor₅_hom : (twistFactor₅ A U V h hU hV n).hom =
    (Scheme.Modules.pullbackCongr (projInclusionTopSection_ι A U V h hU hV)).hom.app
      (twistingSheaf (A.grading U) n) :=
  Iso.app_hom _ _

/-- **Factor six's `hom` is the sixth factor of the tag's composite.** -/
public theorem twistFactor₆_hom : (twistFactor₆ A U n).hom =
    (Scheme.Modules.pullbackId (AlgebraicGeometry.Proj (A.grading U))).hom.app
      (twistingSheaf (A.grading U) n) :=
  Iso.app_hom _ _

/-- **The comparison map is the tag's composite, written out.** This equation holds "by
construction" but cannot be checked by a direct conversion; it is proved by applying the general `rfl` lemmas factor by factor and composing the results with
`comp_congr`, so that no conversion at these types is ever requested of the kernel. -/
public theorem projInclusionTwistMap_eq : projInclusionTwistMap A U V h hU hV n =
    (Scheme.Modules.pullbackCongr (projInclusionMap_eq_comp A U V h hU hV)).inv.app
      (twistingSheaf (A.grading V) n) ≫
    (Scheme.Modules.pullbackComp (projInclusionTopSection A U V h hU hV)
        (projMapData (A.grading V) (A.grading U) (A.res h)).hom).inv.app
      (twistingSheaf (A.grading V) n) ≫
    (Scheme.Modules.pullback (projInclusionTopSection A U V h hU hV)).map
      ((projMapData (A.grading V) (A.grading U) (A.res h)).twistMap n) ≫
    (Scheme.Modules.pullbackComp (projInclusionTopSection A U V h hU hV)
        (mapDomain (A.grading V) (A.grading U) (A.res h)).ι).hom.app
      (twistingSheaf (A.grading U) n) ≫
    (Scheme.Modules.pullbackCongr (projInclusionTopSection_ι A U V h hU hV)).hom.app
      (twistingSheaf (A.grading U) n) ≫
    (Scheme.Modules.pullbackId
      (AlgebraicGeometry.Proj (A.grading U))).hom.app (twistingSheaf (A.grading U) n) :=
  (trans₆_hom (twistFactor₁ A U V h hU hV n) (twistFactor₂ A U V h hU hV n)
      (twistFactor₃ A U V h hU hV n) (twistFactor₄ A U V h hU hV n)
      (twistFactor₅ A U V h hU hV n) (twistFactor₆ A U n)).trans
    (comp_congr (twistFactor₁_hom A U V h hU hV n)
      (comp_congr (twistFactor₂_hom A U V h hU hV n)
        (comp_congr (twistFactor₃_hom A U V h hU hV n)
          (comp_congr (twistFactor₄_hom A U V h hU hV n)
            (comp_congr (twistFactor₅_hom A U V h hU hV n)
              (twistFactor₆_hom A U n))))))

/-- **The comparison map is the tag's composite, bracketed as the first three factors followed
by the last three.**

This is the shape in which the comparison's action on a homogeneous global section is available
(`Stacks.AlgebraicGeometry.ProjInclusionDegreeSection.composite_degreeSection`), whose split
point is forced by an elaboration obstruction recorded there. The reassociation is performed by
`Stacks.AlgebraicGeometry.ProjInclusionTwist.comp₃_comp` at the level of variables, with the four
factors supplied explicitly: with the composite of the last three left to be inferred the
elaborator does not finish. -/
public theorem projInclusionTwistMap_eq_split : projInclusionTwistMap A U V h hU hV n =
    ((Scheme.Modules.pullbackCongr (projInclusionMap_eq_comp A U V h hU hV)).inv.app
        (twistingSheaf (A.grading V) n) ≫
      (Scheme.Modules.pullbackComp (projInclusionTopSection A U V h hU hV)
          (projMapData (A.grading V) (A.grading U) (A.res h)).hom).inv.app
        (twistingSheaf (A.grading V) n) ≫
      (Scheme.Modules.pullback (projInclusionTopSection A U V h hU hV)).map
        ((projMapData (A.grading V) (A.grading U) (A.res h)).twistMap n)) ≫
    ((Scheme.Modules.pullbackComp (projInclusionTopSection A U V h hU hV)
          (mapDomain (A.grading V) (A.grading U) (A.res h)).ι).hom.app
        (twistingSheaf (A.grading U) n) ≫
      (Scheme.Modules.pullbackCongr (projInclusionTopSection_ι A U V h hU hV)).hom.app
        (twistingSheaf (A.grading U) n) ≫
      (Scheme.Modules.pullbackId
        (AlgebraicGeometry.Proj (A.grading U))).hom.app (twistingSheaf (A.grading U) n)) :=
  (projInclusionTwistMap_eq A U V h hU hV n).trans (by simp only [Category.assoc])

end Stacks.AlgebraicGeometry.ProjInclusionTwist

end
