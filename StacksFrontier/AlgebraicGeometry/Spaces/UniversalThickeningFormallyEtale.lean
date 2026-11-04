module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Subfunctor.Image
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFirstOrderIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentials
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSchemeVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FormallyEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalFirstOrderThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningUnramified

/-!
# Formally étale morphisms and their universal first order thickening

Let `S` be a scheme and let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`.  Writing
`X ⊂ X'` for a universal first order thickening of `X` over `Y` in the sense of Stacks 0607,
Stacks 0614 asserts the equivalence of

1. `f` is formally étale,
2. `f` is formally unramified and `X' = X`,
3. `f` is formally unramified and `𝒞_{X/Y} = 0`,
4. `Ω_{X/Y} = 0` and `𝒞_{X/Y} = 0`.

The equivalence of (1) and (2) is proved here outright.  One direction is the universal property
of Stacks 0602 read against the thickening `X ⊂ X'` itself: a formally étale `f` lifts the
identity of `X` across that thickening by Stacks 0611, and the uniqueness clause of Stacks 0602
turns the resulting retraction of the inclusion into an inverse for it.  The other direction
turns the universal property into formal étaleness: when the inclusion `X ⊂ X'` is an
isomorphism, the dotted arrow of Stacks 0602 for the thickening attached to a square-zero closed
immersion of objects of the site *is* the lift required by Stacks 049S, part (2).

The equivalence of (2) and (3) is proved here outright too.  In one direction the defining ideal
of a closed subspace which is the whole space vanishes, and the conormal sheaf is an inverse
image of that ideal.  In the other direction the source's identity `𝒞_{X/Y} = 𝓘` is used, which
for a *first-order* thickening is the invertibility of the unit `𝓘 ⟶ i_*i^*𝓘` of `i^* ⊣ i_*`
supplied by `AlgebraicGeometry.Space.firstOrderConormalModuleIso`: a vanishing conormal sheaf
forces the defining ideal of `X` in `X'` to vanish on every étale chart, and the injectivity
clause of Stacks 03MB returns `X' = X`.

Clause (4) is reached from the other three outright.  That (1), (2) and (3) each imply (4) is
the forward direction of Stacks 04G9 — a formally unramified morphism has a vanishing sheaf of
differentials — which is available with no assumed input as
`AlgebraicGeometry.Space.isZero_sheafOfDifferentials_of_formallyUnramified`, built on the
vanishing shadow of Stacks 04CS proved in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeVanishing.lean`.

Clause (4) implies the other three too, and with no formal unramifiedness among its hypotheses.
The source reaches formal unramifiedness from `Ω_{X/Y} = 0` by the backward direction of
Stacks 04G9, which this development does not have; but it does not need it here, because the
universal property of Stacks 0602 already forces it:
`AlgebraicGeometry.Space.formallyUnramified_of_isUniversal` derives the formal unramifiedness of
`f` from the thickening alone, so the `formallyUnramified` field of the datum of Stacks 0607 is
redundant.  `AlgebraicGeometry.Space.formallyEtale_of_isZero_conormalSheaf_of_isUniversal` is
clause (4) implying clause (1) stated with that field removed.

Finally the thickening itself leaves the statement.  Stacks 0606 — the existence of a universal
first order thickening of a formally unramified morphism — is available in this development as
`AlgebraicGeometry.Space.nonempty_universalFirstOrderThickening`, so the four clauses can be
stated with the thickening quantified over instead of passed in, and the tag holds with no
hypotheses at all: `AlgebraicGeometry.Space.formallyEtale_tfae_unconditional`.

## Main results

* `AlgebraicGeometry.Space.formallyEtale_iff_sub_eq_top`: **Stacks 0614, the equivalence of (1)
  and (2)**, with no hypothesis beyond the datum of Stacks 0607.
* `AlgebraicGeometry.Space.isZero_conormalSheaf_of_sub_eq_top`: **Stacks 0614, (2) implies (3)**.
* `AlgebraicGeometry.Space.sub_eq_top_of_isZero_conormalSheaf`: **Stacks 0614, (3) implies (2)**,
  also with no hypothesis beyond that datum.  With the equivalence of (1) and (2) it derives
  clause (1) from clause (3) too, so (1), (2) and (3) are mutually equivalent outright.
* `isZero_sheafOfDifferentials_and_isZero_conormalSheaf_of_formallyUnramified`:
  **Stacks 0614, (3) implies (4)**, hence (1) implies (4) and (2) implies (4) as well, since
  (1), (2) and (3) are mutually equivalent outright.  Its content is the forward direction of
  Stacks 04G9, carried with no assumed input.
* `AlgebraicGeometry.Space.formallyUnramified_of_isUniversal`: a morphism admitting a universal
  first order thickening in the sense of Stacks 0602 is formally unramified.  This is what makes
  the `formallyUnramified` field of `AlgebraicGeometry.Space.UniversalFirstOrderThickening`
  redundant, and `AlgebraicGeometry.Space.UniversalFirstOrderThickening.ofIsUniversal` is the
  datum of Stacks 0607 assembled without it.
* `AlgebraicGeometry.Space.isZero_sheafOfDifferentials_of_isUniversal`: the first conjunct of
  clause (4) is likewise implied by the thickening, so it cannot be a hypothesis that does work.
* `AlgebraicGeometry.Space.formallyEtale_of_isZero_conormalSheaf_of_isUniversal`: **Stacks 0614,
  (4) implies (1)**, with no formal unramifiedness among the hypotheses — the field is derived,
  as the source derives it.
* `AlgebraicGeometry.Space.formallyEtale_of_isZero_sheafOfDifferentials_of_isZero_conormalSheaf`:
  the same implication for the datum of Stacks 0607.
* `AlgebraicGeometry.Space.formallyEtale_tfae_of_isUniversal`: **Stacks 0614**, the four
  conditions in one statement, with no hypothesis beyond a universal first order thickening in
  the sense of Stacks 0602.  `AlgebraicGeometry.Space.formallyEtale_tfae` is the same for the
  datum of Stacks 0607.
* `AlgebraicGeometry.Space.formallyEtale_tfae_unconditional`: **Stacks 0614 with no hypotheses at
  all.**  The thickening leaves the statement: clauses (2) and (3) are read with `∀` over the
  universal first order thickenings of `X` over `Y` and clause (4) with `∃`, and Stacks 0606
  (`AlgebraicGeometry.Space.nonempty_universalFirstOrderThickening`) is what passes from the one
  to the other.  `AlgebraicGeometry.Space.forall_isZero_conormalSheaf_iff_exists` shows the two
  quantifiers agree, which is the source's definite article.  The equivalence of (1) and (4) is
  read off the list as
  `formallyEtale_iff_isZero_sheafOfDifferentials_and_exists_isZero_conormalSheaf`.

## Implementation notes

**Most statements here take the thickening as a parameter; the tag itself does not.**  Clauses
(2) and (3) of the source speak of *the* universal first order thickening of `X` over `Y` and of
the conormal sheaf `𝒞_{X/Y}` defined from it, and Stacks 0607 defines `𝒞_{X/Y}` only relative to
such a thickening, so `𝒞_{X/Y}` cannot be named without one.  The individual implications below
therefore take a datum `t : AlgebraicGeometry.Space.UniversalFirstOrderThickening`, exactly as
the formalized Stacks 0607 and Stacks 060A do.  That is the shape in which the implications are
proved, not a hypothesis the tag needs: Stacks 0606 is available in this development, as
`AlgebraicGeometry.Space.nonempty_universalFirstOrderThickening` of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/UniversalExistence.lean`, and
`AlgebraicGeometry.Space.formallyEtale_tfae_unconditional` spends it to state the whole tag with
the thickening quantified away and no hypotheses at all.

The datum carries the formal unramifiedness of `f` that the source assumes, so the first
conjunct of clauses (2) and (3) is never an extra condition in the parameterized statements; it
is kept in them because it is what the source writes.  That field is moreover *redundant*: it
follows from the universal property, by
`AlgebraicGeometry.Space.formallyUnramified_of_isUniversal`, and
`AlgebraicGeometry.Space.UniversalFirstOrderThickening.ofIsUniversal` builds the datum without
assuming it.

**"`X' = X`" is "the inclusion is everything".**  A thickening presents its smaller space as a
`CategoryTheory.Subfunctor` of the ambient space, so the source's equality of `X'` with `X` is
`t.sub = ⊤`, equivalently invertibility of the inclusion
(`CategoryTheory.Subfunctor.eq_top_iff_isIso`).  It is an equality of subfunctors of one ambient
space and not an abstract isomorphism `X ≅ X'`, which is the reading the source intends: the
universal thickening is always received by a map from `X`, and the content of clause (2) is that
*that* map is invertible.

**Formal étaleness is read through the Yoneda translation.**  Stacks 049S, part (2) is phrased
with sections of the two presheaves over affine objects of the site; the universal property of
Stacks 0602 delivers transformations of presheaves.  The private lemma below translates the
latter into the former, exactly as `AlgebraicGeometry.Space.formallyUnramified_of_yoneda_hom_ext`
does for part (3) in
`StacksFrontier/AlgebraicGeometry/Spaces/UniversalThickeningUnramified.lean`.  No affineness of the
test objects is used in the proof of (2) ⟹ (1), so what is really established there is the
stronger statement with affineness dropped; it is Stacks 0611 for `f` in the presence of the
datum, and is not stated separately.

## Where (3) ⟹ (2) gets the source's `𝒞_{X/Y} = 𝓘`

The step the source makes by "`𝒞_{X/Y} = 𝒞_{X/X'}` is the ideal sheaf of `X` in `X'`" is the
identification of Stacks 04CN, part (3) in the square-zero case, and that case *is* available
here even though the general one is not: for a first-order thickening the quotient `𝓘/𝓘²` is
`𝓘` itself, so the unit `𝓘 ⟶ i_*i^*𝓘` of `i^* ⊣ i_*` is invertible.  That invertibility is
`AlgebraicGeometry.Space.firstOrderConormalModuleIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleFirstOrderIdeal.lean`, which gets it from
the essential-image clause of Stacks 04CJ, free for a thickening.  The conormal *sheaf* of
Stacks 0607 is the conormal module of the thickening pulled back along the identification of
`X` with the smaller space; that identification is an isomorphism, and the unit law of
Stacks 03LU (`AlgebraicGeometry.Space.modulePullbackIdIso`) together with the composition law
(`AlgebraicGeometry.Space.modulePullbackCompIso`) carries a vanishing conormal sheaf back to a
vanishing conormal module.  The "What is not proved" section of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModule.lean`, which records part (3) as
unavailable, is about an arbitrary closed subspace, and that is not what is used here.

## What is not proved

Nothing of Stacks 0614 is open.  All four clauses are proved mutually equivalent, with no
hypotheses whatever, in `AlgebraicGeometry.Space.formallyEtale_tfae_unconditional`.

* **The backward direction of Stacks 04G9 is not needed here.**  The source passes from
  clause (4) to the other three through it: `Ω_{X/Y} = 0` makes `f` formally unramified, which
  is what lets `𝒞_{X/Y}` mean anything.  That direction is proved, in
  `StacksFrontier/AlgebraicGeometry/Spaces/SchemeSpaceDifferentialsVanishing.lean`, downstream of
  this file.  Clause (4) names a universal first order thickening, because `𝒞_{X/Y}` is defined
  relative to one, and a thickening forces formal unramifiedness by
  `AlgebraicGeometry.Space.formallyUnramified_of_isUniversal` — which is exactly what the source
  extracts from `Ω_{X/Y} = 0`.  So the step out of clause (4) goes through the thickening
  instead, and `Ω_{X/Y} = 0` is never the thing converted.

## References

* [Stacks Project, Tag 0614](https://stacks.math.columbia.edu/tag/0614)
* [Stacks Project, Tag 0602](https://stacks.math.columbia.edu/tag/0602)
* [Stacks Project, Tag 0606](https://stacks.math.columbia.edu/tag/0606)
* [Stacks Project, Tag 0607](https://stacks.math.columbia.edu/tag/0607)
* [Stacks Project, Tag 0611](https://stacks.math.columbia.edu/tag/0611)
* [Stacks Project, Tag 049S](https://stacks.math.columbia.edu/tag/049S)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT)
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04G9](https://stacks.math.columbia.edu/tag/04G9)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Formal étaleness from unique dotted arrows out of representable presheaves -/

/-- The Yoneda image of a square-zero closed immersion of objects of the site is a
monomorphism of presheaves: a closed immersion of schemes is a monomorphism, the functor to
schemes is faithful, and a monomorphism of presheaves of types is one sectionwise. -/
private theorem mono_yoneda_map_of_isSquareZeroClosedImmersion {P Q : BigFppfOver B S hS}
    (i : P ⟶ Q) (hi : IsSquareZeroClosedImmersion B S hS i) :
    Mono (yoneda.map i) := by
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion
    ((BigFppfOver.toScheme B S hS).map i) := hi.1
  have hmono : Mono ((BigFppfOver.toScheme B S hS).map i) := inferInstance
  have : Mono i := (BigFppfOver.toScheme B S hS).mono_of_mono_map hmono
  suffices _hall : ∀ R, Mono ((yoneda.map i).app R) from NatTrans.mono_of_mono_app _
  intro R
  rw [mono_iff_injective]
  exact fun g₁ g₂ hg => (cancel_mono i).1 (by simpa using hg)

/-- Formal étaleness, from existence and uniqueness of dotted arrows read as transformations
out of representable presheaves.  The test immersions are not required to be affine, which is
why the hypothesis is stronger than the conclusion unwinds to. -/
private theorem formallyEtale_of_yoneda_existsUnique
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    (h : ∀ {P Q : BigFppfOver B S hS} (i : P ⟶ Q), IsSquareZeroClosedImmersion B S hS i →
      ∀ (u : yoneda.obj P ⟶ F) (v : yoneda.obj Q ⟶ G), yoneda.map i ≫ v = u ≫ a →
        ∃! w : yoneda.obj Q ⟶ F, yoneda.map i ≫ w = u ∧ w ≫ a = v) :
    FormallyEtale a := by
  intro P Q _ _ i hi x y hxy
  obtain ⟨w, ⟨hw₁, hw₂⟩, hwu⟩ := h i hi (yonedaEquiv.symm x) (yonedaEquiv.symm y) (by
    rw [yonedaEquiv_symm_naturality_left, yonedaEquiv_symm_naturality_right, hxy])
  refine ⟨yonedaEquiv w, ⟨?_, ?_⟩, ?_⟩
  · refine yonedaEquiv.symm.injective ?_
    rw [← yonedaEquiv_symm_naturality_left, Equiv.symm_apply_apply]
    exact hw₁
  · refine yonedaEquiv.symm.injective ?_
    rw [← yonedaEquiv_symm_naturality_right, Equiv.symm_apply_apply]
    exact hw₂
  · intro z hz
    have hzw := hwu (yonedaEquiv.symm z)
      ⟨by rw [yonedaEquiv_symm_naturality_left, hz.1],
        by rw [yonedaEquiv_symm_naturality_right, hz.2]⟩
    rw [← hzw, Equiv.apply_symm_apply]

/-! ### The equivalence of (1) and (2) -/

variable {B S hS} {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}

/-- **Stacks 0614, (1) implies (2).**  If `f : X ⟶ Y` is formally étale then the smaller space
of a universal first order thickening of `X` over `Y` is the whole ambient space.

Stacks 0611 drops the affineness of the test objects from formal étaleness, so `f` lifts the
inverse of the identification of `X` with the smaller space across the thickening `X ⊂ X'`
itself; the lift is a retraction of the inclusion, and the uniqueness clause of Stacks 0602
applied to the two endomorphisms `𝟙` and "retract, then include" of `X'` shows that it is a
two-sided inverse. -/
theorem sub_eq_top_of_formallyEtale (t : UniversalFirstOrderThickening B S hS f)
    (hf : FormallyEtale f.hom) : t.sub = ⊤ := by
  obtain ⟨c, ⟨hc₁, hc₂⟩, -⟩ := FormallyEtale.existsUnique_lift_of_firstOrderThickening
    B S hS f hf t.sub t.isUniversal.firstOrder t.sourceIso.inv t.toBase.hom
    (by rw [← t.sourceIso_ι_toBase, Iso.inv_hom_id_assoc])
  have h₁ : t.sub.ι ≫ c ≫ t.sourceIso.hom = 𝟙 t.sub.toFunctor := by
    rw [← Category.assoc, hc₁, Iso.inv_hom_id]
  have h₂ : (c ≫ t.sourceIso.hom) ≫ t.sub.ι = 𝟙 t.ambient.obj := by
    refine t.isUniversal.eq_of_lifts t.sub t.isUniversal.firstOrder (𝟙 t.sub.toFunctor)
      t.toBase.hom _ _ ?_ ?_ (by simp) (Category.id_comp _)
    · simp only [Category.assoc, Category.id_comp]
      rw [← Category.assoc, hc₁, Iso.inv_hom_id_assoc]
    · simp only [Category.assoc, t.sourceIso_ι_toBase]
      exact hc₂
  rw [Subfunctor.eq_top_iff_isIso]
  exact ⟨c ≫ t.sourceIso.hom, h₁, h₂⟩

/-- **Stacks 0614, (2) implies (1).**  If the smaller space of a universal first order
thickening of `X` over `Y` is the whole ambient space, then `f : X ⟶ Y` is formally étale.

A square-zero closed immersion `T ⟶ T'` of objects of the site presents `T` as a first-order
thickening of the algebraic space represented by `T'`, so the universal property of Stacks 0602
produces a unique morphism `T' ⟶ X'` solving the lifting problem; composing with the inverse of
the inclusion `X ⊂ X'` turns it into the unique lift into `X` that Stacks 049S, part (2)
asks for. -/
theorem formallyEtale_of_sub_eq_top (t : UniversalFirstOrderThickening B S hS f)
    (hsub : t.sub = ⊤) : FormallyEtale f.hom := by
  have hι : IsIso t.sub.ι := by rw [hsub]; infer_instance
  obtain ⟨e, d, hed, hde, he⟩ : ∃ (e : X.obj ⟶ t.ambient.obj) (d : t.ambient.obj ⟶ X.obj),
      e ≫ d = 𝟙 X.obj ∧ d ≫ e = 𝟙 t.ambient.obj ∧ t.sourceIso.hom ≫ t.sub.ι = e := by
    refine ⟨t.sourceIso.hom ≫ t.sub.ι, inv t.sub.ι ≫ t.sourceIso.inv, ?_, ?_, rfl⟩ <;> simp
  have hef : e ≫ t.toBase.hom = f.hom := by
    rw [← he, Category.assoc, t.sourceIso_ι_toBase]
  refine formallyEtale_of_yoneda_existsUnique B S hS f.hom ?_
  intro P Q i hi u v huv
  have hmono : Mono (yoneda.map i) := mono_yoneda_map_of_isSquareZeroClosedImmersion B S hS i hi
  obtain ⟨G, hG, ρ, σ, hρσ, hσρ, hρ⟩ :
      ∃ (G : Subfunctor (yoneda.obj Q))
        (_ : IsFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).obj Q) G)
        (ρ : yoneda.obj P ⟶ G.toFunctor) (σ : G.toFunctor ⟶ yoneda.obj P),
        ρ ≫ σ = 𝟙 (yoneda.obj P) ∧ σ ≫ ρ = 𝟙 G.toFunctor ∧ ρ ≫ G.ι = yoneda.map i := by
    refine ⟨Subfunctor.range (yoneda.map i), isFirstOrderThickening_range_yoneda_map B S hS i hi,
      Subfunctor.toRange (yoneda.map i), inv (Subfunctor.toRange (yoneda.map i)),
      IsIso.hom_inv_id _, IsIso.inv_hom_id _, Subfunctor.toRange_ι _⟩
  have hGι : σ ≫ yoneda.map i = G.ι := by
    rw [← hρ, ← Category.assoc, hσρ, Category.id_comp]
  have hcomm : G.ι ≫ v = (σ ≫ u ≫ t.sourceIso.hom) ≫ t.sub.ι ≫ t.toBase.hom := by
    rw [← hGι, Category.assoc, huv, ← t.sourceIso_ι_toBase]
    simp only [Category.assoc]
  have hex : ∃! w : yoneda.obj Q ⟶ t.ambient.obj,
      G.ι ≫ w = (σ ≫ u ≫ t.sourceIso.hom) ≫ t.sub.ι ∧ w ≫ t.toBase.hom = v :=
    t.isUniversal.existsUnique_lift (T' := (schemeSpaceFunctor B S hS).obj Q) G hG
      (σ ≫ u ≫ t.sourceIso.hom) v hcomm
  obtain ⟨c, ⟨hc₁, hc₂⟩, hcu⟩ := hex
  have hic : yoneda.map i ≫ c = u ≫ e := by
    rw [← hρ, Category.assoc, hc₁, ← he]
    simp only [Category.assoc]
    rw [← Category.assoc, hρσ, Category.id_comp]
  refine ⟨c ≫ d, ⟨?_, ?_⟩, fun w hw => ?_⟩
  · rw [← Category.assoc, hic, Category.assoc, hed, Category.comp_id]
  · rw [← hef, Category.assoc, ← Category.assoc d, hde, Category.id_comp, hc₂]
  · have hwc : w ≫ e = c := by
      refine hcu (w ≫ e) ⟨?_, ?_⟩
      · rw [← hGι, Category.assoc, ← Category.assoc (yoneda.map i), hw.1, ← he]
        simp only [Category.assoc]
      · rw [Category.assoc, hef]
        exact hw.2
    rw [← hwc, Category.assoc, hed, Category.comp_id]

/-- **Stacks 0614, the equivalence of (1) and (2).**  A morphism `f : X ⟶ Y` of algebraic spaces
over `S` admitting a universal first order thickening `X ⊂ X'` over `Y` is formally étale exactly
when that thickening is trivial, that is when the smaller space is the whole of `X'`.

The formal unramifiedness of `f` which clause (2) of the source states alongside the triviality
of the thickening is part of the datum of Stacks 0607 and so does not appear; see the
implementation notes. -/
@[stacks 0614 "the equivalence of (1) and (2)"]
theorem formallyEtale_iff_sub_eq_top (t : UniversalFirstOrderThickening B S hS f) :
    FormallyEtale f.hom ↔ t.sub = ⊤ :=
  ⟨sub_eq_top_of_formallyEtale t, formallyEtale_of_sub_eq_top t⟩

/-! ### The vanishing of the conormal sheaf -/

/-- The inverse image of modules along a morphism of algebraic spaces preserves zero objects,
being a left adjoint. -/
private theorem isZero_modulePullback_obj {A A' : AlgebraicSpaces B S hS} (g : A ⟶ A')
    {M : Modules.{u, u} B S hS A'.1 A'.2} (h : IsZero M) :
    IsZero ((modulePullback B S hS g).obj M) :=
  have := (modulePullbackAdjunction B S hS g).isLeftAdjoint
  Functor.map_isZero _ h

/-- **Stacks 0614, (2) implies (3).**  If the smaller space of a universal first order
thickening of `X` over `Y` is the whole ambient space, then the conormal sheaf `𝒞_{X/Y}` of
Stacks 0607 vanishes.

The inclusion of the smaller space is then invertible, so it is retracted by its inverse and the
defining ideal of the smaller space vanishes on every étale chart.  The conormal sheaf is an
inverse image of that ideal sheaf along two morphisms of algebraic spaces, and an inverse image
of modules preserves zero objects, being a left adjoint. -/
@[stacks 0614 "(2) implies (3)"]
theorem isZero_conormalSheaf_of_sub_eq_top (t : UniversalFirstOrderThickening B S hS f)
    (hsub : t.sub = ⊤) : IsZero (conormalSheaf B S hS t) := by
  have hι : IsIso t.sub.ι := by rw [hsub]; infer_instance
  have hbot := definingIdealAt_eq_bot_of_retraction B S hS t.ambient t.closedSub
    (ObjectProperty.homMk (inv t.sub.ι)) (ObjectProperty.hom_ext _ (IsIso.inv_hom_id _))
  have hzero : IsZero (definingIdealSheaf B S hS t.ambient t.closedSub).toSheafOfModules := by
    refine (IsZero.iff_id_eq_zero _).mpr ?_
    ext W z
    have hz : z = 0 := Subtype.ext ((Submodule.eq_bot_iff _).1 (hbot W) _ z.2)
    rw [hz]
    simp
  rw [conormalSheaf_eq, conormalModule_eq]
  exact isZero_modulePullback_obj _ (isZero_modulePullback_obj _ hzero)

/-- The conormal module of the thickening `X ⊂ X'` vanishes as soon as the conormal sheaf
`𝒞_{X/Y}` of Stacks 0607 does.  The two differ by the inverse image along the identification of
`X` with the smaller space, and that identification is an isomorphism, so the inverse image
along its inverse carries the one to the other: the two inverse images compose to the inverse
image along an identity, which is the identity functor by the unit law of Stacks 03LU. -/
private theorem isZero_conormalModule_of_isZero_conormalSheaf
    (t : UniversalFirstOrderThickening B S hS f) (h : IsZero (conormalSheaf B S hS t)) :
    IsZero (conormalModule B S hS t.ambient t.closedSub) := by
  have hinv : (ObjectProperty.homMk t.sourceIso.inv : t.subSpace ⟶ X) ≫ t.sourceInclusion =
      𝟙 t.subSpace := ObjectProperty.hom_ext _ t.sourceIso.inv_hom_id
  rw [conormalSheaf_eq] at h
  have h₁ := isZero_modulePullback_obj (ObjectProperty.homMk t.sourceIso.inv : t.subSpace ⟶ X) h
  have h₂ : IsZero ((modulePullback B S hS
      ((ObjectProperty.homMk t.sourceIso.inv : t.subSpace ⟶ X) ≫ t.sourceInclusion)).obj
        (conormalModule B S hS t.ambient t.closedSub)) :=
    IsZero.of_iso h₁ ((modulePullbackCompIso B S hS
      (ObjectProperty.homMk t.sourceIso.inv : t.subSpace ⟶ X) t.sourceInclusion).app _).symm
  rw [hinv] at h₂
  exact IsZero.of_iso h₂ ((modulePullbackIdIso B S hS t.subSpace).app _).symm

/-- **Stacks 0614, (3) implies (2).**  If the conormal sheaf `𝒞_{X/Y}` of Stacks 0607 vanishes
then the smaller space of the universal first order thickening is the whole ambient space.

This is where Stacks 04CN, part (3) is spent, in the only form the argument needs: for a
*first-order* thickening the unit `𝓘 ⟶ i_*i^*𝓘` of `i^* ⊣ i_*` is an isomorphism — the
identification `𝓘/𝓘² = 𝓘` of the source, which
`AlgebraicGeometry.Space.firstOrderConormalModuleIso` supplies from the essential-image clause
of Stacks 04CJ — so the vanishing of the conormal module forces the defining ideal of `X` in
`X'` to vanish on every étale chart.  The injectivity clause of Stacks 03MB
(`AlgebraicGeometry.Space.le_of_definingIdealSheaf_le`) then returns `t.sub = ⊤`.

It is the converse of `AlgebraicGeometry.Space.isZero_conormalSheaf_of_sub_eq_top`, and the two
are the content of the equivalence of clauses (2) and (3) of Stacks 0614.  Composed with
`AlgebraicGeometry.Space.formallyEtale_iff_sub_eq_top` it derives clause (1) from clause (3) as
well, which is what closes the equivalence of (3) with the other clauses.  The formal
unramifiedness that clause (3) states alongside the vanishing of the conormal sheaf is part of
the datum of Stacks 0607 and so does not appear; see the implementation notes. -/
@[stacks 0614 "(3) implies (2)"]
theorem sub_eq_top_of_isZero_conormalSheaf (t : UniversalFirstOrderThickening B S hS f)
    (h : IsZero (conormalSheaf B S hS t)) : t.sub = ⊤ := by
  have hC := isZero_conormalModule_of_isZero_conormalSheaf t h
  have : (modulePushforward B S hS
      (subspaceInclusion B S hS t.ambient t.closedSub)).Additive :=
    modulePushforward_additive B S hS _
  have hpush := Functor.map_isZero
    (modulePushforward B S hS (subspaceInclusion B S hS t.ambient t.closedSub)) hC
  rw [modulePushforward_conormalModule_eq] at hpush
  have hI : IsZero
      (definingIdealSheaf B S hS t.ambient t.closedSub).toSheafOfModules :=
    IsZero.of_iso hpush
      (firstOrderConormalModuleIso B S hS t.closedSub t.isUniversal.firstOrder)
  have hbot : ∀ W, definingIdealAt B S hS t.ambient t.closedSub W = ⊥ := by
    intro W
    have hs : Subsingleton
        ((definingIdealSheaf B S hS t.ambient t.closedSub).obj W) :=
      AddCommGrpCat.subsingleton_of_isZero
        (Functor.map_isZero ((evaluation _ _).obj W)
          (Functor.map_isZero (PresheafOfModules.toPresheaf.{u} _)
            (Functor.map_isZero (SheafOfModules.forget _) hI)))
    refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
    have hz : (⟨x, hx⟩ : ((definingIdealSheaf B S hS t.ambient t.closedSub).obj W)) = 0 :=
      hs.elim _ _
    exact congrArg Subtype.val hz
  refine le_antisymm le_top (le_of_definingIdealSheaf_le B S hS t.ambient
    ⟨⊤, isClosedSubspace_top B S hS t.ambient⟩ t.closedSub fun W => ?_)
  rw [definingIdealSheaf_obj, hbot W]
  exact bot_le

/-- Formal étaleness from the vanishing of the conormal sheaf of a universal first order
thickening: the thickening is then trivial. -/
private theorem formallyEtale_of_isZero_conormalSheaf (t : UniversalFirstOrderThickening B S hS f)
    (h : IsZero (conormalSheaf B S hS t)) : FormallyEtale f.hom :=
  (formallyEtale_iff_sub_eq_top t).mpr (sub_eq_top_of_isZero_conormalSheaf t h)

/-! ### The formal unramifiedness of `f` is carried by the universal property -/

/-- **The formal unramifiedness of `f` is not an independent assumption on the datum of
Stacks 0607: the universal property already forces it.**  If `X ⊂ X'` is a universal first order
thickening over `Y` in the sense of Stacks 0602, with `e` identifying `X` with the smaller space
compatibly with `f`, then `f` is formally unramified — no hypothesis on `f` is used.

The structure morphism `X' ⟶ Y` of the thickening is formally unramified by Stacks 0609,
`AlgebraicGeometry.Space.formallyUnramified_of_isUniversalFirstOrderThickening`; the inclusion
of a subfunctor is a monomorphism and so is formally unramified by
`AlgebraicGeometry.Space.formallyUnramified_of_mono`, as is the isomorphism `e`; and
`AlgebraicGeometry.Space.formallyUnramified_comp` is Stacks 049T.  Since `f` factors as
`X ≅ X_{sub} ⊂ X' ⟶ Y`, it is formally unramified.

This is what makes the `formallyUnramified` field of
`AlgebraicGeometry.Space.UniversalFirstOrderThickening` redundant, and so what lets clause (4)
of Stacks 0614 be proved with no formal unramifiedness among its hypotheses; see
`AlgebraicGeometry.Space.formallyEtale_of_isZero_conormalSheaf_of_isUniversal`. -/
theorem formallyUnramified_of_isUniversal {X' : AlgebraicSpaces B S hS}
    (sub : Subfunctor X'.obj) (toBase : X' ⟶ Y)
    (hU : IsUniversalFirstOrderThickening B S hS sub toBase)
    (e : X.obj ≅ sub.toFunctor) (he : e.hom ≫ sub.ι ≫ toBase.hom = f.hom) :
    FormallyUnramified f.hom := by
  rw [← he]
  exact formallyUnramified_comp _ _ (formallyUnramified_of_mono _)
    (formallyUnramified_comp _ _ (formallyUnramified_of_mono _)
      (AlgebraicGeometry.Space.formallyUnramified_of_isUniversalFirstOrderThickening
        B S hS sub toBase hU))

/-- **The datum of Stacks 0607 assembled from the universal property alone.**  A universal first
order thickening `X ⊂ X'` of `X` over `Y` in the sense of Stacks 0602, together with the
identification of `X` with the smaller space over `Y`, is the datum of Stacks 0607: its
`formallyUnramified` field is supplied by
`AlgebraicGeometry.Space.formallyUnramified_of_isUniversal` rather than assumed.

This is the shape in which clauses (2), (3) and (4) of Stacks 0614 can be stated with no
hypothesis of formal unramifiedness anywhere. -/
def UniversalFirstOrderThickening.ofIsUniversal {X' : AlgebraicSpaces B S hS}
    (sub : Subfunctor X'.obj) (toBase : X' ⟶ Y)
    (hU : IsUniversalFirstOrderThickening B S hS sub toBase)
    (e : X.obj ≅ sub.toFunctor) (he : e.hom ≫ sub.ι ≫ toBase.hom = f.hom) :
    UniversalFirstOrderThickening B S hS f where
  formallyUnramified := formallyUnramified_of_isUniversal sub toBase hU e he
  ambient := X'
  toBase := toBase
  sub := sub
  isUniversal := hU
  sourceIso := e
  sourceIso_ι_toBase := he

/-- **The first conjunct of clause (4) of Stacks 0614 is implied by the datum of Stacks 0607.**
The sheaf of differentials `Ω_{X/Y}` of Stacks 04CT vanishes as soon as `f : X ⟶ Y` admits a
universal first order thickening over `Y`.

The datum forces `f` to be formally unramified by
`AlgebraicGeometry.Space.formallyUnramified_of_isUniversal`, and a formally unramified morphism
has a vanishing sheaf of differentials by the forward direction of Stacks 04G9,
`AlgebraicGeometry.Space.isZero_sheafOfDifferentials_of_formallyUnramified`, which carries no
assumed input.

This is why the `Ω_{X/Y} = 0` conjunct of clause (4) does no work in
`AlgebraicGeometry.Space.formallyEtale_of_isZero_conormalSheaf_of_isUniversal`: it is not that
the proof declines to use it, but that it holds automatically once clause (4) is statable at
all. -/
theorem isZero_sheafOfDifferentials_of_isUniversal {X' : AlgebraicSpaces B S hS}
    (sub : Subfunctor X'.obj) (toBase : X' ⟶ Y)
    (hU : IsUniversalFirstOrderThickening B S hS sub toBase)
    (e : X.obj ≅ sub.toFunctor) (he : e.hom ≫ sub.ι ≫ toBase.hom = f.hom) :
    IsZero (sheafOfDifferentials B S hS f) :=
  isZero_sheafOfDifferentials_of_formallyUnramified B S hS f
    (formallyUnramified_of_isUniversal sub toBase hU e he)

/-! ### Clause (4) -/

/-- **Stacks 0614, (4) implies (1), with no formal unramifiedness among the hypotheses.**  Let
`X ⊂ X'` be a universal first order thickening of `X` over `Y` in the sense of Stacks 0602, with
`e` identifying `X` with the smaller space compatibly with `f`.  If the sheaf of differentials
`Ω_{X/Y}` of Stacks 04CT and the conormal sheaf `𝒞_{X/Y}` of Stacks 0607 both vanish, then
`f : X ⟶ Y` is formally étale.

**Where the source derives formal unramifiedness, so does this.**  The source reads clause (4)
through Stacks 04G9: `Ω_{X/Y} = 0` makes `f` formally unramified, which by Stacks 0606 gives the
universal first order thickening and hence makes `𝒞_{X/Y}` mean anything at all.  Here the
thickening is a parameter — `𝒞_{X/Y}` is not nameable without one — and the formal
unramifiedness the source derives is derived here too, from the universal property, by
`AlgebraicGeometry.Space.formallyUnramified_of_isUniversal`.  So no hypothesis of this statement
asserts that `f` is formally unramified, and none of its hypotheses is the conclusion of a
clause of the tag.  `AlgebraicGeometry.Space.formallyEtale_tfae_unconditional` is the form in
which the thickening is quantified away rather than passed in, using Stacks 0606.

The `Ω_{X/Y} = 0` conjunct is not consumed, and provably cannot be: it follows from the
thickening alone, by
`AlgebraicGeometry.Space.isZero_sheafOfDifferentials_of_isUniversal`.  It is kept in the
statement because it is what the source writes.

It carries no Stacks registration: the tag is registered, with no hypotheses, on
`AlgebraicGeometry.Space.formallyEtale_tfae_unconditional` and
`formallyEtale_iff_isZero_sheafOfDifferentials_and_exists_isZero_conormalSheaf`. -/
theorem formallyEtale_of_isZero_conormalSheaf_of_isUniversal {X' : AlgebraicSpaces B S hS}
    (sub : Subfunctor X'.obj) (toBase : X' ⟶ Y)
    (hU : IsUniversalFirstOrderThickening B S hS sub toBase)
    (e : X.obj ≅ sub.toFunctor) (he : e.hom ≫ sub.ι ≫ toBase.hom = f.hom)
    (h : IsZero (sheafOfDifferentials B S hS f) ∧
      IsZero (conormalSheaf B S hS
        (UniversalFirstOrderThickening.ofIsUniversal sub toBase hU e he))) :
    FormallyEtale f.hom :=
  formallyEtale_of_isZero_conormalSheaf
    (UniversalFirstOrderThickening.ofIsUniversal sub toBase hU e he) h.2

/-- **Stacks 0614, (4) implies (1), for the datum of Stacks 0607.**  If the sheaf of
differentials `Ω_{X/Y}` of Stacks 04CT and the conormal sheaf `𝒞_{X/Y}` of Stacks 0607 both
vanish, then `f : X ⟶ Y` is formally étale.

The `formallyUnramified` field of the datum `t` is **not** an extra hypothesis: it is a
consequence of the universal property that the rest of `t` carries, by
`AlgebraicGeometry.Space.formallyUnramified_of_isUniversal`.  The form of this implication in
which that field never appears is
`AlgebraicGeometry.Space.formallyEtale_of_isZero_conormalSheaf_of_isUniversal`, and this
statement follows from it; it is kept because `t` is the shape every other clause of the tag is
stated in.

The `Ω_{X/Y} = 0` conjunct is again not consumed, for the reason recorded there: the datum
already forces it. -/
@[stacks 0614 "(4) implies (1), for the datum of Stacks 0607"]
theorem formallyEtale_of_isZero_sheafOfDifferentials_of_isZero_conormalSheaf
    (t : UniversalFirstOrderThickening B S hS f)
    (h : IsZero (sheafOfDifferentials B S hS f) ∧ IsZero (conormalSheaf B S hS t)) :
    FormallyEtale f.hom :=
  formallyEtale_of_isZero_conormalSheaf t h.2

/-- **Stacks 0614, (3) implies (4).**  If `f : X ⟶ Y` is formally unramified and the conormal
sheaf `𝒞_{X/Y}` of Stacks 0607 vanishes, then the sheaf of differentials `Ω_{X/Y}` of
Stacks 04CT vanishes too and so does `𝒞_{X/Y}`.

Since clauses (1), (2) and (3) are mutually equivalent outright — by
`AlgebraicGeometry.Space.formallyEtale_iff_sub_eq_top`,
`AlgebraicGeometry.Space.isZero_conormalSheaf_of_sub_eq_top` and
`AlgebraicGeometry.Space.sub_eq_top_of_isZero_conormalSheaf` — this is at the same time the
implication from clause (1) and the implication from clause (2).

The content is the forward direction of Stacks 04G9, which is available with no assumed
input as `AlgebraicGeometry.Space.isZero_sheafOfDifferentials_of_formallyUnramified`; the second
conjunct is carried through unchanged. -/
@[stacks 0614 "(3) implies (4), hence also (1) implies (4) and (2) implies (4) through the
  proved equivalence of (1), (2) and (3)"]
theorem isZero_sheafOfDifferentials_and_isZero_conormalSheaf_of_formallyUnramified
    (t : UniversalFirstOrderThickening B S hS f)
    (h : FormallyUnramified f.hom ∧ IsZero (conormalSheaf B S hS t)) :
    IsZero (sheafOfDifferentials B S hS f) ∧ IsZero (conormalSheaf B S hS t) :=
  ⟨isZero_sheafOfDifferentials_of_formallyUnramified B S hS f h.1, h.2⟩

/-! ### The four conditions -/

/-- **Stacks 0614.**  Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` admitting a
universal first order thickening `X ⊂ X'` over `Y` in the sense of Stacks 0607.  Then the four
conditions

1. `f` is formally étale,
2. `f` is formally unramified and `X' = X`,
3. `f` is formally unramified and `𝒞_{X/Y} = 0`,
4. `Ω_{X/Y} = 0` and `𝒞_{X/Y} = 0`

are equivalent.

No hypothesis is carried beyond the datum `t` of Stacks 0607.  Clauses (1), (2) and (3) are
equivalent by `AlgebraicGeometry.Space.formallyEtale_iff_sub_eq_top`,
`AlgebraicGeometry.Space.isZero_conormalSheaf_of_sub_eq_top` and
`AlgebraicGeometry.Space.sub_eq_top_of_isZero_conormalSheaf`; they imply clause (4) by
`isZero_sheafOfDifferentials_and_isZero_conormalSheaf_of_formallyUnramified`,
the forward direction of Stacks 04G9; and clause (4) implies them by
`AlgebraicGeometry.Space.formallyEtale_of_isZero_sheafOfDifferentials_of_isZero_conormalSheaf`.

Its `4 → 3` step reads the formal unramifiedness of `f` off the datum `t`.  That is not a
strengthening of the source's clause (4): the field is a consequence of the universal property
the rest of `t` carries, by `AlgebraicGeometry.Space.formallyUnramified_of_isUniversal`.  The
form in which the field never appears is
`AlgebraicGeometry.Space.formallyEtale_tfae_of_isUniversal`, and that is the one the whole-tag
registration sits on. -/
theorem formallyEtale_tfae (t : UniversalFirstOrderThickening B S hS f) :
    List.TFAE
      [FormallyEtale f.hom, FormallyUnramified f.hom ∧ t.sub = ⊤,
        FormallyUnramified f.hom ∧ IsZero (conormalSheaf B S hS t),
        IsZero (sheafOfDifferentials B S hS f) ∧ IsZero (conormalSheaf B S hS t)] := by
  tfae_have 1 ↔ 2 := by
    rw [formallyEtale_iff_sub_eq_top t]
    exact ⟨fun h => ⟨t.formallyUnramified, h⟩, fun h => h.2⟩
  tfae_have 2 → 3 := fun h => ⟨h.1, isZero_conormalSheaf_of_sub_eq_top t h.2⟩
  tfae_have 3 → 2 := fun h => ⟨h.1, sub_eq_top_of_isZero_conormalSheaf t h.2⟩
  tfae_have 3 → 4 := fun h =>
    isZero_sheafOfDifferentials_and_isZero_conormalSheaf_of_formallyUnramified t h
  tfae_have 4 → 3 := fun h => ⟨t.formallyUnramified, h.2⟩
  tfae_finish

/-- **Stacks 0614.**  Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` and let
`X ⊂ X'` be a universal first order thickening of `X` over `Y` in the sense of Stacks 0602, with
`e` identifying `X` with the smaller space compatibly with `f`.  Then the four conditions

1. `f` is formally étale,
2. `f` is formally unramified and `X' = X`,
3. `f` is formally unramified and `𝒞_{X/Y} = 0`,
4. `Ω_{X/Y} = 0` and `𝒞_{X/Y} = 0`

are equivalent.

**No hypothesis of formal unramifiedness is carried.**  The thickening is a parameter because
Stacks 0607 defines `𝒞_{X/Y}` relative to one, so clauses (3) and (4) cannot be written without
it.  Everything the source derives from `Ω_{X/Y} = 0` before the clauses can be compared is
derived here too: `AlgebraicGeometry.Space.formallyUnramified_of_isUniversal` makes `f` formally
unramified from the universal property alone, which is what the source gets from the backward
direction of Stacks 04G9.

The parameter is not needed either.  Stacks 0606 is available as
`AlgebraicGeometry.Space.nonempty_universalFirstOrderThickening`, and
`AlgebraicGeometry.Space.formallyEtale_tfae_unconditional` spends it to state the same four
conditions with the thickening quantified over and no hypotheses at all.

This is `AlgebraicGeometry.Space.formallyEtale_tfae` at the datum
`AlgebraicGeometry.Space.UniversalFirstOrderThickening.ofIsUniversal`, whose
`formallyUnramified` field is that derivation.

It carries no Stacks registration: Stacks 0614 is registered, with no hypotheses, on
`AlgebraicGeometry.Space.formallyEtale_tfae_unconditional`. -/
theorem formallyEtale_tfae_of_isUniversal {X' : AlgebraicSpaces B S hS}
    (sub : Subfunctor X'.obj) (toBase : X' ⟶ Y)
    (hU : IsUniversalFirstOrderThickening B S hS sub toBase)
    (e : X.obj ≅ sub.toFunctor) (he : e.hom ≫ sub.ι ≫ toBase.hom = f.hom) :
    List.TFAE
      [FormallyEtale f.hom, FormallyUnramified f.hom ∧ sub = ⊤,
        FormallyUnramified f.hom ∧ IsZero (conormalSheaf B S hS
          (UniversalFirstOrderThickening.ofIsUniversal sub toBase hU e he)),
        IsZero (sheafOfDifferentials B S hS f) ∧ IsZero (conormalSheaf B S hS
          (UniversalFirstOrderThickening.ofIsUniversal sub toBase hU e he))] :=
  formallyEtale_tfae (UniversalFirstOrderThickening.ofIsUniversal sub toBase hU e he)

/-! ### Stacks 0606 discharged: the tag with no hypotheses -/

/-- A formally étale transformation is formally unramified: Stacks 049S, part (2) is part (3)
with the existence clause added, so the uniqueness of the lift is the uniqueness clause of the
`∃!`. -/
theorem formallyUnramified_of_formallyEtale {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    (ha : FormallyEtale a) : FormallyUnramified a :=
  fun T T' hT hT' i hi x y hxy _z₁ _z₂ h₁ h₂ =>
    (ha T T' hT hT' i hi x y hxy).unique h₁ h₂

/-- **The source's definite article, verified.**  For a formally unramified `f : X ⟶ Y` the
conormal sheaf `𝒞_{X/Y}` of Stacks 0607 vanishes for *some* universal first order thickening of
`X` over `Y` exactly when it vanishes for *every* one.

Both halves are substantial.  Left to right spends Stacks 0606,
`AlgebraicGeometry.Space.nonempty_universalFirstOrderThickening`: there is at least one
thickening, so the universal quantifier is not vacuous.  Right to left spends the equivalence of
clauses (1) and (3): a single thickening with vanishing conormal sheaf makes `f` formally étale,
by `AlgebraicGeometry.Space.formallyEtale_iff_sub_eq_top` and
`AlgebraicGeometry.Space.sub_eq_top_of_isZero_conormalSheaf`, and formal étaleness then trivializes
every other thickening by `AlgebraicGeometry.Space.sub_eq_top_of_formallyEtale`.

This is why the quantifier chosen in a clause of
`AlgebraicGeometry.Space.formallyEtale_tfae_unconditional` is immaterial, and so why
reading the source's `𝒞_{X/Y} = 0` as a statement quantified over thickenings is not a choice
between two different assertions. -/
theorem forall_isZero_conormalSheaf_iff_exists (hf : FormallyUnramified f.hom) :
    (∀ t : UniversalFirstOrderThickening B S hS f, IsZero (conormalSheaf B S hS t)) ↔
      ∃ t : UniversalFirstOrderThickening B S hS f, IsZero (conormalSheaf B S hS t) := by
  refine ⟨fun h => ?_, fun ⟨t, ht⟩ t' => ?_⟩
  · obtain ⟨t⟩ := nonempty_universalFirstOrderThickening B S hS f hf
    exact ⟨t, h t⟩
  · exact isZero_conormalSheaf_of_sub_eq_top t'
      (sub_eq_top_of_formallyEtale t' (formallyEtale_of_isZero_conormalSheaf t ht))

/-- **Stacks 0614, with no hypotheses at all.**  Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`.  Then the four conditions

1. `f` is formally étale,
2. `f` is formally unramified and the universal first order thickening of `X` over `Y` is `X`,
3. `f` is formally unramified and `𝒞_{X/Y} = 0`,
4. `Ω_{X/Y} = 0` and `𝒞_{X/Y} = 0`

are equivalent.  Nothing is assumed about `f`: no universal first order thickening is a
parameter, and no formal unramifiedness is a hypothesis.

**How the thickening leaves the hypotheses.**  Stacks 0607 defines `𝒞_{X/Y}` relative to a
universal first order thickening, so `𝒞_{X/Y} = 0` is a statement quantified over those
thickenings; `AlgebraicGeometry.Space.forall_isZero_conormalSheaf_iff_exists` shows the two
quantifiers agree for a formally unramified `f`, which is the source's definite article.  The
quantifier written in each clause is the one the source's own reading of that clause supplies:
clauses (2) and (3) state formal unramifiedness, from which Stacks 0606 produces the thickening,
so they are read with `∀`; clause (4) does not, and the source's remark that it "only makes
sense because `Ω_{X/Y} = 0` implies that `𝒞_{X/Y}` is defined" is exactly the assertion that a
thickening exists, so it is read with `∃`.

**Where Stacks 0606 is spent.**  In the step from (3) to (4), to produce the thickening whose
conormal sheaf the existential of clause (4) names:
`AlgebraicGeometry.Space.nonempty_universalFirstOrderThickening` of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/UniversalExistence.lean`.  This is what the
earlier statements of this file carried as a parameter.

**The backward direction of Stacks 04G9 is still not used, and is not needed.**  The source gets
formal unramifiedness out of clause (4) through it.  Here clause (4) carries a thickening in its
existential instead, and a thickening forces formal unramifiedness by
`AlgebraicGeometry.Space.formallyUnramified_of_isUniversal` — which is also why the step from (4)
to (1) needs nothing beyond the equivalence of (1) and (3). -/
@[stacks 0614 "the equivalence of the four conditions, with no hypotheses: Stacks 0606 supplies
  the universal first order thickening"]
theorem formallyEtale_tfae_unconditional :
    List.TFAE
      [FormallyEtale f.hom,
        FormallyUnramified f.hom ∧
          ∀ t : UniversalFirstOrderThickening B S hS f, t.sub = ⊤,
        FormallyUnramified f.hom ∧
          ∀ t : UniversalFirstOrderThickening B S hS f, IsZero (conormalSheaf B S hS t),
        IsZero (sheafOfDifferentials B S hS f) ∧
          ∃ t : UniversalFirstOrderThickening B S hS f, IsZero (conormalSheaf B S hS t)] := by
  tfae_have 1 → 2 := fun h =>
    ⟨formallyUnramified_of_formallyEtale h, fun t => sub_eq_top_of_formallyEtale t h⟩
  tfae_have 2 → 3 := fun h =>
    ⟨h.1, fun t => isZero_conormalSheaf_of_sub_eq_top t (h.2 t)⟩
  tfae_have 3 → 4 := fun h =>
    ⟨isZero_sheafOfDifferentials_of_formallyUnramified B S hS f h.1,
      (forall_isZero_conormalSheaf_iff_exists h.1).mp h.2⟩
  tfae_have 4 → 1 := fun h => by
    obtain ⟨t, ht⟩ := h.2
    exact formallyEtale_of_isZero_conormalSheaf t ht
  tfae_finish

/-- **Stacks 0614, the equivalence of (1) and (4), with no hypotheses.**  A morphism
`f : X ⟶ Y` of algebraic spaces over `S` is formally étale exactly when the sheaf of
differentials `Ω_{X/Y}` of Stacks 04CT vanishes and `X` admits a universal first order thickening
over `Y` whose conormal sheaf `𝒞_{X/Y}` of Stacks 0607 vanishes.

The existential is the source's reading of clause (4), whose remark on that clause is that
`𝒞_{X/Y}` has to be defined before the clause says anything; see
`AlgebraicGeometry.Space.formallyEtale_tfae_unconditional`, of which this is the
instance at indices 1 and 4. -/
@[stacks 0614 "the equivalence of (1) and (4), with no hypotheses"]
theorem formallyEtale_iff_isZero_sheafOfDifferentials_and_exists_isZero_conormalSheaf :
    FormallyEtale f.hom ↔
      IsZero (sheafOfDifferentials B S hS f) ∧
        ∃ t : UniversalFirstOrderThickening B S hS f, IsZero (conormalSheaf B S hS t) :=
  formallyEtale_tfae_unconditional.out 1 4

end AlgebraicGeometry.Space

end
