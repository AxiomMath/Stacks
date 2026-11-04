module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceThickening
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleIdealSheafRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFiniteReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Comp
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Factor
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FormallyEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Universal
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalFirstOrderThickeningCriteria

/-!
# Étale base change of a universal first-order thickening

Let `Z ⟶ Y ⟶ X` be morphisms of algebraic spaces over a scheme `S` with `Z ⟶ Y` étale, and let
`Y ⊂ Y'` be a universal first-order thickening of `Y` over `X`, with structure morphism
`p : Y' ⟶ X`.  If `g : Z' ⟶ Y'` is étale and `Z ⊂ Z'` is the inverse image of `Y ⊂ Y'`, that is
if the square

```
  Z  --→  Y
  |       |
  ↓       ↓
  Z' --→  Y'
```

is cartesian, then `Z ⊂ Z'` is a universal first-order thickening of `Z` over `X`, with
structure morphism the composite `g ≫ p`.  This is the first part of Stacks 0605.

The descent in the other direction is proved here as well.  If `Z ⟶ Y` is *surjective* étale,
if `g : Z' ⟶ Y'` is an étale morphism of first-order thickenings over `X` extending it, and if
`Z ⊂ Z'` is a universal first-order thickening of `Z` over `X`, then `Y ⊂ Y'` is a universal
first-order thickening of `Y` over `X`.  This is the second part of Stacks 0605.

The file also contains the first of the three assertions of Stacks 060D, the étale localization
of universal first-order thickenings.  For a formally unramified `h : Z ⟶ X` and a commutative
square

```
  V --f--→  U
  |         |
  v         u
  ↓         ↓
  Z --h--→  X
```

with `v` and `u` étale, the localized morphism `f` is again formally unramified.

## Main results

* `AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.etalePullback`: **Stacks 0605,
  part (1)**.
* `AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.of_surjectiveEtale`: **Stacks 0605,
  part (2)**, the descent of universality along a surjective étale morphism of first-order
  thickenings.
* `AlgebraicGeometry.Space.formallyUnramified_of_etaleLocalization`: **Stacks 060D, the first of
  its three assertions**, formal unramifiedness of the étale localization of a formally
  unramified morphism of algebraic spaces.

## Implementation notes

The source states part (1) for *the* étale `Z' ⟶ Y'` with `Z = Y ×_{Y'} Z'`, whose existence and
uniqueness is the topological invariance of the spaces-étale site, Stacks 05ZH.  Topological
invariance is not used here: the statement below is universally quantified over étale morphisms
`g : Z' ⟶ Y'` fitting into a cartesian square over the inclusion of `Y`, so it applies to any
such extension without asserting that one exists.

Being cartesian over the inclusion of `Y` forces `Z` to be the inverse image subfunctor
`Y.preimage g.hom` (`CategoryTheory.Subfunctor.range_eq_preimage_of_isPullback`), and that
inverse image is again a first-order thickening: it is a thickening by Stacks 09ZX, and its
defining ideal at an étale chart `V` of `Z'` is the defining ideal of `Y` at the postcomposed
chart `V ⟶ Z' ⟶ Y'` by
`AlgebraicGeometry.Space.definingIdealAt_preimage_eq_definingIdealAt_postcomp`, where it has
square zero by hypothesis.  Only the étale case of Stacks 09ZX is needed, which is why the
quasi-coherence of Stacks 03MB — unavailable in this library outside affine charts — is not an
input.

The lifting property is the two-step argument of the source.  A solid diagram over `X` built
from a first-order thickening `T ⊂ T'` and a morphism `T ⟶ Z` is pushed forward along `Z ⟶ Y`
to a solid diagram over `X` for the thickening `Y ⊂ Y'`, where universality of `Y'` produces a
unique `T' ⟶ Y'`.  Étaleness of `g` makes it formally étale, by Stacks 0616, so Stacks 0611
lifts that morphism uniquely to the required `T' ⟶ Z'`.  Uniqueness is the same two steps run
backwards: a competing extension `T' ⟶ Z'` composes with `g` to a lift of the pushed-forward
diagram, which universality of `Y'` identifies with the chosen one, and then Stacks 0611
identifies the two extensions themselves.

**Part (2).** The source produces the étale extension of the test thickening from the
topological invariance of the spaces-étale site, Stacks 05ZH; the route taken here avoids it.
Avoiding it is not a necessity: Stacks 05ZH is formalized at a first-order thickening, which
is the case at issue here, by
`AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isFirstOrderThickening` and
`AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isFirstOrderThickening` of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/SpacesEtaleEssSurj.lean`, and the extension
itself is assembled from it, unconditionally, by
`Stacks.Spaces.UniversalThickening.etaleExtendsAlongFirstOrderThickening`.  The route below is
kept because it is proved and because it produces a *representable* extension, which Stacks 05ZH
on the spaces-étale site does not.  By Stacks 0603
(`AlgebraicGeometry.Space.isUniversalFirstOrderThickening_iff_affine_lifting`) the ambient test
object `T'` may be taken to be an affine scheme, and then `T ⊂ T'` is a thickening of affine
schemes by `AlgebraicGeometry.Space.exists_nthOrderThickening_chart_pullback`.  The fibre
product `T ×_Y Z` is étale and surjective over `T`; a scheme chart of it is refined by the
finitely many affine opens whose images already cover the quasi-compact `T`, which produces a
surjective étale `W ⟶ T` with `W` an affine object of the site.  Stacks 039R
(`Stacks.Etale.exists_etale_pullback_iso_of_isClosedImmersion_of_surjective`) extends `W` to an
étale `W' ⟶ T'` with `W = T ×_{T'} W'`, and `W'` is quasi-compact and of finite type over the
affine `T'`, hence an object of the site by Stacks 000R, part (5).

Universality of `Z'` lifts `W ⟶ Z` to a morphism `c' : W' ⟶ Z'`, and `c' ≫ g` descends along
the surjective étale `W' ⟶ T'`, which presents `T'` as the coequalizer of its kernel pair in
fppf sheaves by Stacks 0262.  The cocycle condition is part (1) applied to the étale projection
`Z' ×_{Y'} Z' ⟶ Z'`: the inverse image of `Z` there is a universal first-order thickening over
`X`, so the two restrictions of `c'` to `W' ×_{T'} W'` are the two projections of one lift into
`Z' ×_{Y'} Z'`, by the uniqueness of lifts into `Z'`.  Uniqueness of the descended arrow needs
no cocycle: a competing arrow lifts uniquely through the formally étale `g` by Stacks 0611, and
universality of `Z'` identifies the two lifts.

The second and third assertions of Stacks 060D are not proved in *this* module, and nothing here
carries those parts of the tag; they are proved in
`StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningEtaleLocalization`, which carries them.
They assert that the universal first-order thickening `V ⊂ V'` of `V` over `U` is étale over
`Z'`, and that consequently `𝒞_{Z/X}|_V = 𝒞_{V/U}`.  The route taken there does not use
Stacks 05ZH either: instead of producing an étale `V'' ⟶ Z'` by
the essential surjectivity of Stacks 05ZH and identifying `V'` with it, the étale extension is
hypothesised where the source produces it — the same shape the `@[stacks 0605 "part (1)"]` statement
already takes here — and étaleness over `Z'` is then *concluded* for every universal first-order
thickening of `V` over `U` by transporting along the canonical Stacks 060A morphisms, which are
mutually inverse.  The conormal clause is Stacks 04CO for the étale morphism `V' ⟶ Z'`,
`AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso`, transported along the cartesian
square.  Only the first assertion of Stacks 060D, formal unramifiedness of `f`, is proved here.

## References

* [Stacks Project, Tag 0605](https://stacks.math.columbia.edu/tag/0605)
* [Stacks Project, Tag 0602](https://stacks.math.columbia.edu/tag/0602)
* [Stacks Project, Tag 0603](https://stacks.math.columbia.edu/tag/0603)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 039R](https://stacks.math.columbia.edu/tag/039R)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 0611](https://stacks.math.columbia.edu/tag/0611)
* [Stacks Project, Tag 0616](https://stacks.math.columbia.edu/tag/0616)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
* [Stacks Project, Tag 060D](https://stacks.math.columbia.edu/tag/060D)
* [Stacks Project, Tag 049T](https://stacks.math.columbia.edu/tag/049T)
* [Stacks Project, Tag 04G5](https://stacks.math.columbia.edu/tag/04G5)
* [Stacks Project, Tag 04G8](https://stacks.math.columbia.edu/tag/04G8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An étale morphism of algebraic spaces is formally étale, by Stacks 0616. -/
private theorem formallyEtale_of_isEtale' {A C : AlgebraicSpaces B S hS} (f : A ⟶ C)
    (hf : IsEtale B S hS f.hom) : FormallyEtale f.hom :=
  ((isEtale_iff_isLocallyOfFinitePresentation_and_formallyEtale B S hS
    A.property C.property f.hom).mp hf).2

/-- **Stacks 0605, part (1).** Let `Y ⊂ Y'` be a universal first-order thickening of `Y` over an
algebraic space `X`, with structure morphism `p : Y' ⟶ X`.  Let `g : Z' ⟶ Y'` be étale and let
`Z ⊂ Z'` be a closed subspace whose inclusion sits in a cartesian square over the inclusion of
`Y`, so that `Z = Y ×_{Y'} Z'`.  Then `Z ⊂ Z'` is a universal first-order thickening of `Z` over
`X`, with structure morphism `g ≫ p`.

The morphism `Z ⟶ Y` of the source appears as the top edge `a` of the cartesian square; it is
automatically étale, being a base change of `g`.  The source produces `Z' ⟶ Y'` from the
topological invariance of the spaces-étale site; here it is given, so no such input is needed. -/
@[stacks 0605 "part (1)"]
theorem IsUniversalFirstOrderThickening.etalePullback {X Y' Z' : AlgebraicSpaces B S hS}
    (Y : Subfunctor Y'.obj) (p : Y' ⟶ X)
    (hY : IsUniversalFirstOrderThickening B S hS Y p)
    (g : Z' ⟶ Y') (hg : IsEtale B S hS g.hom)
    (Z : Subfunctor Z'.obj) (a : Z.toFunctor ⟶ Y.toFunctor)
    (hsq : IsPullback a Z.ι Y.ι g.hom) :
    IsUniversalFirstOrderThickening B S hS Z (g ≫ p) := by
  -- The cartesian square identifies `Z` with the inverse image of `Y`, which is a first-order
  -- thickening because `g` is étale.
  have hZeq : Z = Y.preimage g.hom := by
    have h := Subfunctor.range_eq_preimage_of_isPullback hsq.flip
    rwa [Subfunctor.range_ι, Subfunctor.range_ι] at h
  have hZfirst : IsFirstOrderThickening B S hS Z' Z := by
    rw [hZeq]
    exact isNthOrderThickening_preimage_of_isEtale B S hS Y g hg hY.firstOrder
  have hgFE := formallyEtale_of_isEtale' B S hS g hg
  have hcomp : (g ≫ p).hom = g.hom ≫ p.hom := rfl
  refine ⟨hZfirst, ?_⟩
  intro T' T hT aT b hcompat
  rw [hcomp] at hcompat ⊢
  -- Push the solid diagram forward along `Z ⟶ Y` and lift it by universality of `Y'`.
  have hcompatY : T.ι ≫ b = (aT ≫ a) ≫ Y.ι ≫ p.hom := by
    rw [hcompat]
    simp only [Category.assoc, reassoc_of% hsq.w]
  obtain ⟨d, hd, hdu⟩ := hY.existsUnique_lift T hT (aT ≫ a) b hcompatY
  -- The lift turns the diagram into a solid square for the formally étale `g`.
  have hsolid : (aT ≫ Z.ι) ≫ g.hom = T.ι ≫ d := by
    rw [hd.1]
    simp only [Category.assoc, hsq.w]
  obtain ⟨c, hc, hcu⟩ := FormallyEtale.existsUnique_lift_of_firstOrderThickening B S hS g hgFE
    T hT (aT ≫ Z.ι) d hsolid
  refine ⟨c, ⟨hc.1, ?_⟩, fun c' hc' ↦ ?_⟩
  · rw [← Category.assoc, hc.2, hd.2]
  · refine hcu c' ⟨hc'.1, hdu (c' ≫ g.hom) ⟨?_, ?_⟩⟩
    · rw [← Category.assoc, hc'.1, hsolid, hd.1]
    · rw [Category.assoc]
      exact hc'.2

/-! ### Stacks 0605, part (2) -/

/-- An isomorphism of schemes is surjective on points. -/
private theorem isoSurjective {A C : Scheme.{u}} (e : A ≅ C) :
    Function.Surjective e.hom.base := fun y => ⟨e.inv.base y, by simp⟩

/-- A scheme receiving a surjective morphism from a quasi-compact scheme is quasi-compact. -/
private theorem compactSpace_of_surjective_hom {A C : Scheme.{u}} (f : A ⟶ C)
    (hf : Function.Surjective f.base) (_h : CompactSpace ↥A) : CompactSpace ↥C := by
  have _ := _h
  rw [← isCompact_univ_iff, ← Set.range_eq_univ.2 hf]
  exact isCompact_range f.continuous

section Part2

variable {X Y' Z' : AlgebraicSpaces B S hS} {Y : Subfunctor Y'.obj} {Z : Subfunctor Z'.obj}
  {p : Y' ⟶ X} {g : Z' ⟶ Y'} {a₀ : Z.toFunctor ⟶ Y.toFunctor}

/-- **The chart-level lift is compatible with the kernel pair of the chart.** Let `c'` be the
lift into `Z'` over an étale chart `w : V ⟶ T'` of a test thickening, and let `s, t : R ⇉ V`
be the kernel pair of `w`.  Then the two restrictions of `c'` agree after `Z' ⟶ Y'`: both are
projections of one and the same lift into `Z' ×_{Y'} Z'`, which is a universal first-order
thickening of `Z ×_{Y'} Z'` over `X` by part (1). -/
private theorem comp_eq_comp_of_chart
    (hcompat : a₀ ≫ Y.ι = Z.ι ≫ g.hom)
    (hZ : IsUniversalFirstOrderThickening B S hS Z (g ≫ p))
    (hq₁ : IsEtale B S hS (pullback.fst g.hom g.hom))
    {T' : AlgebraicSpaces B S hS} (T : Subfunctor T'.obj)
    (hT : IsFirstOrderThickening B S hS T' T)
    (a : T.toFunctor ⟶ Y.toFunctor) (b : T'.obj ⟶ X.obj)
    {V R : BigFppfOver B S hS} (w : yoneda.obj V ⟶ T'.obj)
    (hwE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) w)
    (s t : R ⟶ V) (hpb : IsPullback (yoneda.map s) (yoneda.map t) w w)
    (hsE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (yoneda.map s))
    (cW : (T.preimage w).toFunctor ⟶ Z.toFunctor)
    (hcW : cW ≫ a₀ = T.fromPreimage w ≫ a)
    {c' : yoneda.obj V ⟶ Z'.obj}
    (hc₁ : (T.preimage w).ι ≫ c' = cW ≫ Z.ι)
    (hc₂ : c' ≫ (g ≫ p).hom = w ≫ b) :
    (yoneda.map s ≫ c') ≫ g.hom = (yoneda.map t ≫ c') ≫ g.hom := by
  classical
  have hmul := (isMultiplicative_presheaf_etale B S hS).toIsStableUnderComposition
  obtain ⟨u, hus, hut⟩ : ∃ u : yoneda.obj R ⟶ T'.obj,
      yoneda.map s ≫ w = u ∧ yoneda.map t ≫ w = u :=
    ⟨yoneda.map s ≫ w, rfl, hpb.w.symm⟩
  have huE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) u := by
    rw [← hus]
    exact MorphismProperty.comp_mem _ _ _ hsE hwE
  let Nsp : AlgebraicSpaces B S hS := ⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩
  have hN : IsFirstOrderThickening B S hS Nsp (T.preimage u) :=
    isFirstOrderThickening_preimage_of_isEtale B S hS T (ObjectProperty.homMk u : Nsp ⟶ T')
      (isEtale_of_presheaf_etale B S hS huE) hT
  -- the comparison maps between the restrictions of `T` to `R` and to `V`, along `s` and `t`,
  -- and the restricted lifting problems solved by the two restrictions of the chart-level lift
  have restr : ∀ v : R ⟶ V, yoneda.map v ≫ w = u →
      ∃ q : (T.preimage u).toFunctor ⟶ (T.preimage w).toFunctor,
        q ≫ T.fromPreimage w = T.fromPreimage u ∧
        (T.preimage u).ι ≫ (yoneda.map v ≫ c') = (q ≫ cW) ≫ Z.ι ∧
        (yoneda.map v ≫ c') ≫ (g ≫ p).hom = u ≫ b ∧
        (T.preimage u).ι ≫ (u ≫ b) = (q ≫ cW) ≫ Z.ι ≫ (g ≫ p).hom := by
    intro v hvw
    have hpre : T.preimage u = (T.preimage w).preimage (yoneda.map v) := by
      rw [← hvw, Subfunctor.preimage_comp]
    obtain ⟨q, hq⟩ : ∃ q : (T.preimage u).toFunctor ⟶ (T.preimage w).toFunctor,
        q ≫ (T.preimage w).ι = (T.preimage u).ι ≫ yoneda.map v :=
      ⟨Subfunctor.lift ((T.preimage u).ι ≫ yoneda.map v) (by
        rw [Subfunctor.range_comp, Subfunctor.range_ι, Subfunctor.image_le_iff, ← hpre]), rfl⟩
    have hd₁ : (T.preimage u).ι ≫ (yoneda.map v ≫ c') = (q ≫ cW) ≫ Z.ι := by
      rw [← reassoc_of% hq, hc₁, Category.assoc]
    have hd₂ : (yoneda.map v ≫ c') ≫ (g ≫ p).hom = u ≫ b := by
      rw [Category.assoc, hc₂, ← Category.assoc, hvw]
    exact ⟨q, (cancel_mono T.ι).1 (by
        simp only [Category.assoc, Subfunctor.fromPreimage_ι, reassoc_of% hq, hvw]), hd₁, hd₂, by
      simp only [← hd₂, reassoc_of% hd₁, Category.assoc]⟩
  obtain ⟨qS, hqSa, hdS₁, hdS₂, hcompS⟩ := restr s hus
  obtain ⟨qT, hqTa, hdT₁, hdT₂, hcompT⟩ := restr t hut
  -- the fibre product `Z' ×_{Y'} Z'`, universal over `X` by part (1)
  let P' : AlgebraicSpaces B S hS := AlgebraicSpaces.fiberProduct B S hS g g
  let pr₁ : P' ⟶ Z' := ObjectProperty.homMk (pullback.fst g.hom g.hom)
  let pr₂ : P' ⟶ Z' := ObjectProperty.homMk (pullback.snd g.hom g.hom)
  let P : Subfunctor P'.obj := Z.preimage pr₁.hom
  have hPpb : IsPullback (Z.fromPreimage pr₁.hom) P.ι Z.ι pr₁.hom :=
    Subfunctor.isPullback_preimage pr₁.hom Z
  have hPuniv : IsUniversalFirstOrderThickening B S hS P (pr₁ ≫ (g ≫ p)) :=
    IsUniversalFirstOrderThickening.etalePullback B S hS Z (g ≫ p) hZ pr₁ hq₁ P
      (Z.fromPreimage pr₁.hom) hPpb
  -- the pair of restrictions, as a morphism to the fibre product
  have hpair : ((qS ≫ cW) ≫ Z.ι) ≫ g.hom = ((qT ≫ cW) ≫ Z.ι) ≫ g.hom := by
    simp only [Category.assoc, ← hcompat, reassoc_of% hcW, reassoc_of% hqSa,
      reassoc_of% hqTa]
  let ρ₀ : (T.preimage u).toFunctor ⟶ P'.obj :=
    pullback.lift ((qS ≫ cW) ≫ Z.ι) ((qT ≫ cW) ≫ Z.ι) hpair
  have hρ₀₁ : ρ₀ ≫ pr₁.hom = (qS ≫ cW) ≫ Z.ι := pullback.lift_fst _ _ _
  have hρ₀₂ : ρ₀ ≫ pr₂.hom = (qT ≫ cW) ≫ Z.ι := pullback.lift_snd _ _ _
  let ρ : (T.preimage u).toFunctor ⟶ P.toFunctor := hPpb.lift (qS ≫ cW) ρ₀ hρ₀₁.symm
  have hρι : ρ ≫ P.ι = ρ₀ := hPpb.lift_snd _ _ _
  have hcond : pr₁.hom ≫ g.hom = pr₂.hom ≫ g.hom := pullback.condition
  -- the lift into the fibre product, and its two projections
  have hcompatP : (T.preimage u).ι ≫ (u ≫ b) = ρ ≫ P.ι ≫ (pr₁ ≫ (g ≫ p)).hom := by
    calc (T.preimage u).ι ≫ (u ≫ b)
        = (qS ≫ cW) ≫ Z.ι ≫ (g ≫ p).hom := hcompS
      _ = ρ ≫ P.ι ≫ pr₁.hom ≫ (g ≫ p).hom := by
        simp only [reassoc_of% hρι, reassoc_of% hρ₀₁, Category.assoc]
  obtain ⟨π, hπ, -⟩ := hPuniv.existsUnique_lift (T' := Nsp) (T.preimage u) hN ρ (u ≫ b) hcompatP
  have huniq : ∀ q : (T.preimage u).toFunctor ⟶ (T.preimage w).toFunctor,
      (T.preimage u).ι ≫ (u ≫ b) = (q ≫ cW) ≫ Z.ι ≫ (g ≫ p).hom →
      ∀ d₁ d₂ : yoneda.obj R ⟶ Z'.obj,
      ((T.preimage u).ι ≫ d₁ = (q ≫ cW) ≫ Z.ι ∧ d₁ ≫ (g ≫ p).hom = u ≫ b) →
      ((T.preimage u).ι ≫ d₂ = (q ≫ cW) ≫ Z.ι ∧ d₂ ≫ (g ≫ p).hom = u ≫ b) → d₁ = d₂ :=
    fun q hq d₁ d₂ h₁ h₂ ↦
      have ⟨_, _, hu⟩ := hZ.existsUnique_lift (T' := Nsp) (T.preimage u) hN (q ≫ cW) (u ≫ b) hq
      (hu _ h₁).trans (hu _ h₂).symm
  have hπι : (T.preimage u).ι ≫ π = ρ₀ := by rw [hπ.1, hρι]
  have hπfst : (T.preimage u).ι ≫ π ≫ pr₁.hom = (qS ≫ cW) ≫ Z.ι := by
    rw [← Category.assoc, hπι, hρ₀₁]
  have hπsnd : (T.preimage u).ι ≫ π ≫ pr₂.hom = (qT ≫ cW) ≫ Z.ι := by
    rw [← Category.assoc, hπι, hρ₀₂]
  have hπX₁ : (π ≫ pr₁.hom) ≫ (g ≫ p).hom = u ≫ b := (Category.assoc _ _ _).trans hπ.2
  have hπX₂ : (π ≫ pr₂.hom) ≫ (g ≫ p).hom = u ≫ b := by
    rw [← hπX₁, show (g ≫ p).hom = g.hom ≫ p.hom from rfl]
    simp only [Category.assoc, reassoc_of% hcond]
  have e₁ : yoneda.map s ≫ c' = π ≫ pr₁.hom :=
    huniq qS hcompS _ _ ⟨hdS₁, hdS₂⟩ ⟨hπfst, hπX₁⟩
  have e₂ : yoneda.map t ≫ c' = π ≫ pr₂.hom :=
    huniq qT hcompT _ _ ⟨hdT₁, hdT₂⟩ ⟨hπsnd, hπX₂⟩
  rw [e₁, e₂, Category.assoc, Category.assoc, hcond]

/-- **The lift over an étale chart of the test object descends.** Let `T ⊂ T'` be a test
first-order thickening over `X` with `a : T ⟶ Y`, and let `w : V ⟶ T'` be a surjective étale
chart by a scheme over which the restriction of `T` maps to `Z` compatibly with `a`.  Then the
diagram of Stacks 0602 for `Y ⊂ Y'` has exactly one dotted arrow. -/
private theorem existsUnique_lift_of_chart
    (hg : IsEtale B S hS g.hom) (hcompat : a₀ ≫ Y.ι = Z.ι ≫ g.hom)
    (hZ : IsUniversalFirstOrderThickening B S hS Z (g ≫ p))
    (hq₁ : IsEtale B S hS (pullback.fst g.hom g.hom))
    {T' : AlgebraicSpaces B S hS} (T : Subfunctor T'.obj)
    (hT : IsFirstOrderThickening B S hS T' T)
    (a : T.toFunctor ⟶ Y.toFunctor) (b : T'.obj ⟶ X.obj)
    (hcomm : T.ι ≫ b = a ≫ Y.ι ≫ p.hom)
    {V : BigFppfOver B S hS} (w : yoneda.obj V ⟶ T'.obj)
    (hwS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) w)
    (hwE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) w)
    (cW : (T.preimage w).toFunctor ⟶ Z.toFunctor)
    (hcW : cW ≫ a₀ = T.fromPreimage w ≫ a) :
    ∃! c : T'.obj ⟶ Y'.obj, T.ι ≫ c = a ≫ Y.ι ∧ c ≫ p.hom = b := by
  classical
  have hmul := (isMultiplicative_presheaf_etale B S hS).toIsStableUnderComposition
  have hmulS := isStableUnderComposition_presheaf_surjective B S hS
  let Vsp : AlgebraicSpaces B S hS := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
  have hTV : IsFirstOrderThickening B S hS Vsp (T.preimage w) :=
    isFirstOrderThickening_preimage_of_isEtale B S hS T (ObjectProperty.homMk w : Vsp ⟶ T')
      (isEtale_of_presheaf_etale B S hS hwE) hT
  -- the solid diagram restricted along the chart, and the lift into `Z'` it produces
  have hcompV : (T.preimage w).ι ≫ (w ≫ b) = cW ≫ Z.ι ≫ (g ≫ p).hom := by
    rw [show (g ≫ p).hom = g.hom ≫ p.hom from rfl, ← reassoc_of% hcompat, reassoc_of% hcW,
      ← hcomm, Subfunctor.fromPreimage_ι_assoc]
  obtain ⟨c', hc', hc'u⟩ :=
    hZ.existsUnique_lift (T' := Vsp) (T.preimage w) hTV cW (w ≫ b) hcompV
  -- every dotted arrow restricts along the chart to `c' ≫ g`, by Stacks 0611 and uniqueness
  have hgFE := formallyEtale_of_isEtale' B S hS g hg
  have step : ∀ c : T'.obj ⟶ Y'.obj, T.ι ≫ c = a ≫ Y.ι → c ≫ p.hom = b →
      w ≫ c = c' ≫ g.hom := by
    intro c hc₁ hc₂
    have hsq : (cW ≫ Z.ι) ≫ g.hom = (T.preimage w).ι ≫ (w ≫ c) := by
      rw [Category.assoc, ← hcompat, reassoc_of% hcW, ← hc₁, Subfunctor.fromPreimage_ι_assoc]
    obtain ⟨d, hd, -⟩ := FormallyEtale.existsUnique_lift_of_firstOrderThickening B S hS g hgFE
      (T' := Vsp) (T.preimage w) hTV (cW ≫ Z.ι) (w ≫ c) hsq
    have hdZ : d ≫ (g ≫ p).hom = w ≫ b := by
      rw [show (g ≫ p).hom = g.hom ≫ p.hom from rfl, reassoc_of% hd.2, hc₂]
    have hdc : d = c' := hc'u d ⟨hd.1, hdZ⟩
    rw [← hd.2, hdc]
  -- the kernel pair of the chart, and the cocycle condition
  have hrep : yoneda.relativelyRepresentable w := hwE.1
  obtain ⟨R, s, t, hpb, hsE⟩ :
      ∃ (R : BigFppfOver B S hS) (s t : R ⟶ V),
        IsPullback (yoneda.map s) (yoneda.map t) w w ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) (yoneda.map s) :=
    ⟨hrep.pullback w, hrep.snd w, hrep.fst' w, (hrep.isPullback' w).flip,
      (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
        (@Etale.{u} : MorphismProperty Scheme.{u}) (hrep.snd w)).2
        (hwE.2 w (hrep.fst w) (hrep.snd w) (hrep.isPullback w))⟩
  have hcoc := comp_eq_comp_of_chart B S hS hcompat hZ hq₁ T hT a b w hwE s t hpb hsE cW hcW
    hc'.1 hc'.2
  -- descend `c' ≫ g` along the chart
  obtain ⟨hRsh, hVsh, ⟨hcoeq⟩⟩ :=
    isCoequalizer_of_surjectiveEtale B S hS w s t hpb T'.property hwS hwE
  let J := BigFppfOver.topology B S hS
  let VF : Sheaf J (Type u) := ⟨yoneda.obj V, hVsh⟩
  let RF : Sheaf J (Type u) := ⟨yoneda.obj R, hRsh⟩
  let TF : Sheaf J (Type u) := ⟨T'.obj, T'.property.isSheaf⟩
  let YF : Sheaf J (Type u) := ⟨Y'.obj, Y'.property.isSheaf⟩
  let sf : RF ⟶ VF := ObjectProperty.homMk (yoneda.map s)
  let tf : RF ⟶ VF := ObjectProperty.homMk (yoneda.map t)
  let wf : VF ⟶ TF := ObjectProperty.homMk w
  have hww : sf ≫ wf = tf ≫ wf := Sheaf.hom_ext hpb.w
  have hcol : IsColimit (Cofork.ofπ wf hww) := hcoeq
  have hcoc' : yoneda.map s ≫ c' ≫ g.hom = yoneda.map t ≫ c' ≫ g.hom := by
    simpa only [Category.assoc] using hcoc
  have hlw : sf ≫ (ObjectProperty.homMk (c' ≫ g.hom) : VF ⟶ YF) =
      tf ≫ ObjectProperty.homMk (c' ≫ g.hom) := Sheaf.hom_ext hcoc'
  have hfac : w ≫ (hcol.desc (Cofork.ofπ
      (ObjectProperty.homMk (c' ≫ g.hom) : VF ⟶ YF) hlw)).hom = c' ≫ g.hom :=
    congrArg (fun k : VF ⟶ YF ↦ k.hom)
      (hcol.fac (Cofork.ofπ (ObjectProperty.homMk (c' ≫ g.hom) : VF ⟶ YF) hlw)
        WalkingParallelPair.one)
  set cfin := (hcol.desc (Cofork.ofπ
    (ObjectProperty.homMk (c' ≫ g.hom) : VF ⟶ YF) hlw)).hom
  -- the descended arrow restricts to `a` on `T`
  obtain ⟨V₂, e, heSurj, heEtale⟩ := hTV.1.1.1.exists_atlas
  have hqSurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (T.fromPreimage w) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (Subfunctor.isPullback_preimage w T).flip hwS
  have hqEtale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (T.fromPreimage w) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (Subfunctor.isPullback_preimage w T).flip hwE
  have hrestr : T.ι ≫ cfin = a ≫ Y.ι := by
    refine eq_of_comp_eq_of_surjectiveEtale B S hS hT.1.1.1 Y'.property.isSheaf
      (e ≫ T.fromPreimage w) (MorphismProperty.comp_mem _ _ _ heSurj hqSurj)
      (MorphismProperty.comp_mem _ _ _ heEtale hqEtale) ?_
    simp only [Category.assoc, Subfunctor.fromPreimage_ι_assoc, hfac, reassoc_of% hc'.1,
      ← hcompat, reassoc_of% hcW]
  -- the descended arrow lies over `X`
  have hover : cfin ≫ p.hom = b := by
    refine eq_of_comp_eq_of_surjectiveEtale B S hS T'.property X.property.isSheaf w hwS hwE ?_
    rw [reassoc_of% hfac]
    exact hc'.2
  refine ⟨cfin, ⟨hrestr, hover⟩, fun d hd ↦ ?_⟩
  refine eq_of_comp_eq_of_surjectiveEtale B S hS T'.property Y'.property.isSheaf w hwS hwE ?_
  rw [step d hd.1 hd.2, step cfin hrestr hover]

end Part2

/-- **Stacks 060D, the first of its three assertions.** Let `h : Z ⟶ X` be a formally unramified
morphism of algebraic spaces over `S`, and let `f : V ⟶ U` sit in a commutative square over it
whose vertical arrows `v : V ⟶ Z` and `u : U ⟶ X` are étale.  Then `f` is formally unramified:
taking the étale localization of a formally unramified morphism preserves formal unramifiedness.

An étale morphism of algebraic spaces is formally étale by Stacks 0616, hence formally
unramified, so the diagonal `v ≫ h` of the square is formally unramified by Stacks 049T.  That
diagonal is the composite `f ≫ u`, and a first factor of a formally unramified composite whose
second factor is formally unramified is itself formally unramified by Stacks 04G5.  Étaleness of
`v` enters through formal unramifiedness of the diagonal and étaleness of `u` through formal
unramifiedness of the second factor; formal unramifiedness of `h` enters through the diagonal as
well.  The source instead reads the statement off the étale-chart criterion of Stacks 04G8; the
route taken here proves the same statement without passing through charts.

The remaining two assertions of Stacks 060D — that the universal first-order thickening of `V`
over `U` is étale over the universal first-order thickening `Z'` of `Z` over `X`, and the
resulting identification of conormal modules — are proved in the sibling module
`StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningEtaleLocalization`, which carries those
parts of the tag; nothing in this module does. -/
@[stacks 060D "the étale localization of a formally unramified morphism is formally unramified"]
theorem formallyUnramified_of_etaleLocalization {V U Z X : AlgebraicSpaces B S hS}
    (f : V ⟶ U) (v : V ⟶ Z) (h : Z ⟶ X) (u : U ⟶ X) (hsq : f ≫ u = v ≫ h)
    (hh : FormallyUnramified h.hom) (hv : IsEtale B S hS v.hom)
    (hu : IsEtale B S hS u.hom) :
    FormallyUnramified f.hom := by
  have hsq' : f.hom ≫ u.hom = v.hom ≫ h.hom := congrArg (fun k => k.hom) hsq
  -- The two étale vertical arrows are formally étale, hence formally unramified.
  have hFU : ∀ {A C : AlgebraicSpaces B S hS} (k : A ⟶ C), IsEtale B S hS k.hom →
      FormallyUnramified k.hom := fun k hk T T' hT hT' i hi x y hxy z₁ z₂ hz₁ hz₂ ↦
    (formallyEtale_of_isEtale' B S hS k hk T T' hT hT' i hi x y hxy).unique hz₁ hz₂
  have hvFU := hFU v hv
  have huFU := hFU u hu
  -- The diagonal of the square is formally unramified, and `f` is its first factor.
  have hcomp : FormallyUnramified (f.hom ≫ u.hom) := by
    rw [hsq']
    exact formallyUnramified_comp v.hom h.hom hvFU hh
  exact formallyUnramified_left_of_comp f.hom u.hom huFU hcomp

/-- **Stacks 0605, part (2).** Let `Z ⟶ Y ⟶ X` be morphisms of algebraic spaces over `S` with
`a₀ : Z ⟶ Y` surjective étale, let `g : Z' ⟶ Y'` be an étale morphism of first-order
thickenings over `X` extending `a₀`, and let `Z ⊂ Z'` be a universal first-order thickening of
`Z` over `X`.  Then `Y ⊂ Y'` is a universal first-order thickening of `Y` over `X`. -/
@[stacks 0605 "part (2)"]
theorem IsUniversalFirstOrderThickening.of_surjectiveEtale
    {X Y' Z' : AlgebraicSpaces B S hS} (Y : Subfunctor Y'.obj) (Z : Subfunctor Z'.obj)
    (p : Y' ⟶ X) (g : Z' ⟶ Y') (hg : IsEtale B S hS g.hom)
    (hY : IsFirstOrderThickening B S hS Y' Y)
    (a₀ : Z.toFunctor ⟶ Y.toFunctor) (hcompat : a₀ ≫ Y.ι = Z.ι ≫ g.hom)
    (ha₀ : IsEtale B S hS a₀) (hsurj : IsSurjective B S hS a₀)
    (hZ : IsUniversalFirstOrderThickening B S hS Z (g ≫ p)) :
    IsUniversalFirstOrderThickening B S hS Y p := by
  classical
  have hmul := (isMultiplicative_presheaf_etale B S hS).toIsStableUnderComposition
  have hq₁ : IsEtale B S hS (pullback.fst g.hom g.hom) :=
    isEtale_of_isPullback B S hS _ _ g g
      (AlgebraicSpaces.isPullback_fiberProduct B S hS g g).flip hg
  let Ysp : AlgebraicSpaces B S hS := ⟨Y.toFunctor, hY.1.1.1⟩
  let Zsp : AlgebraicSpaces B S hS := ⟨Z.toFunctor, hZ.firstOrder.1.1.1⟩
  let a₀m : Zsp ⟶ Ysp := ObjectProperty.homMk a₀
  rw [isUniversalFirstOrderThickening_iff_affine_lifting B S hS Y p hY]
  intro T' hT' T hT a b hcomm
  obtain ⟨U', hU'aff, ⟨eT'⟩⟩ := hT'
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U') := hU'aff
  have heE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf eT'.inv :=
    presheaf_etale_of_isEtale B S hS (isEtale_of_iso B S hS eT'.symm)
  obtain ⟨U₀, j, pT, hpbT, hjci, hjker⟩ :=
    exists_nthOrderThickening_chart_pullback B S hS hT U' eT'.inv heE
  have : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j) := hjci
  have hU₀aff : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map j)
  have hjsurj : Function.Surjective ((BigFppfOver.toScheme B S hS).map j).base :=
    (Stacks.Thickenings.IsNthOrderThickening.isThickening (n := 1) ⟨hjci, hjker⟩).2
  -- `W = U₀ ×_Y Z`, and an étale surjective chart of it by a scheme
  let U₀sp : AlgebraicSpaces B S hS := ⟨yoneda.obj U₀, isAlgebraicSpace_yoneda B S hS U₀⟩
  let γ : U₀sp ⟶ Ysp := ObjectProperty.homMk (pT ≫ a)
  have hWsq : IsPullback
      (ObjectProperty.homMk (pullback.fst γ.hom a₀m.hom) :
        AlgebraicSpaces.fiberProduct B S hS γ a₀m ⟶ U₀sp)
      (ObjectProperty.homMk (pullback.snd γ.hom a₀m.hom) :
        AlgebraicSpaces.fiberProduct B S hS γ a₀m ⟶ Zsp) γ a₀m :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS γ a₀m
  have hfstE : IsEtale B S hS (pullback.fst γ.hom a₀m.hom) :=
    isEtale_of_isPullback B S hS _ _ a₀m γ hWsq.flip ha₀
  have hfstS : IsSurjective B S hS (pullback.fst γ.hom a₀m.hom) :=
    isSurjective_of_isPullback B S hS hWsq.flip hsurj
  obtain ⟨W₁, μ₀, hμS, hμE⟩ := (AlgebraicSpaces.fiberProduct B S hS γ a₀m).property.exists_atlas
  obtain ⟨μ, hμeq⟩ : ∃ μ : yoneda.obj W₁ ⟶ Limits.pullback γ.hom a₀m.hom, μ = μ₀ := ⟨μ₀, rfl⟩
  rw [← hμeq] at hμS hμE
  have hπE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (μ ≫ pullback.fst γ.hom a₀m.hom) :=
    hfstE W₁ μ hμE
  have hπS : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (μ ≫ pullback.fst γ.hom a₀m.hom) := by
    refine (presheafSurjective_iff_isSurjective_yoneda B S hS (yoneda.obj U₀)
      (isAlgebraicSpace_yoneda B S hS U₀) W₁ _).2 ?_
    have h1 : Function.Surjective (pointsMap B S hS (yoneda.obj W₁) μ) :=
      isSurjective_of_presheafSurjective B S hS μ hμS
    have hcomp := pointsMap_comp B S hS (yoneda.obj W₁) μ (pullback.fst γ.hom a₀m.hom)
    have h2 := hfstS.comp h1
    rwa [← hcomp] at h2
  -- the chart as a morphism of the site, and its scheme-level properties
  let jW : W₁ ⟶ U₀ := yoneda.preimage (μ ≫ pullback.fst γ.hom a₀m.hom)
  have hjWmap : yoneda.map jW = μ ≫ pullback.fst γ.hom a₀m.hom := yoneda.map_preimage _
  have hjWE : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map jW) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ jW).1 (by rw [hjWmap]; exact hπE)
  have hjWS : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map jW) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ jW).1 (by rw [hjWmap]; exact hπS)
  -- finitely many affine opens of the chart already cover `U₀`
  have hv (i : ((BigFppfOver.toScheme B S hS).obj W₁).affineOpens) : B.Contains i.1.toScheme :=
    Scheme.size_lt_of_isOpenImmersion i.1.ι W₁.left.property
  have hopen : ∀ i : ((BigFppfOver.toScheme B S hS).obj W₁).affineOpens,
      IsOpen (Set.range (i.1.ι ≫ (BigFppfOver.toScheme B S hS).map jW).base) := by
    intro i
    simpa [Set.image_univ] using
      (i.1.ι ≫ (BigFppfOver.toScheme B S hS).map jW).isOpenMap _ isOpen_univ
  have hcov : (Set.univ : Set ((BigFppfOver.toScheme B S hS).obj U₀)) ⊆
      ⋃ i : ((BigFppfOver.toScheme B S hS).obj W₁).affineOpens,
        Set.range (i.1.ι ≫ (BigFppfOver.toScheme B S hS).map jW).base := by
    intro x _
    obtain ⟨y, hy⟩ := hjWS.1 x
    obtain ⟨i, ⟨V₀, hV₀, rfl⟩, hpV₀, -⟩ :=
      ((BigFppfOver.toScheme B S hS).obj W₁).isBasis_affineOpens.exists_subset_of_mem_open
        (show y ∈ (Set.univ : Set ((BigFppfOver.toScheme B S hS).obj W₁)) from trivial)
        isOpen_univ
    exact Set.mem_iUnion.2 ⟨⟨V₀, hV₀⟩, ⟨y, hpV₀⟩, hy⟩
  obtain ⟨sfin, hsfin⟩ := isCompact_univ.elim_finite_subcover _ hopen hcov
  have : Finite { i : ((BigFppfOver.toScheme B S hS).obj W₁).affineOpens // i ∈ sfin } :=
    sfin.finite_toSet
  let Yfam : { i : ((BigFppfOver.toScheme B S hS).obj W₁).affineOpens // i ∈ sfin } →
      Scheme.{u} := fun i => i.1.1.toScheme
  have instAff (i : { i : ((BigFppfOver.toScheme B S hS).obj W₁).affineOpens // i ∈ sfin }) :
      IsAffine (Yfam i) := i.1.2
  let d : (∐ Yfam) ⟶ (BigFppfOver.toScheme B S hS).obj W₁ :=
    Limits.Sigma.desc (fun i => i.1.1.ι)
  have : IsZariskiLocalAtSource (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  have hdE : Etale d :=
    IsZariskiLocalAtSource.sigmaDesc (fun i => by change Etale i.1.1.ι; infer_instance)
  have hYc : B.Contains (∐ Yfam) := Scheme.size_sigmaObj_lt B.aleph0_lt_cutoff
    B.aleph0_lt_cutoff_cof Cardinal.mk_le_aleph0 Yfam (fun i => hv i.1)
  obtain ⟨Au, kA', eA, hkA'⟩ := exists_siteObject_toScheme_map_eq B S hS hYc d
  have : IsAffine (∐ Yfam) := inferInstance
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj Au) := isAffine_of_isAffineHom eA.hom
  let kA : Au ⟶ U₀ := kA' ≫ jW
  have hkAmap : (BigFppfOver.toScheme B S hS).map kA =
      eA.hom ≫ d ≫ (BigFppfOver.toScheme B S hS).map jW := by
    rw [Functor.map_comp, hkA', Category.assoc]
  have hkAE : Etale ((BigFppfOver.toScheme B S hS).map kA) := by
    rw [hkAmap]; infer_instance
  have hkAS : Function.Surjective ((BigFppfOver.toScheme B S hS).map kA).base := by
    rw [hkAmap]
    intro x
    obtain ⟨i, hi, z, hz⟩ := Set.mem_iUnion₂.mp (hsfin (Set.mem_univ x))
    refine ⟨(Limits.Sigma.ι Yfam ⟨i, hi⟩ ≫ eA.inv).base z, ?_⟩
    have hkey : (Limits.Sigma.ι Yfam ⟨i, hi⟩ ≫ eA.inv) ≫
        eA.hom ≫ d ≫ (BigFppfOver.toScheme B S hS).map jW =
        i.1.ι ≫ (BigFppfOver.toScheme B S hS).map jW := by
      rw [Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc, Limits.Sigma.ι_desc]
    have hcc := congrArg (fun f : Yfam ⟨i, hi⟩ ⟶ _ => f.base z) hkey
    simpa using hcc.trans hz
  -- the étale extension of `Au ⟶ U₀` across the thickening, by Stacks 039R
  obtain ⟨Vs, q, hqE, eP, hePfac⟩ :=
    Stacks.Etale.exists_etale_pullback_iso_of_isClosedImmersion_of_surjective
      ((BigFppfOver.toScheme B S hS).map j) hjsurj
      ((BigFppfOver.toScheme B S hS).obj Au) ((BigFppfOver.toScheme B S hS).map kA) hkAE
  have : Etale q := hqE
  have hjsurj' : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map j) := ⟨hjsurj⟩
  have hfstsurj : Function.Surjective
      (Limits.pullback.fst q ((BigFppfOver.toScheme B S hS).map j)).base :=
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective.{u})
      (IsPullback.of_hasPullback q ((BigFppfOver.toScheme B S hS).map j)).flip hjsurj').1
  have : CompactSpace ↥(Limits.pullback q ((BigFppfOver.toScheme B S hS).map j)) :=
    compactSpace_of_surjective_hom eP.inv (isoSurjective eP.symm) inferInstance
  have hVcpt : CompactSpace ↥Vs :=
    compactSpace_of_surjective_hom
      (Limits.pullback.fst q ((BigFppfOver.toScheme B S hS).map j)) hfstsurj inferInstance
  have : QuasiCompact q := inferInstance
  have hVc : B.Contains Vs := contains_of_locallyOfFiniteType_of_quasiCompact B S hS q
  obtain ⟨Vu, ν, eV, hν⟩ := exists_siteObject_toScheme_map_eq B S hS hVc q
  -- the chart of the test object, and the scheme-level cartesian square over it
  have hνE : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map ν) := by
    rw [hν]; infer_instance
  have hsnd : Function.Surjective
      (Limits.pullback.snd q ((BigFppfOver.toScheme B S hS).map j)).base := by
    intro y
    obtain ⟨z, hz⟩ := hkAS y
    obtain ⟨t, ht⟩ := isoSurjective eP z
    exact ⟨t, by rw [← hePfac]; simpa [ht] using hz⟩
  have hqsurj : Function.Surjective q.base := by
    intro x
    obtain ⟨y, hy⟩ := hjsurj x
    obtain ⟨t, ht⟩ := hsnd y
    refine ⟨(Limits.pullback.fst q ((BigFppfOver.toScheme B S hS).map j)).base t, ?_⟩
    rw [← Scheme.Hom.comp_apply, Limits.pullback.condition, Scheme.Hom.comp_apply, ht, hy]
  have hνS : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map ν) := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨y, hy⟩ := hqsurj x
    obtain ⟨z, hz⟩ := isoSurjective eV y
    exact ⟨z, by rw [hν]; simpa [hz] using hy⟩
  -- the cartesian square of schemes produced by Stacks 039R, transported to the site
  have hsq0 : IsPullback
      (eP.inv ≫ Limits.pullback.fst q ((BigFppfOver.toScheme B S hS).map j))
      ((BigFppfOver.toScheme B S hS).map kA) q ((BigFppfOver.toScheme B S hS).map j) := by
    have hinvsnd : eP.inv ≫ Limits.pullback.snd q ((BigFppfOver.toScheme B S hS).map j) =
        (BigFppfOver.toScheme B S hS).map kA := by
      rw [← hePfac, Iso.inv_hom_id_assoc]
    refine IsPullback.of_iso_pullback ⟨?_⟩ eP.symm rfl hinvsnd
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hinvsnd]
  have hw : ∀ {A C : BigFppfOver B S hS} (f : A ⟶ C),
      (BigFppfOver.toScheme B S hS).map f ≫ B.inclusion.map C.hom = B.inclusion.map A.hom :=
    fun f ↦ (B.inclusion.map_comp f.left _).symm.trans (congrArg B.inclusion.map (Over.w f))
  have hwν := hw ν
  have hwj := hw j
  have hwkA := hw kA
  have hcomm1 : ((eP.inv ≫ Limits.pullback.fst q ((BigFppfOver.toScheme B S hS).map j)) ≫
        eV.inv) ≫ (BigFppfOver.toScheme B S hS).map ν =
      (BigFppfOver.toScheme B S hS).map kA ≫ (BigFppfOver.toScheme B S hS).map j := by
    rw [hν, Category.assoc, ← Category.assoc eV.inv, Iso.inv_hom_id, Category.id_comp]
    exact hsq0.w
  obtain ⟨ιA, hιA⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS
    ((eP.inv ≫ Limits.pullback.fst q ((BigFppfOver.toScheme B S hS).map j)) ≫ eV.inv)
    (by rw [← hwν, ← Category.assoc, hcomm1, Category.assoc, hwj, hwkA])
  have hsq1 : IsPullback ((BigFppfOver.toScheme B S hS).map ιA)
      ((BigFppfOver.toScheme B S hS).map kA) ((BigFppfOver.toScheme B S hS).map ν)
      ((BigFppfOver.toScheme B S hS).map j) := by
    have ht : IsPullback eV.hom ((BigFppfOver.toScheme B S hS).map ν) q
        (𝟙 ((BigFppfOver.toScheme B S hS).obj U')) :=
      IsPullback.of_horiz_isIso ⟨by rw [hν, Category.comp_id]⟩
    have hs : IsPullback (((eP.inv ≫
          Limits.pullback.fst q ((BigFppfOver.toScheme B S hS).map j)) ≫ eV.inv) ≫ eV.hom)
        ((BigFppfOver.toScheme B S hS).map kA) q
        ((BigFppfOver.toScheme B S hS).map j ≫ 𝟙 ((BigFppfOver.toScheme B S hS).obj U')) := by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact hsq0
    rw [hιA]
    exact IsPullback.of_right hs hcomm1 ht
  have hsite : IsPullback ιA kA ν j :=
    IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS) hsq1
  -- the chart of the test object
  have hwE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map ν ≫ eT'.inv) :=
    MorphismProperty.comp_mem _ _ _
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ ν).2 hνE) heE
  have hinvS : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf eT'.inv := by
    refine (presheafSurjective_iff_isSurjective_yoneda B S hS T'.obj T'.property U'
      eT'.inv).2 ?_
    have hc := pointsMap_comp B S hS T'.obj eT'.hom eT'.inv
    rw [eT'.hom_inv_id, pointsMap_id] at hc
    have hid : Function.Surjective (pointsMap B S hS (yoneda.obj U') eT'.inv ∘
        pointsMap B S hS T'.obj eT'.hom) := by rw [← hc]; exact Function.surjective_id
    exact Function.Surjective.of_comp hid
  have hwS : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map ν ≫ eT'.inv) :=
    have := isStableUnderComposition_presheaf_surjective B S hS
    MorphismProperty.comp_mem _ _ _
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ ν).2 hνS) hinvS
  -- the restriction of the test thickening to the chart, and its morphism to `Z`
  have hApb : IsPullback (yoneda.map kA ≫ pT) (yoneda.map ιA) T.ι (yoneda.map ν ≫ eT'.inv) :=
    (hsite.flip.map yoneda).paste_horiz hpbT
  let iso := (Subfunctor.isPullback_preimage (yoneda.map ν ≫ eT'.inv) T).isoIsPullback _ _ hApb
  have hisofst : iso.hom ≫ (yoneda.map kA ≫ pT) = T.fromPreimage (yoneda.map ν ≫ eT'.inv) :=
    IsPullback.isoIsPullback_hom_fst _ _ _ _
  refine existsUnique_lift_of_chart B S hS hg hcompat hZ hq₁ T hT a b hcomm
    (yoneda.map ν ≫ eT'.inv) hwS hwE
    (iso.hom ≫ yoneda.map kA' ≫ μ ≫ pullback.snd γ.hom a₀m.hom) ?_
  calc (iso.hom ≫ yoneda.map kA' ≫ μ ≫ pullback.snd γ.hom a₀m.hom) ≫ a₀
      = iso.hom ≫ yoneda.map kA' ≫ μ ≫ pullback.snd γ.hom a₀m.hom ≫ a₀m.hom := by
        simp only [Category.assoc]; rfl
    _ = iso.hom ≫ yoneda.map kA' ≫ μ ≫ pullback.fst γ.hom a₀m.hom ≫ γ.hom := by
        rw [Limits.pullback.condition (f := γ.hom) (g := a₀m.hom)]
    _ = iso.hom ≫ yoneda.map kA' ≫ (μ ≫ pullback.fst γ.hom a₀m.hom) ≫ pT ≫ a := by
        simp only [Category.assoc]; rfl
    _ = iso.hom ≫ yoneda.map kA' ≫ yoneda.map jW ≫ pT ≫ a := by rw [hjWmap]
    _ = iso.hom ≫ (yoneda.map kA ≫ pT) ≫ a := by
        rw [show kA = kA' ≫ jW from rfl, Functor.map_comp]
        simp only [Category.assoc]
    _ = (iso.hom ≫ (yoneda.map kA ≫ pT)) ≫ a := (Category.assoc _ _ _).symm
    _ = T.fromPreimage (yoneda.map ν ≫ eT'.inv) ≫ a := by rw [hisofst]

end AlgebraicGeometry.Space

end
