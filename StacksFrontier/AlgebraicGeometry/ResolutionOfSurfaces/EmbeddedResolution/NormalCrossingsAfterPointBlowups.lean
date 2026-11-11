module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.Components
public import StacksFrontier.AlgebraicGeometry.CodimensionOneDivisor.Basic
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierAfterPointBlowups

/-!
# Embedded resolution on a regular surface

Let `X` be a regular Noetherian scheme of dimension two and let `Z ⊆ X` be a closed subscheme
which does not contain an irreducible component of `X`, each of whose one-dimensional irreducible
components admits a resolution by blowups at closed points. Then a finite sequence of blowups at
closed points `Xₙ → … → X₁ → X` makes the inverse image `Zₙ` of `Z` an effective Cartier divisor
supported on a strict normal crossings divisor.

## Main definitions

* `Stacks.ResolutionOfSurfaces.ComponentsInNormalPosition` — the configuration the source's
  intersection-multiplicity iteration produces: every irreducible component of a divisor is
  regular, any two components meet only in points whose ambient local ring has dimension two and
  meet there in a regular scheme, and no three components have a common point.

## Main results

* `Stacks.ResolutionOfSurfaces.isStrictNormalCrossingsDivisor_of_componentsInNormalPosition` — a
  reduced effective Cartier divisor on a regular scheme whose components are in normal position
  has strict normal crossings. This is the last paragraph of the source's proof, which reads the
  configuration off through [Stacks, Tag 0BIA].
* `Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_comap_isStrictNormalCrossings` — the
  reduction of [Stacks, Tag 0BIC] to four inputs. The tag itself is
  `Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_comap_support_eq_isStrictNormalCrossings`
  (`EmbeddedResolution/NormalCrossingsResolution.lean`), which takes none of them.

## Implementation notes

The vocabulary is the one the neighbouring tags are stated in: a sequence of blowups at closed
points is `Stacks.ResolutionOfSurfaces.PointBlowupChain`, the scheme-theoretic inverse image of a
closed subscheme is `AlgebraicGeometry.Scheme.IdealSheafData.comap`, an effective Cartier divisor
is `Stacks.Divisors.IsEffectiveCartierDivisor`, strict normal crossings is
`Stacks.Divisors.IsStrictNormalCrossingsDivisor`, and the components of a divisor and their
scheme-theoretic intersections are `Stacks.Divisors.componentIdeal` and
`Stacks.Divisors.componentIntersection`.

The source reads "let `Z ⊂ X` be a proper closed subscheme", where *proper* means *not the whole
of `X`*. That hypothesis is taken here in the form `IsNowhereDense (Z.support : Set X)`, exactly
as [Stacks, Tag 0BIB] takes it, so that the two tags agree; the literal reading is not
enough in general, since for `X` a disjoint union of two affine planes and `Z` one of them the
ideal sheaf of `Z` is zero on that copy and stays zero under every inverse image. The divisor
`Zₙ` is allowed multiplicities: it is the reduced structure on its support, which is
`Scheme.IdealSheafData.vanishingIdeal`, that has strict normal crossings. The conclusion records
that the support of `Zₙ` *equals* the support of that divisor, which is what the source's
`Zₙ = ∑ mᵢ Yᵢ` with `∑ Yᵢ` strict normal crossings gives, rather than only the inclusion that
"supported on" literally asks for.

Four statements are threaded through the reduction as explicit hypotheses, each in a generality
(arbitrary schemes, arbitrary chains) beyond what the tag needs. The unconditional
`Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_comap_support_eq_isStrictNormalCrossings`
proves the instances of their content that the source's argument uses, and that theorem carries
[Stacks, Tag 0BIC]:

* `descent` is the local splitting of [Stacks, Tag 0AGT] that the library's form of
  [Stacks, Tag 0AHH] consumes, and hence that [Stacks, Tag 0BIB] consumes; it is
  threaded through unchanged from there.
* `blowupRegular` is the global form of [Stacks, Tag 0AGR]: the blowup of a regular Noetherian
  scheme of dimension two at a closed point is again regular of dimension two.
* `resInherited` says that the resolution hypothesis on the one-dimensional components, which is
  condition (3) of [Stacks, Tag 0BI4], passes to the components of the inverse image
  along a chain of blowups at closed points.
* `normalPosition` is the intersection-multiplicity iteration in the middle of the source's
  proof: that finitely many blowups at closed points bring the components of an effective
  Cartier divisor on a regular surface into normal position. The unconditional theorem runs that
  iteration on the family of components instead
  (`Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_transverse`).

What is proved here is the reduction of the source's statement to that iteration: the Cartier
conclusion in full, by [Stacks, Tag 0BIB] followed by the composition of the two chains and the
invariance of the Cartier property along a chain; the propagation of Noetherianness, regularity
and dimension along a chain; and the whole of the source's last paragraph, which turns the
configuration into strict normal crossings. In that last step only the regularity of a pairwise
intersection and the dimension of the ambient local ring there are taken from the configuration:
that the components are effective Cartier divisors, that they have codimension one, that a
pairwise intersection has codimension two, and that an intersection of three or more components
imposes nothing are all derived.

## References

* [Stacks Project, Tag 0BIC](https://stacks.math.columbia.edu/tag/0BIC)
* [Stacks Project, Tag 0BIB](https://stacks.math.columbia.edu/tag/0BIB)
* [Stacks Project, Tag 0BIA](https://stacks.math.columbia.edu/tag/0BIA)
* [Stacks Project, Tag 0BI8](https://stacks.math.columbia.edu/tag/0BI8)
* [Stacks Project, Tag 0BI4](https://stacks.math.columbia.edu/tag/0BI4)
* [Stacks Project, Tag 0AGR](https://stacks.math.columbia.edu/tag/0AGR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Divisors

universe u

namespace Stacks.ResolutionOfSurfaces

/-! ### Properties propagated along a chain of blowups at closed points -/




/-- Granted that one blowup at a closed point of a regular Noetherian scheme of dimension two is
again regular of dimension two, a whole chain of such blowups is. -/
private theorem isRegular_of_pointBlowupChain
    (blowupRegular : ∀ Y : Scheme.{u}, IsNoetherian Y → AlgebraicGeometry.IsRegular Y →
      topologicalKrullDim Y = 2 → ∀ (y : Y) (hy : IsClosed ({y} : Set Y)),
        AlgebraicGeometry.IsRegular
            (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y))) ∧
          topologicalKrullDim
            (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y))) = 2)
    {X W : Scheme.{u}} [IsNoetherian X] (hX : AlgebraicGeometry.IsRegular X)
    (hdim : topologicalKrullDim X = 2) {T : Set X} {f : W ⟶ X}
    (h : PointBlowupChain X T W f) :
    AlgebraicGeometry.IsRegular W ∧ topologicalKrullDim W = 2 := by
  induction h with
  | refl => exact ⟨hX, hdim⟩
  | step hh w hw hwT ih =>
      exact blowupRegular _ (isNoetherian_of_pointBlowupChain hh) ih.1 ih.2 w hw

/-! ### Codimension at a point -/

/-- The codimension of the closure of a point is the Krull dimension of the local ring there. -/
private theorem codimension_closureSingleton_eq_of_ringKrullDim_stalk {X : Scheme.{u}} (x : X)
    {n : ℕ} (h : ringKrullDim (X.presheaf.stalk x) = (n : WithBot ℕ∞)) :
    codimension (IrreducibleCloseds.closureSingleton x) = (n : ℕ∞) := by
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight] at h
  rw [Stacks.AlgebraicGeometry.CodimensionOneDivisor.codimension_closureSingleton_eq_coheight]
  exact_mod_cast h

/-! ### Normal position of the components of a divisor -/

/-- The components of a divisor `D` on a scheme are **in normal position** when every irreducible
component of `D` is regular, any two of them meet in a regular scheme supported at points whose
ambient local ring has dimension two, and no three of them have a common point.

This is the configuration at which the source's intersection-multiplicity iteration stops: at
every closed point of `D` either no component passes, or exactly one and it is regular there, or
exactly two and they are regular and meet transversally. -/
public def ComponentsInNormalPosition {W : Scheme.{u}} (D : W.IdealSheafData) : Prop :=
  (∀ C : irreducibleComponents D.subscheme,
      AlgebraicGeometry.IsRegular (componentIdeal D C).subscheme) ∧
  (∀ J : Finset (irreducibleComponents D.subscheme), J.card = 2 →
      AlgebraicGeometry.IsRegular (componentIntersection D J).subscheme ∧
        ∀ x ∈ ((componentIntersection D J).support : Set W),
          ringKrullDim (W.presheaf.stalk x) = 2) ∧
  (∀ J : Finset (irreducibleComponents D.subscheme), 3 ≤ J.card →
      ((componentIntersection D J).support : Set W) = ∅)

/-! ### Components of a divisor on a regular scheme -/

/-- The support of a component of a closed subscheme is the image of that component. -/
private theorem coe_support_componentIdeal {W : Scheme.{u}} (D : W.IdealSheafData)
    (C : irreducibleComponents D.subscheme) :
    ((componentIdeal D C).support : Set W) = D.subschemeι '' (C : Set D.subscheme) := by
  have hCclosed : IsClosed (D.subschemeι '' (C : Set D.subscheme)) :=
    D.subschemeι.isClosedEmbedding.isClosedMap _
      (isClosed_of_mem_irreducibleComponents _ C.2)
  rw [componentIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact hCclosed.closure_eq

/-- A component of a closed subscheme, with its reduced structure in the ambient scheme, is
integral. -/
private theorem isIntegral_componentIdeal {W : Scheme.{u}} (D : W.IdealSheafData)
    (C : irreducibleComponents D.subscheme) :
    IsIntegral (componentIdeal D C).subscheme := by
  have hirr : IsIrreducible (Set.range (componentIdeal D C).subschemeι) := by
    rw [(componentIdeal D C).range_subschemeι, coe_support_componentIdeal D C]
    exact C.2.1.image D.subschemeι.base D.subschemeι.continuous.continuousOn
  have : IrreducibleSpace (componentIdeal D C).subscheme :=
    Scheme.IdealSheafData.irreducibleSpace_subscheme W _ hirr
  have : IsReduced (componentIdeal D C).subscheme := by
    rw [componentIdeal]; infer_instance
  exact isIntegral_of_irreducibleSpace_of_isReduced (componentIdeal D C).subscheme

/-- The generic point of a component of a closed subscheme, taken in the component with its
reduced structure in the ambient scheme, has the same image as the generic point of that
component taken in the subscheme. -/
private theorem subschemeι_genericPoint_componentIdeal {W : Scheme.{u}} (D : W.IdealSheafData)
    (C : irreducibleComponents D.subscheme) :
    letI := isIntegral_componentIdeal D C
    (componentIdeal D C).subschemeι
        (_root_.genericPoint (componentIdeal D C).subscheme) =
      D.subschemeι C.2.1.genericPoint := by
  have := isIntegral_componentIdeal D C
  have hη : IsGenericPoint C.2.1.genericPoint (C : Set D.subscheme) :=
    C.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ C.2)
  have h₁ : IsGenericPoint
      ((componentIdeal D C).subschemeι
        (_root_.genericPoint (componentIdeal D C).subscheme))
      (D.subschemeι '' (C : Set D.subscheme)) := by
    refine isGenericPoint_def.mpr ?_
    rw [← Set.image_singleton,
      (componentIdeal D C).subschemeι.isClosedEmbedding.closure_image_eq,
      genericPoint_closure, Set.image_univ, (componentIdeal D C).range_subschemeι]
    exact coe_support_componentIdeal D C
  have h₂ : IsGenericPoint (D.subschemeι C.2.1.genericPoint)
      (D.subschemeι '' (C : Set D.subscheme)) := by
    refine isGenericPoint_def.mpr ?_
    rw [← Set.image_singleton, D.subschemeι.isClosedEmbedding.closure_image_eq]
    exact congrArg (fun s : Set D.subscheme => D.subschemeι '' s) hη.def
  exact h₁.eq h₂

/-- The closure of the generic point of a component of an effective Cartier divisor has
codimension one. -/
private theorem codimension_closureSingleton_genericPoint_eq_one {W : Scheme.{u}}
    [IsLocallyNoetherian W] (D : W.IdealSheafData) (hD : IsEffectiveCartierDivisor D)
    (C : irreducibleComponents D.subscheme) :
    codimension (IrreducibleCloseds.closureSingleton (D.subschemeι C.2.1.genericPoint)) = 1 := by
  have hη : IsGenericPoint C.2.1.genericPoint (C : Set D.subscheme) :=
    C.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ C.2)
  exact_mod_cast codimension_closureSingleton_eq_of_ringKrullDim_stalk (n := 1) _ (by
    simpa using ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor D hD
      C.2.1.genericPoint ⟨C, hη⟩)

/-- Every irreducible component of an effective Cartier divisor on a scheme whose local rings are
regular is itself an effective Cartier divisor: it is integral of codimension one, and a regular
local ring is a unique factorization domain. -/
private theorem isEffectiveCartierDivisor_componentIdeal {W : Scheme.{u}}
    [IsLocallyNoetherian W] (hstalk : ∀ x : W, IsRegularLocalRing (W.presheaf.stalk x))
    (D : W.IdealSheafData) (hD : IsEffectiveCartierDivisor D)
    (C : irreducibleComponents D.subscheme) :
    IsEffectiveCartierDivisor (componentIdeal D C) := by
  have := isIntegral_componentIdeal D C
  have hcodim : codimension (IrreducibleCloseds.closureSingleton
      ((componentIdeal D C).subschemeι
        (_root_.genericPoint (componentIdeal D C).subscheme))) = 1 := by
    rw [subschemeι_genericPoint_componentIdeal D C]
    exact codimension_closureSingleton_genericPoint_eq_one D hD C
  exact isEffectiveCartierDivisor_of_codimension_one_of_uniqueFactorizationMonoid
    (componentIdeal D C) hcodim
    fun x _ => IsRegularLocalRing.uniqueFactorizationMonoid (W.presheaf.stalk x)

/-! ### Normal position gives strict normal crossings -/

/-- **The last paragraph of the proof of [Stacks, Tag 0BIC].** A reduced effective Cartier divisor
on a regular locally Noetherian scheme whose components are in normal position has strict normal
crossings.

Only the regularity of a pairwise intersection and the dimension of the ambient local ring there
are taken from the configuration. That each component is an effective Cartier divisor of
codimension one is derived from the divisor being one, that a pairwise intersection has
codimension two is read off the ambient local ring, and an intersection of three or more
components is empty and so imposes nothing. -/
public theorem isStrictNormalCrossingsDivisor_of_componentsInNormalPosition {W : Scheme.{u}}
    [IsLocallyNoetherian W] (hW : AlgebraicGeometry.IsRegular W) (D : W.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hred : IsReduced D.subscheme)
    (hpos : ComponentsInNormalPosition D) :
    IsStrictNormalCrossingsDivisor D := by
  have hstalkPair : IsLocallyNoetherian W ∧ ∀ x : W, IsRegularLocalRing (W.presheaf.stalk x) :=
    ((AlgebraicGeometry.isRegular_tfae W).out 1 2 (by simp) (by simp)).mp hW
  have hstalk : ∀ x : W, IsRegularLocalRing (W.presheaf.stalk x) := hstalkPair.2
  rw [isStrictNormalCrossingsDivisor_iff D hD]
  refine ⟨hred, isEffectiveCartierDivisor_componentIdeal hstalk D hD, fun J hJ => ?_⟩
  have hmem : ∀ y : (componentIntersection D J).subscheme,
      (componentIntersection D J).subschemeι y ∈
        ((componentIntersection D J).support : Set W) := fun y => by
    rw [← (componentIntersection D J).range_subschemeι]
    exact ⟨y, rfl⟩
  obtain hc | hc | hc : J.card = 1 ∨ J.card = 2 ∨ 3 ≤ J.card := by
    have h1 : 1 ≤ J.card := Finset.card_pos.mpr hJ
    omega
  · obtain ⟨C, rfl⟩ := Finset.card_eq_one.mp hc
    have hsingle : componentIntersection D {C} = componentIdeal D C := by
      simp [componentIntersection]
    refine ⟨by rw [hsingle]; exact hpos.1 C, fun C' => ?_⟩
    have hI : IsEffectiveCartierDivisor (componentIntersection D {C}) := by
      rw [hsingle]
      exact isEffectiveCartierDivisor_componentIdeal hstalk D hD C
    simpa using codimension_closureSingleton_genericPoint_eq_one _ hI C'
  · obtain ⟨hreg, hdim2⟩ := hpos.2.1 J hc
    refine ⟨hreg, fun C => ?_⟩
    rw [hc]
    exact codimension_closureSingleton_eq_of_ringKrullDim_stalk (n := 2) _ (by
      simpa using hdim2 _ (hmem _))
  · have hempty := hpos.2.2 J hc
    have hno : IsEmpty (componentIntersection D J).subscheme := by
      refine ⟨fun y => ?_⟩
      rw [← Set.mem_empty_iff_false, ← hempty]
      exact hmem y
    exact ⟨fun y => hno.elim y, fun C => hno.elim C.2.1.nonempty.choose⟩

/-! ### Embedded resolution -/

/-- **A reduction of [Stacks, Tag 0BIC] to four inputs.** Let `X` be a regular Noetherian scheme of
dimension two and let `Z ⊆ X` be a closed subscheme containing no irreducible component of `X` —
the source's "proper closed subscheme" — each of whose one-dimensional irreducible components
satisfies the equivalent conditions of [Stacks, Tag 0BI4], in the point-blowup form of clause (3)
there. Then there is a sequence `Xₙ → … → X₁ → X` of blowups at closed points such that the
inverse image `Zₙ` of `Z` in `Xₙ` is an effective Cartier divisor whose support carries a strict
normal crossings divisor.

Four statements are taken as hypotheses. `descent` is the local splitting of [Stacks, Tag 0AGT]
that [Stacks, Tag 0BIB] consumes, passed on unchanged. `blowupRegular` is the global form of
[Stacks, Tag 0AGR]. `resInherited` says the resolution hypothesis passes to the components of the
inverse image along a chain of blowups at closed points. `normalPosition` is the
intersection-multiplicity iteration in the middle of the source's proof, in the form of
`Stacks.ResolutionOfSurfaces.ComponentsInNormalPosition`. The tag itself is carried, with none of
these hypotheses, by
`Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_comap_support_eq_isStrictNormalCrossings`. -/
public theorem exists_pointBlowupChain_comap_isStrictNormalCrossings
    (descent : ∀ (Y : Scheme.{u}) (S : Finset Y) (J : Y.IdealSheafData),
      (∀ y ∈ S, IsClosed ({y} : Set Y)) →
      (∀ y ∈ S, IsRegularLocalRing (Y.presheaf.stalk y)) →
      (∀ y ∈ S, ringKrullDim (Y.presheaf.stalk y) = 2) →
      (J.support : Set Y) ⊆ (S : Set Y) →
      ∀ y ∈ (J.support : Set Y), ∀ hy : IsClosed ({y} : Set Y),
      ∀ M : Y.IdealSheafData, M = Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩ →
        ∃ (d : ℕ) (S' : Finset (blowUp M)) (J' : (blowUp M).IdealSheafData),
          exceptionalIdeal M ^ d * J' = J.comap (blowUpToBase M) ∧
          (∀ z ∈ S', IsClosed ({z} : Set (blowUp M))) ∧
          (∀ z ∈ S', IsRegularLocalRing ((blowUp M).presheaf.stalk z)) ∧
          (∀ z ∈ S', ringKrullDim ((blowUp M).presheaf.stalk z) = 2) ∧
          (J'.support : Set (blowUp M)) ⊆ (S' : Set (blowUp M)) ∧
          (∀ z ∈ S', (blowUpToBase M).base z ∈ S) ∧
          totalColength J' S' < totalColength J S)
    (blowupRegular : ∀ Y : Scheme.{u}, IsNoetherian Y → AlgebraicGeometry.IsRegular Y →
      topologicalKrullDim Y = 2 → ∀ (y : Y) (hy : IsClosed ({y} : Set Y)),
        AlgebraicGeometry.IsRegular
            (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y))) ∧
          topologicalKrullDim
            (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y))) = 2)
    (resInherited : ∀ (Y V : Scheme.{u}) (f : V ⟶ Y), PointBlowupChain Y Set.univ V f →
      ∀ E : Y.IdealSheafData,
      (∀ C : irreducibleComponents E.subscheme,
        topologicalKrullDim (componentIdeal E C).subscheme = 1 →
        ∃ (P : Scheme.{u}) (g : P ⟶ (componentIdeal E C).subscheme),
          PointBlowupChain (componentIdeal E C).subscheme Set.univ P g ∧
            AlgebraicGeometry.IsRegular P) →
      ∀ C : irreducibleComponents (E.comap f).subscheme,
        topologicalKrullDim (componentIdeal (E.comap f) C).subscheme = 1 →
        ∃ (P : Scheme.{u}) (g : P ⟶ (componentIdeal (E.comap f) C).subscheme),
          PointBlowupChain (componentIdeal (E.comap f) C).subscheme Set.univ P g ∧
            AlgebraicGeometry.IsRegular P)
    (normalPosition : ∀ Y : Scheme.{u}, IsNoetherian Y → AlgebraicGeometry.IsRegular Y →
      topologicalKrullDim Y = 2 → ∀ E : Y.IdealSheafData, IsEffectiveCartierDivisor E →
      (∀ C : irreducibleComponents E.subscheme,
        topologicalKrullDim (componentIdeal E C).subscheme = 1 →
        ∃ (P : Scheme.{u}) (g : P ⟶ (componentIdeal E C).subscheme),
          PointBlowupChain (componentIdeal E C).subscheme Set.univ P g ∧
            AlgebraicGeometry.IsRegular P) →
      ∃ (V : Scheme.{u}) (f : V ⟶ Y), PointBlowupChain Y Set.univ V f ∧
        IsEffectiveCartierDivisor
            (Scheme.IdealSheafData.vanishingIdeal (E.comap f).support) ∧
          ComponentsInNormalPosition
            (Scheme.IdealSheafData.vanishingIdeal (E.comap f).support))
    (X : Scheme.{u}) [IsNoetherian X] (hX : AlgebraicGeometry.IsRegular X)
    (hdim : topologicalKrullDim X = 2) (Z : X.IdealSheafData)
    (hZ : IsNowhereDense (Z.support : Set X))
    (hres : ∀ C : irreducibleComponents Z.subscheme,
      topologicalKrullDim (componentIdeal Z C).subscheme = 1 →
      ∃ (P : Scheme.{u}) (g : P ⟶ (componentIdeal Z C).subscheme),
        PointBlowupChain (componentIdeal Z C).subscheme Set.univ P g ∧
          AlgebraicGeometry.IsRegular P) :
    ∃ (W : Scheme.{u}) (f : W ⟶ X), PointBlowupChain X Set.univ W f ∧
      IsEffectiveCartierDivisor (Z.comap f) ∧
      ∃ (hW : IsLocallyNoetherian W) (D : W.IdealSheafData),
        @IsStrictNormalCrossingsDivisor W hW D ∧
          ((Z.comap f).support : Set W) = (D.support : Set W) := by
  obtain ⟨W₁, f₁, hchain₁, hcart₁⟩ :=
    exists_pointBlowupChain_comap_isEffectiveCartierDivisor descent X hX hdim Z hZ
  have hN₁ : IsNoetherian W₁ := isNoetherian_of_pointBlowupChain hchain₁
  obtain ⟨hreg₁, hdim₁⟩ := isRegular_of_pointBlowupChain blowupRegular hX hdim hchain₁
  obtain ⟨W₂, f₂, hchain₂, hDcart, hpos⟩ :=
    normalPosition W₁ hN₁ hreg₁ hdim₁ (Z.comap f₁) hcart₁
      (resInherited X W₁ f₁ hchain₁ Z hres)
  have hN₂ : IsNoetherian W₂ := isNoetherian_of_pointBlowupChain hchain₂
  have hLN₂ : IsLocallyNoetherian W₂ := IsNoetherian.toIsLocallyNoetherian
  obtain ⟨hreg₂, -⟩ := isRegular_of_pointBlowupChain blowupRegular hreg₁ hdim₁ hchain₂
  refine ⟨W₂, f₂ ≫ f₁, hchain₁.comp hchain₂ fun _ _ => Set.mem_univ _, ?_, hLN₂,
    Scheme.IdealSheafData.vanishingIdeal ((Z.comap f₁).comap f₂).support, ?_, ?_⟩
  · rw [Scheme.IdealSheafData.comap_comp]
    exact hchain₂.isEffectiveCartierDivisor_comap hcart₁
  · exact isStrictNormalCrossingsDivisor_of_componentsInNormalPosition hreg₂ _ hDcart
      inferInstance hpos
  · rw [Scheme.IdealSheafData.comap_comp,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]

end Stacks.ResolutionOfSurfaces

end
