module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissage
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentFromSpaceBaseEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherenceChartConditions
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherenceConditionsEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasicoherentModules

/-!
# Coherent modules across a presentation (towards Stacks 0GRC)

Let `𝒳` be a locally Noetherian algebraic stack, let `U` be an algebraic space and let
`f : 𝒰 ⟶ 𝒳` be surjective, flat and locally of finite presentation, and let `(U, R, s, t, c)` be
the attached groupoid in algebraic spaces.  Stacks 06WT gives an equivalence
`QCoh(𝒪_𝒳) ≅ QCoh(U, R, s, t, c)` whose forward functor sends `ℱ` to the pair
`(f^*ℱ|_{U_étale}, α)`.  Stacks 0GRC asserts that this equivalence sends coherent sheaves to
coherent sheaves *and vice versa*, so that it induces an equivalence
`Coh(𝒪_𝒳) ≅ Coh(U, R, s, t, c)`.

This file lands everything in Stacks 0GRC that does not depend on the construction of that
equivalence: the full subcategory `Coh(U, R, s, t, c)` of Groupoids in Spaces, Section 0GPN, the
reading of coherence of Stacks 0GR6 at a flat chart, and the restriction to the coherent
subcategories of any equivalence normalized as the equivalence of Stacks 06WT is.

## Where Stacks 0GRC is registered

**Stacks 0GRC is not registered in this file.**  The equivalence of Stacks 06WT is an argument
`e` of `AlgebraicGeometry.Stack.coherentPresentationEquivalence`, together with the normalization
`he` of its forward functor.  The equivalence `QCoh(𝒪_𝒳) ≅ QCoh(𝒪_{[U/R]}) ≅ QCoh(U, R, s, t, c)`
and its normalization are constructed in
`StacksFrontier/AlgebraicGeometry/Stacks/CoherentFlatPresentationEquivalence.lean`, where
Stacks 0GRC
is registered on `AlgebraicGeometry.Stack.SelfIntersection.coherentFlatPresentationEquivalence`.

## Main definitions

* `AlgebraicGeometry.Space.QuasicoherentModule.coherentModules` and
  `AlgebraicGeometry.Space.QuasicoherentModule.Coh`: the full subcategory
  `Coh(U, R, s, t, c) ⊂ QCoh(U, R, s, t, c)` of **coherent modules** on a groupoid in algebraic
  spaces — those `(𝒢, α)` whose underlying `𝒪_U`-module `𝒢` is coherent.
* `AlgebraicGeometry.Stack.quasicoherentCoherentModules`: `Coh(𝒪_𝒳)` of Stacks 0GR6 read inside
  `QCoh(𝒪_𝒳)`, and `AlgebraicGeometry.Stack.cohEquivQuasicoherentCoherent`, its equivalence with
  `AlgebraicGeometry.Stack.Coh`.
* `AlgebraicGeometry.Space.chartCoherentQuasicoherentSheaves`: `Coh(𝒪_X)` read at a chart, for a
  base which is an algebraic space.

## Main results

* `AlgebraicGeometry.Stack.isCoherent_iff_isCoherent_spaceChartRestriction`: in the situation of
  Stacks 0GRC a quasi-coherent `𝒪_𝒳`-module is coherent exactly when `f^*ℱ|_{U_étale}` is — the
  step the source calls "immediate from the definition", through Stacks 0GR5 and Stacks 06R6.
* `AlgebraicGeometry.Stack.inverseImage_coherentModules_eq_quasicoherentCoherentModules`: the
  transfer of coherence across a normalized equivalence, in both directions.
* `AlgebraicGeometry.Stack.coherentPresentationEquivalence`: the induced equivalence
  `Coh(𝒪_𝒳) ≌ Coh(U, R, s, t, c)`, for a given normalized equivalence.
* `AlgebraicGeometry.Space.coherentFromSpaceBaseEquivalence`: the same construction for the
  equivalence of Stacks 03M3, which the library has, with nothing carried.

## Implementation notes

The restriction of an equivalence to a pair of full subcategories is
`CategoryTheory.Equivalence.congrFullSubcategory`, which asks for the *equality*
`Q.inverseImage e.functor = P` of properties of objects and for `Q` to be closed under
isomorphism.  The equality is where "and vice versa" lives: it is proved by `propext` from the
two implications, each of which is the chart reading of coherence followed by invariance of
coherence under an isomorphism of `𝒪_U`-modules, `AlgebraicGeometry.Space.isCoherent_of_iso`.

## References

* [Stacks Project, Tag 0GRC](https://stacks.math.columbia.edu/tag/0GRC)
* [Stacks Project, Tag 0GR5](https://stacks.math.columbia.edu/tag/0GR5)
* [Stacks Project, Tag 0GR6](https://stacks.math.columbia.edu/tag/0GR6)
* [Stacks Project, Tag 06R6](https://stacks.math.columbia.edu/tag/06R6)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
* [Stacks Project, Tag 07UA](https://stacks.math.columbia.edu/tag/07UA)
-/

@[expose] public section

open CategoryTheory

universe u t

namespace AlgebraicGeometry.Space.QuasicoherentModule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)

/-- **The coherent modules on a groupoid in algebraic spaces.**  The property of a quasi-coherent
module `(𝒢, α)` on `(U, R, s, t, c)` of Stacks 0441 that its underlying `𝒪_U`-module `𝒢` be
coherent in the sense of Stacks 07UA.

This is the property cutting out the full subcategory `Coh(U, R, s, t, c) ⊂ QCoh(U, R, s, t, c)`
defined in Groupoids in Spaces, Section 0GPN, which is the right-hand side of Stacks 0GRC.

No condition is imposed on the transition morphism `α`, and none is needed: the source asks only
that the underlying `𝒪_U`-module be coherent, and `α` is an isomorphism for every object of
`QCoh(U, R, s, t, c)` already, by
`AlgebraicGeometry.Space.QuasicoherentModule.isIso_alpha`, which derives it from the cocycle and
unit laws that Stacks 0441 imposes. -/
def coherentModules : ObjectProperty (QuasicoherentModule B S hS G) :=
  fun M ↦ IsCoherent B S hS G.objects.1 G.objects.2 M.F.obj

/-- The category `Coh(U, R, s, t, c)` of coherent modules on a groupoid in algebraic spaces: the
full subcategory of `QCoh(U, R, s, t, c)` cut out by
`AlgebraicGeometry.Space.QuasicoherentModule.coherentModules`. -/
abbrev Coh := (coherentModules B S hS G).FullSubcategory

/-- An object of `Coh(U, R, s, t, c)` has coherent underlying `𝒪_U`-module. -/
theorem isCoherent_of_mem_coh (M : Coh B S hS G) :
    IsCoherent B S hS G.objects.1 G.objects.2 M.obj.F.obj :=
  M.property

/-- Coherence of a module on a groupoid in algebraic spaces is invariant under isomorphism: an
isomorphism of quasi-coherent modules on the groupoid has an isomorphism of the underlying
`𝒪_U`-modules underneath it, by `AlgebraicGeometry.Space.QuasicoherentModule.forget`, and
coherence of a module on an algebraic space is invariant under isomorphism by
`AlgebraicGeometry.Space.isCoherent_of_iso`. -/
instance : (coherentModules B S hS G).IsClosedUnderIsomorphisms where
  of_iso e hM := isCoherent_of_iso B S hS G.objects.2 ((forget G).mapIso e) hM

end AlgebraicGeometry.Space.QuasicoherentModule

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, t} B S hS)

/-- **Coherence on a locally Noetherian algebraic stack is read at any flat chart.**  Let `𝒳` be
a locally Noetherian algebraic stack, let `U` be an algebraic space and let `f : 𝒰 ⟶ 𝒳` be
surjective, flat and locally of finite presentation — the situation of Stacks 0GRC.  Then a
quasi-coherent `𝒪_𝒳`-module `ℱ` is coherent in the sense of Stacks 0GR6 if and only if its
restriction `f^*ℱ|_{U_étale}` is a coherent `𝒪_U`-module (Stacks 07UA).

This is "immediate from the definition of coherent `𝒪_𝒳`-modules", as the proof of Stacks 0GRC
says, once the definition is unfolded through Stacks 0GR5
(`AlgebraicGeometry.Stack.isCoherent_tfae`): coherence gives condition (3), which applies at `f`
because `U` is locally Noetherian (Stacks 06R6, at
`AlgebraicGeometry.Stack.hasEtaleLocalProperty_isLocallyNoetherian_of_chart`); and coherence of
`f^*ℱ|_{U_étale}` is condition (4) at the chart `f`. -/
theorem isCoherent_iff_isCoherent_spaceChartRestriction
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (f : algebraicSpaceStack.{u, t} B S hS F hF ⟶ 𝒳)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (hflat : AlgebraicStacks.IsFlat B S hS f) (hsurj : IsSurjective B S hS f)
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)) (hM : M.IsQuasicoherentOnSite) :
    IsCoherent B S hS 𝒳 M ↔
      Space.IsCoherent B S hS F hF (spaceChartRestriction B S hS 𝒳 F hF f M) := by
  have h := isCoherent_tfae B S hS 𝒳 h𝒳 M
  have hlft := AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hlfp
  have h14 : IsCoherent B S hS 𝒳 M ↔ IsCoherentOnNoetherianSpaceCharts.{u, u, t} B S hS 𝒳 M :=
    h.out 1 4
  have h15 : IsCoherent B S hS 𝒳 M ↔ IsCoherentOnSomeFlatSpaceChart.{u, u, t} B S hS 𝒳 M :=
    h.out 1 5
  refine ⟨fun hc ↦ ?_, fun hc ↦ h15.mpr ⟨hM, F, hF, f, hlft, hflat, hsurj, hc⟩⟩
  exact (h14.mp hc).2 F hF f
    (hasEtaleLocalProperty_isLocallyNoetherian_of_chart B S hS 𝒳 h𝒳 hF f hlft)

/-- A coherent `𝒪_𝒳`-module is quasi-coherent: condition (1) of Stacks 0GR5 contains
quasi-coherence. -/
theorem IsCoherent.isQuasicoherentOnSite {M : SheafOfModules.{u} (ringStructureSheafCore B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology le_rfl)}
    (hM : IsCoherent B S hS 𝒳 M) : M.IsQuasicoherentOnSite :=
  hM.1.1

/-- `Coh(𝒪_𝒳)` as a full subcategory of `QCoh(𝒪_𝒳)`: the quasi-coherent modules which are coherent
in the sense of Stacks 0GR6.  It is equivalent to `AlgebraicGeometry.Stack.Coh`, the same modules
read as a full subcategory of all `𝒪_𝒳`-modules, by
`AlgebraicGeometry.Stack.cohEquivQuasicoherentCoherent`, because a coherent module is
quasi-coherent. -/
def quasicoherentCoherentModules :
    ObjectProperty (quasicoherentModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) :=
  fun ℱ ↦ IsCoherent B S hS 𝒳 ℱ.obj

/-- **`Coh(𝒪_𝒳)` read inside `QCoh(𝒪_𝒳)`.**  The category `AlgebraicGeometry.Stack.Coh` of
coherent `𝒪_𝒳`-modules, a full subcategory of all modules, is equivalent to the full subcategory
of `QCoh(𝒪_𝒳)` cut out by coherence; both functors are the identity on underlying modules. -/
noncomputable def cohEquivQuasicoherentCoherent :
    Coh.{u, u, t} B S hS 𝒳 ≌ (quasicoherentCoherentModules B S hS 𝒳).FullSubcategory where
  functor := ObjectProperty.lift _
    (ObjectProperty.lift _ (coherentModules.{u, u, t} B S hS 𝒳).ι
      fun M ↦ IsCoherent.isQuasicoherentOnSite B S hS 𝒳 M.property)
    fun M ↦ M.property
  inverse := ObjectProperty.lift _
    ((quasicoherentCoherentModules B S hS 𝒳).ι ⋙
      (SheafOfModules.isQuasicoherentOnSite _).ι)
    fun M ↦ M.property
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)

variable {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)

/-- **The transfer of coherence across a presentation equivalence, in both directions.**  In the
situation of Stacks 0GRC — `𝒳` locally Noetherian, `f : 𝒰 ⟶ 𝒳` surjective, flat and locally of
finite presentation from the algebraic stack of the object space `U` of the groupoid — let
`e : QCoh(𝒪_𝒳) ≌ QCoh(U, R, s, t, c)` be an equivalence whose forward functor has underlying
`𝒪_U`-module `f^*ℱ|_{U_étale}`, as the forward functor of the equivalence of Stacks 06WT does.
Then `e.functor.obj ℱ` lies in `Coh(U, R, s, t, c)` exactly when `ℱ` is coherent. -/
theorem inverseImage_coherentModules_eq_quasicoherentCoherentModules
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    (f : algebraicSpaceStack.{u, t} B S hS G.objects.1 G.objects.2 ⟶ 𝒳)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (hflat : AlgebraicStacks.IsFlat B S hS f) (hsurj : IsSurjective B S hS f)
    (e : quasicoherentModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids ≌
      Space.QuasicoherentModule B S hS G)
    (he : ∀ ℱ : quasicoherentModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids,
      (e.functor.obj ℱ).F.obj ≅
        spaceChartRestriction B S hS 𝒳 G.objects.1 G.objects.2 f ℱ.obj) :
    (Space.QuasicoherentModule.coherentModules B S hS G).inverseImage e.functor =
      quasicoherentCoherentModules B S hS 𝒳 := by
  funext ℱ
  have hiff := isCoherent_iff_isCoherent_spaceChartRestriction B S hS 𝒳 h𝒳 _ _ f hlfp hflat hsurj
    ℱ.obj ℱ.property
  exact propext ⟨fun h ↦ hiff.mpr (Space.isCoherent_of_iso B S hS G.objects.2 (he ℱ) h),
    fun h ↦ Space.isCoherent_of_iso B S hS G.objects.2 (he ℱ).symm (hiff.mp h)⟩

/-- **The restriction of a presentation equivalence to the coherent subcategories.**  In the
situation of Stacks 0GRC, an equivalence `e : QCoh(𝒪_𝒳) ≌ QCoh(U, R, s, t, c)` whose forward
functor has underlying `𝒪_U`-module `f^*ℱ|_{U_étale}` restricts to an equivalence
`Coh(𝒪_𝒳) ≌ Coh(U, R, s, t, c)`, where `Coh(𝒪_𝒳)` is the category of coherent modules of
Stacks 0GR6 and `Coh(U, R, s, t, c)` that of Groupoids in Spaces, Section 0GPN.

The equivalence `e` is an argument: this declaration is the restriction step of Stacks 0GRC.  It
carries no tag; Stacks 0GRC is registered on
`AlgebraicGeometry.Stack.SelfIntersection.coherentFlatPresentationEquivalence`, which runs it at
the constructed equivalence. -/
noncomputable def coherentPresentationEquivalence
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    (f : algebraicSpaceStack.{u, t} B S hS G.objects.1 G.objects.2 ⟶ 𝒳)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (hflat : AlgebraicStacks.IsFlat B S hS f) (hsurj : IsSurjective B S hS f)
    (e : quasicoherentModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids ≌
      Space.QuasicoherentModule B S hS G)
    (he : ∀ ℱ : quasicoherentModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids,
      (e.functor.obj ℱ).F.obj ≅
        spaceChartRestriction B S hS 𝒳 G.objects.1 G.objects.2 f ℱ.obj) :
    Coh.{u, u, t} B S hS 𝒳 ≌ Space.QuasicoherentModule.Coh B S hS G :=
  (cohEquivQuasicoherentCoherent B S hS 𝒳).trans
    (e.congrFullSubcategory (inverseImage_coherentModules_eq_quasicoherentCoherentModules
      B S hS 𝒳 G h𝒳 f hlfp hflat hsurj e he))

end AlgebraicGeometry.Stack


namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
  {X : AlgebraicSpaces B S hS} (φ : G.objects ⟶ X)

/-- **`Coh(𝒪_X)` read at a chart, for a base which is an algebraic space.**  The property of a
quasi-coherent module `ℱ` on an algebraic space `X` that its inverse image `φ^*ℱ` along a
morphism `φ : U ⟶ X` of algebraic spaces be a coherent `𝒪_U`-module.

The inverse image is the one of Stacks 03LU, which is the functor the forward functor of
Stacks 03M3 is built from. -/
def chartCoherentQuasicoherentSheaves :
    ObjectProperty (QuasicoherentSheaves.{u, u} B S hS X.obj X.property) :=
  fun ℱ ↦ IsCoherent B S hS G.objects.1 G.objects.2 ((modulePullback B S hS φ).obj ℱ.obj)

/-- The category `Coh(𝒪_X)` read at a chart: the full subcategory of `QCoh(𝒪_X)` cut out by
`AlgebraicGeometry.Space.chartCoherentQuasicoherentSheaves`. -/
abbrev CohAtChart := (chartCoherentQuasicoherentSheaves B S hS G φ).FullSubcategory

/-- **The transfer of coherence across the equivalence of Stacks 03M3, in both directions.**  A
quasi-coherent `𝒪_X`-module is coherent at the chart `φ` if and only if the module it goes to on
the groupoid under the functor of Stacks 03M3 is coherent.

Nothing is carried and nothing is proved: the underlying `𝒪_U`-module of the groupoid module
attached to `ℱ` *is* the inverse image `φ^*ℱ`, by
`AlgebraicGeometry.Space.spaceBaseObj_F_obj`. -/
theorem inverseImage_coherentModules_eq_chartCoherentQuasicoherentSheaves
    (hφ : G.target ≫ φ = G.source ≫ φ) :
    (QuasicoherentModule.coherentModules B S hS G).inverseImage
        (quasicoherentFromSpaceBase B S hS G φ hφ) =
      chartCoherentQuasicoherentSheaves B S hS G φ := by
  funext ℱ
  change IsCoherent B S hS G.objects.1 G.objects.2 (spaceBaseObj B S hS G φ hφ ℱ).F.obj =
    IsCoherent B S hS G.objects.1 G.objects.2 ((modulePullback B S hS φ).obj ℱ.obj)
  rw [spaceBaseObj_F_obj]

/-- **Stacks 0GRC for the equivalence of Stacks 03M3, with nothing carried.**  Let
`(U, R, s, t, c)` be a groupoid in algebraic spaces, let `X` be an algebraic space and let
`φ : U ⟶ X` be étale with `t ≫ φ = s ≫ φ`, relatively representable, with `{φ}` a surjective
étale covering of `X` and `R = U ×_X U` — the hypotheses of Stacks 03M3 and nothing else.  Then
the equivalence `QCoh(𝒪_X) ≌ QCoh(U, R, s, t, c)` of Stacks 03M3 restricts to an equivalence
`Coh(𝒪_X) ≌ Coh(U, R, s, t, c)` of the coherent subcategories.

This is the construction of `AlgebraicGeometry.Stack.coherentPresentationEquivalence` run at an
equivalence the library has, `AlgebraicGeometry.Space.equivalenceQuasicoherentFromSpaceBase`, and
it is unconditional.

**It carries no tag, deliberately.**  Stacks 03M3 is the equivalence of the quasi-coherent
categories and says nothing about coherent modules, and Stacks 0GRC makes this claim for an
algebraic stack and the equivalence of Stacks 06WT, whereas the base here is an algebraic
space. -/
noncomputable def coherentFromSpaceBaseEquivalence (hφet : IsEtale B S hS φ.hom)
    (hφ : G.target ≫ φ = G.source ≫ φ)
    (hcov : IsEtaleCovering B S hS (fun _ : Unit => G.objects.1) (fun _ => φ.hom))
    (hrep : yoneda.relativelyRepresentable φ.hom)
    (hpb : IsPullback G.target.hom G.source.hom φ.hom φ.hom) :
    CohAtChart B S hS G φ ≌ QuasicoherentModule.Coh B S hS G :=
  (equivalenceQuasicoherentFromSpaceBase B S hS G φ hφet hφ hcov hrep hpb).congrFullSubcategory
    (inverseImage_coherentModules_eq_chartCoherentQuasicoherentSheaves B S hS G φ hφ)

end AlgebraicGeometry.Space

end
