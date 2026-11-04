module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.DenseRestrictCommutesCompletion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.InverseImageIdealSheafDenseSquare
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.InverseImageIdealSheafToposFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.InverseImageIdealSheafToposIdealCompatible
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.PushforwardCommutesCompletionToposNonemptyIso
public import StacksFrontier.CategoryTheory.Sites.Topos.RingedToposReplacement

/-!
# [Stacks, Tag 0A0G] for a morphism of ringed topoi

Let `f : (Sh(𝒟), 𝒪') ⟶ (Sh(𝒞), 𝒪)` be a morphism of ringed topoi, let `ℐ ⊂ 𝒪` be a sheaf of
ideals **of finite type** and let `ℐ' = f^{-1}ℐ · 𝒪_X` be the ideal sheaf Section 52.7 builds out
of `ℐ`. This file proves that the canonical comparison map

`(Rf_*K)^∧ ⟶ Rf_*(K^∧)`

is invertible for **every** object `K` of `D(𝒪')` — the tag's own statement, at the tag's own
hypotheses.

## The reduction

The proof is the source's: reduce to a morphism of ringed *sites* by [Stacks, Tag 03CR], where the
statement is
`RingedSite.isIso_derivedCompletionPushforwardComparison_inverseImageIdealSheaf_of_isFiniteType`.
The square of that tag replaces `f` by

* the dense-subsite replacements `g : X ⟶ X'` and `e : Y ⟶ Y'`, which are equivalences,
* a middle arrow presented by a morphism of ringed sites, and
* a 2-isomorphism `τ` between `hs ∘ g` and `e ∘ f` — the square commutes only up to a 2-cell.

Two things make that reduction go through.

**Only an existential display has to be transported.**
`AlgebraicGeometry.RingedToposHom.isIso_derivedCompletionPushforwardComparison_of_nonempty_iso`
turns the mere existence of an isomorphism `Rf_*(D^∧) ≅ (Rf_*D)^∧` of *objects*, quantified over
all `D`, into invertibility of the *canonical* map at every `K`. So no coherence between the
isomorphisms assembled across the square and the canonical map has to be proved, so the 2-cell
`τ` costs nothing.

**The sheaves of ideals match.** Each arrow of the square builds its own `f^{-1}ℐ · 𝒪` out of the
ideal it is handed, and
`AlgebraicGeometry.RingedToposHom.inverseImageIdealSheaf_denseSquare` says those agree where the
three applications meet.

The display is then a five-step chain in `D(𝒪)`: the transport of `Rf_*` across the square
(`AlgebraicGeometry.RingedToposHom.TwoIso.derivedPushforwardIso` with the two
composition-with-an-equivalence isomorphisms), the replacement displays of
`DenseRestrictCommutesCompletion.lean` at `X` and at `Y`, and the ringed-sites case of the tag at
the middle arrow. It produces the display after applying `D(e_*)`, and `D(e_*)` is an equivalence,
so `CategoryTheory.Functor.preimageIso` brings it back.

## Main results

* `nonempty_iso_derivedPushforward_derivedCompletion_inverseImageIdealSheaf`:
  the display, for every object.
* `isIso_derivedCompletionPushforwardComparison_inverseImageIdealSheaf_of_isFiniteType`:
  **[Stacks, Tag 0A0G] and [Stacks, Tag 0A0I] for a morphism of ringed topoi.**

## References

* [Stacks Project, Tag 03CR](https://stacks.math.columbia.edu/tag/03CR)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
* [Stacks Project, Tag 099J](https://stacks.math.columbia.edu/tag/099J)
* [Stacks Project, Tag 0A0G](https://stacks.math.columbia.edu/tag/0A0G)
* [Stacks Project, Tag 0A0I](https://stacks.math.columbia.edu/tag/0A0I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Cohomology
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.RingedToposHom

attribute [local instance 100000] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

/-- Additivity of the direct image along a morphism out of a replacement ringed topos, restated
keyed on the structure literal that `AlgebraicGeometry.RingedToposHom.denseReplacement` is a
reducible abbreviation for. `AlgebraicGeometry.RingedToposHom.pushforwardModules_additive` is a
global instance, but instance search does not find it at a target whose fields reduce away in the
discrimination tree. -/
local instance additive_pushforwardModules_denseSquare {A B : RingedTopos.{u, u, u}}
    (k : RingedToposHom.{u, u, u, u, u, u} A B) :
    (pushforwardModules.{u, u, u, u, u, u} k).Additive :=
  pushforwardModules_additive.{u, u, u, u, u, u} k

section Display

variable {X Y : RingedTopos.{u, u, u}} (f : RingedToposHom.{u, u, u, u, u, u} X Y)
  (I : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.toRingedSite.O))))
  [I.toSheafOfModules.IsFiniteType]

/-- **The display of [Stacks, Tag 0A0G] at the level of objects, for a morphism of ringed
topoi**: for every `D` in `D(𝒪')` the two objects `Rf_*(D^∧)` and `(Rf_*D)^∧` are isomorphic, the
completion on the source being along `ℐ' = f^{-1}ℐ · 𝒪_X` and the one on the target along the
finite-type `ℐ`.

The isomorphism is asked to be neither canonical nor natural; that is the point, and it is what
makes the transport across the 2-isomorphism of [Stacks, Tag 03CR] possible.
`AlgebraicGeometry.RingedToposHom.isIso_derivedCompletionPushforwardComparison_of_nonempty_iso`
upgrades it to invertibility of the canonical map. See the module documentation for the chain. -/
theorem nonempty_iso_derivedPushforward_derivedCompletion_inverseImageIdealSheaf
    (M : DerivedCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O)))) :
    Nonempty ((DerivedPushforward.derivedPushforward.{u, u, u, u, u, u} f).obj
        ((RingedSite.derivedCompletion X.toRingedSite
          (inverseImageIdealSheaf.{u} f I)).obj M) ≅
      (RingedSite.derivedCompletion Y.toRingedSite I).obj
        ((DerivedPushforward.derivedPushforward.{u, u, u, u, u, u} f).obj M)) := by
  -- the square of Tag 03CR
  obtain ⟨C', instC', J', D', instD', K', v, w, uu, instv, instw, -, -, -, -, -, -, -, hu, hsq⟩ :=
    exists_twoSided_isDenseSubsite_morphismOfSites X Y f
      (fun z : PEmpty.{u + 1} ↦ z.elim) (fun z : PEmpty.{u + 1} ↦ z.elim)
  obtain ⟨-, -, -, -, ⟨h₀, hsh⟩, hh, ⟨τ₀⟩⟩ := hsq
  change h₀ = hu.morphismOfTopoi at hh
  subst hh
  have := hu.isContinuous
  let hs : RingedSite.Hom (denseReplacement X J' v).toRingedSite
      (denseReplacement Y K' w).toRingedSite :=
    { u := uu
      isMorphismOfSites := hu
      fsharp := hsh ≫ (restrictionCommRingIso K' J' uu (denseReplacement X J' v).O).hom }
  have hhs : RingedToposHom.mk.{u, u, u, u, u, u} (X := denseReplacement X J' v)
      (Y := denseReplacement Y K' w) hu.morphismOfTopoi hsh = hs.ringedToposHom := by
    unfold RingedSite.Hom.ringedToposHom
    congr 1
  have τ : TwoIso.{u, u, u, u, u, u} (A := X) (B := denseReplacement Y K' w)
      (RingedToposHom.comp.{u, u, u, u, u, u, u, u, u} (Y := denseReplacement X J' v)
        hs.ringedToposHom (denseReplacementHom X J' v))
      (RingedToposHom.comp.{u, u, u, u, u, u, u, u, u} (denseReplacementHom Y K' w) f) :=
    hhs ▸ τ₀
  -- the two ideals the replacements produce, and that they match across the middle arrow
  have hmatch : RingedSite.inverseImageIdealSheaf.{u} hs
      (denseReplacementIdeal Y K' w I) = denseReplacementIdeal X J' v
        (inverseImageIdealSheaf.{u} f I) :=
    inverseImageIdealSheaf_denseSquare f J' v K' w hs τ I
  -- the transport of `Rf_*` across the square, at an object
  let GX := denseReplacementMapDerived X J' v
  let GY := denseReplacementMapDerived Y K' w
  let Rhs := DerivedPullbackPushforwardAdjunction.derivedPushforward.{u}
    hs.toRingedToposSiteHom
  let cmp : ∀ N : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)),
      GY.obj ((DerivedPushforward.derivedPushforward.{u, u, u, u, u, u} f).obj N) ≅
        Rhs.obj (GX.obj N) := fun N =>
    ((DerivedPushforward.derivedPushforwardCompEquivIso f
        (denseReplacementHom Y K' w)).app N).symm ≪≫
      (τ.derivedPushforwardIso.app N).symm ≪≫
      (DerivedPushforward.derivedPushforwardEquivCompIso
        (denseReplacementHom X J' v) hs.ringedToposHom).app N ≪≫
      hs.derivedPushforwardToposIso.app (GX.obj N)
  -- the ringed-sites case of the tag at the middle arrow, as an existential display
  -- The ideal is generalized together with its reflector instance: it occurs in an instance
  -- argument of `AlgebraicGeometry.RingedSite.derivedCompletion`, so rewriting `hmatch` in place
  -- builds a motive that does not typecheck. With the ideal a variable, `subst` does the work and
  -- proof irrelevance identifies the two reflector instances.
  have hmid : ∀ (Q : SheafOfModules.Submodule (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (denseReplacement X J' v).toRingedSite.O)))
      [(ObjectProperty.ι (RingedSite.IsDerivedComplete.{u, u, u, u}
        (denseReplacement X J' v).toRingedSite Q)).IsRightAdjoint],
      RingedSite.inverseImageIdealSheaf.{u} hs (denseReplacementIdeal Y K' w I) = Q →
      ∀ E : DerivedCategory (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (denseReplacement X J' v).toRingedSite.O)),
      Nonempty (Rhs.obj ((RingedSite.derivedCompletion
            (denseReplacement X J' v).toRingedSite Q).obj E) ≅
        (RingedSite.derivedCompletion (denseReplacement Y K' w).toRingedSite
          (denseReplacementIdeal Y K' w I)).obj (Rhs.obj E)) := by
    intro Q _ hQ E
    subst hQ
    exact ⟨(@asIso _ _ _ _ _ <|
      RingedSite.isIso_derivedCompletionPushforwardComparison_inverseImageIdealSheaf_of_isFiniteType
        hs (denseReplacementIdeal Y K' w I) E).symm⟩
  -- the chain, after applying `D(e_*)`
  obtain ⟨pX⟩ := nonempty_iso_mapDerivedCategory_derivedCompletion_denseReplacement
    X J' v (inverseImageIdealSheaf.{u} f I) M
  obtain ⟨pmid⟩ := hmid _ hmatch (GX.obj M)
  obtain ⟨pY⟩ := nonempty_iso_mapDerivedCategory_derivedCompletion_denseReplacement
    Y K' w I ((DerivedPushforward.derivedPushforward.{u, u, u, u, u, u} f).obj M)
  have hadd : (pushforwardModules.{u, u, u, u, u, u} (denseReplacementHom Y K' w)).Additive :=
    pushforwardModules_additive.{u, u, u, u, u, u} (denseReplacementHom Y K' w)
  have hGY : GY.IsEquivalence :=
    Stacks.Injectives.mapDerivedCategory_isEquivalence
      (pushforwardModules.{u, u, u, u, u, u} (denseReplacementHom Y K' w))
  exact ⟨GY.preimageIso
    (cmp _ ≪≫ Rhs.mapIso pX ≪≫ pmid ≪≫
      (RingedSite.derivedCompletion (denseReplacement Y K' w).toRingedSite
        (denseReplacementIdeal Y K' w I)).mapIso (cmp M).symm ≪≫ pY.symm)⟩

/-- **[Stacks, Tag 0A0G].** Let `f : (Sh(𝒟), 𝒪') ⟶ (Sh(𝒞), 𝒪)` be a morphism of ringed topoi, let
`ℐ ⊂ 𝒪` be a sheaf of ideals **of finite type** and let `ℐ' = f^{-1}ℐ · 𝒪_X` be the sheaf of
ideals generated by `f^♯(f^{-1}ℐ)` that Section 52.7 builds out of `ℐ`. Then the canonical
comparison map

`(Rf_*K)^∧ ⟶ Rf_*(K^∧)`

is invertible for **every** object `K` of `D(𝒪')`, the completion on the target being taken along
`ℐ` and the one on the source along `ℐ'`.

Both of the properties `ℐ'` has to have are theorems about the construction rather than
hypotheses: the relation of [Stacks, Tag 099J] between `ℐ` and `ℐ'`, which the comparison map
needs in order to exist, is
`AlgebraicGeometry.RingedToposHom.idealCompatible_inverseImageIdealSheaf`, and finite type of
`ℐ'` — which is what makes the derived completion functor along it exist at all, by
[Stacks, Tag 099F] — is
`AlgebraicGeometry.RingedToposHom.isFiniteType_inverseImageIdealSheaf`.

The proof is the source's reduction to a morphism of ringed *sites* by [Stacks, Tag 03CR]; see the
module documentation. -/
@[stacks 0A0G "**the tag's own statement, for a morphism of ringed topoi.** For a morphism of \
ringed topoi `f`, a sheaf of ideals `ℐ ⊂ 𝒪` of finite type and `ℐ' = f^{-1}ℐ · 𝒪_X` the sheaf of \
ideals generated by `f^♯(f^{-1}ℐ)` that Section 52.7 builds out of `ℐ`, the canonical comparison \
map `(Rf_*K)^∧ ⟶ Rf_*(K^∧)` is invertible for every object `K` of `D(𝒪')`. The hypotheses are \
exactly the source's: the relation of [Stacks, Tag 099J] between the two sheaves of ideals is a \
theorem about the construction, \
`AlgebraicGeometry.RingedToposHom.idealCompatible_inverseImageIdealSheaf`, and so is finite type \
of `ℐ'`, `AlgebraicGeometry.RingedToposHom.isFiniteType_inverseImageIdealSheaf`; no object is \
excluded and no generating family is assumed global. The proof is the source's reduction to a \
morphism of ringed sites by [Stacks, Tag 03CR], whose ringed-sites case is \
`AlgebraicGeometry.RingedSite.isIso_derivedCompletionPushforwardComparison_inverseImageIdealSheaf_of_isFiniteType`. \
Two results make that reduction go through: the sheaves of ideals that the square's arrows build \
agree where the applications meet, by \
`AlgebraicGeometry.RingedToposHom.inverseImageIdealSheaf_denseSquare`, and the square's \
2-isomorphism costs no coherence because \
`AlgebraicGeometry.RingedToposHom.isIso_derivedCompletionPushforwardComparison_of_nonempty_iso` \
reduces invertibility of the canonical map to a display of objects quantified over all objects",
  stacks 0A0I "Equation 52.7.0.1 for a morphism of ringed topoi, as an invertibility of the \
**canonical** comparison map `(Rf_*ℱ)^∧ ⟶ Rf_*(ℱ^∧)`, for an **arbitrary** object of `D(𝒪')`, at \
a sheaf of ideals of finite type and the ideal sheaf `f^{-1}ℐ · 𝒪_X` that Section 52.7 builds out \
of it. The two sides of the equation are therefore identified by the map [Stacks, Tag 0A0G] \
names, and are isomorphic through it rather than merely abstractly"]
theorem isIso_derivedCompletionPushforwardComparison_inverseImageIdealSheaf_of_isFiniteType
    (K : DerivedCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O)))) :
    IsIso ((derivedCompletionPushforwardComparison f I (inverseImageIdealSheaf.{u} f I)
      (idealCompatible_inverseImageIdealSheaf.{u} f I)).app K) :=
  isIso_derivedCompletionPushforwardComparison_of_nonempty_iso f I
    (inverseImageIdealSheaf.{u} f I) (idealCompatible_inverseImageIdealSheaf.{u} f I)
    (nonempty_iso_derivedPushforward_derivedCompletion_inverseImageIdealSheaf f I) K

end Display

end AlgebraicGeometry.RingedToposHom

end
