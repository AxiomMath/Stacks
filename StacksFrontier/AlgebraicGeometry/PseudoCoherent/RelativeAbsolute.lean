module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffinePairStructureSheaf
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffinePairs
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictTarget
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SideCondition
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PullbackPushforwardAdjunction
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.FinitePresentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Relative and absolute pseudo-coherence agree over a pseudo-coherent base morphism

Let `p : P ⟶ S` be a pseudo-coherent morphism of schemes — by Stacks 067Y this is the same as
asking that `p` be locally of finite type and that `𝒪_P` be pseudo-coherent relative to `S`.
Then for *every* object `F` of `D(𝒪_P)` and every integer `m`, relative `m`-pseudo-coherence of
`F` over `S` (Stacks 09UI) is the same as absolute `m`-pseudo-coherence of `F` on `P`
(Stacks 08CB).

A flat morphism locally of finite presentation is pseudo-coherent (Stacks 0695,
`AlgebraicGeometry.pseudoCoherent_of_flat_of_locallyOfFinitePresentation`), so the equivalence
applies in particular to a flat, locally finitely presented `p`, which is the equivalence of
clauses (2) and (3) of Stacks 09UU.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_pushforward_unit_of_pseudoCoherent`: **the
  side condition of Stacks 09VA at every closed immersion of an affine open of `P` into an affine
  space over an affine open of `S`, over that open**, for `p` pseudo-coherent.
* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_iff_of_pseudoCoherent`: relative
  `m`-pseudo-coherence over `S` and absolute `m`-pseudo-coherence on `P` agree, for every object
  of `D(𝒪_P)`.
* `AlgebraicGeometry.Scheme.Hom.derivedPushforwardRelative_iff_pseudoCoherentFrom`: **the
  equivalence of clauses (2) and (3) of Stacks 09UU**, the previous result at the unbounded
  derived pushforward of an object of `D(𝒪_X)` along a morphism `i : X ⟶ P`.
* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherent_iff_of_flat_of_locallyOfFinitePresentation`:
  **Stacks 0DII for a morphism of schemes**, relative and absolute pseudo-coherence in all degrees
  at once, for `f` flat and locally of finite presentation.

## Implementation notes

**Where the two directions meet.** Both halves of Stacks 09VA —
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_pushforward_mapDerivedCategory` and
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_of_pushforward_mapDerivedCategory` — carry
the same side condition: the pushforward of the structure sheaf along the closed immersion
`j : U ⟶ 𝔸ⁿ_V` used to test the local condition must be a pseudo-coherent sheaf on `𝔸ⁿ_V`. That
single side condition is what pseudo-coherence of `p` supplies, and it is the only place the
hypothesis on `p` is used. Neither direction needs Stacks 09UJ: the direction from relative to
absolute consumes the covers that relative pseudo-coherence provides, one point at a time,
through locality of the absolute predicate
(`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_local_restrict`), and the converse
produces the cover by all compatible pairs of affine opens
(`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_of_forall_affinePair`).

**Why the side condition is available at the immersion actually used.** Pseudo-coherence of `p`
gives, at a compatible pair of affine opens `U ⊆ p ⁻¹ᵁ V`, that `Γ(P, U)` is pseudo-coherent as a
module over itself relative to `Γ(S, V)`
(`AlgebraicGeometry.algebraPseudoCoherent_appLE_iff`), and that predicate is the one quantified
over *all* finite polynomial presentations of `Γ(P, U)` over `Γ(S, V)`. So no independence
statement is needed: `AlgebraicGeometry.exists_algHom_isPseudoCoherentFromAfterPushforward_iff`
turns the given closed immersion into one such presentation and the hypothesis applies to it
directly.

**The two spellings of restriction.** The definition of relative pseudo-coherence restricts an
object along `AlgebraicGeometry.Scheme.Modules.restrictFunctor`, while locality of the absolute
predicate and `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_derivedRestrictModules` are
stated for `AlgebraicGeometry.RingedSpace.derivedRestrictModules`. The two functors are compared
by `AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor`; its two sides land in
two definitionally but not reducibly equal spellings of one category, so the comparison is passed
as a term to `AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom.of_iso`, which checks it at
default transparency.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of these results makes the
same declaration.

## References

* [The Stacks Project, Lemma 36.61.6 (09UU)](https://stacks.math.columbia.edu/tag/09UU)
* [The Stacks Project, Lemma 36.61.3 (09UT)](https://stacks.math.columbia.edu/tag/09UT)
* [The Stacks Project, Lemma 37.60.12 (0695)](https://stacks.math.columbia.edu/tag/0695)
* [The Stacks Project, Lemma 36.60.1 (067Y)](https://stacks.math.columbia.edu/tag/067Y)
* [The Stacks Project, Lemma 36.60.9 (09VA)](https://stacks.math.columbia.edu/tag/09VA)
* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Lemma 76.45.4 (0DII)](https://stacks.math.columbia.edu/tag/0DII)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

namespace Scheme.Modules

/-- **The side condition of Stacks 09VA at a closed immersion into an affine space over an affine
open of the base.** Let `p : P ⟶ S` be pseudo-coherent, let `U ⊆ p ⁻¹ᵁ V` be a compatible pair of
affine opens and let `j : U ⟶ 𝔸ⁿ_V` be a closed immersion over `V` through which `p` restricted
to `U` factors. Then `j_*𝒪_U`, placed in degree zero, is a pseudo-coherent object of
`D(𝒪_{𝔸ⁿ_V})`.

Pseudo-coherence of `p` says that `Γ(P, U)` is pseudo-coherent as a module over itself relative
to `Γ(S, V)` (`AlgebraicGeometry.algebraPseudoCoherent_appLE_iff`), and that predicate is
asserted at every finite polynomial presentation;
`AlgebraicGeometry.exists_algHom_isPseudoCoherentFromAfterPushforward_iff` exhibits `j` as such a
presentation and converts the module statement into the local condition of Stacks 09UI for `𝒪_P`
at `j`. From there
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff` reads the local
condition as `m`-pseudo-coherence of `j_*` of the restriction of `𝒪_P` to `U`, the restriction is
identified with `𝒪_U` by `AlgebraicGeometry.Scheme.Modules.restrictUnitIso`, and
`AlgebraicGeometry.RingedSpace.isPseudoCoherent_of_forall` assembles the degrees. -/
public theorem isPseudoCoherent_pushforward_unit_of_pseudoCoherent {P S : Scheme.{u}} (p : P ⟶ S)
    [PseudoCoherent p] {U : P.Opens} (hU : IsAffineOpen U) {V : S.Opens} (hV : IsAffineOpen V)
    (e : U ≤ p ⁻¹ᵁ V) {n : ℕ}
    (j : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) V.toScheme) [IsClosedImmersion j]
    (hj : j ≫ (AffineSpace.over (ULift.{u} (Fin n)) V.toScheme).hom = p.resLE V U e) :
    RingedSpace.IsPseudoCoherent
      (X := (AffineSpace (ULift.{u} (Fin n)) V.toScheme).toRingedSpace)
      ((DerivedCategory.singleFunctor
            (AffineSpace (ULift.{u} (Fin n)) V.toScheme).Modules 0).obj
        ((pushforward j).obj (SheafOfModules.unit U.toScheme.ringCatSheaf))) := by
  let : Algebra Γ(S, V) Γ(P, U) := (p.appLE V U e).hom.toAlgebra
  have : Algebra.FiniteType Γ(S, V) Γ(P, U) := algebraFiniteType_appLE p U hU V hV e
  have hrel : PseudoCoherence.IsModuleRelativelyPseudoCoherent
      (R := Γ(S, V)) (A := Γ(P, U)) Γ(P, U) :=
    (algebraPseudoCoherent_appLE_iff p U hU V hV e).mp
      (PseudoCoherent.pseudoCoherent_appLE p hV hU e)
  refine RingedSpace.isPseudoCoherent_of_forall.{u} _ fun m => ?_
  obtain ⟨α, hα, hiff⟩ :=
    exists_algHom_isPseudoCoherentFromAfterPushforward_iff p hU hV e rfl j hj m
  have eU := (Functor.mapDerivedCategorySingleFunctor (restrictFunctor U.ι) 0).app
      (SheafOfModules.unit P.ringCatSheaf) ≪≫
    (DerivedCategory.singleFunctor U.toScheme.Modules 0).mapIso (restrictUnitIso U.ι)
  exact RingedSpace.IsPseudoCoherentFrom.of_iso
    (X := (AffineSpace (ULift.{u} (Fin n)) V.toScheme).toRingedSpace)
    ((isPseudoCoherentFromAfterPushforward_iff j _ m).mp
      ((isPseudoCoherentFromAfterPushforward_iff_of_iso j eU m).mp (hiff.mpr (hrel m n α hα))))
    (((pushforward j).mapDerivedCategorySingleFunctor 0).app _)

end Scheme.Modules

namespace Scheme.Hom

/-- **Relative and absolute `m`-pseudo-coherence agree over a pseudo-coherent morphism.** Let
`p : P ⟶ S` be a pseudo-coherent morphism of schemes, let `F` be an object of `D(𝒪_P)` and let `m`
be an integer. Then `F` is relatively `m`-pseudo-coherent for `p` in the sense of Stacks 09UI if
and only if it is `m`-pseudo-coherent on `P` in the sheaf-level sense of Stacks 08CB.

Forwards, absolute `m`-pseudo-coherence is local on `P`
(`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_local_restrict`), and around a point one
member of each of the two covers that relative pseudo-coherence provides gives a closed immersion
to which the converse half of Stacks 09VA applies, its side condition being
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_pushforward_unit_of_pseudoCoherent`.

Backwards, `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_of_forall_affinePair` reduces the
relative condition to every compatible pair of affine opens; on such a pair a closed immersion
exists by `AlgebraicGeometry.exists_isClosedImmersion_affineSpace_resLE`, the restriction of `F`
is `m`-pseudo-coherent by
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_derivedRestrictModules`, and the forward half
of Stacks 09VA pushes that forward with the same side condition. -/
@[sga "6 III 1.11" "(b), special case"]
public theorem isPseudoCoherentFrom_iff_of_pseudoCoherent {P S : Scheme.{u}} (p : P ⟶ S)
    [PseudoCoherent p] (F : DerivedCategory P.Modules) (m : ℤ) :
    p.IsPseudoCoherentFrom F m ↔
      RingedSpace.IsPseudoCoherentFrom (X := P.toRingedSpace) F m := by
  constructor
  · rintro ⟨ι, V, hVcov, hV⟩
    refine RingedSpace.isPseudoCoherentFrom_of_local_restrict
      (X := P.toRingedSpace) F m fun x => ?_
    have hxS : p.base x ∈ (⨆ a, ((V a).1 : S.Opens)) := hVcov ▸ Opens.mem_top _
    obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hxS
    obtain ⟨κ, U, hUcov, hU⟩ := hV a
    have hxP : x ∈ (⨆ b, ((U b).1 : P.Opens)) := hUcov ▸ ha
    obtain ⟨b, hb⟩ := Opens.mem_iSup.mp hxP
    obtain ⟨hle, n, j, _, hjo, hpc⟩ := hU b
    refine ⟨(U b).1, hb, ?_⟩
    have hside := Scheme.Modules.isPseudoCoherent_pushforward_unit_of_pseudoCoherent
      p (U b).2 (V a).2 hle j hjo
    have hres := Scheme.Modules.isPseudoCoherentFrom_of_pushforward_mapDerivedCategory j hside m _
      ((Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff j _ m).mp hpc)
    exact hres.of_iso
      (((RingedSpace.derivedRestrictModulesIsoRestrictFunctor P (U b).1).app F).symm)
  · intro hF
    refine isPseudoCoherentFrom_of_forall_affinePair p F m fun U V hUV => ?_
    obtain ⟨n, j, hcj, hjo⟩ := exists_isClosedImmersion_affineSpace_resLE p V U hUV
    refine ⟨n, j, hcj, hjo, ?_⟩
    have hside := Scheme.Modules.isPseudoCoherent_pushforward_unit_of_pseudoCoherent
      p U.2 V.2 hUV j hjo
    have hres := (RingedSpace.isPseudoCoherentFrom_derivedRestrictModules
        (X := P.toRingedSpace) F m hF U.1).of_iso
      ((RingedSpace.derivedRestrictModulesIsoRestrictFunctor P U.1).app F)
    exact (Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff j _ m).mpr
      (Scheme.Modules.isPseudoCoherentFrom_pushforward_mapDerivedCategory j hside m _ hres)

/-- **Stacks 09UU, the equivalence of clauses (2) and (3).** Let `i : X ⟶ P` be a morphism of
schemes and let `p : P ⟶ S` be flat and locally of finite presentation. For an object `E` of
`D(𝒪_X)` and an integer `m`, the unbounded derived pushforward `Ri_*E` is relatively
`m`-pseudo-coherent for `p` if and only if it is `m`-pseudo-coherent on `P`.

This is `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_iff_of_pseudoCoherent` at the object
`Ri_*E`, together with
`AlgebraicGeometry.pseudoCoherent_of_flat_of_locallyOfFinitePresentation`. Nothing about `Ri_*E`
beyond its being an object of `D(𝒪_P)` is used, and in particular no hypothesis on `i` is
needed. -/
@[stacks 09UU "the equivalence of clauses (2) and (3)"]
public theorem derivedPushforwardRelative_iff_pseudoCoherentFrom {X P S : Scheme.{u}} (i : X ⟶ P)
    (p : P ⟶ S) [Flat p] [LocallyOfFinitePresentation p] (E : DerivedCategory X.Modules)
    (m : ℤ) :
    p.IsPseudoCoherentFrom
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          i.toLRSHom.toShHom).obj E) m ↔
      RingedSpace.IsPseudoCoherentFrom (X := P.toRingedSpace)
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          i.toLRSHom.toShHom).obj E) m :=
  isPseudoCoherentFrom_iff_of_pseudoCoherent p _ m

/-- **Stacks 0DII, the case of schemes.** Let `f : X ⟶ Y` be a flat morphism of schemes locally of
finite presentation and let `E` be an object of `D(𝒪_X)`. Then `E` is pseudo-coherent relative to
`Y` in the sense of Stacks 09UI if and only if `E` is pseudo-coherent on `X` in the sheaf-level
sense of Stacks 08CB. -/
@[stacks 0DII "the case of schemes"]
public theorem isPseudoCoherent_iff_of_flat_of_locallyOfFinitePresentation {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] (E : DerivedCategory X.Modules) :
    f.IsPseudoCoherent E ↔ RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E := by
  refine ⟨fun h => RingedSpace.isPseudoCoherent_of_forall E fun m =>
      (isPseudoCoherentFrom_iff_of_pseudoCoherent f E m).mp (h m), fun h m => ?_⟩
  obtain ⟨K, hK, e⟩ := h
  exact (isPseudoCoherentFrom_iff_of_pseudoCoherent f E m).mpr ⟨K, hK m, e⟩

end Scheme.Hom

end AlgebraicGeometry

end
