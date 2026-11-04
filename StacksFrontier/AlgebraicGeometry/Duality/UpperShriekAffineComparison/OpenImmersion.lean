module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Basic
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineCrossing
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardClosedImmersion

/-!
# The exceptional inverse image of an open immersion

Let `S` be a scheme and let `j : X ⟶ Y` be a morphism of `AlgebraicGeometry.FTS S`, the category
of schemes separated and of finite type over `S` of [Stacks, Tag 0F42], whose underlying morphism
of schemes is an open immersion. [Stacks, Tag 0AU0] (Lemma 48.17.1) says that `j^!` is the
restriction functor, and its proof is one line: take `X̄ = Y` as the compactification of `X` over
`Y`, so that the proper structure morphism is `𝟙 Y`; the right adjoint of `R(𝟙_Y)_*` supplied by
[Stacks, Tag 0A9E] is then the identity functor, and `j^! = j^*` holds by the definition of `j^!`
as `j^* ∘ ā`.

This file formalizes that proof. The compactification by the codomain is constructed, the
identification of the right adjoint of `R(𝟙_Y)_*` with the identity is *proved*, and the
conclusion is read off from `Stacks.Duality.upperShriek`.

## Main definitions

All in the namespace `Stacks.Duality`.

* `derivedPullbackIdIso` and `derivedPushforwardIdIso` — `L(𝟙_Y)^*` and `R(𝟙_Y)_*` are the
  identity functor of `D(𝒪_Y)`.
* `quasiCoherentDerivedPushforwardIdIso` and `quasiCoherentDerivedPullbackIdIsoOfIsQuasicoherent`
  — the same for `R(𝟙_Y)_*` and for `L(𝟙_Y)^*` on `D_QCoh(𝒪_Y)`.
* `twistedInverseImageIdIso` — the twisted inverse image of `𝟙_Y`, that is the right adjoint of
  `R(𝟙_Y)_*` on `D_QCoh(𝒪_Y)`, is the identity functor. This is the step the source's proof
  calls "the right adjoint of Lemma 48.3.1 applied to `id : Y ⟶ Y` is the identity functor".
* `openCompactification` — `X ⟶ Y ⟶ Y` as an object of
  `AlgebraicGeometry.CompactificationOf (Over.mk j.left)`: the compactification by the codomain
  that the source's proof chooses.
* `Stacks.Duality.restrictedDerivedRestrictIsoQuasiCoherentDerivedPullback` — for an open
  immersion, restriction `j^*` and derived pullback `Lj^*` agree on `D_QCoh`.

## Main results

* `isLeftAdjoint_quasiCoherentDerivedPushforward_id` — `R(𝟙_Y)_*` on `D_QCoh(𝒪_Y)` has a right
  adjoint, namely the identity. For this one morphism, therefore, the conclusion of
  [Stacks, Tag 0A9E] is not a hypothesis.
* `isQuasicoherent_homology_derivedPullback_id` — `L(𝟙_Y)^*` preserves quasi-coherence of
  cohomology, so the `hpull` argument that the quasi-coherent derived pullback takes is a theorem
  for the identity morphism.
* `upperShriekIsoDerivedPullbackOfOpenImmersion` — **[Stacks, Tag 0AU0]**: for an open immersion
  `j` of `FTS S` and the compactification by the codomain,
  `j^! ≅ Lj^* : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)`.

The identification of the twisted inverse image of `𝟙_Y` with the identity,
`Stacks.Duality.twistedInverseImageIdIso`, is in
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImageFTS/Basic.lean`.

## Implementation notes

*Why the compactification is still an argument of the conclusion.* `Stacks.Duality.upperShriek`
takes the compactification as an explicit argument, because the existence of one is
[Stacks, Tag 0F41] (Nagata) and independence of the choice is [Stacks, Tag 0AA0]. The statement
below is therefore about `j^!` computed from `openCompactification`, which is exactly the
compactification the source's proof of Tag 0AU0 selects; the source also computes `j^!` at this
one compactification and appeals to independence only to transport the answer.

*`Lj^*`, not the exact restriction.* The source writes `j^*` for restriction of sheaves of
modules along the open immersion. `Stacks.Duality.upperShriek` is defined with the derived
pullback `Lj^*` as its second factor, and the conclusion is stated with
`Stacks.Duality.quasiCoherentDerivedPullback'`, which is the functor the source's "by definition"
refers to on this side; `restrictedDerivedRestrictIsoQuasiCoherentDerivedPullback` identifies it
with restriction.

## References

* [Stacks Project, Tag 0AU0](https://stacks.math.columbia.edu/tag/0AU0)
* [Stacks Project, Tag 0A9Y](https://stacks.math.columbia.edu/tag/0A9Y)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0F41](https://stacks.math.columbia.edu/tag/0F41)
* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
* [Stacks Project, Tag 0BV2](https://stacks.math.columbia.edu/tag/0BV2)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

/-! ### Derived pullback and derived direct image along the identity -/

section Identity

variable (Y : Scheme.{u})

variable (hpush : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward (𝟙 Y)).obj K.obj)).IsQuasicoherent)

/-- **Derived pullback along the identity preserves quasi-coherence of cohomology.** `L(𝟙_Y)^*`
is isomorphic to the identity functor of `D(𝒪_Y)`, so on an object of `D_QCoh(𝒪_Y)` its
cohomology sheaves are those of the object itself. This discharges, for the identity morphism,
the `hpull` argument that `Stacks.Duality.quasiCoherentDerivedPullback` takes. -/
theorem isQuasicoherent_homology_derivedPullback_id (K : quasiCoherentDerivedCategory Y)
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPullback (𝟙 Y)).obj K.obj)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    (((DerivedCategory.homologyFunctor Y.Modules i).mapIso
      ((derivedPullbackIdIso Y).app K.obj)).symm) (K.property i)

/-- **Derived pullback along the identity is the identity on `D_QCoh(𝒪_Y)`**: the ambient
isomorphism `L(𝟙_Y)^* ≅ 𝟭` read on the full subcategory of complexes with quasi-coherent
cohomology. -/
def quasiCoherentDerivedPullbackIdIsoOfIsQuasicoherent :
    quasiCoherentDerivedPullback (𝟙 Y) (isQuasicoherent_homology_derivedPullback_id Y) ≅
      𝟭 (quasiCoherentDerivedCategory Y) :=
  NatIso.ofComponents
    (fun K => ObjectProperty.isoMk _ ((derivedPullbackIdIso Y).app K.obj))
    (fun e => ObjectProperty.hom_ext _ ((derivedPullbackIdIso Y).hom.naturality e.hom))

end Identity

/-! ### The compactification of an open immersion by its codomain -/

section OpenImmersion

variable {S : Scheme.{u}} {X Y : AlgebraicGeometry.FTS S} (j : X ⟶ Y) [IsOpenImmersion j.left]

/-- **The compactification of an open immersion by its codomain.** For `j : X ⟶ Y` in
`AlgebraicGeometry.FTS S` whose underlying morphism of schemes is an open immersion, the
factorisation `X ⟶ Y ⟶ Y` through the identity of `Y` is an object of
`AlgebraicGeometry.CompactificationOf (Over.mk j.left)`: the first arrow is an open immersion by
hypothesis and the second is proper because the identity is. This is the compactification the
proof of [Stacks, Tag 0AU0] chooses, written `X̄ = Y` there. -/
def openCompactification : AlgebraicGeometry.CompactificationOf (Over.mk j.left) :=
  ⟨StructuredArrow.mk (Y := Over.mk (𝟙 Y.left))
      (Over.homMk j.left (Category.comp_id j.left)),
    ⟨inferInstanceAs (IsOpenImmersion j.left), inferInstanceAs (IsProper (𝟙 Y.left))⟩⟩

/-- The space of the compactification of `j` by its codomain is the codomain `Y`. -/
@[simp]
theorem openCompactification_space : (openCompactification j).space = Y.left :=
  rfl

/-- The open immersion of the compactification of `j` by its codomain is `j` itself. -/
@[simp]
theorem openCompactification_immersion : (openCompactification j).immersion = j.left :=
  rfl

/-- The proper structure morphism of the compactification of `j` by its codomain is `𝟙 Y`. -/
@[simp]
theorem openCompactification_toBase : (openCompactification j).toBase = 𝟙 Y.left :=
  rfl

/-! ### Restriction along an open immersion is derived pullback -/

/-- **Restriction along an open immersion is the derived pullback along it**, as functors
`D(𝒪_Y) ⥤ D(𝒪_X)` at the locally small model. Restriction is exact, so the functor it induces
on derived categories is already its derived functor, and restriction is isomorphic to pullback
along the same morphism. -/
def derivedRestrictIsoDerivedPullback {U Z : Scheme.{u}} (i : U ⟶ Z) [IsOpenImmersion i] :
    OpenImmersion.derivedRestrict i ≅ derivedPullback i :=
  haveI : (Scheme.Modules.pullback i).Additive :=
    Functor.additive_of_iso (Scheme.Modules.restrictFunctorIsoPullback i)
  haveI : PreservesFiniteLimits (Scheme.Modules.pullback i) :=
    preservesFiniteLimits_of_natIso (Scheme.Modules.restrictFunctorIsoPullback i)
  haveI : PreservesFiniteColimits (Scheme.Modules.pullback i) :=
    preservesFiniteColimits_of_natIso (Scheme.Modules.restrictFunctorIsoPullback i)
  Functor.mapDerivedCategoryCongr (Scheme.Modules.restrictFunctorIsoPullback i) ≪≫
    (derivedPullbackMapDerivedIso i).symm

/-- **Restriction along an open immersion is the derived pullback along it on `D_QCoh`**: the
ambient isomorphism `Stacks.Duality.derivedRestrictIsoDerivedPullback` read on the full
subcategories of complexes with quasi-coherent cohomology. Composed with
`Stacks.Duality.upperShriekIsoDerivedPullbackOfOpenImmersion` it exhibits `j^!` as restriction. -/
def restrictedDerivedRestrictIsoQuasiCoherentDerivedPullback {U Z : Scheme.{u}} (i : U ⟶ Z)
    [IsOpenImmersion i] :
    OpenImmersion.restrictedDerivedRestrict i ≅ quasiCoherentDerivedPullback' i :=
  NatIso.ofComponents
    (fun K => ObjectProperty.isoMk _ ((derivedRestrictIsoDerivedPullback i).app K.obj))
    (fun e => ObjectProperty.hom_ext _
      ((derivedRestrictIsoDerivedPullback i).hom.naturality e.hom))

/-! ### Tag 0AU0 -/

variable [CompactSpace S] [QuasiSeparatedSpace S]

/-- **Stacks Project, Tag 0AU0 (Lemma 48.17.1).** Let `j : X ⟶ Y` be a morphism of
`AlgebraicGeometry.FTS S` whose underlying morphism of schemes is an open immersion. Then the
exceptional inverse image of `j`, computed from the compactification of `X` by `Y` itself, is the
derived pullback along `j`:

  `j^! ≅ Lj^* : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)`.

The source's proof is reproduced: with `X̄ = Y` the proper structure morphism of the
compactification is `𝟙_Y`, the right adjoint of `R(𝟙_Y)_*` is the identity functor by
`Stacks.Duality.twistedInverseImageIdIso`, and `j^!` is `j^* ∘ ā` by definition. -/
def upperShriekIsoDerivedPullbackOfOpenImmersion :
    upperShriek j (openCompactification j) ≅ quasiCoherentDerivedPullback' j.left :=
  Functor.isoWhiskerRight (twistedInverseImageIdIso Y.left _)
      (quasiCoherentDerivedPullback' j.left) ≪≫
    (quasiCoherentDerivedPullback' j.left).leftUnitor

end OpenImmersion

end Stacks.Duality

end
