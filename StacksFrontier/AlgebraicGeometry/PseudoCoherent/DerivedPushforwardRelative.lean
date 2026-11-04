module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.Relative
public import StacksFrontier.CategoryTheory.Functor.Derived.DerivableOfInverts

/-!
# Derived pushforward along a closed immersion and relative pseudo-coherence

The local condition out of which relative pseudo-coherence of Stacks 09UI is built,
`AlgebraicGeometry.Scheme.Modules.IsPseudoCoherentFromAfterPushforward i E m`, asks for a complex
`K` representing `E` together with a *value of the right derived functor* of `K ↦ Q(i_*K)` at `K`,
in the sense of `CategoryTheory.Functor.IsRightDerivedValueAt`, whose vertex is pseudo-coherent.
Carrying the value cocone in the statement is what makes the condition unconditional: the
unbounded derived pushforward of sheaves of modules need not be given by a functor on the whole
derived category.

When `i` is a closed immersion the derived functor is nonetheless everywhere defined and computed
by `i_*` itself, because `i_*` is exact
(`Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward_of_isClosedImmersion`). This
file proves that, and deduces that for a closed immersion the local condition is exactly
pseudo-coherence of the honest pushforward
`(AlgebraicGeometry.Scheme.Modules.pushforward i).mapDerivedCategory.obj E`, with no cocone and no
choice of representing complex. Every use of the local condition inside Stacks 09UI is at a closed
immersion, so this is the form in which that definition is meant to be consumed.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff`: for a closed
  immersion `i`, the local condition of Stacks 09UI holds for `E` and `m` if and only if
  `i_*E`, formed with the functor induced on derived categories by the exact functor `i_*`, is
  `m`-pseudo-coherent in the sheaf-level sense of Stacks 08CB.
* `AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom.of_iso`,
  `AlgebraicGeometry.Scheme.Modules.IsPseudoCoherentFromAfterPushforward.of_iso` and
  `AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFrom.of_iso`: all three pseudo-coherence
  predicates on an object of a derived category are invariant under isomorphism of that object.

## Implementation notes

The general category-theoretic input — that a functor inverting `W` has a value of its right
derived functor at every object, namely its own value there, and that every other value is then
isomorphic to it — is `CategoryTheory.Functor.isRightDerivedValueAt_valueCoconeOfInverts` and
`CategoryTheory.Functor.IsRightDerivedValueAt.isoObjOfInverts` of
`StacksFrontier.CategoryTheory.Functor.Derived.DerivableOfInverts`.

For a closed immersion `i` of schemes, `i_*` on sheaves of modules preserves homology, so it maps
quasi-isomorphisms of cochain complexes to quasi-isomorphisms, and `DerivedCategory.Q` inverts
those; this is the hypothesis just discussed, applied to
`K ↦ Q(i_*K)`. `CategoryTheory.Functor.mapDerivedCategoryFactors` identifies the value `Q(i_*K)`
with `(i_*).mapDerivedCategory` applied to `Q(K)`, and `DerivedCategory.Q` is essentially
surjective, which supplies the representing complex in the converse direction.

The library's exactness instance for pushforward along a closed immersion is stated for
`RingedSpaceModuleAdjunction.modulePushforward i.toLRSHom.toShHom`, which is the same functor as
`AlgebraicGeometry.Scheme.Modules.pushforward i` but not reducibly so;
`AlgebraicGeometry.Scheme.Modules.preservesFiniteColimits_pushforward_of_isClosedImmersion`
restates it at the scheme-level spelling so that instance search finds it.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of these results makes the
same declaration.

## References

* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Definition 20.46.4 (08CB)](https://stacks.math.columbia.edu/tag/08CB)
* [The Stacks Project, Definition 13.14.2 (05S9)](https://stacks.math.columbia.edu/tag/05S9)
* [The Stacks Project, Lemma 20.46.11 (08KS)](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v₁ v₂ u₁ u₂ u d

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

namespace RingedSpace

/-- Sheaf-level `m`-pseudo-coherence of an object of the derived category of `𝒪_X`-modules only
depends on its isomorphism class, since it asks for an `m`-pseudo-coherent complex isomorphic to
it. -/
public theorem IsPseudoCoherentFrom.of_iso {X : RingedSpace.{u, u}}
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X)]
    {E E' : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X)} {m : ℤ}
    (h : IsPseudoCoherentFrom E m) (e : E ≅ E') : IsPseudoCoherentFrom E' m := by
  obtain ⟨K, hK, ⟨g⟩⟩ := h
  exact ⟨K, hK, ⟨g ≪≫ e⟩⟩

/-- Sheaf-level pseudo-coherence of an object of the derived category of `𝒪_X`-modules only
depends on its isomorphism class. -/
public theorem IsPseudoCoherent.of_iso {X : RingedSpace.{u, u}}
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X)]
    {E E' : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X)}
    (h : IsPseudoCoherent E) (e : E ≅ E') : IsPseudoCoherent E' := by
  obtain ⟨K, hK, ⟨g⟩⟩ := h
  exact ⟨K, hK, ⟨g ≪≫ e⟩⟩

end RingedSpace

namespace Scheme.Modules

/-- Pushforward of sheaves of modules along a closed immersion of schemes is right exact. This
restates `Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward_of_isClosedImmersion`
at the scheme-level spelling of the functor, so that instance search finds it for
`AlgebraicGeometry.Scheme.Modules.pushforward`. -/
public instance preservesFiniteColimits_pushforward_of_isClosedImmersion {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] : PreservesFiniteColimits (pushforward i) :=
  Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward_of_isClosedImmersion i

/-- The local condition of Stacks 09UI only depends on the isomorphism class of the object of the
derived category, since it asks for a complex isomorphic to it. -/
public theorem IsPseudoCoherentFromAfterPushforward.of_iso {X Y : Scheme.{u}} (i : X ⟶ Y)
    {E E' : DerivedCategory X.Modules} {m : ℤ} (h : IsPseudoCoherentFromAfterPushforward i E m)
    (e : E ≅ E') : IsPseudoCoherentFromAfterPushforward i E' m := by
  obtain ⟨K, ⟨g⟩, c, hc, hpc⟩ := h
  exact ⟨K, ⟨g ≪≫ e⟩, c, hc, hpc⟩

/-- Pushforward along a closed immersion preserves homology, so the functor
`K ↦ Q(i_*K)` from cochain complexes of `𝒪_X`-modules to the derived category of
`𝒪_Y`-modules inverts the quasi-isomorphisms. -/
public theorem quasiIso_isInvertedBy_pushforward {X Y : Scheme.{u}} (i : X ⟶ Y)
    [IsClosedImmersion i] :
    (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)).IsInvertedBy
      ((pushforward i).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) := by
  intro K L f hf
  have : QuasiIso f := hf
  dsimp only [Functor.comp_map]
  rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
  infer_instance

/-- For a closed immersion `i : X ⟶ Y` of schemes, the local condition of Stacks 09UI for an
object `E` of the derived category of `𝒪_X`-modules holds if and only if the derived pushforward
of `E` — which is `i_*E` for the functor induced on derived categories by the exact functor `i_*`
— is `m`-pseudo-coherent on `Y` in the sheaf-level sense of Stacks 08CB.

So for a closed immersion neither the representing complex nor the value cocone that the local
condition carries is a real choice: the right derived functor of `K ↦ Q(i_*K)` is everywhere
defined, and computed by `i_*` itself. -/
public theorem isPseudoCoherentFromAfterPushforward_iff {X Y : Scheme.{u}} (i : X ⟶ Y)
    [IsClosedImmersion i] (E : DerivedCategory X.Modules) (m : ℤ) :
    IsPseudoCoherentFromAfterPushforward i E m ↔
      RingedSpace.IsPseudoCoherentFrom (X := Y.toRingedSpace)
        ((pushforward i).mapDerivedCategory.obj E) m := by
  have hW := quasiIso_isInvertedBy_pushforward i
  constructor
  · rintro ⟨K, ⟨e⟩, c, hc, hpc⟩
    have iso : c.pt ≅ (pushforward i).mapDerivedCategory.obj E :=
      hc.isoObjOfInverts hW ≪≫ ((pushforward i).mapDerivedCategoryFactors.app K).symm ≪≫
        (pushforward i).mapDerivedCategory.mapIso e
    exact hpc.of_iso iso
  · intro h
    have iso : (pushforward i).mapDerivedCategory.obj E ≅
        ((pushforward i).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).obj
          (DerivedCategory.Q.objPreimage E) :=
      (pushforward i).mapDerivedCategory.mapIso
          (DerivedCategory.Q.objObjPreimageIso E).symm ≪≫
        (pushforward i).mapDerivedCategoryFactors.app _
    exact ⟨DerivedCategory.Q.objPreimage E, ⟨DerivedCategory.Q.objObjPreimageIso E⟩,
      Functor.valueCoconeOfInverts _ _ hW _,
      Functor.isRightDerivedValueAt_valueCoconeOfInverts _ _ hW _, h.of_iso iso⟩

end Scheme.Modules

namespace Scheme.Hom

/-- Relative `m`-pseudo-coherence of an object of the derived category of `𝒪_X`-modules only
depends on its isomorphism class. -/
public theorem IsPseudoCoherentFrom.of_iso {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {E E' : DerivedCategory X.Modules} {m : ℤ}
    (h : IsPseudoCoherentFrom f E m) (e : E ≅ E') : IsPseudoCoherentFrom f E' m := by
  obtain ⟨ι, V, hV, hU⟩ := h
  refine ⟨ι, V, hV, fun j => ?_⟩
  obtain ⟨κ, U, hUcover, hUloc⟩ := hU j
  refine ⟨κ, U, hUcover, fun k => ?_⟩
  obtain ⟨hle, n, g, hg, hcomm, hpc⟩ := hUloc k
  exact ⟨hle, n, g, hg, hcomm,
    hpc.of_iso g ((Scheme.Modules.restrictFunctor (U k).1.ι).mapDerivedCategory.mapIso e)⟩

/-- Relative pseudo-coherence of an object of the derived category of `𝒪_X`-modules only depends
on its isomorphism class. -/
public theorem IsPseudoCoherent.of_iso {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {E E' : DerivedCategory X.Modules}
    (h : IsPseudoCoherent f E) (e : E ≅ E') : IsPseudoCoherent f E' :=
  fun m => (h m).of_iso f e

end Scheme.Hom

end AlgebraicGeometry

end
