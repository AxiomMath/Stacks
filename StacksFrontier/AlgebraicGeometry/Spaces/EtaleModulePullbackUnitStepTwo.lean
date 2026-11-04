module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge

/-!
# The unit of the Stacks 03LU adjunction is the transpose of its change-of-rings half

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, and let `𝒱` denote `CategoryTheory.Sheaf.moduleSheafFunctor`, the passage from a sheaf
of modules to its underlying sheaf of sets.  The unit of the adjunction
`AlgebraicGeometry.Space.modulePullbackAdjunction` of Stacks 03LU is a map
`M ⟶ f_*(f^*M)` of `𝒪_Y`-modules, and the pullback `f^*M = 𝒪_X ⊗_{f⁻¹𝒪_Y} f⁻¹M` is an
extension of scalars applied to an inverse image, so on underlying sheaves of sets that unit
ought to be nothing but the transpose, across the adjunction `f⁻¹ ⊣ f_*` of topoi, of the
change-of-rings map `x ↦ 1 ⊗ x`.

This file proves that.  It is the second of the four steps of the comparison of the unit of
étale restriction of modules with the unit for sheaves of sets which the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackUnitComparison.lean` lay out, and which
that file records as *not available*: the obstruction identified there is a single cancellation
`𝒱(w) ≫ 𝒱(ι) = 𝒱(w)` of the comparison `ι` of the two spellings of the direct image, whose
**statement** — not proof — exceeds the elaborator's budget, because writing it forces the two
spellings of `𝒱(f_*N)` to be identified inside a composition.

The cancellation is avoided rather than paid for.
`Stacks.Sheaves.GradedAlgebraEssentiallySmall.moduleSheafFunctor_map_pullbackUnit` performs it
already, at a general ringed topos, for the adjunction with the comparison *folded in*; so the
only thing left to do at the small étale ringed topos of an algebraic space is to recognise
`AlgebraicGeometry.Space.modulePullbackAdjunction` as that adjunction transported once more
along an equality of functors, and to carry the resulting transport through.  Both steps are
cheap, and neither ever writes the cancellation down.

## Main results

* `Stacks.Sheaves.GradedAlgebraEssentiallySmall.moduleSheafFunctor_map_ofNatIsoRight_unit_app`:
  for a morphism of ringed topoi, the unit of the pullback-pushforward adjunction of
  Stacks 03D7 transported along an isomorphism of right adjoints which factors as the comparison
  of the two spellings of the direct image followed by a transport along an equality of
  functors, read on underlying sheaves of sets, is the transpose of the change-of-rings half
  followed by that transport.  The factorization is a hypothesis, which is what lets a consumer
  supply it as an equality proved elsewhere instead of having it matched against a definition.
* `AlgebraicGeometry.Space.modulePullbackAdjunction_eq_ofNatIsoRight`:
  `AlgebraicGeometry.Space.modulePullbackAdjunction` *is* the adjunction of Stacks 03D7 for the
  morphism of small étale ringed topoi, transported along
  `AlgebraicGeometry.Space.modulePushforwardIso`.  It holds by `Eq.refl`.
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_eqToIso_pushforwardModules_eq_modulePushforward`:
  the transport along the equality of the two spellings of the direct image of modules is the
  identity on underlying sheaves of sets.
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePullbackAdjunction_unit_app_comp`: the
  unit of Stacks 03LU on underlying sheaves of sets, as the transpose of the change-of-rings
  half followed by that transport.
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePullbackAdjunction_unit_app`: **the
  unit of Stacks 03LU on underlying sheaves of sets is the transpose of its change-of-rings
  half.**  This is step 2 of the comparison of
  `StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackUnitComparison.lean`.

## Implementation notes

**Why the statements are in the ringed-topos vocabulary.**  The structure sheaf of the small
étale site of an algebraic space has two spellings — `AlgebraicGeometry.Space.structureRingSheaf`,
which is the ring sheaf of `AlgebraicGeometry.Space.smallEtaleRingedSite`, and
`Stacks.SheafOfModules.Tensor.ringSheaf` of the structure sheaf of
`AlgebraicGeometry.Space.smallEtaleRingedTopos` — and identifying them is one of the
identifications the kernel budget barely affords.  Each statement below is therefore written in
the vocabulary of the *generic* lemma it is proved from, so that the elaborated term's type is
syntactically the declared one.  Writing
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePullbackAdjunction_unit_app_comp` in the
`AlgebraicGeometry.Space.structureRingSheaf` spelling instead — with everything else unchanged —
elaborates and then reports

`error: (kernel) deterministic timeout`

so the choice of spelling is not cosmetic.

**Why the adjunction is unfolded in a declaration of its own.**  Passing
`AlgebraicGeometry.Space.modulePullbackAdjunction` straight to the generic lemma asks the
elaborator to match it against `CategoryTheory.Adjunction.ofNatIsoRight` applied to a
metavariable; with the isomorphism left implicit that reaches

`error: (deterministic) timeout at 'whnf', maximum number of heartbeats (200000) has been reached`

and with the isomorphism supplied explicitly it reaches the same limit at `isDefEq`.
`AlgebraicGeometry.Space.modulePullbackAdjunction_eq_ofNatIsoRight` is that unfolding, by
`Eq.refl`, in a declaration with its own budget; the consumer then only transports along an
equation, which costs nothing.

`rw` is not used at these types: rewriting with
`AlgebraicGeometry.Space.moduleSheafFunctor_map_eqToIso_pushforwardModules_eq_modulePushforward`
inside the final statement reaches the limit at `whnf` while building its motive, whereas the
same step written as `congrArg` against `CategoryTheory.Category.comp_id` is immediate.

Nothing here raises a compiler limit or disables a linter.

## What is not done

Steps 1 and 4 of that comparison are in
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackUnitComparison.lean` and step 2 is
here, so what remains of the comparison is step 3: that the change-of-rings half followed by the
underlying sheaf of sets of the identification of Stacks 03LW is the comparison of Stacks 03LQ.
Nothing in this file bears on it.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.GradedAlgebraEssentiallySmall

namespace Stacks.Sheaves.GradedAlgebraEssentiallySmall

universe w v u₁

variable {X Y : AlgebraicGeometry.RingedTopos.{v, u₁, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : AlgebraicGeometry.RingedToposHom X Y)

/-- **The unit of the Stacks 03D7 adjunction, transported twice, on underlying sheaves of
sets.**  Let `f` be a morphism of ringed topoi, let `h : f_* = P` be an equality of functors of
sheaves of modules and let `I` be an isomorphism of the direct image of the modules development
with `P` which factors as the comparison
`AlgebraicGeometry.RingedToposHom.pushforwardModulesIso` of the two spellings of the direct image
followed by the transport along `h`.  Then the unit of the Stacks 03D7 adjunction transported
along `I`, read on underlying sheaves of sets, is the transpose of the change-of-rings half
`Stacks.Sheaves.GradedAlgebraEssentiallySmall.pullbackScalarUnit` followed by the underlying
sheaf of sets of the transport along `h`.

This is
`Stacks.Sheaves.GradedAlgebraEssentiallySmall.moduleSheafFunctor_map_pullbackUnit`, which does
the whole cancellation of the comparison once and for all, with the extra transport along `h`
carried along.  The factorization of `I` is a hypothesis rather than matched against a
definition: that is what lets a consumer pass an equality proved elsewhere, and it is the step
that makes this usable at the small étale ringed topos of an algebraic space; see this file's
implementation notes. -/
theorem moduleSheafFunctor_map_ofNatIsoRight_unit_app
    (P : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (h : f.pushforwardModules = P)
    (I : Stacks.Sheaves.RingedToposModules.pushforwardModules f.toRingedToposModulesHom ≅ P)
    (hI : I = f.pushforwardModulesIso ≪≫ eqToIso h)
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        (((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
            f.toRingedToposModulesHom).ofNatIsoRight I).unit.app M) =
      f.toToposHom.adj.homEquiv _ _ (pullbackScalarUnit f M) ≫
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          ((eqToIso h).hom.app
            (f.toRingedToposModulesHom.pullbackModules.obj M)) := by
  subst hI
  have h1 : ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
        f.toRingedToposModulesHom).ofNatIsoRight
          (f.pushforwardModulesIso ≪≫ eqToIso h)).unit.app M =
      f.pullbackAdjPushforwardModulesViaComparison.unit.app M ≫
        (eqToIso h).hom.app
          (f.toRingedToposModulesHom.pullbackModules.obj M) := by
    rw [Adjunction.unit_app_ofNatIsoRight]
    exact (Category.assoc _ _ _).symm
  rw [h1, (Sheaf.moduleSheafFunctor
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map_comp]
  exact congrArg
    (fun k ↦ k ≫ (Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
      ((eqToIso h).hom.app (f.toRingedToposModulesHom.pullbackModules.obj M)))
    (moduleSheafFunctor_map_pullbackUnit f M)

end Stacks.Sheaves.GradedAlgebraEssentiallySmall

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-! ### The adjunction of Stacks 03LU, unfolded -/

/-- `AlgebraicGeometry.Space.modulePullbackAdjunction` is the adjunction of Stacks 03D7 for the
morphism of small étale ringed topoi of Stacks 03G8, transported along the comparison
`AlgebraicGeometry.Space.modulePushforwardIso` of the two direct images.  It holds by `Eq.refl`,
being the definition.

It is recorded as a declaration of its own because the matching that this unfolding performs is
not affordable as part of an instantiation; see this file's implementation notes. -/
theorem modulePullbackAdjunction_eq_ofNatIsoRight :
    modulePullbackAdjunction B S hS f =
      (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
        (smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom).ofNatIsoRight
          (modulePushforwardIso B S hS f) := rfl

/-! ### The unit on underlying sheaves of sets -/

/-- The transport along the equality
`AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward` of the two spellings of the
direct image of modules is the identity on underlying sheaves of sets: the two have the same
underlying sheaf of sets, namely `AlgebraicGeometry.Space.smallEtaleDirectImage` of the sheaf of
sets underlying the module.

This is `AlgebraicGeometry.Space.eqToIso_pushforwardModules_hom_app_val_app` read as an equality
of morphisms of sheaves of sets rather than on each section. -/
theorem moduleSheafFunctor_map_eqToIso_pushforwardModules_eq_modulePushforward
    (N : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS Y).O)).map
        ((eqToIso (pushforwardModules_eq_modulePushforward B S hS f)).hom.app N) =
      CategoryStruct.id ((smallEtaleDirectImage B S hS f).obj (moduleSetSheaf B S hS X N)) :=
  (moduleSheafFunctor_map_eqToIso_hom_app
    (pushforwardModules_eq_modulePushforward B S hS f) N).trans rfl

/-- The unit of the Stacks 03D7 adjunction for the morphism of small étale ringed topoi,
transported along `AlgebraicGeometry.Space.modulePushforwardIso`, on underlying sheaves of sets:
the transpose of the change-of-rings half, followed by the transport along the equality of the
two spellings of the direct image.

This is
`Stacks.Sheaves.GradedAlgebraEssentiallySmall.moduleSheafFunctor_map_ofNatIsoRight_unit_app` at
the morphism of small étale ringed topoi, the factorization of the comparison being
`AlgebraicGeometry.Space.modulePushforwardIso_eq_eqToIso`: the comparison factors through the
component-wise identification of the two restrictions of scalars, and that identification is the
transport along their equality. -/
theorem moduleSheafFunctor_map_ofNatIsoRight_modulePushforwardIso_unit_app
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y).O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS Y).O)).map
        (((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
            (smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom).ofNatIsoRight
              (modulePushforwardIso B S hS f)).unit.app M) =
      (smallEtaleRingedToposHom B S hS f).toToposHom.adj.homEquiv _ _
          (pullbackScalarUnit (smallEtaleRingedToposHom B S hS f) M) ≫
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedTopos B S hS Y).O)).map
          ((eqToIso (pushforwardModules_eq_modulePushforward B S hS f)).hom.app
            ((smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom.pullbackModules.obj M)) :=
  Stacks.Sheaves.GradedAlgebraEssentiallySmall.moduleSheafFunctor_map_ofNatIsoRight_unit_app
    (smallEtaleRingedToposHom B S hS f) (modulePushforward B S hS f)
    (pushforwardModules_eq_modulePushforward B S hS f) (modulePushforwardIso B S hS f)
    (modulePushforwardIso_eq_eqToIso B S hS f) M

/-- The unit of `AlgebraicGeometry.Space.modulePullbackAdjunction` on underlying sheaves of
sets, as the transpose of the change-of-rings half followed by the transport along the equality
of the two spellings of the direct image.

It is the previous statement read through
`AlgebraicGeometry.Space.modulePullbackAdjunction_eq_ofNatIsoRight`. -/
theorem moduleSheafFunctor_map_modulePullbackAdjunction_unit_app_comp
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y).O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS Y).O)).map
        ((modulePullbackAdjunction B S hS f).unit.app M) =
      (smallEtaleRingedToposHom B S hS f).toToposHom.adj.homEquiv _ _
          (pullbackScalarUnit (smallEtaleRingedToposHom B S hS f) M) ≫
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedTopos B S hS Y).O)).map
          ((eqToIso (pushforwardModules_eq_modulePushforward B S hS f)).hom.app
            ((smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom.pullbackModules.obj M)) :=
  (congrArg
      (fun adj : modulePullback B S hS f ⊣ modulePushforward B S hS f ↦
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS Y).O)).map (adj.unit.app M))
      (modulePullbackAdjunction_eq_ofNatIsoRight B S hS f)).trans
    (moduleSheafFunctor_map_ofNatIsoRight_modulePushforwardIso_unit_app B S hS f M)

/-- **The unit of the Stacks 03LU adjunction, on underlying sheaves of sets, is the transpose of
its change-of-rings half.**  For a morphism `f : X ⟶ Y` of algebraic spaces and an `𝒪_Y`-module
`M`, the sheaf of sets underlying the unit `M ⟶ f_*(f^*M)` of
`AlgebraicGeometry.Space.modulePullbackAdjunction` is the adjunct, across the adjunction
`f⁻¹ ⊣ f_*` of small étale topoi, of the map `x ↦ 1 ⊗ x` from the inverse image of `M` to the
extension of scalars that `f^*M` is.

This is **step 2** of the four-step comparison of the unit of étale restriction of modules with
the unit for sheaves of sets which the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackUnitComparison.lean` lay out; that file
records it as unavailable, the obstruction being a cancellation whose statement exceeded the
elaborator's budget.  The cancellation is not performed here either: it is already performed, at
a general ringed topos, by
`Stacks.Sheaves.GradedAlgebraEssentiallySmall.moduleSheafFunctor_map_pullbackUnit`. -/
theorem moduleSheafFunctor_map_modulePullbackAdjunction_unit_app
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y).O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS Y).O)).map
        ((modulePullbackAdjunction B S hS f).unit.app M) =
      (smallEtaleRingedToposHom B S hS f).toToposHom.adj.homEquiv _ _
        (pullbackScalarUnit (smallEtaleRingedToposHom B S hS f) M) :=
  (moduleSheafFunctor_map_modulePullbackAdjunction_unit_app_comp B S hS f M).trans
    ((congrArg
        (fun k ↦ (smallEtaleRingedToposHom B S hS f).toToposHom.adj.homEquiv _ _
          (pullbackScalarUnit (smallEtaleRingedToposHom B S hS f) M) ≫ k)
        (moduleSheafFunctor_map_eqToIso_pushforwardModules_eq_modulePushforward B S hS f
          ((smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom.pullbackModules.obj
            M))).trans
      (Category.comp_id _))

end AlgebraicGeometry.Space

end
