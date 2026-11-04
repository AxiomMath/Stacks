module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDualLocalDualBasis
import StacksCore.Tactic.StacksAttribute

/-!
# The dual of a module locally a summand of a finite free module is a left dual

Let `(C, 𝒪)` be a ringed site and let `F` be a sheaf of `𝒪`-modules such that **every object `U`
of `C` has a covering `{U_i → U}` on whose members `F` restricts to a direct summand of a finite
free `𝒪|_{U_i}`-module**. [Stacks, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY) asserts
that then the canonical map

`F ⊗_𝒪 SheafHom(F, 𝒪) ⟶ SheafHom(F, F)`

is an isomorphism, and that the dual `F^∨ = SheafHom(F, 𝒪)`, together with the coevaluation
`η : 𝒪 ⟶ F ⊗ F^∨` obtained from it and the evaluation `ε : F^∨ ⊗ F ⟶ 𝒪`, is a **left dual** of
`F` in the monoidal category of sheaves of `𝒪`-modules.

The four objects and the isomorphism are already in the library, where they carry
`@[stacks 0FNV]`: `Stacks.SheafOfModules.dualSheaf` and `Stacks.SheafOfModules.evaluation` in
`...Sheaf.SheafHom`, `Stacks.SheafOfModules.tensorDualToEndomorphism`,
`Stacks.SheafOfModules.isIso_tensorDualToEndomorphism` and
`Stacks.SheafOfModules.coevaluation` in `...Sheaf.TensorDualEndomorphism`, and the exact pairing
`Stacks.SheafOfModules.exactPairingDualSheafOfRetract` in `...Sheaf.LeftDualLocalDualBasis`. All
of them are stated for an arbitrary site, so Tag 0FNV and Tag 0FNY are the same mathematics; what
differs is the *shape of the local hypothesis*. Those declarations take it in the form of a family
of objects `X : K → C` covering the final object (`CategoryTheory.GrothendieckTopology.CoversTop`)
on which `F` is a retract of a finite free module, whereas Tag 0FNY states it per object, as a
covering sieve of every object of `C`. This file is that form of the hypothesis and the passage
from it to the other, which is what makes Tag 0FNY compose with its converse Tag 0FNZ: the
conclusion of `Stacks.SheafOfModules.exists_cover_retract_finiteFree_of_exactPairing` is exactly
the predicate below.

## Main definitions

* `Stacks.SheafOfModules.IsLocallyDirectSummandOfFiniteFree`: the hypothesis of Tag 0FNY — on a
  covering of every object, `F` restricts to a direct summand of a finite free module.
* `Stacks.SheafOfModules.LocalFiniteFreeSummandCover` and
  `Stacks.SheafOfModules.localFiniteFreeSummandCover`: the covering data the imported duality
  statements consume, and its extraction from the predicate above.
* `Stacks.SheafOfModules.exactPairingDualSheafOfLocalSummand`: **the exact pairing of Tag 0FNY**,
  exhibiting `F^∨` as a left dual of `F`, and
  `Stacks.SheafOfModules.hasRightDualOfLocalSummand` the same read as
  `CategoryTheory.HasRightDual F`, which is Mathlib's spelling of "`F^∨` is a left dual of `F`".

## Main results

* `Stacks.SheafOfModules.exists_coversTop_retract_of_isLocallyDirectSummandOfFiniteFree`: the
  passage from the per-object hypothesis to a single family of objects covering the final object
  which carries the retracts. This is the only step the file proves, and every other result in it
  is this step composed with an imported one.
* `Stacks.SheafOfModules.isIso_tensorDualToEndomorphism_of_localSummand`: **the first assertion
  of Tag 0FNY**, that `F ⊗ F^∨ ⟶ SheafHom(F, F)` is an isomorphism.

## Implementation notes

**The family is indexed by the arrows of the chosen sieves.** Given a covering sieve `S_U` of
each object `U`, the family is indexed by all pairs of an object `U` and an arrow `V ⟶ U` lying
in `S_U`, and its value there is the source `V`. That family covers the final object for a direct
reason: the sieve witnessing `Sieve.ofObjects` at an object `W` can be taken to be `S_W` itself,
since every arrow `V ⟶ W` of `S_W` has `V` as a member of the family, through the identity. No
pullback of sieves and no refinement is needed, which is why the step is three lines. The chosen
sieves and the finite index types are extracted with `choose`, so the declarations producing data
are noncomputable; the pairing is independent of those choices because
`Stacks.SheafOfModules.coevaluation` is determined by
`Stacks.SheafOfModules.coevaluation_comp_tensorDualToEndomorphism` and the isomorphism it
inverts.

**The index types.** Tag 0FNY says "finite free", so the predicate quantifies over an index type
with `Finite`, in the module universe, as
`Stacks.SheafOfModules.exists_cover_retract_finiteFree_of_exactPairing` produces it. The imported
pairing wants `Fintype` and `DecidableEq`, which are supplied classically where it is applied; no
`Fin n` reindexing is needed, because the imported statement already accepts an arbitrary finite
index type.

**Universes.** The sections of `𝒪` and of the modules live in `max u v`, where `u` and `v` are the
universes of the objects and the arrows of the site. That is forced by the internal hom of Tag
03EM, which the dual is an instance of: a section of `SheafHom(F, G)` over `U` is a morphism of
presheaves of modules on the slice site `C/U`, whose arrows live in `max u v`. Tag 0FNZ, which
does not mention the internal hom, is stated with an independent section universe.

## References

* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY)
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV) — the same example for a
  ringed space.
* [Stacks Project, Tag 0FNZ](https://stacks.math.columbia.edu/tag/0FNZ) — the converse.
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP) — left duals in a
  monoidal category.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the monoidal structure.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite SheafOfModules

universe v u

namespace Stacks.SheafOfModules

attribute [local instance] Strict.monoidalCategory monoidalCategoryPresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
  (h𝒪 : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf 𝒪))

/-- **A sheaf of modules locally a direct summand of a finite free module.** Every object `U` of
the site has a covering sieve on whose members `F` restricts to a retract of a free sheaf of
modules on a finite index type.

This is the hypothesis of Stacks 0FNY and the conclusion of Stacks 0FNZ (1). -/
@[sga "6 II 2.0" "special case"]
def IsLocallyDirectSummandOfFiniteFree
    (F : SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪)) : Prop :=
  ∀ U : C, ∃ S : Sieve U, S ∈ J U ∧
    ∀ (V : C) (i : V ⟶ U), S i →
      ∃ I : Type (max u v), Finite I ∧
        Nonempty (Retract (F.over V)
          (free (R := (TensorSheafification.structureSheaf 𝒪 h𝒪).over V) I))

variable (F : SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪))

/-- **The covering data of Stacks 0FNY.** A single family of objects covering the final object,
together with a finite index type and a retract of the restriction of `F` onto the free module on
it for each member of the family. This is the form of the local hypothesis that the duality
statements of Tag 0FNV consume, and `Stacks.SheafOfModules.localFiniteFreeSummandCover` produces
it from the per-object form that Tag 0FNY states. -/
structure LocalFiniteFreeSummandCover where
  /-- The index type of the family. -/
  K : Type (max u v)
  /-- The family of objects. -/
  X : K → C
  /-- The family covers the final object. -/
  coversTop : J.CoversTop X
  /-- The finite index type of the free module at a member of the family. -/
  I : K → Type (max u v)
  /-- Each index type is finite, as an enumeration. -/
  fintypeI : ∀ k, Fintype (I k)
  /-- Equality of indices is decidable. -/
  decEqI : ∀ k, DecidableEq (I k)
  /-- `F` restricted to a member of the family is a retract of a finite free module. -/
  retract : ∀ k, Retract (F.over (X k))
    (free (R := (TensorSheafification.structureSheaf 𝒪 h𝒪).over (X k)) (I k))

/-- **The covering data of Stacks 0FNY, extracted from the per-object hypothesis.** Index the
family by the pairs of an object and an arrow into it belonging to the chosen covering sieve of
that object, and take the source of the arrow as its value. That family covers the final object
because the chosen sieve of an object already consists of arrows whose sources are members of the
family, through the identity; no pullback of sieves and no refinement is needed. -/
noncomputable def localFiniteFreeSummandCover
    (hF : IsLocallyDirectSummandOfFiniteFree 𝒪 h𝒪 F) :
    LocalFiniteFreeSummandCover 𝒪 h𝒪 F := by
  classical
  choose S hS hret using hF
  exact
    { K := Σ U : C, Σ V : C, { i : V ⟶ U // S U i }
      X := fun k => k.2.1
      coversTop := fun W =>
        J.superset_covering (fun V g hg => ⟨⟨W, V, g, hg⟩, ⟨𝟙 V⟩⟩) (hS W)
      I := fun k => (hret k.1 k.2.1 k.2.2.1 k.2.2.2).choose
      fintypeI := fun k =>
        @Fintype.ofFinite _ (hret k.1 k.2.1 k.2.2.1 k.2.2.2).choose_spec.1
      decEqI := fun _ => Classical.decEq _
      retract := fun k => (hret k.1 k.2.1 k.2.2.1 k.2.2.2).choose_spec.2.some }

/-- **The per-object hypothesis of Stacks 0FNY produces a single family of objects covering the
final object on which `F` is a retract of a finite free sheaf of modules.** This is the passage
between the two forms of the local hypothesis, and the only step this file proves; everything
else in it is this step composed with an imported statement. -/
theorem exists_coversTop_retract_of_isLocallyDirectSummandOfFiniteFree
    (hF : IsLocallyDirectSummandOfFiniteFree 𝒪 h𝒪 F) :
    ∃ (K : Type (max u v)) (X : K → C) (_ : J.CoversTop X) (I : K → Type (max u v))
      (_ : ∀ k, Finite (I k)),
      ∀ k, Nonempty (Retract (F.over (X k))
        (free (R := (TensorSheafification.structureSheaf 𝒪 h𝒪).over (X k)) (I k))) :=
  let c := localFiniteFreeSummandCover 𝒪 h𝒪 F hF
  ⟨c.K, c.X, c.coversTop, c.I, fun k => @Finite.of_fintype _ (c.fintypeI k),
    fun k => ⟨c.retract k⟩⟩

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- **Stacks Project, Tag 0FNY, first assertion.** For a sheaf of modules which is locally a
direct summand of a finite free sheaf of modules, the canonical map
`F ⊗_𝒪 SheafHom(F, 𝒪) ⟶ SheafHom(F, F)` is an isomorphism.

The map is `Stacks.SheafOfModules.tensorDualToEndomorphism`, pinned down on local sections by
`Stacks.SheafOfModules.tensorDualToEndomorphism_toTensorSheafSection`. -/
@[stacks 0FNY "the map `ℱ ⊗ 𝓗om(ℱ,𝒪) ⟶ 𝓗om(ℱ,ℱ)` is an ISOMORPHISM, with the local hypothesis \
in the per-object form the tag states it in", sga "5 IIIB 5.0" "partial"]
theorem isIso_tensorDualToEndomorphism_of_localSummand
    (hF : IsLocallyDirectSummandOfFiniteFree 𝒪 h𝒪 F) :
    IsIso (tensorDualToEndomorphism 𝒪 h𝒪 F) := by
  set c := localFiniteFreeSummandCover 𝒪 h𝒪 F hF
  let := c.fintypeI
  let := c.decEqI
  exact isIso_tensorDualToEndomorphism 𝒪 h𝒪 c.coversTop
    fun k => FiniteDualBasis.ofRetract 𝒪 h𝒪 (c.retract k)

/-- **Stacks Project, Tag 0FNY, second assertion.** For a sheaf of modules `F` which is locally a
direct summand of a finite free sheaf of modules, the dual `F^∨ = SheafHom(F, 𝒪)`, with the
canonical coevaluation `η : 𝒪 ⟶ F ⊗ F^∨` and the canonical evaluation `ε : F^∨ ⊗ F ⟶ 𝒪`, is a
**left dual** of `F` in the monoidal category of sheaves of `𝒪`-modules of Tag 01CA. That is, the
two triangle identities hold. -/
@[stacks 0FNY "the LEFT-DUAL assertion: `𝓗om(ℱ,𝒪)` with the canonical coevaluation and \
evaluation satisfies the two triangle identities, with the local hypothesis in the per-object \
form the tag states it in", instance_reducible, sga "5 IIIB 5.0" "5.0.3 iso"]
noncomputable def exactPairingDualSheafOfLocalSummand
    (hF : IsLocallyDirectSummandOfFiniteFree 𝒪 h𝒪 F) :
    ExactPairing F (dualSheaf 𝒪 h𝒪 F) :=
  letI c := localFiniteFreeSummandCover 𝒪 h𝒪 F hF
  letI := c.fintypeI
  letI := c.decEqI
  exactPairingDualSheafOfRetract 𝒪 h𝒪 F c.coversTop c.retract

/-- `Stacks.SheafOfModules.exactPairingDualSheafOfLocalSummand` read as Mathlib's
`CategoryTheory.HasRightDual F`, which is Stacks' "`F^∨` is a left dual of `F`". -/
@[instance_reducible]
noncomputable def hasRightDualOfLocalSummand
    (hF : IsLocallyDirectSummandOfFiniteFree 𝒪 h𝒪 F) : HasRightDual F where
  rightDual := dualSheaf 𝒪 h𝒪 F
  exact := exactPairingDualSheafOfLocalSummand 𝒪 h𝒪 F hF

end Stacks.SheafOfModules

end
