module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafGenerator
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafReductionQuasiIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafStalk
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Sheaf
public import StacksFrontier.Homology.Eta.Reduction

import StacksCore.Tactic.StacksAttribute
import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOnOpenDerived

/-!
# The stalks of the comparison of Tag 0GT9, and the algebraic input of Tag 0F7T

Let `(X, O_X)` be a ringed space, `ι : I ⟶ O_X` an invertible ideal subsheaf, and `F` a cochain
complex of `I`-torsion-free `O_X`-modules.  `EtaSheafReductionQuasiIso.lean` reduces
Tag 0GT9's quasi-isomorphism to the acyclicity of one complex and records that the acyclicity, and
equivalently the quasi-isomorphy of the comparison, may be checked on stalks.  This file supplies
everything the stalk route needs *except* the identification of the stalk of the comparison with
the algebraic comparison of Tag 0F7T: the generator of the stalk ideal, its regularity on the
stalk complex, Tag 0F7T consumed at that generator, and the passage between the two spellings of
the stalk of a complex of sheaves of modules.

## Main results

* `Stacks.IdealTorsion.Eta.isSMulRegular_stalk_of_generatesStalkIdeal` and
  `isSMulRegular_stalkComplex`: a generator of the stalk ideal `I_x` acts injectively on the stalk
  of an `I`-torsion-free module, and therefore on every term of the stalk complex of `F`.  This is
  clause (5) of Tag 0GT5 read in the spelling the décalage's stalk calculus uses.
* `exists_stalkGenerator`: at every point there is a generator of the stalk ideal and it is a
  nonzerodivisor of `O_{X,x}`.
* `quasiIso_stalk_etaTensorMod_to_bockstein`: **Tag 0F7T at a stalk of `X`** — the algebraic
  comparison `η_f F_x ⊗ O_{X,x}/f ⟶ H^•(F_x/f)` is a quasi-isomorphism.  This is the input the
  source's proof of Tag 0GT9 appeals to.
* `quasiIso_stalkFunctor_map_of_stalkComplexFunctor_map`: the two spellings of the stalk of a
  complex — the one over the `CommRingCat` stalk `O_{X,x}` that `Eta.stalkComplex` uses and the
  one over the `RingCat` stalk that `StacksFrontier/Topology/Sheaves/Modules/StalkAcyclic.lean` uses
  — have the same
  quasi-isomorphisms, restriction of scalars along the comparison of the two rings being an
  exact functor that reflects isomorphisms.
* `HasStalkModelComparison`: the stalkwise model identification, as a predicate — an
  identification of the stalk of `η_I F ⊗ O_X/I` with `η_f F_x ⊗ O_{X,x}/f` and of the stalk of
  the chain-level Bockstein complex with the algebraic one, compatibly with the two comparisons.
  Its first half is discharged in `EtaSheafReductionStalkModel.lean`, where
  `Reduction.HasStalkBocksteinComparison` is the residue; see the note at the end of this
  section.
* `quasiIso_reductionComparisonChainMap_of_hasStalkModelComparison` and
  `acyclic_reductionComparisonKernel_of_hasStalkModelComparison`: **granted that
  identification, Tag 0GT9's comparison is a quasi-isomorphism and the kernel complex of
  `EtaSheafReductionQuasiIso.lean` is acyclic.**

## Implementation notes

### Why the stalk route carries a hypothesis on the stalks of `O_X`

The statements of `EtaSheaf.lean`, `EtaSheafReduction.lean` and `EtaSheafReductionQuasiIso.lean`
assume only condition (2) of Tag 0GT3 — `I` invertible together with `Mono ι` — which is weaker
than Situation 0GT4's condition (1), local generation by a nonzerodivisor.  The source's proof of
Tag 0GT9 works with a *local generator* `f` of `I`, and over a general ringed space an invertible
module need not have free stalks (`Eta.isFiniteFreeStalkOfRank_one_of_isLocalRing` is where that
hypothesis enters, and the note before it records that the converse of Tag 0B8M fails over a
general ringed space), so no such `f` need exist at a point.  Exactly one statement below
therefore carries `[∀ z : X, IsLocalRing (X.presheaf.stalk z)]`: `exists_stalkGenerator`, the one
that *produces* a generator, the local-ring hypothesis being what makes the stalk of `I` free of
rank one.  `Eta.isFiniteFreeStalkOfRank_one_of_isLocallyGeneratedByRegular` is the alternative
input, available under Situation 0GT4's own condition (1).  That the source's own argument needs
this, and so does not reach the general invertible case, is recorded here rather than hidden.

Everything that merely *consumes* a generator stands without it.  In particular
`Stacks.IdealTorsion.Eta.isSMulRegular_stalk_of_generatesStalkIdeal`, `isSMulRegular_stalkComplex`
and `quasiIso_stalk_etaTensorMod_to_bockstein` do not carry it, although they used to: regularity
of a given generator on the stalk of an `I`-torsion-free module is
`Eta.isSMulRegular_stalk_of_generatesStalkIdeal`, proved inside `EtaSheaf.lean` from the monomorphy
of the first ideal-power inclusion and the fact that its stalk is `f` times an isomorphism, with no
hypothesis on the stalks of `O_X` at all.  The route through the stalkwise clause of Tag 0GT5
needed the freeness, and that is where the hypothesis came from.

The two conclusions about Tag 0GT9 itself,
`quasiIso_reductionComparisonChainMap_of_hasStalkModelComparison` and
`acyclic_reductionComparisonKernel_of_hasStalkModelComparison`, do *not* carry it: the generator
and its regularity sit inside the existential of `HasStalkModelComparison`, so those two
statements stand in the generality of `EtaSheafReductionQuasiIso.lean`.

### The two spellings of a stalk

`Eta.stalkComplex` takes stalks over the `CommRingCat` stalk `ringStalk X x`, because
`EtaComplex` is a development about modules over a commutative ring, while
`AlgebraicGeometry.SheafOfModules.quasiIso_iff_forall_stalk_quasiIso` of
`StacksFrontier/Topology/Sheaves/Modules/StalkAcyclic.lean` speaks about the `RingCat`-valued stalk
functor.  The first is the second
followed by `ModuleCat.restrictScalars` along `SemilinearStalk.commStalkIso`, so the passage is
Mathlib's `HomologicalComplex.quasiIso_map_iff_of_preservesHomology`: restriction of scalars
along a ring map is additive and reflects isomorphisms by global instances, and preserving
homology is `preservesHomology_restrictScalars` below.  No transport is needed, because
`(G ⋙ H).mapHomologicalComplex c` and the composite of the two `mapHomologicalComplex`es agree
by `rfl`.

Two seams made this three lines rather than one.  Mathlib's exactness instances for
`ModuleCat.restrictScalars` are stated for *commutative* rings, and the `RingCat`-valued stalk
is not known to be one, so exactness is reproved here from
`ShortComplex.ShortExact.moduleCat_exact_iff_function_exact`; and applying
`quasiIso_map_iff_of_preservesHomology` to the stalk functor directly runs out of heartbeats at
`whnf`, so the cancellation is stated once with every category, functor and complex a variable
and applied by `exact`.

### The module-spelling seam

`Tag 0GT5`'s stalkwise clause is stated for `grpStalk`, the stalk of the stalk calculus of
Tag 01CB, while the décalage's stalk complex is built from `stalkModuleFunctor`.  The two have
the same underlying group and the same `O_{X,x}`-action, by
`Eta.stalkModuleLinearEquiv`, whose underlying map is the identity; regularity of a scalar is
transported along it rather than along a rewrite, since the two module instances are equal but
not syntactically so.

### Why nothing here carries the attribute

Everything here is a step of the *proof* of Tag 0GT9, not a clause of its statement, so no
declaration below carries `@[stacks 0GT9]`.  The tag's own conclusion is proved in Situation
0GT4 in `EtaSheafReductionDerivedIsoRegular.lean`, as
`Reduction.isIso_reductionComparisonQ_of_isLocallyGeneratedByRegular` and
`Reduction.reductionComparisonQIsoOfRegular`.

`HasStalkModelComparison` names the source's step "on stalks this construction matches the maps
built in More on Algebra, Lemma 15.97.6": the two model isomorphisms at each stalk, compatibly
with the comparisons.  It is not vacuous — it demands isomorphisms rather than mere morphisms,
so no zero map inhabits it — and it is proved rather than assumed, in Situation 0GT4, by
`Reduction.hasStalkBocksteinSquare_of_isLocallyGeneratedByRegular` composed with
`Reduction.hasStalkBocksteinComparison_of_hasStalkBocksteinSquare` and
`Reduction.hasStalkModelComparison_of_hasStalkBocksteinComparison`.

Its two halves are proved separately.  `EtaSheafReductionStalkModel.lean` proves
`Reduction.etaModIdealStalkIso`, the identification of the stalk of `η_I F ⊗ O_X/I` with the
algebraic model, from Tag 0GT6's `Eta.etaStalkIso` and the exactness of the stalk functor; the
Bockstein half and the square are isolated there as
`Reduction.HasStalkBocksteinComparison`, from which it rederives both conclusions below, and
`EtaSheafBocksteinStalk.lean` proves the square as
`Reduction.map_reductionComparison_comp_bocksteinChainStalkTermIso`.

## References

* [Stacks Project, Tag 0GT9](https://stacks.math.columbia.edu/tag/0GT9)
* [Stacks Project, Tag 0F7T](https://stacks.math.columbia.edu/tag/0F7T)
* [Stacks Project, Tag 0GT5](https://stacks.math.columbia.edu/tag/0GT5)
* [Stacks Project, Tag 0GT6](https://stacks.math.columbia.edu/tag/0GT6)
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk grpStalk)

universe u

namespace Stacks.IdealTorsion.Reduction

open Stacks.IdealTorsion.Eta

variable (X : RingedSpace.{u, u})

local notation "Oₓ" => (Stacks.SheafOfModules.Tensor.ringSheaf
  (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf))
local notation "𝒪" => SheafOfModules.unit Oₓ

/-! ### The two spellings of the stalk of a complex -/

/-- The stalk functor over `O_{X,x}` preserves zero morphisms: it is the additive stalk functor
followed by restriction of scalars.  Stated as a theorem and passed explicitly, because the
category in the middle of the composite carries two spellings of the same `RingCat` stalk. -/
public theorem stalkModuleFunctor_preservesZeroMorphisms (x : X) :
    (stalkModuleFunctor X x).PreservesZeroMorphisms :=
  ⟨fun Y Z => by
    change (ModuleCat.restrictScalars (SemilinearStalk.commStalkIso X.presheaf x).inv.hom).map
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor Oₓ x).map (0 : Y ⟶ Z)) = 0
    rw [Functor.map_zero]
    rfl⟩

/-- The degreewise stalk of a complex of sheaves of modules, over the commutative local ring
`O_{X,x}`, as a functor.  On objects it is `Eta.stalkComplex`. -/
public noncomputable abbrev stalkComplexFunctor (x : X) :
    CochainComplex (SheafOfModules.{u} Oₓ) ℤ ⥤
      CochainComplex (ModuleCat.{u} (ringStalk X x)) ℤ :=
  @Functor.mapHomologicalComplex _ _ _ _ _ _ _ (stalkModuleFunctor X x)
    (stalkModuleFunctor_preservesZeroMorphisms X x) (ComplexShape.up ℤ)

/-- On objects `stalkComplexFunctor` is `Eta.stalkComplex`. -/
public theorem stalkComplexFunctor_obj (x : X)
    (K : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) :
    (stalkComplexFunctor X x).obj K = stalkComplex X x K := rfl

/-- Restriction of scalars along a ring map preserves homology, being exact.

Not available by synthesis: Mathlib's `PreservesFiniteLimits` and `PreservesFiniteColimits`
instances for `ModuleCat.restrictScalars` are stated for commutative rings, which the
`RingCat`-valued stalk is not known to be, and the older adjunction route needs the module
universe to be `max u v` rather than the diagonal `u` used here. -/
private theorem preservesHomology_restrictScalars {R S : Type u} [Ring R] [Ring S]
    (φ : R →+* S) : (ModuleCat.restrictScalars.{u} φ).PreservesHomology :=
  ((Functor.exact_tfae (ModuleCat.restrictScalars.{u} φ)).out 2 3).mp
    (Stacks.Cohomology.ModuleComparison.restrictScalars_map_exact φ)

/-- **A functor that reflects isomorphisms and preserves homology may be cancelled from the
right of a degreewise-applied composite.**  Everything is a variable, so that the single
`isDefEq` the application performs is the unfolding of the composite functor and not a descent
into the stalk functor; applied to the stalk functor directly, Mathlib's
`HomologicalComplex.quasiIso_map_iff_of_preservesHomology` runs out of heartbeats at `whnf`. -/
private theorem quasiIso_mapHomologicalComplex_of_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    [CategoryWithHomology D] [CategoryWithHomology E]
    (H : C ⥤ D) [H.Additive] (R : D ⥤ E) [hRa : R.Additive] [hRh : R.PreservesHomology]
    [hRr : R.ReflectsIsomorphisms]
    {K L : CochainComplex C ℤ} (g : K ⟶ L)
    (h : QuasiIso (((H ⋙ R).mapHomologicalComplex (ComplexShape.up ℤ)).map g)) :
    QuasiIso ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map g) :=
  (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map g) R).1 h

/-- **The stalk over `O_{X,x}` detects quasi-isomorphy of the stalk over the `RingCat` stalk.**
The first complex is the second with its scalars restricted along the comparison of the two
spellings of the stalk of the structure sheaf, and restriction of scalars along a ring map is
additive, exact and reflects isomorphisms, so it neither creates nor destroys
quasi-isomorphisms. -/
public theorem quasiIso_stalkFunctor_map_of_stalkComplexFunctor_map (x : X)
    {K L : CochainComplex (SheafOfModules.{u} Oₓ) ℤ} (g : K ⟶ L)
    (h : QuasiIso ((stalkComplexFunctor X x).map g)) :
    QuasiIso (((AlgebraicGeometry.SheafOfModules.stalkFunctor Oₓ x).mapHomologicalComplex
      (ComplexShape.up ℤ)).map g) := by
  exact quasiIso_mapHomologicalComplex_of_comp
    (AlgebraicGeometry.SheafOfModules.stalkFunctor Oₓ x)
    (ModuleCat.restrictScalars.{u} (SemilinearStalk.commStalkIso X.presheaf x).inv.hom)
    (hRa := by exact (inferInstance : (ModuleCat.restrictScalars.{u}
      (SemilinearStalk.commStalkIso X.presheaf x).inv.hom).Additive))
    (hRh := by exact (preservesHomology_restrictScalars
      (SemilinearStalk.commStalkIso X.presheaf x).inv.hom))
    (hRr := by exact (inferInstance : (ModuleCat.restrictScalars.{u}
      (SemilinearStalk.commStalkIso X.presheaf x).inv.hom).ReflectsIsomorphisms)) g h

/-! ### The generator of the stalk ideal and its regularity -/

/-- **A generator of the stalk ideal is regular on every term of the stalk complex.**  This is
the hypothesis `hM` of Tag 0F7T at the stalk complex of a termwise `I`-torsion-free complex. -/
public theorem isSMulRegular_stalkComplex
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (x : X) (f : ringStalk X x) (hf : GeneratesStalkIdeal X ι x f) (k : ℤ) :
    IsSMulRegular ((stalkComplex X x F).X k) f :=
  Stacks.IdealTorsion.Eta.isSMulRegular_stalk_of_generatesStalkIdeal X I ι (F.X k) (hF k) x f hf

/-- **At every point the stalk ideal has a generator, and it is a nonzerodivisor.**  The stalk
of an invertible sheaf on a space with local stalks is free of rank one, and a trivialization of
it produces the generator.  This is clause (5) of Tag 0GT5 read at `x`. -/
public theorem exists_stalkGenerator
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    [∀ z : X, IsLocalRing (X.presheaf.stalk z)] (x : X) :
    ∃ f : ringStalk X x,
      GeneratesStalkIdeal X ι x f ∧ f ∈ nonZeroDivisors (ringStalk X x) :=
  exists_generatesStalkIdeal_mem_nonZeroDivisors X I ι x
    (nonempty_ideal_stalk_linearEquiv X I x
      (isFiniteFreeStalkOfRank_one_of_isLocalRing X I x)).some

/-! ### Tag 0F7T at a stalk -/

/-- **Tag 0F7T at a stalk of `X`.**  At a generator `f` of the stalk ideal `I_x`, which is a
nonzerodivisor of `O_{X,x}`, the algebraic comparison from `η_f F_x ⊗ O_{X,x}/f` to the
Bockstein complex of `F_x/f` is a quasi-isomorphism.

This is the statement the source's proof of Tag 0GT9 appeals to on stalks; what is still needed
to use it is the identification of the stalk of the sheaf-level comparison with this map. -/
public theorem quasiIso_stalk_etaTensorMod_to_bockstein
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (x : X) (f : ringStalk X x) (hgen : GeneratesStalkIdeal X ι x f)
    (hf : f ∈ nonZeroDivisors (ringStalk X x)) :
    QuasiIso
      ((Stacks.EtaComplex.ModNonzerodivisor.etaTensorQuotientIso f hf (stalkComplex X x F)
          (isSMulRegular_stalkComplex X I ι F hF x f hgen)).hom ≫
        Stacks.EtaComplex.ModNonzerodivisor.etaQuotientToBockstein f hf (stalkComplex X x F)
          (isSMulRegular_stalkComplex X I ι F hF x f hgen)) :=
  Stacks.EtaComplex.ModNonzerodivisor.etaTensorMod_to_bockstein_quasiIso f hf
    (stalkComplex X x F) (isSMulRegular_stalkComplex X I ι F hF x f hgen)

/-! ### Tag 0GT9 modulo the two model isomorphisms -/

/-- **The stalkwise model identification used by the proof of Tag 0GT9.**  At every
point `x` of `X` there are a generator `f` of the stalk ideal `I_x` which is a nonzerodivisor of
`O_{X,x}` and regular on every term of the stalk complex, an isomorphism `α` of the stalk of the
reduced décalage `η_I F ⊗ O_X/I` with the algebraic `η_f F_x ⊗ O_{X,x}/f`, and an isomorphism `β`
of the stalk of the chain-level Bockstein complex with the algebraic Bockstein complex of
`F_x/f`, such that `α` and `β` carry the stalk of the comparison of Tag 0GT9 to the algebraic
comparison of Tag 0F7T.

This is the source's last step — "on stalks this construction matches the maps built in More on
Algebra, Lemma 15.97.6".  It is a named predicate because the two statements below both consume
it.  It holds in Situation 0GT4, by
`hasStalkModelComparison_of_hasStalkBocksteinComparison` applied to
`hasStalkBocksteinComparison_of_hasStalkBocksteinSquare` and
`hasStalkBocksteinSquare_of_isLocallyGeneratedByRegular`.

The first four data are not themselves the obligation: on a space whose structure-sheaf stalks
are local rings `exists_stalkGenerator` supplies `f` together with the proof that it is a
nonzerodivisor, and `isSMulRegular_stalkComplex` supplies its regularity, so what is owed there
is exactly the pair `α`, `β` and the square.  They are existentially quantified here all the
same, so that the two statements below hold in the full generality of
`EtaSheafReductionQuasiIso.lean` — condition (2) of Tag 0GT3 alone — rather than only on a space
with local stalks.

Nothing here is inhabited vacuously: `α` and `β` are isomorphisms, not bare morphisms, so no
zero map satisfies the square, and the predicate is satisfied by the model isomorphisms the
source constructs. -/
public def HasStalkModelComparison
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k)) : Prop :=
  ∀ x : X, ∃ (f : ringStalk X x) (_ : GeneratesStalkIdeal X ι x f)
      (hf : f ∈ nonZeroDivisors (ringStalk X x))
      (hreg : ∀ k : ℤ, IsSMulRegular ((stalkComplex X x F).X k) f)
      (α : (stalkComplexFunctor X x).obj (etaModIdealComplex X I ι F hF) ≅
            Stacks.EtaComplex.ModNonzerodivisor.etaTensorMod f (stalkComplex X x F))
      (β : (stalkComplexFunctor X x).obj (bocksteinChainComplex X I ι F hF) ≅
            EtaPow.Bockstein.bocksteinComplex f hf (stalkComplex X x F) hreg),
      (stalkComplexFunctor X x).map (reductionComparisonChainMap X I ι F hF) ≫ β.hom =
        α.hom ≫
          (Stacks.EtaComplex.ModNonzerodivisor.etaTensorQuotientIso f hf
              (stalkComplex X x F) hreg).hom ≫
            Stacks.EtaComplex.ModNonzerodivisor.etaQuotientToBockstein f hf
              (stalkComplex X x F) hreg

/-- **Tag 0GT9's quasi-isomorphism from the stalkwise model identification.**  From
`HasStalkModelComparison`, the comparison of Tag 0GT9 is a quasi-isomorphism, hence an
isomorphism in `D(O_X)` on a termwise `I`-torsion-free representative.

Everything else in the source's proof is discharged here: the stalk criterion of Tag 08TL
through `Reduction.quasiIso_reductionComparisonChainMap_of_forall_stalk_quasiIso`, the passage
between the two spellings of a stalk, and Tag 0F7T itself.  `HasStalkModelComparison` is itself
proved in Situation 0GT4, so the form of this conclusion with no hypothesis beyond the situation
is `Reduction.quasiIso_reductionComparisonChainMap_of_isLocallyGeneratedByRegular` in
`EtaSheafReductionDerivedIsoRegular.lean`.  The attribute sits there rather than here because
this declaration's hypothesis is a step of the source's proof, not a clause of the tag. -/
public theorem quasiIso_reductionComparisonChainMap_of_hasStalkModelComparison
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (hmodel : HasStalkModelComparison X I ι F hF) :
    QuasiIso (reductionComparisonChainMap X I ι F hF) := by
  refine quasiIso_reductionComparisonChainMap_of_forall_stalk_quasiIso X I ι F hF fun x => ?_
  obtain ⟨f, -, hf, hreg, α, β, hsq⟩ := hmodel x
  refine quasiIso_stalkFunctor_map_of_stalkComplexFunctor_map X x
    (reductionComparisonChainMap X I ι F hF) ?_
  have hfac : (stalkComplexFunctor X x).map (reductionComparisonChainMap X I ι F hF) =
      (α.hom ≫
        ((Stacks.EtaComplex.ModNonzerodivisor.etaTensorQuotientIso f hf
            (stalkComplex X x F) hreg).hom ≫
          Stacks.EtaComplex.ModNonzerodivisor.etaQuotientToBockstein f hf
            (stalkComplex X x F) hreg)) ≫ β.inv := by
    rw [← hsq, Category.assoc, β.hom_inv_id, Category.comp_id]
  rw [hfac]
  have := Stacks.EtaComplex.ModNonzerodivisor.etaTensorMod_to_bockstein_quasiIso f hf
    (stalkComplex X x F) hreg
  exact quasiIso_comp _ _

/-- **The acyclicity of Tag 0GT9's kernel complex, from the stalkwise model identification.**
`EtaSheafReductionQuasiIso.lean`'s chain-level form of the tag: the kernel complex of
the comparison is acyclic.  It is
`Reduction.acyclic_reductionComparisonKernel_of_quasiIso` applied to
`quasiIso_reductionComparisonChainMap_of_hasStalkModelComparison`. -/
public theorem acyclic_reductionComparisonKernel_of_hasStalkModelComparison
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (hmodel : HasStalkModelComparison X I ι F hF) :
    (reductionComparisonKernel X I ι F hF).Acyclic :=
  acyclic_reductionComparisonKernel_of_quasiIso X I ι F hF
    (quasiIso_reductionComparisonChainMap_of_hasStalkModelComparison X I ι F hF hmodel)

end Stacks.IdealTorsion.Reduction

end
