module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedRelativeTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullback
public import StacksCore.Tactic.StacksAttribute

/-!
# Good right differential graded modules

Let `(C, O)` be a ringed site and let `A` be a sheaf of differential graded `O`-algebras on it.
A right differential graded `A`-module `P` is *good* when

1. the functor `N ↦ P ⊗_A N` is exact on the category of left graded `A`-modules,
2. `P ⊗_A N` is acyclic for every acyclic left differential graded `A`-module `N`, and
3. both properties hold for the pullback `f^* P`, as a differential graded `A'`-module, for
   every morphism of ringed sites `f`, every differential graded `O'`-algebra `A'` and every
   homomorphism `φ : f^{-1}A → A'`.

Condition (1) says that `P` is flat as a right graded `A`-module, condition (2) that it is
K-flat, and condition (3) that both hold after arbitrary base change.

**Tag 0FSA is not registered in this file.** Its condition (3) quantifies over morphisms of
ringed *topoi*, and the definition which does that is
`SheafOfModules.IsGoodToposBaseChange` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeDifferentialGradedModuleToposPullback.lean`,
where the tag sits. The two definitions below quantify condition (3) over a bare functor of the
two underlying categories together with a `PullbackData`; that is a different quantification,
incomparable with the source's, and they are auxiliary definitions serving the consumers already
stated against them.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.IsGood` is the predicate above with condition (3)
  read over a bare functor of the two underlying categories, using the relative tensor product
  of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedRelativeTensor.lean`.
* `SheafOfModules.DifferentialGradedModule.IsGoodCocontinuousBaseChange` is the same predicate
  with condition (3) quantified over those base changes whose pullback preserves the colimits of
  right differential graded modules.

## Main results

* `SheafOfModules.DifferentialGradedModule.IsGood.isGradedFlat`,
  `SheafOfModules.DifferentialGradedModule.IsGood.isKFlat` and
  `SheafOfModules.DifferentialGradedModule.IsGood.baseChange` expose the three conditions to
  consumers, and
  `SheafOfModules.DifferentialGradedModule.IsGoodCocontinuousBaseChange.isGradedFlat`,
  `isKFlat`, `baseChange` do the same for the second predicate.
* `SheafOfModules.DifferentialGradedModule.IsGood.isGoodCocontinuousBaseChange`: condition (3)
  of `IsGood` is the stronger quantification, so `IsGood` implies
  `IsGoodCocontinuousBaseChange`.

## Implementation notes

The relative tensor product is the constructed one: condition (1) is exactness of the functor
`N ↦ P ⊗_A N` built as the degreewise cokernel of the balance map, and condition (2) is
acyclicity of the cochain complex `P ⊗_A N` whose differential is constructed, not assumed. So
neither condition is vacuous.

Exactness in condition (1) is expressed degreewise, with the vanishing of the composite of the
two induced maps as part of the conclusion rather than a hypothesis; this is what "`P ⊗_A -`
carries a short exact sequence to a short exact sequence" amounts to without a prior abelian
structure on left graded modules.

The base change of condition (3) is a morphism of ringed sites in the sense of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPullback.lean`: a functor
`u : C ⥤ C'` in the direction opposite to `f` together with the structure map of its sheaves of
rings, and the semilinear homomorphism `φ : A ⟶ f_*A'` is the adjoint form of the source's
`φ : f^{-1}A → A'`; quantifying over every such homomorphism gives precisely the same base
changes. The pullback itself is quantified over as a `PullbackData`, which carries the pullback
of every module together with the universal property that determines it up to unique
isomorphism; this is how the pullback exists in this development, there being no construction
of `f^*M = f^{-1}M ⊗_{f^{-1}A} A'` available.

Condition (3) of `IsGood` puts no hypothesis on the functor `u` of the morphism of ringed sites,
and a pullback along an arbitrary `u` need not preserve colimits. The lemmas of the section — a
direct sum or a filtered colimit of good modules is good, two out of three of an admissible short
exact sequence are good — consume exactly that preservation, so
`IsGoodCocontinuousBaseChange` quantifies condition (3) over the pullbacks which preserve the
colimits that right differential graded modules have. Continuity of `u` is not assumed instead:
`CategoryTheory.Functor.IsContinuous` tests sheaves of types valued in one universe built from
all four universes of the two sites, which would tie them together and exclude base change to a
site in another universe. Preservation of colimits is a consequence of continuity, through the
adjunction between the pullback and the pushforward, and is universe-neutral.

Condition (3) as written quantifies over a bare functor `u` of the underlying categories
together with a `PullbackData`, and that is a *different* quantification from the source's, over
morphisms of ringed topoi, with neither containing the other. A functor with no continuity
hypothesis induces no morphism of topoi, and yet it can carry a `PullbackData`: the identity
functor of a site equipped with the trivial topology does, every presheaf being a sheaf there, so
`IsGood` has clauses the source's condition (3) does not — and for the free module of Tag 0FSG
the source's own argument is false at one of them, for which see the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeGradedModuleFlat.lean`. In the other
direction, a morphism of topoi need not be induced by any functor of the two given sites — only
by one of a site equivalent to the target (Tag 03CR, which is the first step of the source's own
proof of Tag 0FSB) — so `IsGood` also has no clause for such a base change.

The source's quantification is available in this development. `MorphismOfTopoi` of
`StacksFrontier/CategoryTheory/Sites/Topos/MorphismOfTopoi.lean` carries the inverse image `f⁻¹` as
data, for sheaves of any coefficients and with the two topoi at independent universes, and
`AlgebraicGeometry.RingedToposHom` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposHom.lean` is a morphism of ringed
topoi. What the source's proofs of Tags 0FSB and 0FSG use about the base change is exactly the
inverse image of a sheaf — of sets for 0FSG, of modules for 0FSB — which those data supply and
`(u, σ, PullbackData)` does not, `PullbackData` supplying the pullback of *modules* only.
Reading condition (3) over `RingedToposHom` is therefore both the faithful quantification and
the one at which the source's arguments run, and it is where Tag 0FSA is registered. `IsGood` is
not changed here, the chapter's consumers being stated against it.

What such a restatement would have to replace is not the quantifier but the *pullback*. A
`RingedToposHom` supplies `f^{-1}` and `f_*` for sheaves of sets and, through
`Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules` (Tags 03D6 and 03D7), for
sheaves of modules; it does not supply them for sheaves of differential graded modules, and the
pullback of this file's condition (3) is a `PullbackData`, keyed to a functor `u` of the two
underlying categories and expressing its universal property on sections over `u V`. The two
encodings meet at `SheafOfModules.DifferentialGradedModule.semilinearHomEquiv` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPushforward.lean`, which reads a
`φ`-semilinear map as a morphism into the direct image — and that carries `[u.IsContinuous J' J]`
and one single module universe for the two sites, because its direct image is restriction of
sections along `u`. So a faithful reading of condition (3) is not `IsGood` with its binders
rewritten: it needs the direct image of a sheaf of differential graded modules along a morphism
of topoi. That construction is available, as
`SheafOfModules.DifferentialGradedModule.toposPushforward` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedToposDirectImage.lean`, and so is
the faithful reading built on it: `SheafOfModules.IsGoodToposBaseChange` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeDifferentialGradedModuleToposPullback.lean`,
which carries Tag 0FSA and where `SheafOfModules.freeDGModule_isGoodToposBaseChange` is `A[S]`
at it and carries Tag 0FSG.
The reasons for this are recorded in items 6, 7 and 8 of the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeGradedModuleFlat.lean`, and the sheaf-of-sets
half of it is `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedSetsToposInverseImage.lean`.

**The restatement, applied.** `SheafOfModules.IsGoodToposBaseChange P` keeps conditions
(1) and (2) verbatim and quantifies condition (3) over

* a second ringed topos `Y : AlgebraicGeometry.RingedTopos.{v₁, u₁, m₁}` at its own three
  universes, carrying the four `GrothendieckTopology.HasSheafCompose` instances that
  `AlgebraicGeometry.RingedToposHom` needs;
* a morphism of ringed topoi `f` from `Y` to the ambient one — either
  `Stacks.Sheaves.RingedToposModules.RingedToposHom`, which is what the pushforward and pullback
  of sheaves of modules of Tags 03D6 and 03D7 are stated for, or
  `AlgebraicGeometry.RingedToposHom` passed through
  `AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom`; the two are equivalent data;
* a sheaf of differential graded algebras `A₁` on `Y`;
* a unital homomorphism `φ : A ⟶ f_*A₁` of sheaves of differential graded algebras, the adjoint
  form of the source's `φ : f^{-1}A → A₁`;
* nothing else: the pullback of `P` is not quantified but required to **exist**, as an object
  corepresenting `M ↦ (P ⟶ f_*M)`,

and concludes that it exists and that every object corepresenting that functor is flat as a
graded module and K-flat.

All five binders can be written. The target of `φ` is the direct image of a sheaf of differential
graded *algebras* along a morphism of ringed topoi,
`SheafOfModules.DifferentialGradedModule.toposPushforwardAlgebra`, and the pullback datum's
universal property is stated against the direct image of differential graded *modules*,
`toposPushforward`; both are built in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedToposDirectImage.lean` from a lax
monoidal additive direct image of ordinary sheaves of modules together with the comparison `ν` of
underlying sheaves of sets, and at a morphism of ringed topoi both of those data are
unconditional: `ν` is the identity
(`Stacks.Sheaves.RingedToposModules.toposPushforwardSetIso`) and the lax monoidal structure is
`Stacks.SheafOfModules.RingedToposPullback.pushforwardLaxMonoidal` at
`Stacks.SheafOfModules.RingedToposPullback.pullbackCoherence`, the coherence of Tag 03EL, proved
in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposPullbackCoherence.lean`.

`IsGoodToposBaseChange` is that reading, it carries Tag 0FSA, and it remains **incomparable**
with `IsGood`, for the reasons in the paragraph above: `IsGood` has clauses along functors that
induce no morphism of topoi, and no clause for a morphism of topoi not induced by a functor of
the two given sites. Neither direction is therefore provable, and no implication between the
two is stated anywhere in the library. What they share is conditions (1) and (2), verbatim.
`IsGood` is not changed here, the chapter's consumers being stated against it.

Lean cannot quantify over a universe, so the universes of the second ringed site and of its
module components are parameters of the definition rather than quantified inside it, as they are
in the surrounding differential graded files. The two sheaves of rings take values in one and
the same `RingCat.{t}`, which the structure map of a morphism of ringed sites forces.

The homogeneous pieces of the algebra and of the modules share one universe. This is forced by
the relative tensor product, whose summand `P^r ⊗_O A^s ⊗_O N^t` mixes all three; see the
implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedRelativeTensor.lean`.

## References

* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
* [Stacks Project, Tag 0FRU](https://stacks.math.columbia.edu/tag/0FRU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t m v u m₁ v₁ u₁

namespace SheafOfModules

namespace DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
  {Osharp : Sheaf J CommRingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)}

/-- An auxiliary variant of goodness: a right differential graded `A`-module is flat as a graded
module, K-flat, and stays so after every base change along a morphism of ringed sites and a
homomorphism of differential graded algebras.

Tag 0FSA itself is `SheafOfModules.IsGoodToposBaseChange` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeDifferentialGradedModuleToposPullback.lean`,
whose condition (3) runs over the source's own base changes, the morphisms of ringed topoi. This
definition quantifies a bare functor of the two underlying categories instead, and the two are
incomparable in the way recorded in the implementation notes below. -/
def IsGood (P : DifferentialGradedModule.{t, m, m} A) : Prop :=
  RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded P) ∧
    RelativeTensor.IsKFlat P ∧
      ∀ {C₁ : Type u₁} [Category.{v₁} C₁] {J₁ : GrothendieckTopology C₁}
        [J₁.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
        [J₁.WEqualsLocallyBijective AddCommGrpCat.{m₁}] [HasSheafify J₁ AddCommGrpCat.{m₁}]
        {Osharp₁ : Sheaf J₁ CommRingCat.{t}} (u : C ⥤ C₁)
        (σ : (toRingCat J Osharp).obj ⟶ u.op ⋙ (toRingCat J₁ Osharp₁).obj)
        (A₁ : DifferentialGradedAlgebra.{t, m₁} (toRingCat J₁ Osharp₁))
        (φ : DifferentialGradedAlgebra.SemilinearHom u σ A A₁)
        (PD : PullbackData.{t, m₁, m₁, v₁, u₁, m, m, v, u} φ),
        RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded (PD.obj P)) ∧
          RelativeTensor.IsKFlat (PD.obj P)

namespace IsGood

variable {P : DifferentialGradedModule.{t, m, m} A}

/-- The underlying graded module of a good differential graded module is flat. -/
theorem isGradedFlat (hP : IsGood.{t, m, v, u, m₁, v₁, u₁} P) :
    RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded P) :=
  hP.1

/-- A good differential graded module is K-flat. -/
theorem isKFlat (hP : IsGood.{t, m, v, u, m₁, v₁, u₁} P) : RelativeTensor.IsKFlat P :=
  hP.2.1

/-- Flatness and K-flatness of a good differential graded module persist after an arbitrary base
change. -/
theorem baseChange (hP : IsGood.{t, m, v, u, m₁, v₁, u₁} P) {C₁ : Type u₁} [Category.{v₁} C₁]
    {J₁ : GrothendieckTopology C₁} [J₁.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
    [J₁.WEqualsLocallyBijective AddCommGrpCat.{m₁}] [HasSheafify J₁ AddCommGrpCat.{m₁}]
    {Osharp₁ : Sheaf J₁ CommRingCat.{t}} (u : C ⥤ C₁)
    (σ : (toRingCat J Osharp).obj ⟶ u.op ⋙ (toRingCat J₁ Osharp₁).obj)
    (A₁ : DifferentialGradedAlgebra.{t, m₁} (toRingCat J₁ Osharp₁))
    (φ : DifferentialGradedAlgebra.SemilinearHom u σ A A₁)
    (PD : PullbackData.{t, m₁, m₁, v₁, u₁, m, m, v, u} φ) :
    RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded (PD.obj P)) ∧
      RelativeTensor.IsKFlat (PD.obj P) :=
  hP.2.2 u σ A₁ φ PD

end IsGood

/-- An auxiliary variant of goodness: a right differential graded `A`-module is flat as a graded
module, K-flat, and stays so after base change along every morphism of ringed sites, every
differential graded algebra and every homomorphism whose pullback preserves the colimits of
right differential graded modules.

This weakens the condition (3) of `IsGood` to the base changes the direct-sum and
filtered-colimit arguments of the section can use. Tag 0FSA itself is
`SheafOfModules.IsGoodToposBaseChange`, whose condition (3) runs over morphisms of ringed
topoi. -/
def IsGoodCocontinuousBaseChange (P : DifferentialGradedModule.{t, m, m} A) : Prop :=
  RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded P) ∧
    RelativeTensor.IsKFlat P ∧
      ∀ {C₁ : Type u₁} [Category.{v₁} C₁] {J₁ : GrothendieckTopology C₁}
        [J₁.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
        [J₁.WEqualsLocallyBijective AddCommGrpCat.{m₁}] [HasSheafify J₁ AddCommGrpCat.{m₁}]
        {Osharp₁ : Sheaf J₁ CommRingCat.{t}} (u : C ⥤ C₁)
        (σ : (toRingCat J Osharp).obj ⟶ u.op ⋙ (toRingCat J₁ Osharp₁).obj)
        (A₁ : DifferentialGradedAlgebra.{t, m₁} (toRingCat J₁ Osharp₁))
        (φ : DifferentialGradedAlgebra.SemilinearHom u σ A A₁)
        (PD : PullbackData.{t, m₁, m₁, v₁, u₁, m, m, v, u} φ),
        PreservesColimitsOfSize.{m, m} PD.functor →
        RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded (PD.obj P)) ∧
          RelativeTensor.IsKFlat (PD.obj P)

namespace IsGoodCocontinuousBaseChange

variable {P : DifferentialGradedModule.{t, m, m} A}

/-- The underlying graded module of a good differential graded module is flat. -/
theorem isGradedFlat (hP : IsGoodCocontinuousBaseChange.{t, m, v, u, m₁, v₁, u₁} P) :
    RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded P) :=
  hP.1

/-- A good differential graded module is K-flat. -/
theorem isKFlat (hP : IsGoodCocontinuousBaseChange.{t, m, v, u, m₁, v₁, u₁} P) :
    RelativeTensor.IsKFlat P :=
  hP.2.1

/-- Flatness and K-flatness of a good differential graded module persist after base change along
a pullback which preserves colimits. -/
theorem baseChange (hP : IsGoodCocontinuousBaseChange.{t, m, v, u, m₁, v₁, u₁} P)
    {C₁ : Type u₁} [Category.{v₁} C₁] {J₁ : GrothendieckTopology C₁}
    [J₁.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
    [J₁.WEqualsLocallyBijective AddCommGrpCat.{m₁}] [HasSheafify J₁ AddCommGrpCat.{m₁}]
    {Osharp₁ : Sheaf J₁ CommRingCat.{t}} (u : C ⥤ C₁)
    (σ : (toRingCat J Osharp).obj ⟶ u.op ⋙ (toRingCat J₁ Osharp₁).obj)
    (A₁ : DifferentialGradedAlgebra.{t, m₁} (toRingCat J₁ Osharp₁))
    (φ : DifferentialGradedAlgebra.SemilinearHom u σ A A₁)
    (PD : PullbackData.{t, m₁, m₁, v₁, u₁, m, m, v, u} φ)
    (hPD : PreservesColimitsOfSize.{m, m} PD.functor) :
    RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded (PD.obj P)) ∧
      RelativeTensor.IsKFlat (PD.obj P) :=
  hP.2.2 u σ A₁ φ PD hPD

end IsGoodCocontinuousBaseChange

/-- Condition (3) of `IsGood` concludes for every pullback, so it concludes in particular for the
pullbacks which preserve colimits: a good module in the sense of `IsGood` is good in the sense of
`IsGoodCocontinuousBaseChange`. -/
theorem IsGood.isGoodCocontinuousBaseChange {P : DifferentialGradedModule.{t, m, m} A}
    (hP : IsGood.{t, m, v, u, m₁, v₁, u₁} P) :
    IsGoodCocontinuousBaseChange.{t, m, v, u, m₁, v₁, u₁} P := by
  refine ⟨hP.isGradedFlat, hP.isKFlat, ?_⟩
  intro C₁ _ J₁ _ _ _ Osharp₁ u σ A₁ φ PD _
  exact hP.baseChange u σ A₁ φ PD

end DifferentialGradedModule

end SheafOfModules
