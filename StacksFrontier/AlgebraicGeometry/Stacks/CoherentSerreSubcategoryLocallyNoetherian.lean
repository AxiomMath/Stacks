module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalPresentationOfPresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherenceConditions

/-!
# Coherent modules as a Serre subcategory of the quasi-coherent modules (Stacks 0GRB)

Let `𝒳` be a locally Noetherian algebraic stack.  Stacks 0GRB makes four assertions: that
`Coh(𝒪_𝒳)` is a Serre subcategory of `QCoh(𝒪_𝒳)`, and, for a map `φ : ℱ ⟶ 𝒢` of quasi-coherent
`𝒪_𝒳`-modules,

1. if `ℱ` is coherent and `φ` is surjective then `𝒢` is coherent;
2. if `ℱ` is coherent then `Im(φ)` is coherent;
3. if `𝒢` is coherent and `Ker(φ)` is parasitic then `ℱ` is coherent.

**Part (1) is proved here with no hypothesis beyond the source's.**  Part (2) is proved here up
to quasi-coherence of the image, which this library does not have; the Serre-subcategory
assertion and part (3) are not proved, and the obstruction common to both is recorded below.

## Main results

* `AlgebraicGeometry.Stack.isQuasicoherentFiniteTypeModule_of_epi`: **Stacks 0GRB, part (1).**
* `AlgebraicGeometry.Stack.isFiniteTypeOnSite_image`: the finite-type half of
  **Stacks 0GRB, part (2)**, with no extra hypothesis.
* `AlgebraicGeometry.Stack.isQuasicoherentFiniteTypeModule_image`: **Stacks 0GRB, part (2)**,
  over quasi-coherence of the image.

## Implementation notes

**Which reading of "coherent" is used.**  Stacks 0GR6 calls an `𝒪_𝒳`-module coherent when it
satisfies the four equivalent conditions of Stacks 0GR5.  The condition used here is
Stacks 0GR5(1), that the module be quasi-coherent and of finite type, which is
`AlgebraicGeometry.Stack.IsQuasicoherentFiniteTypeModule`.  It is the condition in which the
assertions of Stacks 0GRB about surjections are *statements about finite type alone*: the target
of a surjection out of a quasi-coherent module is quasi-coherent by the hypothesis of the source,
which takes `φ` to be a map of quasi-coherent modules, and what has to be proved is that it is of
finite type.  Finite type on a site passes to quotients over an arbitrary ringed site, so part (1)
costs no Noetherianity at all.

This is a different predicate from `AlgebraicGeometry.Stack.IsCoherentModule`, the reading of
Stacks 0GR5(2) — finite presentation on the fppf site — that Stacks 0GR7 and 0GR8 are stated for
in `StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian`, and from
`SheafOfModules.IsCoherentOnSite`, the reading of Stacks 03DL(8) that Stacks 0GRA is stated for
in `StacksFrontier.AlgebraicGeometry.Stacks.CoherentExtensionLocallyNoetherian`.  The three readings
are not compared in this library: of the equivalences of Stacks 0GR5 only the implication
(2) ⟹ (1) is available, at
`AlgebraicGeometry.Stack.isQuasicoherentFiniteTypeModule_of_isFinitePresentationOnSite`.  That
is what forces the choice of reading here.  Condition (1) is inherited by quotients over an
arbitrary ringed site, while condition (2) is not — a quotient of a finitely presented module by
a submodule which is not of finite type is of finite type and not of finite presentation — so,
with the equivalence of the two unavailable, part (1) of Stacks 0GRB is a theorem for the
reading 0GR5(1) and is out of reach for the reading 0GR5(2), whose proof in the source passes
through conditions (3) and (4).

**Local Noetherianity is a hypothesis of every statement here and is used by none of them.**
That is the situation of the whole family of files around Stacks 0GR5: finite type on a site is
inherited by quotients over an arbitrary ringed site.  It is kept because the source has it, and
because it is what makes "coherent" well defined there.

**Part (2): the image, and what is missing.**  The image of `φ` is taken in `Mod(𝒪_𝒳)`, as
Stacks 0GR9 prescribes.  Its finite-type half is part (1) applied to
`CategoryTheory.Limits.factorThruImage φ`, which is an epimorphism, and needs nothing further.
Its quasi-coherence is Stacks 06WV, parts (3) and (7) — the inclusion
`QCoh(𝒪_𝒳) ⟶ Mod(𝒪_𝒳)` is right exact but not exact, so quasi-coherence of a subobject of a
quasi-coherent module is a theorem and not a formality — and those parts of Stacks 06WV are not
in this library: what carries its tag is the tensor-product clause (5), in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentTensor` and
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.MixedTensorQuasicoherent`, and the
right-exactness half of clause (3), in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineSectionBaseChangeExit`,
which gives that cokernels agree and not that a subobject of a quasi-coherent module is
quasi-coherent.  Quasi-coherence of the image is therefore carried as the hypothesis `hIm` of
`AlgebraicGeometry.Stack.isQuasicoherentFiniteTypeModule_image`, which is accordingly **not**
tagged; the unconditional `AlgebraicGeometry.Stack.isFiniteTypeOnSite_image` is not tagged either,
being only half of the assertion.  Note that `SheafOfModules.IsQuasicoherentOnSite`, the
condition of Stacks 03DL(6), is *not* inherited by quotients: a global presentation of a quotient
needs generators of the submodule divided out, which is exactly what is unavailable.

**The Serre-subcategory assertion and part (3) are not proved, and the obstruction is the same
for both.**  A Serre subcategory, `CategoryTheory.ObjectProperty.IsSerreClass`, is closed under
subobjects, quotients and extensions.  The quotient clause is part (1).  The subobject clause is
the assertion that a quasi-coherent submodule of a coherent module is coherent, and part (3) is
that assertion in the form the source states it, `Ker(φ)` parasitic making `φ` a monomorphism in
`QCoh(𝒪_𝒳)` by Stacks 0779 (1).  That assertion is *false* without local Noetherianity — over the
spectrum of a non-discrete valuation ring of rank one the maximal ideal is a quasi-coherent
submodule of the coherent structure sheaf and is not of finite type, the counterexample recorded
in `StacksFrontier.AlgebraicGeometry.Spaces.CoherentSubquotientNoetherian` — so proving it requires
putting local Noetherianity of `𝒳` to work, and the source does that by restricting along a
smooth surjective chart and quoting the case of algebraic spaces, Stacks 07UD.

Contrary to what the implementation notes of
`StacksFrontier.AlgebraicGeometry.Stacks.CoherenceConditions` say, the functor that conditions (3)
and (4) are phrased with does exist in this library:
`AlgebraicGeometry.Space.etaleRestrictedModuleInverseImage` is `ℱ ↦ f^*ℱ|_{U_étale}` for a
1-morphism `f : 𝒰 ⥤ 𝒳` out of a category fibred in groupoids representable by an algebraic
space, so conditions (3) and (4) *can* be stated.  What blocks the route is not the functor but
three things it does not come with.  **Stacks 0GQC**, that the restriction of a quasi-coherent
module is quasi-coherent, is available only for the identity 1-morphism and only over carried
hypotheses encoding the identification Stacks 0GQA calls clear, and in the functorial
formulation of equation 075K it appears as the explicitly undischarged
`AlgebraicGeometry.Space.RestrictionPreservesQuasicoherent`, which nothing in this library
discharges; Stacks 07UD needs it, its submodule clause being about a *quasi-coherent* submodule
and so having quasi-coherence of the restricted submodule among its inputs.  No exactness
property of the restriction is proved — not left exactness, not preservation of monomorphisms or
of epimorphisms — and cocontinuity of the chart functor, through which preservation of
epimorphisms would come, is proved for the chart functor of Stacks 073M alone and not for the
composite with `f`.  And nothing connects the restriction to parasitic modules, which is what
part (3) needs on top of the subobject clause; Stacks 0774 (1), at
`AlgebraicGeometry.Stack.isParasitic_modulePresheafPullbackOfHom`, kills parasitic modules along
a flat 1-morphism of stacks, but its composite with the restriction to the small étale site is
not available.  A fourth gap is one of universes: that restriction takes modules with sections in
the universe `u` of the schemes, and so does Stacks 07UD, while the fppf-site readings of
coherence need the sections in a universe `m` with `UnivLE.{u + 1, m}`, as the paragraph below
explains.  What the route does *not* need is any further Noetherian input on the chart: local
Noetherianity of a chart locally of finite type over a locally Noetherian stack is
`AlgebraicGeometry.Stack.hasEtaleLocalProperty_isLocallyNoetherian_of_chart`, which is exactly
the `Fact` instance Stacks 07UD asks for.  Nothing weaker is offered in place of the two
assertions, and no reduction over Stacks 0GQC is stated here.

Stacks 0GR9 is **not** a lever for either.  Its formalization,
`StacksFrontier.AlgebraicGeometry.Stacks.CoherentKernelCokernelLocallyNoetherian`, reads coherence
as Stacks 03DL(8) and derives every clause from Stacks 01BY over an arbitrary ringed site, with
local Noetherianity bound to an unused binder; a Noetherian-free theorem cannot supply an input
to an assertion that is false without Noetherianity.  Its clauses also assume *both* modules
coherent, where Stacks 0GRB assumes only `ℱ` coherent and `𝒢` quasi-coherent, so they do not
discharge `hIm` either.

**The module universe, and the plumbing that it forces.**  The big fppf site of an algebraic
stack has its objects in `Type (u + 1)` and its morphisms in `Type u`, while its structure sheaf
takes values in `RingCat.{u}`; so the sheafification instances that make `Mod(𝒪_𝒳)` abelian need
the module sections in a universe `m` with `UnivLE.{u + 1, m}`, and the module universe cannot be
the universe of the coefficient rings.  `Stacks.SheafOfModules.isFiniteTypeOnSite_of_epi` ties
the two together, so the four primed lemmas below re-run its proof — unchanged except for the
universes — with the module universe independent of the ring universe.  They belong in
`StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteEpi`, beside the statements they
generalize, and carry that file's namespace `Stacks.SheafOfModules` so that they can be moved
there without renaming.

## References

* [Stacks Project, Tag 0GRB](https://stacks.math.columbia.edu/tag/0GRB)
* [Stacks Project, Tag 0GR5](https://stacks.math.columbia.edu/tag/0GR5)
* [Stacks Project, Tag 0GR6](https://stacks.math.columbia.edu/tag/0GR6)
* [Stacks Project, Tag 0GR9](https://stacks.math.columbia.edu/tag/0GR9)
* [Stacks Project, Tag 0GQC](https://stacks.math.columbia.edu/tag/0GQC)
* [Stacks Project, Tag 0774](https://stacks.math.columbia.edu/tag/0774)
* [Stacks Project, Equation 075K](https://stacks.math.columbia.edu/tag/075K)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 07UD](https://stacks.math.columbia.edu/tag/07UD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

universe u t m uC vC r

namespace Stacks.SheafOfModules

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- **Local surjectivity of a morphism of sheaves of modules is inherited by its restriction to
a slice of the site**, with the universe of the module sections independent of the universe of
the coefficient rings.  This is
`Stacks.SheafOfModules.isLocallySurjective_over`, whose proof applies verbatim: the forgetful
functor of the slice is cocontinuous, and local surjectivity is preserved by whiskering along a
cocontinuous functor. -/
theorem isLocallySurjective_over' {M N : SheafOfModules.{m} R} (q : M ⟶ N)
    [Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map q)] (U : C) :
    Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf (R.over U)).map (q.over U)) := by
  let _ : (Over.forget U).IsCocontinuous (J.over U) J :=
    ⟨fun hS => J.overEquiv_symm_mem_over _ _ hS⟩
  exact Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U)
    ((SheafOfModules.toSheaf R).map q).hom

/-- **The restriction of an epimorphism of sheaves of modules to a slice of the site is an
epimorphism**, with the universe of the module sections independent of the universe of the
coefficient rings.  This is `Stacks.SheafOfModules.epi_over`: an epimorphism is a local
surjection, local surjectivity restricts to the slice, and a local surjection is an
epimorphism. -/
theorem epi_over' [HasSheafify J AddCommGrpCat.{m}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    {M N : SheafOfModules.{m} R} (q : M ⟶ N) [Epi q] (U : C) : Epi (q.over U) := by
  have : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map q) :=
    Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi q
  exact Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective (q.over U)
    (isLocallySurjective_over' q U)

/-- **Generation by finitely many global sections passes to a quotient**, with the universe of
the module sections independent of the universe of the coefficient rings.  This is
`Stacks.SheafOfModules.hasFiniteGlobalGenerators_of_epi`: compose the epimorphism from the
finite coproduct presenting the source with the given one, the universe of the sections being
raised by a functor which preserves colimits and therefore epimorphisms. -/
theorem hasFiniteGlobalGenerators_of_epi'
    [HasWeakSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasWeakSheafify J AddCommGrpCat.{max uC vC r m}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r m}]
    {M N : SheafOfModules.{m} R} (q : M ⟶ N) [Epi q]
    (hM : M.HasFiniteGlobalGenerators) : N.HasFiniteGlobalGenerators := by
  have : PreservesColimitsOfSize.{0, 0}
      (uliftForPresentationFunctor.{uC, vC, r, m, max uC vC r} (R := R)) :=
    have := uliftForPresentationFunctor_preservesColimits.{uC, vC, r, m, max uC vC r} (R := R)
    preservesColimitsOfSize_shrink _
  have hu : Epi ((uliftForPresentationFunctor.{uC, vC, r, m, max uC vC r} (R := R)).map q) :=
    inferInstance
  obtain ⟨n, P, ι, hP, π, hπ⟩ := hM
  exact ⟨n, P, ι, hP, _, @epi_comp _ _ _ _ _ π hπ _ hu⟩

/-- **A quotient of a sheaf of modules of finite type on a site is of finite type on the site**,
with the universe of the module sections independent of the universe of the coefficient rings.
This is `Stacks.SheafOfModules.isFiniteTypeOnSite_of_epi`, the clause 03DL(5) of Stacks 03DL for
an epimorphism: on each member of a covering witnessing finite type for the source, the
restricted epimorphism composes with the finite presenting coproduct of the source to present
the target. -/
theorem isFiniteTypeOnSite_of_epi' [HasSheafify J AddCommGrpCat.{m}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{m}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{m}]
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max uC vC r m}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max uC vC r m}]
    {M N : SheafOfModules.{m} R} (p : M ⟶ N) [Epi p]
    (hM : M.IsFiniteTypeOnSite) : N.IsFiniteTypeOnSite := by
  refine ⟨fun U => ?_⟩
  obtain ⟨I, V, f, hf, h⟩ := hM.locally_finitelyGenerated U
  refine ⟨I, V, f, hf, fun i => ?_⟩
  have := epi_over' p (V i)
  exact hasFiniteGlobalGenerators_of_epi' (p.over (V i)) (h i)

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Stack

attribute [local instance] CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : AlgebraicStacks.{u, t} B S hS) [UnivLE.{u + 1, m}]

/-- **Stacks 0GRB, part (1).**  Let `𝒳` be a locally Noetherian algebraic stack and let
`φ : ℱ ⟶ 𝒢` be a surjective map of quasi-coherent `𝒪_𝒳`-modules.  If `ℱ` is coherent then so
is `𝒢`.

Coherence is condition (1) of Stacks 0GR5, that the module be quasi-coherent and of finite type;
see the module documentation.  Quasi-coherence of `𝒢` is the hypothesis of the source, which
takes `φ` to be a map of quasi-coherent modules, and what is proved is that `𝒢` is of finite
type: the condition 03DL(5) is inherited by quotients over an arbitrary ringed site.
Surjectivity is `CategoryTheory.Epi`, which for a morphism of sheaves of modules is local
surjectivity, by `Stacks.SheafOfModules.EpiMono.epi_iff_isLocallySurjective`.  Local
Noetherianity is the hypothesis of the source and is not used. -/
@[stacks 0GRB "part (1): a quotient of a coherent module by a surjection of quasi-coherent
modules is coherent"]
theorem isQuasicoherentFiniteTypeModule_of_epi
    (_h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    {F G : SheafOfModules.{m} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)}
    (φ : F ⟶ G) [Epi φ]
    (hF : IsQuasicoherentFiniteTypeModule B S hS 𝒳 F)
    (hG : G.IsQuasicoherentOnSite) :
    IsQuasicoherentFiniteTypeModule B S hS 𝒳 G :=
  ⟨hG, Stacks.SheafOfModules.isFiniteTypeOnSite_of_epi' φ hF.2⟩

/-- **The finite-type half of Stacks 0GRB, part (2).**  Let `𝒳` be a locally Noetherian
algebraic stack and let `φ : ℱ ⟶ 𝒢` be a map of `𝒪_𝒳`-modules with `ℱ` coherent.  Then the image
of `φ`, computed in `Mod(𝒪_𝒳)` as Stacks 0GR9 prescribes, is of finite type.

This is part (1) applied to `CategoryTheory.Limits.factorThruImage φ`, which is an epimorphism.
It is the whole of part (2) except for quasi-coherence of the image, which is Stacks 06WV (3),
(7) and is not in this library; the statement therefore carries no tag.  Local Noetherianity is
the hypothesis of the source and is not used. -/
theorem isFiniteTypeOnSite_image
    (_h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    {F G : SheafOfModules.{m} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)}
    (φ : F ⟶ G) (hF : IsQuasicoherentFiniteTypeModule B S hS 𝒳 F) :
    (image φ).IsFiniteTypeOnSite :=
  Stacks.SheafOfModules.isFiniteTypeOnSite_of_epi' (factorThruImage φ) hF.2

/-- **Stacks 0GRB, part (2), over quasi-coherence of the image.**  Let `𝒳` be a locally
Noetherian algebraic stack and let `φ : ℱ ⟶ 𝒢` be a map of quasi-coherent `𝒪_𝒳`-modules with `ℱ`
coherent.  If the image of `φ`, computed in `Mod(𝒪_𝒳)` as Stacks 0GR9 prescribes, is
quasi-coherent, then it is coherent.

Quasi-coherence of the image is the hypothesis `hIm`.  In the source it is part of the ambient
setup, being Stacks 06WV (3), (7), and it is not formal: the condition 03DL(6) is not inherited
by quotients, and the inclusion of the quasi-coherent modules into all modules is right exact
but not exact.  That part of Stacks 06WV is not in this library, so the hypothesis is carried and
the statement is not tagged.  Everything else is the finite-type statement
`AlgebraicGeometry.Stack.isFiniteTypeOnSite_image`.  Local Noetherianity is the hypothesis of the
source and is not used. -/
theorem isQuasicoherentFiniteTypeModule_image
    (_h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    {F G : SheafOfModules.{m} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)}
    (φ : F ⟶ G) (hF : IsQuasicoherentFiniteTypeModule B S hS 𝒳 F)
    (hIm : (image φ).IsQuasicoherentOnSite) :
    IsQuasicoherentFiniteTypeModule B S hS 𝒳 (image φ) :=
  ⟨hIm, isFiniteTypeOnSite_image B S hS 𝒳 _h𝒳 φ hF⟩

end AlgebraicGeometry.Stack

end
