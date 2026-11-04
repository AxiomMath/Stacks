module

public import StacksFrontier.AlgebraicGeometry.Stacks.QuasicoherentRestrictionAlgebraicSpace
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageFullyFaithful
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackContinuousUnivLE
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Modules
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageFullyFaithfulExtensions

/-!
# Additions to `QuasicoherentRestrictionAlgebraicSpace`

Declarations this development adds alongside
`StacksFrontier.AlgebraicGeometry.Stacks.QuasicoherentRestrictionAlgebraicSpace`, kept in their own
module so that the base file is unchanged: 2 declaration(s) that the base file does not have, with
the section variables, namespaces and options they are stated in.
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.FibredSite

universe u v w m

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (τ : SiteKind)

end AlgebraicGeometry.FibredSite

namespace CategoryTheory.Adjunction

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {P : C ⥤ D} {R : D ⥤ C} (adj : P ⊣ R)

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Space

universe u v w m v' w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)
  (e : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (X.1 ⋙ typeToCat)).p)

/-! ### Restriction of modules to the small étale site of the representing space -/

/-! ### The comparison functor on quasi-coherent modules -/

/-! ### The equivalence -/

section Equivalence

variable (hres : RestrictionPreservesQuasicoherent.{u, v, w, m} B S hS X p hp e)
  {P : Modules.{u, m} B S hS X.1 X.2 ⥤
    SheafOfModules.{m} (FibredSite.ringStructureSheafCore B S hS p hp .etale)}
  (adj : P ⊣ moduleRestriction B S hS X p hp e)

end Equivalence

/-! ### The quasi-inverse exists, and the unit of the adjunction is an isomorphism

The two statements of this section are at **different** module universes, and the difference is
the whole point of the section.

`AlgebraicGeometry.Space.isRightAdjoint_moduleRestriction'` — the quasi-inverse exists — is at
`max u m` with `m` free: the module universe has to dominate the universe `u` of the sections of
the two structure sheaves, and that is the only constraint. Taking `m := u` gives it at `u`
itself, which is where the quasi-coherence inputs for `π_X^*` live
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_projectionPullbackModules`); taking
`m := max (u + 1) w m'` gives it at `max (u + 1) w m'`, so this subsumes the universe of
`AlgebraicGeometry.Space.isRightAdjoint_moduleRestriction`.

`AlgebraicGeometry.Space.isIso_unit_moduleRestriction` — `hunit` — is still at
`max (u + 1) w m`, and its docstring says why: it is proved against the direct image of sheaves
of modules, a construction that does need the module universe to dominate the universe of the
objects of the source site. So `hunit`, not the existence of the quasi-inverse, is what keeps the
equivalence clause of Stacks 0GQD off the module universe `u`.

For the existence statement, neither the universe `u + 1` of the objects of the small étale site
of `X` nor the universe `w` of the morphisms of `𝒳` occurs. The routes to a left adjoint that do
ask the module universe to dominate the universe of the *objects* of the source site —
`SheafOfModules.pushforward_isRightAdjoint_of_univLE`,
`Stacks.Sheaves.ModuleAdjunction.pushforward_isRightAdjoint` and
`Stacks.SheafOfModules.lowerShriek` — are not the only ones, and are not used here:
`SheafOfModules.pushforward_isRightAdjoint_of_essentiallySmall` asks instead that the source site
be *essentially* small and the target locally small in the module universe, which the two sites
of equation 075K satisfy at `u` by
`AlgebraicGeometry.Space.essentiallySmall_of_equivalenceOver` and
`AlgebraicGeometry.Space.SmallEtale.instEssentiallySmall`. The hypothesis
`AlgebraicGeometry.Space.RestrictionPreservesQuasicoherent` is available at this universe too,
because the 075K/06WJ/0GQC chain leaves the module universe free.
-/

section Adjoint

/-- **The quasi-inverse `π_X^*` of Stacks 0GQD exists, at every module universe dominating `u`.**
Restriction of modules to the small étale site of the algebraic space `X` representing `𝒳` —
equation 075K — is a right adjoint at the module universe `max u m`, so the hypothesis
`adj : P ⊣ moduleRestriction …` of the statements above is satisfiable there; at
`m := max (u + 1) w m'` this is `AlgebraicGeometry.Space.isRightAdjoint_moduleRestriction`.

The left adjoint is `SheafOfModules.pullback` of the structure homomorphism, which exists by
`SheafOfModules.pushforward_isRightAdjoint_of_essentiallySmall_univLE`. That instance asks only
that the source site of the restriction — the small étale site of `X` — be essentially small in
the module universe and that its target, the inherited étale site of `𝒳`, be locally small in
it; it asks nothing of the universe in which the *objects* of either site live, which is what
lets the module universe be `max u m` rather than a universe dominating `u + 1`. Both sites are
essentially small in the universe `u` of the schemes, by
`AlgebraicGeometry.Space.SmallEtale.instEssentiallySmall` and
`AlgebraicGeometry.Space.essentiallySmall_of_equivalenceOver`, hence in `max u m`; essential
smallness of `𝒳` there also supplies sheafification of abelian sheaves on `𝒳` and local
bijectivity, the remaining two hypotheses. The universe of the sheaves of rings is `u`, below the
module universe, which is the generality
`SheafOfModules.pushforward_isRightAdjoint_of_essentiallySmall_univLE` is stated at. -/
theorem isRightAdjoint_moduleRestriction' :
    (moduleRestriction.{u, v, w, max u m} B S hS X p hp e).IsRightAdjoint := by
  let _ := restrictionFunctor_isContinuous B S hS X.1 p hp e
  let _ : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_equivalenceOver B S hS X.1 p e
  let _ : EssentiallySmall.{max u m} 𝒳 :=
    (essentiallySmall_congr (equivSmallModel.{u} 𝒳)).mpr inferInstance
  let _ : EssentiallySmall.{max u m} (SmallEtale B S hS X.1) :=
    (essentiallySmall_congr (equivSmallModel.{u} (SmallEtale B S hS X.1))).mpr inferInstance
  let _ : HasWeakSheafify (BigFppfOver.associatedTopology B S hS p .etale)
      AddCommGrpCat.{max u m} :=
    (hasSheafifyEssentiallySmallSite.{_, _, _, _, max u m} _ _).1
  let _ : (BigFppfOver.associatedTopology B S hS p .etale).WEqualsLocallyBijective
      AddCommGrpCat.{max u m} :=
    .ofEssentiallySmall.{_, _, _, _, max u m} _
  exact inferInstanceAs (SheafOfModules.pushforward.{max u m}
    (restrictionStructureHom B S hS X p hp e)).IsRightAdjoint

/-- **The hypothesis `hunit` of Stacks 0GQD at the module universe `u`.** The unit of
`π_X^* ⊣ i_X^*` is an isomorphism, for every left adjoint `P` of restriction to the small étale
site of `X`, at module sections in the universe `u` of the schemes.

**This is the same assertion as `AlgebraicGeometry.Space.isIso_unit_moduleRestriction` at an
incomparable module universe, and neither implies the other.** Both are
`SheafOfModules.isIso_unit_of_fullyFaithful_rightAdjoint` — the adjoint triple
`P ⊣ i_X^* ⊣ G` for a fully faithful right adjoint `G` of restriction — and they differ only in
which construction of `G` they use, the two constructions covering disjoint universe regimes:

* `SheafOfModules.isIso_unit_of_isIso_coefficient` takes `G` to be the direct image of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DirectImage.lean`, whose sections over `x` are
  the compatible families indexed by the *objects* of a comma category of the source site, an
  explicit product over a type in `Type (max uC vD)`; its module universe therefore has to
  dominate `max (u + 1) w`, and in exchange the universe of the sheaves of rings is free.
* `SheafOfModules.pushforwardToposDirectImageAdjunction`, used here, takes `G` to be the
  Stacks 03D3 direct image of the morphism of topoi of `u_X`. Its universe-sensitive step is
  right Kan extension along `u_X^{op}` of sheaves of *sets*, an abstract limit, which exists
  from essential smallness of the small étale site of `X` in `Type u`
  (`AlgebraicGeometry.Space.SmallEtale.instEssentiallySmall`) and local smallness of `𝒳` there
  (`AlgebraicGeometry.Space.essentiallySmall_of_equivalenceOver`); nothing asks the module
  universe to dominate either site's object or morphism universe. In exchange it asks the module
  universe to *equal* the universe of the sheaves of rings, because the inverse and direct images
  of modules along a morphism of topoi read a sheaf of modules as an internal module over an
  internal ring object of the topos of sheaves of sets. The structure sheaf of Stacks 06TV has
  its sections in `Type u`, so that universe is `u`.

A single statement covering both would need a direct image of sheaves of modules at a module
universe that neither dominates the source site's object universe nor equals the ring universe —
either a site-level direct image built as an abstract limit over the comma category rather than
as an explicit product over its objects, or a restriction of scalars for sheaves of rings across
universes, with which the structure sheaf could be lifted to the module universe. Neither is in
the library.

`AlgebraicGeometry.Space.isRightAdjoint_moduleRestriction'` holds at `max u m`, hence at `u`, so
the hypothesis of this statement is satisfiable; and
`AlgebraicGeometry.Space.restrictionPreservesQuasicoherent` and the essential-surjectivity input
of Descent, Proposition 03DX are theorems at `u`, which is what makes this the universe the
clauses of Stacks 0GQD want. -/
theorem isIso_unit_moduleRestriction'
    {P : Modules.{u, u} B S hS X.1 X.2 ⥤
      SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .etale)}
    (adj : P ⊣ moduleRestriction.{u, v, w, u} B S hS X p hp e) :
    IsIso adj.unit := by
  let _ := restrictionFunctor_isContinuous B S hS X.1 p hp e
  let _ := restrictionFunctor_isCocontinuous B S hS X.1 p hp e
  let _ := isIso_restrictionStructureHom B S hS X p hp e
  let _ : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_equivalenceOver B S hS X.1 p e
  let _ : ∀ F : (SmallEtale B S hS X.1)ᵒᵖ ⥤ Type u,
      (restrictionFunctor B S hS X.1 p e).op.HasPointwiseRightKanExtension F := fun _ Y =>
    let := CategoryTheory.Limits.hasLimitsOfShape_of_essentiallySmall.{u}
      (CategoryTheory.StructuredArrow Y (restrictionFunctor B S hS X.1 p e).op) (Type u)
    inferInstance
  exact SheafOfModules.isIso_unit_of_fullyFaithful_rightAdjoint
    (restrictionStructureHom B S hS X p hp e)
    (SheafOfModules.pushforwardToposDirectImageAdjunction.{u}
      (restrictionFunctor B S hS X.1 p e) (SmallEtale.topology B S hS X.1)
      (BigFppfOver.associatedTopology B S hS p .etale)
      (FibredSite.ringStructureSheafCore B S hS p hp .etale)
      (restrictionStructureHom B S hS X p hp e)) adj

end Adjoint

/-! ### Compatibility with pullback -/

end AlgebraicGeometry.Space

end
