module

public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LerayDegreewise
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ProperHigherDirectImageVanishing
public import StacksFrontier.Topology.Maps.Proper
public import StacksFrontier.Topology.Proper.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.FibrewiseSoftPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.FlasqueSoft
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.ProperBaseChangeAtAPoint
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianBaseChangeMap
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianBaseChangeStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Proper base change for the derived direct image of abelian sheaves

Let

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

be a cartesian square of topological spaces with `f` proper in the sense of
[Stacks, Tag 005O] (5). This file proves that the base change morphism

`g^{-1} Rf_* ⟶ Rf'_* (g')^{-1}`

of `Stacks.Cohomology.BaseChange.abelianBaseChange` is an isomorphism of functors on bounded
below derived categories of abelian sheaves, which is [Stacks, Tag 09V6]. The only hypotheses are
the two of the source: the square is cartesian and `f` is proper.

## The route

The derived statement is not obtained by globalising [Stacks, Tag 09V5]: as formalized,
`Stacks.Cohomology.ProperBaseChange.isIso_properBaseChangeMap` is about ringed spaces and
sheaves of modules and concludes in the derived category of `𝒪_{Y,y}`-modules, whereas the
present statement is about topological spaces and abelian sheaves, and no stalkwise detection
of isomorphisms in `D⁺` of abelian sheaves is available.

Instead the fully abstract criterion
`Stacks.Cohomology.ProperBaseChange.isIso_baseChangeDerived` applies directly:
`abelianBaseChange` *is* `Stacks.Cohomology.BaseChange.derived` applied to
`abelianSheafBaseChange` and `abelianPullbackComparison`, so invertibility of the derived
morphism reduces to exactly two inputs,

* the invertibility of the underived morphism `abelianSheafBaseChange`, and
* the vanishing `R^p f'_*((g')^{-1} I) = 0` for `p > 0` and `I` an injective abelian sheaf
  on `X`,

the comparison `e` of the criterion being supplied by exactness of the inverse image of abelian
sheaves (`Stacks.Cohomology.BaseChange.abelianPullbackComparison`) and the invertibility of the
derived-functor unit of `(g')^{-1}` by the same exactness
(`Stacks.Cohomology.BaseChange.exactUnit_isIso`).

Both inputs are proved here.

The first is `isIso_abelianSheafBaseChange_of_properMap`, and it holds at *every* abelian sheaf
and not only at an injective one, the criterion's restriction to injectives being a weakening of
its hypothesis. It is the stalkwise argument, steps (1)–(4) of the proof recorded at the tag,
assembled in
`StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/AbelianBaseChangeStalk.lean`:
isomorphisms of abelian sheaves are detected on stalks
(`TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso`; it is in `D⁺` that stalkwise detection is
unavailable, which is why the derived statement needs the criterion at all), the stalk of
`g^{-1}` is the stalk at the image point (`Stacks.Topology.isIso_ambientStalkHom`), the stalk of
`f_*` at a point is the sections on the fibre for a closed map with quasi-compact separated
fibres (`Stacks.Topology.isIso_fiberStalkSectionsMap`), and the two fibres have the same sections
(`Stacks.Topology.squareSectionsIso`). That the base change morphism is the map those three
identifications produce is
`Stacks.Cohomology.BaseChange.ambientStalkHom_comp_stalkFunctor_map_abelianSheafBaseChange`, a
four-factor identity in which it is the only non-invertible factor, checked on a germ.

The second input is the vanishing. The inverse image `(g')^{-1} I` of an injective sheaf is
neither injective nor flasque, so the vanishing is not the acyclicity of an injective: it is
`Stacks.Topology.isZero_rightDerived_pushforward_of_isSoft_fiber`, the vanishing of the higher
direct images along a closed map with quasi-compact separated fibres of a sheaf whose
restriction to each fibre is soft, fed the fibrewise softness
`Stacks.Topology.isSoft_restrictionFunctorUnivLE_fiber_of_isFlasque` of the inverse image of a
flasque sheaf — an injective abelian sheaf being flasque by
`Stacks.Topology.isFlasque_of_injective`.

Both of those need `f'` to be closed with quasi-compact separated fibres, and that is the third
thing proved here: properness in the sense of [Stacks, Tag 005O] (5) is by definition
separatedness together with universal closedness, so `f'` is closed *by the definition of
properness of `f`* once the vertex of the square is presented as the subspace of `Y' × X` cut
out by `g p.1 = f p.2`; the fibres of `f'` are homeomorphic to those of `f` by
`Stacks.Topology.fiberHomeoOfPullbackPresentation` and so quasi-compact, `f` being closed with
quasi-compact fibres by [Stacks, Tag 005R]; and separatedness of `f'` follows from that of `f`
because `g'` is injective on each fibre of `f'`. No Hausdorff hypothesis on any of the four
spaces is used — in particular `Stacks.Topology.isProperMap_subtype_fst`, which needs `Y` and
`Y'` Hausdorff, is *not* the transfer used.

## Main definitions

* `pullbackHomeo`: the presentation of the vertex of the cartesian square as the subspace
  `{p : Y' × X // g p.1 = f p.2}` of the product, compatible with the two projections.

## Main results

All in the namespace `Stacks.Cohomology.AbelianProperBaseChange`.

* `isClosedMap_baseChange`, `isCompact_fiber_baseChange`, `isSeparatedMap_baseChange`: the
  transfer of properness from `f` to `f'`, across an abstract cartesian square.
* `rightAcyclic_pushforward_pullback_of_injective`: the vanishing
  `R^{p>0} f'_*((g')^{-1} I) = 0` for `I` injective, in the shape
  `Stacks.Cohomology.ProperBaseChange.isIso_baseChangeDerived` consumes.
* `isIso_abelianSheafBaseChange_of_properMap`: the underived morphism `g^{-1} f_* ⟶ f'_*(g')^{-1}`
  is an isomorphism, at every abelian sheaf.
* `isIso_abelianBaseChange`: **[Stacks, Tag 09V6]**, with no hypothesis beyond the square being
  cartesian and `f` proper.
* `isIso_abelianBaseChange_app`: the same read at one bounded below complex.
* `isIso_abelianBaseChange_id`: the identity square, the certificate that the two hypotheses are
  jointly satisfiable.

## The underived input, and the route not taken

Both inputs are proved. The underived morphism `g^{-1} f_* ⟶ f'_*(g')^{-1}` is a
`Stacks.Cohomology.BaseChange.mate`, so any route to its invertibility has to compute what it
does on sections, and that computation is
`Stacks.Cohomology.BaseChange.abelianSheafBaseChange_unit`: transposing it back across the
adjunction of `g` returns `f_*` applied to the unit of the adjunction of `g'`, with
`abelianSheafBaseChange_hom_app_unit` reading that at one open. Transposition being a bijection,
this determines the morphism. The route taken is the stalkwise one, and its three further
ingredients are

* the spelling `Stacks.Topology.ambientSection_eq_unit`, that
  `ambientSection f F (le_refl ((Opens.map f).obj U))` is
  `((TopCat.Sheaf.pullbackPushforwardAdjunction C f).unit.app F).hom.app (op U)`, with the germ
  formula `Stacks.Topology.germ_unit_app`
  (`Topology/Sheaves/Functors/Pullback/UnitOnSections.lean`);
* the identification of `Γ(f'^{-1}(y'), (g')^{-1}F)` with `Γ(f^{-1}(g y'), F)` across the
  homeomorphism of fibres, compatibly with `ambientSection`:
  `Stacks.Topology.squareSectionsIso` and
  `Stacks.Topology.ambientSection_comp_squareSectionsIso`
  (`Topology/Sheaves/Cohomology/CompactSubset/InverseImageSquareSections.lean`);
* the stalk-level assembly of those two with the two stalk computations,
  `Stacks.Cohomology.BaseChange.ambientStalkHom_comp_stalkFunctor_map_abelianSheafBaseChange`
  (`Topology/Sheaves/Cohomology/HigherDirectImage/AbelianBaseChangeStalk.lean`).

The alternative route, through [Stacks, Tag 0D90], is *not* taken and remains unbuilt. The
library proves the corresponding statement for sheaves of **sets**,
`Stacks.Topology.ProperBaseChange.isIso_properBaseChangeMap`, but that is a different statement
about a different map: its inverse images are the germ models `GermPullback.sheaf` (identified
with `TopCat.Sheaf.pullback` by `GermPullback.sheafPullbackIso` and
`GermPullback.abelianSheafPullbackIso`), its square is the concrete `Function.Pullback` rather
than an abstract cartesian one, and the passage from sheaves of sets to abelian sheaves is the
transfer of [Stacks, Tag 04JC], carried out for the Zariski comparison only in
`Stacks.Topology.LocallyQuasiCompactZariskiSituation.isIso_zariskiBaseChange_of_properMap`. What
that route would still owe is the identification of the mate with
`Stacks.Topology.ProperBaseChange.properBaseChangeMap` across those isomorphisms, and the
transfer of invertibility from the concrete square to an abstract cartesian one. Neither is
needed for the tag.

The statement is stated about `Stacks.Cohomology.BaseChange.abelianBaseChange` and not about
the `@[stacks 02N7]` map of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/FlatBaseChange.lean`: the latter is
the ringed-space, sheaves-of-modules, *flat* morphism `g^* Rf_* ⟶ Rf'_*(g')^*`, and neither map
is obtained from the other by specialization.

## References

* [Stacks Project, Tag 09V6](https://stacks.math.columbia.edu/tag/09V6)
* [Stacks Project, Tag 005O](https://stacks.math.columbia.edu/tag/005O)
* [Stacks Project, Tag 005R](https://stacks.math.columbia.edu/tag/005R)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
* [SGA4, Exposé V bis, 4.1.1]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Stacks.Cohomology.AbelianProperBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X X' Y Y' : TopCat.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)

/-! ### The vertex of a cartesian square as a subspace of the product -/

/-- **The vertex of a cartesian square of spaces, presented as the subspace of `Y' × X` cut out
by `g p.1 = f p.2`.** This is the shape in which both the properness transfer of
[Stacks, Tag 005O] (4) and the fibrewise softness of
`Stacks.Topology.isSoft_restrictionFunctorUnivLE_fiber_of_isFlasque` consume a cartesian
square. -/
def pullbackHomeo (hcart : IsPullback g' f' f g) :
    X' ≃ₜ {p : Y' × X // (g.hom : Y' → Y) p.1 = (f.hom : X → Y) p.2} :=
  TopCat.homeoOfIso (hcart.flip.isoPullback ≪≫ TopCat.pullbackIsoProdSubtype g f)

/-- The presentation of the vertex is compatible with the two projections: a point of `X'` goes
to the pair of its images under `f'` and `g'`. -/
theorem pullbackHomeo_apply (hcart : IsPullback g' f' f g) (q : X') :
    ((pullbackHomeo f f' g g' hcart) q).val
      = ((f'.hom : X' → Y') q, (g'.hom : X' → X) q) := by
  have h1 := ConcreteCategory.congr_hom hcart.flip.isoPullback_hom_fst q
  have h2 := ConcreteCategory.congr_hom hcart.flip.isoPullback_hom_snd q
  rw [ConcreteCategory.comp_apply] at h1 h2
  exact Prod.ext h1 h2

/-! ### Properness transfers to the base change -/

/-- **The base change of a proper map is closed.** This is the definition of universal
closedness, [Stacks, Tag 005O] (4), read through `pullbackHomeo`. -/
theorem isClosedMap_baseChange (hcart : IsPullback g' f' f g)
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u} (f.hom : X → Y)) :
    IsClosedMap (f'.hom : X' → Y') := by
  have hclosed : IsClosedMap
      (Function.Pullback.fst : Function.Pullback (g.hom : Y' → Y) (f.hom : X → Y) → Y') :=
    hf.2 Y' (g.hom : Y' → Y) g.hom.continuous
  have hcomp : (f'.hom : X' → Y')
      = Function.Pullback.fst ∘ (pullbackHomeo f f' g g' hcart) := by
    funext q
    exact (congrArg Prod.fst (pullbackHomeo_apply f f' g g' hcart q)).symm
  rw [hcomp]
  exact hclosed.comp (pullbackHomeo f f' g g' hcart).isClosedMap

/-- **A proper map has quasi-compact fibres.** Properness is separatedness together with
universal closedness, [Stacks, Tag 005O] (5), and [Stacks, Tag 005R] turns universal closedness
into closedness together with quasi-compactness of the fibres. -/
theorem isCompact_fiber (hf : StacksDraft.Topology.IsProperMap.{u, u, u} (f.hom : X → Y))
    (y : Y) :
    IsCompact ((f.hom : X → Y) ⁻¹' ({y} : Set Y)) := by
  have hucm : StacksDraft.Topology.IsUniversallyClosedMap.{u, u, u} (f.hom : X → Y) := hf.2
  have huc : IsUniversallyClosed (f.hom : X → Y) := by
    intro Z _ k hk
    exact hucm Z k hk
  have htfae : IsUniversallyClosed (f.hom : X → Y) ↔
      (IsClosedMap (f.hom : X → Y) ∧
        ∀ y : Y, IsQuasiCompactSubset ((f.hom : X → Y) ⁻¹' ({y} : Set Y))) :=
    (isProperMap_tfae (f.hom : X → Y) f.hom.continuous).out 3 4
  exact (htfae.1 huc).2 y

/-- **The fibres of the base change of a proper map are quasi-compact.** The second projection
carries the fibre of `f'` over `y'` homeomorphically onto the fibre of `f` over `g y'`
(`Stacks.Topology.fiberHomeoOfPullbackPresentation`), and the latter is quasi-compact. -/
theorem isCompact_fiber_baseChange (hcart : IsPullback g' f' f g)
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u} (f.hom : X → Y)) (y' : Y') :
    IsCompact ((f'.hom : X' → Y') ⁻¹' ({y'} : Set Y')) := by
  rw [isCompact_iff_compactSpace]
  have _hc : CompactSpace ((f.hom : X → Y) ⁻¹' ({(g.hom : Y' → Y) y'} : Set Y)) :=
    isCompact_iff_compactSpace.1 (isCompact_fiber f hf _)
  exact (Stacks.Topology.fiberHomeoOfPullbackPresentation f g f' g'
    (pullbackHomeo f f' g g' hcart) (pullbackHomeo_apply f f' g g' hcart) y').symm.compactSpace

/-- **The base change of a separated map is separated.** Two distinct points of `X'` with the
same image under `f'` have distinct images under `g'`, the pair `(f', g')` being injective by
`pullbackHomeo`, and those images lie in one fibre of `f`; disjoint open neighbourhoods of them
pull back to disjoint open neighbourhoods in `X'`. -/
theorem isSeparatedMap_baseChange (hcart : IsPullback g' f' f g)
    (hsep : IsSeparatedMap (f.hom : X → Y)) :
    IsSeparatedMap (f'.hom : X' → Y') := by
  have hcomm : ∀ q : X', (f.hom : X → Y) ((g'.hom : X' → X) q)
      = (g.hom : Y' → Y) ((f'.hom : X' → Y') q) := by
    intro q
    have h := ConcreteCategory.congr_hom hcart.w q
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
    exact h
  intro q₁ q₂ hfq hne
  have hne' : (g'.hom : X' → X) q₁ ≠ (g'.hom : X' → X) q₂ := by
    intro h
    refine hne ((pullbackHomeo f f' g g' hcart).injective (Subtype.ext ?_))
    rw [pullbackHomeo_apply, pullbackHomeo_apply, hfq, h]
  obtain ⟨A, B, hA, hB, hqA, hqB, hAB⟩ :=
    hsep _ _ (by rw [hcomm, hcomm, hfq]) hne'
  exact ⟨(g'.hom : X' → X) ⁻¹' A, (g'.hom : X' → X) ⁻¹' B,
    hA.preimage g'.hom.continuous, hB.preimage g'.hom.continuous, hqA, hqB, hAB.preimage _⟩

/-! ### Higher direct images of the inverse image of an injective sheaf -/

/-- **`R^p f'_*((g')^{-1} I) = 0` for `p > 0` and `I` an injective abelian sheaf on `X`**, for a
cartesian square whose vertical map `f` is proper.

This is the acyclicity input of
`Stacks.Cohomology.ProperBaseChange.isIso_baseChangeDerived`. The sheaf `(g')^{-1} I` is neither
injective nor flasque; what makes its higher direct images along `f'` vanish is that its
restriction to every fibre of `f'` is soft
(`Stacks.Topology.isSoft_restrictionFunctorUnivLE_fiber_of_isFlasque`, `I` being flasque by
`Stacks.Topology.isFlasque_of_injective`), together with `f'` being closed with quasi-compact
separated fibres. -/
theorem rightAcyclic_pushforward_pullback_of_injective (hcart : IsPullback g' f' f g)
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u} (f.hom : X → Y))
    (I : TopCat.Sheaf AddCommGrpCat.{u} X) (hI : Injective I) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f').rightAcyclic
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u} g').obj I) := by
  have _hinj := hI
  have _hei : EnoughInjectives (TopCat.Sheaf AddCommGrpCat.{u} X') :=
    Stacks.Topology.enoughInjectives_sheafOpens.{u, u} X'
  have _hpl : PreservesFiniteLimits (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f') :=
    let : PreservesLimitsOfSize.{0, 0} (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f') :=
      inferInstance
    PreservesLimitsOfSize.preservesFiniteLimits _
  have _hfl : TopCat.Sheaf.IsFlasque I := Stacks.Topology.isFlasque_of_injective I
  rw [Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived]
  intro p hp
  exact Stacks.Topology.isZero_rightDerived_pushforward_of_isSoft_fiber f'
    ((TopCat.Sheaf.pullback AddCommGrpCat.{u} g').obj I)
    (isClosedMap_baseChange f f' g g' hcart hf)
    (isCompact_fiber_baseChange f f' g g' hcart hf)
    (isSeparatedMap_baseChange f f' g g' hcart hf.1)
    (fun w => Stacks.Topology.isSoft_restrictionFunctorUnivLE_fiber_of_isFlasque.{u}
      f g f' g' (pullbackHomeo f f' g g' hcart) (pullbackHomeo_apply f f' g g' hcart)
      I (isCompact_fiber f hf) hf.1 w)
    p hp

/-! ### The underived base change morphism -/

/-- **The underived base change morphism `g^{-1} f_* ⟶ f'_*(g')^{-1}` of abelian sheaves is an
isomorphism**, for a cartesian square whose vertical map `f` is proper — at every abelian sheaf on
`X`, injective or not.

This is steps (1)–(4) of the proof of [Stacks, Tag 09V6]: it is `Stacks.Cohomology.BaseChange`'s
stalkwise criterion `isIso_abelianSheafBaseChange_of_fiberIso` fed the properness transfer proved
above (`isClosedMap_baseChange`, `isCompact_fiber_baseChange`, `isSeparatedMap_baseChange`, and
for `f` itself `StacksDraft.Topology.IsProperMap.isClosedMap` and `isCompact_fiber`) together
with the identification of the fibres of `f'` with those of `f`,
`Stacks.Topology.fiberIsoOfPullbackPresentation` read through `pullbackHomeo`.

It is a step of the proof of the tag and not a clause of its statement, so it carries no tag; what
it does is supply the invertibility of the base change map in the proof of
`isIso_abelianBaseChange`. -/
theorem isIso_abelianSheafBaseChange_of_properMap (hcart : IsPullback g' f' f g)
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u} (f.hom : X → Y)) :
    IsIso (BaseChange.abelianSheafBaseChange f f' g g' hcart.w) :=
  BaseChange.isIso_abelianSheafBaseChange_of_fiberIso f f' g g' hcart.w
    (StacksDraft.Topology.IsProperMap.isClosedMap f.hom.continuous hf) hf.1
    (isClosedMap_baseChange f f' g g' hcart hf)
    (isSeparatedMap_baseChange f f' g g' hcart hf.1)
    (isCompact_fiber f hf) (isCompact_fiber_baseChange f f' g g' hcart hf)
    (fun y' => Stacks.Topology.fiberIsoOfPullbackPresentation f g f' g'
      (pullbackHomeo f f' g g' hcart) (pullbackHomeo_apply f f' g g' hcart) y')
    (fun y' => Stacks.Topology.subsetInclusion_comp_fiberIsoOfPullbackPresentation f g f' g'
      (pullbackHomeo f f' g g' hcart) (pullbackHomeo_apply f f' g g' hcart) y')

/-! ### Proper base change -/

/-- **Proper base change for abelian sheaves on topological spaces, [Stacks, Tag 09V6].** For a
cartesian square of topological spaces

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` proper in the sense of [Stacks, Tag 005O] (5), the canonical base change morphism

`g^{-1} Rf_* ⟶ Rf'_* (g')^{-1}`

of `Stacks.Cohomology.BaseChange.abelianBaseChange` is an isomorphism of functors
`D⁺(X) ⥤ D⁺(Y')` on bounded below derived categories of abelian sheaves — hence an isomorphism
at every bounded below complex, naturally in it.

Both inputs of the criterion `Stacks.Cohomology.ProperBaseChange.isIso_baseChangeDerived` are
proved from properness.
They are the invertibility of the *underived* base change morphism
`Stacks.Cohomology.BaseChange.abelianSheafBaseChange`, `g^{-1} f_* ⟶ f'_* (g')^{-1}`, which is
`isIso_abelianSheafBaseChange_of_properMap` above — asked for by the criterion only at injective
sheaves, because both derived functors on its right-hand side are computed on a complex of
injectives, but proved at every abelian sheaf — and the vanishing
`R^{p>0} f'_*((g')^{-1} I) = 0` at an injective `I`, which is
`rightAcyclic_pushforward_pullback_of_injective`, together with the transfer of properness from
`f` to `f'`. -/
@[stacks 09V6 "derived proper base change for abelian sheaves: g^{-1} Rf_* ⟶ Rf'_* (g')^{-1} is \
an isomorphism of functors on D⁺ for f proper and the square cartesian; the underived base \
change morphism is inverted by isIso_abelianSheafBaseChange_of_properMap, the acyclicity \
R^p f'_* (g')^{-1} I = 0 for p > 0 is rightAcyclic_pushforward_pullback_of_injective, and \
properness of f' is isClosedMap_baseChange/isCompact_fiber_baseChange/isSeparatedMap_baseChange",
  sga "4 Vbis 4.1.1" "more general"]
theorem isIso_abelianBaseChange (hcart : IsPullback g' f' f g)
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u} (f.hom : X → Y)) :
    IsIso (BaseChange.abelianBaseChange f f' g g' hcart.w) := by
  have _hei : ∀ Z : TopCat.{u}, EnoughInjectives (TopCat.Sheaf AddCommGrpCat.{u} Z) :=
    fun Z => Stacks.Topology.enoughInjectives_sheafOpens.{u, u} Z
  have _hunit :
      IsIso (TopCat.Sheaf.pullback AddCommGrpCat.{u} g').rightDerivedFunctorPlusUnith :=
    BaseChange.exactUnit_isIso (TopCat.Sheaf.pullback AddCommGrpCat.{u} g')
  exact ProperBaseChange.isIso_baseChangeDerived
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f')
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} g)
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} g')
    (BaseChange.abelianSheafBaseChange f f' g g' hcart.w)
    (fun I _ =>
      have _h := isIso_abelianSheafBaseChange_of_properMap f f' g g' hcart hf
      inferInstance)
    (BaseChange.abelianPullbackComparison g)
    (fun M hM => rightAcyclic_pushforward_pullback_of_injective f f' g g' hcart hf M hM)

/-- **[Stacks, Tag 09V6] at one bounded below complex**, the form in which the base change
morphism is applied: for `E` a bounded below complex of abelian sheaves on `X`, the morphism
`g^{-1} Rf_* E ⟶ Rf'_* (g')^{-1} E` is an isomorphism in `D⁺(Y')`. -/
theorem isIso_abelianBaseChange_app (hcart : IsPullback g' f' f g)
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u} (f.hom : X → Y))
    (E : DerivedCategory.Plus (TopCat.Sheaf AddCommGrpCat.{u} X)) :
    IsIso ((BaseChange.abelianBaseChange f f' g g' hcart.w).app E) :=
  have _h := isIso_abelianBaseChange f f' g g' hcart hf
  inferInstance

/-! ### The hypotheses are satisfiable: the identity square -/

/-- **[Stacks, Tag 09V6] for the cartesian square whose horizontal arrows are identities.**

Both hypotheses of `isIso_abelianBaseChange` are hypotheses of the source statement — the square
is cartesian and `f` is proper — and this records that they are jointly satisfiable: the square
with identity horizontal arrows is cartesian over an arbitrary pair of spaces and an arbitrary
proper `f`, so the theorem is not vacuous. The non-degenerate instantiation is the one of the
source itself, `X' = Y' ×_Y X`; see `isIso_abelianSheafBaseChange_of_properMap`, where the fibre
isomorphism is `Stacks.Topology.fiberIsoOfPullbackPresentation`. -/
theorem isIso_abelianBaseChange_id
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u} (f.hom : X → Y)) :
    IsIso (BaseChange.abelianBaseChange f f (𝟙 Y) (𝟙 X)
      (IsPullback.of_id_fst (f := f)).w) :=
  isIso_abelianBaseChange f f (𝟙 Y) (𝟙 X) (IsPullback.of_id_fst (f := f)) hf

end Stacks.Cohomology.AbelianProperBaseChange

end
