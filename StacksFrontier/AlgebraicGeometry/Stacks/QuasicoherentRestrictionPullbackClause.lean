module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.Smallness
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionDirectImageComparisonIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphismModules

/-!
# The pullback-compatibility clause of Stacks 0GQD

Let `𝒳 ⥤ (Sch/S)_{fppf}` and `𝒴 ⥤ (Sch/S)_{fppf}` be categories fibred in groupoids representable
by algebraic spaces `F` and `G`, and let `f : 𝒳 ⥤ 𝒴` be a 1-morphism over the base.  **Stacks
0GQD** says that restriction to the small étale site is an equivalence `QCoh(𝒪_𝒳) ⟶ QCoh(𝒪_F)`
with quasi-inverse `𝒢 ↦ π_F^*𝒢`, and that the equivalence **is compatible with pullback** along
`f`.  This file carries that last clause.

The source's proof of it is one sentence: "compatibility with pullbacks follows from the fact that
the quasi-inverse is given by `π_F^*` and the commutative diagram of ringed topoi in Lemma 073N".
Read through the quasi-inverses, the clause says that the two inverse images commute with `π_F^*`
and `π_G^*`,

```
π_G^* ⋙ f^*  ≅  g^* ⋙ π_F^*,
```

where `g : F ⟶ G` is the morphism of algebraic spaces that `f` induces.  That is what is proved
below, and it is proved **unconditionally**: the square of ringed topoi of Stacks 073N commutes at
the induced morphism (`AlgebraicGeometry.Space.restrictionRingedSquareOfInduced`, which has
equation 075M as `AlgebraicGeometry.Space.isIso_restrictedDirectImageComparison`), and a commuting
square of ringed topoi gives a commuting square of pullbacks of sheaves of modules
(`AlgebraicGeometry.RingedToposHom.TwoIso.pullbackModulesIso`) because each pullback is the left
adjoint of the corresponding direct image.

## Main results

* `AlgebraicGeometry.Space.nonempty_projectionPullbackModules_comp_iso`: **the
  pullback-compatibility clause of Stacks 0GQD**, with no hypothesis beyond the data of the two
  representable categories fibred in groupoids and the 1-morphism between them.

## Why no adjunction is assumed, and in which universe

`AlgebraicGeometry.Space.nonempty_projectionPullback_comp_iso` in
`StacksFrontier/AlgebraicGeometry/Stacks/QuasicoherentRestrictionAlgebraicSpace.lean` is the same
deduction run abstractly: it quantifies over adjunctions for the inverse and direct images of
Stacks 06WE and Stacks 03LU and for the two quasi-inverses, and takes the comparison of the two
direct images as a hypothesis.  Nothing of that is needed here, because every one of those four
adjunctions is the Stacks 03D7 adjunction of a morphism of ringed topoi
(`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules`), and the four morphisms of
ringed topoi are all available:

* `AlgebraicGeometry.Space.projectionRingedToposHom` is `π_F` (Stacks 073M), whose Stacks 03D6
  pullback of modules is the source's `π_F^*`;
* `AlgebraicGeometry.FibredSite.ringedToposMorphism` is the morphism of ringed topoi of the
  1-morphism `f`, whose pullback of modules is the inverse image of Stacks 06WE;
* `AlgebraicGeometry.Space.smallEtaleRingedToposHom` is the morphism of small étale ringed topoi
  of Stacks 03G8 of the induced `g : F ⟶ G`, whose pullback of modules is the inverse image of
  Stacks 03LU.

So the module universe is the universe `u` of the sections of the structure sheaves, for all four
at once, and no size bound on the two fibred categories enters.  This is the one universe in which
the clause can be stated at all: the direct image of Stacks 03LU is assembled from the comparison
equivalence of Stacks 03G1, which exists only at `Type u`
(`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullback.lean`), while the chosen
quasi-inverse `AlgebraicGeometry.Space.projectionModulePullback` of
`StacksFrontier/AlgebraicGeometry/Stacks/QuasicoherentRestrictionDescentInputs.lean` is stated at
`max (u + 1) w m`.  That is **not** because a left adjoint of restriction needs the module
universe to dominate the universe `u + 1` of the objects of the small étale site, as an earlier
revision of this paragraph said: `AlgebraicGeometry.Space.isRightAdjoint_moduleRestriction'`
holds at `max u m`, through `SheafOfModules.pushforward_isRightAdjoint_of_essentiallySmall`, which
asks nothing about object universes.  It is because the chain that file builds on the chosen
quasi-inverse passes through `hunit`,
`AlgebraicGeometry.Space.isIso_unit_moduleRestriction`, whose adjoint-triple argument needs the
direct image of sheaves of modules and so does need the module universe to dominate `u + 1`.
Either way the ringed-topos route taken here avoids that bound rather than meeting it, and so is
not an instance of the abstract statement.

## Implementation notes

The three pullbacks are spelled uniformly as
`AlgebraicGeometry.RingedToposHom.pullbackModules`, Stacks 03D6 part (2) at the two-field morphism
of ringed topoi of Stacks 01D3.  For the induced morphism `g` of algebraic spaces that is the same
construction as `AlgebraicGeometry.Space.modulePullback`, which carries `@[stacks 03LU "pullback"]`
— both are Stacks 03D6 part (2) applied to `AlgebraicGeometry.Space.smallEtaleRingedToposHom` —
but the two are not *definitionally* the same term, because they reach the four-field morphism of
the modules development by the two different conversions
`AlgebraicGeometry.RingedToposHom.toModulesHom` and
`AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom`: one adjuncts the structure map at the
level of sheaves of rings, the other at the level of sheaves of commutative rings and then forgets
commutativity.  The identification of those two adjuncts is not recorded in this development — the
docstring of `AlgebraicGeometry.RingedToposHom.fSharpInverseImageRing` says so — so the uniform
spelling is used here and the 03LU spelling is not claimed.

The instance `∀ H, f.op.HasPointwiseRightKanExtension H` is the existence of the direct image
along `f`, which equation 075M is a statement about; it is the hypothesis under which
`AlgebraicGeometry.Space.restrictionRingedSquareOfInduced` itself is stated.

## References

* [Stacks Project, Tag 0GQD](https://stacks.math.columbia.edu/tag/0GQD)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
* [Stacks Project, Tag 073N](https://stacks.math.columbia.edu/tag/073N)
* [Stacks Project, Equation 075M](https://stacks.math.columbia.edu/tag/075M)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v w v' w'

attribute [local instance] hasSheafCompose_forget_ringCat
  Stacks.hasSheafCompose_forget₂_commRingCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
  (eF : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (F ⋙ typeToCat)).p)
  (eG : StacksRepresentableCFG.EquivalenceOver q
    (presheafOfCategories (G ⋙ typeToCat)).p)
  (f : 𝒳 ⥤ 𝒴) (hf : p.IsFibredOneMorphism q f)
  [∀ H : 𝒳ᵒᵖ ⥤ Type u, f.op.HasPointwiseRightKanExtension H]

/-- Restriction to the small étale site is compatible with pullback. The equivalence
`QCoh(𝒪_𝒳) ⟶ QCoh(𝒪_F)` of Stacks 0GQD is compatible with pullback along a 1-morphism
`f : 𝒳 ⥤ 𝒴` between categories fibred in groupoids representable by algebraic spaces `F` and
`G`: read through the quasi-inverses, pulling an `𝒪_G`-module back to `𝒴` along `π_G` and then
along `f` is naturally pulling it back to `F` along the induced morphism `g : F ⟶ G` of algebraic
spaces and then along `π_F`.

Here `π_F^*` and `π_G^*` are the inverse images of modules along the morphisms of ringed topoi
`π_F` and `π_G` of Stacks 073M — which is what the source means by the quasi-inverse of the
equivalence — `f^*` is the inverse image of Stacks 06WE along `f`, and `g^*` is the inverse image
of Stacks 03LU along `g`; each is Stacks 03D6 part (2) at the corresponding morphism of ringed
topoi.

Nothing is assumed beyond the data of the two representable categories fibred in groupoids and of
the 1-morphism between them. The proof is the source's: the square of ringed topoi of Stacks 073N
commutes at the induced morphism, by
`AlgebraicGeometry.Space.restrictionRingedSquareOfInduced`, whose geometric content is that the
comparison map of equation 075M is an isomorphism; and a 2-isomorphism of two morphisms of ringed
topoi gives an isomorphism of their pullbacks of sheaves of modules, by uniqueness of left
adjoints of the two direct images
(`AlgebraicGeometry.RingedToposHom.TwoIso.pullbackModulesIso`). The two composites are split off
by `AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso`, the pseudo-functoriality of
Stacks 03D6 part (2). -/
theorem nonempty_projectionPullbackModules_comp_iso :
    letI : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_equivalenceOver B S hS F p eF
    letI : EssentiallySmall.{u} 𝒴 := essentiallySmall_of_equivalenceOver B S hS G q eG
    letI : (FibredSite.associatedRingedTopos B S hS p hp .etale).J.HasSheafCompose
      (forget AddCommGrpCat.{u}) := inferInstance
    letI : (FibredSite.associatedRingedTopos B S hS q hq .etale).J.HasSheafCompose
      (forget AddCommGrpCat.{u}) := inferInstance
    letI : HasWeakSheafify (FibredSite.associatedRingedTopos B S hS p hp .etale).J
      AddCommGrpCat.{u} := FibredSite.hasWeakSheafify_associatedTopology B S hS p .etale
    letI : HasWeakSheafify (FibredSite.associatedRingedTopos B S hS q hq .etale).J
      AddCommGrpCat.{u} := FibredSite.hasWeakSheafify_associatedTopology B S hS q .etale
    letI : (FibredSite.associatedRingedTopos B S hS p hp .etale).J.WEqualsLocallyBijective
      AddCommGrpCat.{u} := FibredSite.wEqualsLocallyBijective_associatedTopology B S hS p .etale
    letI : (FibredSite.associatedRingedTopos B S hS q hq .etale).J.WEqualsLocallyBijective
      AddCommGrpCat.{u} := FibredSite.wEqualsLocallyBijective_associatedTopology B S hS q .etale
    Nonempty ((projectionRingedToposHom B S hS G q hq hG eG).toModulesHom.pullbackModules ⋙
        (FibredSite.ringedToposMorphism B S hS p q hp hq f hf
          .etale).toModulesHom.pullbackModules ≅
      (smallEtaleRingedToposHom B S hS
            (inducedSpacesHom B S hS (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) p q eF eG f
              hf.comp_eq)).toModulesHom.pullbackModules ⋙
        (projectionRingedToposHom B S hS F p hp hF eF).toModulesHom.pullbackModules) := by
  let : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_equivalenceOver B S hS F p eF
  let : EssentiallySmall.{u} 𝒴 := essentiallySmall_of_equivalenceOver B S hS G q eG
  let : HasWeakSheafify (FibredSite.associatedRingedTopos B S hS p hp .etale).J
    AddCommGrpCat.{u} := FibredSite.hasWeakSheafify_associatedTopology B S hS p .etale
  let : HasWeakSheafify (FibredSite.associatedRingedTopos B S hS q hq .etale).J
    AddCommGrpCat.{u} := FibredSite.hasWeakSheafify_associatedTopology B S hS q .etale
  let : (FibredSite.associatedRingedTopos B S hS p hp .etale).J.WEqualsLocallyBijective
    AddCommGrpCat.{u} := FibredSite.wEqualsLocallyBijective_associatedTopology B S hS p .etale
  let : (FibredSite.associatedRingedTopos B S hS q hq .etale).J.WEqualsLocallyBijective
    AddCommGrpCat.{u} := FibredSite.wEqualsLocallyBijective_associatedTopology B S hS q .etale
  exact ⟨(RingedToposHom.pullbackModulesCompIso
        (X := FibredSite.associatedRingedTopos B S hS p hp .etale)
        (Y := FibredSite.associatedRingedTopos B S hS q hq .etale)
        (Z := smallEtaleRingedTopos B S hS ⟨G, hG⟩) _ _).symm ≪≫
      (restrictionRingedSquareOfInduced B S hS F G p q hp hq hF hG eF eG f
        hf).pullbackModulesIso ≪≫
      RingedToposHom.pullbackModulesCompIso
        (X := FibredSite.associatedRingedTopos B S hS p hp .etale)
        (Y := smallEtaleRingedTopos B S hS ⟨F, hF⟩)
        (Z := smallEtaleRingedTopos B S hS ⟨G, hG⟩) _ _⟩

end AlgebraicGeometry.Space

end
