module

public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.FlatPullbackExact
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Sheaf.HasSheafComposeForgetRing
public import StacksFrontier.Deformation.ToposThickening.PushforwardComparison.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPushforwardComp
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksCore.Tactic.StacksAttribute

/-!
# Flat direct image preserves K-injective complexes

**Stacks 093Y.** For a *flat* morphism of ringed topoi
`(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and a K-injective complex `I` of `O_C`-modules, the
degreewise direct image `f_*I` is a K-injective complex of `O_D`-modules.

Flatness is Stacks 04JB, `AlgebraicGeometry.RingedToposHom.IsFlat`: the ring map
`f♯ : f⁻¹O_D ⟶ O_C` is flat, i.e. `O_C` is a flat `f⁻¹O_D`-module. Nothing else is assumed
of `f`.

## Main results

* `AlgebraicGeometry.RingedToposHom.pullbackModules_preservesFiniteLimits_of_isFlat`: for a
  flat morphism, the pullback of sheaves of modules is left exact — the half of Stacks 04JC
  that carries the flatness hypothesis.
* `AlgebraicGeometry.RingedToposHom.pushforwardModules_isKInjective_of_isFlat`:
  **Stacks 093Y.**

## Implementation notes

The source's proof is the adjunction `Hom_{K(O_D)}(F, f_*I) = Hom_{K(O_C)}(f^*F, I)` of
Stacks 03D7 together with exactness of `f^*`: an acyclic `F` has acyclic pullback, which
K-injectivity of `I` then kills. That implication, over an arbitrary adjunction of additive
functors between abelian categories, is Stacks 08BJ,
`CochainComplex.isKInjective_mapHomologicalComplex_of_exact`. So the only content specific to
this tag is exactness of `f^*`, which is where flatness enters and which Stacks 04JC supplies
as `Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap`. Right exactness of
`f^*` is free — it is a left adjoint — but both halves of that conjunction are passed on,
since the criterion asks for exactness.

This is the same reduction that Stacks 0730 makes for injective *objects* in
`AlgebraicGeometry.RingedToposHom.pushforwardModules_injective`, with the preservation of
monomorphisms there replaced by the preservation of acyclicity here.

The direct image is `AlgebraicGeometry.RingedToposHom.pushforwardModules`, Stacks 03D6
part (1) for the two-field morphism of ringed topoi of Stacks 01D3 part (2) — the Stacks 03D1
direct image followed by restriction of scalars along the direct-image form `f♯` of the
structure map. The pullback adjoint to it is taken in the spelling Stacks 04JC proves exact,
over the four-field `toRingedToposModulesHom`, and the adjunction between the two is
`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModulesViaComparison`. No comparison
of the development's two spellings of `f_*` is needed: that comparison is already inside that
adjunction, as `pushforwardModulesIso`.

Flatness of a morphism of sheaves of commutative rings is asserted after lifting the section
rings into a universe containing the site — this is what
`AlgebraicGeometry.SheafOfModules.IsFlatMapULift`, which `IsFlat` unfolds to, does — because
the tensor product of sheaves of modules needs sheafification of presheaves of abelian groups,
which is unavailable for an arbitrary universe of sections. At a site whose objects, morphisms
and sections share one universe the lift is invisible,
`AlgebraicGeometry.SheafOfModules.isFlatMapULift_iff_isFlatMap`.

The `CategoryTheory.GrothendieckTopology.HasSheafCompose` witnesses for the underlying-set and
underlying-group forgetful functors are the global instances of
`StacksFrontier.CategoryTheory.Sites.Sheaf.HasSheafComposeForgetRing`, which is why they are not
hypotheses here; the remaining instance arguments are what make sheaves of modules on the two
sites abelian categories, so that complexes of them have K-injectivity at all. The two ringed
topoi share the universe of their sections, as they do in Stacks 04JC, and keep independent
universes for their sites.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 0730](https://stacks.math.columbia.edu/tag/0730)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
* [Stacks Project, Tag 093Y](https://stacks.math.columbia.edu/tag/093Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Sheaves.RingedToposModules

universe v u v' u' w

namespace AlgebraicGeometry.RingedToposHom

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Pullback of sheaves of modules along a *flat* morphism of ringed topoi is left exact. This
is the left-exactness half of Stacks 04JC,
`Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap`, and the only place
flatness is used in Stacks 093Y. -/
theorem pullbackModules_preservesFiniteLimits_of_isFlat
    (f : RingedToposHom X Y) (hf : f.IsFlat) :
    PreservesFiniteLimits (f.toRingedToposModulesHom.pullbackModules) :=
  ((exactFunctor_iff _).mp (pullbackModules_exact_of_isFlatMap f hf)).1

/-- **Stacks 093Y.** Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a *flat* morphism of ringed
topoi — flat in the sense of Stacks 04JB, that the ring map `f♯ : f⁻¹O_D ⟶ O_C` is flat — and
let `I` be a K-injective complex of `O_C`-modules. Then the degreewise direct image `f_*I` is a
K-injective complex of `O_D`-modules.

The proof is the source's. The adjunction `f^* ⊣ f_*` of Stacks 03D7 identifies
`Hom_{K(O_D)}(F, f_*I)` with `Hom_{K(O_C)}(f^*F, I)`; flatness makes `f^*` exact (Stacks 04JC),
so it carries an acyclic `F` to an acyclic `f^*F`, on which K-injectivity of `I` makes every
morphism into `I` null-homotopic. That is Stacks 08BJ applied to this adjunction. -/
@[stacks 093Y, sga "4 V 4.9" "more general"]
theorem pushforwardModules_isKInjective_of_isFlat
    (f : RingedToposHom X Y) (hf : f.IsFlat)
    (I : CochainComplex (SheafOfModules.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      ((f.pushforwardModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  have hadj : f.toRingedToposModulesHom.pullbackModules ⊣ f.pushforwardModules :=
    f.pullbackAdjPushforwardModulesViaComparison
  have : (f.toRingedToposModulesHom.pullbackModules).Additive := hadj.left_adjoint_additive
  have := f.pullbackModules_preservesFiniteLimits_of_isFlat hf
  have : PreservesFiniteColimits (f.toRingedToposModulesHom.pullbackModules) :=
    ((exactFunctor_iff _).mp (pullbackModules_exact_of_isFlatMap f hf)).2
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ _ hadj I

end AlgebraicGeometry.RingedToposHom

end
