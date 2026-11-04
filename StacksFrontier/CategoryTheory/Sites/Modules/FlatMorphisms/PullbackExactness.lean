module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.ChangeOfRingsReduction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.InverseImageExactness
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.FlatPullbackExact

/-!
# Exactness of the abstract module pullback along a flat morphism of ringed topoi

Let `f : (Sh(C), O_X) ⟶ (Sh(D), O_Y)` be a morphism of ringed topoi whose geometric part is
presented by a continuous functor `f.u : D.C ⥤ X.C` between the underlying sites. If `f` is
flat — that is, if the inverse-image form `f⁻¹O_Y ⟶ O_X` of its structure map is a flat
morphism of sheaves of rings — and `f.u` is a morphism of sites, then the pullback of sheaves
of modules along `f` is exact.

The pullback here is `AlgebraicGeometry.RingedToposSiteHom.pullbackTopos`, Mathlib's
`SheafOfModules.pullback`, defined as the left adjoint of the pushforward. The argument is the
factorization `f^* ≅ g^* ⋙ h^*` of
`StacksPullbackFactorization.pullbackFactorIso` into the inverse image with no change of rings
followed by extension of scalars along `f⁻¹O_Y ⟶ O_X`, together with left exactness of each
factor:

* `g^*` is left exact because `f.u` is a morphism of sites, which is
  `Stacks.Sheaves.InverseImageExactness.preservesFiniteLimits_pullbackTopos_auxHomG`;
* `h^*` is left exact because `f` is flat, which is
  `Stacks.Sheaves.RingedToposModules.extendScalars_preservesFiniteLimits`.

Right exactness needs neither hypothesis: `f^*` is a left adjoint.

## Main results

* `AlgebraicGeometry.RingedToposSiteHom.pullbackTopos_preservesFiniteLimits`: the pullback of
  sheaves of modules along a flat morphism of ringed topoi is left exact.
* `AlgebraicGeometry.RingedToposSiteHom.pullbackTopos_preservesFiniteColimits`: it is right
  exact, with no hypothesis.
* `AlgebraicGeometry.RingedToposSiteHom.pullbackTopos_exact`: it is exact.

## Implementation notes

**Flatness is spelled out rather than named.** The hypothesis is
`AlgebraicGeometry.SheafOfModules.IsFlatMapULift (StacksPullbackFactorization.auxHomH f).fSharp`,
and `(auxHomH f).fSharp` *is* the inverse-image form `f⁻¹O_Y ⟶ O_X` of the structure map of `f`:
it is the adjunct of `f.fSharp` under the inverse-image/direct-image adjunction on sheaves of
commutative rings, and the direct image along the identity functor of the site is the identity
on the nose, so no comparison intervenes. So this is exactly the condition that
`AlgebraicGeometry.RingedToposHom.IsFlat` imposes, read at the presentation of the geometric
morphism that `pullbackTopos` is available for. No new flatness predicate is introduced and no
comparison of two flatness predicates is asserted.

**The morphism-of-sites hypothesis is not an extra assumption on the source's statement.** A
`RingedToposSiteHom` carries only a *continuous* functor, which does not by itself induce a
morphism of topoi; `AlgebraicGeometry.RingedToposSiteHom.toToposHom` needs precisely
`f.u.IsMorphismOfSites`, and it is that condition which makes `f⁻¹` on sheaves of sets left
exact. So `hmos` is what makes `f` a morphism of ringed *topoi* at all, which the source assumes
outright.

**This is the assertion of Stacks 04JC at the other pullback of this development, so it carries
no tag.** The tag is registered on
`Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap`, which is the same
assertion for the pullback that Stacks 03D6 part (2) *constructs* from the inverse image of
Stacks 03D2. Neither statement follows from the other: the two pullbacks are left adjoints of
two pushforwards that are identified only through the comparison of the transported and the
restriction direct images, which is why both have to be proved, and the proofs share the
change-of-rings half and differ in the geometric half.

**Universes.** Both ringed topoi are at `AlgebraicGeometry.RingedTopos.{u, u, u}`. The narrowing
is inherited, not chosen here; its four independent forcings on this chain are recorded in the
implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/ChangeOfRingsReduction.lean`.

## References

* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open StacksPullbackFactorization

noncomputable section

universe u

namespace AlgebraicGeometry.RingedToposSiteHom

variable {X Y : RingedTopos.{u, u, u}} (f : RingedToposSiteHom X Y)

/-- **The change-of-rings half.** Extension of scalars along the inverse-image form
`f⁻¹O_Y ⟶ O_X` of the structure map of `f` is left exact when that map is flat.

`StacksPullbackFactorization.pullbackTopos_auxHomH` identifies `h^*` with extension of scalars
along that map; `Stacks.Sheaves.DerivedPullback.FlatExtendScalars.extendScalarsIsoChangeOfRings`
identifies the abstract extension of scalars, defined as a left adjoint, with the sheafified
sectionwise tensor product, for which left exactness under flatness is
`Stacks.Sheaves.RingedToposModules.extendScalars_preservesFiniteLimits`. -/
theorem pullbackTopos_auxHomH_preservesFiniteLimits
    (hf : SheafOfModules.IsFlatMapULift.{u, u, u} (auxHomH f).fSharp) :
    PreservesFiniteLimits (auxHomH f).pullbackTopos :=
  @preservesFiniteLimits_of_natIso _ _ _ _ _ _
    (Stacks.Sheaves.DerivedPullback.FlatExtendScalars.extendScalarsIsoChangeOfRings
      (auxHomH f).fSharp).symm
    (Stacks.Sheaves.RingedToposModules.extendScalars_preservesFiniteLimits
      (auxTopos f).J (auxHomH f).fSharp hf)

/-- **Stacks 04JC for the abstract module pullback, left exactness.** The pullback of sheaves of
modules along a flat morphism of ringed topoi preserves finite limits.

`f^* ≅ g^* ⋙ h^*`, the inverse image with no change of rings followed by extension of scalars
along `f⁻¹O_Y ⟶ O_X`; the first factor is left exact because `f.u` is a morphism of sites and
the second because `f` is flat. -/
theorem pullbackTopos_preservesFiniteLimits (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (hf : SheafOfModules.IsFlatMapULift.{u, u, u} (auxHomH f).fSharp) :
    PreservesFiniteLimits f.pullbackTopos :=
  have : PreservesFiniteLimits (auxHomG f).pullbackTopos :=
    Stacks.Sheaves.InverseImageExactness.preservesFiniteLimits_pullbackTopos_auxHomG f hmos
  have : PreservesFiniteLimits (auxHomH f).pullbackTopos :=
    pullbackTopos_auxHomH_preservesFiniteLimits f hf
  have : PreservesFiniteLimits ((auxHomG f).pullbackTopos ⋙ (auxHomH f).pullbackTopos) :=
    comp_preservesFiniteLimits _ _
  preservesFiniteLimits_of_natIso (pullbackFactorIso f)

/-- **Stacks 04JC for the abstract module pullback, right exactness.** The pullback of sheaves
of modules is a left adjoint, so it preserves finite colimits. Neither flatness nor the
morphism-of-sites condition is used. -/
theorem pullbackTopos_preservesFiniteColimits :
    PreservesFiniteColimits f.pullbackTopos :=
  have : PreservesColimitsOfSize.{0, 0} f.pullbackTopos :=
    f.pullbackPushforwardAdjunctionTopos.leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- **Stacks 04JC for the abstract module pullback.** The pullback of sheaves of modules along a
flat morphism of ringed topoi is exact. -/
theorem pullbackTopos_exact (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (hf : SheafOfModules.IsFlatMapULift.{u, u, u} (auxHomH f).fSharp) :
    exactFunctor (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) f.pullbackTopos :=
  (exactFunctor_iff f.pullbackTopos).2
    ⟨pullbackTopos_preservesFiniteLimits f hmos hf, pullbackTopos_preservesFiniteColimits f⟩

end AlgebraicGeometry.RingedToposSiteHom

end

end
