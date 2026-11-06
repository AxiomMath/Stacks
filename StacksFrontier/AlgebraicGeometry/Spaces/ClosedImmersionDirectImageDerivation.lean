module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionCommRingCounitSquare
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.Differentials
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleSourceLocalization
public import StacksFrontier.Cotangent.SheavesOfRings.InverseImageDerivations

/-!
# Derivations of the direct image of the structure sheaf of a closed subspace

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over `B` and `b : X ⟶ B` a structure
morphism.  The descent of derivations along the structure map
`i♯_direct : 𝒪_X ⟶ i_*𝒪_Z`, which is where the defining ideal sheaf of `Z` is literally the
kernel, produces derivations of `i_*𝒪_Z` on the small étale site of `X`.  This file carries those
to derivations of `𝒪_Z` on the small étale site of `Z`, which is what the universal property of
`Ω_{Z/B}` consumes.

## Main definitions

* `AlgebraicGeometry.Space.directImageDerivationEquiv`: the bijection
  `Der_B(i_*𝒪_Z, i_*W) ≃ Der_B(𝒪_Z, W)`.

## Main results

* `AlgebraicGeometry.Space.directImageDerivationEquiv_postcomp`: the bijection is natural in
  the coefficient module, which is what makes it usable in a corepresentability argument.

## Implementation notes

The bijection is two known ones composed, in the shape the four-bijection assembly of
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsEtaleSourceLocalization.lean` uses for
the étale-source case:

* `Stacks.Sheaves.RingedToposModules.inverseImageDerivationEquiv`, the derivation-level half of
  Stacks 08TQ, at `P := i_*𝒪_Z`.  It transposes a derivation of `i_*𝒪_Z` with values in a direct
  image into a derivation of `i⁻¹i_*𝒪_Z` on the site of `Z`;
* `AlgebraicGeometry.SheafOfModules.derivationEquivOfRingDataIso` at the square
  `AlgebraicGeometry.Space.inverseImageStructureSharpCounit_square`, whose two isomorphisms are
  the comparison `i⁻¹b⁻¹𝒪_B ≅ (i ≫ b)⁻¹𝒪_B` of Stacks 03G8 and the commutative-ring counit
  `i⁻¹i_*𝒪_Z ≅ 𝒪_Z` of `AlgebraicGeometry.Space.commRingCounitIso`, invertible by Stacks 04E5,
  part (1).

**The coefficient module is left in the shape the transposition produces**, namely the direct
image of `W` with its scalars first restricted along the counit.  It is *not* rewritten to
`AlgebraicGeometry.Space.moduleDirectImage`: the two have the same underlying sheaf of sets, but
identifying their scalar actions is a separate step, and
`Stacks.Sheaves.RingedToposModules.directImageModulesRestrictScalarsIso` does **not** do it —
that lemma moves a restriction of scalars along a map of the *target* site's rings through the
direct image, whereas the counit is a map of the source site's rings and is not the inverse image
of anything.  A consumer joining this to the descent on the site of `X` owes that identification.

The closed-immersion hypothesis is used only through the counit, i.e. only to know that
`i⁻¹i_*𝒪_Z ⟶ 𝒪_Z` is invertible.

## References

* [Stacks Project, Tag 08TQ](https://stacks.math.columbia.edu/tag/08TQ), the derivation-level
  transposition.
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the composition law.
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5), part (1).
* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA), the conormal sequence,
  for whose exactness at the middle term this is an input.
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Z X Bb : AlgebraicSpaces B S hS}

/-- The base map of `i_*𝒪_Z` over `B`: the structure map of `b` followed by the direct-image form
of the structure map of `i`. -/
noncomputable abbrev directImageBase (i : Z ⟶ X) (b : X ⟶ Bb) :=
  (smallEtaleRingedToposHom B S hS b).fSharpInverseImage ≫ structureSharpCommRing B S hS i

/-- The commutative-ring counit `i⁻¹i_*𝒪_Z ≅ 𝒪_Z` at the structure sheaf of `Z`. -/
noncomputable abbrev structureCounitIso (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom) :=
  commRingCounitIso B S hS i hi (smallEtaleRingedTopos B S hS Z).O

/-- An `𝒪_Z`-module read as an `i⁻¹i_*𝒪_Z`-module along the counit.  This is the shape
`AlgebraicGeometry.SheafOfModules.derivationEquivOfRingDataIso` states its source at. -/
noncomputable abbrev counitRestrictScalars (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (W : Modules.{u, u} B S hS Z.1 Z.2) :=
  (SheafOfModules.restrictScalars
    ((Stacks.forgetCommRingSheaf.{u, u + 1, u} (SmallEtale.topology B S hS Z.1)).map
      (structureCounitIso B S hS i hi).hom)).obj W

/-- **`Der_B(i_*𝒪_Z, i_*W) ≃ Der_B(𝒪_Z, W)` for a closed immersion.**  A `B`-derivation of the
direct image `i_*𝒪_Z` with values in a direct image is a `B`-derivation of `𝒪_Z`: transpose it
across `i⁻¹ ⊣ i_*` by the derivation-level half of Stacks 08TQ, then carry it along the
commutative-ring counit `i⁻¹i_*𝒪_Z ≅ 𝒪_Z` and the comparison `i⁻¹b⁻¹𝒪_B ≅ (i ≫ b)⁻¹𝒪_B`, which
commute with the structure maps by
`AlgebraicGeometry.Space.inverseImageStructureSharpCounit_square`. -/
noncomputable def directImageDerivationEquiv (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (b : X ⟶ Bb)
    (W : Modules.{u, u} B S hS Z.1 Z.2) :
    PresheafOfModulesOfCommRing.Derivation'
      ((directImageModules (smallEtaleRingedToposHom B S hS i).toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf
            ((pushforwardCommRingFunctor (smallToposMorphismTypeU B S hS i)).obj
              (smallEtaleRingedTopos B S hS Z).O))).obj
        (counitRestrictScalars B S hS i hi W)).val
      (directImageBase B S hS i b).hom ≃
      PresheafOfModulesOfCommRing.Derivation' W.val
        ((smallEtaleRingedToposHom B S hS (i ≫ b)).fSharpInverseImage).hom :=
  (inverseImageDerivationEquiv (smallEtaleRingedToposHom B S hS i).toToposHom
      (directImageBase B S hS i b) (counitRestrictScalars B S hS i hi W)).symm.trans
    (AlgebraicGeometry.SheafOfModules.derivationEquivOfRingDataIso
      ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS i b).app
        (smallEtaleRingedTopos B S hS Bb).O)
      (structureCounitIso B S hS i hi)
      (inverseImageStructureSharpCounit_square B S hS i hi b) W)

/-- **The bijection is natural in the coefficient module.**  Both factors are, and that is what
makes it usable in a corepresentability argument: `inverseImageDerivationEquiv_symm_postcomp`
for the transposition, `AlgebraicGeometry.Space.derivationEquivOfRingDataIso_postcomp` for the
transport along the ring data. -/
lemma directImageDerivationEquiv_postcomp (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (b : X ⟶ Bb)
    {W W' : Modules.{u, u} B S hS Z.1 Z.2} (k : W ⟶ W')
    (D : PresheafOfModulesOfCommRing.Derivation'
      ((directImageModules (smallEtaleRingedToposHom B S hS i).toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf
            ((pushforwardCommRingFunctor (smallToposMorphismTypeU B S hS i)).obj
              (smallEtaleRingedTopos B S hS Z).O))).obj
        (counitRestrictScalars B S hS i hi W)).val
      (directImageBase B S hS i b).hom) :
    directImageDerivationEquiv B S hS i hi b W'
        (D.postcomp ((directImageModules (smallEtaleRingedToposHom B S hS i).toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf
            ((pushforwardCommRingFunctor (smallToposMorphismTypeU B S hS i)).obj
              (smallEtaleRingedTopos B S hS Z).O))).map
          ((SheafOfModules.restrictScalars
            ((Stacks.forgetCommRingSheaf.{u, u + 1, u} (SmallEtale.topology B S hS Z.1)).map
              (structureCounitIso B S hS i hi).hom)).map k)).val) =
      (directImageDerivationEquiv B S hS i hi b W D).postcomp k.val :=
  (congrArg (SheafOfModules.derivationEquivOfRingDataIso
        ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS i b).app
          (smallEtaleRingedTopos B S hS Bb).O) _
        (inverseImageStructureSharpCounit_square B S hS i hi b) W')
      (inverseImageDerivationEquiv_symm_postcomp _ _ _ D).symm).trans
    (derivationEquivOfRingDataIso_postcomp _ _ _ k _)

end AlgebraicGeometry.Space

end
