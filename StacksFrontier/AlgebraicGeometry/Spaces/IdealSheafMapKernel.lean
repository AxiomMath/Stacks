module

public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafMapVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureProjectionComposition

/-!
# The map of defining ideal sheaves of a chain of closed subspaces

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let
`Y, Z ⊆ X` be closed subspaces with `Z ⊆ Y`, and write `j : Y ⟶ X` for the inclusion.  Since
`Z ⊆ Y` the defining ideal sheaf of `Y` is contained in that of `Z`, so there is an inclusion
`𝓘_Y ⟶ 𝓘_Z` of `𝒪_X`-modules.  This file builds that inclusion and shows that its inverse
image along `j`, followed by the map `j^*𝓘_Z ⟶ 𝓘_W` of [Stacks Project, Tag 04CP] attached to
any closed subspace `W ⊆ Y` sent into `Z` by `j`, vanishes.

So `j^*𝓘_Y ⟶ j^*𝓘_Z ⟶ 𝓘_W` is a complex of `𝒪_Y`-modules: the sequence of ideal sheaves
underlying the conormal sequence of a chain of closed subspaces, whose vanishing clause at the
level of conormal modules is
`AlgebraicGeometry.Space.conormalMap_comp_conormalMap_eq_zero`.

## Main definitions

* `AlgebraicGeometry.Space.definingIdealSheafHomOfLe`: for `Z ⊆ Y` the inclusion
  `𝓘_Y ⟶ 𝓘_Z` of defining ideal sheaves, which exists by the inclusion-reversal clause of
  [Stacks Project, Tag 03MB].

## Main results

* `AlgebraicGeometry.Space.definingIdealSheafHomOfLe_comp_ι` and
  `AlgebraicGeometry.Space.mono_definingIdealSheafHomOfLe`: the inclusion of defining ideal
  sheaves is compatible with their inclusions into `𝒪_X`, and is a monomorphism.
* `AlgebraicGeometry.Space.homEquiv_idealSheafMap_comp_pushforward_ι`: the transpose of the map
  of defining ideal sheaves of a commutative square, read inside the direct image of the
  structure sheaf.  This is `AlgebraicGeometry.Space.idealSheafMap_comp_definingIdealSheaf_ι`
  transposed along the adjunction of [Stacks Project, Tag 03D7], the transpose of the canonical
  comparison `g^*𝒪_{X'} ⟶ 𝒪_X` being the canonical morphism `𝒪_{X'} ⟶ g_*𝒪_X` by
  `AlgebraicGeometry.Space.structureProjectionOfHom_eq_homEquiv_structureModulePullbackMap`.
* `AlgebraicGeometry.Space.modulePullback_definingIdealSheaf_ι_comp_structureModulePullbackMap`:
  the inverse image along `j` of the inclusion `𝓘_Y ⊆ 𝒪_X`, read in `𝒪_Y`, vanishes.
* `AlgebraicGeometry.Space.modulePullback_definingIdealSheafHomOfLe_comp_idealSheafMap`: the
  inverse image along `j` of the inclusion `𝓘_Y ⊆ 𝓘_Z`, followed by the map `j^*𝓘_Z ⟶ 𝓘_W` of
  [Stacks Project, Tag 04CP], vanishes.

## What is not proved

**The kernel of the map is not computed.**  The transpose `𝓘_Z ⟶ j_*𝓘_W` of the map of
[Stacks Project, Tag 04CP] has, for `W` the inverse image of `Z` along `j`, the inclusion
`𝓘_Y ⟶ 𝓘_Z` as its kernel, and that — together with surjectivity of the transpose — is what
the exactness in the middle of [Stacks Project, Tag 06BD] reduces to.  It is **not** proved
here.  Every mathematical input is available:
`AlgebraicGeometry.Space.homEquiv_idealSheafMap_comp_pushforward_ι` above moves the computation
to `X`, `AlgebraicGeometry.Space.definingIdealSheafIsoKernel` presents `𝓘_Y` as the kernel of
the structure projection `𝒪_X ⟶ j_*𝒪_Y`, and the inclusion `𝓘_Z ⊆ 𝒪_X` is a monomorphism.
What blocks it is spelling, not mathematics: the statement of the kernel fork needs the zero
morphism of a hom-type whose two ends are spelled one as an
`AlgebraicGeometry.Space.Modules` and the other as a `SheafOfModules` over the structure ring
sheaf, and the universal property's uniqueness clause exhausts the heartbeat
budget at `whnf` on such a goal.

## Implementation notes

**Why the vanishing is computed at the upper subspace `⊤`.**  The inverse image along `j` of the
inclusion `𝓘_Y ⊆ 𝒪_X`, read in `𝒪_Y`, is the map of [Stacks Project, Tag 04CP] at the square
with lower subspace `Y` and *any* upper subspace, followed by that upper subspace's inclusion
into `𝒪_Y`.  Taking the upper subspace to be `⊤` makes the map itself vanish, by
`AlgebraicGeometry.Space.idealSheafMap_eq_zero_of_factorization` — `j` factors through `Y` by
the identity of `Y` — and so avoids any computation with the inclusion.

**Why the statements are at a variable upper subspace.**  The configuration this file is used in
has `W` the inverse image of `Z` along `j`, but nothing in the argument uses that: the upper
subspace, the vertical morphism and the commutativity of the square are taken as variables, and
the consumer instantiates them.  Keeping the concrete fibre-product spelling out of the
statements is what makes the elaboration cheap.

**Why the zero morphisms are ascribed.**  `AlgebraicGeometry.Space.Modules` and the
`SheafOfModules` over the structure ring sheaf that a defining ideal sheaf's
`toSheafOfModules` lands in are the same type, but the zero morphisms are found only at the
first spelling, so each statement asserting that a composite vanishes ascribes the end that
would otherwise be read at the second.  This is the same device as
`AlgebraicGeometry.Space.idealSheafMap_eq_zero_of_factorization`.

## References

* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP), the map of defining
  ideal sheaves of a commutative square.
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), the defining ideal
  sheaf and its inclusion-reversal.
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7), the adjunction.
* [Stacks Project, Tag 06BD](https://stacks.math.columbia.edu/tag/06BD), the conormal sequence
  of a chain of immersions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The inclusion of defining ideal sheaves of a chain of closed subspaces -/

section HomOfLe

variable {X : AlgebraicSpaces B S hS} (Y Z : ClosedSubspaces B S hS X.1)

/-- **The inclusion `𝓘_Y ⊆ 𝓘_Z` of defining ideal sheaves of a chain of closed subspaces.**  For
`Z ⊆ Y` the defining ideal sheaf of `Y` is contained in that of `Z`, by the inclusion-reversal
clause of [Stacks Project, Tag 03MB]
(`AlgebraicGeometry.Space.definingIdealSheaf_antitone`), so the inclusion of `𝓘_Y` into `𝒪_X`
factors through `𝓘_Z`. -/
def definingIdealSheafHomOfLe (hZY : Z.1 ≤ Y.1) :
    (definingIdealSheaf B S hS X Y).toSheafOfModules ⟶
      (definingIdealSheaf B S hS X Z).toSheafOfModules :=
  (definingIdealSheaf B S hS X Z).factorThru (definingIdealSheaf B S hS X Y).ι
    fun U x ↦ definingIdealSheaf_antitone B S hS X Z Y hZY U x.2

/-- The inclusion of defining ideal sheaves is compatible with their inclusions into `𝒪_X`. -/
@[reassoc]
theorem definingIdealSheafHomOfLe_comp_ι (hZY : Z.1 ≤ Y.1) :
    definingIdealSheafHomOfLe B S hS Y Z hZY ≫ (definingIdealSheaf B S hS X Z).ι =
      (definingIdealSheaf B S hS X Y).ι :=
  (definingIdealSheaf B S hS X Z).factorThru_ι _ _

/-- The inclusion of defining ideal sheaves is a monomorphism, its composite with the
monomorphism `𝓘_Z ⊆ 𝒪_X` being the monomorphism `𝓘_Y ⊆ 𝒪_X`. -/
theorem mono_definingIdealSheafHomOfLe (hZY : Z.1 ≤ Y.1) :
    Mono (definingIdealSheafHomOfLe B S hS Y Z hZY) :=
  mono_of_mono_fac (definingIdealSheafHomOfLe_comp_ι B S hS Y Z hZY)

end HomOfLe

/-! ### The transpose of the map of defining ideal sheaves -/

section Transpose

variable {X X' : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
    (Z' : ClosedSubspaces B S hS X'.1) (g : X ⟶ X')
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')

/-- **The transpose of the map of defining ideal sheaves, read inside the structure sheaf.**  The
transpose `𝓘' ⟶ g_*𝓘` along the adjunction of [Stacks Project, Tag 03D7] of the map
`g^*𝓘' ⟶ 𝓘` of [Stacks Project, Tag 04CP], followed by the direct image of the inclusion
`𝓘 ⊆ 𝒪_X`, is the inclusion `𝓘' ⊆ 𝒪_{X'}` followed by the canonical morphism
`𝒪_{X'} ⟶ g_*𝒪_X`.

This is `AlgebraicGeometry.Space.idealSheafMap_comp_definingIdealSheaf_ι` transposed: the two
naturalities of `CategoryTheory.Adjunction.homEquiv` move the transpose past the two inclusions,
and
`AlgebraicGeometry.Space.structureProjectionOfHom_eq_homEquiv_structureModulePullbackMap`
identifies the transpose of the canonical comparison `g^*𝒪_{X'} ⟶ 𝒪_X` with the canonical
morphism `𝒪_{X'} ⟶ g_*𝒪_X`. -/
theorem homEquiv_idealSheafMap_comp_pushforward_ι :
    (modulePullbackAdjunction B S hS g).homEquiv _ _
          (idealSheafMap B S hS Z Z' g f hsq) ≫
        (modulePushforward B S hS g).map (definingIdealSheaf B S hS X Z).ι =
      (definingIdealSheaf B S hS X' Z').ι ≫ structureProjectionOfHom B S hS g := by
  refine Eq.trans ((modulePullbackAdjunction B S hS g).homEquiv_naturality_right
    (idealSheafMap B S hS Z Z' g f hsq) (definingIdealSheaf B S hS X Z).ι).symm ?_
  refine Eq.trans (congrArg ((modulePullbackAdjunction B S hS g).homEquiv _ _)
    (idealSheafMap_comp_definingIdealSheaf_ι B S hS Z Z' g f hsq)) ?_
  refine Eq.trans ((modulePullbackAdjunction B S hS g).homEquiv_naturality_left
    (definingIdealSheaf B S hS X' Z').ι (structureModulePullbackMap B S hS g)) ?_
  exact congrArg (fun m ↦ (definingIdealSheaf B S hS X' Z').ι ≫ m)
    (structureProjectionOfHom_eq_homEquiv_structureModulePullbackMap B S hS g).symm

end Transpose

/-! ### The kernel of the transpose -/

section Kernel

variable {X : AlgebraicSpaces B S hS} (Y Z : ClosedSubspaces B S hS X.1) (hZY : Z.1 ≤ Y.1)
    (W : ClosedSubspaces B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS).1)
    (p : (⟨W.1.toFunctor, W.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS) W ≫
        subspaceInclusion B S hS X Y =
      p ≫ subspaceInclusion B S hS X Z)

/-- **The inverse image along `j` of the inclusion `𝓘_Y ⊆ 𝒪_X`, read in `𝒪_Y`, vanishes.**  A
regular function vanishing on `Y` restricts to zero on `Y`.

The computation is made at the upper subspace `⊤`, whose defining ideal sheaf includes into the
structure sheaf by the zero morphism: by
`AlgebraicGeometry.Space.idealSheafMap_comp_definingIdealSheaf_ι` the composite in question is
the map `j^*𝓘_Y ⟶ 𝓘_⊤` of [Stacks Project, Tag 04CP] for the square with lower edge `j` and
lower subspace `Y`, followed by that inclusion, and the map itself vanishes by
`AlgebraicGeometry.Space.idealSheafMap_eq_zero_of_factorization`, `j` factoring through `Y` by
the identity of `Y`. -/
theorem modulePullback_definingIdealSheaf_ι_comp_structureModulePullbackMap :
    (show (modulePullback B S hS (subspaceInclusion B S hS X Y)).obj
          (definingIdealSheaf B S hS X Y).toSheafOfModules ⟶
        (show Modules.{u, u} B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS).1
            (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS).2 from
          SheafOfModules.unit
            (structureRingSheaf B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS))) from
      (modulePullback B S hS (subspaceInclusion B S hS X Y)).map
          (definingIdealSheaf B S hS X Y).ι ≫
        structureModulePullbackMap B S hS (subspaceInclusion B S hS X Y)) = 0 := by
  let T : ClosedSubspaces B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS).1 :=
    ⟨⊤, isClosedSubspace_top B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS)⟩
  have hzero := idealSheafMap_eq_zero_of_factorization B S hS T Y (subspaceInclusion B S hS X Y)
    (subspaceInclusion B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS) T) rfl
    (𝟙 (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS)) (Category.id_comp _)
  exact (idealSheafMap_comp_definingIdealSheaf_ι B S hS T Y (subspaceInclusion B S hS X Y)
    (subspaceInclusion B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS) T)
    rfl).symm.trans ((congrArg (· ≫ _) hzero).trans zero_comp)

/-- The inverse image along `j` of the inclusion `𝓘_Y ⊆ 𝓘_Z`, followed by the map
`j^*𝓘_Z ⟶ 𝓘_W` of [Stacks Project, Tag 04CP], vanishes.

The inclusion `𝓘_W ⊆ 𝒪_Y` is a monomorphism, so it is enough to check this after it, where
`AlgebraicGeometry.Space.idealSheafMap_comp_definingIdealSheaf_ι` turns the composite into the
inverse image of the inclusion `𝓘_Y ⊆ 𝒪_X` read in `𝒪_Y`, which is zero. -/
theorem modulePullback_definingIdealSheafHomOfLe_comp_idealSheafMap :
    (show (modulePullback B S hS (subspaceInclusion B S hS X Y)).obj
          (definingIdealSheaf B S hS X Y).toSheafOfModules ⟶
        (show Modules.{u, u} B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS).1
            (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS).2 from
          (definingIdealSheaf B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS)
            W).toSheafOfModules) from
      (modulePullback B S hS (subspaceInclusion B S hS X Y)).map
          (definingIdealSheafHomOfLe B S hS Y Z hZY) ≫
        idealSheafMap B S hS W Z (subspaceInclusion B S hS X Y) p hsq) = 0 := by
  refine (cancel_mono
    (definingIdealSheaf B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS) W).ι).mp ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun m ↦ _ ≫ m)
    (idealSheafMap_comp_definingIdealSheaf_ι B S hS W Z
      (subspaceInclusion B S hS X Y) p hsq)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun m ↦ m ≫ structureModulePullbackMap B S hS
    (subspaceInclusion B S hS X Y))
    (((modulePullback B S hS (subspaceInclusion B S hS X Y)).map_comp
      (definingIdealSheafHomOfLe B S hS Y Z hZY)
      (definingIdealSheaf B S hS X Z).ι).symm.trans
      (congrArg (modulePullback B S hS (subspaceInclusion B S hS X Y)).map
        (definingIdealSheafHomOfLe_comp_ι B S hS Y Z hZY)))) ?_
  exact (modulePullback_definingIdealSheaf_ι_comp_structureModulePullbackMap
    B S hS Y).trans zero_comp.symm

end Kernel

end AlgebraicGeometry.Space

end
