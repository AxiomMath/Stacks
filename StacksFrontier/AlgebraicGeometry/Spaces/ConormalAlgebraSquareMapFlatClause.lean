module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraSquareMapDegreePropagation
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeFlat

/-!
# The flat clause of Stacks 09RT

Let a commutative square of algebraic spaces over a scheme `S` be given, together with an ambient
homomorphism `Ψ` as in [Stacks Project, Tag 09RS], and let

`χ : g^*(⨁_{n ≥ 0} (𝓘')ⁿ) ⟶ ⨁_{n ≥ 0} 𝓘ⁿ`

be the ambient comparison `AlgebraicGeometry.Space.conormalAlgebraSquareAmbientComparison`.  This
file proves the second assertion of [Stacks Project, Tag 09RT]: **if `g` is flat then the
canonical map `f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X,*}` of Stacks 09RS is an isomorphism in every nonnegative
degree.**

The two halves are proved separately and have different sources.

* **Surjectivity in every degree** comes from degrees zero and one by
  `SheafOfModules.epi_unitalHom_app_of_nonneg`: the target of `χ` is the Rees graded algebra of
  `𝓘`, whose multiplication is locally surjective
  (`SheafOfModules.isLocallySurjective_reesMulPresheaf`), so a local section of `𝓘^{n + 1}` is
  locally a sum of products of a section of `𝓘ⁿ` and a section of `𝓘`.
* **Injectivity in every degree** comes from the flatness of `g`.  The compatibility square
  `hι` below says that `χ` in degree `n` followed by the embedding of `𝓘ⁿ` into `𝒪_X` is the
  inverse image along `g` of the embedding of `(𝓘')ⁿ` into `𝒪_{X'}` followed by
  `AlgebraicGeometry.Space.structureSheafMap`.  The embedding of a sheaf submodule is injective,
  the inverse image along a flat morphism is exact and therefore preserves injections
  (`AlgebraicGeometry.Space.exactFunctor_modulePullback_of_isFlat`), and
  `AlgebraicGeometry.Space.structureSheafMap` is invertible
  (`AlgebraicGeometry.Space.isIso_structureSheafMap`); so the right-hand side of the square is
  injective, hence so is `χ` in degree `n`.

The category of sheaves of modules on the small étale site is balanced, so surjective and
injective give invertible, and the factorisation (in the namespace `AlgebraicGeometry`)
`Space.isIso_conormalAlgebraSquareMapOfPullbackHom_app_of_isIso_ambientComparison` carries
invertibility down from the ambient space to `Z`.

## What is consumed and what is carried

**The flatness of `g` is genuinely consumed**: it is the hypothesis `hg`, and the proof of
`AlgebraicGeometry.Space.mono_conormalAlgebraSquareAmbientComparison_app_of_isFlat` uses it to
turn the injection `(𝓘')ⁿ ⟶ 𝒪_{X'}` into an injection after inverse image.  Without it that
step fails and nothing below goes through.

**The square being cartesian is not consumed.**  In the source it acts only through the
degree-one statement, and the degree-one statement is carried.  Four inputs are carried.

Neither the cartesian hypothesis nor the immersion hypotheses on `i` and `i'` appear below, not
even as unused parameters: as in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraSquareMapAmbientComparison.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraSquareMap.lean`, the statements are for an
arbitrary commutative square and arbitrary vertical arrows, so they are strictly more general
than the situation of Stacks 09RT and specialise to it.

* `hunit`, that `χ` carries the degree-zero unit.  This is a property of `Ψ`, not the conclusion
  of any named result: `AlgebraicGeometry.Space.conormalAlgebraSquareMapOfPullbackHom` takes `Ψ`
  as an *arbitrary* parameter, and at `Ψ = 0` the comparison carries the unit only if the unit of
  the target is zero.  A canonical `Ψ` is what would discharge it, and the module documentation
  of `StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraSquareMapAmbientComparison.lean`
  records what constructing one still needs.
* `h0`, invertibility of `χ` in degree zero.  In degree zero the ambient comparison is the map
  `g^*𝒪_{X'} ⟶ 𝒪_X` of structure sheaves, and this is the conclusion of
  `AlgebraicGeometry.Space.isIso_structureSheafMap`, transported to this square.
* `h1`, invertibility of `χ` in degree one.  In degree one the ambient comparison is the map
  `g^*(𝓘') ⟶ 𝓘` of ideal sheaves, and this is the conclusion of
  `AlgebraicGeometry.Space.isIso_idealSheafMap_of_isFlat` — the flat half of
  [Stacks Project, Tag 04CQ] — transported to this square.  It is **04CQ's conclusion and not
  09RT's**: the degree-one part of the canonical map of Stacks 09RS is the canonical map of
  conormal *modules* of [Stacks Project, Tag 04CP], about which 04CQ is the statement, and 04CQ
  is formalized and separately tagged.
* `hι`, the compatibility square above, at every nonnegative degree.  Its degree-one instance is
  proved as `AlgebraicGeometry.Space.idealSheafMap_comp_ι`.  It is a commuting square and not a
  surjectivity or injectivity claim, so carrying it discloses an input rather than restating the
  conclusion.

**Why `hι` is carried at every degree and not derived from its degree-one instance.**  The two
sides of the square are two morphisms out of `(g^*(⨁ (𝓘')ⁿ))_n`, so deriving the degree-`n`
instance from the degrees zero and one needs the *source* to be locally generated in degrees at
most one — that is, local surjectivity of the multiplication of a **pullback** of a sheaf of
graded algebras, not of a Rees algebra.  That is a statement about local sections of an inverse
image, and reading it off needs the chart-level description that
`AlgebraicGeometry.Space.smallToposMorphism_inverseImage_obj_obj` supplies only for an étale `g`;
it is the same geometric gap that blocks the construction of a canonical `Ψ`.  No local
surjectivity result for the multiplication of a pullback of sheaves of graded algebras is in the
library, so the induction cannot be run and the square is carried at each degree.

**What the transports of `h0` and `h1` are.**  The two degree-one results are stated for the
canonical preimage square of a **closed** subspace —
`AlgebraicGeometry.Space.preimageSubspace` with
`AlgebraicGeometry.Space.preimageProjection` and
`AlgebraicGeometry.Space.conormalEtaleRestrictionSquare` — whereas Stacks 09RT has an abstract
cartesian square whose vertical arrows are **immersions**.  Carrying `h0` and `h1` therefore
carries, besides 04CQ itself, the passage from that abstract square to the canonical one:
`AlgebraicGeometry.Space.kernelIdealSheaf` of the vertical arrow of a cartesian square has to be
identified with `AlgebraicGeometry.Space.idealSheaf` of the preimage subspace, and
`AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap` in degree one with
`AlgebraicGeometry.Space.idealSheafMap`.

**Both of those two identifications are now available**, and the claim that Base carries no such
passage outside the étale case is out of date for them: the first is
`AlgebraicGeometry.Space.kernelIdealSheaf_eq_definingIdealSheaf_preimageSubspace_of_isPullback`
of `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleBaseChangeCartesian.lean`, the second
`AlgebraicGeometry.Space.kernelIdealSquareMap_one_eq_idealSheafMap` of
`StacksFrontier/AlgebraicGeometry/Spaces/KernelIdealSquareMapDegreeOne.lean`, stated for
`AlgebraicGeometry.Space.kernelIdealSquareMap`, of which the ambient map is the second factor.
What Base still carries no passage for is the reduction of an abstract cartesian square of
**immersions** to the canonical preimage square of a closed subspace; that, and not either
identification, is what carrying `h0` and `h1` still owes.

## Main results

* `AlgebraicGeometry.Space.mono_conormalAlgebraSquareAmbientComparison_app_of_isFlat`: **the
  ambient comparison of a square along a flat morphism is injective in every nonnegative degree**,
  given the compatibility square.
* `AlgebraicGeometry.Space.isIso_conormalAlgebraSquareAmbientComparison_app_of_isFlat`: it is
  invertible in every nonnegative degree.
* `AlgebraicGeometry.Space.isIso_conormalAlgebraSquareMapOfPullbackHom_app_of_isFlat`: **the flat
  clause of [Stacks Project, Tag 09RT]** for the canonical map of [Stacks Project, Tag 09RS].

## References

* [Stacks Project, Tag 09RT](https://stacks.math.columbia.edu/tag/09RT)
* [Stacks Project, Tag 09RS](https://stacks.math.columbia.edu/tag/09RS)
* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {Z X X' Z' : AlgebraicSpaces B S hS}

/-- **The ambient comparison of a commutative square along a flat morphism is injective in every
nonnegative degree**, given that in each degree it is compatible with the embeddings of the
powers of the two ideal sheaves into the two structure sheaves.

The embedding of `(𝓘')ⁿ` into `𝒪_{X'}` is injective; the inverse image along a flat morphism is
exact and so preserves injections; and the map `g^*𝒪_{X'} ⟶ 𝒪_X` of structure sheaves is
invertible.  So the right-hand side of the compatibility square is injective, hence so is the
left, hence so is its first factor. -/
theorem mono_conormalAlgebraSquareAmbientComparison_app_of_isFlat (i : Z ⟶ X) (i' : Z' ⟶ X')
    (f : Z ⟶ Z') (g : X ⟶ X')
    (Ψ : (gradedPull (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS X') (smallEtaleRingedToposHom B S hS g)).obj
        (kernelIdealGradedAlgebra B S hS (f ≫ i')) ⟶ kernelIdealGradedAlgebra B S hS i)
    (hg : (smallEtaleRingedToposHom B S hS g).IsFlat)
    (hι : ∀ n : ℤ, 0 ≤ n →
      (conormalAlgebraSquareAmbientComparison B S hS i i' f g Ψ).app n ≫
          (kernelIdealSheafZPow B S hS i n).ι =
        (modulePullback B S hS g).map (kernelIdealSheafZPow B S hS i' n).ι ≫
          structureSheafMap B S hS g)
    (n : ℤ) (hn : 0 ≤ n) :
    Mono ((conormalAlgebraSquareAmbientComparison B S hS i i' f g Ψ).app n) := by
  have hpm : (modulePullback B S hS g).PreservesMonomorphisms :=
    have := ((exactFunctor_iff (modulePullback B S hS g)).mp
      (exactFunctor_modulePullback_of_isFlat B S hS g hg)).1
    inferInstance
  have hmi : Mono (kernelIdealSheafZPow B S hS i' n).ι := inferInstance
  have h1 : Mono ((modulePullback B S hS g).map (kernelIdealSheafZPow B S hS i' n).ι) :=
    @Functor.map_mono _ _ _ _ (modulePullback B S hS g) hpm _ _
      (kernelIdealSheafZPow B S hS i' n).ι hmi
  have h2 : Mono (structureSheafMap B S hS g) :=
    @IsIso.mono_of_iso _ _ _ _ (structureSheafMap B S hS g) (isIso_structureSheafMap B S hS g)
  have h3 : Mono ((modulePullback B S hS g).map (kernelIdealSheafZPow B S hS i' n).ι ≫
      structureSheafMap B S hS g) := @mono_comp _ _ _ _ _ _ h1 _ h2
  have h4 : Mono ((conormalAlgebraSquareAmbientComparison B S hS i i' f g Ψ).app n ≫
      (kernelIdealSheafZPow B S hS i n).ι) := by
    rw [hι n hn]
    exact h3
  exact mono_of_mono _ (kernelIdealSheafZPow B S hS i n).ι

/-- **The ambient comparison of a commutative square along a flat morphism is invertible in every
nonnegative degree**, given that it carries the unit, is invertible in the degrees zero and one,
and is compatible with the embeddings of the powers of the two ideal sheaves into the two
structure sheaves.

Surjectivity propagates from the degrees zero and one by
`SheafOfModules.epi_unitalHom_app_of_nonneg`; injectivity in each degree is
`AlgebraicGeometry.Space.mono_conormalAlgebraSquareAmbientComparison_app_of_isFlat`, which is
where the flatness of `g` is consumed; and the category of sheaves of modules on the small étale
site is abelian, hence balanced. -/
theorem isIso_conormalAlgebraSquareAmbientComparison_app_of_isFlat (i : Z ⟶ X) (i' : Z' ⟶ X')
    (f : Z ⟶ Z') (g : X ⟶ X')
    (Ψ : (gradedPull (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS X') (smallEtaleRingedToposHom B S hS g)).obj
        (kernelIdealGradedAlgebra B S hS (f ≫ i')) ⟶ kernelIdealGradedAlgebra B S hS i)
    (hg : (smallEtaleRingedToposHom B S hS g).IsFlat)
    (hunit : SheafOfModules.sectionsMap
        ((conormalAlgebraSquareAmbientComparison B S hS i i' f g Ψ).app 0)
        ((gradedPull (X := smallEtaleRingedTopos B S hS X)
            (Y := smallEtaleRingedTopos B S hS X')
            (smallEtaleRingedToposHom B S hS g)).obj
          (kernelIdealGradedAlgebra B S hS i')).one =
      (kernelIdealGradedAlgebra B S hS i).one)
    (h0 : IsIso ((conormalAlgebraSquareAmbientComparison B S hS i i' f g Ψ).app 0))
    (h1 : IsIso ((conormalAlgebraSquareAmbientComparison B S hS i i' f g Ψ).app 1))
    (hι : ∀ n : ℤ, 0 ≤ n →
      (conormalAlgebraSquareAmbientComparison B S hS i i' f g Ψ).app n ≫
          (kernelIdealSheafZPow B S hS i n).ι =
        (modulePullback B S hS g).map (kernelIdealSheafZPow B S hS i' n).ι ≫
          structureSheafMap B S hS g)
    (n : ℤ) (hn : 0 ≤ n) :
    IsIso ((conormalAlgebraSquareAmbientComparison B S hS i i' f g Ψ).app n) := by
  have hbal : Balanced (Modules.{u, u} B S hS X.1 X.2) := by
    have habelian : Abelian (Modules.{u, u} B S hS X.1 X.2) := inferInstance
    exact Stacks.SheafOfModules.ImageSubsheaf.balanced_of_abelian
  exact SheafOfModules.isIso_unitalHom_app_of_nonneg (structureRingSheaf B S hS X).property
    (kernelIdealSheaf B S hS i) hbal
    (SheafOfModules.GradedAlgebra.UnitalHom.ofHom
      (conormalAlgebraSquareAmbientComparison B S hS i i' f g Ψ) hunit) h0 h1
    (fun m hm => mono_conormalAlgebraSquareAmbientComparison_app_of_isFlat B S hS i i' f g Ψ hg
      hι m hm) n hn

/-- **The flat clause of [Stacks Project, Tag 09RT].**  If `g` is flat — that is, if the morphism
of small étale ringed topoi it induces is flat in the sense of [Stacks Project, Tag 04JB] — then
the canonical map `f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X,*}` of [Stacks Project, Tag 09RS] is an isomorphism in
every nonnegative degree.

Flatness is consumed in the injectivity half, through the exactness of the inverse image along a
flat morphism.  Four inputs are carried: that the ambient comparison carries the unit, its
invertibility in the degrees zero and one — the conclusions of
`AlgebraicGeometry.Space.isIso_structureSheafMap` and of the flat half of
[Stacks Project, Tag 04CQ], `AlgebraicGeometry.Space.isIso_idealSheafMap_of_isFlat`, transported
to this square — and the compatibility of the comparison with the embeddings of the powers of the
two ideal sheaves into the two structure sheaves, whose degree-one instance is
`AlgebraicGeometry.Space.idealSheafMap_comp_ι`.  The square being cartesian is therefore not
consumed, and neither is either vertical arrow being an immersion.  What is proved is that the
four suffice: surjectivity and injectivity propagate from the degrees zero and one to every
degree.  The module documentation says why none of the four is available in the library. -/
@[stacks 09RT "the flat clause: an isomorphism in every nonnegative degree when g is flat, \
flatness consumed through exactness of the inverse image; the cartesian hypothesis is NOT \
consumed, four inputs being carried: hunit, h0, h1 (Tag 04CQ's flat half transported) and hiota \
(the n-th power analogue of idealSheafMap_comp_ι); see the module docs"]
theorem isIso_conormalAlgebraSquareMapOfPullbackHom_app_of_isFlat (i : Z ⟶ X) (i' : Z' ⟶ X')
    (f : Z ⟶ Z') (g : X ⟶ X') (hsq : i ≫ g = f ≫ i')
    (Ψ : (gradedPull (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS X') (smallEtaleRingedToposHom B S hS g)).obj
        (kernelIdealGradedAlgebra B S hS (f ≫ i')) ⟶ kernelIdealGradedAlgebra B S hS i)
    (hg : (smallEtaleRingedToposHom B S hS g).IsFlat)
    (hunit : SheafOfModules.sectionsMap
        ((conormalAlgebraSquareAmbientComparison B S hS i i' f g Ψ).app 0)
        ((gradedPull (X := smallEtaleRingedTopos B S hS X)
            (Y := smallEtaleRingedTopos B S hS X')
            (smallEtaleRingedToposHom B S hS g)).obj
          (kernelIdealGradedAlgebra B S hS i')).one =
      (kernelIdealGradedAlgebra B S hS i).one)
    (h0 : IsIso ((conormalAlgebraSquareAmbientComparison B S hS i i' f g Ψ).app 0))
    (h1 : IsIso ((conormalAlgebraSquareAmbientComparison B S hS i i' f g Ψ).app 1))
    (hι : ∀ n : ℤ, 0 ≤ n →
      (conormalAlgebraSquareAmbientComparison B S hS i i' f g Ψ).app n ≫
          (kernelIdealSheafZPow B S hS i n).ι =
        (modulePullback B S hS g).map (kernelIdealSheafZPow B S hS i' n).ι ≫
          structureSheafMap B S hS g)
    (n : ℤ) (hn : 0 ≤ n) :
    IsIso ((conormalAlgebraSquareMapOfPullbackHom B S hS i i' f g hsq Ψ).app n) :=
  isIso_conormalAlgebraSquareMapOfPullbackHom_app_of_isIso_ambientComparison B S hS i i' f g
    hsq Ψ n (isIso_conormalAlgebraSquareAmbientComparison_app_of_isFlat B S hS i i' f g Ψ hg
      hunit h0 h1 hι n hn)

end AlgebraicGeometry.Space

end
