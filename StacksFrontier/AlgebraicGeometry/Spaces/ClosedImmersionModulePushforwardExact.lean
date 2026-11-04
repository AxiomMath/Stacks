module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardRightExact
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom

/-!
# Cokernels and short exact sequences under the direct image along a closed immersion

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  The direct image `i_* : Mod(𝒪_Z) ⥤ Mod(𝒪_X)` of
`AlgebraicGeometry.Space.modulePushforward` is exact, and this file records the consequences that
consumers use: `i_*` carries surjections to surjections, it commutes with cokernels, and it
carries short exact sequences to short exact sequences.

Exactness itself is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModulePushforwardRightExact.lean`.  Left
exactness is formal — `i_*` is the right adjoint of the adjunction of Stacks 03LU, so it preserves
all limits — and right exactness is Stacks 04BD fed the space-level analogue of Stacks 04DX,
part (7): base change of étale scheme charts along a closed immersion is almost cocontinuous.  By
`Stacks.SheafOfModules.LocalCokernel.finiteColimits_of_finiteLimits_epi`, an additive left exact
functor of abelian categories preserving epimorphisms is right exact, so all of the content sits
in the assertion that `i_*` preserves epimorphisms.

## Main definitions

* `AlgebraicGeometry.Space.modulePushforwardCokernelIso` — the identification
  `coker(i_*φ) ≅ i_*(coker φ)`.

## Main results

* `AlgebraicGeometry.Space.epi_modulePushforward_map`: a surjection of `𝒪_Z`-modules has
  surjective direct image.  This is the companion of
  `AlgebraicGeometry.Space.mono_modulePushforward_map`.
* `AlgebraicGeometry.Space.isIso_cokernelComparison_modulePushforward_of_isClosedImmersion`: the
  canonical comparison `coker(i_*φ) ⟶ i_*(coker φ)` is an isomorphism.
* `AlgebraicGeometry.Space.shortExact_map_modulePushforward_of_isClosedImmersion`: `i_*` carries
  a short exact sequence of `𝒪_Z`-modules to a short exact sequence of `𝒪_X`-modules.

## References

* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 04BD](https://stacks.math.columbia.edu/tag/04BD)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 0A4K](https://stacks.math.columbia.edu/tag/0A4K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Z : AlgebraicSpaces B S hS}

/-- A surjection of `𝒪_Z`-modules has surjective direct image along a closed immersion
`i : Z ⟶ X`.  This is the companion of `AlgebraicGeometry.Space.mono_modulePushforward_map`,
which is the injectivity half. -/
theorem epi_modulePushforward_map (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    {M N : Modules.{u, u} B S hS Z.1 Z.2} (φ : M ⟶ N) (hφ : Epi φ) :
    Epi ((modulePushforward B S hS i).map φ) :=
  (preservesEpimorphisms_modulePushforward_of_isClosedImmersion B S hS i hi).preserves φ

/-- The canonical comparison `coker(i_*φ) ⟶ i_*(coker φ)` for a closed immersion `i : Z ⟶ X` is
an isomorphism: the direct image preserves the cokernel of `φ`. -/
theorem isIso_cokernelComparison_modulePushforward_of_isClosedImmersion (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) {M N : Modules.{u, u} B S hS Z.1 Z.2} (φ : M ⟶ N) :
    IsIso (cokernelComparison (C := Modules.{u, u} B S hS Z.1 Z.2) φ
      (modulePushforward B S hS i)) := by
  have h := preservesFiniteColimits_modulePushforward_of_isClosedImmersion B S hS i hi
  have h2 : PreservesColimitsOfShape WalkingParallelPair (modulePushforward B S hS i) :=
    h.preservesFiniteColimits _
  infer_instance

/-- **The direct image along a closed immersion commutes with cokernels**: for a morphism
`φ : M ⟶ N` of `𝒪_Z`-modules the canonical comparison identifies `coker(i_*φ)` with
`i_*(coker φ)`.  This is the form in which consumers use right exactness. -/
def modulePushforwardCokernelIso (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    {M N : Modules.{u, u} B S hS Z.1 Z.2} (φ : M ⟶ N) :
    cokernel (C := Modules.{u, u} B S hS X.1 X.2) ((modulePushforward B S hS i).map φ) ≅
      (modulePushforward B S hS i).obj (cokernel (C := Modules.{u, u} B S hS Z.1 Z.2) φ) :=
  have := isIso_cokernelComparison_modulePushforward_of_isClosedImmersion B S hS i hi φ
  asIso (cokernelComparison (C := Modules.{u, u} B S hS Z.1 Z.2) φ (modulePushforward B S hS i))

/-- **The direct image along a closed immersion carries a short exact sequence of `𝒪_Z`-modules
to a short exact sequence of `𝒪_X`-modules**, the direct image being exact. -/
theorem shortExact_map_modulePushforward_of_isClosedImmersion (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)
    (T : ShortComplex (Modules.{u, u} B S hS Z.1 Z.2)) (hT : T.ShortExact) :
    (T.map (modulePushforward B S hS i)).ShortExact := by
  have h2 : PreservesLimits (modulePushforward B S hS i) :=
    (modulePullbackAdjunction B S hS i).rightAdjoint_preservesLimits
  have h3 : PreservesFiniteLimits (modulePushforward B S hS i) := inferInstance
  have h4 := preservesFiniteColimits_modulePushforward_of_isClosedImmersion B S hS i hi
  exact hT.map_of_exact (modulePushforward B S hS i)

end AlgebraicGeometry.Space

end
