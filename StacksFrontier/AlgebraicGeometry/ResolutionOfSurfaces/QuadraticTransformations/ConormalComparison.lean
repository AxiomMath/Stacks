module

public import StacksFrontier.AlgebraicGeometry.Conormal.ModuleCoverLocality
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.TwoImmersionsConormalSequence
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurve

/-!
# The conormal comparison map of two exceptional curves is an isomorphism

This file isolates the step of [Stacks, Tag 0C5R] (Resolution of Surfaces, Lemma 54.17.1) at
which the source compares conormal sheaves on the exceptional curve. In the situation of that
proof one has a morphism `f' : X' ⟶ Y'` of surfaces, the exceptional curve `E ⊆ X'` of a blowup
of `X'` at a closed point, the exceptional curve `E' ⊆ Y'` of the blowup `Y' ⟶ Y` at a closed
point, and an isomorphism `g : E ⟶ E'` with `i ≫ f' = g ≫ i'`. The comparison map of
[Stacks, Tag 01R4] attached to that square,

`φ : g^* 𝒞_{E'/Y'} ⟶ 𝒞_{E/X'}`,

is a map between two invertible modules of degree one on `E = E' = 𝐏¹_κ`, and the source
concludes from `φ ≠ 0` that `φ` is an isomorphism.

The mathematical content is entirely about the projective line: *a nonzero map between two
invertible modules of the same degree on `𝐏¹_κ` is an isomorphism*. Degree `d` for an invertible
module on the projective line is recorded, as everywhere else in this library — see the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Surfaces/ExceptionalCurveTwistInjectivity.lean` — by an
isomorphism with the `d`-th twist `𝒪(d)` of
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf` on
`AlgebraicGeometry.projectiveLineProj`, which is the `Proj` model of the projective line that
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind` uses. So the hypothesis
"both conormal modules are invertible of degree `d`" is two isomorphisms of their pullbacks
along a presentation `ε : 𝐏¹_k ≅ E` with `𝒪(d)`, and the exceptional case of
[Stacks, Tag 0C5R] is `d = 1`.

## Main definitions

* `Stacks.ResolutionOfSurfaces.projectiveLineTwist` — `𝒪(d)` on `𝐏¹_k`, with its category
  spelled as the category of module sheaves on the *scheme* `projectiveLineProj k`.
* `Stacks.ResolutionOfSurfaces.NonzeroTwistEndoIsIso` — the statement that a nonzero
  endomorphism of `𝒪(d)` on `𝐏¹_k` is an isomorphism, a hypothesis of the results below.

## Main results

* `Stacks.ResolutionOfSurfaces.isIso_of_ne_zero_of_pullback_iso_projectiveLineTwist` — the
  statement about the projective line, transported to a scheme `W` presented as `𝐏¹_k`: a
  nonzero map `N ⟶ M` of modules on `W` whose pullbacks along the presentation are both `𝒪(d)`
  is an isomorphism.
* `Stacks.ResolutionOfSurfaces.isIso_immersionConormalSheafMap_of_ne_zero` — the step of
  [Stacks, Tag 0C5R] itself, for the comparison map of [Stacks, Tag 01R4] attached to a square
  of immersions whose left-hand curve is presented as `𝐏¹_k`.
* `Stacks.ResolutionOfSurfaces.isIso_conormalTransitivityMap_of_ne_zero` — the same for the
  first arrow of [Stacks, Tag 067L], which is the comparison map of the square whose top
  morphism is the identity.

## Implementation notes

No degree theory is used: the two degrees are not computed, only the two isomorphisms with a
common twist, which is what *equal degree* means on the projective line.

The hypothesis `Stacks.ResolutionOfSurfaces.NonzeroTwistEndoIsIso` — a nonzero endomorphism of
`𝒪(d)` on `𝐏¹_k` is an isomorphism — is the equality clause of part (5) of [Stacks, Tag 0B40]
("`deg 𝒩 ≤ deg ℳ` for a nonzero `𝒩 ⟶ ℳ`, with equality if and only if the map is an
isomorphism") at the projective line; equivalently it is the computation
`End_{𝐏¹_k}(𝒪(d)) = Γ(𝐏¹_k, 𝒪) = k` of [Stacks, Tag 01XT] together with invertibility of the
twist. It is quantified over every twist and every endomorphism of it, and mentions none of the
schemes, immersions or conormal sheaves of the conclusions.

## References

* [Stacks Project, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 067L](https://stacks.math.columbia.edu/tag/067L)
* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction
open RingedSpaceModuleAdjunction (toShHomIso isEquivalence_modulePullback_of_iso
  modulePullback_preservesZeroMorphisms_of_iso)

universe u

namespace Stacks.ResolutionOfSurfaces

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The twists on the projective line, and the carried input -/

/-- **The `d`-th twist `𝒪(d)` on the projective line `𝐏¹_k`**, with its category spelled as the
category of sheaves of modules on the *scheme* `AlgebraicGeometry.projectiveLineProj k`.

`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf` produces the twist in the category of
modules over the structure sheaf of `Proj`, which unifies with the category of modules over the
structure sheaf of the scheme `Proj` but is not the same expression; fixing the spelling once
here keeps the two out of the statements below, where a rewrite across them would not be
type-correct. -/
public def projectiveLineTwist (k : Type u) [Field k] (d : ℤ) :
    SheafOfModules.{u} (structureSheafRing (projectiveLineProj k).toRingedSpace) :=
  ProjectiveSpectrum.Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin 2) k) d

/-- **A nonzero endomorphism of `𝒪(d)` on `𝐏¹_k` is an isomorphism.**

This is the equality clause of part (5) of [Stacks, Tag 0B40] at the projective line, and
equivalently the computation `End_{𝐏¹_k}(𝒪(d)) = Γ(𝐏¹_k, 𝒪) = k` of [Stacks, Tag 01XT]: an
endomorphism of an invertible module is multiplication by a global function, on the projective
line the global functions are the ground field, and a nonzero element of a field is a unit. -/
public def NonzeroTwistEndoIsIso (k : Type u) [Field k] : Prop :=
  ∀ (d : ℤ) (ψ : projectiveLineTwist k d ⟶ projectiveLineTwist k d), ψ ≠ 0 → IsIso ψ

/-! ### The statement about the projective line, transported along a presentation -/

/-- **A nonzero map between two invertible modules of the same degree on `𝐏¹_k` is an
isomorphism**, stated on a scheme `W` presented as the projective line by an isomorphism
`ε : 𝐏¹_k ≅ W`, with *degree `d`* recorded by an isomorphism of the pullback along `ε` with the
`d`-th twist.

Pullback along `ε` is an equivalence of the two categories of module sheaves
(`RingedSpaceModuleAdjunction.isEquivalence_modulePullback_of_iso`), so it carries a
nonzero morphism to a nonzero morphism and reflects isomorphisms; the two given isomorphisms
turn the pulled-back morphism into an endomorphism of the twist. -/
public theorem isIso_of_ne_zero_of_pullback_iso_projectiveLineTwist (k : Type u) [Field k]
    (hk : NonzeroTwistEndoIsIso k) {W : Scheme.{u}} (ε : projectiveLineProj k ≅ W) (d : ℤ)
    {N M : SheafOfModules.{u} (structureSheafRing W.toRingedSpace)}
    (α : (modulePullback (toShHomIso ε).hom).obj N ≅ projectiveLineTwist k d)
    (β : (modulePullback (toShHomIso ε).hom).obj M ≅ projectiveLineTwist k d)
    (φ : N ⟶ M) (hφ : φ ≠ 0) : IsIso φ := by
  have hequiv : (modulePullback (toShHomIso ε).hom).IsEquivalence :=
    isEquivalence_modulePullback_of_iso (toShHomIso ε)
  have hzero : (modulePullback (toShHomIso ε).hom).PreservesZeroMorphisms :=
    modulePullback_preservesZeroMorphisms_of_iso (toShHomIso ε)
  set F := modulePullback (toShHomIso ε).hom with hF
  have key : F.map φ = α.hom ≫ (α.inv ≫ F.map φ ≫ β.hom) ≫ β.inv := by simp
  have hψ : α.inv ≫ F.map φ ≫ β.hom ≠ 0 := by
    intro h0
    refine hφ (F.map_injective ?_)
    rw [key, h0, Functor.map_zero]
    simp
  have := hk d _ hψ
  have : IsIso (F.map φ) := by rw [key]; infer_instance
  exact isIso_of_reflects_iso φ F

/-! ### The step of Tag 0C5R -/

/-- **The step of [Stacks, Tag 0C5R] at the conormal comparison map.** Let `i : E ⟶ X'` and
`i' : E' ⟶ Y'` be immersions, `g : E ⟶ E'` and `f' : X' ⟶ Y'` morphisms with
`i ≫ f' = g ≫ i'`, and let

`φ : g^* 𝒞_{E'/Y'} ⟶ 𝒞_{E/X'}`

be the comparison map of [Stacks, Tag 01R4] attached to that square. Suppose `E` is presented as
the projective line by `ε : 𝐏¹_k ≅ E` and that both conormal modules have degree `d` on it, in
the sense that their pullbacks along `ε` are isomorphic to `𝒪(d)`. If `φ ≠ 0` then `φ` is an
isomorphism.

In [Stacks, Tag 0C5R] the two curves are the exceptional curves of blowups of regular surfaces
at closed points, `g` is an isomorphism and `d = 1`; nothing of that is needed here beyond the
two degree hypotheses. -/
public theorem isIso_immersionConormalSheafMap_of_ne_zero (k : Type u) [Field k]
    (hk : NonzeroTwistEndoIsIso k) (d : ℤ) {E E' X' Y' : Scheme.{u}}
    (i : E ⟶ X') (i' : E' ⟶ Y') [IsImmersion i] [IsImmersion i'] (g : E ⟶ E') (f' : X' ⟶ Y')
    (comm : i ≫ f' = g ≫ i') (ε : projectiveLineProj k ≅ E)
    (α : (modulePullback (toShHomIso ε).hom).obj
        ((modulePullback g.toLRSHom.toShHom).obj (Stacks.Conormal.conormalSheaf i')) ≅
      projectiveLineTwist k d)
    (β : (modulePullback (toShHomIso ε).hom).obj (Stacks.Conormal.conormalSheaf i) ≅
      projectiveLineTwist k d)
    (hne : Stacks.Immersion.immersionConormalSheafMap i i' g f'
      (Stacks.Immersion.toShHom_square comm) ≠ 0) :
    IsIso (Stacks.Immersion.immersionConormalSheafMap i i' g f'
      (Stacks.Immersion.toShHom_square comm)) :=
  isIso_of_ne_zero_of_pullback_iso_projectiveLineTwist k hk ε d α β _ hne

/-- **The step of [Stacks, Tag 0C5R] at the first arrow of [Stacks, Tag 067L].** For immersions
`i : E ⟶ X'` and `j : E ⟶ Y'` in a commutative triangle `i ≫ f' = j`, the first arrow

`𝒞_{E/Y'} ⟶ 𝒞_{E/X'}`

of the conormal sequence of [Stacks, Tag 067L] is an isomorphism as soon as it is nonzero and
both conormal modules have degree `d` on a presentation `ε : 𝐏¹_k ≅ E` of `E` as the projective
line.

This is the previous theorem for the square whose top morphism is the identity of `E`, which is
the square the first arrow of [Stacks, Tag 067L] is the comparison map of. -/
public theorem isIso_conormalTransitivityMap_of_ne_zero (k : Type u) [Field k]
    (hk : NonzeroTwistEndoIsIso k) (d : ℤ) {E X' Y' : Scheme.{u}}
    (i : E ⟶ X') (j : E ⟶ Y') (f' : X' ⟶ Y') [IsImmersion i] [IsImmersion j]
    (h : i ≫ f' = j) (ε : projectiveLineProj k ≅ E)
    (α : (modulePullback (toShHomIso ε).hom).obj (Stacks.Conormal.conormalSheaf j) ≅
      projectiveLineTwist k d)
    (β : (modulePullback (toShHomIso ε).hom).obj (Stacks.Conormal.conormalSheaf i) ≅
      projectiveLineTwist k d)
    (hne : Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap i j f' h ≠ 0) :
    IsIso (Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap i j f' h) :=
  isIso_of_ne_zero_of_pullback_iso_projectiveLineTwist k hk ε d α β _ hne

end Stacks.ResolutionOfSurfaces

end
