module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.CotangentSheafComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DifferentialMap
import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms, Lemma 01V0 in the form of restriction of derivations

For a commutative square of schemes

```
X' --f--> X
|         |
p'        p
v         v
S' --g--> S
```

the canonical map `c_f : f^*Ω_{X/S} ⟶ Ω_{X'/S'}` of Stacks 01UV is characterized by
`AlgebraicGeometry.Scheme.Hom.IsRelativeDifferentialsMap`: its transpose across
`f^* ⊣ f_*` carries `d_{X/S}(a)` to `d_{X'/S'}(f♯ a)`.  Reading precomposition with `c_f`
through that transpose and through the universal property of `Ω_{X/S}` turns Stacks 01V0 — `c_f`
is an isomorphism for a cartesian square — into the statement that

> **restriction of derivations along `f`** — the passage from a morphism `θ : Ω_{X'/S'} ⟶ C` of
> `𝒪_{X'}`-modules to the `S`-derivation `f_*(d_{X'/S'} ∘ θ) ∘ f♯` of `𝒪_X` with values in
> `f_*C` — is a bijection for every `𝒪_{X'}`-module `C`.

That is the form in which the spaces-side argument consumes Stacks 01V0: it is the right-hand
column of the square which
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeSquareDerivation.lean` reduces
`AlgebraicGeometry.Space.IsSchemeSquareDerivationRestriction` to, and nothing about the inverse
image of modules survives in it.

This file is the Zariski twin of
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsMapDerivationCriterion.lean`, which
carries out the same reformulation for the comparison map of Stacks 04CX on the small étale site
of an algebraic space.  The two proofs are the same three lines against different APIs:
`AlgebraicGeometry.Scheme.Hom.IsRelativeDifferentialsMap` here against
`AlgebraicGeometry.Space.IsSheafOfDifferentialsMap` there, and
`AlgebraicGeometry.Scheme.Hom.existsUnique_hom_relativeDifferentials` here against
`AlgebraicGeometry.Space.universalDerivation_isUniversal` there.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.pushforwardRelativeDerivation`: the `S`-derivation
  `f_*d_{X'/S'} ∘ f♯` of `𝒪_X`, the transpose of the canonical map of Stacks 01UV.
* `AlgebraicGeometry.Scheme.Hom.restrictRelativeDerivation`: restriction of derivations along
  `f`, that derivation postcomposed with the direct image of `θ`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.pushforwardRelativeDerivation_d`: its value on a local section
  `a` of `𝒪_X` is `d_{X'/S'}(f♯ a)`.
* `AlgebraicGeometry.Scheme.Hom.bijective_restrictRelativeDerivation_of_isPullback`:
  **Stacks 01V0 in derivation form** — for a cartesian square restriction of derivations along
  the top edge is a bijection for every `𝒪_{X'}`-module.
* `AlgebraicGeometry.Scheme.Hom.exists_unique_restrictRelativeDerivation`: the same stated as
  unique existence, which is how a consumer going the other way round the square uses it.

## Implementation notes

`AlgebraicGeometry.Scheme.Hom.restrictRelativeDerivation` is *defined* as a postcomposition of
`AlgebraicGeometry.Scheme.Hom.pushforwardRelativeDerivation` rather than by writing out a
derivation, so that no direct image of an arbitrary derivation has to be constructed: the only
derivation on `X'` that enters is the universal one.
`AlgebraicGeometry.Scheme.Hom.restrictRelativeDerivation_eq` identifies it with the composite
through the adjunction, which is where the bijectivity comes from.

The cartesian square enters only through
`AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsMap_of_isPullback`; everything else here
holds for an arbitrary commutative square.

No Stacks tag is registered: everything here rearranges Stacks 01V0 and the characterization of
Stacks 01UV, whose mathematics is attributed where those are proved.

## References

* [Stacks Project, Tag 01V0](https://stacks.math.columbia.edu/tag/01V0)
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV), the canonical map and
  its characterization.
* [Stacks Project, Tag 08RM](https://stacks.math.columbia.edu/tag/08RM), the universal property
  of the sheaf of relative differentials.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X' X S' S : Scheme.{u}} (f : X' ⟶ X) (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S)
  (hcomm : f ≫ p = p' ≫ g)

/-- **The `S`-derivation `f_*d_{X'/S'} ∘ f♯` of `𝒪_X`**: the transpose across `f^* ⊣ f_*` of the
canonical map of Stacks 01UV, read as a derivation through the universal property of
`Ω_{X/S}`. -/
def pushforwardRelativeDerivation :
    SheafOfModules.SheafDerivation (inverseImageStructureMap p)
      ((Scheme.Modules.pushforward f).obj (relativeDifferentials p')) :=
  (universalRelativeDerivation p).postcomp
    (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv (relativeDifferentials p)
      (relativeDifferentials p') (relativeDifferentialsMap f p p' g hcomm)).val)

/-- The value of `AlgebraicGeometry.Scheme.Hom.pushforwardRelativeDerivation` on a local section
`a` of `𝒪_X` over an open `U` is the universal differential of `f♯ a`.  This is the defining
compatibility of the canonical map of Stacks 01UV with the universal derivations. -/
theorem pushforwardRelativeDerivation_d (U : X.Opens) (a : Γ(X, U)) :
    (pushforwardRelativeDerivation f p p' g hcomm).d a =
      (universalRelativeDerivation p').d ((f.app U).hom a) :=
  relativeDifferentialsMap_app_d g hcomm U a

/-- **Restriction of derivations along the top edge of a commutative square of schemes.**  For a
morphism `θ : Ω_{X'/S'} ⟶ C` of `𝒪_{X'}`-modules, the `S`-derivation of `𝒪_X` with values in
`f_*C` obtained by composing the structure map `f♯` with the direct image of `d_{X'/S'}`
followed by `θ`. -/
def restrictRelativeDerivation (C : X'.Modules) (θ : relativeDifferentials p' ⟶ C) :
    SheafOfModules.SheafDerivation (inverseImageStructureMap p)
      ((Scheme.Modules.pushforward f).obj C) :=
  (pushforwardRelativeDerivation f p p' g hcomm).postcomp
    ((Scheme.Modules.pushforward f).map θ).val

/-- The value of restriction of derivations on a local section `a` of `𝒪_X` is `θ` applied to the
universal differential of `f♯ a`. -/
theorem restrictRelativeDerivation_d (C : X'.Modules) (θ : relativeDifferentials p' ⟶ C)
    (U : X.Opens) (a : Γ(X, U)) :
    (restrictRelativeDerivation f p p' g hcomm C θ).d a =
      (((Scheme.Modules.pushforward f).map θ).val.app (.op U)).hom
        ((universalRelativeDerivation p').d ((f.app U).hom a)) :=
  congrArg (fun z ↦ (((Scheme.Modules.pushforward f).map θ).val.app (.op U)).hom z)
    (pushforwardRelativeDerivation_d f p p' g hcomm U a)

/-- **Restriction of derivations along `f` is precomposition with the canonical map of
Stacks 01UV**, read through the adjunction `f^* ⊣ f_*` and the universal property of
`Ω_{X/S}`.  The transpose is natural in its right argument. -/
theorem restrictRelativeDerivation_eq (C : X'.Modules) (θ : relativeDifferentials p' ⟶ C) :
    restrictRelativeDerivation f p p' g hcomm C θ =
      (universalRelativeDerivation p).postcomp
        (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv (relativeDifferentials p) C
          (relativeDifferentialsMap f p p' g hcomm ≫ θ)).val) := by
  rw [Adjunction.homEquiv_naturality_right]
  rfl

/-- Postcomposition with the universal relative derivation is a bijection from the morphisms out
of `Ω_{X/S}` onto the `S`-derivations of `𝒪_X`.  This is the universal property of Stacks 08RM
read as a bijection. -/
theorem bijective_universalRelativeDerivation_postcomp (F : X.Modules) :
    Function.Bijective
      (fun α : relativeDifferentials p ⟶ F ↦ (universalRelativeDerivation p).postcomp α.val) :=
  (Function.bijective_iff_existsUnique _).2 (existsUnique_hom_relativeDifferentials p F)

/-- **Morphisms, Lemma 01V0 in derivation form.**  For a cartesian square of schemes, restriction
of derivations along the top edge is a bijection from the morphisms `Ω_{X'/S'} ⟶ C` onto the
`S`-derivations of `𝒪_X` with values in `f_*C`, for every `𝒪_{X'}`-module `C`.

By `AlgebraicGeometry.Scheme.Hom.restrictRelativeDerivation_eq` it is precomposition with the
canonical map of Stacks 01UV followed by two bijections — the transpose across `f^* ⊣ f_*` and
the universal property of `Ω_{X/S}` — and the canonical map is an isomorphism by
`AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsMap_of_isPullback`. -/
theorem bijective_restrictRelativeDerivation_of_isPullback (h : IsPullback f p' p g)
    (C : X'.Modules) :
    Function.Bijective (restrictRelativeDerivation f p p' g h.w C) := by
  have := isIso_relativeDifferentialsMap_of_isPullback f p' p g h
  have hcomp : restrictRelativeDerivation f p p' g h.w C =
      (fun α : relativeDifferentials p ⟶ (Scheme.Modules.pushforward f).obj C ↦
          (universalRelativeDerivation p).postcomp α.val) ∘
        ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
          (relativeDifferentials p) C) ∘
        fun θ ↦ relativeDifferentialsMap f p p' g h.w ≫ θ :=
    funext fun θ ↦ restrictRelativeDerivation_eq f p p' g h.w C θ
  rw [hcomp]
  refine (bijective_universalRelativeDerivation_postcomp p _).comp
    (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
      (relativeDifferentials p) C).bijective.comp ⟨fun θ₁ θ₂ hθ ↦ ?_, fun c ↦ ?_⟩)
  · exact (cancel_epi (relativeDifferentialsMap f p p' g h.w)).1 hθ
  · refine ⟨inv (relativeDifferentialsMap f p p' g h.w) ≫ c, ?_⟩
    show relativeDifferentialsMap f p p' g h.w ≫
      inv (relativeDifferentialsMap f p p' g h.w) ≫ c = c
    rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

/-- **Morphisms, Lemma 01V0 in derivation form**, stated as unique existence: for a cartesian
square every `S`-derivation of `𝒪_X` with values in `f_*C` is the restriction along `f` of
exactly one morphism `Ω_{X'/S'} ⟶ C`. -/
theorem exists_unique_restrictRelativeDerivation (h : IsPullback f p' p g) (C : X'.Modules)
    (D : SheafOfModules.SheafDerivation (inverseImageStructureMap p)
      ((Scheme.Modules.pushforward f).obj C)) :
    ∃! θ : relativeDifferentials p' ⟶ C, restrictRelativeDerivation f p p' g h.w C θ = D :=
  (Function.bijective_iff_existsUnique _).1
    (bijective_restrictRelativeDerivation_of_isPullback f p p' g h C) D

end AlgebraicGeometry.Scheme.Hom

end
