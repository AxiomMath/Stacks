module

public import StacksFrontier.AlgebraicGeometry.DeRham.CoefficientRingChange
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.SchemeComplex

/-!
# The target of the identification of the graded pieces of Section 0FMK

Let `f : X ⟶ Y` be a morphism of schemes over a base `S`, with `g : Y ⟶ S` the structure
morphism of the target. Stacks Section 50.12 identifies the graded pieces of the filtration of
`Ω^•_{X/S}` by the forms pulled back from `Y` as

`gr^kΩ^•_{X/S} = f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}`.

**This file builds the right-hand side**, as a complex in the very category
`Stacks.DeRhamSmooth.gradedPiece` lands in — complexes of `(f ∘ g)^{-1}𝒪_S`-modules on `X` — so
that the two sides of that identification are objects of one category and the identification is
a statement about a morphism between them. Nothing is assumed of `f`: the construction is
available for every morphism of schemes.

Three things have to be put together, and the file keeps them separate so that each can be read
off the result:

* **the tensor product over `f^{-1}𝒪_Y`.** `Ω^•_{X/Y}` is already a complex of
  `f^{-1}𝒪_Y`-modules (`Stacks.DeRhamDirectImage.deRhamCochainComplex` at `f`), and
  `f^{-1}Ω^k_{Y/S}` is the inverse image of the `𝒪_Y`-module `Ω^k_{Y/S}` along the projection
  `(X, f^{-1}𝒪_Y) ⟶ Y`. Tensoring with it is an additive endofunctor of
  `f^{-1}𝒪_Y`-modules, so it applies to the complex a degree at a time;
* **the shift `[-k]`**, which puts the single sheaf `f^{-1}Ω^k_{Y/S}` in degree `k` and so moves
  the tensor product up by `k`. Taken on the tensored complex rather than on the single sheaf:
  the two agree, and only one of them needs the tensor product to be formed degreewise;
* **the change of coefficients** from `f^{-1}𝒪_Y` to `(f ∘ g)^{-1}𝒪_S`, which is
  `Stacks.DeRhamDirectImage.coefficientRestriction`. The left-hand side `gr^kΩ^•_{X/S}` is a
  complex of `(f ∘ g)^{-1}𝒪_S`-modules, so the right-hand side has to be read there.

## Main definitions

* `Stacks.DeRhamSmooth.pulledBackTargetForms`: **`f^{-1}Ω^k_{Y/S}`**, the inverse image of the
  sheaf of relative `k`-forms of the target, as a sheaf of `f^{-1}𝒪_Y`-modules on `X`.
* `Stacks.DeRhamSmooth.gradedTargetTensor`: **`f^{-1}Ω^k_{Y/S} ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}`**, a
  complex of `f^{-1}𝒪_Y`-modules.
* `Stacks.DeRhamSmooth.gradedTargetComplex`: **`f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}`**,
  read over `(f ∘ g)^{-1}𝒪_S`: the target of the identification of Section 0FMK.

## Main results

* `Stacks.DeRhamSmooth.gradedTargetComplex_X`: **its degree-`n` term is
  `f^{-1}Ω^k_{Y/S} ⊗_{f^{-1}𝒪_Y} Ω^{n-k}_{X/Y}`** — the shift read on the terms; and
  `Stacks.DeRhamSmooth.eqToHom_gradedTargetComplex_X`, the transport along it read as an
  identity at the tensored side.
* `Stacks.DeRhamSmooth.gradedTargetComplex_d`: **its differential is `(-1)^k(1 ⊗ d_{X/Y})`** —
  the shift read on the differentials. The sign is the one the shift convention of
  `CochainComplex.shiftFunctor` carries, and it is the sign the de Rham differential actually
  induces on the graded piece: modulo `F^{k+1}Ω^•_{X/S}` one has
  `d(ω ∧ η) = (-1)^kω ∧ dη` for `ω` a pulled-back `k`-form, because `dω` is again pulled back
  and so `dω ∧ η` already lies in the next step. This is why Section 50.12 writes the shift.
* `Stacks.DeRhamSmooth.isZero_gradedTargetComplex_X`: **it is concentrated in degrees `≥ k`**,
  the de Rham complex being concentrated in nonnegative degrees.

## Implementation notes

`f^{-1}` on modules is the module pullback along
`Stacks.DeRhamDirectImage.inverseImageBaseProjection`, the projection
`(X, f^{-1}𝒪_Y) ⟶ (Y, 𝒪_Y)` whose underlying map is that of `f` and whose
structure map is the unit of `f^{-1} ⊣ f_*`. Since the structure sheaf of the source *is*
`f^{-1}𝒪_Y`, that pullback is `f^{-1}M ⊗_{f^{-1}𝒪_Y} f^{-1}𝒪_Y`, i.e. the sheaf-theoretic
inverse image with its evident module structure; this is the same device by which
`Stacks.DeRhamSmooth.pulledBackDeRhamComplex` is the inverse image `f^{-1}Ω^•_{Y/S}` of the de
Rham complex of the target, and no second spelling of `f^{-1}` is introduced.

`Ω^k_{Y/S}` is `AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)`, the sheaf of
relative `k`-forms as an `𝒪_Y`-module — the same object the terms of
`AlgebraicGeometry.Scheme.Hom.deRhamComplex g` are the restrictions of scalars of
(`AlgebraicGeometry.Scheme.Hom.deRhamComplex_X`), and the same exterior power the graded pieces
of `StacksFrontier.AlgebraicGeometry.DeRham.ExteriorGradedPiece` are formed from: the exterior
algebra of `Ω_{Y/S}` used there is
`SheafOfModules.ringedSpaceAlgebras Y.toRingedSpace (Ω_{Y/S})`, which is
`AlgebraicGeometry.Scheme.Hom.deRhamAlgebras g` by definition. The `𝒪_Y`-module form is the one
Section 50.12 needs: the tensor product is taken over `f^{-1}𝒪_Y`, which only sees the
`𝒪_Y`-module structure of `Ω^k_{Y/S}`, not its `g^{-1}𝒪_S`-module structure.

The shift is taken after the tensor product and not before. Shifting the single sheaf first
would force the tensor product of two complexes and hence a total complex; shifting afterwards
is the same complex, because tensoring with a fixed sheaf acts degreewise and a shift only
re-indexes and re-signs.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 0FKQ](https://stacks.math.columbia.edu/tag/0FKQ)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.DeRhamDirectImage

universe u

namespace Stacks.DeRhamSmooth

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **`f^{-1}Ω^k_{Y/S}`**, the inverse image of the sheaf of relative `k`-forms of the target,
as a sheaf of `f^{-1}𝒪_Y`-modules on `X`. The inverse image is the module pullback along the
projection `(X, f^{-1}𝒪_Y) ⟶ (Y, 𝒪_Y)`, whose structure sheaf on the source is `f^{-1}𝒪_Y`
itself. -/
abbrev pulledBackTargetForms (k : ℕ) : Modules (inverseImageBase f) :=
  (_root_.pullback (inverseImageBaseProjection f)).obj
    (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))

/-- Tensoring sheaves of `f^{-1}𝒪_Y`-modules on `X` with `f^{-1}Ω^k_{Y/S}`, as an endofunctor.
It is additive (`AlgebraicGeometry.SheafOfModules.tensorFunctor_obj_additive`), which is what
lets it be applied to a complex a degree at a time. -/
abbrev pulledBackTargetFormsTensor (k : ℕ) :
    Modules (inverseImageBase f) ⥤ Modules (inverseImageBase f) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor
    (inverseImageBase f).sheaf).obj (pulledBackTargetForms f g k)

/-- **`f^{-1}Ω^k_{Y/S} ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}`**, a complex of `f^{-1}𝒪_Y`-modules on `X`: the
relative de Rham complex of `f` tensored degreewise with the inverse image of the sheaf of
relative `k`-forms of the target. -/
abbrev gradedTargetTensor (k : ℕ) : CochainComplex (Modules (inverseImageBase f)) ℤ :=
  ((pulledBackTargetFormsTensor f g k).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (deRhamCochainComplex f)

/-- **`f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}`**, read as a complex of
`(f ∘ g)^{-1}𝒪_S`-modules: **the target of the identification of the graded pieces of
[Stacks, Section 0FMK]**.

The shift `[-k]` is taken on the tensored complex, which is the same as taking it on the single
sheaf `f^{-1}Ω^k_{Y/S}`; the change of coefficients to `(f ∘ g)^{-1}𝒪_S` is
`Stacks.DeRhamDirectImage.coefficientRestriction`, and it is what puts this complex in the
category `Stacks.DeRhamSmooth.gradedPiece` lands in. -/
abbrev gradedTargetComplex (k : ℕ) :
    CochainComplex (Modules (inverseImageBase (f ≫ g))) ℤ :=
  ((coefficientRestriction f g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((CategoryTheory.shiftFunctor (CochainComplex (Modules (inverseImageBase f)) ℤ)
      (-(k : ℤ))).obj (gradedTargetTensor f g k))

/-- **The degree-`n` term of the target is `f^{-1}Ω^k_{Y/S} ⊗_{f^{-1}𝒪_Y} Ω^{n-k}_{X/Y}`**, read
over `(f ∘ g)^{-1}𝒪_S`: the shift `[-k]` moves the tensor product up by `k`. -/
theorem gradedTargetComplex_X (k : ℕ) (n : ℤ) :
    (gradedTargetComplex f g k).X n =
      (coefficientRestriction f g).obj
        ((pulledBackTargetFormsTensor f g k).obj
          ((deRhamCochainComplex f).X (n + -(k : ℤ)))) :=
  rfl

/-- **The transport along `Stacks.DeRhamSmooth.gradedTargetComplex_X` is the identity**, written
at the tensored side. The equation holds by `rfl`, so its `eqToHom` is an identity morphism; what
this adds is the *spelling* of that identity — at the tensor product rather than at the term of
the target complex — which is the one a composite through
`Stacks.DeRhamSmooth.gradedTargetXIso` meets, that comparison being built from the `eqToIso` of
the equation above.

Isolated in a statement of its own rather than discharged where it is needed: the equation is
free here and not free inside a square that also carries the two differentials.

Costs 879 heartbeats against the default budget of 200,000. -/
theorem eqToHom_gradedTargetComplex_X (k : ℕ) (n : ℤ) :
    eqToHom (gradedTargetComplex_X f g k n) =
      𝟙 ((coefficientRestriction f g).obj ((pulledBackTargetFormsTensor f g k).obj
        ((deRhamCochainComplex f).X (n + -(k : ℤ))))) :=
  eqToHom_refl _ (gradedTargetComplex_X f g k n)

/-- `Stacks.DeRhamSmooth.eqToHom_gradedTargetComplex_X` for the transport in the other direction,
which is the one `Stacks.DeRhamSmooth.gradedTargetXIso`'s inverse carries. Stated separately
because the two are matched syntactically, not up to `Eq.symm`.

Costs 510 heartbeats against the default budget of 200,000. -/
theorem eqToHom_gradedTargetComplex_X_symm (k : ℕ) (n : ℤ) :
    eqToHom (gradedTargetComplex_X f g k n).symm =
      𝟙 ((coefficientRestriction f g).obj ((pulledBackTargetFormsTensor f g k).obj
        ((deRhamCochainComplex f).X (n + -(k : ℤ))))) :=
  eqToHom_refl _ (gradedTargetComplex_X f g k n).symm

/-- The differential of `f^{-1}Ω^k_{Y/S} ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}` is `1 ⊗ d_{X/Y}`: the tensor
product is formed degreewise, so the de Rham differential of `f` is carried through it. -/
theorem gradedTargetTensor_d (k : ℕ) (n m : ℤ) :
    (gradedTargetTensor f g k).d n m =
      (pulledBackTargetFormsTensor f g k).map ((deRhamCochainComplex f).d n m) :=
  rfl

/-- **The differential of the target is `(-1)^k(1 ⊗ d_{X/Y})`.** The factor `1 ⊗ d_{X/Y}` is the
de Rham differential of `f` tensored with the identity of `f^{-1}Ω^k_{Y/S}`; the sign is the one
the shift `[-k]` carries, and it is the sign the de Rham differential of `X/S` induces on the
`k`-th graded piece, since `d(ω ∧ η) = dω ∧ η + (-1)^kω ∧ dη` and the first summand lies in the
next step of the filtration when `ω` is a pulled-back `k`-form. -/
theorem gradedTargetComplex_d (k : ℕ) (n m : ℤ) :
    (gradedTargetComplex f g k).d n m =
      (-(k : ℤ)).negOnePow •
        (coefficientRestriction f g).map
          ((pulledBackTargetFormsTensor f g k).map
            ((deRhamCochainComplex f).d (n + -(k : ℤ)) (m + -(k : ℤ)))) := by
  refine Eq.trans (Functor.mapHomologicalComplex_obj_d _ _ _ n m) ?_
  refine Eq.trans (congrArg (coefficientRestriction f g).map
    (CochainComplex.shiftFunctor_obj_d' (gradedTargetTensor f g k) (-(k : ℤ)) n m)) ?_
  exact Functor.map_zsmul (coefficientRestriction f g)

/-- **The target is concentrated in degrees `≥ k`**: below `k` the de Rham complex of `f` is
already zero, and tensoring with a fixed sheaf and restricting scalars are additive, hence carry
a zero object to a zero object. -/
theorem isZero_gradedTargetComplex_X (k : ℕ) (n : ℤ) (hn : n < (k : ℤ)) :
    IsZero ((gradedTargetComplex f g k).X n) :=
  (coefficientRestriction f g).map_isZero
    ((pulledBackTargetFormsTensor f g k).map_isZero
      (CochainComplex.isZero_of_isStrictlyGE (deRhamCochainComplex f) 0 (n + -(k : ℤ))
        (by omega)))

end Stacks.DeRhamSmooth

end
