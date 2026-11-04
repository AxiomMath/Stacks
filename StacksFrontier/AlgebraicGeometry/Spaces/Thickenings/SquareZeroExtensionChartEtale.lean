module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineKernelBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionShortExact
public import StacksFrontier.RingTheory.Etale.Basic

/-!
# The charts of a square-zero extension of the structure sheaf are étale over one another

Let `0 ⟶ ℐ ⟶ 𝒜 ⟶ 𝒪_X ⟶ 0` be a square-zero extension of the structure sheaf of an algebraic
space `X` over `Y`, in the sense of
`AlgebraicGeometry.Space.SquareZeroExtension`.  [Stacks Project, Tag 05ZT] builds its realizing
thickening out of the charts `U ↦ Spec(𝒜(U))`, and the step that makes that assignment an
*étale* diagram is the following ring-level statement: for a morphism `h : U ⟶ V` of the small
étale site of `X` between objects with affine underlying scheme,

* `𝒪_X(V) ⟶ 𝒪_X(U)` is étale, because `h` induces an étale morphism of the underlying schemes;
* `𝒜(V) ⟶ 𝒪_X(V)` and `𝒜(U) ⟶ 𝒪_X(U)` are surjective with square-zero kernel; and
* `ℐ(U) = ℐ(V) ⊗_{𝒜(V)} 𝒜(U)`, which is where the quasi-coherence of `ℐ` is spent;

hence `𝒜(V) ⟶ 𝒜(U)` is étale, by [Stacks Project, Tag 05YT].  This file proves that
implication.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.algebraEtale_gamma_of_isAffine`: **between two objects of
  the small étale site with affine underlying scheme the induced map of rings of global functions
  is étale.**  This is the étale companion of
  `AlgebraicGeometry.Space.SmallEtale.flat_gamma_of_isAffine`, with the same shape: the morphism
  of schemes is étale by `AlgebraicGeometry.Space.SmallEtale.etale_map`, and an étale morphism of
  affine schemes has étale map of global functions.
* `AlgebraicGeometry.Space.SquareZeroExtension.algebraEtale_app_of_isBaseChange`: **the sections
  of the extension sheaf over an object of the small étale site are an étale algebra over its
  sections over any object it maps to**, provided both charts are affine and the kernel over the
  source is the base change of the kernel over the target.

## Implementation notes

**What is assumed and what is proved.**  The surjectivity of `𝒜(U) ⟶ 𝒪_X(U)` over an affine
object is *not* an assumption of Tag 05ZT; it is the first step of its proof, and it is proved
here rather than assumed, by
`AlgebraicGeometry.Space.SquareZeroExtension.surjective_π_app_of_isAffine`, which is
`AlgebraicGeometry.Space.surjective_app_of_shortExact_of_isQuasicoherentOnSite` applied to the
short exact sequence `AlgebraicGeometry.Space.SquareZeroExtension.shortComplex` of abelian
sheaves.  So affineness of the two charts is all that is asked on that count.

The base-change hypothesis is an argument of this statement, and it is discharged in
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/SquareZeroExtensionChartKernelBaseChange.lean`,
which makes the conclusion unconditional at an arbitrary pair of affine charts
(`AlgebraicGeometry.Space.SquareZeroExtension.algebraEtale_app_of_isAffine`).  It is the content
of the quasi-coherence of `ℐ`, and two steps separate the two statements.  First, quasi-coherence
has to be read at an arbitrary pair of affine charts rather than over the members of *some*
covering family of one of them, which is
`AlgebraicGeometry.Space.SmallEtale.bijective_liftBaseChange_of_isQuasicoherentOnSite`.  Second,
base change along `𝒪_X(V) ⟶ 𝒪_X(U)` of the `𝒪_X(V)`-module `ℐ(V)` has to be identified with base
change along `𝒜(V) ⟶ 𝒜(U)`, which is
`Module.BaseChange.bijective_liftBaseChange_of_ker_le_map_ker` and rests on
`ker(𝒜(V) ⟶ 𝒪_X(V)) · 𝒜(U) = ker(𝒜(U) ⟶ 𝒪_X(U))`.

**The algebra structures are the consumer's own.**  Only `Algebra 𝒜(V) 𝒜(U)` is an argument,
together with the identification `halg` of its structure map with the restriction map of `𝒜`; it
has to be, because the base-change hypothesis is a statement about `𝒜(V)`-modules.  The four
other algebra structures and the two scalar towers that
`Algebra.Etale.of_ker_sq_eq_bot_of_isBaseChange` wants are built inside the proof from the
reduction maps and the naturality square of `π`, so they are not hypotheses to be matched.  This
is the convention of
`AlgebraicGeometry.Space.SmallEtale.flat_gamma_of_isAffine` and of the scheme-level consumer
`Stacks.Thickenings.etale_of_isKerBaseChange` in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/ThickeningMorphism/Etale.lean`.

**No `@[stacks]` attribute.**  Tag 05ZT is the existence of the realizing thickening; this is one
step of its proof.  Tag 05YT is already registered on
`Algebra.Etale.of_ker_sq_eq_bot_of_isBaseChange`, which this applies.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
* [Stacks Project, Tag 05YT](https://stacks.math.columbia.edu/tag/05YT)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Étaleness of the structure sheaf on affine charts -/

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **Between two objects of the small étale site with affine underlying scheme the induced map
of rings of global functions is étale.**  The morphism of schemes is étale by
`AlgebraicGeometry.Space.SmallEtale.etale_map`, and an étale morphism of affine schemes has étale
map of global functions.

This is the étale companion of `AlgebraicGeometry.Space.SmallEtale.flat_gamma_of_isAffine`, which
proves the same thing for flatness, and it is stated the same way: the algebra structure is the
consumer's own, identified with the induced map by `halg`. -/
theorem SmallEtale.algebraEtale_gamma_of_isAffine {U W : SmallEtale B S hS F} (h : U ⟶ W)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U)))
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W)))
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U), ⊤)]
    (halg : algebraMap
        Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U), ⊤) =
      ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map h)).appTop.hom) :
    Algebra.Etale
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U), ⊤) := by
  have _ := hU
  have _ := hW
  have _ : Etale ((BigFppfOver.toScheme B S hS).map
    ((SmallEtale.toOver B S hS F).map h)) := SmallEtale.etale_map B S hS F h
  refine RingHom.etale_algebraMap.mp ?_
  rw [halg]
  exact HasRingHomProperty.appTop (P := @Etale) _ inferInstance

/-! ### Étaleness of the sections of the extension sheaf -/

/-- **The sections of a square-zero extension of the structure sheaf over an object of the small
étale site are an étale algebra over its sections over any object it maps to**, when both charts
are affine and the kernel over the source is the base change of the kernel over the target.

This is the étaleness of `Spec(𝒜(U)) ⟶ Spec(𝒜(V))` that makes the chart diagram
`U ↦ Spec(𝒜(U))` of [Stacks Project, Tag 05ZT] an étale diagram.  It is
[Stacks Project, Tag 05YT] applied to the square

```
𝒜(V) ⟶ 𝒜(U)
  ↓        ↓
𝒪_X(V) ⟶ 𝒪_X(U)
```

whose bottom row is étale because `h` induces an étale morphism of the underlying schemes, whose
columns are surjective by
`AlgebraicGeometry.Space.SquareZeroExtension.surjective_π_app_of_isAffine` with square-zero
kernel by `AlgebraicGeometry.Space.SquareZeroExtension.ker_pow_two_eq_bot`, and whose kernels are
related by base change by hypothesis. -/
theorem SquareZeroExtension.algebraEtale_app_of_isBaseChange
    {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)
    {U V : SmallEtale B S hS X.1} (h : U ⟶ V)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj U)))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V)))
    [Algebra (E.A.val.obj (op V)) (E.A.val.obj (op U))]
    (halg : algebraMap (E.A.val.obj (op V)) (E.A.val.obj (op U)) = (E.A.val.map h.op).hom)
    (g : RingHom.ker (E.π.hom.app (op V)).hom →ₗ[E.A.val.obj (op V)]
      RingHom.ker (E.π.hom.app (op U)).hom)
    (hg : ∀ x, ((g x : E.A.val.obj (op U)) : E.A.val.obj (op U)) =
      algebraMap (E.A.val.obj (op V)) (E.A.val.obj (op U)) (x : E.A.val.obj (op V)))
    (hbc : IsBaseChange (E.A.val.obj (op U)) g) :
    Algebra.Etale (E.A.val.obj (op V)) (E.A.val.obj (op U)) := by
  let : Algebra (E.A.val.obj (op V)) ((smallEtaleRingedTopos B S hS X).O.val.obj (op V)) :=
    (E.π.hom.app (op V)).hom.toAlgebra
  let : Algebra (E.A.val.obj (op U)) ((smallEtaleRingedTopos B S hS X).O.val.obj (op U)) :=
    (E.π.hom.app (op U)).hom.toAlgebra
  let : Algebra ((smallEtaleRingedTopos B S hS X).O.val.obj (op V))
      ((smallEtaleRingedTopos B S hS X).O.val.obj (op U)) :=
    ((smallEtaleRingedTopos B S hS X).O.val.map h.op).hom.toAlgebra
  let : Algebra (E.A.val.obj (op V)) ((smallEtaleRingedTopos B S hS X).O.val.obj (op U)) :=
    ((E.π.hom.app (op U)).hom.comp (E.A.val.map h.op).hom).toAlgebra
  -- The naturality square of the reduction, as a square of ring maps.
  have hsq : (E.π.hom.app (op U)).hom.comp (E.A.val.map h.op).hom =
      ((smallEtaleRingedTopos B S hS X).O.val.map h.op).hom.comp
        (E.π.hom.app (op V)).hom := by
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, E.π.hom.naturality h.op]
  have htower₁ : IsScalarTower (E.A.val.obj (op V)) (E.A.val.obj (op U))
      ((smallEtaleRingedTopos B S hS X).O.val.obj (op U)) :=
    IsScalarTower.of_algebraMap_eq' (by
      show (E.π.hom.app (op U)).hom.comp (E.A.val.map h.op).hom =
        (E.π.hom.app (op U)).hom.comp
          (algebraMap (E.A.val.obj (op V)) (E.A.val.obj (op U)))
      rw [halg])
  have htower₂ : IsScalarTower (E.A.val.obj (op V))
      ((smallEtaleRingedTopos B S hS X).O.val.obj (op V))
      ((smallEtaleRingedTopos B S hS X).O.val.obj (op U)) :=
    IsScalarTower.of_algebraMap_eq' hsq
  -- The bottom row of the square is étale.
  have hetO : Algebra.Etale ((smallEtaleRingedTopos B S hS X).O.val.obj (op V))
      ((smallEtaleRingedTopos B S hS X).O.val.obj (op U)) :=
    @SmallEtale.algebraEtale_gamma_of_isAffine B S hS X.1 U V h hU hV
      ((smallEtaleRingedTopos B S hS X).O.val.map h.op).hom.toAlgebra
      (congrArg CommRingCat.Hom.hom (Scheme.Γ_map_op
        ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map h))))
  exact Algebra.Etale.of_ker_sq_eq_bot_of_isBaseChange
    (SquareZeroExtension.surjective_π_app_of_isAffine B S hS E V hV)
    (SquareZeroExtension.surjective_π_app_of_isAffine B S hS E U hU)
    (SquareZeroExtension.ker_pow_two_eq_bot B S hS E (op V)) g hg hbc

end AlgebraicGeometry.Space

end
