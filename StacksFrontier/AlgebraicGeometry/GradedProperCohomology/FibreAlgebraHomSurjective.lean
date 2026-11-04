module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedFiniteTypeRestrictScalars
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesPullbackChart
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.BaseReesPullbackLocallySurjective
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.FibreAssociatedGradedFiniteType
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.FibreAssociatedGradedHypotheses
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DiagonalConormal

/-!
# `Θ` is degreewise locally surjective, and the fibre's associated graded module is of finite type

Let
```
Z --i--> X
|g       |f
v        v
Y --j--> S
```
be a commutative square of schemes with `S` **affine**, and let `ℐ` be a quasi-coherent sheaf of
ideals on `S`. `Stacks.AssociatedGradedFibre.fibreAlgebraHom` is the homomorphism

`Θ : g^*(j^*(⨁ₙ ℐⁿ)) ⟶ i^*(⨁ₙ (ℐ𝒪_X)ⁿ)`

of sheaves of graded algebras on `Z` obtained by transposing the inverse-image comparison of
Rees algebras twice. This file proves that **every homogeneous component of `Θ` is locally
surjective**, and deduces the hypothesis `hft` of
`Stacks.GradedProperCohomology.exists_isZero_Hgroup_tensorPowTwist_int_fibreAssociatedGraded`:

`⨁ₙ i^*((ℐ𝒪_X)ⁿℱ)` is of finite type over `g^*(j^*(⨁ₙ ℐⁿ))`

for a quasi-coherent `ℱ` of finite type on `X`.
`Stacks.Blowup.isFiniteType_gradedPullbackReesGradedModule` gives finite type over the *larger*
algebra `i^*(⨁ₙ (ℐ𝒪_X)ⁿ)`, and the module the capstone consumes is that one restricted along `Θ`;
`SheafOfModules.GradedModule.isFiniteType_restrictScalars` closes the gap between the two exactly
when `Θ` is degreewise locally surjective, which is what is proved here.

## Why `Θ` is locally surjective, and the shape of the proof

Over an affine open `V'` of `Z` inside the preimage of an affine open `U` of `X` the sections of
the target `i^*((ℐ𝒪_X)ⁿ)` are spanned over `Γ(Z, V')` by the pullbacks of the sections of
`(ℐ𝒪_X)ⁿ` over `U` (`AlgebraicGeometry.span_pullbackSection_eq_top`), and the range of `Θ` on
sections is a `Γ(Z, V')`-submodule, so it is enough to hit each of those. A section of
`(ℐ𝒪_X)ⁿ` over the affine `U` is in turn in the image of the comparison
`Φ : f^*(⨁ₙ ℐⁿ) ⟶ ⨁ₙ (ℐ𝒪_X)ⁿ` of [Stacks, Tag 01OG] — this is
`Stacks.Blowup.surjective_reesPullbackComparisonLinear`, and it is where `S` affine is used,
the whole of `S` serving as the affine chart downstairs — and the sections of `f^*(ℐⁿ)` over `U`
are spanned by the pullbacks of the global sections of `ℐⁿ`. On such a generator both `Θ` and
`Φ` are computed by the *same* formula, the pullback along `i` of the inverse image
`Stacks.Blowup.reesPieceComap` of the section; so the generator is in the range of `Θ`.

## Main results

* `Stacks.AssociatedGradedFibre.fibreAlgebraHom_app_pullbackSection`: **the only description of
  `Θ`.** On the pullback along `g` of the pullback along `j` of a homogeneous section `a` of
  `ℐⁿ`, read over any open of `Z` below the preimage, `Θ` is the pullback along `i` of the
  inverse image of `a` under `f`. This is
  `Stacks.AssociatedGradedFibre.totalComparison_app` with the two adjoint transposes performed
  (`Stacks.RingedSpace.transposeApp_pullbackUnit`) and the transport along the square discharged
  by `subst`.
* `Stacks.AssociatedGradedFibre.isLocallySurjective_fibreAlgebraHom_app`: **`Θ` is degreewise
  locally surjective** over an affine `S`.
* `Stacks.AssociatedGradedFibre.isFiniteType_fibreAssociatedGradedModule`: **`⨁ₙ i^*((ℐ𝒪_X)ⁿℱ)`
  is of finite type as a graded `g^*(j^*(⨁ₙ ℐⁿ))`-module.**
* `exists_isZero_Hgroup_tensorPowTwist_int_fibreAssociatedGraded_of_isAffine` (in
  `Stacks.GradedProperCohomology`): the capstone of part (2) of [Stacks, Tag 0897] at the fibre
  with **all four of its hypotheses on the graded algebra and the graded module discharged**, over
  an affine, locally Noetherian base.

## Implementation notes

Every step is written as a term-level `Eq.trans` chain rather than with `rw`. The sections of a
pulled-back module have two spellings — `Γ(i^*N, V)` through `Scheme.Modules.presheaf` and
`(i^*N).val.obj (op V)` through the presheaf of modules — which are definitionally equal but of
which only the first carries the `Module Γ(Z, V)` instance, and only the second is the one the
pullback-section API produces. A goal mixing them is not type-correct at the transparency `rw`
builds its motive at; the same observation is recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Blowup.ReesPullbackChart`, which introduces
`Stacks.Blowup.reesPullbackComparison` for exactly this reason.

The implicit `A` and `C` of `Stacks.RingedSpace.transposeApp_pullbackUnit` are supplied
explicitly in `innerFibreHom_app_pullbackSection`. Left to unification they send the elaborator
into `whnf` on `pushforwardAlgebra (g ≫ j) D`, looking for a `?C` with
`pushforwardAlgebra j ?C = pushforwardAlgebra (g ≫ j) D`; the search does not terminate inside
the heartbeat budget. The definition of `Stacks.AssociatedGradedFibre.fibreAlgebraHom` pins the
same implicit for the same reason.

`S` is required affine. At the fibre of [Stacks, Tag 0D2N] it is `Spec A` for a Noetherian local
`A`, so this is no restriction there.

No `@[stacks]` attribute is attached: [Stacks, Tag 01OG] is registered on
`Stacks.Blowup.exists_reesAlgebraData` and [Stacks, Tag 0897] on the capstone it feeds; what is
here is a property of the comparison those proofs produce.

## References

* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 02O7](https://stacks.math.columbia.edu/tag/02O7)
* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 0D2N](https://stacks.math.columbia.edu/tag/0D2N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Blowup RingedSpaceModuleAdjunction
open SheafOfModules.GradedAlgebra (UnitalHom)
open Stacks.Conormal (gradedPullback)

universe u

namespace Stacks.AssociatedGradedFibre

variable {Z X Y S : Scheme.{u}} (i : Z ⟶ X) (f : X ⟶ S) (g : Z ⟶ Y) (j : Y ⟶ S)
  (I : S.IdealSheafData)

/-! ### The only description of `Θ` -/

/-- **The comparison `⨁ₙ ℐⁿ ⟶ m_*(i^*(⨁ₙ (ℐ𝒪_X)ⁿ))` of
`Stacks.AssociatedGradedFibre.comparisonAlong`, restricted to an open of `Z`**: it is the
pullback along `i` of the inverse image of the section under `f`.

The morphism `m : Z ⟶ S` is a variable and the equation `m = i ≫ f` is eliminated by `subst`,
which is what makes the statement type-correct for an `m` presented as the *other* side of the
square; the containment of the open of `Z` in the two preimages is taken as two hypotheses for
the same reason, both being proofs of the same `≤` once `m` is substituted. -/
theorem comparisonAlong_app_restrict (m : Z ⟶ S) (hm : m = i ≫ f) (n : ℤ) (V : S.Opens)
    (a : (reesPiece I n).val.obj (op V)) (W : Z.Opens) (hW : W ≤ m ⁻¹ᵁ V)
    (hW' : W ≤ i ⁻¹ᵁ (f ⁻¹ᵁ V)) :
    ((Scheme.Modules.pullback i).obj (reesPiece (I.comap f) n)).val.map
        (homOfLE hW).op (((comparisonAlong i f I m hm).app n).val.app (op V) a) =
      Scheme.Modules.pullbackSection i (reesPiece (I.comap f) n) (f ⁻¹ᵁ V) W hW'
        ((reesPieceComap f I n).val.app (op V) a) := by
  subst hm
  rw [comparisonAlong_self, totalComparison_app]
  rfl

/-- The inner of the two adjoint transposes making up
`Stacks.AssociatedGradedFibre.fibreAlgebraHom`: the transpose along `j` of
`comparisonAlong`, a homomorphism `j^*(⨁ₙ ℐⁿ) ⟶ g_*(i^*(⨁ₙ (ℐ𝒪_X)ⁿ))`. Named so that the
implicit target algebra is pinned once. -/
abbrev innerFibreHom (hsq : i ≫ f = g ≫ j) :
    UnitalHom (gradedPullback j (reesGradedAlgebra I))
      (Stacks.RingedSpace.pushforwardAlgebra g.toLRSHom.toShHom
        (gradedPullback i (reesGradedAlgebra (I.comap f)))) :=
  Stacks.RingedSpace.transposeUnitalHom
    (C := Stacks.RingedSpace.pushforwardAlgebra g.toLRSHom.toShHom
      (gradedPullback i (reesGradedAlgebra (I.comap f))))
    j.toLRSHom.toShHom (comparisonAlong i f I (g ≫ j) hsq.symm)

/-- `Θ` on the pullback-unit image of a homogeneous section of `j^*(⨁ₙ ℐⁿ)` is the inner
transpose on that section: the defining property of the outer transpose. -/
theorem fibreAlgebraHom_app_pullbackUnit (hsq : i ≫ f = g ≫ j) (n : ℤ) (V' : Y.Opens)
    (y : ((gradedPullback j (reesGradedAlgebra I)).piece n).val.obj (op V')) :
    ((fibreAlgebraHom i f g j I hsq).app n).val.app (op (g ⁻¹ᵁ V'))
        (Stacks.RingedSpace.pullbackUnit g.toLRSHom.toShHom
          ((gradedPullback j (reesGradedAlgebra I)).piece n) (op V') y) =
      ((innerFibreHom i f g j I hsq).app n).val.app (op V') y :=
  Stacks.RingedSpace.transposeApp_pullbackUnit g.toLRSHom.toShHom
    (innerFibreHom i f g j I hsq) n V' y

/-- The inner transpose on the pullback along `j` of a homogeneous section of `ℐⁿ` is
`comparisonAlong` on that section. -/
theorem innerFibreHom_app_pullbackSection (hsq : i ≫ f = g ≫ j) (n : ℤ) (V : S.Opens)
    (a : (reesPiece I n).val.obj (op V)) :
    ((innerFibreHom i f g j I hsq).app n).val.app (op (j ⁻¹ᵁ V))
        (Scheme.Modules.pullbackSection j (reesPiece I n) V (j ⁻¹ᵁ V) le_rfl a) =
      ((comparisonAlong i f I (g ≫ j) hsq.symm).app n).val.app (op V) a := by
  rw [Stacks.Conormal.pullbackSection_self j (reesPiece I n) V a]
  exact Stacks.RingedSpace.transposeApp_pullbackUnit (A := reesGradedAlgebra I)
    (C := Stacks.RingedSpace.pushforwardAlgebra g.toLRSHom.toShHom
      (gradedPullback i (reesGradedAlgebra (I.comap f))))
    j.toLRSHom.toShHom (comparisonAlong i f I (g ≫ j) hsq.symm) n V a

/-- **The only description of `Θ`.** On the pullback along `g` of the pullback along `j` of a
homogeneous section `a` of `ℐⁿ` over an open `V` of `S`, read over any open `W` of `Z` below the
preimage of `V`, `Θ` is the pullback along `i` of the inverse image of `a` under `f`.

Both adjoint transposes are evaluated by `Stacks.RingedSpace.transposeApp_pullbackUnit`, and the
passage from the whole preimage to `W` is naturality of `Θ` in degree `n`. -/
theorem fibreAlgebraHom_app_pullbackSection (hsq : i ≫ f = g ≫ j) (n : ℤ) (V : S.Opens)
    (a : (reesPiece I n).val.obj (op V)) (W : Z.Opens) (hW : W ≤ g ⁻¹ᵁ (j ⁻¹ᵁ V))
    (hW' : W ≤ i ⁻¹ᵁ (f ⁻¹ᵁ V)) :
    ((fibreAlgebraHom i f g j I hsq).app n).val.app (op W)
        (Scheme.Modules.pullbackSection g
          ((gradedPullback j (reesGradedAlgebra I)).piece n) (j ⁻¹ᵁ V) W hW
          (Scheme.Modules.pullbackSection j (reesPiece I n) V (j ⁻¹ᵁ V) le_rfl a)) =
      Scheme.Modules.pullbackSection i (reesPiece (I.comap f) n) (f ⁻¹ᵁ V) W hW'
        ((reesPieceComap f I n).val.app (op V) a) := by
  refine (PresheafOfModules.naturality_apply
    ((fibreAlgebraHom i f g j I hsq).app n).val (homOfLE hW).op
    (Stacks.RingedSpace.pullbackUnit g.toLRSHom.toShHom
      ((gradedPullback j (reesGradedAlgebra I)).piece n) (op (j ⁻¹ᵁ V))
      (Scheme.Modules.pullbackSection j (reesPiece I n) V (j ⁻¹ᵁ V) le_rfl a))).trans ?_
  have h3 := (fibreAlgebraHom_app_pullbackUnit i f g j I hsq n (j ⁻¹ᵁ V)
      (Scheme.Modules.pullbackSection j (reesPiece I n) V (j ⁻¹ᵁ V) le_rfl a)).trans
    (innerFibreHom_app_pullbackSection i f g j I hsq n V a)
  exact (congrArg _ h3).trans
    (comparisonAlong_app_restrict i f I (g ≫ j) hsq.symm n V a W hW hW')

/-- **The comparison `Φ : g^*(⨁ₙ ℐⁿ) ⟶ ⨁ₙ (ℐ𝒪_Z)ⁿ` of [Stacks, Tag 01OG] on a pullback
section over an arbitrary open below the preimage.**
`Stacks.Blowup.reesGradedPullbackHom_pullbackSection` is the case of the whole preimage; this is
it followed by naturality. -/
theorem reesGradedPullbackHom_app_pullbackSection {Z' X' : Scheme.{u}} (g' : Z' ⟶ X')
    (J : X'.IdealSheafData) (n : ℤ) (V : X'.Opens) (a : (reesPiece J n).val.obj (op V))
    (W : Z'.Opens) (hW : W ≤ g' ⁻¹ᵁ V) :
    ((reesGradedPullbackHom g' J).app n).val.app (op W)
        (Scheme.Modules.pullbackSection g' (reesPiece J n) V W hW a) =
      (reesPiece (J.comap g') n).val.map (homOfLE hW).op
        ((reesPieceComap g' J n).val.app (op V) a) := by
  refine (PresheafOfModules.naturality_apply ((reesGradedPullbackHom g' J).app n).val
    (homOfLE hW).op (Stacks.RingedSpace.pullbackUnit g'.toLRSHom.toShHom (reesPiece J n)
      (op V) a)).trans ?_
  exact congrArg _ (Stacks.RingedSpace.transposeApp_pullbackUnit g'.toLRSHom.toShHom
    (reesComapUnitalHom g' J) n V a)

/-! ### Local surjectivity -/

/-- `Θ` in degree `n` on the sections over an open of `Z`, as a `Γ(Z, V)`-linear map, so that its
range is a submodule. -/
def fibreAlgebraHomLinear (hsq : i ≫ f = g ≫ j) (n : ℤ) (V : Z.Opens) :
    Γ((Scheme.Modules.pullback g).obj
        ((gradedPullback j (reesGradedAlgebra I)).piece n), V) →ₗ[Γ(Z, V)]
      Γ((Scheme.Modules.pullback i).obj (reesPiece (I.comap f) n), V) where
  toFun x := Scheme.Modules.Hom.app ((fibreAlgebraHom i f g j I hsq).app n) V x
  map_add' x y := map_add (ConcreteCategory.hom
    (Scheme.Modules.Hom.app ((fibreAlgebraHom i f g j I hsq).app n) V)) x y
  map_smul' r x := Scheme.Modules.Hom.app_smul ((fibreAlgebraHom i f g j I hsq).app n) r x

/-- `fibreAlgebraHomLinear` is the component of `Θ` in degree `n` on the sections over `V`. -/
@[simp] theorem fibreAlgebraHomLinear_apply (hsq : i ≫ f = g ≫ j) (n : ℤ) (V : Z.Opens)
    (x : Γ((Scheme.Modules.pullback g).obj
      ((gradedPullback j (reesGradedAlgebra I)).piece n), V)) :
    fibreAlgebraHomLinear i f g j I hsq n V x =
      ((fibreAlgebraHom i f g j I hsq).app n).val.app (op V) x := rfl

/-- **The pullback along `i` of the value of `Φ` on the pullback along `f` of a global section of
`ℐⁿ` is in the range of `Θ`.** This is the generating case of the local surjectivity: on such a
section both sides are the pullback along `i` of the inverse image of the section, by
`Stacks.AssociatedGradedFibre.fibreAlgebraHom_app_pullbackSection` and
`reesGradedPullbackHom_app_pullbackSection`. -/
theorem mem_range_fibreAlgebraHomLinear_pullbackSection [IsAffine S] (hsq : i ≫ f = g ≫ j)
    (n : ℤ) {U : X.Opens} {V' : Z.Opens} (hV'U : V' ≤ i ⁻¹ᵁ U) (hUtop : U ≤ f ⁻¹ᵁ ⊤)
    (a : (reesPiece I n).val.obj (op ⊤)) :
    Scheme.Modules.pullbackSection i (reesPiece (I.comap f) n) U V' hV'U
        ((reesPullbackComparisonLinear f I n U)
          (pullbackSectionΓ f (Stacks.Conormal.reesModule I n) ⊤ U hUtop a)) ∈
      LinearMap.range (fibreAlgebraHomLinear i f g j I hsq n V') := by
  have hx : ((fibreAlgebraHom i f g j I hsq).app n).val.app (op V')
        (Scheme.Modules.pullbackSection g
          ((gradedPullback j (reesGradedAlgebra I)).piece n) (j ⁻¹ᵁ ⊤) V' le_top
          (Scheme.Modules.pullbackSection j (reesPiece I n) ⊤ (j ⁻¹ᵁ ⊤) le_rfl a)) =
      Scheme.Modules.pullbackSection i (reesPiece (I.comap f) n) U V' hV'U
        ((reesPullbackComparisonLinear f I n U)
          (pullbackSectionΓ f (Stacks.Conormal.reesModule I n) ⊤ U hUtop a)) :=
    (fibreAlgebraHom_app_pullbackSection i f g j I hsq n ⊤ a V' le_top le_top).trans
      ((Stacks.Conormal.pullbackSection_restrict_source i (reesPiece (I.comap f) n)
          (f ⁻¹ᵁ ⊤) U hUtop V' hV'U ((reesPieceComap f I n).val.app (op ⊤) a)).trans
        (congrArg _ (reesGradedPullbackHom_app_pullbackSection f I n ⊤ a U hUtop).symm))
  exact ⟨_, hx⟩

/-- **The pullback along `i` of every section of `(ℐ𝒪_X)ⁿ` over an affine open `U` of `X` is in
the range of `Θ` over any open of `Z` below `i⁻¹U`.**

A section over the affine `U` is the value of `Φ` on a section of `f^*(ℐⁿ)` over `U`
(`Stacks.Blowup.surjective_reesPullbackComparisonLinear`, the affine chart downstairs being the
whole of `S`), and the sections of `f^*(ℐⁿ)` over `U` are spanned by the pullbacks of the global
sections of `ℐⁿ` (`AlgebraicGeometry.span_pullbackSection_eq_top`); pulling back along `i` is
additive and semilinear, so the span induction reduces to the generating case. -/
theorem mem_range_fibreAlgebraHomLinear [IsAffine S] (hsq : i ≫ f = g ≫ j)
    (n : ℤ) (hn : 0 ≤ n) {U : X.Opens} (hU : IsAffineOpen U) {V' : Z.Opens}
    (hV'U : V' ≤ i ⁻¹ᵁ U) (t : Γ(reesPiece (I.comap f) n, U)) :
    Scheme.Modules.pullbackSection i (reesPiece (I.comap f) n) U V' hV'U t ∈
      LinearMap.range (fibreAlgebraHomLinear i f g j I hsq n V') := by
  obtain ⟨w, hw⟩ := surjective_reesPullbackComparisonLinear f I n hn
    ⟨⊤, isAffineOpen_top S⟩ ⟨U, hU⟩ le_top t
  subst hw
  have : (reesPiece I n).IsQuasicoherent := reesPiece_isQuasicoherent I n
  have hspan : w ∈ Submodule.span Γ(X, U)
      (Set.range fun b : Γ(reesPiece I n, ⊤) =>
        AlgebraicGeometry.pullbackSectionHom f (reesPiece I n) ⊤ U le_top b) := by
    rw [AlgebraicGeometry.span_pullbackSection_eq_top f (reesPiece I n)
      (isAffineOpen_top S) hU le_top]
    exact Submodule.mem_top
  set PB := fun z : Γ(reesPiece (I.comap f) n, U) =>
    Scheme.Modules.pullbackSection i (reesPiece (I.comap f) n) U V' hV'U z with hPBdef
  set Φ := reesPullbackComparisonLinear f I n U with hΦdef
  set Θ := fibreAlgebraHomLinear i f g j I hsq n V' with hΘdef
  induction hspan using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      exact mem_range_fibreAlgebraHomLinear_pullbackSection i f g j I hsq n hV'U le_top b
  | zero =>
      exact ⟨0, (map_zero Θ).trans
        ((Stacks.Conormal.pullbackSection_zero i (reesPiece (I.comap f) n) U V' hV'U).symm.trans
          (congrArg PB (map_zero Φ).symm))⟩
  | add x y _ _ hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨v, hv⟩ := hy
      exact ⟨u + v, (map_add Θ u v).trans ((congrArg₂ (· + ·) hu hv).trans
        ((Stacks.Conormal.pullbackSection_add i (reesPiece (I.comap f) n) U V' hV'U
            (Φ x) (Φ y)).symm.trans (congrArg PB (map_add Φ x y).symm)))⟩
  | smul r x _ hx =>
      obtain ⟨u, hu⟩ := hx
      refine ⟨(show Γ(Z, V') from (i.appLE U V' hV'U).hom (show Γ(X, U) from r)) • u, ?_⟩
      exact (map_smul Θ _ u).trans ((congrArg (fun z => _ • z) hu).trans
        ((Stacks.Conormal.pullbackSection_smul_le i (reesPiece (I.comap f) n) U V' hV'U
            r (Φ x)).symm.trans (congrArg PB (map_smul Φ r x).symm)))

/-- **Every homogeneous component of `Θ` is locally surjective**, over an affine `S`.

In a negative degree the target is a zero object
(`Stacks.Conormal.gradedPullback_negative_isZero`), so the component is surjective outright. In a
nonnegative degree, every point of an open of `Z` has an affine neighbourhood inside the preimage
of an affine open of `X`, and over such a neighbourhood the sections of the target are spanned by
the pullbacks of the sections upstairs
(`AlgebraicGeometry.span_pullbackSection_eq_top`), all of which lie in the range of `Θ` by
`Stacks.AssociatedGradedFibre.mem_range_fibreAlgebraHomLinear`. -/
theorem isLocallySurjective_fibreAlgebraHom_app [IsAffine S] (hsq : i ≫ f = g ≫ j) (n : ℤ) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (Z : TopCat))
      ((PresheafOfModules.toPresheaf Z.ringCatSheaf.obj).map
        ((fibreAlgebraHom i f g j I hsq).app n).val) := by
  rcases lt_or_ge n 0 with hn | hn
  · refine Presheaf.isLocallySurjective_of_surjective _ _ ?_
    intro W y
    refine ⟨0, ?_⟩
    have hsub : Subsingleton
        ↥(((gradedPullback i (reesGradedAlgebra (I.comap f))).piece n).val.obj W) :=
      Stacks.subsingleton_of_isZero (Stacks.Conormal.gradedPullback_negative_isZero i
        (reesGradedAlgebra (I.comap f)) (reesPiece_negative_isZero (I.comap f)) n hn) W
    exact @Subsingleton.elim _ hsub _ _
  · have : (reesPiece (I.comap f) n).IsQuasicoherent := reesPiece_isQuasicoherent (I.comap f) n
    constructor
    intro W s
    rw [Opens.mem_grothendieckTopology]
    intro z hz
    obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (i.base z)) isOpen_univ
    obtain ⟨_, ⟨V', hV', rfl⟩, hzV', hV'sub⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
      (show z ∈ ((W ⊓ i ⁻¹ᵁ U : Z.Opens) : Set Z) from ⟨hz, hzU⟩) (W ⊓ i ⁻¹ᵁ U).2
    have hV'le : V' ≤ W ⊓ i ⁻¹ᵁ U := hV'sub
    have hV'W : V' ≤ W := hV'le.trans inf_le_left
    have hV'U : V' ≤ i ⁻¹ᵁ U := hV'le.trans inf_le_right
    have hle : (⊤ : Submodule Γ(Z, V') _) ≤
        LinearMap.range (fibreAlgebraHomLinear i f g j I hsq n V') := by
      rw [← AlgebraicGeometry.span_pullbackSection_eq_top i (reesPiece (I.comap f) n) hU hV' hV'U,
        Submodule.span_le]
      rintro x ⟨t, rfl⟩
      exact mem_range_fibreAlgebraHomLinear i f g j I hsq n hn hU hV'U t
    obtain ⟨t, ht⟩ := hle (x := ((Scheme.Modules.pullback i).obj
      (reesPiece (I.comap f) n)).presheaf.map (homOfLE hV'W).op s) Submodule.mem_top
    exact ⟨V', homOfLE hV'W, ⟨t, ht⟩, hzV'⟩

/-! ### Finite type of the fibre's associated graded module -/

/-- **`⨁ₙ i^*((ℐ𝒪_X)ⁿℱ)` is of finite type as a graded `g^*(j^*(⨁ₙ ℐⁿ))`-module**, for a
quasi-coherent `ℱ` of finite type on `X` and an affine `S`.

`Stacks.Blowup.isFiniteType_gradedPullbackReesGradedModule` gives finite type over the larger
algebra `i^*(⨁ₙ (ℐ𝒪_X)ⁿ)`, and
`SheafOfModules.GradedModule.isFiniteType_restrictScalars` carries it along `Θ`, which is
degreewise locally surjective. This is the hypothesis `hft` of
`Stacks.GradedProperCohomology.exists_isZero_Hgroup_tensorPowTwist_int_fibreAssociatedGraded`. -/
theorem isFiniteType_fibreAssociatedGradedModule [IsAffine S] (ℱ : X.Modules)
    [ℱ.IsQuasicoherent]
    [PresheafOfModules.IsFiniteType (Opens.grothendieckTopology (X : TopCat)) ℱ.val]
    (hsq : i ≫ f = g ≫ j) :
    (fibreAssociatedGradedModule i f g j I ℱ hsq).IsFiniteType :=
  have := Stacks.Blowup.isFiniteType_gradedPullbackReesGradedModule i (I.comap f) ℱ
  SheafOfModules.GradedModule.isFiniteType_restrictScalars
    (fun n => isLocallySurjective_fibreAlgebraHom_app i f g j I hsq n)
    (Stacks.Conormal.gradedPullbackModule i (reesGradedModule (I.comap f) ℱ))

end Stacks.AssociatedGradedFibre

namespace Stacks.GradedProperCohomology

open Stacks.Ample Stacks.RelativeVeryAmple Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open Stacks.AlgebraicGeometry.FiniteTypeDominating
open Stacks.AmpleLocallyClosed (pullbackModule)
open Stacks.AssociatedGradedFibre

variable {Z X S : Scheme.{u}} (i : Z ⟶ X) (f : X ⟶ S) {k : Type u} [CommRing k]
  (g : Z ⟶ Spec (CommRingCat.of k)) (j : Spec (CommRingCat.of k) ⟶ S) (I : S.IdealSheafData)

/-- **Part (2) of [Stacks, Tag 0897] at the fibre, with every hypothesis on the graded algebra
and on the graded module discharged.**

`Stacks.GradedProperCohomology.exists_isZero_Hgroup_tensorPowTwist_int_fibreAssociatedGraded`
with its four open hypotheses supplied: quasi-coherence of the two algebra sheaves and the class
form of the commutativity are instances from
`StacksFrontier.AlgebraicGeometry.GradedProperCohomology.FibreAssociatedGradedHypotheses`, the
quasi-coherence `hB` of the ungraded realization and the local Noetherianness of the relative
spectrum come from the same file, and finite type of the module is
`Stacks.AssociatedGradedFibre.isFiniteType_fibreAssociatedGradedModule`.

What remains are the data the construction cannot supply: properness of `g`, the Noetherian
`k`-algebra `R` with its identification `ρ` of the global sections of `⨁ₙ j^*(ℐⁿ)` and the
compatibility `hρ`, and ampleness `hL` upstairs. At [Stacks, Tag 0D2N] — `S = Spec A` for a
Noetherian local `A`, `ℐ = 𝔪`, `k = κ(y)`, `Z = X_y` and `R = Gr_𝔪(A)` — `hL` is
[Stacks, Tag 0892] part (2) from ampleness of `ℒ_y`, and `R` is Noetherian by
`AssociatedGraded.isNoetherianRing_gradedRing`. -/
theorem exists_isZero_Hgroup_tensorPowTwist_int_fibreAssociatedGraded_of_isAffine
    [IsAffine S] [IsLocallyNoetherian S] [IsLocallyNoetherian Z]
    (hg : AlgebraicGeometry.IsProper g)
    {R : Type u} [CommRing R] [IsNoetherianRing R] [Algebra k R]
    (ρ : R ≃+* ↥((gradedAlgebraSheaf (Spec (CommRingCat.of k))
      (Stacks.Conormal.gradedPullback j (Stacks.Blowup.reesGradedAlgebra I))
      (associatedGradedAlgebra_mul_comm j I)).sections ⊤))
    (hρ : ∀ r : k, ρ (algebraMap k R r) =
      (gradedAlgebraSheaf (Spec (CommRingCat.of k))
        (Stacks.Conormal.gradedPullback j (Stacks.Blowup.reesGradedAlgebra I))
        (associatedGradedAlgebra_mul_comm j I)).unitTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv r))
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    [PresheafOfModules.IsFiniteType (Opens.grothendieckTopology (X : TopCat)) ℱ.val]
    (hsq : i ≫ f = g ≫ j)
    (L : Z.Modules) [IsInvertibleModule Z L]
    (hL : IsAmple (relativeSpecOver (pullbackGradedAlgebraSheaf g
        (Stacks.Conormal.gradedPullback j (Stacks.Blowup.reesGradedAlgebra I))
        (associatedGradedAlgebra_mul_comm j I))).left
      (pullbackModule (relativeSpecOver (pullbackGradedAlgebraSheaf g
        (Stacks.Conormal.gradedPullback j (Stacks.Blowup.reesGradedAlgebra I))
        (associatedGradedAlgebra_mul_comm j I))).hom L)) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ p : ℕ, 0 < p → ∀ n : ℕ,
      IsZero (Hgroup Z.ringCatSheaf ⊤ p
        (tensorModules Z ((fibreAssociatedGradedModule i f g j I ℱ hsq).piece (n : ℤ))
          (tensorPowModule Z L d))) :=
  have := isLocallyNoetherian_relativeSpecOver_fibreAssociatedGraded j I g
    (fun U => have := IsLocallyNoetherian.component_noetherian (X := S) U
      IsNoetherian.noetherian (I.ideal U))
  exists_isZero_Hgroup_tensorPowTwist_int_fibreAssociatedGraded i f g j I hg ρ hρ ℱ hsq
    (isQuasicoherent_ungradedRealization_fibreAssociatedGraded j I g)
    (isFiniteType_fibreAssociatedGradedModule i f g j I ℱ hsq) L hL

end Stacks.GradedProperCohomology

end
