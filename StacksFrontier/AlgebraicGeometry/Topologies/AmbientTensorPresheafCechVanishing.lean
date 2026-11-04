module

public import StacksFrontier.AlgebraicGeometry.Topologies.AffineSliceCoveringObject
public import StacksFrontier.AlgebraicGeometry.Topologies.AmbientTensorPresheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.CechVanishingOnAffineSlice
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardCoveringSingletonReduction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOfASingletonUpToIso

/-!
# Čech vanishing for the coefficient presheaf `Γ(-, 𝒪) ⊗_R M` of a bare module

Let `X` be an affine scheme, `R = Γ(X, 𝒪)` and `M` an `R`-module **at an arbitrary universe
`m`**.  `AlgebraicGeometry.overTensorPresheaf X M` is the presheaf `V ↦ Γ(V.left, 𝒪) ⊗_R M` of
abelian groups on `Over X`, at the coefficient universe `max u m`.  This file proves that its
higher Čech cohomology vanishes on a standard covering of the terminal object `Over.mk (𝟙 X)`
of `Over X`.

It is [Stacks, Tag 03FJ] for these coefficients, and it is the module-universe enlargement of
`AlgebraicGeometry.isZero_cechCohomology_succ_quasiCoherentPresheaf`, which is the same
statement for the coefficients `Fᵃ` of a `AlgebraicGeometry.Scheme.Modules` and hence only at
the universe `u` of the schemes.

## Why the covered object is the terminal object of `Over X`

`AlgebraicGeometry.isZero_cechCohomology_singleton_succ_overAffine`, the Amitsur endpoint of
Tag 03FJ on the slice at an object `U` of `Over S`, asks that the restriction of the coefficient
presheaf to `Over U` underlie a presheaf of `Γ(U.left, 𝒪)`-modules agreeing with the base change
`Γ(-, 𝒪) ⊗_{Γ(U.left, 𝒪)} M` on the fibre powers.  The ambient presheaf
`AlgebraicGeometry.overTensorPresheaf X M` tensors over `Γ(X, 𝒪)`; so the two tensor products
are over the same ring exactly when `U.left = X` with the identity structure morphism, that is
for `U = Over.mk (𝟙 X)`.  That is no restriction on the consumer: it is the object a chart
transport produces, `AlgebraicGeometry.Space.SmallEtale.sliceToOver` being a
`CategoryTheory.Over.post` and so carrying `Over.mk (𝟙 W)` to `Over.mk (𝟙 (chartScheme W))`.

The identity is carried as a hypothesis `g = 𝟙 X` on an endomorphism `g` of `X`, rather than
written into the object, because a `CategoryTheory.Over.post` carries `Over.mk (𝟙 W)` to
`Over.mk (G.map (𝟙 W))` on the nose and `G.map (𝟙 W) = 𝟙 (G.obj W)` is a functor law — for the
chart transport, `AlgebraicGeometry.Space.SmallEtale.sliceToOver_obj_mk_id_hom`.  Stated at
`Over.mk (𝟙 X)` these results would need that equality transported through a Čech complex.

## Main definitions

* `CategoryTheory.Over.postForgetIsoForgetMk`: **the identification of the two functors
  `Over (Over.mk g) ⥤ Over X`**, for `g : X ⟶ X` equal to the identity, that the two routes to
  the coordinate algebras restrict along, `CategoryTheory.Over.post
  (CategoryTheory.Over.forget X)` and `CategoryTheory.Over.forget (Over.mk g)`.  They agree on
  carriers, and their structure maps — `V.hom.left` and `V.left.hom` — agree because the
  structure morphism of the terminal object is the identity.

## Main results

* `AlgebraicGeometry.isZero_cechCohomology_singleton_succ_overTensorPresheaf`: the vanishing for
  a one-member covering of `Over.mk (𝟙 X)` by an affine object whose coordinate ring is
  faithfully flat over `R`.
* `AlgebraicGeometry.isZero_cechCohomology_succ_overTensorPresheaf`: **the vanishing for a
  standard `τ`-covering**, uniformly in the five topologies.

## Implementation notes

All four coefficient slots of
`AlgebraicGeometry.isZero_cechCohomology_singleton_succ_overAffine` are filled from what is
in the library, and only one of them has any content.

* `H`, the presheaf of `R`-modules on the slice, is taken to be
  `(AlgebraicGeometry.overAffineAlgΓ U).leftOp ⋙ Stacks.Descent.amitsurCoefficients R M`, which
  makes `hpow` the identity: `Stacks.CechSite.powerSections` is restriction along the conerve,
  and restriction along a functor is associative.
* `harrow` is `AlgebraicGeometry.sectionsTerminalArrowIsoAlgebraMapArrow`.
* `e` is `AlgebraicGeometry.gammaAlg_eq_comp_overGammaAlg` — the ambient coordinate algebras
  restrict along `CategoryTheory.Over.post` to the slice ones — composed with
  `AlgebraicGeometry.gammaAlgIsoOverAffineAlgΓ`, after
  `CategoryTheory.Over.postForgetIsoForgetMk` has identified the functor the first restricts
  along with `CategoryTheory.Over.forget (Over.mk (𝟙 X))`, which is the one the hypothesis is
  stated against.

The index universe of the covering family is the coefficient universe `max u m`: the Čech
complex of a family indexed by `I` needs products of `AddCommGrpCat.{max u m}` of size `I`, and
that category has them exactly for index types in `max u m`.  A consumer chooses the cofinal
system of coverings it applies the Čech criterion to, so it can present its families there.

The passage from the one-member covering to the family is
`AlgebraicGeometry.isIso_cechComplexMap_coproductRefinement_overTensorPresheaf`, Tag 03FI part
(3) for these coefficients, which carries no coefficient universe lift — unlike
`AlgebraicGeometry.isIso_cechComplexMap_coproductRefinement_over`, whose hypothesis is a sheaf
condition, which the tensor presheaf does not satisfy.  So no analogue of
`AlgebraicGeometry.isZero_cechCohomology_of_isZero_singleton_sigmaDesc` is needed and the lift
is not undone but absent.

## References

* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 03FI](https://stacks.math.columbia.edu/tag/03FI)
* [Stacks Project, Tag 03OZ](https://stacks.math.columbia.edu/tag/03OZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicTopology Stacks.CechSite Stacks.Descent
open scoped AlgebraicGeometry

universe m u v' u'

namespace CategoryTheory.Over

/-- **The two functors `Over (Over.mk g) ⥤ Over X` agree, for an endomorphism `g` of `X` equal
to the identity.**  `CategoryTheory.Over.post` of the slice projection sends an object `V` of the
double slice to its carrier with structure morphism `V.hom.left`, and
`CategoryTheory.Over.forget (Over.mk g)` sends it to the same carrier with structure morphism
`V.left.hom`.  The two structure morphisms agree because `CategoryTheory.Over.w` of `V.hom`
reads `V.hom.left ≫ g = V.left.hom`.

The object is written `Over.mk g` with `g = 𝟙 X` a hypothesis rather than `Over.mk (𝟙 X)`
outright, because that is the shape a slice transport produces: a
`CategoryTheory.Over.post` carries `Over.mk (𝟙 T)` to `Over.mk (G.map (𝟙 T))`, and
`G.map (𝟙 T) = 𝟙 (G.obj T)` is a functor law, not a definitional equality.

For a general object `U` of `Over X` the two functors do not even have the same target, and over
the same target they differ: the first produces `V.hom.left`, the second `V.left.hom`, and those
are related only by composition with `U.hom`. -/
public def postForgetIsoForgetMk {C : Type u'} [Category.{v'} C] {X : C} (g : X ⟶ X)
    (hg : g = 𝟙 X) :
    Over.post (X := Over.mk g) (Over.forget X) ≅ Over.forget (Over.mk g) :=
  NatIso.ofComponents
    (fun V ↦ Over.isoMk (Iso.refl V.left.left) (by
      change 𝟙 _ ≫ V.left.hom = V.hom.left
      rw [Category.id_comp, ← Over.w V.hom]
      simp [hg]))
    (fun φ ↦ Over.OverMorphism.ext (by
      change Over.Hom.left (Over.Hom.left φ) ≫ 𝟙 _ = 𝟙 _ ≫ Over.Hom.left (Over.Hom.left φ)
      simp))

end CategoryTheory.Over

namespace AlgebraicGeometry

/-- An object of `Over X` presented as `CategoryTheory.Over.mk` has affine total space when its
source does.  Instance search does not unfold `CategoryTheory.Over.mk`, so the bridge is
named. -/
public instance isAffine_left_mk {Y X : Scheme.{u}} (f : Y ⟶ X) [IsAffine Y] :
    IsAffine (Over.mk f).left :=
  ‹IsAffine Y›

variable (X : Scheme.{u}) [IsAffine X] (M : Type m) [AddCommGroup M]
  [Module (Scheme.Γ.obj (op X) : Type u) M] {g : X ⟶ X}

/-- **[Stacks, Tag 03FJ] for the coefficient presheaf `Γ(-, 𝒪) ⊗_R M` of a bare module, at a
one-member covering of the terminal object of `Over X` by an affine object.**

The only hypothesis is faithful flatness of the induced map on coordinate rings.  The three
coefficient hypotheses of
`AlgebraicGeometry.isZero_cechCohomology_singleton_succ_overAffine` are all discharged: `hpow`
is the identity, `harrow` is
`AlgebraicGeometry.sectionsTerminalArrowIsoAlgebraMapArrow`, and `e` is
`AlgebraicGeometry.gammaAlg_eq_comp_overGammaAlg` composed with
`AlgebraicGeometry.gammaAlgIsoOverAffineAlgΓ` across
`CategoryTheory.Over.postForgetIsoForgetMk`. -/
public theorem isZero_cechCohomology_singleton_succ_overTensorPresheaf (hg : g = 𝟙 X)
    {W : Over X} (f : W ⟶ Over.mk g) [IsAffine W.left]
    (hff : letI : Algebra (Γ(X, ⊤) : Type u) (Γ(W.left, ⊤) : Type u) :=
        f.left.appTop.hom.toAlgebra
      Module.FaithfullyFlat (Γ(X, ⊤) : Type u) (Γ(W.left, ⊤) : Type u))
    (p : ℕ) :
    IsZero (cechCohomology (PreZeroHypercover.singleton.{max u m} f)
      (overTensorPresheaf X M) (p + 1)) := by
  let : Module (Γ(X, ⊤) : Type u) M :=
    inferInstanceAs (Module (Scheme.Γ.obj (op X) : Type u) M)
  let : Module (Γ((Over.mk g).left, ⊤) : Type u) M :=
    inferInstanceAs (Module (Scheme.Γ.obj (op X) : Type u) M)
  let := overAffineSliceAlgebra (Over.mk g) f
  let : Module.FaithfullyFlat (Γ((Over.mk g).left, ⊤) : Type u)
      (Γ(W.left, ⊤) : Type u) := hff
  refine isZero_cechCohomology_singleton_of_iso.{max u m} f
    ((overAffineAlgSpec (Over.mk g)).obj
      (op (overAffineAlgObj (Over.mk g) (Γ(W.left, ⊤) : Type u)))).hom
    (mkIsoMkSpecOverAffineAlgObj (Over.mk g) f) (overTensorPresheaf X M) (p + 1) ?_
  exact isZero_cechCohomology_singleton_succ_overAffine (Over.mk g)
    (Γ(W.left, ⊤) : Type u) M (overTensorPresheaf X M)
    ((overAffineAlgΓ (Over.mk g)).leftOp ⋙
      amitsurCoefficients.{u, u, m} (Γ(X, ⊤) : Type u) M)
    (Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (NatIso.op (Over.postForgetIsoForgetMk g hg))
          (overGammaAlg X) ≪≫
        gammaAlgIsoOverAffineAlgΓ (Over.mk g))
      (amitsurCoefficients.{u, u, m} (Γ(X, ⊤) : Type u) M ⋙
        forget₂ (ModuleCat.{max u m} (Γ(X, ⊤) : Type u)) AddCommGrpCat.{max u m}))
    (overAffineAlgObj (Over.mk g) (Γ(W.left, ⊤) : Type u)) (Iso.refl _)
    (sectionsTerminalArrowIsoAlgebraMapArrow (Over.mk g) (Γ(W.left, ⊤) : Type u)) p

/-- **[Stacks, Tag 03FJ] for the coefficient presheaf `Γ(-, 𝒪) ⊗_R M` of a bare module, at a
standard `τ`-covering of the terminal object of `Over X`**, uniformly in the five topologies.

This is the module-universe enlargement of
`AlgebraicGeometry.isZero_cechCohomology_succ_quasiCoherentPresheaf`, whose coefficients are
those of a `AlgebraicGeometry.Scheme.Modules` and hence at the universe `u` of the schemes.  The
reduction to the one-member covering by the disjoint union is
`AlgebraicGeometry.isIso_cechComplexMap_coproductRefinement_overTensorPresheaf`, and the two
hypotheses it leaves — that the disjoint union has affine total space, and that its coordinate
ring is faithfully flat over `R` — are
`AlgebraicGeometry.IsStandardCovering.isAffine_left_sigmaObj` and
`AlgebraicGeometry.IsStandardCovering.faithfullyFlat_left_sigmaDesc`. -/
public theorem isZero_cechCohomology_succ_overTensorPresheaf (hg : g = 𝟙 X)
    (τ : CoveringTopology) (E : PreZeroHypercover.{max u m} (Over.mk g))
    (h : IsStandardCovering τ (fun i ↦ (E.X i).left) (fun i ↦ (E.f i).left))
    (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomology E (overTensorPresheaf X M) p) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp).symm⟩
  have hfin : Finite E.I₀ := h.finite_index
  have haff : IsAffine (∐ E.X).left := h.isAffine_left_sigmaObj τ X E
  have hone : IsZero (cechCohomology (PreZeroHypercover.singleton.{max u m} (Sigma.desc E.f))
      (overTensorPresheaf X M) (q + 1)) :=
    isZero_cechCohomology_singleton_succ_overTensorPresheaf X M hg (Sigma.desc E.f)
      (h.faithfullyFlat_left_sigmaDesc τ X E) q
  have := isIso_cechComplexMap_coproductRefinement_overTensorPresheaf X M E
  exact hone.of_iso ((HomologicalComplex.homologyFunctor AddCommGrpCat.{max u m}
    (ComplexShape.up ℕ) (q + 1)).mapIso (asIso (cechComplexMap E
      (PreZeroHypercover.singleton.{max u m} (Sigma.desc E.f)) (coproductRefinement E)
      (overTensorPresheaf X M)))).symm

end AlgebraicGeometry

end
