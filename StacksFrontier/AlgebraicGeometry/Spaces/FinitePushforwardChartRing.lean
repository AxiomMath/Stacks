module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineCokernelDescent

/-!
# The rings of the base-changed charts of a representable morphism

Let `f : X ⟶ Y` be a representable morphism of algebraic spaces over a scheme `S` contained in
a big fppf site `B`, and let `V` be an étale scheme chart of `Y`.  Small-chart base change of
Stacks 03G2, part (4), produces the étale scheme chart `V ×_Y X` of `X`, and the structure map
`f♯` of `AlgebraicGeometry.Space.smallBaseChangeSharp` makes the ring of regular functions on
`V ×_Y X` an algebra over the ring of regular functions on `V`.  This file proves that this
algebra is finite when `f` is finite and the chart is affine, and that the rings of a morphism of
affine charts form a pushout.

## Main definitions

* `AlgebraicGeometry.Space.baseChangeChartAlgebra`: the algebra structure on the ring of a
  base-changed chart given by pullback of regular functions along the cartesian projection.

## Main results

* `AlgebraicGeometry.Space.isPullback_toScheme_smallBaseChange_snd`: for a morphism
  `k : Z ⟶ A` of étale charts of `Y` the square of schemes with corners `Z ×_Y X`, `A ×_Y X`,
  `Z` and `A` is cartesian.
* `AlgebraicGeometry.Space.isFinite_toScheme_smallBaseChange_snd`: the cartesian projection
  `A ×_Y X ⟶ A` is a finite morphism of schemes when `f` is finite.
* `AlgebraicGeometry.Space.moduleFinite_chartRing_smallBaseChange`: hence for an affine chart
  the regular functions on `A ×_Y X` are a finite module over the regular functions on `A`.
* `AlgebraicGeometry.Space.algebra_isPushout_appTop_smallBaseChange`: for a morphism of
  *affine* étale charts of `Y` the four rings of the base-change square form a pushout, that
  is, `𝒪_X(Z ×_Y X) = 𝒪_X(A ×_Y X) ⊗_{𝒪_Y(A)} 𝒪_Y(Z)`.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-! ### The base-change square of schemes -/

/-- **The base changes of a representable morphism to two étale charts are cartesian over the
charts.**  For a morphism `k : Z ⟶ A` of étale charts of `Y` the square of schemes with corners
`Z ×_Y X`, `A ×_Y X`, `Z` and `A` is cartesian. -/
theorem isPullback_toScheme_smallBaseChange_snd (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) {A Z : SmallEtale B S hS Y.1} (k : Z ⟶ A) :
    IsPullback
      ((BigFppfOver.toScheme B S hS).map ((smallBaseChange B S hS f hf).map k).hom.left)
      ((BigFppfOver.toScheme B S hS).map (hf.snd Z.1.hom))
      ((BigFppfOver.toScheme B S hS).map (hf.snd A.1.hom))
      ((BigFppfOver.toScheme B S hS).map k.hom.left) := by
  have hfst : yoneda.map ((smallBaseChange B S hS f hf).map k).hom.left ≫ hf.fst A.1.hom =
      hf.fst Z.1.hom := hf.lift_fst _ _ _
  have hs : IsPullback
      (yoneda.map ((smallBaseChange B S hS f hf).map k).hom.left ≫ hf.fst A.1.hom)
      (yoneda.map (hf.snd Z.1.hom)) f.hom (yoneda.map k.hom.left ≫ A.1.hom) := by
    rw [hfst, CostructuredArrow.w k.hom]
    exact hf.isPullback Z.1.hom
  have hp : yoneda.map ((smallBaseChange B S hS f hf).map k).hom.left ≫
      yoneda.map (hf.snd A.1.hom) =
      yoneda.map (hf.snd Z.1.hom) ≫ yoneda.map k.hom.left :=
    (yoneda.map_comp _ _).symm.trans
      ((congrArg (fun q ↦ yoneda.map q) (smallBaseChange_map_snd B S hS f hf k)).trans
        (yoneda.map_comp _ _))
  have hpre : IsPullback (yoneda.map ((smallBaseChange B S hS f hf).map k).hom.left)
      (yoneda.map (hf.snd Z.1.hom))
      (yoneda.map (hf.snd A.1.hom)) (yoneda.map k.hom.left) :=
    IsPullback.of_right hs hp (hf.isPullback A.1.hom)
  exact (IsPullback.of_map_of_faithful yoneda hpre).map (BigFppfOver.toScheme B S hS)

/-! ### Finiteness of the base-changed chart -/

/-- **The cartesian projection of a base-changed chart is a finite morphism of schemes** when
the morphism of algebraic spaces being base changed is finite. -/
theorem isFinite_toScheme_smallBaseChange_snd (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (hfin : IsFinite B S hS f.hom)
    (A : SmallEtale B S hS Y.1) :
    _root_.AlgebraicGeometry.IsFinite
      ((BigFppfOver.toScheme B S hS).map (hf.snd A.1.hom)) :=
  ((isFinite_iff_representable B S hS f.hom X.2 Y.2).1 hfin).2.2 A.1.hom
    (hf.fst A.1.hom) (hf.snd A.1.hom) (hf.isPullback A.1.hom)

/-! ### The algebra of a base-changed chart -/

/-- The algebra structure that the structure map of small-chart base change puts on the ring of
regular functions of a base-changed chart: pullback of regular functions along the cartesian
projection `A ×_Y X ⟶ A`. -/
@[instance_reducible]
noncomputable def baseChangeChartAlgebra (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (A : SmallEtale B S hS Y.1) :
    Algebra (chartRing B S hS Y.1 Y.2 A)
      (chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hf).obj A)) :=
  (((BigFppfOver.toScheme B S hS).map (hf.snd A.1.hom)).appTop).hom.toAlgebra

/-- The structure map of `baseChangeChartAlgebra` is pullback of regular functions along the
cartesian projection `A ×_Y X ⟶ A`. -/
theorem baseChangeChartAlgebra_algebraMap (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (A : SmallEtale B S hS Y.1) :
    letI := baseChangeChartAlgebra B S hS f hf A
    algebraMap (chartRing B S hS Y.1 Y.2 A)
        (chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hf).obj A)) =
      (((BigFppfOver.toScheme B S hS).map (hf.snd A.1.hom)).appTop).hom := rfl

/-- **The regular functions on the base change of an affine chart along a finite morphism form
a finite module over the regular functions on the chart.** -/
theorem moduleFinite_chartRing_smallBaseChange (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (hfin : IsFinite B S hS f.hom)
    (A : SmallEtale B S hS Y.1) (hA : IsAffine (chartScheme A)) :
    letI := baseChangeChartAlgebra B S hS f hf A
    Module.Finite (chartRing B S hS Y.1 Y.2 A)
      (chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hf).obj A)) := by
  let := baseChangeChartAlgebra B S hS f hf A
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj A.1.left) := hA
  have _ : _root_.AlgebraicGeometry.IsFinite
      ((BigFppfOver.toScheme B S hS).map (hf.snd A.1.hom)) :=
    isFinite_toScheme_smallBaseChange_snd B S hS f hf hfin A
  exact Scheme.Hom.finite_appTop ((BigFppfOver.toScheme B S hS).map (hf.snd A.1.hom))

/-! ### The base-change square of rings -/

/-- The square of rings of a base-changed chart commutes: pulling a function on `A` back to
`A ×_Y X` and restricting it to `Z ×_Y X` is restricting it to `Z` and pulling it back. -/
theorem appTop_smallBaseChange_square (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) {A Z : SmallEtale B S hS Y.1} (k : Z ⟶ A) :
    (((BigFppfOver.toScheme B S hS).map
          ((smallBaseChange B S hS f hf).map k).hom.left).appTop).hom.comp
        (((BigFppfOver.toScheme B S hS).map (hf.snd A.1.hom)).appTop).hom =
      (((BigFppfOver.toScheme B S hS).map (hf.snd Z.1.hom)).appTop).hom.comp
        (((BigFppfOver.toScheme B S hS).map k.hom.left).appTop).hom :=
  congrArg
    (fun g : (BigFppfOver.toScheme B S hS).obj ((smallBaseChange B S hS f hf).obj Z).1.left ⟶
        (BigFppfOver.toScheme B S hS).obj A.1.left ↦ (Scheme.Hom.appTop g).hom)
    (isPullback_toScheme_smallBaseChange_snd B S hS f hf k).w

/-- **The four rings of the base-change square of a morphism of affine charts form a pushout**:
`𝒪_X(Z ×_Y X) = 𝒪_X(A ×_Y X) ⊗_{𝒪_Y(A)} 𝒪_Y(Z)`, for algebra structures whose `algebraMap`s
are the maps of global functions of the square. -/
theorem algebra_isPushout_appTop_smallBaseChange (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (haff : IsAffineHom B S hS f.hom)
    {A Z : SmallEtale B S hS Y.1} (k : Z ⟶ A)
    (hA : IsAffine ((BigFppfOver.toScheme B S hS).obj A.1.left))
    (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj Z.1.left))
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj A.1.left, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((smallBaseChange B S hS f hf).obj A).1.left, ⊤)]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj A.1.left, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj Z.1.left, ⊤)]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj ((smallBaseChange B S hS f hf).obj A).1.left, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((smallBaseChange B S hS f hf).obj Z).1.left, ⊤)]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj Z.1.left, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((smallBaseChange B S hS f hf).obj Z).1.left, ⊤)]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj A.1.left, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((smallBaseChange B S hS f hf).obj Z).1.left, ⊤)]
    [IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj A.1.left, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((smallBaseChange B S hS f hf).obj A).1.left, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((smallBaseChange B S hS f hf).obj Z).1.left, ⊤)]
    [IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj A.1.left, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj Z.1.left, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((smallBaseChange B S hS f hf).obj Z).1.left, ⊤)]
    (hfA : algebraMap Γ((BigFppfOver.toScheme B S hS).obj A.1.left, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj ((smallBaseChange B S hS f hf).obj A).1.left, ⊤) =
      (((BigFppfOver.toScheme B S hS).map (hf.snd A.1.hom)).appTop).hom)
    (hk : algebraMap Γ((BigFppfOver.toScheme B S hS).obj A.1.left, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj Z.1.left, ⊤) =
      (((BigFppfOver.toScheme B S hS).map k.hom.left).appTop).hom)
    (hbc : algebraMap
        Γ((BigFppfOver.toScheme B S hS).obj ((smallBaseChange B S hS f hf).obj A).1.left, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj ((smallBaseChange B S hS f hf).obj Z).1.left, ⊤) =
      (((BigFppfOver.toScheme B S hS).map
        ((smallBaseChange B S hS f hf).map k).hom.left).appTop).hom)
    (hfZ : algebraMap Γ((BigFppfOver.toScheme B S hS).obj Z.1.left, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj ((smallBaseChange B S hS f hf).obj Z).1.left, ⊤) =
      (((BigFppfOver.toScheme B S hS).map (hf.snd Z.1.hom)).appTop).hom) :
    Algebra.IsPushout Γ((BigFppfOver.toScheme B S hS).obj A.1.left, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((smallBaseChange B S hS f hf).obj A).1.left, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj Z.1.left, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((smallBaseChange B S hS f hf).obj Z).1.left, ⊤) :=
  have _ := hA
  have _ := hZ
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((smallBaseChange B S hS f hf).obj A).1.left) :=
    isAffine_smallBaseChange_obj B S hS f hf haff A hA
  algebra_isPushout_appTop_of_isPullback
    (isPullback_toScheme_smallBaseChange_snd B S hS f hf k) hfA hk hbc hfZ

end AlgebraicGeometry.Space

end
