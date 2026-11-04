module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.Algebra.Polynomial.Laurent
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.Multiplicative
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.LocalizationAwayPolynomial
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.Examples.MultiplicativeSmoothDimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The multiplicative group over an object of the big fppf site

For an object `c` of the big fppf site over `S`, with underlying scheme `X`, the multiplicative
group `𝐆_m × c = 𝐆_{m, X}` is again an object of the site, and its projection to `c` is a smooth,
surjective, affine morphism of the site. It carries the universal invertible function: for every
morphism `k : V ⟶ c` of the site and every unit `a` in the global sections of `V` there is a
unique lift `V ⟶ 𝐆_m × c` of `k` pulling the coordinate back to `a`.

## Main definitions

* `AlgebraicGeometry.Space.multiplicativeGroupChart`: the multiplicative group over an object
  `c` of the site, as an object of the site.
* `AlgebraicGeometry.Space.multiplicativeGroupChartHom`: its projection to `c`.
* `AlgebraicGeometry.Space.multiplicativeGroupChartCoordinate`: the Laurent coordinate, an
  invertible global function on it.

## Main results

* `AlgebraicGeometry.surjective_multiplicativeGroupULift` (smoothness is the base
  `AlgebraicGeometry.smooth_multiplicativeGroupULift`): `Spec ℤ[T, T⁻¹] ⟶ Spec ℤ` is smooth
  and surjective; the instances for `AlgebraicGeometry.multiplicativeGroupBaseChange X ↘ X`
  follow by base change.
* `AlgebraicGeometry.Space.smooth_multiplicativeGroupChartHom`,
  `AlgebraicGeometry.Space.surjective_multiplicativeGroupChartHom` and
  `AlgebraicGeometry.Space.isAffineHom_multiplicativeGroupChartHom`: the projection is smooth,
  surjective and affine; being smooth, it is locally of finite presentation by Mathlib's
  instance.
* `AlgebraicGeometry.Space.existsUnique_multiplicativeGroupChart_lift`: the universal property
  of the coordinate.

## Implementation notes

`ℤ[T, T⁻¹]` is the localization of `ℤ[T]` away from `T` (`LaurentPolynomial.isLocalization`),
so it is a smooth `ℤ`-algebra; surjectivity on spectra holds because evaluation at `T = 1` is a
retraction of the constant inclusion, so the structure morphism has a section. The size bound of
the site carries over from `c` because the projection is affine, hence quasi-compact, and
locally of finite type (Stacks 000R (5)). The universal property is read off from
`AlgebraicGeometry.multiplicativeGroupBaseChangeRepresentsGlobalUnits` applied to `X`, whose
components are pullback of the coordinate by
`AlgebraicGeometry.baseChangePointsIsoGlobalUnits_hom_app`.

## References

* [Stacks Project, Tag 022U](https://stacks.math.columbia.edu/tag/022U)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The integral multiplicative group is surjective onto `Spec ℤ`.** Evaluation at `T = 1` is
a retraction of the inclusion of constants, so the structure morphism has a section. -/
theorem surjective_multiplicativeGroupULift :
    Surjective (multiplicativeGroupULift.{u} ↘ Spec (.of (ULift.{u} ℤ))) := by
  let e : LaurentPolynomial (ULift.{u} ℤ) →+* ULift.{u} ℤ :=
    LaurentPolynomial.eval₂ (RingHom.id _) 1
  have he : (CommRingCat.ofHom (LaurentPolynomial.C (R := ULift.{u} ℤ)) ≫
      CommRingCat.ofHom e) = 𝟙 _ := by
    ext r
    simp [e, LaurentPolynomial.eval₂_C]
  have : Surjective (Spec.map (CommRingCat.ofHom e) ≫
      (multiplicativeGroupULift.{u} ↘ Spec (.of (ULift.{u} ℤ)))) := by
    show Surjective (Spec.map (CommRingCat.ofHom e) ≫
      Spec.map (CommRingCat.ofHom LaurentPolynomial.C))
    rw [← Spec.map_comp, he, Spec.map_id]
    infer_instance
  exact Surjective.of_comp (Spec.map (CommRingCat.ofHom e)) _

/-- The multiplicative group over a scheme is smooth over it. -/
instance (X : Scheme.{u}) : Smooth (multiplicativeGroupBaseChange X ↘ X) :=
  smooth_multiplicativeGroupBaseChange X

/-- The multiplicative group over a scheme is surjective onto it, by base change from
`Spec ℤ`. -/
instance surjective_multiplicativeGroupBaseChange (X : Scheme.{u}) :
    Surjective (multiplicativeGroupBaseChange X ↘ X) :=
  have := surjective_multiplicativeGroupULift.{u}
  inferInstanceAs (Surjective (pullback.snd _ _))

/-- The multiplicative group over a scheme is affine over it, by base change from the morphism
of affine schemes `Spec ℤ[T, T⁻¹] ⟶ Spec ℤ`. -/
@[sga "3 IX 2.1" "a, special case"]
instance isAffineHom_multiplicativeGroupBaseChange (X : Scheme.{u}) :
    IsAffineHom (multiplicativeGroupBaseChange X ↘ X) :=
  have : IsAffineHom (multiplicativeGroupULift.{u} ↘ Spec (.of (ULift.{u} ℤ))) :=
    inferInstanceAs (IsAffineHom (Spec.map (CommRingCat.ofHom LaurentPolynomial.C)))
  isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The multiplicative group `𝐆_m × c` over an object `c` of the site**, as an object of the
site. Its underlying scheme is the multiplicative group over the scheme of `c`, which satisfies
the size bound because its projection is affine and locally of finite type (Stacks 000R (5)); its
structure morphism to `S` is the projection followed by that of `c`. -/
def multiplicativeGroupChart (c : BigFppfOver B S hS) : BigFppfOver B S hS :=
  Over.mk (⟨multiplicativeGroupBaseChange ((BigFppfOver.toScheme B S hS).obj c) ↘
      (BigFppfOver.toScheme B S hS).obj c ≫ B.inclusion.map c.hom⟩ :
    B.obj (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
      (multiplicativeGroupBaseChange ((BigFppfOver.toScheme B S hS).obj c) ↘
        (BigFppfOver.toScheme B S hS).obj c) c.left.property) ⟶ B.obj hS)

/-- The projection `𝐆_m × c ⟶ c`, as a morphism of the site. -/
def multiplicativeGroupChartHom (c : BigFppfOver B S hS) : multiplicativeGroupChart c ⟶ c :=
  Over.homMk ⟨multiplicativeGroupBaseChange ((BigFppfOver.toScheme B S hS).obj c) ↘
    (BigFppfOver.toScheme B S hS).obj c⟩ (by rfl)

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.multiplicativeGroupChartHom` is
the structure morphism of the multiplicative group over the scheme of `c`. -/
theorem toScheme_map_multiplicativeGroupChartHom (c : BigFppfOver B S hS) :
    (BigFppfOver.toScheme B S hS).map (multiplicativeGroupChartHom c) =
      multiplicativeGroupBaseChange ((BigFppfOver.toScheme B S hS).obj c) ↘
        (BigFppfOver.toScheme B S hS).obj c :=
  rfl

/-- **The coordinate of `𝐆_m × c`**: the pullback of the Laurent variable `T` along the
projection to the integral multiplicative group, an invertible global function. -/
def multiplicativeGroupChartCoordinate (c : BigFppfOver B S hS) :
    (Γ((BigFppfOver.toScheme B S hS).obj (multiplicativeGroupChart c), ⊤))ˣ :=
  multiplicativeGroupPointUnit (pullback.fst (multiplicativeGroupULift ↘ Spec (.of (ULift.{u} ℤ)))
    (specULiftZIsTerminal.from ((BigFppfOver.toScheme B S hS).obj c)))

/-- The projection `𝐆_m × c ⟶ c` is smooth. -/
instance smooth_multiplicativeGroupChartHom (c : BigFppfOver B S hS) :
    Smooth ((BigFppfOver.toScheme B S hS).map (multiplicativeGroupChartHom c)) :=
  smooth_multiplicativeGroupBaseChange _

/-- The projection `𝐆_m × c ⟶ c` is surjective. -/
instance surjective_multiplicativeGroupChartHom (c : BigFppfOver B S hS) :
    Surjective ((BigFppfOver.toScheme B S hS).map (multiplicativeGroupChartHom c)) :=
  surjective_multiplicativeGroupBaseChange _

/-- The projection `𝐆_m × c ⟶ c` is affine. -/
instance isAffineHom_multiplicativeGroupChartHom (c : BigFppfOver B S hS) :
    _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map (multiplicativeGroupChartHom c)) :=
  isAffineHom_multiplicativeGroupBaseChange _

/-- **The universal property of `𝐆_m × c`.** For every morphism `k : V ⟶ c` of the site and every
unit `a` in the global sections of `V`, there is a unique morphism `g : V ⟶ 𝐆_m × c` over `c`
pulling the coordinate back to `a`. -/
theorem existsUnique_multiplicativeGroupChart_lift (c : BigFppfOver B S hS)
    {V : BigFppfOver B S hS} (k : V ⟶ c) (a : (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))ˣ) :
    ∃! g : V ⟶ multiplicativeGroupChart c, g ≫ multiplicativeGroupChartHom c = k ∧
      ((BigFppfOver.toScheme B S hS).map g).appTop (multiplicativeGroupChartCoordinate c).val =
        a.val := by
  let X := (BigFppfOver.toScheme B S hS).obj c
  let R := multiplicativeGroupBaseChangeRepresentsGlobalUnits X
  let T : Over X := Over.mk ((BigFppfOver.toScheme B S hS).map k)
  let a' : (globalUnits X ⋙ forget GrpCat).obj (Opposite.op T) := a
  have hR : ∀ f : T ⟶ Scheme.asOver (multiplicativeGroupBaseChange X) X,
      (R.homEquiv f).val = f.left.appTop (multiplicativeGroupChartCoordinate c).val := by
    intro f
    have := baseChangePointsIsoGlobalUnits_hom_app X (Opposite.op T) f
    change R.homEquiv f = _ at this
    rw [this]
    simp [multiplicativeGroupPointUnit, multiplicativeGroupChartCoordinate]
    rfl
  have hext : ∀ {W : BigFppfOver B S hS} {g g' : V ⟶ W},
      (BigFppfOver.toScheme B S hS).map g = (BigFppfOver.toScheme B S hS).map g' → g = g' :=
    fun h => Over.OverMorphism.ext (ObjectProperty.hom_ext _ h)
  let toG : (T ⟶ Scheme.asOver (multiplicativeGroupBaseChange X) X) →
      (V ⟶ multiplicativeGroupChart c) := fun f =>
    Over.homMk ⟨f.left⟩ (by
      apply ObjectProperty.hom_ext
      show f.left ≫ (multiplicativeGroupBaseChange X ↘ X) ≫ B.inclusion.map c.hom =
        B.inclusion.map V.hom
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ B.inclusion.map c.hom) (Over.w f)).trans
          ((B.inclusion.map_comp k.left c.hom).symm.trans (congrArg B.inclusion.map (Over.w k)))))
  have htoG : ∀ f, toG f ≫ multiplicativeGroupChartHom c = k := fun f => hext (Over.w f)
  have htoGmap : ∀ f, (BigFppfOver.toScheme B S hS).map (toG f) = f.left := fun f => rfl
  refine ⟨toG (R.homEquiv.symm a'),
    ⟨htoG _, (hR _).symm.trans (congrArg Units.val (R.homEquiv.apply_symm_apply a'))⟩, ?_⟩
  rintro g ⟨hg, hga⟩
  let f : T ⟶ Scheme.asOver (multiplicativeGroupBaseChange X) X :=
    Over.homMk ((BigFppfOver.toScheme B S hS).map g) (by
      show (BigFppfOver.toScheme B S hS).map g ≫
        (BigFppfOver.toScheme B S hS).map (multiplicativeGroupChartHom c) = _
      rw [← Functor.map_comp, hg]
      rfl)
  have hf : R.homEquiv f = a' := Units.ext ((hR f).trans hga)
  have : f = R.homEquiv.symm a' := by rw [← hf, Equiv.symm_apply_apply]
  apply hext
  rw [htoGmap, ← this]
  rfl

end AlgebraicGeometry.Space
