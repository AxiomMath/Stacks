module

public import StacksFrontier.AlgebraicGeometry.Spaces.CokernelAffineSurjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentImpliesCartesian

/-!
# Cokernels and short exact sequences of quasi-coherent modules on an algebraic space

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`. This file
proves, for `𝒪_F`-modules at module universe `u`, the cokernel half of clause (3) and clause (4)
of [Stacks, Tag 03M1], from two hypotheses in which no particular module or morphism occurs:

* `hEss`, essential surjectivity of the functor `M ↦ Mᵃ` of [Stacks, Tag 03DU] onto the
  quasi-coherent modules on the slice of the small étale site of `F` at an affine chart;
* `h03DW`, surjectivity on the sections over an affine chart of every epimorphism of
  `𝒪_F`-modules whose kernel is cartesian on affine charts.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_of_essSurj_of_h03DW`: the cokernel of
  a morphism of quasi-coherent `𝒪_F`-modules is quasi-coherent, given `hEss` and `h03DW`.
* `AlgebraicGeometry.Space.isQuasicoherent_left_of_shortExact_of_essSurj`: in a short exact
  sequence whose middle and right terms are quasi-coherent, the left term is quasi-coherent,
  given `hEss`.
* `AlgebraicGeometry.Space.isQuasicoherent_middle_of_shortExact_of_essSurj_of_h03DW` and
  `AlgebraicGeometry.Space.isQuasicoherent_right_of_shortExact_of_essSurj_of_h03DW`: in a short
  exact sequence in which two of the terms are quasi-coherent, the middle, respectively right,
  term is quasi-coherent, given `hEss` and `h03DW`.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.SmallEtale

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-! ### The cokernel half of clause (3) -/

/-- Assume `hEss`, essential surjectivity of `M ↦ Mᵃ` onto the quasi-coherent modules on the
slice at every affine chart, and `h03DW`, surjectivity on sections over affine charts of every
epimorphism with kernel cartesian on affine charts. Then the cokernel of a morphism of
quasi-coherent `𝒪_F`-modules on an algebraic space is quasi-coherent. -/
theorem isQuasicoherentOnSite_cokernel_of_essSurj_of_h03DW
    {M N : Modules.{u, u} B S hS F hF}
    [M.IsQuasicoherentOnSite] [N.IsQuasicoherentOnSite] (f : M ⟶ N)
    (hEss : ∀ Y : SmallEtale B S hS F, IsAffine (chartScheme Y) →
      ∀ P : SheafOfModules.{u} (sliceRingSheaf B S hS F hF Y), P.IsQuasicoherentOnSite →
        ∃ (M₀ : (chartScheme Y).Modules) (_ : M₀.IsQuasicoherent)
          (hM₀ : Presheaf.IsSheaf ((topology B S hS F).over Y)
            (Stacks.Sites.associatedPresheaf (chartScheme Y) M₀
              (sliceToOver B S hS F Y))),
          Nonempty (P ≅ sliceAssociatedModule B S hS F hF Y M₀ hM₀))
    (h03DW : ∀ {P Q : Modules.{u, u} B S hS F hF} (q : P ⟶ Q), Epi q →
      IsCartesianOnAffineCharts (kernel q) → ∀ W : SmallEtale B S hS F,
        IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
          Function.Surjective (q.val.app (op W))) :
    (cokernel f).IsQuasicoherentOnSite :=
  have h03DX := isCartesianOnAffineCharts_of_isQuasicoherentOnSite_of_essSurj B S hS F hF hEss
  isQuasicoherentOnSite_cokernel_of_h03DW f h03DW
    (h03DX M ‹M.IsQuasicoherentOnSite›) (h03DX N ‹N.IsQuasicoherentOnSite›)

/-! ### Clause (4), the two-out-of-three property -/

/-- Assume `hEss`, essential surjectivity of `M ↦ Mᵃ` onto the quasi-coherent modules on the
slice at every affine chart. Then the left term of a short exact sequence of `𝒪_F`-modules on an
algebraic space is quasi-coherent if the other two terms are. -/
theorem isQuasicoherent_left_of_shortExact_of_essSurj
    (T : ShortComplex (Modules.{u, u} B S hS F hF)) (hT : T.ShortExact)
    (hEss : ∀ Y : SmallEtale B S hS F, IsAffine (chartScheme Y) →
      ∀ P : SheafOfModules.{u} (sliceRingSheaf B S hS F hF Y), P.IsQuasicoherentOnSite →
        ∃ (M₀ : (chartScheme Y).Modules) (_ : M₀.IsQuasicoherent)
          (hM₀ : Presheaf.IsSheaf ((topology B S hS F).over Y)
            (Stacks.Sites.associatedPresheaf (chartScheme Y) M₀
              (sliceToOver B S hS F Y))),
          Nonempty (P ≅ sliceAssociatedModule B S hS F hF Y M₀ hM₀))
    [T.X₂.IsQuasicoherentOnSite] [T.X₃.IsQuasicoherentOnSite] :
    T.X₁.IsQuasicoherentOnSite :=
  isQuasicoherent_left_of_shortExact T hT
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite_of_essSurj B S hS F hF hEss)

/-- Assume `hEss`, essential surjectivity of `M ↦ Mᵃ` onto the quasi-coherent modules on the
slice at every affine chart, and `h03DW`, surjectivity on sections over affine charts of every
epimorphism with kernel cartesian on affine charts. Then an extension of quasi-coherent
`𝒪_F`-modules on an algebraic space is quasi-coherent. -/
theorem isQuasicoherent_middle_of_shortExact_of_essSurj_of_h03DW
    (T : ShortComplex (Modules.{u, u} B S hS F hF)) (hT : T.ShortExact)
    (hEss : ∀ Y : SmallEtale B S hS F, IsAffine (chartScheme Y) →
      ∀ P : SheafOfModules.{u} (sliceRingSheaf B S hS F hF Y), P.IsQuasicoherentOnSite →
        ∃ (M₀ : (chartScheme Y).Modules) (_ : M₀.IsQuasicoherent)
          (hM₀ : Presheaf.IsSheaf ((topology B S hS F).over Y)
            (Stacks.Sites.associatedPresheaf (chartScheme Y) M₀
              (sliceToOver B S hS F Y))),
          Nonempty (P ≅ sliceAssociatedModule B S hS F hF Y M₀ hM₀))
    (h03DW : ∀ {P Q : Modules.{u, u} B S hS F hF} (q : P ⟶ Q), Epi q →
      IsCartesianOnAffineCharts (kernel q) → ∀ W : SmallEtale B S hS F,
        IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
          Function.Surjective (q.val.app (op W)))
    [T.X₁.IsQuasicoherentOnSite] [T.X₃.IsQuasicoherentOnSite] :
    T.X₂.IsQuasicoherentOnSite :=
  have h03DX := isCartesianOnAffineCharts_of_isQuasicoherentOnSite_of_essSurj B S hS F hF hEss
  isQuasicoherent_middle_of_shortExact T hT h03DX
    (fun U hU => surjective_g_val_app_of_shortExact_of_h03DW T hT h03DW
      (h03DX T.X₁ ‹T.X₁.IsQuasicoherentOnSite›) U hU)

/-- Assume `hEss`, essential surjectivity of `M ↦ Mᵃ` onto the quasi-coherent modules on the
slice at every affine chart, and `h03DW`, surjectivity on sections over affine charts of every
epimorphism with kernel cartesian on affine charts. Then the right term of a short exact sequence
of `𝒪_F`-modules on an algebraic space is quasi-coherent if the other two terms are. -/
theorem isQuasicoherent_right_of_shortExact_of_essSurj_of_h03DW
    (T : ShortComplex (Modules.{u, u} B S hS F hF)) (hT : T.ShortExact)
    (hEss : ∀ Y : SmallEtale B S hS F, IsAffine (chartScheme Y) →
      ∀ P : SheafOfModules.{u} (sliceRingSheaf B S hS F hF Y), P.IsQuasicoherentOnSite →
        ∃ (M₀ : (chartScheme Y).Modules) (_ : M₀.IsQuasicoherent)
          (hM₀ : Presheaf.IsSheaf ((topology B S hS F).over Y)
            (Stacks.Sites.associatedPresheaf (chartScheme Y) M₀
              (sliceToOver B S hS F Y))),
          Nonempty (P ≅ sliceAssociatedModule B S hS F hF Y M₀ hM₀))
    (h03DW : ∀ {P Q : Modules.{u, u} B S hS F hF} (q : P ⟶ Q), Epi q →
      IsCartesianOnAffineCharts (kernel q) → ∀ W : SmallEtale B S hS F,
        IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
          Function.Surjective (q.val.app (op W)))
    [T.X₁.IsQuasicoherentOnSite] [T.X₂.IsQuasicoherentOnSite] :
    T.X₃.IsQuasicoherentOnSite :=
  have h03DX := isCartesianOnAffineCharts_of_isQuasicoherentOnSite_of_essSurj B S hS F hF hEss
  isQuasicoherent_right_of_shortExact T hT h03DX
    (fun U hU => surjective_g_val_app_of_shortExact_of_h03DW T hT h03DW
      (h03DX T.X₁ ‹T.X₁.IsQuasicoherentOnSite›) U hU)

end AlgebraicGeometry.Space

end
