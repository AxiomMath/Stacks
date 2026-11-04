module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.CokernelAffineSurjectivityFromCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts

/-!
# The sections of a cokernel over an affine chart

Let `F` be an algebraic space and `φ : M ⟶ N` a morphism of `𝒪_F`-modules.  Over an *affine*
étale chart `V` the sections of the cokernel of `φ` are the ordinary cokernel of the map on
sections: the projection `N ⟶ coker φ` is surjective on the sections over `V`, and its kernel
there is the image of `M(V) → N(V)`.  Equivalently, taking sections over an affine étale chart
carries `M ⟶ N ⟶ coker φ` to an exact pair of modules over the chart ring.

Neither half is formal.  For a general object of the small étale site the discrepancy between the
sections of the cokernel and the cokernel of the sections is a first cohomology group; what makes
it vanish over an affine chart is Descent, Proposition 03DW in degree zero, available here
through `AlgebraicGeometry.Space.surjective_val_app_cokernel_π_of_cartesian` and
`AlgebraicGeometry.Space.surjective_val_app_factorThruImage_of_cartesian`, which consume that the
two ends of `φ` be cartesian on affine charts.

This is the general form of the adic statement
`AlgebraicGeometry.Space.surjective_val_app_idealPowerQuotient_π`, where `φ` is the inclusion of
`𝓘 ^ k M` into `M`, and it is the sections-level content of the cokernel clause of Stacks 03M1
for coherent modules.

## Main results

* `AlgebraicGeometry.Space.exact_val_app_cokernel_π_of_cartesian` — **sections over an affine
  chart carry `M ⟶ N ⟶ coker φ` to an exact pair**, for `M` and `N` cartesian on affine charts.
* `AlgebraicGeometry.Space.ker_val_app_cokernel_π_of_cartesian` — **the kernel of the projection
  onto `coker φ` on the sections over an affine chart is the range of the sections of `φ`**, for
  `M` and `N` cartesian on affine charts.
* `AlgebraicGeometry.Space.surjective_val_app_cokernel_π` — **the projection onto `coker φ` is
  surjective on the sections over an affine chart**, for `M` and `N` coherent.
* `AlgebraicGeometry.Space.ker_val_app_cokernel_π` — **its kernel there is the range of the
  sections of `φ`**, for `M` and `N` coherent.

## Implementation notes

The hypotheses actually consumed are that `M` and `N` be cartesian on affine charts, and the two
`_of_cartesian` statements are the primitive ones.  The coherent forms are obtained from them by
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`, Descent,
Proposition 03DX (2), applied to the quasi-coherence that
`AlgebraicGeometry.Space.IsCoherent` carries; no local Noetherianity is used, and in particular
no `Fact` instance carrying an étale-local property is needed.

Surjectivity of the projection for cartesian modules is already
`AlgebraicGeometry.Space.surjective_val_app_cokernel_π_of_cartesian`, so it is not restated
here; only its coherent specialization is.

The kernel clause is read off from exactness rather than from an identification of
`CategoryTheory.Limits.kernel (CategoryTheory.Limits.cokernel.π φ)` with
`CategoryTheory.Abelian.image φ`: that identification is what
`SheafOfModules.exact_val_app_cokernel_π` already performs internally, and going through it a
second time at the level of subobjects would require transporting cartesianness along
`CategoryTheory.Abelian.imageIsImage` for no gain.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **Sections over an affine étale chart carry a morphism of `𝒪_F`-modules cartesian on affine
charts and the projection onto its cokernel to an exact pair.**

This is `SheafOfModules.exact_val_app_cokernel_π` with its sections-level hypothesis discharged
by `AlgebraicGeometry.Space.surjective_val_app_factorThruImage_of_cartesian`, the degree-zero
form of Descent, Proposition 03DW. -/
theorem exact_val_app_cokernel_π_of_cartesian {M N : Modules.{u, u} B S hS F hF} (φ : M ⟶ N)
    (hM : IsCartesianOnAffineCharts M) (hN : IsCartesianOnAffineCharts N)
    {V : SmallEtale B S hS F} (hV : IsAffine (chartScheme V)) :
    Function.Exact (φ.val.app (op V)) ((cokernel.π φ).val.app (op V)) :=
  SheafOfModules.exact_val_app_cokernel_π φ (op V)
    (surjective_val_app_factorThruImage_of_cartesian φ hM hN V hV)

/-- **The kernel of the projection onto the cokernel of a morphism of `𝒪_F`-modules cartesian on
affine charts, on the sections over an affine étale chart, is the range of the sections of the
morphism.**

This is `AlgebraicGeometry.Space.exact_val_app_cokernel_π_of_cartesian` read as an equality of
submodules of `N(V)`. -/
theorem ker_val_app_cokernel_π_of_cartesian {M N : Modules.{u, u} B S hS F hF} (φ : M ⟶ N)
    (hM : IsCartesianOnAffineCharts M) (hN : IsCartesianOnAffineCharts N)
    {V : SmallEtale B S hS F} (hV : IsAffine (chartScheme V)) :
    LinearMap.ker ((cokernel.π φ).val.app (op V)).hom =
      LinearMap.range (φ.val.app (op V)).hom := by
  exact (exact_val_app_cokernel_π_of_cartesian B S hS F hF φ hM hN hV).linearMap_ker_eq

/-- A coherent `𝒪_F`-module is cartesian on affine charts. -/
private theorem isCartesianOnAffineCharts_of_isCoherent {M : Modules.{u, u} B S hS F hF}
    (hM : IsCoherent B S hS F hF M) : IsCartesianOnAffineCharts M :=
  isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF M hM.toIsQuasicoherentOnSite

/-- **The projection onto the cokernel of a morphism of coherent `𝒪_F`-modules is surjective on
the sections over an affine étale chart.**

This is `AlgebraicGeometry.Space.surjective_val_app_cokernel_π_of_cartesian` for modules whose
cartesianness on affine charts comes from coherence, through the quasi-coherence that
`AlgebraicGeometry.Space.IsCoherent` carries and Descent, Proposition 03DX (2). -/
theorem surjective_val_app_cokernel_π {M N : Modules.{u, u} B S hS F hF} (φ : M ⟶ N)
    (hM : IsCoherent B S hS F hF M) (hN : IsCoherent B S hS F hF N)
    {V : SmallEtale B S hS F} (hV : IsAffine (chartScheme V)) :
    Function.Surjective ((cokernel.π φ).val.app (op V)) :=
  surjective_val_app_cokernel_π_of_cartesian φ
    (isCartesianOnAffineCharts_of_isCoherent B S hS F hF hM)
    (isCartesianOnAffineCharts_of_isCoherent B S hS F hF hN) V hV

/-- **The kernel of the projection onto the cokernel of a morphism of coherent `𝒪_F`-modules, on
the sections over an affine étale chart, is the range of the sections of the morphism.**

This is `AlgebraicGeometry.Space.ker_val_app_cokernel_π_of_cartesian` for modules whose
cartesianness on affine charts comes from coherence, through the quasi-coherence that
`AlgebraicGeometry.Space.IsCoherent` carries and Descent, Proposition 03DX (2). -/
theorem ker_val_app_cokernel_π {M N : Modules.{u, u} B S hS F hF} (φ : M ⟶ N)
    (hM : IsCoherent B S hS F hF M) (hN : IsCoherent B S hS F hF N)
    {V : SmallEtale B S hS F} (hV : IsAffine (chartScheme V)) :
    LinearMap.ker ((cokernel.π φ).val.app (op V)).hom =
      LinearMap.range (φ.val.app (op V)).hom :=
  ker_val_app_cokernel_π_of_cartesian B S hS F hF φ
    (isCartesianOnAffineCharts_of_isCoherent B S hS F hF hM)
    (isCartesianOnAffineCharts_of_isCoherent B S hS F hF hN) hV

end AlgebraicGeometry.Space

end
