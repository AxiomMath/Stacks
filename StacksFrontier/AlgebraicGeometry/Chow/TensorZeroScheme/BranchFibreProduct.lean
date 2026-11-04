module

public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchFactorization

/-!
# Each branch of the zero scheme of a tensor product is the other line bundle over `D`

Let `Y` be a scheme, let `L₁` and `L₂` be invertible `𝒪_Y`-modules, let `s` be a global section
of `L₁ ⊗_{𝒪_Y} L₂` and let `i : D → Y` be the zero scheme of `s`, as in [Stacks, Tag 0F97]. The
functor of points of the branch `D₁`, computed in
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchFactorization`, says that a morphism
`f : W ⟶ T` to the ambient fibre product factors through `D₁` exactly when `f` composed with the
first projection factors through the zero section of the first line bundle and `f ≫ q` factors
through `i`. That is precisely the functor of points of

  `D ×_Y Tot(L₂^{⊗ -1})`,

the second line bundle restricted to `D`: the first coordinate of a point of `D₁` vanishes, and
what remains of it is its image in `D` together with a point of the second line bundle above
that image. This file proves the resulting isomorphism over `D`, and the mirror statement for
`D₂` with the first line bundle.

## Main definitions

* `Stacks.Chow.TensorZeroScheme.branchFibreProduct₁` and `branchFibreProduct₂`: the fibre
  products `D ×_Y Tot(L₂^{⊗ -1})` and `D ×_Y Tot(L₁^{⊗ -1})`, with
  `branchFibreProductToBase₁`, `branchFibreProductToBase₂` their projections to `D` and
  `branchFibreProductToFibre₁`, `branchFibreProductToFibre₂` their projections to the line
  bundle.
* `Stacks.Chow.TensorZeroScheme.fibreProductToTotalSpace₁` and `fibreProductToTotalSpace₂`: the
  morphisms to `T` whose vanishing coordinate is the zero section.
* `Stacks.Chow.TensorZeroScheme.branchToFibreProduct₁` and `branchToFibreProduct₂`: **the
  comparison morphisms `Dᵢ ⟶ D ×_Y Tot(L_{3-i}^{⊗ -1})` over `D`.**

## Main results

* `Stacks.Chow.TensorZeroScheme.isIso_branchToFibreProduct₁` and
  `isIso_branchToFibreProduct₂`: **the comparison morphisms are isomorphisms**, so each branch is
  the other line bundle restricted to `D`.
* `Stacks.Chow.TensorZeroScheme.exists_iso_branchFibreProduct₁` and
  `exists_iso_branchFibreProduct₂`: the same, as an isomorphism over `D`.

## Implementation notes

The comparison morphism is written down: it is the morphism into the fibre product with
coordinates `pᵢ : Dᵢ ⟶ D` and the branch's own other coordinate. Its inverse is produced by the
factorization criterion, so it is obtained from an existence statement and the inverse is not
definitional; what is proved is therefore `CategoryTheory.IsIso` of the written-down morphism,
from which `CategoryTheory.asIso` produces the isomorphism.

Both composites are checked by cancelling a monomorphism, so no computation with sections or
with modules occurs here: `Dᵢ ⟶ T` is a composite of two closed immersions, `i` is a closed
immersion, and `CategoryTheory.Limits.pullback.hom_ext` reduces an identity of morphisms into a
fibre product to its two coordinates. The two coordinate lemmas for `T` and for the fibre product
are restated in terms of the named projections, since those are definitions wrapping
`CategoryTheory.Limits.pullback.fst` and `CategoryTheory.Limits.pullback.snd`.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

@[expose] public noncomputable section

namespace Stacks.Chow.TensorZeroScheme

variable (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤))

/-! ### Coordinates on the ambient fibre product -/

include h₁ h₂ in
/-- A morphism into `T` is determined by its two coordinates. -/
theorem totalSpace_hom_ext {W : Scheme.{u}} {k l : W ⟶ totalSpace Y L₁ L₂}
    (hfst : k ≫ firstProj Y L₁ L₂ = l ≫ firstProj Y L₁ L₂)
    (hsnd : k ≫ secondProj Y L₁ L₂ = l ≫ secondProj Y L₁ L₂) : k = l :=
  Limits.pullback.hom_ext hfst hsnd

/-! ### The line bundle restricted to `D` -/

include h₁ h₂ in
/-- **The fibre product `D ×_Y Tot(L₂^{⊗ -1})`**: the second line bundle restricted to the zero
scheme of `s`. -/
def branchFibreProduct₁ : Scheme.{u} :=
  Limits.pullback (zeroIdeal Y L₁ L₂ s).subschemeι (Stacks.LineBundle.lineBundleProj Y L₂)

include h₁ h₂ in
/-- **The fibre product `D ×_Y Tot(L₁^{⊗ -1})`**: the first line bundle restricted to the zero
scheme of `s`. -/
def branchFibreProduct₂ : Scheme.{u} :=
  Limits.pullback (zeroIdeal Y L₁ L₂ s).subschemeι (Stacks.LineBundle.lineBundleProj Y L₁)

include h₁ h₂ in
/-- The projection `D ×_Y Tot(L₂^{⊗ -1}) ⟶ D`. -/
def branchFibreProductToBase₁ :
    branchFibreProduct₁ Y L₁ L₂ s ⟶ (zeroIdeal Y L₁ L₂ s).subscheme :=
  Limits.pullback.fst _ _

include h₁ h₂ in
/-- The projection `D ×_Y Tot(L₁^{⊗ -1}) ⟶ D`. -/
def branchFibreProductToBase₂ :
    branchFibreProduct₂ Y L₁ L₂ s ⟶ (zeroIdeal Y L₁ L₂ s).subscheme :=
  Limits.pullback.fst _ _

include h₁ h₂ in
/-- The projection `D ×_Y Tot(L₂^{⊗ -1}) ⟶ Tot(L₂^{⊗ -1})`. -/
def branchFibreProductToFibre₁ :
    branchFibreProduct₁ Y L₁ L₂ s ⟶ Stacks.LineBundle.lineBundleSpace Y L₂ :=
  Limits.pullback.snd _ _

include h₁ h₂ in
/-- The projection `D ×_Y Tot(L₁^{⊗ -1}) ⟶ Tot(L₁^{⊗ -1})`. -/
def branchFibreProductToFibre₂ :
    branchFibreProduct₂ Y L₁ L₂ s ⟶ Stacks.LineBundle.lineBundleSpace Y L₁ :=
  Limits.pullback.snd _ _

include h₁ h₂ in
/-- The defining square of `D ×_Y Tot(L₂^{⊗ -1})`. -/
theorem branchFibreProduct₁_condition :
    branchFibreProductToBase₁ Y L₁ L₂ s ≫ (zeroIdeal Y L₁ L₂ s).subschemeι =
      branchFibreProductToFibre₁ Y L₁ L₂ s ≫ Stacks.LineBundle.lineBundleProj Y L₂ :=
  Limits.pullback.condition

include h₁ h₂ in
/-- The defining square of `D ×_Y Tot(L₁^{⊗ -1})`. -/
theorem branchFibreProduct₂_condition :
    branchFibreProductToBase₂ Y L₁ L₂ s ≫ (zeroIdeal Y L₁ L₂ s).subschemeι =
      branchFibreProductToFibre₂ Y L₁ L₂ s ≫ Stacks.LineBundle.lineBundleProj Y L₁ :=
  Limits.pullback.condition

include h₁ h₂ in
/-- A morphism into `D ×_Y Tot(L₂^{⊗ -1})` is determined by its two coordinates. -/
theorem branchFibreProduct₁_hom_ext {W : Scheme.{u}}
    {k l : W ⟶ branchFibreProduct₁ Y L₁ L₂ s}
    (hbase : k ≫ branchFibreProductToBase₁ Y L₁ L₂ s =
      l ≫ branchFibreProductToBase₁ Y L₁ L₂ s)
    (hfibre : k ≫ branchFibreProductToFibre₁ Y L₁ L₂ s =
      l ≫ branchFibreProductToFibre₁ Y L₁ L₂ s) : k = l :=
  Limits.pullback.hom_ext hbase hfibre

include h₁ h₂ in
/-- A morphism into `D ×_Y Tot(L₁^{⊗ -1})` is determined by its two coordinates. -/
theorem branchFibreProduct₂_hom_ext {W : Scheme.{u}}
    {k l : W ⟶ branchFibreProduct₂ Y L₁ L₂ s}
    (hbase : k ≫ branchFibreProductToBase₂ Y L₁ L₂ s =
      l ≫ branchFibreProductToBase₂ Y L₁ L₂ s)
    (hfibre : k ≫ branchFibreProductToFibre₂ Y L₁ L₂ s =
      l ≫ branchFibreProductToFibre₂ Y L₁ L₂ s) : k = l :=
  Limits.pullback.hom_ext hbase hfibre

/-! ### The morphism to the ambient fibre product -/

include h₁ h₂ in
/-- The cone condition defining `Stacks.Chow.TensorZeroScheme.fibreProductToTotalSpace₁`: the
composite of `D ×_Y Tot(L₂^{⊗ -1}) ⟶ D ⟶ Y` with the zero section is a point of the first line
bundle over the same point of `Y` as the second coordinate. It is a theorem of its own so that
the definition below carries a name rather than a proof term: a proof inside a definition is
rechecked wherever that definition is unfolded. -/
theorem fibreProductToTotalSpace₁_condition :
    ((branchFibreProductToBase₁ Y L₁ L₂ s ≫ (zeroIdeal Y L₁ L₂ s).subschemeι) ≫
          (Stacks.LineBundle.inverseSituation Y L₁).zeroSection) ≫
        Stacks.LineBundle.lineBundleProj Y L₁ =
      branchFibreProductToFibre₁ Y L₁ L₂ s ≫ Stacks.LineBundle.lineBundleProj Y L₂ :=
  (comp_zeroSection_comp_lineBundleProj Y L₁
        (branchFibreProductToBase₁ Y L₁ L₂ s ≫ (zeroIdeal Y L₁ L₂ s).subschemeι)).trans
    (branchFibreProduct₁_condition Y L₁ L₂ s)

include h₁ h₂ in
/-- **The morphism `D ×_Y Tot(L₂^{⊗ -1}) ⟶ T` whose first coordinate is the zero section.** -/
def fibreProductToTotalSpace₁ : branchFibreProduct₁ Y L₁ L₂ s ⟶ totalSpace Y L₁ L₂ :=
  Limits.pullback.lift
    ((branchFibreProductToBase₁ Y L₁ L₂ s ≫ (zeroIdeal Y L₁ L₂ s).subschemeι) ≫
      (Stacks.LineBundle.inverseSituation Y L₁).zeroSection)
    (branchFibreProductToFibre₁ Y L₁ L₂ s)
    (fibreProductToTotalSpace₁_condition Y L₁ L₂ s)

include h₁ h₂ in
/-- The cone condition defining `Stacks.Chow.TensorZeroScheme.fibreProductToTotalSpace₂`, the
mirror of `Stacks.Chow.TensorZeroScheme.fibreProductToTotalSpace₁_condition`. -/
theorem fibreProductToTotalSpace₂_condition :
    branchFibreProductToFibre₂ Y L₁ L₂ s ≫ Stacks.LineBundle.lineBundleProj Y L₁ =
      ((branchFibreProductToBase₂ Y L₁ L₂ s ≫ (zeroIdeal Y L₁ L₂ s).subschemeι) ≫
          (Stacks.LineBundle.inverseSituation Y L₂).zeroSection) ≫
        Stacks.LineBundle.lineBundleProj Y L₂ :=
  (branchFibreProduct₂_condition Y L₁ L₂ s).symm.trans
    (comp_zeroSection_comp_lineBundleProj Y L₂
      (branchFibreProductToBase₂ Y L₁ L₂ s ≫ (zeroIdeal Y L₁ L₂ s).subschemeι)).symm

include h₁ h₂ in
/-- **The morphism `D ×_Y Tot(L₁^{⊗ -1}) ⟶ T` whose second coordinate is the zero section.** -/
def fibreProductToTotalSpace₂ : branchFibreProduct₂ Y L₁ L₂ s ⟶ totalSpace Y L₁ L₂ :=
  Limits.pullback.lift (branchFibreProductToFibre₂ Y L₁ L₂ s)
    ((branchFibreProductToBase₂ Y L₁ L₂ s ≫ (zeroIdeal Y L₁ L₂ s).subschemeι) ≫
      (Stacks.LineBundle.inverseSituation Y L₂).zeroSection)
    (fibreProductToTotalSpace₂_condition Y L₁ L₂ s)

include h₁ h₂ in
/-- The first coordinate of `D ×_Y Tot(L₂^{⊗ -1}) ⟶ T` is the zero section. -/
theorem fibreProductToTotalSpace₁_comp_firstProj :
    fibreProductToTotalSpace₁ Y L₁ L₂ s ≫ firstProj Y L₁ L₂ =
      (branchFibreProductToBase₁ Y L₁ L₂ s ≫ (zeroIdeal Y L₁ L₂ s).subschemeι) ≫
        (Stacks.LineBundle.inverseSituation Y L₁).zeroSection :=
  Limits.pullback.lift_fst _ _ _

include h₁ h₂ in
/-- The second coordinate of `D ×_Y Tot(L₂^{⊗ -1}) ⟶ T` is the projection to the line bundle. -/
theorem fibreProductToTotalSpace₁_comp_secondProj :
    fibreProductToTotalSpace₁ Y L₁ L₂ s ≫ secondProj Y L₁ L₂ =
      branchFibreProductToFibre₁ Y L₁ L₂ s :=
  Limits.pullback.lift_snd _ _ _

include h₁ h₂ in
/-- The second coordinate of `D ×_Y Tot(L₁^{⊗ -1}) ⟶ T` is the zero section. -/
theorem fibreProductToTotalSpace₂_comp_secondProj :
    fibreProductToTotalSpace₂ Y L₁ L₂ s ≫ secondProj Y L₁ L₂ =
      (branchFibreProductToBase₂ Y L₁ L₂ s ≫ (zeroIdeal Y L₁ L₂ s).subschemeι) ≫
        (Stacks.LineBundle.inverseSituation Y L₂).zeroSection :=
  Limits.pullback.lift_snd _ _ _

include h₁ h₂ in
/-- The first coordinate of `D ×_Y Tot(L₁^{⊗ -1}) ⟶ T` is the projection to the line bundle. -/
theorem fibreProductToTotalSpace₂_comp_firstProj :
    fibreProductToTotalSpace₂ Y L₁ L₂ s ≫ firstProj Y L₁ L₂ =
      branchFibreProductToFibre₂ Y L₁ L₂ s :=
  Limits.pullback.lift_fst _ _ _

include h₁ h₂ in
/-- The morphism `D ×_Y Tot(L₂^{⊗ -1}) ⟶ T` lies over `D`. -/
theorem fibreProductToTotalSpace₁_comp_totalProj :
    fibreProductToTotalSpace₁ Y L₁ L₂ s ≫ totalProj Y L₁ L₂ =
      branchFibreProductToBase₁ Y L₁ L₂ s ≫ (zeroIdeal Y L₁ L₂ s).subschemeι :=
  (Category.assoc (fibreProductToTotalSpace₁ Y L₁ L₂ s) (firstProj Y L₁ L₂)
      (Stacks.LineBundle.lineBundleProj Y L₁)).symm.trans
    ((congrArg (fun k => k ≫ Stacks.LineBundle.lineBundleProj Y L₁)
        (fibreProductToTotalSpace₁_comp_firstProj Y L₁ L₂ s)).trans
      (comp_zeroSection_comp_lineBundleProj Y L₁
        (branchFibreProductToBase₁ Y L₁ L₂ s ≫ (zeroIdeal Y L₁ L₂ s).subschemeι)))

include h₁ h₂ in
/-- The morphism `D ×_Y Tot(L₁^{⊗ -1}) ⟶ T` lies over `D`. -/
theorem fibreProductToTotalSpace₂_comp_totalProj :
    fibreProductToTotalSpace₂ Y L₁ L₂ s ≫ totalProj Y L₁ L₂ =
      branchFibreProductToBase₂ Y L₁ L₂ s ≫ (zeroIdeal Y L₁ L₂ s).subschemeι :=
  (congrArg (fun k => fibreProductToTotalSpace₂ Y L₁ L₂ s ≫ k)
      (secondProj_comp Y L₁ L₂).symm).trans
    ((Category.assoc (fibreProductToTotalSpace₂ Y L₁ L₂ s) (secondProj Y L₁ L₂)
        (Stacks.LineBundle.lineBundleProj Y L₂)).symm.trans
      ((congrArg (fun k => k ≫ Stacks.LineBundle.lineBundleProj Y L₂)
          (fibreProductToTotalSpace₂_comp_secondProj Y L₁ L₂ s)).trans
        (comp_zeroSection_comp_lineBundleProj Y L₂
          (branchFibreProductToBase₂ Y L₁ L₂ s ≫ (zeroIdeal Y L₁ L₂ s).subschemeι))))

include h₁ h₂ in
/-- The first fibre coordinate vanishes on `D ×_Y Tot(L₂^{⊗ -1})`. -/
theorem pullbackGlobalSections_coord₁_fibreProductToTotalSpace₁ :
    pullbackGlobalSections (fibreProductToTotalSpace₁ Y L₁ L₂ s)
      ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁) (coord₁ Y L₁ L₂) = 0 :=
  (pullbackGlobalSections_coord₁_eq_zero_iff Y L₁ L₂
      (fibreProductToTotalSpace₁ Y L₁ L₂ s)).mpr
    ⟨branchFibreProductToBase₁ Y L₁ L₂ s ≫ (zeroIdeal Y L₁ L₂ s).subschemeι,
      (fibreProductToTotalSpace₁_comp_firstProj Y L₁ L₂ s).symm⟩

include h₁ h₂ in
/-- The second fibre coordinate vanishes on `D ×_Y Tot(L₁^{⊗ -1})`. -/
theorem pullbackGlobalSections_coord₂_fibreProductToTotalSpace₂ :
    pullbackGlobalSections (fibreProductToTotalSpace₂ Y L₁ L₂ s)
      ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂) (coord₂ Y L₁ L₂) = 0 :=
  (pullbackGlobalSections_coord₂_eq_zero_iff Y L₁ L₂
      (fibreProductToTotalSpace₂ Y L₁ L₂ s)).mpr
    ⟨branchFibreProductToBase₂ Y L₁ L₂ s ≫ (zeroIdeal Y L₁ L₂ s).subschemeι,
      (fibreProductToTotalSpace₂_comp_secondProj Y L₁ L₂ s).symm⟩

include h₁ h₂ in
/-- `D ×_Y Tot(L₂^{⊗ -1})` lies over `D`. -/
theorem zeroIdeal_le_ker_fibreProductToTotalSpace₁_comp_totalProj :
    zeroIdeal Y L₁ L₂ s ≤ (fibreProductToTotalSpace₁ Y L₁ L₂ s ≫ totalProj Y L₁ L₂).ker :=
  (Stacks.Divisors.le_ker_iff_factorsThrough _ _).mpr
    ⟨branchFibreProductToBase₁ Y L₁ L₂ s,
      (fibreProductToTotalSpace₁_comp_totalProj Y L₁ L₂ s).symm⟩

include h₁ h₂ in
/-- `D ×_Y Tot(L₁^{⊗ -1})` lies over `D`. -/
theorem zeroIdeal_le_ker_fibreProductToTotalSpace₂_comp_totalProj :
    zeroIdeal Y L₁ L₂ s ≤ (fibreProductToTotalSpace₂ Y L₁ L₂ s ≫ totalProj Y L₁ L₂).ker :=
  (Stacks.Divisors.le_ker_iff_factorsThrough _ _).mpr
    ⟨branchFibreProductToBase₂ Y L₁ L₂ s,
      (fibreProductToTotalSpace₂_comp_totalProj Y L₁ L₂ s).symm⟩

/-! ### The comparison morphisms -/

include h₁ h₂ in
/-- The cone condition defining `Stacks.Chow.TensorZeroScheme.branchToFibreProduct₁`: the two
coordinates `p₁` and `ι₁ ≫ pr₂` of the first branch lie over the same point of `Y`. -/
theorem branchToFibreProduct₁_condition :
    proj₁ Y L₁ L₂ s ≫ (zeroIdeal Y L₁ L₂ s).subschemeι =
      (branchι₁ Y L₁ L₂ s ≫ secondProj Y L₁ L₂) ≫ Stacks.LineBundle.lineBundleProj Y L₂ :=
  (proj₁_comp_zeroIdeal_subschemeι Y L₁ L₂ s).trans
    ((congrArg (fun k => branchι₁ Y L₁ L₂ s ≫ k) (secondProj_comp Y L₁ L₂).symm).trans
      (Category.assoc (branchι₁ Y L₁ L₂ s) (secondProj Y L₁ L₂)
        (Stacks.LineBundle.lineBundleProj Y L₂)).symm)

include h₁ h₂ in
/-- **The comparison morphism `D₁ ⟶ D ×_Y Tot(L₂^{⊗ -1})`**, with coordinates `p₁` and the
branch's second coordinate. -/
def branchToFibreProduct₁ :
    (branch₁ Y L₁ L₂ s).subscheme ⟶ branchFibreProduct₁ Y L₁ L₂ s :=
  Limits.pullback.lift (proj₁ Y L₁ L₂ s) (branchι₁ Y L₁ L₂ s ≫ secondProj Y L₁ L₂)
    (branchToFibreProduct₁_condition Y L₁ L₂ s)

include h₁ h₂ in
/-- The cone condition defining `Stacks.Chow.TensorZeroScheme.branchToFibreProduct₂`, the mirror
of `Stacks.Chow.TensorZeroScheme.branchToFibreProduct₁_condition`. -/
theorem branchToFibreProduct₂_condition :
    proj₂ Y L₁ L₂ s ≫ (zeroIdeal Y L₁ L₂ s).subschemeι =
      (branchι₂ Y L₁ L₂ s ≫ firstProj Y L₁ L₂) ≫ Stacks.LineBundle.lineBundleProj Y L₁ :=
  (proj₂_comp_zeroIdeal_subschemeι Y L₁ L₂ s).trans
    (Category.assoc (branchι₂ Y L₁ L₂ s) (firstProj Y L₁ L₂)
      (Stacks.LineBundle.lineBundleProj Y L₁)).symm

include h₁ h₂ in
/-- **The comparison morphism `D₂ ⟶ D ×_Y Tot(L₁^{⊗ -1})`**, with coordinates `p₂` and the
branch's first coordinate. -/
def branchToFibreProduct₂ :
    (branch₂ Y L₁ L₂ s).subscheme ⟶ branchFibreProduct₂ Y L₁ L₂ s :=
  Limits.pullback.lift (proj₂ Y L₁ L₂ s) (branchι₂ Y L₁ L₂ s ≫ firstProj Y L₁ L₂)
    (branchToFibreProduct₂_condition Y L₁ L₂ s)

include h₁ h₂ in
/-- **The comparison morphism for the first branch is a morphism over `D`.** -/
theorem branchToFibreProduct₁_comp_base :
    branchToFibreProduct₁ Y L₁ L₂ s ≫ branchFibreProductToBase₁ Y L₁ L₂ s =
      proj₁ Y L₁ L₂ s :=
  Limits.pullback.lift_fst _ _ _

include h₁ h₂ in
/-- **The comparison morphism for the second branch is a morphism over `D`.** -/
theorem branchToFibreProduct₂_comp_base :
    branchToFibreProduct₂ Y L₁ L₂ s ≫ branchFibreProductToBase₂ Y L₁ L₂ s =
      proj₂ Y L₁ L₂ s :=
  Limits.pullback.lift_fst _ _ _

include h₁ h₂ in
/-- The line-bundle coordinate of the comparison morphism for the first branch. -/
theorem branchToFibreProduct₁_comp_fibre :
    branchToFibreProduct₁ Y L₁ L₂ s ≫ branchFibreProductToFibre₁ Y L₁ L₂ s =
      branchι₁ Y L₁ L₂ s ≫ secondProj Y L₁ L₂ :=
  Limits.pullback.lift_snd _ _ _

include h₁ h₂ in
/-- The line-bundle coordinate of the comparison morphism for the second branch. -/
theorem branchToFibreProduct₂_comp_fibre :
    branchToFibreProduct₂ Y L₁ L₂ s ≫ branchFibreProductToFibre₂ Y L₁ L₂ s =
      branchι₂ Y L₁ L₂ s ≫ firstProj Y L₁ L₂ :=
  Limits.pullback.lift_snd _ _ _

include h₁ h₂ in
/-- The comparison morphism for the first branch is compatible with the two morphisms to `T`. -/
theorem branchToFibreProduct₁_comp_fibreProductToTotalSpace₁ :
    branchToFibreProduct₁ Y L₁ L₂ s ≫ fibreProductToTotalSpace₁ Y L₁ L₂ s =
      branchι₁ Y L₁ L₂ s := by
  refine totalSpace_hom_ext Y L₁ L₂ ?_ ?_
  · rw [Category.assoc, fibreProductToTotalSpace₁_comp_firstProj, branchι₁_comp_firstProj,
      ← proj₁_comp_zeroIdeal_subschemeι, ← branchToFibreProduct₁_comp_base]
    exact (Category.assoc _ _ _).symm
  · rw [Category.assoc, fibreProductToTotalSpace₁_comp_secondProj,
      branchToFibreProduct₁_comp_fibre]

include h₁ h₂ in
/-- The comparison morphism for the second branch is compatible with the two morphisms to `T`. -/
theorem branchToFibreProduct₂_comp_fibreProductToTotalSpace₂ :
    branchToFibreProduct₂ Y L₁ L₂ s ≫ fibreProductToTotalSpace₂ Y L₁ L₂ s =
      branchι₂ Y L₁ L₂ s := by
  refine totalSpace_hom_ext Y L₁ L₂ ?_ ?_
  · rw [Category.assoc, fibreProductToTotalSpace₂_comp_firstProj,
      branchToFibreProduct₂_comp_fibre]
  · rw [Category.assoc, fibreProductToTotalSpace₂_comp_secondProj,
      branchι₂_comp_secondProj, ← proj₂_comp_zeroIdeal_subschemeι,
      ← branchToFibreProduct₂_comp_base]
    exact (Category.assoc _ _ _).symm

/-! ### The comparison morphisms are isomorphisms -/

include h₁ h₂ in
/-- **The first branch is the second line bundle restricted to `D`.** -/
instance isIso_branchToFibreProduct₁ : IsIso (branchToFibreProduct₁ Y L₁ L₂ s) := by
  obtain ⟨u, hu⟩ := (factorsThrough_branch₁_iff Y L₁ L₂ s
    (fibreProductToTotalSpace₁ Y L₁ L₂ s)).mpr
    ⟨pullbackGlobalSections_coord₁_fibreProductToTotalSpace₁ Y L₁ L₂ s,
      zeroIdeal_le_ker_fibreProductToTotalSpace₁_comp_totalProj Y L₁ L₂ s⟩
  have : Mono (branchι₁ Y L₁ L₂ s) :=
    show Mono ((branch₁ Y L₁ L₂ s).subschemeι ≫ (spaceIdeal Y L₁ L₂ s).subschemeι) from
      inferInstance
  refine ⟨⟨u, ?_, ?_⟩⟩
  · rw [← cancel_mono (branchι₁ Y L₁ L₂ s), Category.assoc, hu,
      branchToFibreProduct₁_comp_fibreProductToTotalSpace₁, Category.id_comp]
  · refine branchFibreProduct₁_hom_ext Y L₁ L₂ s ?_ ?_
    · rw [Category.assoc, branchToFibreProduct₁_comp_base, Category.id_comp,
        ← cancel_mono (zeroIdeal Y L₁ L₂ s).subschemeι, Category.assoc,
        proj₁_comp_zeroIdeal_subschemeι, ← Category.assoc, hu,
        fibreProductToTotalSpace₁_comp_totalProj]
    · rw [Category.assoc, branchToFibreProduct₁_comp_fibre, ← Category.assoc, hu,
        fibreProductToTotalSpace₁_comp_secondProj, Category.id_comp]

include h₁ h₂ in
/-- **The second branch is the first line bundle restricted to `D`.** -/
instance isIso_branchToFibreProduct₂ : IsIso (branchToFibreProduct₂ Y L₁ L₂ s) := by
  obtain ⟨u, hu⟩ := (factorsThrough_branch₂_iff Y L₁ L₂ s
    (fibreProductToTotalSpace₂ Y L₁ L₂ s)).mpr
    ⟨pullbackGlobalSections_coord₂_fibreProductToTotalSpace₂ Y L₁ L₂ s,
      zeroIdeal_le_ker_fibreProductToTotalSpace₂_comp_totalProj Y L₁ L₂ s⟩
  have : Mono (branchι₂ Y L₁ L₂ s) :=
    show Mono ((branch₂ Y L₁ L₂ s).subschemeι ≫ (spaceIdeal Y L₁ L₂ s).subschemeι) from
      inferInstance
  refine ⟨⟨u, ?_, ?_⟩⟩
  · rw [← cancel_mono (branchι₂ Y L₁ L₂ s), Category.assoc, hu,
      branchToFibreProduct₂_comp_fibreProductToTotalSpace₂, Category.id_comp]
  · refine branchFibreProduct₂_hom_ext Y L₁ L₂ s ?_ ?_
    · rw [Category.assoc, branchToFibreProduct₂_comp_base, Category.id_comp,
        ← cancel_mono (zeroIdeal Y L₁ L₂ s).subschemeι, Category.assoc,
        proj₂_comp_zeroIdeal_subschemeι, ← Category.assoc, hu,
        fibreProductToTotalSpace₂_comp_totalProj]
    · rw [Category.assoc, branchToFibreProduct₂_comp_fibre, ← Category.assoc, hu,
        fibreProductToTotalSpace₂_comp_firstProj, Category.id_comp]

include h₁ h₂ in
/-- **The first branch `D₁` is `D ×_Y Tot(L₂^{⊗ -1})` over `D`.** -/
theorem exists_iso_branchFibreProduct₁ :
    ∃ e : (branch₁ Y L₁ L₂ s).subscheme ≅ branchFibreProduct₁ Y L₁ L₂ s,
      e.hom ≫ branchFibreProductToBase₁ Y L₁ L₂ s = proj₁ Y L₁ L₂ s :=
  ⟨asIso (branchToFibreProduct₁ Y L₁ L₂ s), branchToFibreProduct₁_comp_base Y L₁ L₂ s⟩

include h₁ h₂ in
/-- **The second branch `D₂` is `D ×_Y Tot(L₁^{⊗ -1})` over `D`.** -/
theorem exists_iso_branchFibreProduct₂ :
    ∃ e : (branch₂ Y L₁ L₂ s).subscheme ≅ branchFibreProduct₂ Y L₁ L₂ s,
      e.hom ≫ branchFibreProductToBase₂ Y L₁ L₂ s = proj₂ Y L₁ L₂ s :=
  ⟨asIso (branchToFibreProduct₂ Y L₁ L₂ s), branchToFibreProduct₂_comp_base Y L₁ L₂ s⟩

end Stacks.Chow.TensorZeroScheme

end
