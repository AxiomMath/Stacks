module

public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsCokernel
public import StacksFrontier.AlgebraicGeometry.Spaces.ShortExactCartesianCharts

/-!
# Two out of three for quasi-coherence in a short exact sequence on an algebraic space

Stacks 03M1 asserts, among other things, that in a short exact sequence
`0 → F₁ → F₂ → F₃ → 0` of `𝒪_F`-modules on an algebraic space `F`, quasi-coherence of two of
the three terms implies quasi-coherence of the third. This file proves the three implications,
with the module universe equal to the universe of the schemes and with two cited inputs as
explicit hypotheses:

* `h03DX` is the implication "quasi-coherent implies cartesian on affine charts" of Stacks 03DX(2)
  for the small étale site of `F`: the sections of a quasi-coherent `𝒪_F`-module over a smaller
  affine chart are the base change of its sections over a larger one. It is proved as
  `AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`, in a module that
  imports this one.
* `h03DW` is the vanishing of the first étale cohomology of a quasi-coherent module on an affine
  scheme, Stacks 03DW, in the form the argument uses: `F₂ → F₃` is surjective on the sections
  over every affine étale chart. It is needed for the middle and the right term, not for the left
  one.

The unconditional statement, with both inputs discharged, is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_shortExact_twoOutOfThree`.

## Main results

* `AlgebraicGeometry.Space.bijective_baseChange_of_shortExact_middle`: given a right exact
  sequence `G → G' → G'' → 0` of `R`-modules, a left exact sequence `0 → G₁ → G₁' → G₁''` of
  `A`-modules and comparison maps from the base changes which commute with the two sequences, the
  comparison at `G'` is bijective as soon as the ones at `G` and at `G''` are.
* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_shortExact_X₂` and
  `AlgebraicGeometry.Space.isCartesianOnAffineCharts_shortExact_X₃`: being cartesian on affine
  charts passes to the middle and to the right term of a short exact sequence from the other two,
  provided the right-hand map is surjective on the sections over affine charts.
* `AlgebraicGeometry.Space.isQuasicoherent_left_of_shortExact`,
  `AlgebraicGeometry.Space.isQuasicoherent_middle_of_shortExact` and
  `AlgebraicGeometry.Space.isQuasicoherent_right_of_shortExact`: the three implications of
  Stacks 03M1 for short exact sequences, with the two cited inputs above as hypotheses.
* `SheafOfModules.exact_val_app_of_shortExact` and
  `SheafOfModules.injective_f_val_app_of_shortExact`: sections of a short exact sequence of
  sheaves of modules are left exact.

## Implementation notes

The module universe is specialised to the universe `u` of the schemes. The argument needs `F₁` to
be a kernel of `F₂ → F₃` (`CategoryTheory.ShortComplex.ShortExact.fIsKernel`, which needs a
balanced category), and the abelian structure on
`AlgebraicGeometry.Space.Modules.{u, m} B S hS F hF` comes from sheafification of
`AddCommGrpCat.{m}`-valued presheaves on a site whose objects live in `Type (u + 1)`, which needs
`UnivLE.{u + 1, m}`; it is found by instance search for `m := u` and `m := u + 1`, not for an
independent `m`.

No `@[stacks]` attribute is claimed here, because the three theorems carry `h03DX` and (two of
them) `h03DW` as hypotheses; the attribute for Stacks 03M1 is on
`AlgebraicGeometry.Space.isQuasicoherentOnSite_shortExact_twoOutOfThree`.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 01IE](https://stacks.math.columbia.edu/tag/01IE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v r m

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-! ### Sections of a short exact sequence of sheaves of modules -/

/-- An isomorphism of sheaves of modules is bijective on the sections over every object. -/
theorem bijective_iso_hom_val_app {M N : SheafOfModules.{m} R} (e : M ≅ N) (X : Cᵒᵖ) :
    Function.Bijective (e.hom.val.app X) :=
  have : IsIso (e.hom.val.app X) :=
    inferInstanceAs (IsIso ((SheafOfModules.evaluation.{m} R X).map e.hom))
  ConcreteCategory.bijective_of_isIso (e.hom.val.app X)

/-- If `e : K ≅ kernel b` identifies `ι : K ⟶ M` with the inclusion of `kernel b`, then on the
sections over an object `ι` factors through the sections of `kernel b`. -/
theorem val_app_eq_of_isKernelIso {K M N : SheafOfModules.{m} R} {ι : K ⟶ M} {b : M ⟶ N}
    (e : K ≅ kernel b) (he : e.hom ≫ kernel.ι b = ι) (X : Cᵒᵖ) (x : K.val.obj X) :
    ι.val.app X x = (kernel.ι b).val.app X (e.hom.val.app X x) :=
  (congrFun (congrArg (fun g => (ConcreteCategory.hom g : _ → _))
    (congrArg (fun φ => (SheafOfModules.Hom.val φ).app X) he)) x).symm

/-- If `e : K ≅ kernel b` identifies `ι : K ⟶ M` with the inclusion of `kernel b`, then `ι` is
injective on the sections over every object. -/
theorem injective_val_app_of_isKernelIso {K M N : SheafOfModules.{m} R} {ι : K ⟶ M} {b : M ⟶ N}
    (e : K ≅ kernel b) (he : e.hom ≫ kernel.ι b = ι) (X : Cᵒᵖ) :
    Function.Injective (ι.val.app X) := fun x y hxy =>
  (bijective_iso_hom_val_app e X).1 (kernel_ι_val_app_injective b X
    ((val_app_eq_of_isKernelIso e he X x).symm.trans
      (hxy.trans (val_app_eq_of_isKernelIso e he X y))))

/-- **Sections take a kernel to a kernel.**  If `e : K ≅ kernel b` identifies `ι : K ⟶ M` with
the inclusion of `kernel b`, then the maps induced by `ι` and by `b` on the sections over every
object form an exact pair. -/
theorem exact_val_app_of_isKernelIso {K M N : SheafOfModules.{m} R} {ι : K ⟶ M} {b : M ⟶ N}
    (e : K ≅ kernel b) (he : e.hom ≫ kernel.ι b = ι) (X : Cᵒᵖ) :
    Function.Exact (ι.val.app X) (b.val.app X) := by
  intro y
  refine ⟨fun hy => ?_, ?_⟩
  · obtain ⟨z, hz⟩ := (exact_kernel_ι_val_app b X y).mp hy
    obtain ⟨w, hw⟩ := (bijective_iso_hom_val_app e X).2 z
    exact ⟨w, by rw [val_app_eq_of_isKernelIso e he X w, hw, hz]⟩
  · rintro ⟨w, rfl⟩
    rw [val_app_eq_of_isKernelIso e he X w]
    exact (exact_kernel_ι_val_app b X _).mpr ⟨_, rfl⟩

variable [Balanced (SheafOfModules.{m} R)]

/-- The canonical identification of the left term of a short exact sequence of sheaves of
modules with the kernel of its right-hand map, available because the category is balanced. -/
theorem exists_isKernelIso_of_shortExact {T : ShortComplex (SheafOfModules.{m} R)}
    (hT : T.ShortExact) : ∃ e : T.X₁ ≅ kernel T.g, e.hom ≫ kernel.ι T.g = T.f := by
  exact ⟨_, IsLimit.conePointUniqueUpToIso_hom_comp hT.fIsKernel (kernelIsKernel T.g)
    WalkingParallelPair.zero⟩

/-- The left-hand map of a short exact sequence of sheaves of modules is injective on the
sections over every object. -/
theorem injective_f_val_app_of_shortExact {T : ShortComplex (SheafOfModules.{m} R)}
    (hT : T.ShortExact) (X : Cᵒᵖ) : Function.Injective (T.f.val.app X) :=
  let ⟨e, he⟩ := exists_isKernelIso_of_shortExact hT
  injective_val_app_of_isKernelIso e he X

/-- Sections of a short exact sequence of sheaves of modules are left exact: the maps induced on
the sections over an object by the two maps of the sequence form an exact pair. -/
theorem exact_val_app_of_shortExact {T : ShortComplex (SheafOfModules.{m} R)}
    (hT : T.ShortExact) (X : Cᵒᵖ) : Function.Exact (T.f.val.app X) (T.g.val.app X) :=
  let ⟨e, he⟩ := exists_isKernelIso_of_shortExact hT
  exact_val_app_of_isKernelIso e he X

end SheafOfModules

namespace AlgebraicGeometry.Space

/-! ### The commutative-algebra step for the middle term -/

/-- Let `A` be an `R`-algebra, let `G → G' → G'' → 0` be a right exact sequence of `R`-modules and
let `0 → G₁ → G₁' → G₁''` be a left exact sequence of `A`-modules.  Suppose given `A`-linear
comparison maps from the base changes `A ⊗_R G`, `A ⊗_R G'`, `A ⊗_R G''` to `G₁`, `G₁'`, `G₁''`
which commute with the two sequences.  If the comparisons at `G` and at `G''` are bijective,
then so is the one at `G'`. -/
theorem bijective_baseChange_of_shortExact_middle
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {G G' G'' : Type*} [AddCommGroup G] [Module R G] [AddCommGroup G'] [Module R G']
    [AddCommGroup G''] [Module R G'']
    {G₁ G₁' G₁'' : Type*} [AddCommGroup G₁] [Module A G₁] [AddCommGroup G₁'] [Module A G₁']
    [AddCommGroup G₁''] [Module A G₁'']
    {φU : G →ₗ[R] G'} {πU : G' →ₗ[R] G''} {φV : G₁ →ₗ[A] G₁'} {πV : G₁' →ₗ[A] G₁''}
    {cG : TensorProduct R A G →ₗ[A] G₁} {cG' : TensorProduct R A G' →ₗ[A] G₁'}
    {cG'' : TensorProduct R A G'' →ₗ[A] G₁''}
    (hπU : Function.Surjective πU) (hexU : Function.Exact φU πU)
    (hφV : Function.Injective φV) (hexV : Function.Exact φV πV)
    (hsqG : ∀ z, φV (cG z) = cG' (LinearMap.lTensor A φU z))
    (hsqG' : ∀ z, πV (cG' z) = cG'' (LinearMap.lTensor A πU z))
    (hcG : Function.Bijective cG) (hcG'' : Function.Bijective cG'') :
    Function.Bijective cG' := by
  have hexA : Function.Exact (LinearMap.lTensor A φU) (LinearMap.lTensor A πU) :=
    _root_.lTensor_exact A hexU hπU
  refine ⟨(injective_iff_map_eq_zero cG').2 fun z hz => ?_, fun y => ?_⟩
  · have h2 : LinearMap.lTensor A πU z = 0 :=
      (map_eq_zero_iff _ hcG''.1).1 (by rw [← hsqG' z, hz, map_zero])
    obtain ⟨w, hw⟩ := (hexA z).mp h2
    have hw0 : w = 0 :=
      (map_eq_zero_iff _ hcG.1).1
        ((map_eq_zero_iff _ hφV).1 (by rw [hsqG w, hw, hz]))
    rw [← hw, hw0, map_zero]
  · obtain ⟨t, ht⟩ := hcG''.2 (πV y)
    obtain ⟨z, hz⟩ := LinearMap.lTensor_surjective A hπU t
    obtain ⟨x, hx⟩ := (hexV (y - cG' z)).mp (by rw [map_sub, hsqG' z, hz, ht, sub_self])
    obtain ⟨w, hw⟩ := hcG.2 x
    exact ⟨z + LinearMap.lTensor A φU w, by rw [map_add, ← hsqG w, hw, hx, add_sub_cancel]⟩

/-! ### The base change criterion along a short exact sequence -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- Let
`T : 0 → T.X₁ → T.X₂ → T.X₃ → 0` be a short exact sequence of `𝒪_F`-modules and let `f : V ⟶ U`
be a morphism of étale charts along which `T.g` is surjective on the sections over `U`.  If the
sections of `T.X₁` and of `T.X₃` over `V` are the base change of their sections over `U`, then so
are the sections of `T.X₂`. -/
theorem bijective_sectionsBaseChange_shortExact_X₂
    (T : ShortComplex (Modules.{u, u} B S hS F hF)) (hT : T.ShortExact)
    {U V : SmallEtale B S hS F} (f : V ⟶ U)
    (hgU : Function.Surjective (T.g.val.app (op U)))
    (h₁ : Function.Bijective (sectionsBaseChange T.X₁ f))
    (h₃ : Function.Bijective (sectionsBaseChange T.X₃ f)) :
    Function.Bijective (sectionsBaseChange T.X₂ f) := by
  let _ := chartAlgebra (hF := hF) f
  exact bijective_baseChange_of_shortExact_middle
    (φU := (T.f.val.app (op U)).hom) (πU := (T.g.val.app (op U)).hom)
    (φV := (T.f.val.app (op V)).hom) (πV := (T.g.val.app (op V)).hom)
    hgU (SheafOfModules.exact_val_app_of_shortExact hT (op U))
    (SheafOfModules.injective_f_val_app_of_shortExact hT (op V))
    (SheafOfModules.exact_val_app_of_shortExact hT (op V))
    (app_sectionsBaseChange T.f f) (app_sectionsBaseChange T.g f) h₁ h₃

/-- The middle term of a short exact sequence of `𝒪_F`-modules is cartesian on affine charts as
soon as the other two terms are, provided `T.g` is surjective on the sections over every affine
étale chart. -/
theorem isCartesianOnAffineCharts_shortExact_X₂
    (T : ShortComplex (Modules.{u, u} B S hS F hF)) (hT : T.ShortExact)
    (hg : ∀ U : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
        Function.Surjective (T.g.val.app (op U)))
    (h₁ : IsCartesianOnAffineCharts T.X₁) (h₃ : IsCartesianOnAffineCharts T.X₃) :
    IsCartesianOnAffineCharts T.X₂ :=
  fun U V hU hV f => bijective_sectionsBaseChange_shortExact_X₂ T hT f (hg U hU)
    (h₁ U V hU hV f) (h₃ U V hU hV f)

/-- The right term of a short exact sequence of `𝒪_F`-modules is cartesian on affine charts as
soon as the other two terms are, provided `T.g` is surjective on the sections over every affine
étale chart. -/
theorem isCartesianOnAffineCharts_shortExact_X₃
    (T : ShortComplex (Modules.{u, u} B S hS F hF)) (hT : T.ShortExact)
    (hg : ∀ U : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
        Function.Surjective (T.g.val.app (op U)))
    (h₁ : IsCartesianOnAffineCharts T.X₁) (h₂ : IsCartesianOnAffineCharts T.X₂) :
    IsCartesianOnAffineCharts T.X₃ :=
  isCartesianOnAffineCharts_cokernel T.f T.g hg
    (fun U _ => SheafOfModules.exact_val_app_of_shortExact hT (op U)) h₁ h₂

/-! ### Stacks 03M1 for short exact sequences -/

/-- Stacks 03M1 for short exact sequences, left term, given that quasi-coherent modules are
cartesian on affine charts (`h03DX`, Stacks 03DX(2)): the kernel term of a short exact sequence of
`𝒪_F`-modules on an algebraic space is quasi-coherent if the other two terms are. -/
theorem isQuasicoherent_left_of_shortExact
    (T : ShortComplex (Modules.{u, u} B S hS F hF)) (hT : T.ShortExact)
    (h03DX : ∀ G : Modules.{u, u} B S hS F hF,
      G.IsQuasicoherentOnSite → IsCartesianOnAffineCharts G)
    [T.X₂.IsQuasicoherentOnSite] [T.X₃.IsQuasicoherentOnSite] :
    T.X₁.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isCartesianOnAffineCharts _
    (isCartesianOnAffineCharts_shortExact_X₁ T hT
      (h03DX T.X₂ ‹T.X₂.IsQuasicoherentOnSite›)
      (h03DX T.X₃ ‹T.X₃.IsQuasicoherentOnSite›))

/-- Stacks 03M1 for short exact sequences, middle term, given that quasi-coherent modules are
cartesian on affine charts (`h03DX`, Stacks 03DX(2)) and that `T.g` is surjective on the sections
over every affine étale chart (`h03DW`, Stacks 03DW): an extension of quasi-coherent
`𝒪_F`-modules on an algebraic space is quasi-coherent. -/
theorem isQuasicoherent_middle_of_shortExact
    (T : ShortComplex (Modules.{u, u} B S hS F hF)) (hT : T.ShortExact)
    (h03DX : ∀ G : Modules.{u, u} B S hS F hF,
      G.IsQuasicoherentOnSite → IsCartesianOnAffineCharts G)
    (h03DW : ∀ U : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
        Function.Surjective (T.g.val.app (op U)))
    [T.X₁.IsQuasicoherentOnSite] [T.X₃.IsQuasicoherentOnSite] :
    T.X₂.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isCartesianOnAffineCharts _
    (isCartesianOnAffineCharts_shortExact_X₂ T hT h03DW
      (h03DX T.X₁ ‹T.X₁.IsQuasicoherentOnSite›)
      (h03DX T.X₃ ‹T.X₃.IsQuasicoherentOnSite›))

/-- Stacks 03M1 for short exact sequences, right term, given that quasi-coherent modules are
cartesian on affine charts (`h03DX`, Stacks 03DX(2)) and that `T.g` is surjective on the sections
over every affine étale chart (`h03DW`, Stacks 03DW): the quotient term of a short exact sequence
of `𝒪_F`-modules on an algebraic space is quasi-coherent if the other two terms are. -/
theorem isQuasicoherent_right_of_shortExact
    (T : ShortComplex (Modules.{u, u} B S hS F hF)) (hT : T.ShortExact)
    (h03DX : ∀ G : Modules.{u, u} B S hS F hF,
      G.IsQuasicoherentOnSite → IsCartesianOnAffineCharts G)
    (h03DW : ∀ U : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
        Function.Surjective (T.g.val.app (op U)))
    [T.X₁.IsQuasicoherentOnSite] [T.X₂.IsQuasicoherentOnSite] :
    T.X₃.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isCartesianOnAffineCharts _
    (isCartesianOnAffineCharts_shortExact_X₃ T hT h03DW
      (h03DX T.X₁ ‹T.X₁.IsQuasicoherentOnSite›)
      (h03DX T.X₂ ‹T.X₂.IsQuasicoherentOnSite›))

end AlgebraicGeometry.Space

end
