module

public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsCokernel
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealCartesian

/-!
# Free `𝒪_F`-modules on an algebraic space are cartesian on affine charts

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  An
`𝒪_F`-module `G` on the small étale site of `F` is *cartesian on affine charts*
(`AlgebraicGeometry.Space.IsCartesianOnAffineCharts`) when for every morphism `f : V ⟶ U` of
affine étale charts the base change comparison

`𝒪_F(V) ⊗_{𝒪_F(U)} G(U) ⟶ G(V)`

is bijective.  That criterion is the base change half of Descent, Proposition 03DX(2), and it is
what the chart-sections files of this tree carry as a hypothesis.

This file discharges the criterion for the two module types a global presentation is built from:
the structure sheaf `𝒪_F` itself, and the coproducts of copies of it.  These are the base case
of Descent, Proposition 03DX(2): the base change comparison of a free module is the comparison
`𝒪_F(V) ⊗_{𝒪_F(U)} (I →₀ 𝒪_F(U)) ⟶ (I →₀ 𝒪_F(V))`, which is an isomorphism for purely
algebraic reasons once the sections of a coproduct over an affine chart are known to be the
finitely supported families — which is
`AlgebraicGeometry.Space.bijective_freeSectionsMap_of_isAffine`, whose own input is the finite
affine refinement of
`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_refinement`.

Combining with the cokernel clause already in the tree gives the presentation-level statement:
a module presented on the whole site by free modules is cartesian on affine charts, as soon as
the presentation is exact on the sections over affine charts.  That exactness hypothesis is the
only thing left, and it is the cohomological content of Stacks 03DX(2); see the implementation
notes.

## Main results

* `AlgebraicGeometry.Space.bijective_sectionsBaseChange_of_finsuppEquiv`: **a module whose
  sections over two charts are identified with finitely supported families of regular functions,
  compatibly with restriction, has bijective base change comparison between them.**  This is the
  commuting square of the base change comparison in the only form it is needed in, and it is
  what the free case below and the locally free case of
  `StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCoherent` both apply; neither repeats
  the square.
* `AlgebraicGeometry.Space.freeSectionsMap_restrict`: restriction of sections of a free
  `𝒪_F`-module along a chart morphism is, through the comparison map of
  `Stacks.Sites.freeSectionsMap`, the coefficientwise restriction of functions.
* `AlgebraicGeometry.Space.bijective_sectionsBaseChange_free` and
  `AlgebraicGeometry.Space.isCartesianOnAffineCharts_free`: **a free `𝒪_F`-module is cartesian
  on affine charts.**
* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isColimit_cofan`: the same for a module
  exhibited abstractly as a coproduct of copies of `𝒪_F`, which is the shape in which
  `SheafOfModules.HasGlobalPresentation` presents its two terms.
* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_presentation`: **a module presented by
  coproducts of copies of `𝒪_F` is cartesian on affine charts**, granted that the presentation
  is exact on the sections over affine charts.

## Implementation notes

The module universe is pinned to the universe `u` of the schemes throughout, and this is forced
by Mathlib and not by this repository: `SheafOfModules.free` is declared only for `I : Type u`
and `R : Sheaf J RingCat.{u}`, with value in `SheafOfModules.{u} R`, so a free module at an
unrelated module universe does not exist to be talked about.  The same pin is recorded in the
implementation notes of `StacksFrontier/AlgebraicGeometry/Spaces/FreeModuleSections.lean`.

The comparison with the finitely supported families is `Stacks.Sites.freeSectionsMap`, and the
proof of `AlgebraicGeometry.Space.bijective_sectionsBaseChange_free` is a commuting square: the
base change comparison of the free module, precomposed with the base change of that map over
the larger chart, is the map of `Stacks.Sites.freeSectionsMap` over the smaller chart
precomposed with Mathlib's `TensorProduct.finsuppScalarRight`.  Both outer maps are bijective —
the first because the charts are affine, hence quasi-compact objects of the site — so the base
change comparison is.  Only the square is proved by hand, and it reduces on generators to the
commutativity of the ring of functions, which is
`AlgebraicGeometry.Space.chartRing_commRing`.

`AlgebraicGeometry.Space.freeSectionsMap_restrict` is proved as an equality of *additive* maps
and then evaluated, rather than by an induction on the finitely supported family: the two sides
are additive but only semilinear, so `Finsupp.addHom_ext` is the available extensionality
principle and it reduces the statement to the tautological sections, where it is the naturality
of `SheafOfModules.ιFree i`.

The hypotheses `hb` and `hex` of
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_presentation` are what
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_cokernel` needs, and they are not free: a
cokernel of sheaves of modules is the sheafification of the objectwise cokernel, so a
presentation of a sheaf of modules is in general *not* a presentation of its sections over an
object.  Over an affine chart the discrepancy is the first étale cohomology of the image of the
presentation map.  So this file does not prove Descent, Proposition 03DX(2); it proves that
everything in 03DX(2) except that cohomological discrepancy is available, and localises the
discrepancy in two explicitly stated hypotheses.  The counterexample showing the discrepancy is
real on a non-affine object — `U = Spec k[x, y]`, `W = U ∖ {(x, y)}` and the Koszul
presentation, where the objectwise cokernel has sections `k` over `W` and the sheaf cokernel has
`0` — is recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSections.lean`.

No `@[stacks]` attribute is claimed.  Descent, Proposition 03DX(2) is an equivalence of
categories, and `AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_presentation` is
conditional on the two sections-level hypotheses above; the convention of the sibling files
`AlgebraicGeometry.Spaces.ChartSectionsKernel`,
`AlgebraicGeometry.Spaces.ChartSectionsCokernel` and
`AlgebraicGeometry.Spaces.ShortExactQuasicoherent` — no tag on a conditional statement — is
followed here.  Stacks 0935, the computation of the sections of a coproduct over a
quasi-compact object, is already tagged in
`StacksFrontier/CategoryTheory/Sites/QuasiCompact/SetCoproductSections.lean` and
`StacksFrontier/CategoryTheory/Sites/QuasiCompact/ModuleSections.lean`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 0935](https://stacks.math.columbia.edu/tag/0935)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

universe u m

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-! ### The structure sheaf is cartesian -/

/-! ### Restriction of sections of a free module -/

/-- **Restriction of sections of a free `𝒪_F`-module is coefficientwise restriction of
functions.**  Through the comparison map of `Stacks.Sites.freeSectionsMap`, which carries a
finitely supported family of regular functions on a chart to a section of
`SheafOfModules.free I` over it, restriction along a chart morphism `f : V ⟶ U` is
`Finsupp.mapRange` of the restriction map of regular functions.

Both sides are additive and only semilinear, so the proof is an application of
`Finsupp.addHom_ext` reducing the statement to the tautological sections, where it is the
naturality of `SheafOfModules.ιFree i`. -/
theorem freeSectionsMap_restrict (I : Type u) {U V : SmallEtale B S hS F} (f : V ⟶ U)
    (x : I →₀ chartRing B S hS F hF U) :
    (SheafOfModules.free
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
          I).val.map f.op
        ((Stacks.Sites.freeSectionsMap
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
          I (op U)).hom x) =
      (Stacks.Sites.freeSectionsMap
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
          I (op V)).hom
        (Finsupp.mapRange (chartRestrict (hF := hF) f) (map_zero _) x) := by
  have h : ((SheafOfModules.free
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
          I).val.map f.op).hom.toAddMonoidHom.comp
        (Stacks.Sites.freeSectionsMap
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
          I (op U)).hom.toAddMonoidHom =
      (Stacks.Sites.freeSectionsMap
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
          I (op V)).hom.toAddMonoidHom.comp
        (Finsupp.mapRange.addMonoidHom (chartRestrict (hF := hF) f).toAddMonoidHom) := by
    refine Finsupp.addHom_ext ?_
    intro i r
    change (SheafOfModules.free
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
          I).val.map f.op
        ((Stacks.Sites.freeSectionsMap
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
          I (op U)).hom
          (Finsupp.single i r)) =
      (Stacks.Sites.freeSectionsMap
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
          I (op V)).hom
        (Finsupp.mapRange (chartRestrict (hF := hF) f) (map_zero _) (Finsupp.single i r))
    rw [Stacks.Sites.freeSectionsMap_single, Finsupp.mapRange_single,
      Stacks.Sites.freeSectionsMap_single]
    exact (PresheafOfModules.naturality_apply
      (ιFree (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
        i).val f.op r).symm
  exact DFunLike.congr_fun h x

/-- Scaling a coefficientwise restricted family is Mathlib's base change isomorphism
`TensorProduct.finsuppScalarRight` of the finitely supported families.  This is the only place
where commutativity of the ring of regular functions on a chart is used. -/
theorem smul_mapRange_eq_finsuppScalarRight {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A) (I : Type*) [DecidableEq I] (b : A) (p : I →₀ R) :
    letI := φ.toAlgebra
    b • Finsupp.mapRange φ (map_zero φ) p =
      TensorProduct.finsuppScalarRight R A A I (TensorProduct.tmul R b p) := by
  let _ := φ.toAlgebra
  refine Finsupp.ext fun i => ?_
  rw [TensorProduct.finsuppScalarRight_apply_tmul_apply]
  change b * φ (p i) = p i • b
  exact mul_comm b (φ (p i))

/-! ### Free modules are cartesian on affine charts -/

/-- **A module whose sections over two charts are finitely supported families of regular
functions, compatibly with restriction, has bijective base change comparison between them.**

This is the abstract form of the commuting square which
`AlgebraicGeometry.Space.bijective_sectionsBaseChange_free` runs for `SheafOfModules.free`: the
comparison becomes `𝒪_F(V) ⊗_{𝒪_F(U)} (I →₀ 𝒪_F(U)) ⟶ (I →₀ 𝒪_F(V))`, which is Mathlib's
`TensorProduct.finsuppScalarRight`.  The index universe is free; only the two rings of regular
functions live in the universe of the schemes. -/
theorem bijective_sectionsBaseChange_of_finsuppEquiv {M : Modules.{u, m} B S hS F hF}
    {I : Type*} {U V : SmallEtale B S hS F} (f : V ⟶ U)
    (θU : (M.val.obj (op U)) ≃ₗ[chartRing B S hS F hF U] (I →₀ chartRing B S hS F hF U))
    (θV : (M.val.obj (op V)) ≃ₗ[chartRing B S hS F hF V] (I →₀ chartRing B S hS F hF V))
    (hnat : ∀ (x : M.val.obj (op U)) (i : I),
      θV (chartRestrictLinear M f x) i = chartRestrict (hF := hF) f (θU x i)) :
    Function.Bijective (sectionsBaseChange M f) := by
  classical
  let _ := chartAlgebra (hF := hF) f
  let _ := chartSectionsModule M f
  have _ := chartSections_isScalarTower M f
  set G : TensorProduct (chartRing B S hS F hF U) (chartRing B S hS F hF V)
      (M.val.obj (op U)) → (I →₀ chartRing B S hS F hF V) := fun z =>
    TensorProduct.finsuppScalarRight (chartRing B S hS F hF U) (chartRing B S hS F hF V)
      (chartRing B S hS F hF V) I
      (LinearMap.lTensor (chartRing B S hS F hF V) θU.toLinearMap z) with hG
  have hGbij : Function.Bijective G :=
    (TensorProduct.finsuppScalarRight (chartRing B S hS F hF U) (chartRing B S hS F hF V)
      (chartRing B S hS F hF V) I).bijective.comp
      ((LinearEquiv.lTensor (chartRing B S hS F hF V) θU).bijective)
  have hGadd : ∀ z w, G (z + w) = G z + G w := by intro z w; simp only [hG, map_add]
  have hrestrict : ∀ x : M.val.obj (op U),
      θV (chartRestrictLinear M f x)
        = Finsupp.mapRange (chartRestrict (hF := hF) f) (map_zero _) (θU x) :=
    fun x => Finsupp.ext fun i => (hnat x i).trans (Finsupp.mapRange_apply ..).symm
  have key : ∀ z, θV (sectionsBaseChange M f z) = G z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul b y =>
      rw [hG]
      rw [chartBaseChange_tmul M f b y, map_smul, hrestrict y]
      exact smul_mapRange_eq_finsuppScalarRight (chartRestrict (hF := hF) f) I b (θU y)
    | add z w hz hw => rw [map_add, map_add, hz, hw, hGadd]
  have hfun : ⇑(sectionsBaseChange M f) = θV.symm ∘ G :=
    funext fun z =>
      (θV.symm_apply_apply (sectionsBaseChange M f z)).symm.trans (congrArg θV.symm (key z))
  rw [hfun]
  exact θV.symm.bijective.comp hGbij

/-- **The base change comparison of a free `𝒪_F`-module is bijective between affine charts.**

The sections of `SheafOfModules.free I` over an affine chart `W` are the finitely supported
`I`-indexed families of regular functions on `W`
(`AlgebraicGeometry.Space.bijective_freeSectionsMap_of_isAffine`, whose content is Stacks 0935
and the finite affine refinement of an étale covering of an affine chart), and restriction is
coefficientwise (`AlgebraicGeometry.Space.freeSectionsMap_restrict`).  So the comparison becomes
`𝒪_F(V) ⊗_{𝒪_F(U)} (I →₀ 𝒪_F(U)) ⟶ (I →₀ 𝒪_F(V))`, which is Mathlib's
`TensorProduct.finsuppScalarRight`; the identification and the commuting square it rests on are
`AlgebraicGeometry.Space.bijective_sectionsBaseChange_of_finsuppEquiv`, applied to the two
isomorphisms of `Stacks.Sites.freeSectionsMap` and to the coefficientwise restriction. -/
theorem bijective_sectionsBaseChange_free (I : Type u) {U V : SmallEtale B S hS F} (f : V ⟶ U)
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V)) :
    Function.Bijective (sectionsBaseChange (SheafOfModules.free
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
      I) f) := by
  classical
  set eU := LinearEquiv.ofBijective (Stacks.Sites.freeSectionsMap
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
      I (op U)).hom
    (bijective_freeSectionsMap_of_isAffine B S hS F hF I U hU)
  set eV := LinearEquiv.ofBijective (Stacks.Sites.freeSectionsMap
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
      I (op V)).hom
    (bijective_freeSectionsMap_of_isAffine B S hS F hF I V hV)
  refine bijective_sectionsBaseChange_of_finsuppEquiv f eU.symm eV.symm (fun x i => ?_)
  obtain ⟨p, rfl⟩ : ∃ p, x = eU p := ⟨eU.symm x, (eU.apply_symm_apply x).symm⟩
  have hy : eV.symm (chartRestrictLinear (SheafOfModules.free
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
        I) f (eU p))
      = Finsupp.mapRange (chartRestrict (hF := hF) f) (map_zero _) p := by
    refine (eV.symm_apply_eq).2 ?_
    rw [chartRestrictLinear_apply]
    exact freeSectionsMap_restrict (hF := hF) I f p
  rw [eU.symm_apply_apply]
  exact (congrArg (fun q : I →₀ chartRing B S hS F hF V => q i) hy).trans Finsupp.mapRange_apply

/-- **A free `𝒪_F`-module on an algebraic space is cartesian on affine charts.**  This is the
base case of Descent, Proposition 03DX(2): the two terms of a global presentation are
coproducts of copies of `𝒪_F`, and the criterion holds for them with no cohomological input. -/
theorem isCartesianOnAffineCharts_free (I : Type u) :
    IsCartesianOnAffineCharts (SheafOfModules.free
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) I) :=
  fun _ _ hU hV f => bijective_sectionsBaseChange_free I f hU hV

/-- **A module exhibited as a coproduct of copies of `𝒪_F` is cartesian on affine charts.**
This is `AlgebraicGeometry.Space.isCartesianOnAffineCharts_free` transported along the canonical
isomorphism with `SheafOfModules.free I`, and it is the shape in which
`SheafOfModules.HasGlobalPresentation` presents the two terms of a presentation: a cofan with
point `P` whose legs come from the unit module, together with the assertion that it is a
colimit. -/
theorem isCartesianOnAffineCharts_of_isColimit_cofan {I : Type u}
    {P : Modules.{u, u} B S hS F hF}
    (ι : ∀ _ : I, SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) ⟶ P)
    (hP : IsColimit (Cofan.mk P ι)) :
    IsCartesianOnAffineCharts P :=
  IsCartesianOnAffineCharts.of_iso
    (IsColimit.coconePointUniqueUpToIso
      (isColimitFreeCofan
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) I) hP)
    (isCartesianOnAffineCharts_free I)

/-- **A presented `𝒪_F`-module is cartesian on affine charts, granted that its presentation is
exact on the sections over affine charts.**

Let `a : Q ⟶ P` be a morphism of coproducts of copies of `𝒪_F` and let `b : P ⟶ G` exhibit `G`
as its cokernel on the sections over every affine étale chart, that is: `b` is surjective there
with kernel the image of `a`.  Then `G` is cartesian on affine charts.

The two sections-level hypotheses are the cohomological content of Descent,
Proposition 03DX(2): a cokernel of sheaves of modules is the sheafification of the objectwise
cokernel, so they do not follow from `b` being a cokernel of `a`.  Everything else is
discharged — `AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isColimit_cofan` for the two
free terms and `AlgebraicGeometry.Space.isCartesianOnAffineCharts_cokernel` for the passage to
`G`. -/
theorem isCartesianOnAffineCharts_of_presentation {I K : Type u}
    {P Q G : Modules.{u, u} B S hS F hF}
    (ιP : ∀ _ : I, SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) ⟶ P)
    (hP : IsColimit (Cofan.mk P ιP))
    (ιQ : ∀ _ : K, SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) ⟶ Q)
    (hQ : IsColimit (Cofan.mk Q ιQ)) (a : Q ⟶ P) (b : P ⟶ G)
    (hb : ∀ U : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
        Function.Surjective (b.val.app (op U)))
    (hex : ∀ U : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
        Function.Exact (a.val.app (op U)) (b.val.app (op U))) :
    IsCartesianOnAffineCharts G :=
  isCartesianOnAffineCharts_cokernel a b hb hex
    (isCartesianOnAffineCharts_of_isColimit_cofan ιQ hQ)
    (isCartesianOnAffineCharts_of_isColimit_cofan ιP hP)

end AlgebraicGeometry.Space

end
