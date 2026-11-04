module

public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import StacksFrontier.AlgebraicGeometry.AffineQcohEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAffineComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleAffineBaseChange
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.Over
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredColimits.SectionsOverAQuasiCompactOpen

/-!
# A free module on the slice at an affine chart is an `Mᵃ`

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `Y` be an
étale chart of `F` whose underlying scheme `U = chartScheme Y` is **affine**, and let
`I` be a type.  The slice of the small étale site of `F` at `Y` carries two kinds of module:
the free module `SheafOfModules.free I` over the restricted structure sheaf
`AlgebraicGeometry.Space.SmallEtale.sliceRingSheaf`, and the module `Mᵃ` of Tag 03DU of a
quasi-coherent `𝒪_U`-module `M`
(`AlgebraicGeometry.Space.SmallEtale.sliceAssociatedModule`).

This file proves that **the first is one of the second**: `SheafOfModules.free I` is isomorphic
to `(⊕_I 𝒪_U)ᵃ`.  That is the step of the proof of Descent, Proposition 03DX(2) which the source
dispatches with "this is clear for the direct sums", and it is the base case of Tag 03DV: the
two terms of a global presentation are coproducts of copies of the structure sheaf, and for them
essential surjectivity of `(-)ᵃ` is immediate.

The statement proved is the **free instance** of the essential-surjectivity hypothesis `hEss`
carried by
`AlgebraicGeometry.Space.SmallEtale.isCartesianOnAffineCharts_of_isQuasicoherentOnSite_of_essSurj`
— that is, the conclusion of that `hEss` for the particular module `SheafOfModules.free I` — and
not the hypothesis itself, which quantifies over every quasi-coherent module of the slice.

It is *not* directly the conclusion of the differently-shaped `hEss` of
`AlgebraicGeometry.Space.SmallEtale.isCartesianOnAffineCharts_of_essSurj`, which fixes its module
as the restriction `AlgebraicGeometry.Space.SmallEtale.sliceModule` of a given `𝒪_F`-module and
so has no slot at which to put a free module of the slice.  Reaching that one additionally needs
`AlgebraicGeometry.Space.SmallEtale.freeSliceIso` of
`StacksFrontier.AlgebraicGeometry.Spaces.FreeSliceQuasicoherent`, which identifies the free module of
the slice with the restriction of the free `𝒪_F`-module.

## Main definitions

* `Stacks.Sites.sectionsOfCone`: a section of a presheaf restricted along a functor `G`,
  obtained from an element of the presheaf at an object receiving a cone of maps from the image
  of `G` — in practice a terminal object of the target category.
* `AlgebraicGeometry.Space.SmallEtale.sliceToTop`: the structure morphism of a chart over `Y`,
  read as a morphism of schemes over `U` into the terminal object `CategoryTheory.Over.mk (𝟙 U)`.
* `AlgebraicGeometry.Space.SmallEtale.sliceAssociatedSection`: the global section of `Mᵃ` on the
  slice at `Y` determined by a global section of the pullback of `M` along the identity of `U`.
* `AlgebraicGeometry.Space.SmallEtale.freeSliceComparison`: **the comparison morphism**
  `SheafOfModules.free I ⟶ Mᵃ` attached to an `I`-indexed family of such global sections.
* `AlgebraicGeometry.Space.SmallEtale.chartFreeModule`: the free `𝒪_U`-module on `I`.
* `AlgebraicGeometry.Space.SmallEtale.chartFreeSectionsEquiv`: its global sections, after
  pullback along the identity of `U`, identified with the finitely supported `I`-indexed
  families of regular functions on `U`.

## Main results

* `Stacks.AlgebraicGeometry.SectionsBaseChange.bijective_of_single`: **the algebraic core.**  An
  additive map out of the finitely supported families which sends `Finsupp.single i r` to
  `r • e (1 ⊗ 𝑏ᵢ)`, for `e` a bijective extension-of-scalars comparison and `𝑏` the image of a
  basis, is bijective.
* `Stacks.SheafOfModules.freeHomEquiv_symm_val_app_freeSectionsMap_single`: the sections map of a
  morphism out of a free module sends the comparison image of `Finsupp.single i r` to
  `r •` the `i`-th of the defining sections.
* `AlgebraicGeometry.Space.SmallEtale.bijective_freeSliceComparison_app`: **the comparison
  morphism is bijective on the sections over every affine chart over `Y`.**
* `AlgebraicGeometry.Space.SmallEtale.isIso_freeSliceComparison`: hence it is an isomorphism.
* `AlgebraicGeometry.Space.SmallEtale.exists_sliceAssociatedModule_iso_free_of_linearEquiv`: a
  free module on the slice is `M₀ᵃ` for any quasi-coherent `M₀` whose global sections are free.
* `AlgebraicGeometry.Space.SmallEtale.exists_sliceAssociatedModule_iso_free` and
  `AlgebraicGeometry.Space.SmallEtale.exists_sliceAssociatedModule_iso_free_of_h03DT`: **the free
  instance of the conclusion of `hEss`**, with the sheaf condition of Tag 03DT taken in the two
  spellings the tree uses for it.

## Implementation notes

The proof is the commuting square of the two computations of the sections over an affine chart
`Z` over `Y`:

* on the free side, `Stacks.Sites.bijective_freeSectionsMap` computes the sections of
  `SheafOfModules.free I` over a quasi-compact object of any site as the finitely supported
  families of sections of the structure sheaf.  Quasi-compactness of `Z` as an object of the
  *localized* topology comes from
  `CategoryTheory.GrothendieckTopology.isQuasiCompactObject_over` applied to
  `AlgebraicGeometry.Space.isQuasiCompactObject_of_isAffine`;
* on the associated-module side, `Stacks.Sites.affineAssociatedBaseChangeIso` identifies the
  sections of `Mᵃ` over `Z` with the base change along `Γ(U, 𝒪) → Γ(Z, 𝒪)` of its sections over
  the terminal object of the slice.

Affineness of `U` — that is, of the chart `Y` — is used in **two** places: at
`Stacks.Sites.affineAssociatedBaseChangeIso` just mentioned, and inside
`AlgebraicGeometry.Space.SmallEtale.chartFreeSectionsEquiv`, where it makes `U` a compact space
and so makes `⊤` a quasi-compact object of the Zariski site of `U`.  Affineness of `Z` is needed
independently of the quasi-compactness it also supplies.

The square is checked on `Finsupp.single i r`, where both sides are `r •` the restriction of the
`i`-th tautological section, which is the normalisation
`Stacks.Sites.affineAssociatedBaseChangeIso_hom_one_tmul` on one side and
`Stacks.SheafOfModules.freeHomEquiv_symm_val_app_freeSectionsMap_single` on the other.  Passing
from the square to bijectivity happens at abstract types, in
`Stacks.AlgebraicGeometry.SectionsBaseChange.bijective_of_single`, for the reason recorded in the
implementation notes of `StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleEssSurj`: the
`ModuleCat.extendScalars` spelling of a base change and the
`LinearMap.liftBaseChange` spelling are definitionally equal but the check identifying them
exhausts the elaborator's recursion budget at these concrete sheaf-section types.  That lemma is
therefore stated with both spellings in its type and proved once, where the identification is
cheap; it reuses
`Stacks.AlgebraicGeometry.SectionsBaseChange.bijective_liftBaseChange_of_bijective_extendScalars`
and `..._of_linearEquiv`, and `ModuleCat.extendRestrictScalarsAdj` supplies the
semilinear map `m ↦ e (1 ⊗ m)` without any explicit tensor manipulation.

`Stacks.Sites.sectionsOfCone` takes the cone of maps `G.obj c ⟶ d₀` and its compatibility as
data rather than an `CategoryTheory.Limits.IsTerminal d₀`: with `CategoryTheory.Over.mkIdTerminal`
supplied instead, the component formula
`AlgebraicGeometry.Space.SmallEtale.sliceAssociatedSection_val` does not elaborate, the unifier
unfolding `CategoryTheory.Limits.IsTerminal.from` through the limit machinery (a heartbeat
timeout at `whnf`).  With the explicit `AlgebraicGeometry.Space.SmallEtale.sliceToTop`
the same formula is a composite of two `rfl`s at abstract types.  For the same reason the
proof obligation inside `CategoryTheory.Over.homMk` is discharged by
`CategoryTheory.Category.comp_id` as a term and not by `simp`.

What is proved is not Tag 03DV, which asserts that `Mᵃ` is a quasi-coherent module on the site
for *every* quasi-coherent `M`: it is its free case, read through the essential-surjectivity
clause of Tag 03DX(2) rather than through quasi-coherence of `Mᵃ`.  Beyond the free case the
source needs Tag 0GN7 to descend the presenting map, right exactness of `(-)ᵃ`, and Tag 023T to
descend along a covering.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 090H](https://stacks.math.columbia.edu/tag/090H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace SheafOfModules
open scoped ChangeOfRings

universe w v u v' u'

/-! ### Sections of a restricted presheaf from a cone -/

namespace Stacks.Sites

/-- **A section of a presheaf restricted along a functor, from a value at a cone vertex.**  Given
`G : C ⥤ D`, a presheaf `P` on `D`, an object `d₀` of `D` and maps `π c : G.obj c ⟶ d₀`
compatible with the morphisms of `C`, an element of `P` at `d₀` restricts to a section of
`G.op ⋙ P`.

The intended `d₀` is a terminal object of `D`, with `π` its unique maps; the cone is taken as
data because the universal property, supplied through
`CategoryTheory.Limits.IsTerminal.from`, makes the resulting component formula inelaborable. -/
def sectionsOfCone {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (G : C ⥤ D) (P : Dᵒᵖ ⥤ Type w) (d₀ : D) (π : ∀ c : C, G.obj c ⟶ d₀)
    (hπ : ∀ {c c' : C} (f : c' ⟶ c), G.map f ≫ π c = π c') (x : P.obj (op d₀)) :
    (G.op ⋙ P).sections where
  val c := P.map (π c.unop).op x
  property {c c'} f := by
    dsimp
    rw [← types_comp_apply (P.map _) (P.map _), ← P.map_comp]
    exact congrArg (fun g => P.map g x) (congrArg Quiver.Hom.op (hπ f.unop))

end Stacks.Sites

/-! ### The free comparison, at abstract types -/

namespace Stacks.AlgebraicGeometry.SectionsBaseChange

/-- **A map out of the finitely supported families prescribed on `Finsupp.single` by a bijective
base change comparison is bijective.**

Let `φ : A →+* Rv` be a ring map, let `e` be a bijective comparison
`Rv ⊗_A N ⟶ N'` in the `ModuleCat.extendScalars` form, and let `θ` identify `N`
with the finitely supported `I`-indexed families of elements of `A`.  Then any additive map
`ψ : (I →₀ Rv) → N'` with `ψ (Finsupp.single i r) = r • e (1 ⊗ θ (Finsupp.single i 1))` is
bijective.

This is the form in which a sheaf-section computation uses an affine base change isomorphism.
Both spellings of the base change occur in the statement — the extension-of-scalars one in `e`
and the finitely supported one in `ψ` — so the identification of the two scalar structures is
performed once here, at abstract types, where it is cheap; see the implementation notes. -/
theorem bijective_of_single {A Rv N N' : Type u} [CommRing A] [CommRing Rv]
    [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module Rv N'] (φ : A →+* Rv)
    (e : (ModuleCat.extendScalars φ).obj (ModuleCat.of A N) ⟶ ModuleCat.of Rv N')
    (hbij : Function.Bijective e) {I : Type u} (θ : (I →₀ A) ≃ₗ[A] N)
    (ψ : (I →₀ Rv) → N') (hadd : ∀ p q, ψ (p + q) = ψ p + ψ q)
    (hsingle : ∀ (i : I) (r : Rv),
      ψ (Finsupp.single i r) = r • e ((1 : Rv) ⊗ₜ[A,φ] θ (Finsupp.single i 1))) :
    Function.Bijective ψ := by
  classical
  let _ := φ.toAlgebra
  let _ := Module.compHom N' φ
  have _ : IsScalarTower A Rv N' := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let ρ : N →ₗ[A] N' :=
    ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv (ModuleCat.of A N)
      (ModuleCat.of Rv N') e).hom
  have hρe : ∀ m : N, e ((1 : Rv) ⊗ₜ[A,φ] m) = ρ m := fun m =>
    (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply e m).symm
  have hρ : Function.Bijective (ρ.liftBaseChange Rv) :=
    bijective_liftBaseChange_of_bijective_extendScalars φ e hbij ρ hρe
  let σ : (I →₀ A) →ₗ[A] N' := ρ ∘ₗ (θ : (I →₀ A) →ₗ[A] N)
  have hσ : Function.Bijective (σ.liftBaseChange Rv) :=
    bijective_liftBaseChange_of_linearEquiv σ ρ θ (LinearEquiv.refl Rv N') (fun _ => rfl) hρ
  have hfun : ∀ p,
      ψ p = (σ.liftBaseChange Rv) ((TensorProduct.finsuppScalarRight A Rv Rv I).symm p) := by
    intro p
    refine DFunLike.congr_fun (Finsupp.addHom_ext (f := AddMonoidHom.mk' ψ hadd)
      (g := (σ.liftBaseChange Rv).toAddMonoidHom.comp
        (TensorProduct.finsuppScalarRight A Rv Rv I).symm.toAddMonoidHom) ?_) p
    intro i r
    show ψ (Finsupp.single i r) =
      (σ.liftBaseChange Rv) ((TensorProduct.finsuppScalarRight A Rv Rv I).symm
        (Finsupp.single i r))
    rw [hsingle i r, TensorProduct.finsuppScalarRight_symm_apply_single,
      LinearMap.liftBaseChange_tmul, hρe]
    rfl
  rw [show ψ = _ from funext hfun]
  exact hσ.comp (TensorProduct.finsuppScalarRight A Rv Rv I).symm.bijective

end Stacks.AlgebraicGeometry.SectionsBaseChange

/-! ### The pullback-sections presheaf, read in the underlying types -/

namespace AlgebraicGeometry

/-- The restriction map of the presheaf of Tag 03DS, read in the underlying types, is the
pullback map on global sections.  Stated at an abstract morphism of schemes over `S` so that the
unfolding of `AlgebraicGeometry.quasiCoherentPresheafConstruction` happens once; the restriction
of this presheaf to a site is `Stacks.Sites.associatedPresheaf`, whose own version of this
statement is `Stacks.Sites.associatedPresheaf_map_apply` and applies only to morphisms coming
from the site. -/
theorem quasiCoherentPresheafFunctor_forget_map (S : Scheme.{u}) (M : S.Modules)
    [M.IsQuasicoherent] {X Y : Over S} (h : X ⟶ Y)
    (x : Γ((Scheme.Modules.pullback Y.hom).obj M, ⊤)) :
    (quasiCoherentPresheafFunctor S M ⋙ CategoryTheory.forget AddCommGrpCat.{u}).map h.op x =
      pullbackSectionsMap M h x := rfl

end AlgebraicGeometry

/-! ### The sections map of a morphism out of a free sheaf of modules -/

namespace Stacks.SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The sections map of a morphism out of a free module, on the comparison image of
`Finsupp.single`.**  The morphism `SheafOfModules.free I ⟶ N` attached to a family
`s : I → N.sections` carries the image of `Finsupp.single i r` under
`Stacks.Sites.freeSectionsMap` to `r •` the value of `s i` over the object.

Only the `r = 1` case is content — it is
`SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection` — and the general case
follows because both maps are semilinear and `Finsupp.single i r = r • Finsupp.single i 1`. -/
theorem freeHomEquiv_symm_val_app_freeSectionsMap_single (N : _root_.SheafOfModules.{u} R)
    {I : Type u} (s : I → N.sections) (X : Cᵒᵖ) (i : I) (r : R.obj.obj X) :
    (((freeHomEquiv N).symm s).val.app X).hom
        ((Stacks.Sites.freeSectionsMap (R := R) I X).hom (Finsupp.single i r)) =
      r • PresheafOfModules.sections.eval (s i) X := by
  have hs : Finsupp.single i r = r • Finsupp.single i (1 : R.obj.obj X) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hs, map_smul, map_smul]
  congr 1
  rw [Stacks.Sites.freeSectionsMap_single]
  exact congrArg (fun t : N.sections => PresheafOfModules.sections.eval t X)
    (_root_.SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection (R := R) s i)

end Stacks.SheafOfModules

/-! ### The comparison morphism on the slice at a chart -/

namespace AlgebraicGeometry.Space.SmallEtale

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (Y : SmallEtale B S hS F)

/-- The structure morphism of a chart over `Y`, read as a morphism of schemes over the chart's
scheme `U` into the terminal object `CategoryTheory.Over.mk (𝟙 U)` of that slice. -/
def sliceToTop (Z : Over Y) :
    (sliceToOver B S hS F Y).obj Z ⟶ Over.mk (𝟙 (chartScheme Y)) :=
  Over.homMk ((sliceToOver B S hS F Y).obj Z).hom (Category.comp_id _)

/-- The maps of `AlgebraicGeometry.Space.SmallEtale.sliceToTop` form a cone: they are compatible
with the morphisms of the slice at `Y`, by the commuting triangle of a morphism over `Y`. -/
theorem sliceToOver_map_comp_sliceToTop {Z Z' : Over Y} (f : Z' ⟶ Z) :
    (sliceToOver B S hS F Y).map f ≫ sliceToTop B S hS F Y Z = sliceToTop B S hS F Y Z' :=
  Over.OverMorphism.ext (Over.w ((sliceToOver B S hS F Y).map f))

variable (M₀ : (chartScheme Y).Modules) [M₀.IsQuasicoherent]
    (hM₀ : Presheaf.IsSheaf ((topology B S hS F).over Y)
      (Stacks.Sites.associatedPresheaf (chartScheme Y) M₀ (sliceToOver B S hS F Y)))

/-- **A global section of `Mᵃ` on the slice at `Y` from a global section over the chart.**  An
element of the global sections of the pullback of `M₀` along the identity of the chart's scheme
restricts, over each chart `Z` over `Y`, to a section of `Mᵃ` over `Z`, compatibly with the
morphisms of the slice. -/
noncomputable def sliceAssociatedSection
    (x : Γ((Scheme.Modules.pullback (𝟙 (chartScheme Y))).obj M₀, ⊤)) :
    (sliceAssociatedModule B S hS F hF Y M₀ hM₀).sections :=
  Stacks.Sites.sectionsOfCone (sliceToOver B S hS F Y)
    (quasiCoherentPresheafFunctor (chartScheme Y) M₀ ⋙
      CategoryTheory.forget AddCommGrpCat.{u}) (Over.mk (𝟙 (chartScheme Y)))
    (sliceToTop B S hS F Y) (sliceToOver_map_comp_sliceToTop B S hS F Y) x

/-- The component over a chart `Z` of
`AlgebraicGeometry.Space.SmallEtale.sliceAssociatedSection` is the pullback map on global
sections of Tag 03DS along the structure morphism of `Z`. -/
theorem sliceAssociatedSection_val
    (x : Γ((Scheme.Modules.pullback (𝟙 (chartScheme Y))).obj M₀, ⊤)) (Z : Over Y) :
    PresheafOfModules.sections.eval (sliceAssociatedSection B S hS F hF Y M₀ hM₀ x) (op Z) =
      pullbackSectionsMap M₀ (sliceToTop B S hS F Y Z) x :=
  quasiCoherentPresheafFunctor_forget_map (chartScheme Y) M₀
    (sliceToTop B S hS F Y Z) x

/-- **The comparison morphism `SheafOfModules.free I ⟶ Mᵃ` on the slice at `Y`** attached to an
`I`-indexed family of global sections of the pullback of `M₀` along the identity of the chart's
scheme.  It is the morphism out of a coproduct of copies of the structure sheaf determined by the
corresponding family of global sections of `Mᵃ`. -/
noncomputable def freeSliceComparison (I : Type u)
    (t : I → Γ((Scheme.Modules.pullback (𝟙 (chartScheme Y))).obj M₀, ⊤)) :
    SheafOfModules.free (R := sliceRingSheaf B S hS F hF Y) I ⟶
      sliceAssociatedModule B S hS F hF Y M₀ hM₀ :=
  (SheafOfModules.freeHomEquiv _).symm
    (fun i => sliceAssociatedSection B S hS F hF Y M₀ hM₀ (t i))

/-- The comparison morphism sends the image of `Finsupp.single i r` under
`Stacks.Sites.freeSectionsMap` to `r •` the restriction of the `i`-th given global section. -/
theorem freeSliceComparison_app_freeSectionsMap_single (I : Type u)
    (t : I → Γ((Scheme.Modules.pullback (𝟙 (chartScheme Y))).obj M₀, ⊤))
    (Z : Over Y) (i : I) (r : Γ(((sliceToOver B S hS F Y).obj Z).left, ⊤)) :
    ((freeSliceComparison B S hS F hF Y M₀ hM₀ I t).val.app (op Z)).hom
        ((Stacks.Sites.freeSectionsMap
          (R := sliceRingSheaf B S hS F hF Y) I (op Z)).hom (Finsupp.single i r)) =
      r • pullbackSectionsMap M₀ (sliceToTop B S hS F Y Z) (t i) :=
  (Stacks.SheafOfModules.freeHomEquiv_symm_val_app_freeSectionsMap_single
      (sliceAssociatedModule B S hS F hF Y M₀ hM₀)
      (fun i => sliceAssociatedSection B S hS F hF Y M₀ hM₀ (t i)) (op Z) i r).trans
    (congrArg
      (fun y : Γ((Scheme.Modules.pullback ((sliceToOver B S hS F Y).obj Z).hom).obj M₀, ⊤) =>
        r • y)
      (sliceAssociatedSection_val B S hS F hF Y M₀ hM₀ (t i) Z))

/-- **The comparison morphism is bijective on the sections over every affine chart over an affine
chart `Y`.**

Both sides are computed as the finitely supported `I`-indexed families of regular functions on
`Z`: the free module by `Stacks.Sites.bijective_freeSectionsMap`, since `Z` is a quasi-compact
object of the localized topology, and `Mᵃ` by `Stacks.Sites.affineAssociatedBaseChangeIso` from
its sections over the terminal object of the slice, which `θ` identifies with the finitely
supported families on `Y`.  The square commutes on `Finsupp.single i r`, where both sides are
`r •` the restriction of the `i`-th given section. -/
theorem bijective_freeSliceComparison_app (hY : IsAffine (chartScheme Y)) (I : Type u)
    (θ : (I →₀ Γ(chartScheme Y, ⊤)) ≃ₗ[Γ(chartScheme Y, ⊤)]
      Γ((Scheme.Modules.pullback (𝟙 (chartScheme Y))).obj M₀, ⊤))
    (Z : Over Y) (hZ : IsAffine (chartScheme Z.left)) :
    Function.Bijective
      ((freeSliceComparison B S hS F hF Y M₀ hM₀ I
        (fun i => θ (Finsupp.single i 1))).val.app (op Z)).hom := by
  have hU : IsAffine (Over.mk (𝟙 (chartScheme Y))).left := hY
  have hV : IsAffine ((sliceToOver B S hS F Y).obj Z).left := hZ
  have hle : (⊤ : ((sliceToOver B S hS F Y).obj Z).left.Opens) ≤
      (sliceToTop B S hS F Y Z).left ⁻¹ᵁ
        (⊤ : (Over.mk (𝟙 (chartScheme Y))).left.Opens) := by simp
  have hfs : Function.Bijective
      (Stacks.Sites.freeSectionsMap (R := sliceRingSheaf B S hS F hF Y) I (op Z)).hom :=
    Stacks.Sites.bijective_freeSectionsMap I Z
      (GrothendieckTopology.isQuasiCompactObject_over _ Z
        (isQuasiCompactObject_of_isAffine B S hS F Z.left hZ))
  have hψ : Function.Bijective (fun p =>
      ((freeSliceComparison B S hS F hF Y M₀ hM₀ I
          (fun i => θ (Finsupp.single i 1))).val.app (op Z)).hom
        ((Stacks.Sites.freeSectionsMap
          (R := sliceRingSheaf B S hS F hF Y) I (op Z)).hom p)) := by
    refine Stacks.AlgebraicGeometry.SectionsBaseChange.bijective_of_single
      ((sliceToTop B S hS F Y Z).left.appLE ⊤ ⊤ hle).hom
      (Stacks.Sites.affineAssociatedBaseChangeIso M₀ (sliceToTop B S hS F Y Z) hle).hom
      (Stacks.Sites.bijective_affineAssociatedBaseChangeIso_hom M₀
        (sliceToTop B S hS F Y Z) hle) θ _ (fun p q => ?_) (fun i r => ?_)
    · exact (congrArg (fun y => ((freeSliceComparison B S hS F hF Y M₀ hM₀ I
          (fun i => θ (Finsupp.single i 1))).val.app (op Z)).hom y)
        (map_add (Stacks.Sites.freeSectionsMap
          (R := sliceRingSheaf B S hS F hF Y) I (op Z)).hom p q)).trans
        (map_add _ _ _)
    · rw [Stacks.Sites.affineAssociatedBaseChangeIso_hom_one_tmul M₀
        (sliceToTop B S hS F Y Z) hle (θ (Finsupp.single i 1))]
      exact freeSliceComparison_app_freeSectionsMap_single B S hS F hF Y M₀ hM₀ I
        (fun i => θ (Finsupp.single i 1)) Z i r
  exact (Function.Bijective.of_comp_iff _ hfs).1 hψ

include hF in
/-- **The comparison morphism is an isomorphism.**  It is bijective over the affine charts over
`Y`, which cover, so it is locally bijective and hence invertible by
`AlgebraicGeometry.Space.SmallEtale.isIso_of_bijective_app_of_isAffine`. -/
theorem isIso_freeSliceComparison (hY : IsAffine (chartScheme Y)) (I : Type u)
    (θ : (I →₀ Γ(chartScheme Y, ⊤)) ≃ₗ[Γ(chartScheme Y, ⊤)]
      Γ((Scheme.Modules.pullback (𝟙 (chartScheme Y))).obj M₀, ⊤)) :
    IsIso (freeSliceComparison B S hS F hF Y M₀ hM₀ I (fun i => θ (Finsupp.single i 1))) :=
  isIso_of_bijective_app_of_isAffine B S hS F hF Y _
    (fun Z hZ => bijective_freeSliceComparison_app B S hS F hF Y M₀ hM₀ hY I θ Z hZ)

include hF hM₀ in
/-- **A free module on the slice at an affine chart is an `Mᵃ`, given a module whose global
sections are free.**  If `M₀` is a quasi-coherent module on the scheme underlying the affine
chart `Y` whose global sections, pulled back along the identity, are the finitely supported
`I`-indexed families of regular functions, then `SheafOfModules.free I` on the slice at `Y` is
isomorphic to `M₀ᵃ`.

This is the conclusion of the essential-surjectivity hypothesis `hEss` of
`AlgebraicGeometry.Space.SmallEtale.isCartesianOnAffineCharts_of_isQuasicoherentOnSite_of_essSurj`
at the module `SheafOfModules.free I`. -/
theorem exists_sliceAssociatedModule_iso_free_of_linearEquiv
    (hY : IsAffine (chartScheme Y)) (I : Type u)
    (θ : (I →₀ Γ(chartScheme Y, ⊤)) ≃ₗ[Γ(chartScheme Y, ⊤)]
      Γ((Scheme.Modules.pullback (𝟙 (chartScheme Y))).obj M₀, ⊤)) :
    ∃ (M : (chartScheme Y).Modules) (_ : M.IsQuasicoherent)
      (hM : Presheaf.IsSheaf ((topology B S hS F).over Y)
        (Stacks.Sites.associatedPresheaf (chartScheme Y) M (sliceToOver B S hS F Y))),
      Nonempty (SheafOfModules.free (R := sliceRingSheaf B S hS F hF Y) I ≅
        sliceAssociatedModule B S hS F hF Y M hM) :=
  have := isIso_freeSliceComparison B S hS F hF Y M₀ hM₀ hY I θ
  ⟨M₀, inferInstance, hM₀, ⟨asIso (freeSliceComparison B S hS F hF Y M₀ hM₀ I
    (fun i => θ (Finsupp.single i 1)))⟩⟩

end AlgebraicGeometry.Space.SmallEtale

/-! ### The free module on the chart's scheme -/

namespace AlgebraicGeometry.Space.SmallEtale

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (Y : SmallEtale B S hS F)

/-- The free `𝒪_U`-module on a type `I`, for `U` the scheme underlying the chart `Y`: the
coproduct of `I` copies of the structure sheaf, read as an object of
`AlgebraicGeometry.Scheme.Modules`. -/
noncomputable def chartFreeModule (I : Type u) : (chartScheme Y).Modules :=
  SheafOfModules.free (R := (chartScheme Y).ringCatSheaf) I

/-- A free module on the chart's scheme is quasi-coherent, being a coproduct of copies of the
structure sheaf.  This is
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free`. -/
theorem isQuasicoherent_chartFreeModule (I : Type u) :
    (chartFreeModule B S hS F Y I).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free I

/-- **The global sections of the free `𝒪_U`-module over an affine chart are the finitely
supported families of regular functions**, after pullback along the identity of `U`.

The computation is `Stacks.Sites.bijective_freeSectionsMap` at the top open of the Zariski site
of `U`, which is a quasi-compact object because an affine scheme is a compact space
(`Stacks.Cohomology.Sections.isQuasiCompactObject_of_isCompact`), followed by the identification
of a module with its pullback along an identity. -/
noncomputable def chartFreeSectionsEquiv (hY : IsAffine (chartScheme Y)) (I : Type u) :
    (I →₀ Γ(chartScheme Y, ⊤)) ≃ₗ[Γ(chartScheme Y, ⊤)]
      Γ((Scheme.Modules.pullback (𝟙 (chartScheme Y))).obj
        (chartFreeModule B S hS F Y I), ⊤) :=
  (LinearEquiv.ofBijective (Stacks.Sites.freeSectionsMap
      (R := (chartScheme Y).ringCatSheaf) I (op ⊤)).hom
    (Stacks.Sites.bijective_freeSectionsMap I ⊤
      (Stacks.Cohomology.Sections.isQuasiCompactObject_of_isCompact ⊤ (by
        have h : IsCompact (Set.univ : Set ↥(chartScheme Y)) :=
          CompactSpace.isCompact_univ
        simpa using h)))) ≪≫ₗ
    sectionsLinearEquivOfIso ((Scheme.Modules.pullbackId (chartScheme Y)).app
      (chartFreeModule B S hS F Y I)).symm ⊤

include hF in
/-- **A free module on the slice of the small étale site at an affine chart is the module `Mᵃ` of
Tag 03DU of the free module on the chart's scheme** — the free case of the step of the proof of
Descent, Proposition 03DX(2) that the source dispatches with "this is clear for the direct sums".

It is not Tag 03DV, which asserts quasi-coherence of `Mᵃ` for every quasi-coherent `M` and is on
the other side of the equivalence.

The hypothesis `hsh` is the sheaf condition for the presheaf of pullback sections of Tag 03DS on
the slice, which is what `AlgebraicGeometry.Space.SmallEtale.sliceAssociatedModule` takes as a
parameter; it is Tag 03DT, in the spelling `Stacks.Sites.faithful_associatedSheafFunctor` carries
— the sheaf condition for the associated presheaf, with the quasi-coherence binder made explicit
rather than instance-implicit — and
`AlgebraicGeometry.Space.SmallEtale.exists_sliceAssociatedModule_iso_free_of_h03DT` below
supplies it from Tag 03DT itself.

The conclusion is the conclusion of the essential-surjectivity hypothesis `hEss` of
`AlgebraicGeometry.Space.SmallEtale.isCartesianOnAffineCharts_of_isQuasicoherentOnSite_of_essSurj`
at the module `SheafOfModules.free I`, verbatim.  It is *not* that hypothesis, which quantifies
over every quasi-coherent module of the slice, and it is not the conclusion of the
differently-shaped `hEss` of
`AlgebraicGeometry.Space.SmallEtale.isCartesianOnAffineCharts_of_essSurj`; see the module
docstring. -/
theorem exists_sliceAssociatedModule_iso_free (hY : IsAffine (chartScheme Y))
    (I : Type u)
    (hsh : ∀ (M : (chartScheme Y).Modules) (_ : M.IsQuasicoherent),
      Presheaf.IsSheaf ((topology B S hS F).over Y)
        (Stacks.Sites.associatedPresheaf (chartScheme Y) M
          (sliceToOver B S hS F Y))) :
    ∃ (M : (chartScheme Y).Modules) (_ : M.IsQuasicoherent)
      (hM : Presheaf.IsSheaf ((topology B S hS F).over Y)
        (Stacks.Sites.associatedPresheaf (chartScheme Y) M (sliceToOver B S hS F Y))),
      Nonempty (SheafOfModules.free (R := sliceRingSheaf B S hS F hF Y) I ≅
        sliceAssociatedModule B S hS F hF Y M hM) :=
  have hq := isQuasicoherent_chartFreeModule B S hS F Y I
  exists_sliceAssociatedModule_iso_free_of_linearEquiv B S hS F hF Y
    (chartFreeModule B S hS F Y I) (hsh (chartFreeModule B S hS F Y I) hq) hY I
    (chartFreeSectionsEquiv B S hS F Y hY I)

include hF in
/-- **The same statement with the sheaf condition taken as Tag 03DT**, in the spelling the tree
carries as `h03DT`: the fpqc sheaf condition in the underlying types for the presheaf of Tag 03DS
on the schemes over the chart's scheme.  The passage to the slice is
`AlgebraicGeometry.Space.SmallEtale.isSheaf_sliceAssociatedPresheaf`. -/
theorem exists_sliceAssociatedModule_iso_free_of_h03DT
    (hY : IsAffine (chartScheme Y)) (I : Type u)
    (h03DT : ∀ (M : (chartScheme Y).Modules) (_ : M.IsQuasicoherent),
      Presieve.IsSheaf (Scheme.fpqcTopology.{u}.over (chartScheme Y))
        (quasiCoherentPresheafFunctor (chartScheme Y) M ⋙
          CategoryTheory.forget AddCommGrpCat.{u})) :
    ∃ (M : (chartScheme Y).Modules) (_ : M.IsQuasicoherent)
      (hM : Presheaf.IsSheaf ((topology B S hS F).over Y)
        (Stacks.Sites.associatedPresheaf (chartScheme Y) M (sliceToOver B S hS F Y))),
      Nonempty (SheafOfModules.free (R := sliceRingSheaf B S hS F hF Y) I ≅
        sliceAssociatedModule B S hS F hF Y M hM) :=
  exists_sliceAssociatedModule_iso_free B S hS F hF Y hY I
    (fun M hM => isSheaf_sliceAssociatedPresheaf B S hS F Y M (h03DT M hM))

end AlgebraicGeometry.Space.SmallEtale

end
