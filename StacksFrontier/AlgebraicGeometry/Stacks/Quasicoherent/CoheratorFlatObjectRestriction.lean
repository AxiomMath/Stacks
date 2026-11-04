module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorSmallEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedFlatFppfRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeProperty

/-!
# The coherator on the small étale site of a flat object, at the sheaf level (Stacks 0GQK)

Let `𝒳` be an algebraic stack, `Q : Mod(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)` a right adjoint of the inclusion of
the quasi-coherent modules (the coherator of **Stacks 0778** and **Stacks 0781**), and `x` an
object of `𝒳` lying over a scheme `U` with `x : U → 𝒳` flat. **Stacks 0GQK** says that for `𝓕` in
`LQCoh^fbc(𝒪_𝒳)` one has `Q(𝓕)|_{U_étale} = 𝓕|_{U_étale}`; the identification is the restriction
of the counit `ε_𝓕 : Q(𝓕) ⟶ 𝓕`.

The source's proof: the kernel and the cokernel of `ε_𝓕` are parasitic (**Stacks 0779** (2)).
The step it leaves implicit is that a map of sheaves of modules whose kernel and cokernel —
taken in `Mod(𝒪_𝒳)`, so that the cokernel is a sheafified cokernel — are parasitic restricts to
an isomorphism on the small étale site of a flat object. That is proved here: restriction to the
flat-fppf site is exact (`AlgebraicGeometry.Stack.FlatFppf.moduleRestriction_exact`) and kills
exactly the parasitic modules
(`AlgebraicGeometry.Stack.FlatFppf.isParasitic_iff_isZero_moduleRestriction`), so it carries the
map to an isomorphism; the sections at a flat object are unchanged by that restriction, and the
small étale site of `U` only sees flat objects
(`AlgebraicGeometry.Stack.flatObject_smallEtaleToStack_obj`).

## Main results

* `AlgebraicGeometry.Stack.isIso_app_of_isParasitic_kernel_cokernel`: a map of sheaves of
  `𝒪_𝒳`-modules whose kernel and cokernel are parasitic is an isomorphism on sections over every
  flat object.
* `AlgebraicGeometry.Stack.isIso_restrictModuleFunctorToSmallEtale_map_of_isParasitic_sheaf`:
  such a map restricts to an isomorphism on the small étale site of a flat object.

## References

* [Stacks Project, Tag 0GQK](https://stacks.math.columbia.edu/tag/0GQK)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite

universe u w

namespace AlgebraicGeometry.Stack

attribute [local instance] hasSheafCompose_forget_ringCat
  hasSheafCompose_forget_commRingCat Stacks.hasSheafCompose_forget₂_commRingCat
  FlatFppf.isContinuous_inclusion_topology FlatFppf.isCocontinuous_inclusion_topology
  FlatFppf.hasSheafify_addCommGrpCat FlatFppf.wEqualsLocallyBijective_addCommGrpCat
  FlatFppf.hasSheafify_fppf_addCommGrpCat FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat
  FlatFppf.hasSheafify_associatedTopology_ab
  FlatFppf.wEqualsLocallyBijective_fppfTopology_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A map of sheaves of `𝒪_𝒳`-modules with parasitic kernel and cokernel is invertible on
sections over a flat object.** The kernel and the cokernel are taken in `Mod(𝒪_𝒳)`. Restriction
to the flat-fppf site is exact and kills exactly the parasitic modules, so it carries the map to
a morphism with vanishing kernel and cokernel, i.e. an isomorphism; and it does not change the
sections over a flat object. -/
theorem isIso_app_of_isParasitic_kernel_cokernel {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {M N : fppfModules B S hS 𝒳} (φ : M ⟶ N)
    (hker : IsParasitic B S hS 𝒳 .fppf (kernel φ).val)
    (hcoker : IsParasitic B S hS 𝒳 .fppf (cokernel φ).val)
    (y : 𝒳.val.val.obj) (hy : flatObject B S hS 𝒳.val y) :
    Function.Bijective (φ.val.app (op y)) := by
  let R := FlatFppf.moduleRestriction B S hS 𝒳
  have hk : IsZero (kernel (R.map φ)) :=
    ((FlatFppf.isParasitic_iff_isZero_moduleRestriction B S hS 𝒳 _).1 hker).of_iso
      (PreservesKernel.iso R φ).symm
  have hc : IsZero (cokernel (R.map φ)) :=
    ((FlatFppf.isParasitic_iff_isZero_moduleRestriction B S hS 𝒳 _).1 hcoker).of_iso
      (PreservesCokernel.iso R φ).symm
  have : Mono (R.map φ) := mono_of_isZero_kernel _ hk
  have : Epi (R.map φ) := epi_of_isZero_cokernel _ hc
  have : IsIso (R.map φ) := isIso_of_mono_of_epi _
  let y' : (FlatFppf.objectProperty B S hS 𝒳).FullSubcategory := ⟨y, hy⟩
  have h1 : IsIso (R.map φ).val := (SheafOfModules.forget _).map_isIso (R.map φ)
  have h2 : IsIso ((R.map φ).val.app (op y')) :=
    (PresheafOfModules.evaluation _ (op y')).map_isIso (R.map φ).val
  exact (ConcreteCategory.isIso_iff_bijective _).1 h2

variable (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)

/-- **A map of sheaves of `𝒪_𝒳`-modules with parasitic kernel and cokernel restricts to an
isomorphism on the small étale site of a flat object.** The kernel and the cokernel are taken in
`Mod(𝒪_𝒳)`, as in **Stacks 0779** (2); the small étale site of the scheme below a flat object only
sees flat objects, where the map is invertible by
`AlgebraicGeometry.Stack.isIso_app_of_isParasitic_kernel_cokernel`. -/
theorem isIso_restrictModuleFunctorToSmallEtale_map_of_isParasitic_sheaf
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {M N : fppfModules B S hS 𝒳} (φ : M ⟶ N)
    (hker : IsParasitic B S hS 𝒳 .fppf (kernel φ).val)
    (hcoker : IsParasitic B S hS 𝒳 .fppf (cokernel φ).val)
    (x : 𝒳.val.val.obj) (hx : flatObject B S hS 𝒳.val x) :
    IsIso ((restrictModuleFunctorToSmallEtale B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids x (etaleTopology B) (etaleTopology_le_topology B)).map
        φ.val) := by
  have hb : ∀ V : SmallEtale E (𝒳.val.val.p.obj x).left.1
      (contains_base B E h S hS 𝒳.val.val.p x),
      Function.Bijective (φ.val.app (op ((smallEtaleToStack B E h S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids x).obj V))) := fun V ↦
    isIso_app_of_isParasitic_kernel_cokernel B S hS φ hker hcoker _
      (flatObject_smallEtaleToStack_obj B E h S hS x hx V)
  let F := restrictModuleFunctorToSmallEtale B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids x (etaleTopology B) (etaleTopology_le_topology B)
  have : Mono (F.map φ.val) := PresheafOfModules.mono_of_injective fun V ↦ (hb V.unop).1
  have : Epi (F.map φ.val) := PresheafOfModules.epi_of_surjective fun V ↦ (hb V.unop).2
  exact isIso_of_mono_of_epi _

end AlgebraicGeometry.Stack

end
