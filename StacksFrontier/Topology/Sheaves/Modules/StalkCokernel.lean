module

public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The stalk of a cokernel, and an elementwise criterion for a map out of a cokernel

Let `𝒪` be a sheaf of rings on a topological space `X`. Taking stalks at a point `x` is a
functor from sheaves of `𝒪`-modules to modules over the stalk ring `𝒪_x` which preserves all
colimits (`AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits`, Stacks 01AH), so
in particular it carries a cokernel to a cokernel: the stalk of `coker f` *is* the cokernel of
the stalk map of `f`.

Combining that identification with the fact that isomorphy of sheaves of modules is detected
on stalks (`AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap`, Stacks 01AG) gives
the criterion this file is for: a map `coker f ⟶ N` obtained by descending a morphism
`φ : B ⟶ N` which kills `f` is an isomorphism exactly when, at every point of `X`, the map
`coker (f_x) ⟶ N_x` obtained by descending `φ_x` is bijective. The right-hand side is an
elementwise statement about modules over one ring, so a surjectivity and an injectivity proof
carried out at the ring level can be fed into it directly.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.stalkObjCokernelIso`: **the stalk of a cokernel is the
  cokernel of the stalks.**

## Main results

* `AlgebraicGeometry.SheafOfModules.stalkMap_π_comp_stalkObjCokernelIso_hom`: the
  identification is compatible with the two cokernel projections.
* `AlgebraicGeometry.SheafOfModules.stalkMap_comp_eq_zero`: a composite which vanishes still
  vanishes on stalks, which is what makes the descended map on stalks available at all.
* `AlgebraicGeometry.SheafOfModules.stalkMap_cokernelDesc`: the stalk of a descended map is,
  through that identification, the descent of the stalk map.
* `AlgebraicGeometry.SheafOfModules.isIso_cokernelDesc_iff_forall_isIso_stalk` and
  `AlgebraicGeometry.SheafOfModules.isIso_cokernelDesc_iff_forall_bijective_stalk`: **a map out
  of a cokernel is an isomorphism exactly when the corresponding map out of the cokernel of the
  stalks is an isomorphism, respectively bijective, at every point.**
* `AlgebraicGeometry.SheafOfModules.range_stalkMap_le_ker_stalkMap` and
  `AlgebraicGeometry.SheafOfModules.isIso_cokernelDesc_iff_forall_bijective_liftQ`: **the same
  criterion with the cokernel of the stalks presented as the quotient of `B_x` by the range of
  `f_x`**, which is the form a map built by `Submodule.liftQ` can be fed into.

## Implementation notes

`stalkFunctor_preservesColimits` is stated at the unindexed `PreservesColimits`, whose shape
universe is that of the target category of modules; cokernels are colimits over
`CategoryTheory.Limits.WalkingParallelPair`, which lives in `Type 0`. The two are bridged by
`CategoryTheory.Limits.preservesSmallestColimits_of_preservesColimits`, recorded here as the
instance `AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesSmallestColimits` so that
`CategoryTheory.Limits.PreservesCokernel` is found by synthesis.

The criterion is stated about an arbitrary `CategoryTheory.Limits.cokernel.desc`, with the
morphism being descended and the proof that it kills `f` left free. That is the shape in which
`CochainComplex.mappingCone.isIso_homologyMap_zero_iff` presents the comparison map of
Stacks 0E1Y: there `f` is a differential, `φ` is a component of a null homotopy followed by a
cokernel projection, and nothing further is known about either.

## References

* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

noncomputable section

namespace AlgebraicGeometry.SheafOfModules

variable {X : TopCat.{u}}
  (𝒪 : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X)

/-- The stalk functor preserves colimits of diagrams indexed by a category in `Type 0`.

This is `AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits` with its shape
universe lowered. It is needed as a separate instance because the colimits defining kernels
and cokernels are indexed by `CategoryTheory.Limits.WalkingParallelPair`, a category in
`Type 0`, whereas the unindexed `CategoryTheory.Limits.PreservesColimits` refers to the
universe of the category of modules over the stalk ring. -/
@[ega "0 4.3.2" "special case"]
instance stalkFunctor_preservesSmallestColimits :
    PreservesColimitsOfSize.{0, 0} (stalkFunctor 𝒪 x) :=
  preservesSmallestColimits_of_preservesColimits _

variable {A B N : _root_.SheafOfModules.{u} 𝒪}

/-- **The stalk of a cokernel is the cokernel of the stalks.** The stalk functor preserves
colimits, hence cokernels, so the canonical comparison map is an isomorphism. -/
def stalkObjCokernelIso (f : A ⟶ B) :
    stalkObj 𝒪 x (cokernel f) ≅ cokernel (stalkMap 𝒪 x f) :=
  PreservesCokernel.iso (stalkFunctor 𝒪 x) f

/-- The identification of `AlgebraicGeometry.SheafOfModules.stalkObjCokernelIso` carries the
stalk of the cokernel projection of `f` to the cokernel projection of the stalk map of `f`. -/
@[reassoc (attr := simp)]
theorem stalkMap_π_comp_stalkObjCokernelIso_hom (f : A ⟶ B) :
    stalkMap 𝒪 x (cokernel.π f) ≫ (stalkObjCokernelIso 𝒪 x f).hom =
      cokernel.π (stalkMap 𝒪 x f) :=
  PreservesCokernel.π_iso_hom (stalkFunctor 𝒪 x) f

/-- A composite of morphisms of sheaves of modules which vanishes vanishes on every stalk.

This is what makes the descended map of stalks of
`AlgebraicGeometry.SheafOfModules.stalkMap_cokernelDesc` available: the stalk functor preserves
zero morphisms, so the stalk maps still compose to zero. -/
theorem stalkMap_comp_eq_zero {f : A ⟶ B} {φ : B ⟶ N} (h : f ≫ φ = 0) :
    stalkMap 𝒪 x f ≫ stalkMap 𝒪 x φ = 0 := by
  show (stalkFunctor 𝒪 x).map f ≫ (stalkFunctor 𝒪 x).map φ = 0
  rw [← Functor.map_comp, h, Functor.map_zero]

/-- **The stalk of a map descended to a cokernel is the descent of the stalk map.** Read
through `AlgebraicGeometry.SheafOfModules.stalkObjCokernelIso`, the stalk at `x` of
`cokernel.desc f φ h` is `cokernel.desc` of the stalk map of `φ`.

Both sides are determined by their composites with the stalk of the cokernel projection of `f`,
which is an epimorphism because the stalk functor preserves cokernels. -/
theorem stalkMap_cokernelDesc (f : A ⟶ B) (φ : B ⟶ N) (h : f ≫ φ = 0) :
    stalkMap 𝒪 x (cokernel.desc f φ h) =
      (stalkObjCokernelIso 𝒪 x f).hom ≫
        cokernel.desc (stalkMap 𝒪 x f) (stalkMap 𝒪 x φ) (stalkMap_comp_eq_zero 𝒪 x h) := by
  have hfac : stalkMap 𝒪 x (cokernel.π f) =
      cokernel.π (stalkMap 𝒪 x f) ≫ (stalkObjCokernelIso 𝒪 x f).inv := by
    rw [← stalkMap_π_comp_stalkObjCokernelIso_hom, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hepi : Epi (stalkMap 𝒪 x (cokernel.π f)) := by rw [hfac]; infer_instance
  rw [← cancel_epi (stalkMap 𝒪 x (cokernel.π f)),
    stalkMap_π_comp_stalkObjCokernelIso_hom_assoc, cokernel.π_desc]
  show (stalkFunctor 𝒪 x).map (cokernel.π f) ≫ (stalkFunctor 𝒪 x).map (cokernel.desc f φ h) = _
  rw [← Functor.map_comp, cokernel.π_desc]
  rfl

/-- **A map out of a cokernel of sheaves of modules is an isomorphism exactly when it is one on
every stalk.** The map `coker f ⟶ N` descended from `φ : B ⟶ N` is an isomorphism if and only
if, for every point `x` of `X`, the map `coker (f_x) ⟶ N_x` descended from the stalk map of `φ`
is an isomorphism of `𝒪_x`-modules.

Isomorphy of sheaves of modules is a stalkwise condition
(`AlgebraicGeometry.SheafOfModules.isIso_iff_forall_isIso_stalkFunctor_map`), and the stalk of
the descended map is the descended stalk map up to the isomorphism
`AlgebraicGeometry.SheafOfModules.stalkObjCokernelIso`. -/
theorem isIso_cokernelDesc_iff_forall_isIso_stalk (f : A ⟶ B) (φ : B ⟶ N) (h : f ≫ φ = 0) :
    IsIso (cokernel.desc f φ h) ↔ ∀ x : X,
      IsIso (cokernel.desc (stalkMap 𝒪 x f) (stalkMap 𝒪 x φ) (stalkMap_comp_eq_zero 𝒪 x h)) := by
  rw [isIso_iff_forall_isIso_stalkFunctor_map]
  refine forall_congr' fun x => ?_
  show IsIso (stalkMap 𝒪 x (cokernel.desc f φ h)) ↔ _
  rw [stalkMap_cokernelDesc, isIso_comp_left_iff]

/-- **An elementwise criterion for a map out of a cokernel of sheaves of modules to be an
isomorphism.** The map `coker f ⟶ N` descended from `φ : B ⟶ N` is an isomorphism if and only
if, for every point `x` of `X`, the induced map `coker (f_x) ⟶ N_x` of `𝒪_x`-modules is
bijective.

This is `AlgebraicGeometry.SheafOfModules.isIso_cokernelDesc_iff_forall_isIso_stalk` with the
stalkwise condition read elementwise, which is the form in which a surjectivity statement and
an injectivity statement proved about modules over a single ring can be fed in. -/
theorem isIso_cokernelDesc_iff_forall_bijective_stalk
    (f : A ⟶ B) (φ : B ⟶ N) (h : f ≫ φ = 0) :
    IsIso (cokernel.desc f φ h) ↔ ∀ x : X,
      Function.Bijective (cokernel.desc (stalkMap 𝒪 x f) (stalkMap 𝒪 x φ)
        (stalkMap_comp_eq_zero 𝒪 x h)).hom := by
  rw [isIso_cokernelDesc_iff_forall_isIso_stalk]
  exact forall_congr' fun x => ConcreteCategory.isIso_iff_bijective _

/-- The range of the stalk map of `f` is contained in the kernel of the stalk map of `φ`, for a
composite `f ≫ φ` which vanishes. This is
`AlgebraicGeometry.SheafOfModules.stalkMap_comp_eq_zero` read elementwise, and it is the side
condition of the `Submodule.liftQ` in
`AlgebraicGeometry.SheafOfModules.isIso_cokernelDesc_iff_forall_bijective_liftQ`. -/
theorem range_stalkMap_le_ker_stalkMap {f : A ⟶ B} {φ : B ⟶ N} (h : f ≫ φ = 0) :
    LinearMap.range (stalkMap 𝒪 x f).hom ≤ LinearMap.ker (stalkMap 𝒪 x φ).hom := by
  rintro _ ⟨a, rfl⟩
  have h₀ := congrArg (fun ψ => ModuleCat.Hom.hom ψ a) (stalkMap_comp_eq_zero 𝒪 x h)
  simpa using h₀

/-- **An elementwise criterion for a map out of a cokernel of sheaves of modules to be an
isomorphism, with the cokernel of the stalks presented as a quotient module.** The map
`coker f ⟶ N` descended from `φ : B ⟶ N` is an isomorphism if and only if, for every point `x`
of `X`, the map `B_x ⧸ range (f_x) ⟶ N_x` descended from the stalk map of `φ` is bijective.

This is
`AlgebraicGeometry.SheafOfModules.isIso_cokernelDesc_iff_forall_bijective_stalk` with the
categorical cokernel of `f_x` replaced by the quotient of `B_x` by the range of `f_x`, along
`ModuleCat.cokernelIsoRangeQuotient`. It is the form a map produced by `Submodule.liftQ` — the
usual way a map out of such a quotient is built at the ring level — can be fed into. -/
theorem isIso_cokernelDesc_iff_forall_bijective_liftQ
    (f : A ⟶ B) (φ : B ⟶ N) (h : f ≫ φ = 0) :
    IsIso (cokernel.desc f φ h) ↔ ∀ x : X,
      Function.Bijective ((LinearMap.range (stalkMap 𝒪 x f).hom).liftQ (stalkMap 𝒪 x φ).hom
        (range_stalkMap_le_ker_stalkMap 𝒪 x h)) := by
  rw [isIso_cokernelDesc_iff_forall_isIso_stalk]
  refine forall_congr' fun x => ?_
  set ψ := ModuleCat.ofHom ((LinearMap.range (stalkMap 𝒪 x f).hom).liftQ (stalkMap 𝒪 x φ).hom
    (range_stalkMap_le_ker_stalkMap 𝒪 x h)) with hψ
  have hmkQ : Epi (ModuleCat.ofHom (LinearMap.range (stalkMap 𝒪 x f).hom).mkQ) :=
    (ModuleCat.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)
  have key : ψ = (ModuleCat.cokernelIsoRangeQuotient (stalkMap 𝒪 x f)).inv ≫
      cokernel.desc (stalkMap 𝒪 x f) (stalkMap 𝒪 x φ) (stalkMap_comp_eq_zero 𝒪 x h) := by
    rw [← cancel_epi (ModuleCat.ofHom (LinearMap.range (stalkMap 𝒪 x f).hom).mkQ),
      ← Category.assoc, ModuleCat.range_mkQ_cokernelIsoRangeQuotient_inv, cokernel.π_desc, hψ]
    ext a
    exact (LinearMap.congr_fun ((LinearMap.range (stalkMap 𝒪 x f).hom).liftQ_mkQ
      (stalkMap 𝒪 x φ).hom (range_stalkMap_le_ker_stalkMap 𝒪 x h)) a)
  rw [show ((LinearMap.range (stalkMap 𝒪 x f).hom).liftQ (stalkMap 𝒪 x φ).hom
      (range_stalkMap_le_ker_stalkMap 𝒪 x h)) = ψ.hom from rfl,
    ← ConcreteCategory.isIso_iff_bijective, key, isIso_comp_left_iff]

end AlgebraicGeometry.SheafOfModules

end
