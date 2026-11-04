module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Duality.AdequateSheafOfModules

/-!
# The small Zariski site inside a chosen big site

The small Zariski site `S_Zar` of a scheme `S` sits inside the underlying category of every
chosen big site over `S`, an open `U ⊆ S` going to the open subscheme `U` with its open
immersion. This module sets up that inclusion, and the chosen big fppf site over `S` attached to
a chosen big fppf site of schemes.

## Main definitions

* `Stacks.Adequate.opensBelowToOver` and `Stacks.Adequate.BigSite.opensToBig` — the small
  Zariski site of `S` inside the size-bounded schemes over `S`, hence inside the underlying
  category of a chosen big site over `S`.
* `Stacks.Adequate.BigSite.ofBigFppfSite` — the chosen big fppf site over `S` attached to a
  chosen big fppf site, with no hypothesis: the sheaf condition of [Stacks, Tag 03DU] for the
  localized fppf topology is `AlgebraicGeometry.BigFppfOver.structure_isSheaf`.

## Implementation notes

The continuity of the inclusion into a chosen big site of any of the five topologies, and the
restriction functor `𝓖 ↦ 𝓖|_{S_Zar}` on every chosen big site, are
`Stacks.Adequate.BigSite.isContinuous_opensToBig` and
`Stacks.Adequate.BigSite.zariskiRestrictModule` in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/ZariskiInclusion.lean`. The comparison
functors `u : QCoh(𝒪_S) ⥤ Adeq(𝒪)` and `v : Adeq(𝒪) ⥤ QCoh(𝒪_S)` of [Stacks, Tag 06VN] and
their adjunction, on every chosen big site, are in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AssociatedModuleAdjunction.lean`.

## References

* [Stacks Project, Tag 06VN](https://stacks.math.columbia.edu/tag/06VN)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}}

/-! ### The small Zariski site inside the size-bounded schemes over the base -/

/-- An open subscheme of a size-bounded scheme is size bounded, its open immersion being a
monomorphism which is locally of finite presentation. -/
public theorem opensBelow_mem {κ : Cardinal.{u}} (hS : schemeSizeBelow κ S) (U : S.Opens) :
    schemeSizeBelow κ (U : Scheme.{u}) :=
  Scheme.size_lt_of_isOpenImmersion U.ι hS

/-- An open of `S` as a size-bounded scheme over `S`, via its open immersion. -/
@[implicit_reducible]
public def opensBelowObj {κ : Cardinal.{u}} (hS : schemeSizeBelow κ S) (U : S.Opens) :
    Over (⟨S, hS⟩ : SchemeBelow κ) :=
  Over.mk (ObjectProperty.homMk
    (X := (⟨(U : Scheme.{u}), opensBelow_mem hS U⟩ : SchemeBelow κ)) U.ι)

/-- The inclusion of one open of `S` into a larger one, as a morphism of size-bounded schemes
over `S`. -/
@[implicit_reducible]
public noncomputable def opensBelowHom {κ : Cardinal.{u}} (hS : schemeSizeBelow κ S)
    {U V : S.Opens} (h : U ≤ V) : opensBelowObj hS U ⟶ opensBelowObj hS V :=
  Over.homMk (ObjectProperty.homMk
      (X := (⟨(U : Scheme.{u}), opensBelow_mem hS U⟩ : SchemeBelow κ))
      (Y := (⟨(V : Scheme.{u}), opensBelow_mem hS V⟩ : SchemeBelow κ)) (S.homOfLE h))
    (ObjectProperty.hom_ext _ (S.homOfLE_ι h))

/-- The underlying morphism of schemes of `opensBelowHom` is the inclusion of opens. -/
@[simp]
public theorem opensBelowHom_left_hom {κ : Cardinal.{u}} (hS : schemeSizeBelow κ S)
    {U V : S.Opens} (h : U ≤ V) : (opensBelowHom hS h).left.hom = S.homOfLE h := rfl

/-- The small Zariski site of `S` inside the size-bounded schemes over `S`. -/
public noncomputable def opensBelowToOver {κ : Cardinal.{u}} (hS : schemeSizeBelow κ S) :
    S.Opens ⥤ Over (⟨S, hS⟩ : SchemeBelow κ) where
  obj U := opensBelowObj hS U
  map {_ _} h := opensBelowHom hS (leOfHom h)
  map_id U := by
    apply Over.OverMorphism.ext; apply ObjectProperty.hom_ext
    rw [opensBelowHom_left_hom, Over.id_left, ObjectProperty.FullSubcategory.id_hom,
      Scheme.homOfLE_rfl]
    rfl
  map_comp f g := by
    apply Over.OverMorphism.ext; apply ObjectProperty.hom_ext
    rw [opensBelowHom_left_hom, Over.comp_left, ObjectProperty.FullSubcategory.comp_hom,
      opensBelowHom_left_hom, opensBelowHom_left_hom, Scheme.homOfLE_homOfLE]

/-- The small Zariski site of `S` inside the underlying category of a chosen big site over
`S`. -/
public noncomputable abbrev BigSite.opensToBig (B : BigSite τ S) : S.Opens ⥤ B.category :=
  opensBelowToOver B.base_mem

/-! ### A chosen big fppf site from a chosen big fppf site of schemes -/

/-- **The chosen big fppf site over `S` attached to a chosen big fppf site of schemes.** This
is the constructor of [Stacks, Tag 06VG] for `τ = fppf`, with no hypothesis: the sheaf
condition of [Stacks, Tag 03DU] for the localized fppf topology is
`AlgebraicGeometry.BigFppfOver.structure_isSheaf`. -/
public noncomputable def BigSite.ofBigFppfSite (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : BigSite .fppf S :=
  BigSite.ofFppf B S hS (BigFppfOver.structure_isSheaf B S hS)

/-- The cutoff of `BigSite.ofBigFppfSite` is that of the chosen big fppf site of schemes. -/
@[simp]
public theorem BigSite.ofBigFppfSite_cutoff (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : (BigSite.ofBigFppfSite B S hS).cutoff = B.cutoff := rfl

/-- The topology of `BigSite.ofBigFppfSite` is the localized fppf topology. -/
@[simp]
public theorem BigSite.ofBigFppfSite_topology (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (BigSite.ofBigFppfSite B S hS).topology = BigFppfOver.topology B S hS := rfl

end Stacks.Adequate

end
