module

public import StacksFrontier.AlgebraicGeometry.Conormal.IsoSquare

/-!
# Morphisms of sheaves of modules are determined by their restrictions to an open cover

Let `Xr` be a ringed space and let `V` be a family of open subspaces covering it. Two morphisms
of sheaves of `𝒪_{Xr}`-modules that agree after restriction to each `V k` are equal. The same
holds for pullback along the open immersions `ι_{V k} : Xr|_{V k} ⟶ Xr` and, for a scheme, for
pullback along the inclusions `AlgebraicGeometry.Scheme.homOfLE` of a family of opens into a
larger open they cover.

## Main results

* `AlgebraicGeometry.RingedSpace.moduleRestrict_map_injective`: the restriction functors to a
  family of opens covering the space are jointly faithful.
* `AlgebraicGeometry.RingedSpace.modulePullback_ofRestrict_map_injective`: the same for pullback
  along the open immersions.
* `RingedSpaceModuleAdjunction.modulePullback_map_injective_of_opensCover`: the same for a
  family of morphisms of schemes each factoring as an isomorphism onto an open subscheme, where
  the opens cover.
* `RingedSpaceModuleAdjunction.modulePullback_homOfLE_map_injective`: the same for the
  inclusions of a family of opens of a scheme into a larger open they cover.

## References

* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 04FH](https://stacks.math.columbia.edu/tag/04FH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction 
open AlgebraicGeometry AlgebraicGeometry.RingedSpace

universe u

namespace AlgebraicGeometry.RingedSpace

/-- If two morphisms have equal images under a functor `F`, they have equal images under any
functor `G` naturally isomorphic to `F`. -/
private theorem map_eq_of_iso {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (α : F ≅ G)
    {M N : C} {P Q : M ⟶ N} (h : F.map P = F.map Q) : G.map P = G.map Q := by
  refine (cancel_epi (α.hom.app M)).1 ?_
  rw [← α.hom.naturality P, ← α.hom.naturality Q, h]

/-- Two morphisms of sheaves of modules on a ringed space whose restrictions to each member of a
covering family of opens agree are equal. -/
theorem moduleRestrict_map_injective {Xr : RingedSpace.{u, u}} {J : Type*}
    (V : J → Opens Xr.carrier) (hV : ∀ x : Xr.carrier, ∃ k, x ∈ V k)
    {M N : SheafOfModules.{u} (structureSheafRing Xr)} {P Q : M ⟶ N}
    (h : ∀ k, (moduleRestrict Xr (V k)).map P = (moduleRestrict Xr (V k)).map Q) : P = Q := by
  set B : (Σ k : J, Opens (Xr.restrict (V k).isOpenEmbedding).carrier) → Opens Xr.carrier :=
    fun p => (restrictOpensInclusion Xr (V p.1)).obj p.2
  have hBasis : Opens.IsBasis (Set.range B) := by
    rw [Opens.isBasis_iff_nbhd]
    intro O x hx
    obtain ⟨k, hk⟩ := hV x
    refine ⟨B ⟨k, (Opens.map (Xr.ofRestrict (V k).isOpenEmbedding).hom.base).obj O⟩,
      ⟨_, rfl⟩, ⟨⟨x, hk⟩, hx, rfl⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hz
  refine SheafOfModules.hom_ext ((PresheafOfModules.toPresheaf _).map_injective ?_)
  refine TopCat.Sheaf.hom_ext (B := B) _
    (show TopCat.Sheaf _ Xr.carrier from ⟨N.val.presheaf, N.isSheaf⟩) hBasis (fun p => ?_)
  ext s
  exact congrArg (fun z => z.val.app (op p.2) s) (h p.1)

/-- Two morphisms of sheaves of modules on a ringed space whose pullbacks along the open
immersions of each member of a covering family of opens agree are equal. -/
theorem modulePullback_ofRestrict_map_injective {Xr : RingedSpace.{u, u}} {J : Type*}
    (V : J → Opens Xr.carrier) (hV : ∀ x : Xr.carrier, ∃ k, x ∈ V k)
    {M N : SheafOfModules.{u} (structureSheafRing Xr)} {P Q : M ⟶ N}
    (h : ∀ k, (modulePullback (Xr.ofRestrict (V k).isOpenEmbedding)).map P =
      (modulePullback (Xr.ofRestrict (V k).isOpenEmbedding)).map Q) : P = Q := by
  refine moduleRestrict_map_injective V hV (fun k => ?_)
  exact map_eq_of_iso (modulePullbackRestrictIso Xr (V k)) (h k)

end AlgebraicGeometry.RingedSpace

namespace RingedSpaceModuleAdjunction

/-- The isomorphism of underlying ringed spaces of an isomorphism of schemes. -/
abbrev toShHomIso {Zs Zt : Scheme.{u}} (e : Zs ≅ Zt) : Zs.toSheafedSpace ≅ Zt.toSheafedSpace where
  hom := e.hom.toLRSHom.toShHom
  inv := e.inv.toLRSHom.toShHom
  hom_inv_id := congrArg (fun p : Zs ⟶ Zs => p.toLRSHom.toShHom) e.hom_inv_id
  inv_hom_id := congrArg (fun p : Zt ⟶ Zt => p.toLRSHom.toShHom) e.inv_hom_id

/-- Two morphisms of sheaves of modules on a scheme whose pullbacks along the inclusions of the
members of an open cover agree are equal. -/
theorem modulePullback_ι_map_injective {Zs : Scheme.{u}} {J : Type*} (O : J → Zs.Opens)
    (hO : ∀ x : Zs, ∃ k, x ∈ O k)
    {M N : SheafOfModules.{u} (structureSheafRing Zs.toSheafedSpace)} {P Q : M ⟶ N}
    (h : ∀ k, (modulePullback (O k).ι.toLRSHom.toShHom).map P =
      (modulePullback (O k).ι.toLRSHom.toShHom).map Q) : P = Q :=
  AlgebraicGeometry.RingedSpace.modulePullback_ofRestrict_map_injective O hO h

/-- Two morphisms of sheaves of modules on a scheme whose pullbacks along each `g k` agree are
equal, for a family `g k = e k ≫ ι_{O k}` of isomorphisms onto members of an open cover. -/
theorem modulePullback_map_injective_of_opensCover {Zs : Scheme.{u}} {J : Type*}
    {Z : J → Scheme.{u}} (g : ∀ k, Z k ⟶ Zs) (O : J → Zs.Opens)
    (e : ∀ k, Z k ≅ (O k).toScheme) (hg : ∀ k, g k = (e k).hom ≫ (O k).ι)
    (hO : ∀ x : Zs, ∃ k, x ∈ O k)
    {M N : SheafOfModules.{u} (structureSheafRing Zs.toSheafedSpace)} {P Q : M ⟶ N}
    (h : ∀ k, (modulePullback (g k).toLRSHom.toShHom).map P =
      (modulePullback (g k).toLRSHom.toShHom).map Q) : P = Q := by
  refine modulePullback_ι_map_injective O hO (fun k => ?_)
  have hiso : (modulePullback (toShHomIso (e k)).hom).IsEquivalence :=
    isEquivalence_modulePullback_of_iso (toShHomIso (e k))
  have hk := h k
  rw [hg k] at hk
  exact (modulePullback (e k).hom.toLRSHom.toShHom).map_injective
    (map_eq_of_iso (modulePullbackComp (e k).hom.toLRSHom.toShHom (O k).ι.toLRSHom.toShHom) hk)

/-- For opens `A k ≤ B` of a scheme `X` covering `B`, two morphisms of sheaves of modules on `B`
whose pullbacks along the inclusions `A k ⟶ B` agree are equal. -/
theorem modulePullback_homOfLE_map_injective {X : Scheme.{u}} {B : X.Opens} {J : Type*}
    (A : J → X.Opens) (hAB : ∀ k, A k ≤ B) (hcov : ∀ x : X, x ∈ B → ∃ k, x ∈ A k)
    {M N : SheafOfModules.{u} (structureSheafRing B.toScheme.toSheafedSpace)} {P Q : M ⟶ N}
    (h : ∀ k, (modulePullback (X.homOfLE (hAB k)).toLRSHom.toShHom).map P =
      (modulePullback (X.homOfLE (hAB k)).toLRSHom.toShHom).map Q) : P = Q := by
  have hrange (k) : Set.range (X.homOfLE (hAB k)).base = Set.range (B.ι ⁻¹ᵁ A k).ι.base := by
    rw [Scheme.Opens.range_ι, ← Scheme.opensRange_homOfLE (hAB k)]
    rfl
  refine modulePullback_map_injective_of_opensCover (fun k => X.homOfLE (hAB k))
    (fun k => B.ι ⁻¹ᵁ A k)
    (fun k => AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq (X.homOfLE (hAB k))
      (B.ι ⁻¹ᵁ A k).ι (hrange k))
    (fun k => (AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ (hrange k)).symm)
    (fun x => by obtain ⟨k, hk⟩ := hcov x.1 x.2; exact ⟨k, hk⟩) h

end RingedSpaceModuleAdjunction

end
