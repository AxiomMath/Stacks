module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineSectionBaseChangeExit
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfSheafificationAffineSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentLocallyQuasicoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction

/-!
# Sections over an affine object commute with colimits of quasi-coherent modules

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `x` be an object of `𝒳`
lying over an affine scheme. Taking sections over `x` commutes with colimits of quasi-coherent
modules on the fppf site of `𝒳`: for a diagram `F` of quasi-coherent modules with colimit `M`,
`colim F(x) ⟶ M(x)` is an isomorphism.

The colimit of `F` in `Mod(𝒪_𝒳)` is the sheafification of the colimit `P` of the underlying
presheaves of modules. A colimit of cartesian presheaves of modules is cartesian
(`Stacks.PresheafOfModules.isIso_restrictionBaseChange_colimit`), quasi-coherent modules are
cartesian between affine objects
(`AlgebraicGeometry.FibredSite.isIso_restrictionBaseChange_of_isQuasicoherentOnSite`), and the
sheafification of a presheaf of modules cartesian along flat morphisms of affines does not
change its sections over affine objects
(`AlgebraicGeometry.FibredSite.bijective_sheafificationAdjunction_unit_app_of_isAffine_of_flat`).
So `M(x) = P(x) = colim F(x)`, the last because colimits of presheaves of modules are computed
objectwise.

## Main results

* `AlgebraicGeometry.FibredSite.isColimit_mapCocone_evaluation_of_isAffine`: sections over `x`
  of a colimit in `Mod(𝒪_𝒳)` of a diagram of quasi-coherent modules.
* `AlgebraicGeometry.FibredSite.preservesColimitsOfSize_quasicoherentEvaluation`: **the functor
  `QCoh(𝒪_𝒳) ⥤ Mod_{𝒪(x)}`, `M ↦ M(x)`, preserves small colimits.**

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  [EssentiallySmall.{u} 𝒳]

/-- **Sections over an affine object of a colimit of quasi-coherent modules.** For a diagram `F`
of quasi-coherent modules on the fppf site of `𝒳` and a colimit cocone `c` of `F` in
`Mod(𝒪_𝒳)`, the sections over an object `x` lying over an affine scheme form a colimit cocone
of the sections of `F` over `x`. -/
theorem isColimit_mapCocone_evaluation_of_isAffine {K : Type u} [Category.{u} K]
    (F : K ⥤ SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    (hF : ∀ k, (F.obj k).IsQuasicoherentOnSite) {c : Cocone F} (hc : IsColimit c) {x : 𝒳}
    (hx : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x))) :
    Nonempty (IsColimit ((SheafOfModules.forget _ ⋙
      PresheafOfModules.evaluation _ (op x)).mapCocone c)) := by
  have := hasWeakSheafify_associatedTopology B S hS p .fppf
  have := wEqualsLocallyBijective_associatedTopology B S hS p .fppf
  let R := ringStructureSheafCore B S hS p hp .fppf
  let L := PresheafOfModules.sheafification (𝟙 R.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  let U := SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  let E := PresheafOfModules.evaluation R.obj (op x)
  let G := F ⋙ U
  let hs := colimit.isColimit G
  let s := colimit.cocone G
  let φ : s.pt ⟶ U.obj c.pt := hs.desc (U.mapCocone c)
  have hφ (k : K) : s.ι.app k ≫ φ = U.map (c.ι.app k) := hs.fac _ k
  -- the colimit presheaf is cartesian along flat morphisms of affines
  have hP : ∀ {z y : 𝒳} (g : z ⟶ y), IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj z)) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj y)) →
      Flat ((BigFppfOver.toScheme B S hS).map (p.map g)) →
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange
        (R := (structureSheaf B S hS p hp .fppf).obj) s.pt g.op) := fun g hz hy _ =>
    Stacks.PresheafOfModules.isIso_restrictionBaseChange_colimit
      (structureSheaf B S hS p hp .fppf).obj G s hs g.op fun k =>
        isIso_restrictionBaseChange_of_isQuasicoherentOnSite (F.obj k) (hF k) g hz hy
  have hunit : IsIso (E.map (adj.unit.app s.pt)) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_sheafificationAdjunction_unit_app_of_isAffine_of_flat B S hS p hp s.pt hP hx)
  -- the sheafification of the colimit presheaf is the colimit sheaf
  let ψ : L.obj s.pt ⟶ c.pt := (adj.homEquiv _ _).symm φ
  have hφψ : φ = adj.unit.app s.pt ≫ U.map ψ :=
    ((adj.homEquiv _ _).apply_symm_apply φ).symm.trans (adj.homEquiv_unit _ _ _)
  have : PreservesColimitsOfSize.{u, u} L := adj.leftAdjoint_preservesColimits
  let α : F ≅ G ⋙ L := (Functor.isoWhiskerLeft F (asIso adj.counit)).symm ≪≫
    (Functor.associator _ _ _).symm
  let t := (Cocone.precompose α.hom).obj (L.mapCocone s)
  have ht : IsColimit t := (IsColimit.precomposeHomEquiv α _).symm (isColimitOfPreserves L hs)
  have hψ : ψ = ht.desc c := by
    refine ht.uniq c ψ fun k => ?_
    show (α.hom.app k ≫ L.map (s.ι.app k)) ≫ ψ = c.ι.app k
    have h₁ : L.map (s.ι.app k) ≫ ψ = (adj.homEquiv _ _).symm (s.ι.app k ≫ φ) :=
      (adj.homEquiv_naturality_left_symm _ _).symm
    rw [Category.assoc, h₁, hφ, Adjunction.homEquiv_counit]
    simp [α]
  have : IsIso ψ := hψ ▸ (IsColimit.coconePointUniqueUpToIso ht hc).isIso_hom
  have hE : IsIso (E.map φ) := by rw [hφψ, E.map_comp]; infer_instance
  -- conclude at `x`
  have := PresheafOfModules.evaluation_preservesColimitsOfShape.{u} R.obj K (op x)
  let P := isColimitOfPreserves E hs
  have hd : P.desc ((U ⋙ E).mapCocone c) = E.map φ :=
    (P.uniq _ _ fun k => by
      show E.map (s.ι.app k) ≫ E.map φ = E.map (U.map (c.ι.app k))
      rw [← E.map_comp, hφ]).symm
  have : IsIso (P.desc ((SheafOfModules.forget R ⋙ E).mapCocone c)) := hd ▸ hE
  exact ⟨IsColimit.ofPointIso P⟩

/-- **Sections over an affine object commute with colimits of quasi-coherent modules.** For an
object `x` of `𝒳` lying over an affine scheme, the functor `QCoh(𝒪_𝒳) ⥤ Mod_{𝒪(x)}` sending a
quasi-coherent module to its sections over `x` preserves small colimits. -/
theorem preservesColimitsOfSize_quasicoherentEvaluation {x : 𝒳}
    (hx : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x))) :
    PreservesColimitsOfSize.{u, u} ((SheafOfModules.isQuasicoherentOnSite.{v, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf)).ι ⋙ SheafOfModules.forget _ ⋙
        PresheafOfModules.evaluation _ (op x)) := by
  have := preservesColimitsOfSize_quasicoherentInclusion' B S hS p hp
  exact ⟨fun {K} _ => ⟨fun {F} => ⟨fun {c} hc => isColimit_mapCocone_evaluation_of_isAffine
    B S hS p hp
    (F ⋙ (SheafOfModules.isQuasicoherentOnSite (ringStructureSheafCore B S hS p hp .fppf)).ι)
    (fun k => (F.obj k).property) (isColimitOfPreserves _ hc) hx⟩⟩⟩

end AlgebraicGeometry.FibredSite

end
