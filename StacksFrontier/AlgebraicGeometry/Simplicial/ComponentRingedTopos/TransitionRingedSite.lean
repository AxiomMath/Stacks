module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.Transition
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.LocalizedMorphism

/-!
# The transitions of a simplicial site of case (A) as morphisms of ringed sites

In case (A) of Stacks 09WE the transition `f_φ : Sh(C_n) → Sh(C_m)` attached to `φ : [m] → [n]`
is the morphism of topoi of the morphism of sites given by the continuous functor
`u_φ : C_m ⥤ C_n`. Together with the transition of structure sheaves it is a morphism of ringed
sites (Stacks 03AD) between the component ringed sites, whose morphism of ringed topoi is the
transition morphism of ringed topoi.
-/

@[expose] public section

open CategoryTheory Stacks.Sheaves.ToposPullback

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- The ringed site of the component of degree `n` of a simplicial site. -/
noncomputable abbrev componentRingedSiteTransitionRingedSite (n : SimplexCategory) :
    AlgebraicGeometry.RingedSite.{u, u, u} where
  C := (S.componentRingedTopos O n).C
  J := (S.componentRingedTopos O n).J
  O := (S.componentRingedTopos O n).O

end CategoryTheory.SimplicialSiteSituation

namespace CategoryTheory.SimplicialSite

variable (C : SimplicialSite.{u})
  (O : Sheaf (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology CommRingCat.{u})

/-- **The transition of a simplicial site of case (A) as a morphism of ringed sites.** For
`φ : [m] → [n]` it is given by the continuous functor `u_φ : C_m ⥤ C_n` and the transition of
structure sheaves. -/
noncomputable def transitionRingedSiteHomTransitionRingedSite {m n : SimplexCategory} (φ : m ⟶ n) :
    AlgebraicGeometry.RingedSite.Hom
      ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentRingedSiteTransitionRingedSite O n)
      ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentRingedSiteTransitionRingedSite O m)
    where
  u := (C.underlying.map φ).toFunctor
  isMorphismOfSites := C.isMorphismOfSites φ
  fsharp :=
    let := (C.isMorphismOfSites φ).isContinuous
    ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionRingedToposHom O φ).fSharp ≫
      (restrictionCommRingIso (C.coverage m).toGrothendieck (C.coverage n).toGrothendieck
        (C.underlying.map φ).toFunctor
        ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentRingedTopos O n).O).hom

/-- The morphism of ringed topoi of the transition morphism of ringed sites is the transition
morphism of ringed topoi. -/
theorem transitionRingedSiteHom_ringedToposHom_transitionRingedSite {m n : SimplexCategory}
    (φ : m ⟶ n) :
    (C.transitionRingedSiteHomTransitionRingedSite O φ).ringedToposHom =
      (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionRingedToposHom O φ := by
  rw [AlgebraicGeometry.RingedSite.Hom.ringedToposHom]
  simp only [transitionRingedSiteHomTransitionRingedSite]
  rfl

end CategoryTheory.SimplicialSite
