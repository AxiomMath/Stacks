module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFinitePresentationProjectiveSectionsAlongFibre

/-!
# The pointed elementary form of Stacks 05KW inside the big fppf site

`AlgebraicGeometry.Space.exists_isAffine_etale_hom_projective_sections_along_fibre` reads the case
of schemes of Stacks 0CVZ — Stacks 05KW — inside the big fppf site, keeping the containment of
the fibre in the image of the upper chart.  This file reads the sharper, *pointed elementary* form
`AlgebraicGeometry.exists_elementary_pointed_projective_cover` inside the site: the étale
neighbourhood of the base point is elementary, that is, induces an isomorphism of residue fields
at its distinguished point, and every point of the fibre is the image of a point of the upper
chart lying over that distinguished point.

Both refinements are what the proof of Stacks 0CWC needs to compare the fibre of the base change
`X ×_Y E'` over the distinguished point with the upper chart: points of a fibre product over a
point with trivial residue field extension are determined by their image in the other factor,
`AlgebraicGeometry.Space.eq_of_pointsMap_eq_of_isPullback_of_isIso_residueFieldMap`.

## Main results

* `AlgebraicGeometry.Space.exists_isAffine_elementary_etale_hom_projective_sections_along_fibre`.

## References

* [Stacks Project, Tag 05KW](https://stacks.math.columbia.edu/tag/05KW)
* [Stacks Project, Tag 0CWC](https://stacks.math.columbia.edu/tag/0CWC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 05KW, pointed and elementary, inside the big fppf site.** Let `h : D ⟶ E` be a
morphism of the site whose morphism of schemes is of finite presentation, `G` a quasi-coherent
module of finite presentation on `D` flat over `E` along the fibre over `ε`. Then there are affine
objects `D'`, `E'` of the site, étale morphisms `p : D' ⟶ D`, `q : E' ⟶ E`, a morphism
`k : D' ⟶ E'` over `h` and a point `ε'` of `E'` over `ε` at which `q` induces an isomorphism of
residue fields, such that every point of the fibre over `ε` is `p(d)` for a point `d` with
`k(d) = ε'`, and the sections of `p^* G` are projective over `Γ(E', 𝒪)`. -/
theorem exists_isAffine_elementary_etale_hom_projective_sections_along_fibre
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (D E : BigFppfOver B S hS) (h : D ⟶ E)
    (G : ((BigFppfOver.toScheme B S hS).obj D).Modules)
    (ε : (BigFppfOver.toScheme B S hS).obj E)
    (hfp : FinitePresentation ((BigFppfOver.toScheme B S hS).map h))
    (hqc : G.IsQuasicoherent) (hGfp : G.IsFinitePresentation)
    (hflat : ∀ δ : (BigFppfOver.toScheme B S hS).obj D,
      (BigFppfOver.toScheme B S hS).map h δ = ε →
      AlgebraicGeometry.IsFlatOverAt
        (LocallyRingedSpace.forgetToSheafedSpace.map
          ((BigFppfOver.toScheme B S hS).map h).toLRSHom) G δ) :
    ∃ (D' E' : BigFppfOver B S hS) (p : D' ⟶ D) (q : E' ⟶ E) (k : D' ⟶ E')
      (ε' : (BigFppfOver.toScheme B S hS).obj E'),
      Etale ((BigFppfOver.toScheme B S hS).map p) ∧
      Etale ((BigFppfOver.toScheme B S hS).map q) ∧
      k ≫ q = p ≫ h ∧
      (BigFppfOver.toScheme B S hS).map q ε' = ε ∧
      IsIso (((BigFppfOver.toScheme B S hS).map q).residueFieldMap ε') ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj D') ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj E') ∧
      (∀ δ : (BigFppfOver.toScheme B S hS).obj D,
        (BigFppfOver.toScheme B S hS).map h δ = ε →
        ∃ d : (BigFppfOver.toScheme B S hS).obj D',
          (BigFppfOver.toScheme B S hS).map p d = δ ∧
          (BigFppfOver.toScheme B S hS).map k d = ε') ∧
      (let M := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map p)).obj G
       letI : Module Γ((BigFppfOver.toScheme B S hS).obj E', ⊤) Γ(M, ⊤) :=
         Module.compHom Γ(M, ⊤) ((BigFppfOver.toScheme B S hS).map k).appTop.hom
       Module.Projective Γ((BigFppfOver.toScheme B S hS).obj E', ⊤) Γ(M, ⊤)) := by
  have := hqc
  have := hGfp
  have hID : ExistsElementaryEtaleNeighborhoodProjectiveSections.{u} := by
    intro X S f _ F _ _ x hflat
    exact exists_elementaryEtaleNeighborhood_projective_sections_of_isFlatOverAt f F x hflat
  obtain ⟨N, hNel, hNaff, Z, hZaff, m, g, hgE, hcomm, hcov, hproj⟩ :=
    exists_elementary_pointed_projective_cover hID
      ((BigFppfOver.toScheme B S hS).map h) G ε hfp fun x =>
        hflat _ (by
          have hx : ((BigFppfOver.toScheme B S hS).map h).fiberι ε x ∈
              (BigFppfOver.toScheme B S hS).map h ⁻¹' {ε} := by
            rw [← Scheme.Hom.range_fiberι]
            exact Set.mem_range_self x
          exact hx)
  have := hNaff
  have := hZaff
  have := hgE
  have hZsize : B.Contains Z :=
    (Scheme.size_le_of_locallyOfFiniteType g).trans_lt D.left.property
  have hNsize : B.Contains N.scheme :=
    (Scheme.size_le_of_locallyOfFiniteType N.toBase).trans_lt E.left.property
  have hbaseD : (BigFppfOver.toScheme B S hS).map h ≫ B.inclusion.map E.hom =
      B.inclusion.map D.hom :=
    congrArg (fun w => B.inclusion.map w) (Over.w h)
  let D' : BigFppfOver B S hS :=
    Over.mk ((ObjectProperty.homMk (g ≫ B.inclusion.map D.hom) :
      B.obj hZsize ⟶ B.obj hS))
  let E' : BigFppfOver B S hS :=
    Over.mk ((ObjectProperty.homMk (N.toBase ≫ B.inclusion.map E.hom) :
      B.obj hNsize ⟶ B.obj hS))
  have hk : (ObjectProperty.homMk m : B.obj hZsize ⟶ B.obj hNsize) ≫ E'.hom = D'.hom := by
    refine ObjectProperty.hom_ext _ ?_
    change m ≫ N.toBase ≫ B.inclusion.map E.hom = g ≫ B.inclusion.map D.hom
    rw [← Category.assoc, hcomm, Category.assoc, hbaseD]
  refine ⟨D', E',
      Over.homMk (ObjectProperty.homMk g : B.obj hZsize ⟶ D.left) rfl,
      Over.homMk (ObjectProperty.homMk N.toBase : B.obj hNsize ⟶ E.left) rfl,
      Over.homMk (ObjectProperty.homMk m : B.obj hZsize ⟶ B.obj hNsize) hk, N.point,
      hgE, N.etale_toBase, ?_, N.map_point, (N.isElementary_iff).1 hNel, hZaff, hNaff,
      fun δ hδ => ?_, hproj⟩
  · refine (BigFppfOver.toScheme B S hS).map_injective ?_
    rw [Functor.map_comp, Functor.map_comp]
    exact hcomm
  · obtain ⟨d, hd, hdk⟩ := hcov ((((BigFppfOver.toScheme B S hS).map h).fiberHomeo ε).symm
      ⟨δ, hδ⟩)
    refine ⟨d, ?_, hdk⟩
    change g d = δ
    rw [hd, Scheme.Hom.fiberι_fiberHomeo_symm]

end AlgebraicGeometry.Space

end
