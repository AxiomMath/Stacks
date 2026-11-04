module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.LocalSchemeAffineLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.StrictHenselizationStalkSections

/-!
# Sections over the local scheme at a point, as a colimit of sections over neighbourhoods

Let `X` be a scheme, `η` a point and `g : Spec 𝒪_{X,η} ⟶ X` the canonical morphism. The functor
`Ψ = Γ(Spec 𝒪_{X,η}, g⁻¹ -)` on abelian sheaves on `X_ét` receives, for every open neighbourhood
`V` of `η`, the restriction `θ_V : 𝓖(V) ⟶ Γ(Spec 𝒪_{X,η}, g⁻¹𝓖)` along `Spec 𝒪_{X,η} ⟶ V`. These
are compatible, and exhibit `Ψ(𝓖)` as the filtered colimit of the `𝓖(V)`: every section over the
local scheme comes from some `V`, and a section over `V` restricting to zero vanishes on a smaller
neighbourhood. This is Stacks 09YQ in degree zero
(`Stacks.EtaleCohomology.LimitExt.limitSectionsAb_colimit`), at the directed limit
`AlgebraicGeometry.Scheme.isLimitLocalAffineCone`.

## Main definitions

* `AlgebraicGeometry.Scheme.localSchemeSections η`: the functor `Ψ`.
* `AlgebraicGeometry.Scheme.localSchemeSectionsι η V hV`: the restriction `θ_V`.

## Main results

* `AlgebraicGeometry.Scheme.localSchemeSectionsι_comp`: compatibility of the `θ_V`.
* `AlgebraicGeometry.Scheme.exists_localSchemeSectionsι_app_eq`: every section of `Ψ(𝓖)` comes
  from a neighbourhood.
* `AlgebraicGeometry.Scheme.exists_map_eq_zero_of_localSchemeSectionsι_app_eq_zero`: a section
  dying in `Ψ(𝓖)` dies on a smaller neighbourhood.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} (η : X)

/-- **Sections over the local scheme at `η`**: `𝓖 ↦ Γ(Spec 𝒪_{X,η}, g⁻¹𝓖)` with
`g = X.fromSpecStalk η`. -/
abbrev localSchemeSections :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  smallEtalePullbackAb (X.fromSpecStalk η) ⋙
    Sheaf.Γ (Spec (X.presheaf.stalk η)).smallEtaleTopology AddCommGrpCat.{u + 1}

/-- **The restriction to the local scheme** `𝓖(V) ⟶ Γ(Spec 𝒪_{X,η}, g⁻¹𝓖)` for an open
neighbourhood `V` of `η`, along the canonical morphism `Spec 𝒪_{X,η} ⟶ V`. -/
def localSchemeSectionsι (V : X.Opens) (hV : η ∈ V) :
    (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op ((opensToEtale X).obj V)) ⟶ localSchemeSections η :=
  smallEtaleSectionsPullbackAb (X.fromSpecStalk η) ((opensToEtale X).obj V)
    (Scheme.Opens.fromSpecStalkOfMem (X := X) V η hV) (Scheme.Opens.fromSpecStalkOfMem_ι _ _ _)

/-- **The restrictions to the local scheme are compatible.** -/
theorem localSchemeSectionsι_comp (V V' : X.Opens) (hV : η ∈ V) (hV' : η ∈ V') (h : V' ≤ V) :
    (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((opensToEtale X).map (homOfLE h)).op ≫ localSchemeSectionsι η V' hV' =
        localSchemeSectionsι η V hV := by
  have hr : (Scheme.Opens.fromSpecStalkOfMem (X := X) V' η hV' ≫ X.homOfLE h) ≫ V.ι =
      X.fromSpecStalk η := by
    rw [Category.assoc, Scheme.homOfLE_ι, Scheme.Opens.fromSpecStalkOfMem_ι]
  have heq : Scheme.Opens.fromSpecStalkOfMem (X := X) V' η hV' ≫ X.homOfLE h =
      Scheme.Opens.fromSpecStalkOfMem (X := X) V η hV := by
    rw [← cancel_mono (Scheme.Opens.ι (X := X) V), hr, Scheme.Opens.fromSpecStalkOfMem_ι]
  exact (map_comp_smallEtaleSectionsPullbackAb (X.fromSpecStalk η) ((opensToEtale X).obj V')
    (Scheme.Opens.fromSpecStalkOfMem (X := X) V' η hV') ((opensToEtale X).map (homOfLE h))
    (Scheme.Opens.fromSpecStalkOfMem_ι _ _ _) hr).trans
      (smallEtaleSectionsPullbackAb_congr _ _ _ _ _ heq)

/-- The restriction to the local scheme at a level of `localAffineEtaleDiagram` is the
restriction to the limit of `Stacks.EtaleCohomology.LimitExt.limitSectionsAb`, read as a global
section. -/
theorem localSchemeSectionsι_app_eq_limitSectionsAb (V₀ : AffineOpenNhds X η)
    (i : LocalAffineIndex η V₀) (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (localSchemeSectionsι η (OrderDual.ofDual i).1 (OrderDual.ofDual i).2.2.1).app G =
      LimitExt.limitSectionsAb (localAffineEtaleDiagram η V₀) (localAffineCone η V₀)
          (localAffineCone_π_app_comp η V₀) G (op i) ≫
        (Sheaf.ΓNatIsoSheafSections (Spec (X.presheaf.stalk η)).smallEtaleTopology
          AddCommGrpCat.{u + 1} (isTerminalEtaleMkId _)).inv.app
          ((smallEtalePullbackAb (X.fromSpecStalk η)).obj G) :=
  rfl

/-- **Every section over the local scheme comes from a neighbourhood.** -/
theorem exists_localSchemeSectionsι_app_eq (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (y : (localSchemeSections η).obj G) :
    ∃ (V : X.Opens) (hV : η ∈ V) (x : G.obj.obj (op ((opensToEtale X).obj V))),
      (localSchemeSectionsι η V hV).app G x = y := by
  obtain ⟨V₀, -⟩ := exists_affineOpenNhds_le X η ⊤
  let e := (Sheaf.ΓNatIsoSheafSections (Spec (X.presheaf.stalk η)).smallEtaleTopology
    AddCommGrpCat.{u + 1} (isTerminalEtaleMkId _)).app
      ((smallEtalePullbackAb (X.fromSpecStalk η)).obj G)
  obtain ⟨i, x, hx⟩ := (LimitExt.limitSectionsAb_colimit (localAffineEtaleDiagram η V₀)
    (localAffineCone η V₀) (localAffineCone_π_app_comp η V₀) G
    (isLimitLocalAffineCone η V₀)).1 (e.hom y)
  refine ⟨(OrderDual.ofDual i).1, (OrderDual.ofDual i).2.2.1, x, ?_⟩
  exact (congrArg e.inv hx).trans (e.hom_inv_id_apply y)

/-- **A section dying over the local scheme dies on a smaller neighbourhood.** -/
theorem exists_map_eq_zero_of_localSchemeSectionsι_app_eq_zero
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (V : X.Opens) (hV : η ∈ V)
    (x : G.obj.obj (op ((opensToEtale X).obj V)))
    (hx : (localSchemeSectionsι η V hV).app G x = 0) :
    ∃ (V' : X.Opens) (h : V' ≤ V), η ∈ V' ∧
      G.obj.map ((opensToEtale X).map (homOfLE h)).op x = 0 := by
  obtain ⟨V₀, hV₀⟩ := exists_affineOpenNhds_le X η ⟨V, hV⟩
  have hV₀V : V₀.obj.1 ≤ V := hV₀
  let e := (Sheaf.ΓNatIsoSheafSections (Spec (X.presheaf.stalk η)).smallEtaleTopology
    AddCommGrpCat.{u + 1} (isTerminalEtaleMkId _)).app
      ((smallEtalePullbackAb (X.fromSpecStalk η)).obj G)
  let x₀ := G.obj.map ((opensToEtale X).map (homOfLE hV₀V)).op x
  have hx₀ : (localSchemeSectionsι η V₀.obj.1 V₀.obj.2).app G x₀ = 0 := by
    rwa [← localSchemeSectionsι_comp η V V₀.obj.1 hV V₀.obj.2 hV₀V] at hx
  have h0 : LimitExt.limitSectionsAb (localAffineEtaleDiagram η V₀) (localAffineCone η V₀)
      (localAffineCone_π_app_comp η V₀) G (op ⊥) x₀ = 0 := by
    have h1 : e.inv (LimitExt.limitSectionsAb (localAffineEtaleDiagram η V₀)
        (localAffineCone η V₀) (localAffineCone_π_app_comp η V₀) G (op ⊥) x₀) = 0 := hx₀
    exact (e.inv_hom_id_apply _).symm.trans ((congrArg e.hom h1).trans (map_zero _))
  obtain ⟨j, d, hj⟩ := (LimitExt.limitSectionsAb_colimit (localAffineEtaleDiagram η V₀)
    (localAffineCone η V₀) (localAffineCone_π_app_comp η V₀) G
    (isLimitLocalAffineCone η V₀)).2.1 ⊥ x₀ h0
  have hj' : (OrderDual.ofDual j).1 ≤ V := (OrderDual.ofDual j).2.2.2.trans hV₀V
  refine ⟨(OrderDual.ofDual j).1, hj', (OrderDual.ofDual j).2.2.1, ?_⟩
  have e1 : ((opensToEtale X).map (homOfLE hj')).op =
      ((opensToEtale X).map (homOfLE hV₀V)).op ≫
        ((opensToEtale X).map (homOfLE (OrderDual.ofDual j).2.2.2)).op := by
    rw [← op_comp, ← Functor.map_comp]
    rfl
  rw [e1, Functor.map_comp, ConcreteCategory.comp_apply]
  exact hj

end AlgebraicGeometry.Scheme

end
