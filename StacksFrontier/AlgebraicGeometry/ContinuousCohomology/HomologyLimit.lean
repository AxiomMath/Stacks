module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.ContinuityOfCohomology
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.RestrictedHomologyDelta

/-!
# Homology with finite coefficients as a limit over the finite quotients

Let `G` be a profinite group, `Λ` a finite ring and `M` a finite `Λ`-module with a continuous
action of `G`, with homology `H_i(G, M) = Hⁱ(G, M^∨)^∨`
(`Stacks.ContinuousCohomology.restrictedHomologyDelta`). The open normal subgroups `U` acting
trivially on `M` form a cofiltered poset (`Stacks.ContinuousCohomology.TrivialSubgroup`), and `M`
descends to a module over each finite quotient `G ⧸ U`. Then

* `Hⁱ(G, M^∨) = colim_U Hⁱ(G ⧸ U, M^∨)` along the inflation maps
  (`Stacks.ContinuousCohomology.isColimitCohomologyCoconeAb`), by continuity of cohomology;
* dually, `H_i(G, M) = lim_U H_i(G ⧸ U, M)` along the coinflation maps
  (`Stacks.ContinuousCohomology.isLimitHomologyCone`,
  `Stacks.ContinuousCohomology.homologyIsoLimit`), since a character of a filtered colimit is a
  compatible family of characters.

## Main definitions

* `Stacks.ContinuousCohomology.cohomologyDiagram`, `Stacks.ContinuousCohomology.cohomologyCocone`.
* `Stacks.ContinuousCohomology.homologyDiagram`, `Stacks.ContinuousCohomology.homologyCone`.

## Main results

* `Stacks.ContinuousCohomology.isColimitCohomologyCoconeAb`.
* `Stacks.ContinuousCohomology.isLimitHomologyCone`, `Stacks.ContinuousCohomology.homologyIsoLimit`.

## References

* [Stacks Project, Section 03VI](https://stacks.math.columbia.edu/tag/03VI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology

open scoped CharacterModule.MulOppositeAction

universe w

namespace Stacks.ContinuousCohomology

section Ext

variable {R : Type} [Ring R] {Γ : Type w} [Group Γ] [TopologicalSpace Γ]

/-- Morphisms of finite modules with continuous action agreeing on underlying elements are
equal. -/
theorem finiteTypeContinuousModule_hom_ext {X Y : FiniteTypeContinuousModule.{0, w, w} R Γ}
    {f g : X ⟶ Y} (h : ∀ x, f.hom.hom.hom.hom.hom x = g.hom.hom.hom.hom.hom x) : f = g :=
  ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _
    (Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext h)))))

end Ext

section Limit

variable (Λ : Type) [Ring Λ] [Finite Λ] {G : Type w} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  (M : FiniteTypeContinuousModule.{0, w, w} Λ G)

/-- **The open normal subgroups of `G` acting trivially on `M`**, ordered by inclusion. -/
abbrev TrivialSubgroup : Type w := {U : OpenNormalSubgroup G // ActsTrivially Λ U M}

/-- Two open normal subgroups acting trivially intersect in one. -/
instance : SemilatticeInf (TrivialSubgroup Λ M) :=
  Subtype.semilatticeInf fun {U V} hU _ g hg ↦ hU g ((inf_le_left : U ⊓ V ≤ U) hg)

/-- Some open normal subgroup acts trivially on `M`. -/
instance nonempty_trivialSubgroup : Nonempty (TrivialSubgroup Λ M) :=
  let ⟨U, hU⟩ := exists_actsTrivially Λ M
  ⟨⟨U, hU⟩⟩

variable {Λ M}

/-- The module `M` over the finite quotient `G ⧸ U`. -/
abbrev descendU (U : TrivialSubgroup Λ M) :
    FiniteTypeContinuousModule.{0, w, w} Λ (G ⧸ (U.1 : Subgroup G)) :=
  descend Λ U.1 M U.2

/-- The character dual `M^∨` over the finite quotient `G ⧸ U`. -/
abbrev dualU (U : TrivialSubgroup Λ M) :
    FiniteTypeContinuousModule.{0, w, w} Λᵐᵒᵖ (G ⧸ (U.1 : Subgroup G)) :=
  (finiteTypeContinuousModuleDual.{0, w, w} Λ (G ⧸ (U.1 : Subgroup G))).obj
    (Opposite.op (descendU U))

/-- The dual over `G ⧸ U`, restricted to `G ⧸ V`, is the dual over `G ⧸ V`: both restrict to
`M^∨` over `G`. -/
def dualTransition {U V : TrivialSubgroup Λ M} (h : V ≤ U) :
    (finiteTypeContinuousModuleRes.{0, w, w} Λᵐᵒᵖ (quotientMap (show V.1 ≤ U.1 from h))).obj
      (dualU U) ⟶ dualU V :=
  resPreimage Λᵐᵒᵖ (quotientMk V.1) (quotientMk_surjective V.1)
    (𝟙 ((finiteTypeContinuousModuleDual.{0, w, w} Λ G).obj (Opposite.op M)))

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- Restricted to `G`, the transition of duals is the identity. -/
theorem res_map_dualTransition {U V : TrivialSubgroup Λ M} (h : V ≤ U) :
    (finiteTypeContinuousModuleRes.{0, w, w} Λᵐᵒᵖ (quotientMk V.1)).map (dualTransition h) =
      𝟙 ((finiteTypeContinuousModuleDual.{0, w, w} Λ G).obj (Opposite.op M)) :=
  rfl

variable (M) in
/-- **The cohomology diagram** `U ↦ Hⁱ(G ⧸ U, M^∨)`, with the inflation maps. -/
def cohomologyDiagram (i : ℕ) : (TrivialSubgroup Λ M)ᵒᵖ ⥤ ModuleCat.{w} Λᵐᵒᵖ where
  obj U := ((cohomologyDelta Λᵐᵒᵖ (G ⧸ (U.unop.1 : Subgroup G))).functor i).obj (dualU U.unop)
  map {U V} f :=
    ((inflation Λᵐᵒᵖ (quotientMap (show V.unop.1 ≤ U.unop.1 from leOfHom f.unop))).app i).app
        (dualU U.unop) ≫
      ((cohomologyDelta Λᵐᵒᵖ (G ⧸ (V.unop.1 : Subgroup G))).functor i).map
        (dualTransition (leOfHom f.unop))
  map_id U := by
    have h := congrArg (fun η ↦ (η.app i).app (dualU U.unop))
      (inflation_comp_comparison_of_eq_id Λᵐᵒᵖ (quotientMap (le_refl U.unop.1))
        (fun g ↦ by induction g using QuotientGroup.induction_on with | H g => rfl))
    refine Eq.trans ?_ h
    congr 1
  map_comp {U V W} f g := by
    have hVU : V.unop.1 ≤ U.unop.1 := leOfHom f.unop
    have hWV : W.unop.1 ≤ V.unop.1 := leOfHom g.unop
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    let HW := (cohomologyDelta Λᵐᵒᵖ (G ⧸ (W.unop.1 : Subgroup G))).functor i
    let ττy := ((inflation Λᵐᵒᵖ (quotientMap hWV)).app i).app
      ((finiteTypeContinuousModuleRes.{0, w, w} Λᵐᵒᵖ (quotientMap hVU)).obj (dualU U.unop))
      (((inflation Λᵐᵒᵖ (quotientMap hVU)).app i).app (dualU U.unop) y)
    have h1 := inflation_quotientMap_quotientMap_apply Λᵐᵒᵖ hVU hWV i (dualU U.unop) y
    have h2 := inflation_naturality_apply (quotientMap hWV) i
      (dualTransition (leOfHom f.unop))
      (((inflation Λᵐᵒᵖ (quotientMap hVU)).app i).app (dualU U.unop) y)
    have h3 : (finiteTypeContinuousModuleRes.{0, w, w} Λᵐᵒᵖ (quotientMap hWV)).map
          (dualTransition (leOfHom f.unop)) ≫ dualTransition (leOfHom g.unop) =
        (resComparison Λᵐᵒᵖ (quotientMap hVU) (quotientMap hWV) (quotientMap (hWV.trans hVU))
          (quotientMap_quotientMap hVU hWV)).app (dualU U.unop) ≫
          dualTransition (leOfHom (f ≫ g).unop) :=
      finiteTypeContinuousModule_hom_ext fun _ ↦ rfl
    refine Eq.symm ((congrArg (HW.map (dualTransition (leOfHom g.unop))) h2).trans ?_)
    refine (ConcreteCategory.congr_hom (HW.map_comp _ _) ττy).symm.trans ?_
    refine (congrArg (fun φ ↦ HW.map φ ττy) h3).trans ?_
    refine (ConcreteCategory.congr_hom (HW.map_comp _ _) ττy).trans ?_
    exact congrArg (HW.map (dualTransition (leOfHom (f ≫ g).unop))) h1

variable (M) in
/-- **The inflation cocone** `Hⁱ(G ⧸ U, M^∨) ⟶ Hⁱ(G, M^∨)`. -/
def cohomologyCocone (i : ℕ) : Cocone (cohomologyDiagram M i) where
  pt := ((cohomologyDelta Λᵐᵒᵖ G).functor i).obj
    ((finiteTypeContinuousModuleDual.{0, w, w} Λ G).obj (Opposite.op M))
  ι :=
    { app U := ((inflation Λᵐᵒᵖ (quotientMk U.unop.1)).app i).app (dualU U.unop)
      naturality {U V} f := by
        have hVU : V.unop.1 ≤ U.unop.1 := leOfHom f.unop
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro y
        refine (inflation_naturality_apply (quotientMk V.unop.1) i
          (dualTransition (leOfHom f.unop))
          (((inflation Λᵐᵒᵖ (quotientMap hVU)).app i).app (dualU U.unop) y)).trans ?_
        refine (ConcreteCategory.congr_hom (congrArg ((cohomologyDelta Λᵐᵒᵖ G).functor i).map
          (res_map_dualTransition (leOfHom f.unop))) _).trans ?_
        refine (ConcreteCategory.congr_hom (((cohomologyDelta Λᵐᵒᵖ G).functor i).map_id _) _).trans
          ?_
        exact inflation_quotientMk_quotientMap_apply Λᵐᵒᵖ hVU i (dualU U.unop) y }

/-- The inflation cocone, as a cocone of abelian groups. -/
abbrev cohomologyCoconeAb (i : ℕ) :
    Cocone (cohomologyDiagram M i ⋙ forget₂ (ModuleCat.{w} Λᵐᵒᵖ) AddCommGrpCat.{w}) :=
  (forget₂ (ModuleCat.{w} Λᵐᵒᵖ) AddCommGrpCat.{w}).mapCocone (cohomologyCocone M i)

omit [TotallyDisconnectedSpace G] in
/-- The inflation cocone of abelian groups, on underlying elements, is inflation. -/
theorem forget_cohomologyCoconeAb_ι_app_apply (i : ℕ) (U : (TrivialSubgroup Λ M)ᵒᵖ)
    (z : (cohomologyDiagram M i).obj U) :
    ConcreteCategory.hom
        (((forget AddCommGrpCat.{w}).mapCocone (cohomologyCoconeAb (M := M) i)).ι.app U) z =
      ((inflation Λᵐᵒᵖ (quotientMk U.unop.1)).app i).app (dualU U.unop) z :=
  rfl

omit [TotallyDisconnectedSpace G] in
/-- The cohomology diagram of abelian groups, on underlying elements, is inflation followed by
the transition of duals. -/
theorem forget_cohomologyDiagram_map_apply (i : ℕ) {U V : (TrivialSubgroup Λ M)ᵒᵖ}
    (f : U ⟶ V) (z : (cohomologyDiagram M i).obj U) :
    ConcreteCategory.hom
        (((cohomologyDiagram M i ⋙ forget₂ (ModuleCat.{w} Λᵐᵒᵖ) AddCommGrpCat.{w}) ⋙
          forget AddCommGrpCat.{w}).map f) z =
      ((cohomologyDelta Λᵐᵒᵖ (G ⧸ (V.unop.1 : Subgroup G))).functor i).map
        (dualTransition (leOfHom f.unop))
        (((inflation Λᵐᵒᵖ (quotientMap (show V.unop.1 ≤ U.unop.1 from leOfHom f.unop))).app
          i).app (dualU U.unop) z) :=
  rfl

/-- Inflating from `G ⧸ V` agrees with transporting to the dual over `G ⧸ V` and inflating, as
elements of `Hⁱ(G, M^∨)`. -/
theorem inflation_eq_inflation_map_dualTransition (i : ℕ) (U₀ : TrivialSubgroup Λ M)
    (V : TrivialSubgroup Λ M) (h : V ≤ U₀)
    (y : ((cohomologyDelta Λᵐᵒᵖ (G ⧸ (V.1 : Subgroup G))).functor i).obj
      ((finiteTypeContinuousModuleRes.{0, w, w} Λᵐᵒᵖ (quotientMap (show V.1 ≤ U₀.1 from h))).obj
        (dualU U₀))) :
    @Eq (((cohomologyDelta Λᵐᵒᵖ G).functor i).obj
        ((finiteTypeContinuousModuleDual.{0, w, w} Λ G).obj (Opposite.op M)))
      (((inflation Λᵐᵒᵖ (quotientMk V.1)).app i).app
        ((finiteTypeContinuousModuleRes.{0, w, w} Λᵐᵒᵖ
        (quotientMap (show V.1 ≤ U₀.1 from h))).obj (dualU U₀)) y)
      (((inflation Λᵐᵒᵖ (quotientMk V.1)).app i).app (dualU V)
        (((cohomologyDelta Λᵐᵒᵖ (G ⧸ (V.1 : Subgroup G))).functor i).map (dualTransition h) y)) :=
  have h₁ := inflation_naturality_apply (quotientMk V.1) i (dualTransition h) y
  have h₂ := ConcreteCategory.congr_hom (congrArg ((cohomologyDelta Λᵐᵒᵖ G).functor i).map
    (res_map_dualTransition h)) (((inflation Λᵐᵒᵖ (quotientMk V.1)).app i).app
      ((finiteTypeContinuousModuleRes.{0, w, w} Λᵐᵒᵖ
        (quotientMap (show V.1 ≤ U₀.1 from h))).obj (dualU U₀)) y)
  have h₃ := ConcreteCategory.congr_hom (((cohomologyDelta Λᵐᵒᵖ G).functor i).map_id
    ((finiteTypeContinuousModuleDual.{0, w, w} Λ G).obj (Opposite.op M)))
    (((inflation Λᵐᵒᵖ (quotientMk V.1)).app i).app
      ((finiteTypeContinuousModuleRes.{0, w, w} Λᵐᵒᵖ
        (quotientMap (show V.1 ≤ U₀.1 from h))).obj (dualU U₀)) y)
  (h₁.trans (h₂.trans h₃)).symm

/-- Every element of `Hⁱ(G, M^∨)` comes from some finite quotient `G ⧸ U`. -/
theorem forget_cohomologyCoconeAb_surjective (i : ℕ)
    (x : ((forget AddCommGrpCat.{w}).mapCocone (cohomologyCoconeAb (M := M) i)).pt) :
    ∃ U xi,
      x = ((forget AddCommGrpCat.{w}).mapCocone (cohomologyCoconeAb (M := M) i)).ι.app U xi := by
  obtain ⟨U₀⟩ := (inferInstance : Nonempty (TrivialSubgroup Λ M))
  obtain ⟨V, h, y, hy⟩ := (inflationSurjective_and_inflationInjective Λᵐᵒᵖ (G := G) i).1 U₀.1
    (dualU U₀) x
  let V' : TrivialSubgroup Λ M := ⟨V, U₀.2.mono Λ h⟩
  refine ⟨Opposite.op V', ((cohomologyDelta Λᵐᵒᵖ (G ⧸ (V : Subgroup G))).functor i).map
    (dualTransition (show V' ≤ U₀ from h)) y, ?_⟩
  exact hy.symm.trans ((inflation_eq_inflation_map_dualTransition i U₀ V' h y).trans
    (forget_cohomologyCoconeAb_ι_app_apply i (Opposite.op V')
      (((cohomologyDelta Λᵐᵒᵖ (G ⧸ (V : Subgroup G))).functor i).map
        (dualTransition (show V' ≤ U₀ from h)) y)).symm)

/-- An element of `Hⁱ(G ⧸ U, M^∨)` dying in `Hⁱ(G, M^∨)` dies in some smaller finite quotient. -/
theorem forget_cohomologyCoconeAb_injective (i : ℕ) (U : (TrivialSubgroup Λ M)ᵒᵖ)
    (x y : ((cohomologyDiagram M i ⋙ forget₂ (ModuleCat.{w} Λᵐᵒᵖ) AddCommGrpCat.{w}) ⋙
      forget AddCommGrpCat.{w}).obj U)
    (hxy : ((forget AddCommGrpCat.{w}).mapCocone (cohomologyCoconeAb (M := M) i)).ι.app U x =
      ((forget AddCommGrpCat.{w}).mapCocone (cohomologyCoconeAb (M := M) i)).ι.app U y) :
    ∃ (k : _) (f : U ⟶ k),
      ((cohomologyDiagram M i ⋙ forget₂ (ModuleCat.{w} Λᵐᵒᵖ) AddCommGrpCat.{w}) ⋙
        forget AddCommGrpCat.{w}).map f x =
      ((cohomologyDiagram M i ⋙ forget₂ (ModuleCat.{w} Λᵐᵒᵖ) AddCommGrpCat.{w}) ⋙
        forget AddCommGrpCat.{w}).map f y := by
  replace hxy := (forget_cohomologyCoconeAb_ι_app_apply i U x).symm.trans
    (hxy.trans (forget_cohomologyCoconeAb_ι_app_apply i U y))
  have hxy' : ((inflation Λᵐᵒᵖ (quotientMk U.unop.1)).app i).app (dualU U.unop) (x - y) = 0 :=
    (map_sub _ x y).trans (sub_eq_zero.2 hxy)
  obtain ⟨V, h, hV⟩ := (inflationSurjective_and_inflationInjective Λᵐᵒᵖ (G := G) i).2 U.unop.1
    (dualU U.unop) (x - y) hxy'
  replace hV := sub_eq_zero.1 ((map_sub _ x y).symm.trans hV)
  let V' : TrivialSubgroup Λ M := ⟨V, U.unop.2.mono Λ h⟩
  refine ⟨Opposite.op V', (homOfLE (show V' ≤ U.unop from h)).op, ?_⟩
  exact (forget_cohomologyDiagram_map_apply i (homOfLE (show V' ≤ U.unop from h)).op x).trans
    ((congrArg (((cohomologyDelta Λᵐᵒᵖ (G ⧸ (V : Subgroup G))).functor i).map
      (dualTransition (show V' ≤ U.unop from h))) hV).trans
      (forget_cohomologyDiagram_map_apply i (homOfLE (show V' ≤ U.unop from h)).op y).symm)

variable (M) in
/-- **Continuity of cohomology**: `Hⁱ(G, M^∨) = colim_U Hⁱ(G ⧸ U, M^∨)`, the colimit over the open
normal subgroups acting trivially on `M`, along the inflation maps. -/
def isColimitCohomologyCoconeAb (i : ℕ) : IsColimit (cohomologyCoconeAb (M := M) i) := by
  have := reflectsColimitsOfShape_of_reflectsIsomorphisms (G := forget AddCommGrpCat.{w})
    (J := (TrivialSubgroup Λ M)ᵒᵖ)
  exact isColimitOfReflects (forget AddCommGrpCat.{w})
    (Types.FilteredColimit.isColimitOf' _ _ (forget_cohomologyCoconeAb_surjective i)
      (forget_cohomologyCoconeAb_injective i))

variable (M) in
/-- **The homology diagram** `U ↦ H_i(G ⧸ U, M) = Hⁱ(G ⧸ U, M^∨)^∨`, with the coinflation maps,
the duals of the inflation maps. -/
def homologyDiagram (i : ℕ) : TrivialSubgroup Λ M ⥤ ModuleCat.{w} Λ :=
  (cohomologyDiagram M i).rightOp ⋙ CharacterModule.moduleCatDualOfMulOppositeFunctor Λ

omit [TotallyDisconnectedSpace G] in
/-- The homology diagram at `U` is the homology of `G ⧸ U` with coefficients in `M`. -/
theorem homologyDiagram_obj (i : ℕ) (U : TrivialSubgroup Λ M) :
    (homologyDiagram M i).obj U =
      ((restrictedHomologyDelta Λ (ContinuousMonoidHom.id (G ⧸ (U.1 : Subgroup G)))).functor i).obj
        (descendU U) :=
  rfl

variable (M) in
/-- **The coinflation cone** `H_i(G, M) ⟶ H_i(G ⧸ U, M)`. -/
def homologyCone (i : ℕ) : Cone (homologyDiagram M i) :=
  (CharacterModule.moduleCatDualOfMulOppositeFunctor Λ).mapCone
    (coneRightOpOfCocone (cohomologyCocone M i))

omit [TotallyDisconnectedSpace G] in
/-- The vertex of the coinflation cone is the homology of `G` with coefficients in `M`. -/
theorem homologyCone_pt (i : ℕ) :
    (homologyCone M i).pt =
      ((restrictedHomologyDelta Λ (ContinuousMonoidHom.id G)).functor i).obj M :=
  rfl

section LimitAux

variable (i : ℕ)

/-- `ℚ/ℤ` as an abelian group in the universe of the modules. -/
abbrev circle : AddCommGrpCat.{w} := AddCommGrpCat.of (ULift.{w} (AddCircle (1 : ℚ)))

/-- A character, as a morphism of abelian groups to `ℚ/ℤ`. -/
def characterHom {A : AddCommGrpCat.{w}} (χ : CharacterModule A) : A ⟶ circle :=
  AddCommGrpCat.ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp χ)

/-- A morphism of abelian groups to `ℚ/ℤ`, as a character. -/
def homCharacter {A : AddCommGrpCat.{w}} (f : A ⟶ circle) : CharacterModule A :=
  AddEquiv.ulift.toAddMonoidHom.comp f.hom

/-- Characters of `Hⁱ(G, M^∨)` agreeing on the image of every finite quotient are equal. -/
theorem character_ext {χ χ' : CharacterModule (cohomologyCocone M i).pt}
    (h : ∀ U y, χ ((cohomologyCocone M i).ι.app U y) = χ' ((cohomologyCocone M i).ι.app U y)) :
    χ = χ' := by
  have := (isColimitCohomologyCoconeAb M i).hom_ext
    (f := characterHom χ) (f' := characterHom χ') fun U ↦
      AddCommGrpCat.ext fun y ↦ congrArg ULift.up (h U y)
  exact AddMonoidHom.ext fun x ↦ congrArg ULift.down (ConcreteCategory.congr_hom this x)

/-- A point of the homology diagram at `U`, as a character of `Hⁱ(G ⧸ U, M^∨)`. -/
abbrev toCharacter {U : (TrivialSubgroup Λ M)ᵒᵖ} (χ : (homologyDiagram M i).obj U.unop) :
    CharacterModule ((cohomologyDiagram M i).obj U) :=
  χ

/-- The compatible family of characters given by a point of a cone over the homology diagram,
as a cocone of abelian groups with vertex `ℚ/ℤ`. -/
def characterCocone (s : Cone (homologyDiagram M i)) (z : s.pt) :
    Cocone (cohomologyDiagram M i ⋙ forget₂ (ModuleCat.{w} Λᵐᵒᵖ) AddCommGrpCat.{w}) where
  pt := circle
  ι :=
    { app U := characterHom (toCharacter i (U := U) (s.π.app U.unop z))
      naturality {U _} f :=
        AddCommGrpCat.ext fun y ↦ congrArg ULift.up (congrArg
          (fun (φ : s.pt ⟶ (homologyDiagram M i).obj U.unop) ↦
            toCharacter i (U := U) (ConcreteCategory.hom φ z) y) (s.w f.unop)) }

/-- The character of `Hⁱ(G, M^∨)` induced by a compatible family. -/
def characterDesc (s : Cone (homologyDiagram M i)) (z : s.pt) :
    CharacterModule (cohomologyCocone M i).pt :=
  homCharacter ((isColimitCohomologyCoconeAb M i).desc (characterCocone i s z))

/-- The induced character restricts to the given characters. -/
theorem characterDesc_apply (s : Cone (homologyDiagram M i)) (z : s.pt) (U)
    (y : (cohomologyDiagram M i).obj U) :
    characterDesc i s z ((cohomologyCocone M i).ι.app U y) =
      toCharacter i (U := U) (s.π.app U.unop z) y :=
  congrArg ULift.down (ConcreteCategory.congr_hom
    ((isColimitCohomologyCoconeAb M i).fac (characterCocone i s z) U) y)

end LimitAux

variable (M) in
/-- **Homology is the limit of the homology of the finite quotients**:
`H_i(G, M) = lim_U H_i(G ⧸ U, M)`, along the coinflation maps. -/
def isLimitHomologyCone (i : ℕ) : IsLimit (homologyCone M i) where
  lift s := ModuleCat.ofHom
    { toFun := characterDesc i s
      map_add' z z' := character_ext i fun U y ↦ by
        refine (characterDesc_apply i s (z + z') U y).trans ?_
        refine (congrArg (fun χ ↦ toCharacter i (U := U) χ y)
          (map_add (s.π.app U.unop).hom z z')).trans ?_
        exact congrArg₂ (· + ·) (characterDesc_apply i s z U y).symm
          (characterDesc_apply i s z' U y).symm
      map_smul' r z := character_ext i fun U y ↦ by
        refine (characterDesc_apply i s (r • z) U y).trans ?_
        refine (congrArg (fun χ ↦ toCharacter i (U := U) χ y)
          (map_smul (s.π.app U.unop).hom r z)).trans ?_
        exact (characterDesc_apply i s z U (MulOpposite.op r • y)).symm.trans
          (congrArg (characterDesc i s z)
            (map_smul ((cohomologyCocone M i).ι.app U).hom (MulOpposite.op r) y)) }
  fac s U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact AddMonoidHom.ext fun y ↦ characterDesc_apply i s z (Opposite.op U) y
  uniq s m hm := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    refine character_ext (χ := m.hom z) i fun U y ↦ ?_
    refine Eq.trans ?_ (characterDesc_apply i s z U y).symm
    exact congrArg (fun (φ : s.pt ⟶ (homologyDiagram M i).obj U.unop) ↦
      toCharacter i (U := U) (ConcreteCategory.hom φ z) y) (hm U.unop)

variable (M) in
/-- **`H_i(G, M) ≅ lim_U H_i(G ⧸ U, M)`**, `U` running over the open normal subgroups acting
trivially on `M`. -/
def homologyIsoLimit (i : ℕ) :
    ((restrictedHomologyDelta Λ (ContinuousMonoidHom.id G)).functor i).obj M ≅
      limit (homologyDiagram M i) :=
  (isLimitHomologyCone M i).conePointUniqueUpToIso (limit.isLimit _)

end Limit

end Stacks.ContinuousCohomology

end
