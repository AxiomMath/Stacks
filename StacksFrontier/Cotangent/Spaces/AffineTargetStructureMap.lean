module

public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleFlat
public import StacksFrontier.Cotangent.Spaces.ConstantBaseRingPresheaf

/-!
# The structure map `Λ̲ ⟶ 𝒪_X` of a morphism to a scheme, chart by chart

Let `f : X ⟶ T` be a morphism from an algebraic space to (the algebraic space represented by) an
object `T` of the big fppf site, and let `Λ = Γ(T, 𝒪_T)`. On every étale scheme chart `U ⟶ X`
the morphism `f` induces a morphism of schemes `U ⟶ T` (`AlgebraicGeometry.Space.chartToBaseOfMap`)
and so a ring map `Λ → Γ(U, 𝒪_U)`. These form a map of presheaves of rings from the constant
presheaf `Λ` to `𝒪_X` (`AlgebraicGeometry.Space.chartBaseStructurePresheafMap`), whose
sheafification is a map `Λ̲ ⟶ 𝒪_X` from the constant sheaf
(`AlgebraicGeometry.Space.chartBaseStructureMap`); for `f` the identity of `T` this is the
structure map of `T` over `Λ`.

This file proves that the map obtained from the structure map of `T` by inverse image along `f`
is this one: under the identification `Λ̲_X ≅ f⁻¹Λ̲_T` of constant sheaves
(`AlgebraicGeometry.Space.constantSheafInverseImageIso`), the composite
`Λ̲_X ≅ f⁻¹Λ̲_T ⟶ f⁻¹𝒪_T ⟶ 𝒪_X` is `AlgebraicGeometry.Space.chartBaseStructureMap f`
(`AlgebraicGeometry.Space.constantSheafInverseImageIso_hom_comp_chartBaseStructureMap`). This is
the form of the tower `Λ̲ ⟶ f⁻¹𝒪_T ⟶ 𝒪_X` in which its sections over a chart `U` are the
`Λ`-algebra `Γ(U, 𝒪_U)` given by `f`.

The argument is the one of `StacksFrontier/Cotangent/Spaces/ConstantBaseRingPresheaf.lean` for
spaces over `Spec Λ`: both maps are adjoint to ring maps `Λ → Γ(X, 𝒪_X)` under the adjunction
between the constant sheaf and global sections, and these agree after restriction to every chart,
by the computation of `f♯` on a commutative diagram of charts (Stacks 03G8).

## Main definitions

* `AlgebraicGeometry.Space.chartBaseStructurePresheafMap`
* `AlgebraicGeometry.Space.chartBaseStructureMap`

## Main results

* `AlgebraicGeometry.Space.constantSheafInverseImageIso_hom_comp_eq`: for any map
  `σ : Λ̲_Y ⟶ 𝒪_Y`, the composite `Λ̲_X ≅ f⁻¹Λ̲_Y ⟶ f⁻¹𝒪_Y ⟶ 𝒪_X` is adjoint to the ring map
  `Λ → Γ(Y, 𝒪_Y) → Γ(X, 𝒪_X)`.
* `AlgebraicGeometry.Space.constantSheafInverseImageIso_hom_comp_chartBaseStructureMap`
* `AlgebraicGeometry.Space.toSheafify_comp_inverseImageStructureMap`: the same, on the sections
  of the constant presheaf.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 08VG](https://stacks.math.columbia.edu/tag/08VG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The chartwise structure map -/

section Chartwise

variable {T : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace T)

/-- **The chartwise structure map of `f : X ⟶ T`**: on an étale scheme chart `U` of `X`, the ring
map `Γ(T, 𝒪_T) → Γ(U, 𝒪_U)` of the morphism of schemes `U ⟶ T` induced by `f`. -/
def chartBaseStructurePresheafMap :
    (Functor.const (SmallEtale B S hS X.1)ᵒᵖ).obj (CommRingCat.of (baseRing B S hS T)) ⟶
      structurePresheaf B S hS X.1 where
  app U := Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (chartToBaseOfMap f U.unop)).op
  naturality {U V} m := by
    change 𝟙 _ ≫ Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (chartToBaseOfMap f V.unop)).op =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (chartToBaseOfMap f U.unop)).op ≫
        Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map m.unop.hom.left).op
    rw [Category.id_comp, ← Scheme.Γ.map_comp, ← op_comp, ← Functor.map_comp,
      chartToBaseOfMap_naturality]

/-- The constant sheaf of rings with value `Γ(T, 𝒪_T)` on the small étale site of `X`. -/
abbrev chartBaseConstantRing : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u} :=
  (constantSheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}).obj
    (CommRingCat.of (baseRing B S hS T))

/-- **The structure map `Λ̲ ⟶ 𝒪_X` of `f : X ⟶ T`**, `Λ = Γ(T, 𝒪_T)`: the map of sheaves of rings
induced by the chartwise structure maps. -/
def chartBaseStructureMap :
    chartBaseConstantRing (X := X) (T := T) ⟶ (smallEtaleRingedTopos B S hS X).O :=
  ((sheafificationAdjunction (SmallEtale.topology B S hS X.1) CommRingCat.{u}).homEquiv _ _).symm
    (chartBaseStructurePresheafMap f)

/-- The structure map is the sheafification of the chartwise structure maps. -/
theorem toSheafify_comp_chartBaseStructureMap :
    toSheafify (SmallEtale.topology B S hS X.1)
        ((Functor.const (SmallEtale B S hS X.1)ᵒᵖ).obj (CommRingCat.of (baseRing B S hS T))) ≫
      (chartBaseStructureMap f).hom = chartBaseStructurePresheafMap f := by
  have h := ((sheafificationAdjunction (SmallEtale.topology B S hS X.1)
    CommRingCat.{u}).homEquiv _ (smallEtaleRingedTopos B S hS X).O).apply_symm_apply
    (chartBaseStructurePresheafMap f)
  rw [Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app] at h
  exact h

end Chartwise

/-! ### The identity chart of `T` -/

section IdentityChart

variable (T : BigFppfOver B S hS)

/-- The identity chart of `T`, as an étale chart of the algebraic space represented by `T`. -/
abbrev schemeSpaceIdChart : SmallEtale B S hS (schemeSpace T).1 := idEtaleChart B S hS T

/-- The morphism of schemes from the identity chart of `T` to `T` is the identity. -/
theorem chartToBaseOfMap_id_schemeSpaceIdChart :
    chartToBaseOfMap (𝟙 (schemeSpace T)) (schemeSpaceIdChart T) = 𝟙 T :=
  yoneda.map_injective ((yoneda_map_chartToBaseOfMap _ _).trans
    ((Category.id_comp _).trans (yoneda.map_id T).symm))

/-- On the identity chart of `T`, the structure map of `T` is the identity of `Γ(T, 𝒪_T)`. -/
theorem chartBaseStructurePresheafMap_app_schemeSpaceIdChart_apply (a : baseRing B S hS T) :
    (chartBaseStructurePresheafMap (𝟙 (schemeSpace T))).app (op (schemeSpaceIdChart T)) a = a := by
  have h : (BigFppfOver.toScheme B S hS).map
      (chartToBaseOfMap (𝟙 (schemeSpace T)) (schemeSpaceIdChart T)) =
        𝟙 ((BigFppfOver.toScheme B S hS).obj T) :=
    (congrArg (BigFppfOver.toScheme B S hS).map (chartToBaseOfMap_id_schemeSpaceIdChart T)).trans
      ((BigFppfOver.toScheme B S hS).map_id T)
  have h2 : Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      (chartToBaseOfMap (𝟙 (schemeSpace T)) (schemeSpaceIdChart T))).op = 𝟙 _ :=
    (congrArg (fun g => Scheme.Γ.map (Quiver.Hom.op g)) h).trans
      ((congrArg Scheme.Γ.map (op_id (X := (BigFppfOver.toScheme B S hS).obj T))).trans
        (Scheme.Γ.map_id _))
  exact ConcreteCategory.congr_hom h2 a

end IdentityChart

/-! ### The structure map through an inverse image -/

section InverseImage

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) {M : CommRingCat.{u}}
  (σ : (constantSheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u}).obj M ⟶
    (smallEtaleRingedTopos B S hS Y).O)

/-- **The inverse image of a structure map, on global sections.** For `f : X ⟶ Y` and a map
`σ : M̲_Y ⟶ 𝒪_Y` from a constant sheaf, the composite `M̲_X ≅ f⁻¹M̲_Y ⟶ f⁻¹𝒪_Y ⟶ 𝒪_X` of the
identification of constant sheaves, the inverse image of `σ` and `f♯` is adjoint to the ring map
`M → Γ(Y, 𝒪_Y) → Γ(X, 𝒪_X)`: the ring map adjoint to `σ`, followed by `f♯` on global sections. -/
theorem constantSheafInverseImageIso_hom_comp_eq :
    (constantSheafInverseImageIso f).hom.app M ≫
        (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImageRing.map σ ≫
        (smallEtaleRingedToposHom B S hS f).fSharpInverseImage =
      ((constantSheafGlobalSectionsAdj X).homEquiv _ _).symm
        ((constantSheafGlobalSectionsAdj Y).homEquiv _ _ σ ≫
          (ringGlobalSections Y).map (smallEtaleRingedToposHom B S hS f).fSharp ≫
          (globalSectionsPushforwardIso f).hom.app _) := by
  let p := smallEtaleRingedToposHom B S hS f
  let adj1 := constantSheafGlobalSectionsAdj X
  let adj2 := ((constantSheafGlobalSectionsAdj Y).comp
      p.toToposHom.ringAdjunction).ofNatIsoRight (globalSectionsPushforwardIso f)
  have key : ∀ {O} (h : (constantSheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u} ⋙
        p.toToposHom.inverseImageRing).obj M ⟶ O),
      adj1.homEquiv _ _ ((adj1.leftAdjointUniq adj2).hom.app _ ≫ h) = adj2.homEquiv _ _ h := by
    intro O h
    rw [adj1.homEquiv_unit, adj2.homEquiv_unit, Functor.map_comp, ← Category.assoc,
      Adjunction.unit_leftAdjointUniq_hom_app]
  refine (adj1.homEquiv _ _).injective (((key _).trans ?_).trans (Equiv.apply_symm_apply _ _).symm)
  let adjY := constantSheafGlobalSectionsAdj Y
  let ra := p.toToposHom.ringAdjunction
  have hs : ra.homEquiv _ _ p.fSharpInverseImage = p.fSharp :=
    Equiv.apply_symm_apply _ _
  have h1 : ra.homEquiv _ _ (p.toToposHom.inverseImageRing.map σ ≫ p.fSharpInverseImage) =
      σ ≫ p.fSharp :=
    (ra.homEquiv_naturality_left _ _).trans (congrArg (σ ≫ ·) hs)
  have h2 : (adjY.comp ra).homEquiv _ _
      (p.toToposHom.inverseImageRing.map σ ≫ p.fSharpInverseImage) =
      adjY.homEquiv _ _ σ ≫ (ringGlobalSections Y).map p.fSharp :=
    (congrArg (fun e => e _ _ (p.toToposHom.inverseImageRing.map σ ≫ p.fSharpInverseImage))
        (Adjunction.comp_homEquiv adjY ra)).trans
      ((congrArg (adjY.homEquiv _ _) h1).trans (adjY.homEquiv_naturality_right _ _))
  exact (Adjunction.homEquiv_ofNatIsoRight_apply _ _ _).trans
    ((congrArg (· ≫ _) h2).trans (Category.assoc _ _ _))

end InverseImage

/-! ### Chart by chart -/

section Charts

variable {T : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace T)

/-- An étale scheme chart `U` of `X` over the identity chart of `T`: the commutative diagram of
charts over `f : X ⟶ T` whose vertical morphism is the morphism of schemes `U ⟶ T` induced by
`f`. -/
def affineTargetChartDiagram (U : SmallEtale B S hS X.1) :
    ChartDiagram B S hS X.1 (schemeSpace T).1 f.hom where
  U := U
  V := schemeSpaceIdChart T
  g := chartToBaseOfMap f U
  comm := (yoneda_map_chartToBaseOfMap f U).symm.trans (Category.comp_id _).symm

/-- The ring map `Γ(T, 𝒪_T) → Γ(X, 𝒪_X)` adjoint to the structure map of `T`, followed by `f♯` on
global sections. -/
def chartBaseGlobalStructureMap :
    CommRingCat.of (baseRing B S hS T) ⟶
      (ringGlobalSections X).obj (smallEtaleRingedTopos B S hS X).O :=
  (constantSheafGlobalSectionsAdj (schemeSpace T)).homEquiv _ _
      (chartBaseStructureMap (𝟙 (schemeSpace T))) ≫
    (ringGlobalSections (schemeSpace T)).map (smallEtaleRingedToposHom B S hS f).fSharp ≫
    (globalSectionsPushforwardIso f).hom.app _

/-- **The global structure map of `f`, restricted to a chart**, is the chart's own structure map
`Γ(U ⟶ T)`. -/
theorem chartBaseGlobalStructureMap_comp_res (U : SmallEtale B S hS X.1) :
    chartBaseGlobalStructureMap f ≫
        ringGlobalSectionsRes X (smallEtaleRingedTopos B S hS X).O U =
      (chartBaseStructurePresheafMap f).app (op U) := by
  let d := affineTargetChartDiagram f U
  let O := (smallEtaleRingedTopos B S hS X).O
  let G := (ringRestrictionEquiv X).inverse.obj O
  let p := smallEtaleRingedToposHom B S hS f
  let P := smallEtaleRingedToposHom_pushforwardRing B S hS f
  let st := chartBaseStructurePresheafMap (𝟙 (schemeSpace T))
  let Q : (p.toToposHom.pushforwardRing.obj O).obj.obj (op d.V) → _ := fun y =>
    ((ringRestrictionEquiv X).counitIso.hom.app O).hom.app (op U)
      (G.obj.map (baseChangeArrowOfChartDiagram B S hS f d).op ((P.hom.app G).hom.app (op d.V)
        ((p.toToposHom.pushforwardRing.map ((ringRestrictionEquiv X).counitIso.inv.app O)).hom.app
          (op d.V) y)))
  have hB := globalSectionsPushforwardIso_hom_app_comp_res f O d.V U
    (baseChangeArrowOfChartDiagram B S hS f d)
  have hN := ringGlobalSections_map_comp_res (schemeSpace T) p.fSharp d.V
  have hA : (constantSheafGlobalSectionsAdj (schemeSpace T)).homEquiv _ _
        (chartBaseStructureMap (𝟙 (schemeSpace T))) ≫ ringGlobalSectionsRes (schemeSpace T)
        (smallEtaleRingedTopos B S hS (schemeSpace T)).O d.V = st.app (op d.V) := by
    have e := ((constantSheafGlobalSectionsAdj (schemeSpace T)).homEquiv _ _).symm_apply_apply
      (chartBaseStructureMap (𝟙 (schemeSpace T)))
    exact (toSheafify_comp_constantSheafGlobalSectionsAdj_homEquiv_symm_app _ _ d.V).symm.trans
        ((congrArg (fun m => (toSheafify _ _).app (op d.V) ≫ m.hom.app (op d.V)) e).trans
          (congrArg (fun m => m.app (op d.V))
            (toSheafify_comp_chartBaseStructureMap (𝟙 (schemeSpace T)))))
  ext a
  have hC := fSharp_app_pushforwardRing_chartRes B S hS f d (st.app (op d.V) a)
  refine (ConcreteCategory.congr_hom hB (((ringGlobalSections (schemeSpace T)).map p.fSharp)
    ((constantSheafGlobalSectionsAdj (schemeSpace T)).homEquiv _ _
      (chartBaseStructureMap (𝟙 (schemeSpace T))) a))).trans ?_
  refine (congrArg Q (ConcreteCategory.congr_hom hN _)).trans ?_
  refine (congrArg (fun y => Q (p.fSharp.hom.app (op d.V) y))
    (ConcreteCategory.congr_hom hA a)).trans (hC.trans ?_)
  change Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (chartToBaseOfMap f U)).op
      ((st.app (op (schemeSpaceIdChart T))) a) =
    Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (chartToBaseOfMap f U)).op a
  exact congrArg _ (chartBaseStructurePresheafMap_app_schemeSpaceIdChart_apply T a)

/-- **The tower `Λ̲_X ≅ f⁻¹Λ̲_T ⟶ f⁻¹𝒪_T ⟶ 𝒪_X` composes to the structure map of `f`.** -/
theorem constantSheafInverseImageIso_hom_comp_chartBaseStructureMap :
    (constantSheafInverseImageIso f).hom.app (CommRingCat.of (baseRing B S hS T)) ≫
        (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImageRing.map
          (chartBaseStructureMap (𝟙 (schemeSpace T))) ≫
        (smallEtaleRingedToposHom B S hS f).fSharpInverseImage =
      chartBaseStructureMap f := by
  refine (constantSheafInverseImageIso_hom_comp_eq f _).trans ?_
  refine ObjectProperty.hom_ext _ (sheafify_hom_ext _ _ _
    (smallEtaleRingedTopos B S hS X).O.property ?_)
  refine NatTrans.ext (funext fun U => ?_)
  refine (toSheafify_comp_constantSheafGlobalSectionsAdj_homEquiv_symm_app X
    (chartBaseGlobalStructureMap f) U.unop).trans ?_
  refine (chartBaseGlobalStructureMap_comp_res f U.unop).trans ?_
  exact (congrArg (fun m => m.app U) (toSheafify_comp_chartBaseStructureMap f)).symm

/-- **The tower on the sections of the constant presheaf**: precomposed with the sheafification
map of the constant presheaf, `Λ̲_X ≅ f⁻¹Λ̲_T ⟶ f⁻¹𝒪_T ⟶ 𝒪_X` is, on every chart `U`, the ring
map `Γ(U ⟶ T)`. -/
theorem toSheafify_comp_inverseImageStructureMap :
    toSheafify (SmallEtale.topology B S hS X.1)
        ((Functor.const (SmallEtale B S hS X.1)ᵒᵖ).obj (CommRingCat.of (baseRing B S hS T))) ≫
      ((constantSheafInverseImageIso f).hom.app (CommRingCat.of (baseRing B S hS T)) ≫
        (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImageRing.map
          (chartBaseStructureMap (𝟙 (schemeSpace T))) ≫
        (smallEtaleRingedToposHom B S hS f).fSharpInverseImage).hom =
      chartBaseStructurePresheafMap f := by
  rw [constantSheafInverseImageIso_hom_comp_chartBaseStructureMap]
  exact toSheafify_comp_chartBaseStructureMap f

end Charts

end AlgebraicGeometry.Space

end
