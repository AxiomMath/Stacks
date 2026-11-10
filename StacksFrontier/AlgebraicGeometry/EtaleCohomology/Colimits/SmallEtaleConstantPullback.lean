module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LevelExtColimit
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ConstantSheafInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SpecializationMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystemIdentity

/-!
# The inverse image of the constant sheaf `ℤ` on small étale sites

For a morphism of schemes `f : X ⟶ Y`, the inverse image `f⁻¹ ℤ_Y` of the constant sheaf `ℤ` of
the small étale site of `Y` corepresents the sections over the base change of the final object
`Y ⟶ Y`, which is final in the small étale site of `X`; so does `ℤ_X`. The isomorphism matching
the two canonical sections is `Stacks.EtaleCohomology.ColimitBaseChange.constPullbackIso f`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Stacks.EtaleCohomology.ColimitBaseChange

universe u

open Stacks.WeakSites.ExtColimit

/-- The constant sheaf `ℤ` of the small étale site. -/
abbrev constZ (Y : Scheme.{u}) : Sheaf Y.smallEtaleTopology Ab.{u + 1} :=
  (constantSheaf Y.smallEtaleTopology Ab.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))

/-- The canonical section `1` of `ℤ` over an object. -/
abbrev constGen (Y : Scheme.{u}) (U : Y.Etale) : (constZ Y).obj.obj (op U) :=
  Stacks.ConstantSheaf.constantSheafSection Y.smallEtaleTopology Ab.{u + 1}
    (AddCommGrpCat.of (ULift ℤ)) U (ULift.up 1)

/-- The restriction of the canonical section `1` of `ℤ` along `V ⟶ U` is the canonical section
over `V`. -/
theorem constGen_restrict (Y : Scheme.{u}) {U V : Y.Etale} (h : V ⟶ U) :
    (constZ Y).obj.map h.op (constGen Y U) = constGen Y V :=
  ConcreteCategory.congr_hom (Stacks.ConstantSheaf.constantSheafSection_restrict
    Y.smallEtaleTopology Ab.{u + 1} (AddCommGrpCat.of (ULift ℤ)) h) (ULift.up 1)

/-- **`ℤ` corepresents the sections over a final object**, with its canonical section. -/
theorem isCorepresentingSection_constZ (Y : Scheme.{u}) {T : Y.Etale} (hT : IsTerminal T) :
    IsCorepresentingSection (constZ Y) T (constGen Y T) := by
  simpa only [Stacks.ConstantSheaf.constantSheafAdj_unit_app_eq] using
    isCorepresentingSection_constantSheaf.{u + 1, u, u + 1} Y.smallEtaleTopology hT

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The base change of the final object `Y ⟶ Y` along `f`, a final object of `X_étale`. -/
abbrev bcTop : X.Etale := (smallEtaleBaseChange f).obj (Scheme.Etale.mk (𝟙 Y))

/-- The object `bcTop f` is final in the small étale site of `X`. -/
def isTerminal_bcTop : IsTerminal (bcTop f) :=
  (isTerminalEtaleMkId Y).isTerminalObj (smallEtaleBaseChange f)

/-- The canonical section of `f⁻¹ ℤ_Y` over `bcTop f`: the image of `1` under the unit. -/
abbrev pbGen : ((smallEtalePullbackAb f).obj (constZ Y)).obj.obj (op (bcTop f)) :=
  ((smallEtaleAdjunctionAb f).unit.app (constZ Y)).hom.app (op (Scheme.Etale.mk (𝟙 Y)))
    (constGen Y (Scheme.Etale.mk (𝟙 Y)))

/-- `f⁻¹ ℤ_Y` corepresents the sections over `bcTop f`, with the canonical section `pbGen f`. -/
theorem isCorepresentingSection_pbGen :
    IsCorepresentingSection ((smallEtalePullbackAb f).obj (constZ Y)) (bcTop f) (pbGen f) :=
  (isCorepresentingSection_constZ Y (isTerminalEtaleMkId Y)).pullback (smallEtaleBaseChange f)
    (smallEtaleAdjunctionAb f)

/-- **`f⁻¹ ℤ_Y ≅ ℤ_X`**, matching the canonical sections over `bcTop f`. -/
def constPullbackIso : (smallEtalePullbackAb f).obj (constZ Y) ≅ constZ X :=
  (isCorepresentingSection_pbGen f).isoOfCorep
    (isCorepresentingSection_constZ X (isTerminal_bcTop f))

/-- The isomorphism `constPullbackIso f` sends `pbGen f` to the canonical section `1` of `ℤ_X`
over `bcTop f`. -/
theorem constPullbackIso_hom_apply :
    (constPullbackIso f).hom.hom.app (op (bcTop f)) (pbGen f) = constGen X (bcTop f) :=
  (isCorepresentingSection_pbGen f).isoOfCorep_hom_apply _

/-- `constPullbackIso f` sends every restriction of `pbGen f` to the canonical section `1`. -/
private theorem constPullbackIso_hom_apply_map {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Etale}
    (ρ : U ⟶ bcTop f) :
    (constPullbackIso f).hom.hom.app (op U)
      (((smallEtalePullbackAb f).obj (constZ Y)).obj.map ρ.op (pbGen f)) = constGen X U :=
  (ConcreteCategory.congr_hom ((constPullbackIso f).hom.hom.naturality ρ.op) (pbGen f)).trans
    ((congrArg _ (constPullbackIso_hom_apply f)).trans (constGen_restrict X ρ))

/-- The unit of the inverse image of abelian sheaves, on sections, commutes with restriction. -/
theorem unit_app_map {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Sheaf Y.smallEtaleTopology Ab.{u + 1})
    {U V : Y.Etale} (ρ : V ⟶ U) (x : M.obj.obj (op U)) :
    ((smallEtaleAdjunctionAb f).unit.app M).hom.app (op V) (M.obj.map ρ.op x) =
      ((smallEtalePullbackAb f).obj M).obj.map ((smallEtaleBaseChange f).map ρ).op
        (((smallEtaleAdjunctionAb f).unit.app M).hom.app (op U) x) :=
  ConcreteCategory.congr_hom (((smallEtaleAdjunctionAb f).unit.app M).hom.naturality ρ.op) x

/-- The unit of the inverse image of abelian sheaves, on sections, is natural in the sheaf. -/
theorem map_unit_app {X Y : Scheme.{u}} (f : X ⟶ Y) {M N : Sheaf Y.smallEtaleTopology Ab.{u + 1}}
    (φ : M ⟶ N) (U : Y.Etale) (x : M.obj.obj (op U)) :
    ((smallEtalePullbackAb f).map φ).hom.app (op ((smallEtaleBaseChange f).obj U))
        (((smallEtaleAdjunctionAb f).unit.app M).hom.app (op U) x) =
      ((smallEtaleAdjunctionAb f).unit.app N).hom.app (op U) (φ.hom.app (op U) x) :=
  (ConcreteCategory.congr_hom
    (congrArg (fun k => k.hom.app (op U)) ((smallEtaleAdjunctionAb f).unit.naturality φ)) x).symm

/-- On sections over `U`, the inverse of the comparison of direct images of abelian sheaves along
`h = g ≫ f` with the composite of the direct images along `g` and `f` is the restriction along
the inverse of the comparison of base changes `smallEtaleBaseChangeComp'`. -/
theorem smallEtalePushforwardAbCompIso'_inv_app_hom_app {W X Y : Scheme.{u}} (g : W ⟶ X)
    (f : X ⟶ Y) (h : W ⟶ Y) (hh : h = g ≫ f) (N : Sheaf W.smallEtaleTopology Ab.{u + 1})
    (U : Y.Etale) :
    ((smallEtalePushforwardAbCompIso' g f h hh).inv.app N).hom.app (op U) =
      N.obj.map ((smallEtaleBaseChangeComp' g f h hh).inv.app U).op := by
  have hiso : (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U)).mapIso
      ((smallEtalePushforwardAbCompIso' g f h hh).app N) =
      N.obj.mapIso ((smallEtaleBaseChangeComp' g f h hh).app U).op :=
    Iso.ext (smallEtalePushforwardComp'_hom_app_hom_app g f h hh Ab.{u + 1} N (op U))
  exact congrArg Iso.inv hiso

/-- **The comparisons `f⁻¹ ℤ ≅ ℤ` form a cocycle** with the composition comparison of inverse
images. -/
theorem constPullbackIso_comp {W X Y : Scheme.{u}} (g : W ⟶ X) (f : X ⟶ Y) (h : W ⟶ Y)
    (hh : h = g ≫ f) :
    (smallEtalePullbackAb g).map (constPullbackIso f).hom ≫ (constPullbackIso g).hom =
      (smallEtalePullbackAbCompIso' g f h hh).hom.app (constZ Y) ≫ (constPullbackIso h).hom := by
  refine ((isCorepresentingSection_pbGen f).pullback (smallEtaleBaseChange g)
    (smallEtaleAdjunctionAb g)).hom_ext ?_
  have hT : IsTerminal (Scheme.Etale.mk (𝟙 X)) := isTerminalEtaleMkId X
  have hL : (constPullbackIso g).hom.hom.app (op ((smallEtaleBaseChange g).obj (bcTop f)))
      (((smallEtalePullbackAb g).map (constPullbackIso f).hom).hom.app
        (op ((smallEtaleBaseChange g).obj (bcTop f)))
        (((smallEtaleAdjunctionAb g).unit.app _).hom.app (op (bcTop f)) (pbGen f))) =
      constGen W ((smallEtaleBaseChange g).obj (bcTop f)) := by
    rw [map_unit_app, constPullbackIso_hom_apply, ← constGen_restrict X (hT.from (bcTop f)),
      unit_app_map]
    exact constPullbackIso_hom_apply_map g ((smallEtaleBaseChange g).map (hT.from (bcTop f)))
  have hR : (constPullbackIso h).hom.hom.app (op ((smallEtaleBaseChange g).obj (bcTop f)))
      (((smallEtalePullbackAbCompIso' g f h hh).hom.app (constZ Y)).hom.app
        (op ((smallEtaleBaseChange g).obj (bcTop f)))
        (((smallEtaleAdjunctionAb g).unit.app _).hom.app (op (bcTop f)) (pbGen f))) =
      constGen W ((smallEtaleBaseChange g).obj (bcTop f)) := by
    have s1 := (homEquiv_hom_app_apply (smallEtaleBaseChange g) (smallEtaleAdjunctionAb g)
      ((smallEtalePullbackAbCompIso' g f h hh).hom.app (constZ Y)) (pbGen f)).symm
    have e2 : (smallEtaleAdjunctionAb g).homEquiv _ _
        ((smallEtalePullbackAbCompIso' g f h hh).hom.app (constZ Y)) =
        ((smallEtaleAdjunctionAb f).homEquiv _ _).symm
          ((smallEtaleAdjunctionAb h).unit.app (constZ Y) ≫
            (smallEtalePushforwardAbCompIso' g f h hh).inv.app _) :=
      Stacks.EtaleCohomology.TransitionBaseChange.homEquiv_leftAdjointCompIso_hom_app _ _ _ _ _
    have s3 := homEquiv_symm_hom_app_unit_apply (smallEtaleBaseChange f) (smallEtaleAdjunctionAb f)
      ((smallEtaleAdjunctionAb h).unit.app (constZ Y) ≫
          (smallEtalePushforwardAbCompIso' g f h hh).inv.app _)
      (constGen Y (Scheme.Etale.mk (𝟙 Y)))
    have s4 : ((smallEtaleAdjunctionAb h).unit.app (constZ Y) ≫
          (smallEtalePushforwardAbCompIso' g f h hh).inv.app _).hom.app
          (op (Scheme.Etale.mk (𝟙 Y))) (constGen Y (Scheme.Etale.mk (𝟙 Y))) =
        ((smallEtalePullbackAb h).obj (constZ Y)).obj.map
          ((smallEtaleBaseChangeComp' g f h hh).inv.app (Scheme.Etale.mk (𝟙 Y))).op (pbGen h) := by
      change ((smallEtalePushforwardAbCompIso' g f h hh).inv.app _).hom.app
        (op (Scheme.Etale.mk (𝟙 Y))) (pbGen h) = _
      rw [smallEtalePushforwardAbCompIso'_inv_app_hom_app]
      rfl
    refine (congrArg ((constPullbackIso h).hom.hom.app
      (op ((smallEtaleBaseChange g).obj (bcTop f)))) s1).trans ?_
    refine (congrArg (fun φ => (constPullbackIso h).hom.hom.app
      (op ((smallEtaleBaseChange g).obj (bcTop f))) (φ.hom.app (op (bcTop f)) (pbGen f)))
      e2).trans ?_
    refine (congrArg ((constPullbackIso h).hom.hom.app _) s3).trans ?_
    refine (congrArg ((constPullbackIso h).hom.hom.app _) s4).trans ?_
    exact constPullbackIso_hom_apply_map h _
  exact hL.trans hR.symm

end Stacks.EtaleCohomology.ColimitBaseChange

end
