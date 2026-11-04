module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekGeometricStalkProperBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitEtaleSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.StrictHenselizationFibreSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.SectionPullbackComp
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationConeBase
public import StacksFrontier.CategoryTheory.Sites.PullbackSectionsComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardBoundedSite
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.FiniteSurjectiveDescent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sections over the geometric fibre of a proper morphism come from étale neighbourhoods

Let `f : X ⟶ Y` be a proper morphism of a big étale site and `ȳ` a geometric point of `Y`. This
file proves that every global section over the geometric fibre `X_ȳ` of the inverse image of a
sheaf on the small étale site of `X` is pulled back from a section over `X_V = V ×_Y X` for some
étale neighbourhood `(V, v̄)` of `ȳ`. This is the surjectivity half of proper base change in
degree `0` ([Stacks, Tag 095T](https://stacks.math.columbia.edu/tag/095T)), used for the stalks of
`f_!` ([Stacks, Tag 0F76](https://stacks.math.columbia.edu/tag/0F76)).

The proof follows the source. A section over `X_ȳ` extends to the base change of `X` to the strict
henselization `Spec(𝒪^{sh}_{Y,ȳ})` (Stacks 0A3S and 0A3I). That base change is the limit of the
base changes `X_V` over a small cofinal family of affine étale neighbourhoods of `ȳ`, which are
quasi-compact and quasi-separated since `f` is proper, with affine transition morphisms. So the
extension comes from a section over some `X_V` (Stacks 03Q9). Pulling back along the composite
`X_ȳ ⟶ X ×_Y Spec(𝒪^{sh}_{Y,ȳ}) ⟶ X_V` is the composite of the two pullbacks, and that composite
is the morphism `X_ȳ ⟶ X_V` of the big étale site.

## Main results

* `AlgebraicGeometry.SmallEtale.neighborhoodBaseChangeConeIsLimit`: the base change of `X` to the
  strict henselization is the limit of the base changes of `X` to the affine étale
  neighbourhoods of `ȳ`.
* `AlgebraicGeometry.SmallEtale.exists_smallEtaleSectionPullback_eq_of_isProper`: the statement
  for sheaves of sets on Mathlib's small étale site.
* `AlgebraicGeometry.SmallEtale.exists_geometricFibreRestriction_eq_of_isProper`: the statement
  for abelian sheaves on the small étale site of the big étale site.

## References

* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 0F76](https://stacks.math.columbia.edu/tag/0F76)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace Stacks.EtaleCohomology

section RelativeSections

/-- **Global sections of an inverse image along a factorization, read on an object.** For
`p = g ≫ f` and a global section `σ` of `f⁻¹F`, the image of `σ` under
`Stacks.EtaleCohomology.relativeGlobalSectionsMap`, restricted to an object `V` of the small
étale site of `Z`, is the pullback along `g` of the restriction of `σ` to the identity object of
`Y`, restricted along any `V ⟶ g*(Y/Y)` and carried through the composition isomorphism
`g⁻¹(f⁻¹F) ≅ p⁻¹F`. -/
theorem ΓRes_relativeGlobalSectionsMap {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (p : Z ⟶ X) (hp : p = g ≫ f) (F : Sheaf X.smallEtaleTopology (Type (max (u + 1) v)))
    (V : Z.Etale) (k : V ⟶ (smallEtaleBaseChange g).obj (Scheme.Etale.mk (𝟙 Y)))
    (σ : (etaleGlobalSections.{u, v} Y).obj ((smallEtaleInverseImage f).obj F)) :
    Sheaf.ΓRes ((smallEtaleInverseImage.{u, v} p).obj F) (op V)
        (relativeGlobalSectionsMap.{u, v} f g p hp F σ) =
      ((etalePullbackCompIso f g p hp).hom.app F).hom.app (op V)
        (((smallEtaleInverseImage g).obj ((smallEtaleInverseImage f).obj F)).obj.map k.op
          (smallEtaleSectionPullback.{u, v} g ((smallEtaleInverseImage f).obj F)
            (Scheme.Etale.mk (𝟙 Y))
            (Sheaf.ΓRes ((smallEtaleInverseImage f).obj F) (op (Scheme.Etale.mk (𝟙 Y))) σ))) := by
  have hr : relativeGlobalSectionsMap.{u, v} f g p hp F σ =
      (etaleGlobalSections.{u, v} Z).map ((etalePullbackCompIso f g p hp).hom.app F)
        (etaleGlobalPullback g ((smallEtaleInverseImage f).obj F) σ) := by
    rw [relativeGlobalSectionsMap, ConcreteCategory.comp_apply]
  rw [hr]
  have h := ConcreteCategory.congr_hom (Sheaf.ΓRes_naturality
    ((etalePullbackCompIso f g p hp).hom.app F) (op V))
    (etaleGlobalPullback g ((smallEtaleInverseImage f).obj F) σ)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  rw [h]
  refine congrArg (((etalePullbackCompIso f g p hp).hom.app F).hom.app (op V)) ?_
  dsimp only [Functor.comp_obj]
  have e1 : etaleGlobalPullback g ((smallEtaleInverseImage.{u, v} f).obj F) σ =
      smallEtaleGlobalSectionsMapAt.{u, v} g
        ((isTerminalSmallEtaleBaseChangeObj g terminalIsTerminal).from _)
        ((smallEtaleInverseImage.{u, v} f).obj F) σ := by
    unfold etaleGlobalPullback
    rw [(globalSectionsSmallEtaleInverseImageComparison.{u, v} g).2]
  have e2 := ConcreteCategory.congr_hom
    (((smallEtaleInverseImage.{u, v} g).obj ((smallEtaleInverseImage.{u, v} f).obj F)).ΓRes_map
      (terminal.from V).op) (etaleGlobalPullback g ((smallEtaleInverseImage.{u, v} f).obj F) σ)
  have e3 := ConcreteCategory.congr_hom
    (((smallEtaleInverseImage.{u, v} f).obj F).ΓRes_map
      ((isTerminalEtaleMkId Y).from (terminal Y.Etale)).op) σ
  rw [ConcreteCategory.comp_apply] at e2 e3
  rw [← e2, e1, smallEtaleGlobalSectionsMapAt_apply,
    ← Sheaf.ΓNatIsoSheafSections_hom_app _ _ terminalIsTerminal
      ((smallEtaleInverseImage.{u, v} g).obj ((smallEtaleInverseImage.{u, v} f).obj F)),
    ← ConcreteCategory.comp_apply
      ((Sheaf.ΓNatIsoSheafSections _ (Type (max (u + 1) v)) terminalIsTerminal).inv.app _),
    Iso.inv_hom_id_app, ConcreteCategory.id_apply,
    Sheaf.ΓNatIsoSheafSections_hom_app Y.smallEtaleTopology (terminal Y.Etale)
      terminalIsTerminal ((smallEtaleInverseImage.{u, v} f).obj F),
    ← e3,
    smallEtaleGlobalSectionPullback_eq_map_smallEtaleSectionPullback,
    ← smallEtaleSectionPullback_map.{u, v} g _ ((isTerminalEtaleMkId Y).from (terminal Y.Etale)),
    ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
    (isTerminalSmallEtaleBaseChangeObj g (isTerminalEtaleMkId Y)).hom_ext
      ((terminal.from V ≫ (isTerminalSmallEtaleBaseChangeObj g terminalIsTerminal).from _) ≫
        (smallEtaleBaseChange g).map ((isTerminalEtaleMkId Y).from (terminal Y.Etale))) k]

/-- The restriction of global sections of a sheaf of sets to an object which is terminal in the
small étale site is bijective. -/
theorem bijective_ΓRes_of_isTerminal {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (Type (max (u + 1) v))) {T : X.Etale} (hT : IsTerminal T) :
    Function.Bijective (Sheaf.ΓRes F (op T)) := by
  rw [← Sheaf.ΓNatIsoSheafSections_hom_app _ _ hT]
  exact ((Sheaf.ΓNatIsoSheafSections _ _ hT).app F).toEquiv.bijective

/-- **Pulling a restricted section back along a composite.** For `p = g ≫ f`, the pullback along
`g` of the restriction along `k : V ⟶ f*W` of the pullback along `f` of `s ∈ H(W)`, restricted
along `c : V' ⟶ g*V` and carried through `g⁻¹(f⁻¹H) ≅ p⁻¹H`, is the pullback of `s` along `p`
restricted along the composite `V' ⟶ g*V ⟶ g*(f*W) ≅ p*W`. -/
theorem etalePullbackCompIso_hom_map_smallEtaleSectionPullback {X₁ X₂ X₃ : Scheme.{u}}
    (g : X₁ ⟶ X₂) (f : X₂ ⟶ X₃) (p : X₁ ⟶ X₃) (hp : p = g ≫ f)
    (H : Sheaf X₃.smallEtaleTopology (Type (max (u + 1) v))) {V : X₂.Etale} {V' : X₁.Etale}
    (c : V' ⟶ (smallEtaleBaseChange g).obj V) {W : X₃.Etale}
    (k : V ⟶ (smallEtaleBaseChange f).obj W) (s : H.obj.obj (op W)) :
    ((etalePullbackCompIso f g p hp).hom.app H).hom.app (op V')
        (((smallEtaleInverseImage g).obj ((smallEtaleInverseImage f).obj H)).obj.map c.op
          (smallEtaleSectionPullback.{u, v} g ((smallEtaleInverseImage f).obj H) V
            (((smallEtaleInverseImage.{u, v} f).obj H).obj.map k.op
              (smallEtaleSectionPullback.{u, v} f H W s)))) =
      ((smallEtaleInverseImage.{u, v} p).obj H).obj.map
        (c ≫ (smallEtaleBaseChange g).map k ≫ (etaleBaseChangeCompIso f g p hp).inv.app W).op
        (smallEtaleSectionPullback.{u, v} p H W s) := by
  rw [← smallEtaleSectionPullback_map.{u, v} g ((smallEtaleInverseImage f).obj H) k,
    ← Functor.map_comp_apply, ← op_comp]
  refine (NatTrans.naturality_apply ((etalePullbackCompIso f g p hp).hom.app H).hom
    (c ≫ (smallEtaleBaseChange g).map k).op _).trans ?_
  rw [etalePullbackCompIso_hom_smallEtaleSectionPullback, ← Functor.map_comp_apply,
    ← op_comp, Category.assoc]

/-- **Lifts into base changes along a factorization.** For `p = g ≫ f`, a morphism of étale
`X₃`-schemes `φ : W ⟶ W'`, a lift `r : X₁ ⟶ W` of `p` and a lift `ℓ : X₂ ⟶ W'` of `f` with
`r ≫ φ = g ≫ ℓ`: the lift `X₁/X₁ ⟶ p*W` determined by `r`, followed by `p*φ`, is the lift
`X₁/X₁ ⟶ g*(X₂/X₂)` determined by `g`, followed by the base change along `g` of the lift
`X₂/X₂ ⟶ f*W'` determined by `ℓ` and the comparison `g*(f*W') ≅ p*W'`. -/
theorem smallEtaleBaseChangeLift_comp_map {X₁ X₂ X₃ : Scheme.{u}} (g : X₁ ⟶ X₂) (f : X₂ ⟶ X₃)
    (p : X₁ ⟶ X₃) (hp : p = g ≫ f) {W W' : X₃.Etale} (φ : W ⟶ W') (r : X₁ ⟶ W.left)
    (hr : r ≫ W.hom = p) (ℓ : X₂ ⟶ W'.left) (hℓ : ℓ ≫ W'.hom = f) (h : r ≫ φ.left = g ≫ ℓ) :
    smallEtaleBaseChangeLift p W r hr ≫ (smallEtaleBaseChange p).map φ =
      smallEtaleBaseChangeLift g (Scheme.Etale.mk (𝟙 X₂)) g (Category.comp_id g) ≫
        (smallEtaleBaseChange g).map (smallEtaleBaseChangeLift f W' ℓ hℓ) ≫
          (etaleBaseChangeCompIso f g p hp).inv.app W' := by
  refine smallEtaleBaseChange_hom_ext p ?_
  have e₁ : (smallEtaleBaseChangeLift p W r hr ≫ (smallEtaleBaseChange p).map φ).left ≫
      pullback.fst W'.hom p = r ≫ φ.left :=
    (Category.assoc _ _ _).trans ((congrArg ((smallEtaleBaseChangeLift p W r hr).left ≫ ·)
      (smallEtaleBaseChange_map_left_fst p φ)).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ φ.left) (pullback.lift_fst _ _ _))))
  have e₂ : (smallEtaleBaseChangeLift g (Scheme.Etale.mk (𝟙 X₂)) g (Category.comp_id g) ≫
      (smallEtaleBaseChange g).map (smallEtaleBaseChangeLift f W' ℓ hℓ) ≫
        (etaleBaseChangeCompIso f g p hp).inv.app W').left ≫ pullback.fst W'.hom p = g ≫ ℓ :=
    (Category.assoc _ _ _).trans ((congrArg
      ((smallEtaleBaseChangeLift g (Scheme.Etale.mk (𝟙 X₂)) g (Category.comp_id g)).left ≫ ·)
      ((Category.assoc _ _ _).trans ((congrArg
        (((smallEtaleBaseChange g).map (smallEtaleBaseChangeLift f W' ℓ hℓ)).left ≫ ·)
        (etaleBaseChangeCompIso_inv_app_left_fst f g p hp W')).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ pullback.fst W'.hom f)
          (smallEtaleBaseChange_map_left_fst g (smallEtaleBaseChangeLift f W' ℓ hℓ))))))).trans
      ((congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans ((Category.assoc _ _ _).symm.trans
        (congrArg₂ (· ≫ ·) (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _)))))
  exact e₁.trans (h.trans e₂.symm)

end RelativeSections

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- **The canonical geometric point of the strict henselization maps to the chosen lift in every
affine étale neighbourhood.** The leg of the limit cone at a member `(V, v̄)` of the small affine
family, precomposed with the canonical geometric point of the strict henselization, is `v̄`. Both
are morphisms into an affine scheme, and on global functions both evaluate a function at the
geometric point through `v̄` (`structureSheafStalkToGeometricField_ι` and
`strictHenselizationCone_π_appTop_affine`). -/
theorem geometricPointToStrictHenselization_comp_strictHenselizationAffineCone_π_app
    (a : etaleNeighborhoodAffineIndex B S hS s) :
    geometricPointToStrictHenselization B S hS s ≫
        (strictHenselizationAffineCone B S hS s).π.app a =
      ((etaleNeighborhoodAffineInclusion B S hS s).obj a).2.1 := by
  refine ext_of_isAffine ((Scheme.Hom.comp_appTop _ _).trans ?_)
  rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of s.residueField)).hom,
    Category.assoc, geometricPointToStrictHenselization, Scheme.ΓSpecIso_naturality]
  ext b
  have h1 := strictHenselizationCone_π_appTop_affine B S hS s a b
  have h2 := congrArg (fun φ => φ b) (structureSheafStalkToGeometricField_ι B S hS s
    (op ((etaleNeighborhoodAffineInclusion B S hS s).obj a)))
  exact (congrArg (structureSheafStalkToGeometricField B S hS s) h1).trans h2

end AlgebraicGeometry

namespace AlgebraicGeometry.SmallEtale

open Stacks.EtaleCohomology

attribute [local instance] CategoryTheory.IsCofiltered.isConnected

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) (y : GeometricPoint Y.obj)

/-- The system of base changes `X_V = V ×_Y X` of `X` over the small cofinal family of affine
étale neighbourhoods `(V, v̄)` of `ȳ`, as étale schemes over `X` (in Mathlib's small étale site of
the underlying scheme of `X`). -/
abbrev neighborhoodBaseChangeSystem :
    etaleNeighborhoodAffineIndex B Y.obj Y.property y ⥤ X.obj.Etale :=
  etaleNeighborhoodAffineInclusion B Y.obj Y.property y ⋙
    CategoryOfElements.π (geometricPointFiber B Y.obj Y.property y) ⋙
      toEtaleSite B Y.obj Y.property ⋙
        Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)

/-- The affine étale neighbourhoods of `ȳ`, as schemes over `Y`. -/
abbrev neighborhoodOverDiagram :
    etaleNeighborhoodAffineIndex B Y.obj Y.property y ⥤ Over Y.obj :=
  etaleNeighborhoodAffineInclusion B Y.obj Y.property y ⋙
    CategoryOfElements.π (geometricPointFiber B Y.obj Y.property y) ⋙
      toEtaleSite B Y.obj Y.property ⋙ Scheme.Etale.forget Y.obj

/-- The strict henselization of `Y` at `ȳ`, over `Y`, as a cone on the affine étale
neighbourhoods of `ȳ`. -/
def strictHenselizationOverCone : Cone (neighborhoodOverDiagram B y) where
  pt := Over.mk (strictHenselizationToBase B Y.obj Y.property y)
  π :=
    { app a := Over.homMk ((strictHenselizationAffineCone B Y.obj Y.property y).π.app a)
        (strictHenselizationAffineCone_π_comp_hom_eq B Y.obj Y.property y a)
      naturality a b h := by
        ext
        exact ((strictHenselizationAffineCone B Y.obj Y.property y).w h).symm.trans
          (Category.id_comp _).symm }

/-- **The strict henselization is the limit of the affine étale neighbourhoods over `Y`.** -/
def strictHenselizationOverConeIsLimit : IsLimit (strictHenselizationOverCone B y) :=
  isLimitOfReflects (Over.forget Y.obj)
    (strictHenselizationAffineConeIsLimit B Y.obj Y.property y)

/-- The base change `X ×_Y Spec(𝒪^{sh}_{Y,ȳ})` of `X` to the strict henselization, as a cone on
the system of base changes of `X` to the affine étale neighbourhoods of `ȳ`. -/
def neighborhoodBaseChangeCone :
    Cone (neighborhoodBaseChangeSystem B f y ⋙ Scheme.Etale.forget X.obj ⋙ Over.forget X.obj) :=
  ((Over.pullback (B.inclusion.map f) ⋙ Over.forget X.obj).mapCone
    (strictHenselizationOverCone B y)).extend
      (pullbackSymmetry (B.inclusion.map f) (strictHenselizationToBase B Y.obj Y.property y)).hom

/-- **The base change of `X` to the strict henselization is the limit of the base changes of `X`
to the affine étale neighbourhoods of `ȳ`**: pulling back along `X ⟶ Y` preserves limits and the
forgetful functor of the slice preserves connected limits. -/
def neighborhoodBaseChangeConeIsLimit : IsLimit (neighborhoodBaseChangeCone B f y) :=
  IsLimit.ofIsoLimit
    (isLimitOfPreserves (Over.pullback (B.inclusion.map f) ⋙ Over.forget X.obj)
      (strictHenselizationOverConeIsLimit B y))
    (Cone.extendIso ((Over.pullback (B.inclusion.map f) ⋙ Over.forget X.obj).mapCone
      (strictHenselizationOverCone B y))
      (pullbackSymmetry (B.inclusion.map f)
        (strictHenselizationToBase B Y.obj Y.property y)).symm)

/-- A component of `neighborhoodBaseChangeCone` followed by the first projection of the stage
`V ×_Y X` is the projection to the strict henselization followed by its morphism to `V`. -/
@[reassoc]
theorem neighborhoodBaseChangeCone_π_app_fst
    (a : etaleNeighborhoodAffineIndex B Y.obj Y.property y) :
    (neighborhoodBaseChangeCone B f y).π.app a ≫ pullback.fst (B.inclusion.map
        ((etaleNeighborhoodAffineInclusion B Y.obj Y.property y).obj a).1.obj.hom)
        (B.inclusion.map f) =
      pullback.snd (B.inclusion.map f) (strictHenselizationToBase B Y.obj Y.property y) ≫
        (strictHenselizationAffineCone B Y.obj Y.property y).π.app a :=
  (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)).trans
    (pullbackSymmetry_hom_comp_fst_assoc _ _ _))

/-- A component of `neighborhoodBaseChangeCone` followed by the second projection of the stage
`V ×_Y X` is the projection of `X ×_Y Spec(𝒪^{sh}_{Y,ȳ})` to `X`. -/
@[reassoc]
theorem neighborhoodBaseChangeCone_π_app_snd
    (a : etaleNeighborhoodAffineIndex B Y.obj Y.property y) :
    (neighborhoodBaseChangeCone B f y).π.app a ≫ pullback.snd (B.inclusion.map
        ((etaleNeighborhoodAffineInclusion B Y.obj Y.property y).obj a).1.obj.hom)
        (B.inclusion.map f) =
      pullback.fst (B.inclusion.map f) (strictHenselizationToBase B Y.obj Y.property y) :=
  (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullback.lift_snd _ _ _)).trans
    (pullbackSymmetry_hom_comp_snd _ _))

/-- The components of `neighborhoodBaseChangeCone` lie over `X`: followed by the structure
morphism of the stage, each is the projection of the base change to the strict henselization
to `X`. -/
theorem neighborhoodBaseChangeCone_π_app_hom
    (a : etaleNeighborhoodAffineIndex B Y.obj Y.property y) :
    (neighborhoodBaseChangeCone B f y).π.app a ≫ ((neighborhoodBaseChangeSystem B f y).obj a).hom =
      strictHenselizationBaseChangeToSource B Y.property (B.inclusion.map f) y :=
  neighborhoodBaseChangeCone_π_app_snd B f y a

/-- The transition morphisms of the system of base changes of `X` to the affine étale
neighbourhoods of `ȳ` are affine: they are base changes of morphisms between affine schemes. -/
instance isAffineHom_neighborhoodBaseChangeSystem_map
    {a b : etaleNeighborhoodAffineIndex B Y.obj Y.property y} (e : a ⟶ b) :
    IsAffineHom ((neighborhoodBaseChangeSystem B f y).map e).left := by
  let m := ((toEtaleSite B Y.obj Y.property).map
    ((etaleNeighborhoodAffineInclusion B Y.obj Y.property y).map e).1)
  have hsq := baseChange_square m.left
    ((toEtaleSite B Y.obj Y.property).obj ((etaleNeighborhoodAffineInclusion B Y.obj
      Y.property y).obj b).1).hom
    ((toEtaleSite B Y.obj Y.property).obj ((etaleNeighborhoodAffineInclusion B Y.obj
      Y.property y).obj a).1).hom (B.inclusion.map f) (MorphismProperty.Over.w m)
  have hm : IsAffineHom m.left := by
    have : AlgebraicGeometry.IsAffine ((toEtaleSite B Y.obj Y.property).obj
        ((etaleNeighborhoodAffineInclusion B Y.obj Y.property y).obj a).1).left :=
      isAffine_etaleNeighborhoodAffineDiagram_obj B Y.obj Y.property y a
    have : AlgebraicGeometry.IsAffine ((toEtaleSite B Y.obj Y.property).obj
        ((etaleNeighborhoodAffineInclusion B Y.obj Y.property y).obj b).1).left :=
      isAffine_etaleNeighborhoodAffineDiagram_obj B Y.obj Y.property y b
    exact isAffineHom_of_isAffine _
  exact MorphismProperty.of_isPullback hsq.flip hm

variable [IsProper (B.inclusion.map f)]

/-- For `X ⟶ Y` proper, the base change of `X` to an affine étale neighbourhood of `ȳ` is
quasi-compact. -/
instance compactSpace_neighborhoodBaseChangeSystem_obj
    (a : etaleNeighborhoodAffineIndex B Y.obj Y.property y) :
    CompactSpace ((neighborhoodBaseChangeSystem B f y).obj a).left := by
  let V := (toEtaleSite B Y.obj Y.property).obj
    ((etaleNeighborhoodAffineInclusion B Y.obj Y.property y).obj a).1
  have : AlgebraicGeometry.IsAffine ((𝟭 Scheme).obj V.left) :=
    isAffine_etaleNeighborhoodAffineDiagram_obj B Y.obj Y.property y a
  have : QuasiCompact (pullback.fst V.hom (B.inclusion.map f)) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (IsPullback.of_hasPullback V.hom (B.inclusion.map f)).flip inferInstance
  have h := QuasiCompact.compactSpace_of_compactSpace (pullback.fst V.hom (B.inclusion.map f))
  exact h

/-- For `X ⟶ Y` proper, the base change of `X` to an affine étale neighbourhood of `ȳ` is
quasi-separated. -/
instance quasiSeparatedSpace_neighborhoodBaseChangeSystem_obj
    (a : etaleNeighborhoodAffineIndex B Y.obj Y.property y) :
    QuasiSeparatedSpace ((neighborhoodBaseChangeSystem B f y).obj a).left := by
  let V := (toEtaleSite B Y.obj Y.property).obj
    ((etaleNeighborhoodAffineInclusion B Y.obj Y.property y).obj a).1
  have : AlgebraicGeometry.IsAffine ((𝟭 Scheme).obj V.left) :=
    isAffine_etaleNeighborhoodAffineDiagram_obj B Y.obj Y.property y a
  have : QuasiSeparated (pullback.fst V.hom (B.inclusion.map f)) :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated)
      (IsPullback.of_hasPullback V.hom (B.inclusion.map f)).flip inferInstance
  have h := quasiSeparatedSpace_of_quasiSeparated (pullback.fst V.hom (B.inclusion.map f))
  exact h

variable (hy : B.Contains y.source)

/-- The geometric fibre of the big étale site, pushed into all schemes, is Mathlib's geometric
fibre of the underlying morphism: the inclusion preserves fibre products (Stacks 021D). -/
abbrev geometricFibreObjIso :
    B.inclusion.obj (geometricFibreObj B f y hy) ≅ geometricFibre (B.inclusion.map f) y :=
  PreservesPullback.iso B.inclusion f (geometricPointHom B y hy)

/-- The morphism from the geometric fibre to the base change of `X` to the strict henselization:
the identification with Mathlib's geometric fibre followed by its canonical morphism there. -/
abbrev geometricFibreToNeighborhoodLimit :
    B.inclusion.obj (geometricFibreObj B f y hy) ⟶
      strictHenselizationBaseChange B Y.property (B.inclusion.map f) y :=
  (geometricFibreObjIso B f y hy).hom ≫
    geometricFibreToStrictHenselizationBaseChange B Y.property (B.inclusion.map f) y

omit [IsProper (B.inclusion.map f)] in
/-- The projection of the geometric fibre to `X` factors through the base change of `X` to the
strict henselization. -/
theorem geometricFibreToNeighborhoodLimit_comp :
    B.inclusion.map (geometricFibreProj B f y hy) =
      geometricFibreToNeighborhoodLimit B f y hy ≫
        strictHenselizationBaseChangeToSource B Y.property (B.inclusion.map f) y := by
  rw [Category.assoc, geometricFibreToStrictHenselizationBaseChange_comp_toSource]
  exact (PreservesPullback.iso_hom_fst B.inclusion f (geometricPointHom B y hy)).symm

/-- The comparison of the base change of a stage over `Y` in the two models of the small étale
site, as a morphism of Mathlib's small étale site of `X`. -/
abbrev neighborhoodBaseChangeComparison
    (a : etaleNeighborhoodAffineIndex B Y.obj Y.property y) :
    (toEtaleSite B X.obj X.property).obj ((smallEtaleBaseChange B f).obj
        ((etaleNeighborhoodAffineInclusion B Y.obj Y.property y).obj a).1) ⟶
      (neighborhoodBaseChangeSystem B f y).obj a :=
  (toEtaleSiteBaseChangeComponent B f ((etaleNeighborhoodAffineInclusion B Y.obj Y.property
    y).obj a).1).hom

omit [IsProper (B.inclusion.map f)] in
/-- The two routes from the geometric fibre to the base change `X_V` of an étale scheme `V` over
`Y` agree, given a lift `v̄` of `ȳ` to `V` and a morphism `ℓ` from the strict henselization to `V`
over `Y` carrying its canonical geometric point to `v̄`: through `X_ȳ ⟶ X_V` in the big étale
site, or through the base change of `X` to the strict henselization followed by the base change
of `ℓ`. -/
theorem geometricFibre_lift_comp_preservesPullbackIso (V : SmallEtale B Y.obj Y.property)
    (pt : B.obj y.source hy ⟶ V.obj.left) (hpt : pt ≫ V.obj.hom = geometricPointHom B y hy)
    (ℓ : strictHenselization B Y.obj Y.property y ⟶ B.inclusion.obj V.obj.left)
    (hℓ : ℓ ≫ B.inclusion.map V.obj.hom = strictHenselizationToBase B Y.obj Y.property y)
    (hgℓ : geometricPointToStrictHenselization B Y.obj Y.property y ≫ ℓ = B.inclusion.map pt) :
    B.inclusion.map (pullback.lift (geometricFibreStruct B f y hy ≫ pt)
        (geometricFibreProj B f y hy) (by
          rw [Category.assoc, hpt]
          exact pullback.condition.symm)) ≫
        (PreservesPullback.iso B.inclusion V.obj.hom f).hom =
      geometricFibreToNeighborhoodLimit B f y hy ≫
        (pullbackSymmetry (B.inclusion.map f)
          (strictHenselizationToBase B Y.obj Y.property y)).hom ≫
          pullback.lift (pullback.fst _ _ ≫ ℓ) (pullback.snd _ _) (by
            rw [Category.assoc, hℓ]
            exact pullback.condition) := by
  apply pullback.hom_ext
  · rw [Category.assoc, PreservesPullback.iso_hom_fst, ← B.inclusion.map_comp, pullback.lift_fst,
      B.inclusion.map_comp]
    simp only [Category.assoc, pullback.lift_fst, pullbackSymmetry_hom_comp_fst_assoc,
      geometricFibreToStrictHenselizationBaseChange, pullback.lift_snd_assoc]
    rw [← hgℓ, ← PreservesPullback.iso_hom_snd B.inclusion f (geometricPointHom B y hy),
      Category.assoc]
    rfl
  · rw [Category.assoc, PreservesPullback.iso_hom_snd, ← B.inclusion.map_comp, pullback.lift_snd]
    simp only [Category.assoc, pullback.lift_snd, pullbackSymmetry_hom_comp_snd]
    exact geometricFibreToNeighborhoodLimit_comp B f y hy

omit [IsProper (B.inclusion.map f)] in
/-- The two routes from the geometric fibre into a stage of the system agree: through the lift
`X_ȳ ⟶ X_V` of the neighbourhood and the comparison of the two models of `X_V`, or through the
base change of `X` to the strict henselization and the limit projection. -/
theorem geometricFibreToNeighborhood_comp_comparison
    (a : etaleNeighborhoodAffineIndex B Y.obj Y.property y) :
    B.inclusion.map (geometricFibreToNeighborhood B f y hy
        ((etaleNeighborhoodAffineInclusion B Y.obj Y.property y).obj a)) ≫
        (neighborhoodBaseChangeComparison B f y a).left =
      geometricFibreToNeighborhoodLimit B f y hy ≫ (neighborhoodBaseChangeCone B f y).π.app a :=
  (geometricFibre_lift_comp_preservesPullbackIso B f y hy _ _
    (neighborhoodPointHom_comp B y hy _) _
    (strictHenselizationAffineCone_π_comp_hom_eq B Y.obj Y.property y a)
    (geometricPointToStrictHenselization_comp_strictHenselizationAffineCone_π_app
      B Y.obj Y.property y a)).trans (Category.assoc _ _ _).symm

/-- **Proper base change for `H⁰` on the geometric fibre, sheaves of sets on Mathlib's small
étale site.** Let `f : X ⟶ Y` be a proper morphism of a big étale site, `ȳ` a geometric point of
`Y` whose spectrum lies in the site, and `p : X_ȳ ⟶ X` the projection of the geometric fibre. For
every sheaf of sets `H` on Mathlib's small étale site of `X`, every global section of `p⁻¹H` is,
for some étale neighbourhood `(V, v̄)` of `ȳ`, the pullback of a section of `H` over `X_V` along
`X_ȳ ⟶ X_V`.

A global section over `X_ȳ` extends to the base change `X ×_Y Spec(𝒪^{sh}_{Y,ȳ})` of `X` to the
strict henselization (Stacks 0A3S and 0A3I,
`Stacks.EtaleCohomology.surjective_relativeGlobalSectionsMap_geometricFibre_of_isProper`); that
base change is the limit of the base changes `X_V` over the affine étale neighbourhoods `(V, v̄)`
of `ȳ`, so the extension comes from a section over some `X_V` (Stacks 03Q9,
`Stacks.EtaleCohomology.exists_limitStagePullback_eq`), and pulling back along the composite
`X_ȳ ⟶ X ×_Y Spec(𝒪^{sh}_{Y,ȳ}) ⟶ X_V`, which is `X_ȳ ⟶ X_V`, is the composite of the two
pullbacks. -/
@[sga "4 XII 5.2" "(i)"]
theorem exists_smallEtaleSectionPullback_eq_of_isProper
    (H : Sheaf (Scheme.smallEtaleTopology X.obj) (Type (max (u + 1) v)))
    (t : ((Stacks.EtaleCohomology.smallEtaleInverseImage.{u, v}
        (B.inclusion.map (geometricFibreProj B f y hy))).obj H).obj.obj
          (op (Scheme.Etale.mk (𝟙 (geometricFibreObj B f y hy).obj)))) :
    ∃ (N : (geometricPointFiber B Y.obj Y.property y).Elements)
      (s : H.obj.obj (op ((toEtaleSite B X.obj X.property).obj
        ((smallEtaleBaseChange B f).obj N.1)))),
      ((Stacks.EtaleCohomology.smallEtaleInverseImage.{u, v}
          (B.inclusion.map (geometricFibreProj B f y hy))).obj H).obj.map
        (Stacks.EtaleCohomology.smallEtaleBaseChangeLift
          (B.inclusion.map (geometricFibreProj B f y hy))
          ((toEtaleSite B X.obj X.property).obj ((smallEtaleBaseChange B f).obj N.1))
          (B.inclusion.map ((geometricFibreLift B f y hy N).hom.left ≫
            baseChangeObjProjection B (geometricFibreProj B f y hy)
              ((smallEtaleBaseChange B f).obj N.1)))
          (baseChangeLift_condition B (geometricFibreProj B f y hy)
            ((smallEtaleBaseChange B f).obj N.1) (geometricFibreLift B f y hy N))).op
        (Stacks.EtaleCohomology.smallEtaleSectionPullback.{u, v}
          (B.inclusion.map (geometricFibreProj B f y hy)) H _ s) = t := by
  let p := B.inclusion.map (geometricFibreProj B f y hy)
  let e := geometricFibreObjIso B f y hy
  let π := strictHenselizationBaseChangeToSource B Y.property (B.inclusion.map f) y
  let g := geometricFibreToStrictHenselizationBaseChange B Y.property (B.inclusion.map f) y
  let q := geometricFibreToSource (B.inclusion.map f) y
  let g' := geometricFibreToNeighborhoodLimit B f y hy
  have hq : q = g ≫ π :=
    (geometricFibreToStrictHenselizationBaseChange_comp_toSource B Y.property
      (B.inclusion.map f) y).symm
  have he : p = e.hom ≫ q := (PreservesPullback.iso_hom_fst B.inclusion f
    (geometricPointHom B y hy)).symm
  have hp : p = g' ≫ π := geometricFibreToNeighborhoodLimit_comp B f y hy
  -- global sections over the geometric fibre extend to the strict henselization
  have hsurj : Function.Surjective (relativeGlobalSectionsMap.{u, v} π g' p hp H) := by
    intro x
    obtain ⟨x₁, hx₁⟩ := ((ConcreteCategory.bijective_of_isIso
      ((etaleGlobalSections _).map ((etalePullbackCompIso q e.hom p he).hom.app H))).2.comp
        (bijective_etaleGlobalPullback_of_isIso e.hom _).2) x
    obtain ⟨σ, hσ⟩ := surjective_relativeGlobalSectionsMap_geometricFibre_of_isProper.{u, v}
      B Y.property (B.inclusion.map f) y H x₁
    refine ⟨σ, (relativeGlobalSectionsMap_comp π g e.hom q hq g' rfl p hp he H σ).symm.trans ?_⟩
    rw [hσ]
    exact hx₁
  obtain ⟨τ, hτ⟩ := (bijective_ΓRes_of_isTerminal
    ((Stacks.EtaleCohomology.smallEtaleInverseImage.{u, v} p).obj H)
    (isTerminalEtaleMkId _)).2 t
  obtain ⟨σ, rfl⟩ := hsurj τ
  -- the extension comes from a stage of the system of neighbourhoods
  obtain ⟨i, s₀, hs₀⟩ := exists_limitStagePullback_eq (neighborhoodBaseChangeSystem B f y)
    (neighborhoodBaseChangeCone B f y) π (neighborhoodBaseChangeCone_π_app_hom B f y) H
    (neighborhoodBaseChangeConeIsLimit B f y)
    (Sheaf.ΓRes ((Stacks.EtaleCohomology.smallEtaleInverseImage.{u, v} π).obj H)
      (op (Scheme.Etale.mk (𝟙 (strictHenselizationBaseChange B Y.property
        (B.inclusion.map f) y)))) σ)
  let N := (etaleNeighborhoodAffineInclusion B Y.obj Y.property y).obj i
  refine ⟨N, H.obj.map (neighborhoodBaseChangeComparison B f y i).op s₀, ?_⟩
  let k := Stacks.EtaleCohomology.smallEtaleBaseChangeLift g' (Scheme.Etale.mk (𝟙 _)) g'
    (Category.comp_id g')
  let W := (toEtaleSite B X.obj X.property).obj ((smallEtaleBaseChange B f).obj N.1)
  let lift := Stacks.EtaleCohomology.smallEtaleBaseChangeLift p W
    (B.inclusion.map ((geometricFibreLift B f y hy N).hom.left ≫
      baseChangeObjProjection B (geometricFibreProj B f y hy)
        ((smallEtaleBaseChange B f).obj N.1)))
    (baseChangeLift_condition B (geometricFibreProj B f y hy)
      ((smallEtaleBaseChange B f).obj N.1) (geometricFibreLift B f y hy N))
  let L := limitStageLift (neighborhoodBaseChangeSystem B f y) (neighborhoodBaseChangeCone B f y)
    π (neighborhoodBaseChangeCone_π_app_hom B f y) i
  have key : lift ≫ (Stacks.EtaleCohomology.smallEtaleBaseChange p).map
        (neighborhoodBaseChangeComparison B f y i) =
      k ≫ (Stacks.EtaleCohomology.smallEtaleBaseChange g').map L ≫
        (etaleBaseChangeCompIso π g' p hp).inv.app _ :=
    smallEtaleBaseChangeLift_comp_map g' π p hp _ _ _ _ _
      ((congrArg (· ≫ (neighborhoodBaseChangeComparison B f y i).left)
        (congrArg B.inclusion.map (geometricFibreLift_proj B f y hy N))).trans
          (geometricFibreToNeighborhood_comp_comparison B f y hy i))
  rw [← hτ, ΓRes_relativeGlobalSectionsMap π g' p hp H _ k σ, ← hs₀]
  refine Eq.trans ?_
    (etalePullbackCompIso_hom_map_smallEtaleSectionPullback.{u, v} g' π p hp H k L s₀).symm
  rw [← smallEtaleSectionPullback_map.{u, v} p H (neighborhoodBaseChangeComparison B f y i) s₀,
    ← Functor.map_comp_apply, ← op_comp]
  exact congrArg (fun m => ((Stacks.EtaleCohomology.smallEtaleInverseImage.{u, v} p).obj H).obj.map
    m.op (smallEtaleSectionPullback.{u, v} p H _ s₀)) key

/-- **Sections over the geometric fibre of a proper morphism come from étale neighbourhoods.**
Let `f : X ⟶ Y` be a proper morphism of a big étale site, `ȳ` a geometric point of `Y` whose
spectrum lies in the site, and `F` an abelian sheaf on the small étale site of `X`. Every global
section of `F|_{X_ȳ}` is the pullback, along `X_ȳ ⟶ X_V`, of a section of `F` over `X_V` for some
étale neighbourhood `(V, v̄)` of `ȳ`: the surjectivity half of proper base change in degree `0`
(Stacks 095T), which enters the description of the stalks of `f_!` (Stacks 0F76).

This is `AlgebraicGeometry.SmallEtale.exists_geometricFibreRestriction_eq_of_isProper_of_sets`
with its hypothesis discharged by
`AlgebraicGeometry.SmallEtale.exists_smallEtaleSectionPullback_eq_of_isProper`. -/
theorem exists_geometricFibreRestriction_eq_of_isProper
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (t : geometricFibreSections B f y hy F) :
    ∃ (N : (geometricPointFiber B Y.obj Y.property y).Elements)
      (s : F.obj.obj (op ((smallEtaleBaseChange B f).obj N.1))),
      geometricFibreRestriction B f y hy F N s = t :=
  exists_geometricFibreRestriction_eq_of_isProper_of_sets B f y hy
    (exists_smallEtaleSectionPullback_eq_of_isProper B f y hy) F t

end AlgebraicGeometry.SmallEtale
