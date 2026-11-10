module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardSquareComparisonSets
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSetBaseChangeMate
public import StacksFrontier.CategoryTheory.Adjunction.MateAlongFunctorsApp

/-!
# Étale base change for the direct image of modules, on underlying sheaves of sets

For a cartesian square of algebraic spaces with étale bottom arrow `g`, the base change map
`g^* f_* ⟶ f'_* i^*` of modules across the adjunctions of Stacks 03LU is compared with the base
change map of sheaves of sets across the adjunctions of étale restriction.  The underlying sheaf
of sets of a direct image or of an étale restriction of a module is, definitionally, the direct
image or étale restriction of the underlying sheaf of sets; the comparisons below record these
identities at variables, and `Stacks.CategoryTheory.isIso_map_mateEquiv_symm_app_of_comp₃`
transports the invertibility of the mate of sets (Stacks 03LR, part (1)) to the mate of modules.

## Main results

* `AlgebraicGeometry.Space.moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_comp`
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardSquare_comp`
* `AlgebraicGeometry.Space.isIso_moduleSheafFunctor_map_etaleModuleBaseChangeMate_app`

## Implementation notes

The instantiation is done in two steps: first over a variable 2-square of sheaves of sets and
variable 2-cells of modules
(`AlgebraicGeometry.Space.isIso_moduleSheafFunctor_map_mateEquiv_symm_of_twoSquare`), then at
the canonical ones.  Done in one step the kernel has to compare the two spellings of the
composite direct images of sheaves of sets inside the hypotheses, which exceeds its budget.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u


namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Comparisons

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The underlying sheaf of sets of the direct image of a module is the direct image of its
underlying sheaf of sets. -/
def modulePushforwardSetSheafHom :
    modulePushforward B S hS f ⋙ Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y) ⟶
      Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X) ⋙ smallEtaleDirectImage B S hS f where
  app N := 𝟙 ((smallEtaleDirectImage B S hS f).obj (moduleSetSheaf B S hS X N))
  naturality _ _ _ := rfl

/-- The same comparison, with the direct image of sheaves of sets read as the direct image of
the morphism of small étale topoi at the universe of the structure rings. -/
def modulePushforwardTopoiSetSheafHom :
    modulePushforward B S hS f ⋙ Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y) ⟶
      Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X) ⋙
        (smallToposMorphismTypeU B S hS f).pushforward where
  app N := 𝟙 ((smallEtaleDirectImage B S hS f).obj (moduleSetSheaf B S hS X N))
  naturality _ _ _ := rfl

/-- Every component of `modulePushforwardTopoiSetSheafHom` is an isomorphism. -/
instance isIso_modulePushforwardTopoiSetSheafHom_app (N : Modules.{u, u} B S hS X.1 X.2) :
    IsIso ((modulePushforwardTopoiSetSheafHom B S hS f).app N) := by
  change IsIso (𝟙 ((smallEtaleDirectImage B S hS f).obj (moduleSetSheaf B S hS X N)))
  infer_instance

variable (hf : IsEtale B S hS f.hom)

/-- The underlying sheaf of sets of the étale restriction of a module is the étale restriction
of its underlying sheaf of sets. -/
def etaleModulePullbackSetSheafIso (M : Modules.{u, u} B S hS Y.1 Y.2) :
    moduleSetSheaf B S hS X ((etaleModulePullback.{u, u} B S hS f hf).obj M) ≅
      (smallEtaleSetRestriction B S hS f hf).obj (moduleSetSheaf B S hS Y M) :=
  Iso.refl _

end Comparisons


section Unit

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
  (hrep : yoneda.relativelyRepresentable f.hom)

include hrep in
/-- The unit of étale restriction of modules, read on underlying sheaves of sets through the
comparisons, is the unit of étale restriction of sheaves of sets. -/
theorem moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_comp
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        ((etaleModulePullbackAdjunction B S hS f hf).unit.app M) ≫
      (modulePushforwardSetSheafHom B S hS f).app
          ((etaleModulePullback.{u, u} B S hS f hf).obj M) ≫
        (smallEtaleDirectImage B S hS f).map (etaleModulePullbackSetSheafIso B S hS f hf M).hom =
      (smallEtaleSetRestrictionAdjunction B S hS f hf).unit.app (moduleSetSheaf B S hS Y M) := by
  have e := moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit B S hS f hf hrep M
  have e2 := Stacks.CategoryTheory.comp_id_comp_map_id_eq (smallEtaleDirectImage B S hS f)
    (R := moduleSetSheaf B S hS X ((etaleModulePullback.{u, u} B S hS f hf).obj M)) e
  exact e2

end Unit



section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS} (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
  (g : Y' ⟶ Y)

/-- The underlying sheaf of sets of a twice direct image of modules is the twice direct image of
its underlying sheaf of sets, through `g` and `f'`. -/
def modulePushforwardPushforwardSetSheafHom (N : Modules.{u, u} B S hS X'.1 X'.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).obj
      ((modulePushforward B S hS g).obj ((modulePushforward B S hS f').obj N)) ⟶
    (smallEtaleDirectImage B S hS g).obj ((smallToposMorphismTypeU B S hS f').pushforward.obj
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).obj N)) :=
  𝟙 ((smallEtaleDirectImage B S hS g).obj ((smallToposMorphismTypeU B S hS f').pushforward.obj
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).obj N)))

/-- The underlying sheaf of sets of a twice direct image of modules is the twice direct image of
its underlying sheaf of sets, through `f` and `i`. -/
def modulePushforwardPushforwardSetSheafHom' (N : Modules.{u, u} B S hS X'.1 X'.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).obj
      ((modulePushforward B S hS f).obj ((modulePushforward B S hS i).obj N)) ⟶
    (smallToposMorphismTypeU B S hS f).pushforward.obj ((smallEtaleDirectImage B S hS i).obj
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).obj N)) :=
  𝟙 ((smallToposMorphismTypeU B S hS f).pushforward.obj ((smallEtaleDirectImage B S hS i).obj
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).obj N)))

/-- `modulePushforwardPushforwardSetSheafHom` is the composite of the comparison for `g` with the
direct image along `g` of the comparison for `f'`. -/
theorem modulePushforwardPushforwardSetSheafHom_eq (N : Modules.{u, u} B S hS X'.1 X'.2) :
    modulePushforwardPushforwardSetSheafHom B S hS f' g N =
      (modulePushforwardSetSheafHom B S hS g).app ((modulePushforward B S hS f').obj N) ≫
        (smallEtaleDirectImage B S hS g).map
          ((modulePushforwardTopoiSetSheafHom B S hS f').app N) :=
  Stacks.CategoryTheory.id_eq_id_comp_map_id (smallEtaleDirectImage B S hS g)
    ((smallToposMorphismTypeU B S hS f').pushforward.obj
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).obj N))

/-- `modulePushforwardPushforwardSetSheafHom'` is the composite of the comparison for `f` with the
direct image along `f` of the comparison for `i`. -/
theorem modulePushforwardPushforwardSetSheafHom'_eq (N : Modules.{u, u} B S hS X'.1 X'.2) :
    modulePushforwardPushforwardSetSheafHom' B S hS i f N =
      (modulePushforwardTopoiSetSheafHom B S hS f).app ((modulePushforward B S hS i).obj N) ≫
        (smallToposMorphismTypeU B S hS f).pushforward.map
          ((modulePushforwardSetSheafHom B S hS i).app N) :=
  Stacks.CategoryTheory.id_eq_id_comp_map_id (smallToposMorphismTypeU B S hS f).pushforward
    ((smallEtaleDirectImage B S hS i).obj
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).obj N))

set_option maxHeartbeats 1000000 in
-- the statement composes several module and set-sheaf direct images, whose elaboration and
-- the `rw` steps through them are heavy
/-- The comparison of the two composite direct images of modules around a commutative square,
read on underlying sheaves of sets one factor at a time, is the comparison of the two composite
direct images of sheaves of sets (Stacks 03G2, part (3)). -/
theorem moduleSheafFunctor_map_modulePushforwardSquare_comp (w : i ≫ f = f' ≫ g)
    (N : Modules.{u, u} B S hS X'.1 X'.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        ((modulePushforwardCompIso B S hS i f).hom.app N) ≫
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        ((eqToHom (congrArg (fun k : X' ⟶ Y => modulePushforward B S hS k) w)).app N) ≫
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        ((modulePushforwardCompIso B S hS f' g).inv.app N) ≫
        modulePushforwardPushforwardSetSheafHom B S hS f' g N =
      modulePushforwardPushforwardSetSheafHom' B S hS i f N ≫
        ((smallToposMorphismTypeU_comp B S hS i f).hom ≫
          eqToHom (congrArg (fun k : X' ⟶ Y => (smallToposMorphismTypeU B S hS k).pushforward)
            w) ≫
          (smallToposMorphismTypeU_comp B S hS f' g).inv).app
            ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).obj N) := by
  rw [moduleSheafFunctor_map_modulePushforwardCompIso_hom_app,
    moduleSheafFunctor_map_eqToHom_modulePushforward_congr_app B S hS w N,
    moduleSheafFunctor_map_modulePushforwardCompIso_inv_app]
  exact Stacks.CategoryTheory.comp₃_app_comp_id _ _ _ _

/-- `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardSquare_comp` with the
comparison of sheaves of sets read as a 2-square from the small étale direct image along `i`. -/
theorem moduleSheafFunctor_map_modulePushforwardSquare_twoSquare (w : i ≫ f = f' ≫ g)
    (N : Modules.{u, u} B S hS X'.1 X'.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        ((modulePushforwardCompIso B S hS i f).hom.app N) ≫
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        ((eqToHom (congrArg (fun k : X' ⟶ Y => modulePushforward B S hS k) w)).app N) ≫
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        ((modulePushforwardCompIso B S hS f' g).inv.app N) ≫
        modulePushforwardPushforwardSetSheafHom B S hS f' g N =
      modulePushforwardPushforwardSetSheafHom' B S hS i f N ≫
        (TwoSquare.mk _ _ _ _ ((smallToposMorphismTypeU_comp B S hS i f).hom ≫
          eqToHom (congrArg (fun k : X' ⟶ Y => (smallToposMorphismTypeU B S hS k).pushforward)
            w) ≫
          (smallToposMorphismTypeU_comp B S hS f' g).inv) :
          TwoSquare (smallEtaleDirectImage B S hS i) (smallToposMorphismTypeU B S hS f').pushforward
            (smallToposMorphismTypeU B S hS f).pushforward
            (smallEtaleDirectImage B S hS g)).app
            ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).obj N) :=
  moduleSheafFunctor_map_modulePushforwardSquare_comp B S hS i f' f g w N

/-- The base change map of modules across the étale adjunctions of Stacks 03LU, for any
2-cell of composite direct images of modules which agrees, on underlying sheaves of sets, with a
2-cell of composite direct images of sheaves of sets whose mate is invertible, is invertible on
underlying sheaves of sets. -/
theorem isIso_moduleSheafFunctor_map_mateEquiv_symm_of_twoSquare
    (hg : IsEtale B S hS g.hom) (hrep : yoneda.relativelyRepresentable g.hom)
    (hi : IsEtale B S hS i.hom) (hrepi : yoneda.relativelyRepresentable i.hom)
    {P Q : Modules.{u, u} B S hS X'.1 X'.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2}
    (a : modulePushforward B S hS i ⋙ modulePushforward B S hS f ⟶ P) (b : P ⟶ Q)
    (c : Q ⟶ modulePushforward B S hS f' ⋙ modulePushforward B S hS g)
    (θ : TwoSquare (smallEtaleDirectImage B S hS i) (smallToposMorphismTypeU B S hS f').pushforward
      (smallToposMorphismTypeU B S hS f).pushforward (smallEtaleDirectImage B S hS g))
    (hθ : ∀ N : Modules.{u, u} B S hS X'.1 X'.2,
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map (a.app N) ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map (b.app N) ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map (c.app N) ≫
          modulePushforwardPushforwardSetSheafHom B S hS f' g N =
        modulePushforwardPushforwardSetSheafHom' B S hS i f N ≫
          θ.app ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).obj N))
    (h : IsIso ((mateEquiv (smallEtaleSetRestrictionAdjunction B S hS i hi)
      (smallEtaleSetRestrictionAdjunction B S hS g hg)).symm θ))
    (K : Modules.{u, u} B S hS X.1 X.2) :
    IsIso ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y')).map
      (((mateEquiv (etaleModulePullbackAdjunction B S hS i hi)
        (etaleModulePullbackAdjunction B S hS g hg)).symm
        (TwoSquare.mk _ _ _ _ (a ≫ b ≫ c))).app K)) :=
  Stacks.CategoryTheory.isIso_map_mateEquiv_symm_app_of_comp₃
    (etaleModulePullbackAdjunction B S hS i hi) (etaleModulePullbackAdjunction B S hS g hg)
    (smallEtaleSetRestrictionAdjunction B S hS i hi)
    (smallEtaleSetRestrictionAdjunction B S hS g hg) a b c θ
    (modulePushforwardSetSheafHom B S hS g) (modulePushforwardTopoiSetSheafHom B S hS f)
    (modulePushforwardSetSheafHom B S hS i) (modulePushforwardTopoiSetSheafHom B S hS f')
    (etaleModulePullbackSetSheafIso B S hS g hg) (etaleModulePullbackSetSheafIso B S hS i hi)
    (modulePushforwardPushforwardSetSheafHom' B S hS i f)
    (modulePushforwardPushforwardSetSheafHom B S hS f' g)
    (moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_comp B S hS g hg hrep)
    (moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_comp B S hS i hi hrepi)
    (modulePushforwardPushforwardSetSheafHom'_eq B S hS i f)
    (modulePushforwardPushforwardSetSheafHom_eq B S hS f' g) hθ
    (isIso_modulePushforwardTopoiSetSheafHom_app B S hS f')
    (isIso_modulePushforwardTopoiSetSheafHom_app B S hS f) K
    (NatIso.isIso_app_of_isIso _ _)

/-- **The base change map of modules across the étale adjunctions of Stacks 03LU is, on
underlying sheaves of sets, invertible**, for a cartesian square whose bottom arrow is étale and
representable: it is the base change map of sheaves of sets, up to identities, and that one is
invertible by Stacks 03LR, part (1). -/
theorem isIso_moduleSheafFunctor_map_etaleModuleBaseChangeMate_app (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) (hrep : yoneda.relativelyRepresentable g.hom)
    (K : Modules.{u, u} B S hS X.1 X.2) :
    IsIso ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y')).map
      (((mateEquiv (etaleModulePullbackAdjunction B S hS i
          (isEtale_of_isPullback B S hS f' i g f sq.flip hg))
        (etaleModulePullbackAdjunction B S hS g hg)).symm
        (TwoSquare.mk _ _ _ _ ((modulePushforwardCompIso B S hS i f).hom ≫
          eqToHom (congrArg (fun k : X' ⟶ Y => modulePushforward B S hS k) sq.w) ≫
          (modulePushforwardCompIso B S hS f' g).inv))).app K)) :=
  isIso_moduleSheafFunctor_map_mateEquiv_symm_of_twoSquare B S hS i f' f g hg hrep
    (isEtale_of_isPullback B S hS f' i g f sq.flip hg)
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (AlgebraicSpaces.isPullback_hom B S hS sq).flip hrep)
    (modulePushforwardCompIso B S hS i f).hom
    (eqToHom (congrArg (fun k : X' ⟶ Y => modulePushforward B S hS k) sq.w))
    (modulePushforwardCompIso B S hS f' g).inv _
    (moduleSheafFunctor_map_modulePushforwardSquare_twoSquare B S hS i f' f g sq.w)
    (isIso_mateEquiv_symm_smallSetPushforwardCompSquare B S hS i f' f g sq hg) K

end Square

end AlgebraicGeometry.Space

end
