module

public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardForkSheafCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartDirectImageUnitArrowSheafTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardCompIsoSheafTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePresentationForkTransports
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleSheafForkReflection
public import StacksCore.Tactic.StacksAttribute
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# The exact sequence of an étale presentation for the direct image of modules

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, let `U → X` be a surjective étale morphism from a scheme, put `R = U ×_X U` with its
two projections `t, s : R → U`, and let `a : U → Y` and `b : R → Y` be the induced morphisms.
Stacks 03M8 asserts that for every `𝒪_X`-module `F` there is an exact sequence

`0 → f_*F → a_*(F|_U) → b_*(F|_R)`

in `Mod(𝒪_Y)` whose second arrow is the difference `t^* - s^*`.

This file proves it, `AlgebraicGeometry.Space.exact_moduleChartDirectImage`, with the terms
and arrows of the source:

* `f_*F`, `a_*(F|_U)` and `b_*(F|_R)` are `AlgebraicGeometry.Space.modulePushforward` along `f`,
  along `a = τ ≫ f` and along `b = ρ ≫ f` of `F` and of its étale restrictions
  `AlgebraicGeometry.Space.etaleModulePullback` to the chart `τ : U ⟶ X` and to the relation
  `ρ : R ⟶ X`;
* the first arrow is `AlgebraicGeometry.Space.moduleChartDirectImageUnitArrow`, the direct image
  along `f` of the unit `F ⟶ τ_*(F|_U)` followed by the comparison `f_* ∘ τ_* ≅ a_*` of
  Stacks 03LU;
* the arrows `t^*` and `s^*` are `AlgebraicGeometry.Space.moduleChartDirectImageParallelArrow`
  at the factorizations `t ≫ τ = ρ` and `s ≫ τ = ρ`: the direct image along `f` of the unit of
  restriction along `t` (resp. `s`), conjugated by the comparisons of Stacks 03LU.

These are morphisms of `𝒪_Y`-modules by construction, and the conclusion is exactness of the
short complex `f_*F → a_*(F|_U) → b_*(F|_R)` with second arrow `t^* - s^*`, together with the
injectivity of the first arrow, in the abelian category `Mod(𝒪_Y)`.

## Proof

The functor `CategoryTheory.Sheaf.moduleSheafFunctor` taking a sheaf of modules to its underlying
sheaf of sets reflects the limits of forks
(`Stacks.Sheaves.RingedToposModules.isLimitForkOfIsLimitForkModuleSheaf`), and on underlying
sheaves of sets the sequence is the limiting fork
`AlgebraicGeometry.Space.isLimitForkSheafChartDirectImageCanonical`, which is the sheaf
condition of Stacks 03H7 for the covering `{V ×_Y U → V ×_Y X}` read on every étale chart `V` of
`Y`.  What this file adds is the identification of the three arrows of the module sequence, on
underlying sheaves of sets, with the three arrows of that fork:

* `AlgebraicGeometry.Space.heq_moduleSheafFunctor_map_moduleChartDirectImageUnitArrow` for the
  first arrow,
* `AlgebraicGeometry.Space.heq_moduleSheafFunctor_map_moduleRestrictionUnitArrow` and
  `AlgebraicGeometry.Space.heq_moduleSheafFunctor_map_moduleChartDirectImageParallelArrow` for
  `t^*` and `s^*`,

each assembled from the factor comparisons
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforward_map_unit_app` (the unit of
étale restriction) and
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardCompIso_hom_app` and `..._inv_app`
(the comparisons of Stacks 03LU).  From them,
`AlgebraicGeometry.Space.moduleChartDirectImage_fork_condition` is the statement that the
sequence is a complex (the image functor is faithful), and
`AlgebraicGeometry.Space.nonempty_isLimitForkModuleChartDirectImage` that the first arrow is the
equalizer of `t^*` and `s^*`; in a preadditive category this is the kernel of `t^* - s^*`.

## Implementation notes

The identifications are stated as heterogeneous equalities, because the two sides are morphisms
between objects that agree only definitionally: the sheaf of sets underlying `f_*F` is the direct
image of the sheaf of sets underlying `F` by `rfl`
(`AlgebraicGeometry.Space.moduleSheaf_modulePushforward`), and similarly for the restrictions.
The arrows themselves are definitions whose bodies are composites, and a composite is typed at
the middle object of its first factor while its second factor is typed at its own source, which
is written differently (`(τ_* ⋙ f_*).obj M` against `f_*.obj (τ_*.obj M)`, `(𝟭 _).obj M` against
`M`).  Every such re-reading is made by the congruence lemmas of the first section, with the
equality of objects supplied by `CategoryTheory.Functor.comp_obj` and
`CategoryTheory.Functor.id_obj`, and the comparisons between the same morphism under two
spellings are closed by the tactics `heq_congr` and `heq_split_map_comp` of
`StacksFrontier/Tactic/HEqCongr.lean`, which build the congruence proof directly and leave the
remaining checks between objects to the kernel.  Asking the elaborator to unify those spellings
instead exceeds the default heartbeat budget.

The equalizer form is stated as `Nonempty (IsLimit _)` in a theorem: as a definition its
fork-condition proof would be abstracted into an auxiliary lemma whose statement the kernel
would have to compare with the elaborated one.

## References

* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03H7](https://stacks.math.columbia.edu/tag/03H7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe v₁ v₂ u₁ u₂ u

/-! ### Congruence for heterogeneous equality -/

section HEq

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

private theorem heq_comp {X Y Z X' Y' Z' : C} (a : X ⟶ Y) (b : Y ⟶ Z) (a' : X' ⟶ Y')
    (b' : Y' ⟶ Z') (hX : X = X') (hY : Y = Y') (hZ : Z = Z') (ha : HEq a a') (hb : HEq b b') :
    HEq (a ≫ b) (a' ≫ b') := by
  subst hX hY hZ
  cases ha; cases hb; rfl

private theorem heq_map (G : C ⥤ D) {X Y X' Y' : C} (m : X ⟶ Y) (m' : X' ⟶ Y') (hX : X = X')
    (hY : Y = Y') (h : HEq m m') : HEq (G.map m) (G.map m') := by
  subst hX hY
  cases h; rfl

private theorem heq_app {F G F' G' : C ⥤ D} (η : F ⟶ G) (η' : F' ⟶ G') (X X' : C)
    (hF : F = F') (hG : G = G') (hη : HEq η η') (hX : X = X') : HEq (η.app X) (η'.app X') := by
  subst hF hG hX; cases hη; rfl

private theorem heq_app_id {G G' : C ⥤ C} (η : 𝟭 C ⟶ G) (η' : 𝟭 C ⟶ G') (X X' : C)
    (hG : G = G') (hη : HEq η η') (hX : X = X') :
    @HEq (X ⟶ G.obj X) (η.app X) (X' ⟶ G'.obj X') (η'.app X') := by
  subst hG hX; cases hη; rfl

private theorem map_eq_comp_of_eq (G : C ⥤ D) {X Y Z : C} {k : X ⟶ Z} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hk : k = f ≫ g) : G.map k = G.map f ≫ G.map g := by
  rw [hk, G.map_comp]

/-- A fork is a limit as soon as a fork with the same three objects and heterogeneously equal
arrows is. -/
private noncomputable def isLimitForkOfHEq {A M N A' M' N' : C} {ι : A ⟶ M} {φ ψ : M ⟶ N}
    {ι' : A' ⟶ M'} {φ' ψ' : M' ⟶ N'} (w : ι ≫ φ = ι ≫ ψ) (w' : ι' ≫ φ' = ι' ≫ ψ')
    (hA : A = A') (hM : M = M') (hN : N = N') (hι : HEq ι ι') (hφ : HEq φ φ') (hψ : HEq ψ ψ')
    (h : IsLimit (Fork.ofι ι' w')) : IsLimit (Fork.ofι ι w) := by
  subst hA hM hN
  obtain rfl := eq_of_heq hι
  obtain rfl := eq_of_heq hφ
  obtain rfl := eq_of_heq hψ
  exact h

end HEq

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y U R : AlgebraicSpaces B S hS}

/-! ### The objects -/

private theorem moduleSheaf_restriction_unit_obj {τ : U ⟶ X} (hτ : IsEtale B S hS τ.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj
        ((modulePushforward B S hS τ).obj ((etaleModulePullback.{u, u} B S hS τ hτ).obj F)) =
      (smallEtaleSetRestriction B S hS τ hτ ⋙ smallEtaleDirectImage B S hS τ).obj
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) :=
  (moduleSheaf_modulePushforward_etaleModulePullback B S hS τ τ hτ F).trans
    (Functor.comp_obj _ _ _).symm

/-! ### The factors of the arrows, on underlying sheaves of sets -/

/-- The unit factor `f_*(F ⟶ τ_*(F|_U))`, on underlying sheaves of sets. -/
private theorem heq_moduleSheaf_unit (f : X ⟶ Y) {τ : U ⟶ X} (hτ : IsEtale B S hS τ.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    HEq ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        ((modulePushforward B S hS f).map ((etaleModulePullbackAdjunction B S hS τ hτ).unit.app F)))
      ((smallEtaleDirectImage B S hS f).map
        ((smallEtaleSetRestrictionAdjunction B S hS τ hτ).unit.app
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F))) :=
  (heq_of_eq (moduleSheafFunctor_map_modulePushforward_map_unit_app B S hS f hτ F)).trans
    (heq_map (smallEtaleDirectImage B S hS f) _ _ (Functor.id_obj _).symm
      (moduleSheaf_restriction_unit_obj B S hS hτ F) HEq.rfl)

/-- The composition comparison `τ_* ⋙ f_* ≅ (τ ≫ f)_*`, on underlying sheaves of sets. -/
private theorem heq_moduleSheaf_compIso_hom (f : X ⟶ Y) {τ : U ⟶ X} (hτ : IsEtale B S hS τ.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    HEq ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        ((modulePushforwardCompIso B S hS τ f).hom.app
          ((etaleModulePullback.{u, u} B S hS τ hτ).obj F)))
      ((smallEtaleDirectImageCompIso B S hS τ f).hom.app
        ((smallEtaleSetRestriction B S hS τ hτ).obj
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F))) :=
  (heq_of_eq (moduleSheafFunctor_map_modulePushforwardCompIso_hom_app B S hS τ f
      ((etaleModulePullback.{u, u} B S hS τ hτ).obj F))).trans
    (heq_app _ _ _ _ rfl rfl HEq.rfl rfl)

/-- The inverse composition comparison, on underlying sheaves of sets. -/
private theorem heq_moduleSheaf_compIso_inv (f : X ⟶ Y) {τ : U ⟶ X} (hτ : IsEtale B S hS τ.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    HEq ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        ((modulePushforwardCompIso B S hS τ f).inv.app
          ((etaleModulePullback.{u, u} B S hS τ hτ).obj F)))
      ((smallEtaleDirectImageCompIso B S hS τ f).inv.app
        ((smallEtaleSetRestriction B S hS τ hτ).obj
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F))) :=
  (heq_of_eq (moduleSheafFunctor_map_modulePushforwardCompIso_inv_app B S hS τ f
      ((etaleModulePullback.{u, u} B S hS τ hτ).obj F))).trans
    (heq_app _ _ _ _ rfl rfl HEq.rfl rfl)

/-! ### The arrows -/

/-- **The first arrow of Stacks 03M8 on underlying sheaves of sets.** -/
theorem heq_moduleSheafFunctor_map_moduleChartDirectImageUnitArrow (f : X ⟶ Y) {τ : U ⟶ X}
    (hτ : IsEtale B S hS τ.hom) (F : Modules.{u, u} B S hS X.1 X.2) :
    HEq ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        (moduleChartDirectImageUnitArrow B S hS f hτ F))
      (chartDirectImageUnitArrow B S hS f hτ
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F)) := by
  refine (heq_of_eq (map_eq_comp_of_eq (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)) _ _
      (moduleChartDirectImageUnitArrow.eq_1 B S hS f hτ F))).trans
    (HEq.trans (heq_comp _ _ _ _ ?o1 ?o2 ?o3 ?ha ?hb)
      (heq_of_eq (chartDirectImageUnitArrow.eq_1 B S hS f hτ _).symm))
  case o1 => exact moduleSheaf_modulePushforward B S hS f F
  case o2 =>
    exact (moduleSheaf_modulePushforward B S hS f _).trans
      (congrArg (smallEtaleDirectImage B S hS f).obj
        ((congrArg (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj
          (Functor.comp_obj _ _ _)).trans (moduleSheaf_restriction_unit_obj B S hS hτ F)))
  case o3 => exact moduleSheaf_modulePushforward_etaleModulePullback B S hS (τ ≫ f) τ hτ F
  case ha =>
    refine HEq.trans ?_ (heq_moduleSheaf_unit B S hS f hτ F)
    refine heq_map _ _ _ ?_ rfl ?_
    · exact congrArg (modulePushforward B S hS f).obj (Functor.id_obj F).symm
    · exact heq_map _ _ _ (Functor.id_obj F).symm rfl HEq.rfl
  case hb =>
    refine HEq.trans ?_ (heq_moduleSheaf_compIso_hom B S hS f hτ F)
    refine heq_map _ _ _ ?_ rfl ?_
    · exact (congrArg (modulePushforward B S hS f).obj (Functor.comp_obj _ _ _)).trans
        (Functor.comp_obj _ _ _).symm
    · exact heq_app _ _ _ _ rfl rfl HEq.rfl rfl


/-- **The arrow `τ_*(F|_U) ⟶ ρ_*(F|_R)` of a factorization, on underlying sheaves of sets.** -/
theorem heq_moduleSheafFunctor_map_moduleRestrictionUnitArrow {τ : U ⟶ X}
    (hτ : IsEtale B S hS τ.hom) {h : R ⟶ U} (hh : IsEtale B S hS h.hom) {ρ : R ⟶ X}
    (hρ : IsEtale B S hS ρ.hom) (hfac : h ≫ τ = ρ) (F : Modules.{u, u} B S hS X.1 X.2) :
    HEq ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        (moduleRestrictionUnitArrow B S hS hτ hh hρ hfac F))
      (restrictionUnitArrow B S hS hτ hh hρ hfac
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F)) := by
  subst hfac
  refine (heq_of_eq (map_eq_comp_of_eq (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)) _ _
      (moduleRestrictionUnitArrow.eq_1 B S hS hτ hh hρ rfl F))).trans
    (HEq.trans (heq_comp _ _ _ _ ?o1 ?o2 ?o3 ?ha ?hb)
      (heq_of_eq (restrictionUnitArrow.eq_1 B S hS hτ hh hρ rfl _).symm))
  case o1 => exact moduleSheaf_modulePushforward_etaleModulePullback B S hS τ τ hτ F
  case o2 =>
    exact (moduleSheaf_modulePushforward B S hS τ _).trans
      (congrArg (smallEtaleDirectImage B S hS τ).obj
        ((congrArg (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS U)).obj
          (Functor.comp_obj _ _ _)).trans
          ((moduleSheaf_restriction_unit_obj B S hS hh _).trans
            (congrArg (smallEtaleSetRestriction B S hS h hh ⋙ smallEtaleDirectImage B S hS h).obj
              (moduleSheaf_etaleModulePullback B S hS τ hτ F)))))
  case o3 => exact moduleSheaf_modulePushforward_etaleModulePullback B S hS (h ≫ τ) (h ≫ τ) hρ F
  case ha =>
    refine HEq.trans ?_ ((heq_moduleSheaf_unit B S hS τ hh
      ((etaleModulePullback.{u, u} B S hS τ hτ).obj F)).trans ?_)
    · refine heq_map _ _ _ ?_ rfl ?_
      · exact congrArg (modulePushforward B S hS τ).obj
          (Functor.id_obj ((etaleModulePullback.{u, u} B S hS τ hτ).obj F)).symm
      · refine heq_map _ _ _ (Functor.id_obj ((etaleModulePullback.{u, u} B S hS τ hτ).obj F)).symm
          rfl ?_
        dsimp only [Functor.id_obj]
        exact heq_app_id _ _ _ _ rfl HEq.rfl rfl
    · exact heq_map _ _ _
        (congrArg (𝟭 (Sheaf (SmallEtale.topology B S hS U.1) (Type u))).obj
          (moduleSheaf_etaleModulePullback B S hS τ hτ F))
        (congrArg (smallEtaleSetRestriction B S hS h hh ⋙ smallEtaleDirectImage B S hS h).obj
          (moduleSheaf_etaleModulePullback B S hS τ hτ F))
        (heq_app _ _ _ _ rfl rfl HEq.rfl (moduleSheaf_etaleModulePullback B S hS τ hτ F))
  case hb =>
    refine HEq.trans ?_ ((heq_moduleSheaf_compIso_hom B S hS τ hh
      ((etaleModulePullback.{u, u} B S hS τ hτ).obj F)).trans ?_)
    · heq_congr
    · exact heq_app _ _ _ _ rfl rfl HEq.rfl
        ((congrArg (smallEtaleSetRestriction B S hS h hh).obj
          (moduleSheaf_etaleModulePullback B S hS τ hτ F)).trans
          (smallEtaleSetRestriction_comp_obj B S hS h τ hh hτ hρ _))


/-- **The second arrow `a_*(F|_U) ⟶ b_*(F|_R)` of Stacks 03M8 on underlying sheaves of sets.** -/
theorem heq_moduleSheafFunctor_map_moduleChartDirectImageParallelArrow (f : X ⟶ Y) {τ : U ⟶ X}
    (hτ : IsEtale B S hS τ.hom) {h : R ⟶ U} (hh : IsEtale B S hS h.hom) {ρ : R ⟶ X}
    (hρ : IsEtale B S hS ρ.hom) (hfac : h ≫ τ = ρ) (F : Modules.{u, u} B S hS X.1 X.2) :
    HEq ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        (moduleChartDirectImageParallelArrow B S hS f hτ hh hρ hfac F))
      (chartDirectImageParallelArrow B S hS f hτ hh hρ hfac
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F)) := by
  have o2 : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).obj
      ((modulePushforward B S hS τ ⋙ modulePushforward B S hS f).obj
        ((etaleModulePullback.{u, u} B S hS τ hτ).obj F)) =
      (smallEtaleDirectImage B S hS τ ⋙ smallEtaleDirectImage B S hS f).obj
        ((smallEtaleSetRestriction B S hS τ hτ).obj
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F)) :=
    (congrArg (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).obj
      (Functor.comp_obj _ _ _)).trans ((moduleSheaf_modulePushforward B S hS f _).trans
        ((congrArg (smallEtaleDirectImage B S hS f).obj
          (moduleSheaf_modulePushforward_etaleModulePullback B S hS τ τ hτ F)).trans
          (Functor.comp_obj _ _ _).symm))
  refine (heq_of_eq (map_eq_comp_of_eq (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)) _ _
      (moduleChartDirectImageParallelArrow.eq_1 B S hS f hτ hh hρ hfac F))).trans
    (HEq.trans (heq_comp _ _ _ _ ?o1 o2 ?o3 ?hinv ?hrest)
      (heq_of_eq (chartDirectImageParallelArrow.eq_1 B S hS f hτ hh hρ hfac _).symm))
  case o1 => exact moduleSheaf_modulePushforward_etaleModulePullback B S hS (τ ≫ f) τ hτ F
  case o3 => exact moduleSheaf_modulePushforward_etaleModulePullback B S hS (ρ ≫ f) ρ hρ F
  case hinv =>
    refine HEq.trans ?_ ((heq_moduleSheaf_compIso_inv B S hS f hτ F).trans ?_)
    · heq_congr
    · heq_congr
  case hrest =>
    heq_split_map_comp
    refine (heq_comp _ _ _ _ o2 ?p2
        (moduleSheaf_modulePushforward_etaleModulePullback B S hS (ρ ≫ f) ρ hρ F) ?hm ?hhom)
    case p2 =>
      exact (moduleSheaf_modulePushforward B S hS f _).trans
        (congrArg (smallEtaleDirectImage B S hS f).obj
          (moduleSheaf_modulePushforward_etaleModulePullback B S hS ρ ρ hρ F))
    case hm =>
      refine HEq.trans ?_ ((heq_of_eq (moduleSheafFunctor_map_modulePushforward_map B S hS f
        (moduleRestrictionUnitArrow B S hS hτ hh hρ hfac F))).trans
        ((heq_map (smallEtaleDirectImage B S hS f) _
          (restrictionUnitArrow B S hS hτ hh hρ hfac
            ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F))
          (moduleSheaf_modulePushforward_etaleModulePullback B S hS τ τ hτ F)
          (moduleSheaf_modulePushforward_etaleModulePullback B S hS ρ ρ hρ F)
          (heq_moduleSheafFunctor_map_moduleRestrictionUnitArrow B S hS hτ hh hρ hfac F)).trans ?_))
      · heq_congr
      · heq_congr
    case hhom =>
      refine HEq.trans ?_ ((heq_moduleSheaf_compIso_hom B S hS f hρ F).trans ?_)
      · heq_congr
      · heq_congr

/-! ### The sequence -/

section Sequence

variable (f : X ⟶ Y) {U R : SmallEtale B S hS X.1}

/-- The parallel arrow of the chart `R ⟶ U` on underlying sheaves of sets. -/
private theorem heq_parallel_chart (t : R ⟶ U) (F : Modules.{u, u} B S hS X.1 X.2) :
    HEq ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        (moduleChartDirectImageParallelArrow B S hS f ((comparisonFunctor B S hS X).obj U).2
          (isEtale_chartMap B S hS X t) ((comparisonFunctor B S hS X).obj R).2
          (Over.w ((comparisonFunctor B S hS X).map t).hom) F))
      (chartDirectImageParallelArrow B S hS f ((comparisonFunctor B S hS X).obj U).2
        (isEtale_chartMap B S hS X t) ((comparisonFunctor B S hS X).obj R).2
        (Over.w ((comparisonFunctor B S hS X).map t).hom)
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F)) :=
  heq_moduleSheafFunctor_map_moduleChartDirectImageParallelArrow B S hS f
    ((comparisonFunctor B S hS X).obj U).2 (isEtale_chartMap B S hS X t)
    ((comparisonFunctor B S hS X).obj R).2
    (Over.w ((comparisonFunctor B S hS X).map t).hom) F

/-- The image under the sheaf-of-sets functor of the first arrow followed by a parallel arrow is
the corresponding composite of sheaves of sets. -/
private theorem heq_moduleSheafFunctor_map_comp (t : R ⟶ U) (F : Modules.{u, u} B S hS X.1 X.2) :
    HEq ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        (moduleChartDirectImageUnitArrow B S hS f ((comparisonFunctor B S hS X).obj U).2 F ≫
          moduleChartDirectImageParallelArrow B S hS f ((comparisonFunctor B S hS X).obj U).2
            (isEtale_chartMap B S hS X t) ((comparisonFunctor B S hS X).obj R).2
            (Over.w ((comparisonFunctor B S hS X).map t).hom) F))
      (chartDirectImageUnitArrow B S hS f ((comparisonFunctor B S hS X).obj U).2
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) ≫
        chartDirectImageParallelArrow B S hS f ((comparisonFunctor B S hS X).obj U).2
          (isEtale_chartMap B S hS X t) ((comparisonFunctor B S hS X).obj R).2
          (Over.w ((comparisonFunctor B S hS X).map t).hom)
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F)) := by
  heq_split_map_comp
  refine HEq.trans ?_ ((heq_comp _ _ _ _ (moduleSheaf_modulePushforward B S hS f F)
    (moduleSheaf_modulePushforward_etaleModulePullback B S hS _ _ _ F)
    (moduleSheaf_modulePushforward_etaleModulePullback B S hS _ _ _ F)
    (heq_moduleSheafFunctor_map_moduleChartDirectImageUnitArrow B S hS f
      ((comparisonFunctor B S hS X).obj U).2 F)
    (heq_parallel_chart B S hS f t F)).trans ?_)
  · heq_congr
  · heq_congr

/-- **The sequence of Stacks 03M8 is a complex**: the first arrow followed by `t^*` agrees with the
first arrow followed by `s^*`.  It is the corresponding statement on underlying sheaves of sets,
`AlgebraicGeometry.Space.fork_condition_chartDirectImageCanonical`, carried back along the
faithful functor to sheaves of sets. -/
theorem moduleChartDirectImage_fork_condition (t s : R ⟶ U) (F : Modules.{u, u} B S hS X.1 X.2) :
    moduleChartDirectImageUnitArrow B S hS f ((comparisonFunctor B S hS X).obj U).2 F ≫
        moduleChartDirectImageParallelArrow B S hS f ((comparisonFunctor B S hS X).obj U).2
          (isEtale_chartMap B S hS X t) ((comparisonFunctor B S hS X).obj R).2
          (Over.w ((comparisonFunctor B S hS X).map t).hom) F =
      moduleChartDirectImageUnitArrow B S hS f ((comparisonFunctor B S hS X).obj U).2 F ≫
        moduleChartDirectImageParallelArrow B S hS f ((comparisonFunctor B S hS X).obj U).2
          (isEtale_chartMap B S hS X s) ((comparisonFunctor B S hS X).obj R).2
          (Over.w ((comparisonFunctor B S hS X).map s).hom) F :=
  by
  apply Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor
    (R := structureRingSheaf B S hS Y)
  have h1 := heq_moduleSheafFunctor_map_comp B S hS f t F
  have h2 := heq_moduleSheafFunctor_map_comp B S hS f s F
  have h3 := fork_condition_chartDirectImageCanonical B S hS f
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) t s
  refine eq_of_heq (HEq.trans ?_ (h1.trans (HEq.trans ?_ ((heq_of_eq h3).trans
    (HEq.trans ?_ (h2.symm.trans ?_))))))
  all_goals heq_congr

/-- The first arrow composed with the difference `t^* - s^*` is zero. -/
theorem moduleChartDirectImage_comp_sub_eq_zero (t s : R ⟶ U)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    moduleChartDirectImageUnitArrow B S hS f ((comparisonFunctor B S hS X).obj U).2 F ≫
        (moduleChartDirectImageParallelArrow B S hS f ((comparisonFunctor B S hS X).obj U).2
            (isEtale_chartMap B S hS X t) ((comparisonFunctor B S hS X).obj R).2
            (Over.w ((comparisonFunctor B S hS X).map t).hom) F -
          moduleChartDirectImageParallelArrow B S hS f ((comparisonFunctor B S hS X).obj U).2
            (isEtale_chartMap B S hS X s) ((comparisonFunctor B S hS X).obj R).2
            (Over.w ((comparisonFunctor B S hS X).map s).hom) F) = 0 :=
  (Preadditive.comp_sub _ _ _).trans
    (sub_eq_zero.mpr (moduleChartDirectImage_fork_condition B S hS f t s F))

/-- **The equalizer form of Stacks 03M8.**  For a surjective étale scheme chart `U` of `X`, the
relation `R = U ×_X U` with its two projections `t, s`, and an `𝒪_X`-module `F`, the first arrow
`f_*F ⟶ a_*(F|_U)` is an equalizer of `t^*, s^* : a_*(F|_U) ⟶ b_*(F|_R)` in `Mod(𝒪_Y)`. -/
theorem nonempty_isLimitForkModuleChartDirectImage (hU : IsSurjective B S hS U.1.hom)
    {t s : R ⟶ U}
    (hR : IsPullback ((comparisonFunctor B S hS X).map t) ((comparisonFunctor B S hS X).map s)
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U)))
    (F : Modules.{u, u} B S hS X.1 X.2) :
    Nonempty (IsLimit (Fork.ofι
      (moduleChartDirectImageUnitArrow B S hS f ((comparisonFunctor B S hS X).obj U).2 F)
      (moduleChartDirectImage_fork_condition B S hS f t s F))) := by
  refine ⟨Stacks.Sheaves.RingedToposModules.isLimitForkOfIsLimitForkModuleSheaf
    (R := structureRingSheaf B S hS Y) (moduleChartDirectImage_fork_condition B S hS f t s F) ?_⟩
  refine isLimitForkOfHEq _ (fork_condition_chartDirectImageCanonical B S hS f
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) t s) ?hA ?hM ?hN ?hι ?hφ ?hψ
    (isLimitForkSheafChartDirectImageCanonical B S hS f
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) hU hR)
  case hA => exact moduleSheaf_modulePushforward B S hS f F
  case hM => exact moduleSheaf_modulePushforward_etaleModulePullback B S hS _ _ _ F
  case hN => exact moduleSheaf_modulePushforward_etaleModulePullback B S hS _ _ _ F
  case hι =>
    exact heq_moduleSheafFunctor_map_moduleChartDirectImageUnitArrow B S hS f
      ((comparisonFunctor B S hS X).obj U).2 F
  case hφ => exact heq_parallel_chart B S hS f t F
  case hψ => exact heq_parallel_chart B S hS f s F

/-- **Stacks 03M8.**  Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`, let `U` be a
surjective étale scheme chart of `X` with structure morphism `τ`, let `R = U ×_X U` (the
cartesian square `hR` in the spaces-étale site of `X`) with its two projections `t, s : R ⟶ U`
and structure morphism `ρ`, and put `a = τ ≫ f`, `b = ρ ≫ f`.  For every `𝒪_X`-module `F` the
sequence

`0 → f_*F → a_*(F|_U) → b_*(F|_R)`

of `𝒪_Y`-modules, whose first arrow is `AlgebraicGeometry.Space.moduleChartDirectImageUnitArrow`
and whose second arrow is the difference `t^* - s^*` of the two arrows
`AlgebraicGeometry.Space.moduleChartDirectImageParallelArrow`, is exact: the short complex is
exact and its first arrow is a monomorphism. -/
@[stacks 03M8]
theorem exact_moduleChartDirectImage (hU : IsSurjective B S hS U.1.hom) {t s : R ⟶ U}
    (hR : IsPullback ((comparisonFunctor B S hS X).map t) ((comparisonFunctor B S hS X).map s)
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U)))
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (ShortComplex.mk
        (moduleChartDirectImageUnitArrow B S hS f ((comparisonFunctor B S hS X).obj U).2 F)
        (moduleChartDirectImageParallelArrow B S hS f ((comparisonFunctor B S hS X).obj U).2
            (isEtale_chartMap B S hS X t) ((comparisonFunctor B S hS X).obj R).2
            (Over.w ((comparisonFunctor B S hS X).map t).hom) F -
          moduleChartDirectImageParallelArrow B S hS f ((comparisonFunctor B S hS X).obj U).2
            (isEtale_chartMap B S hS X s) ((comparisonFunctor B S hS X).obj R).2
            (Over.w ((comparisonFunctor B S hS X).map s).hom) F)
        (moduleChartDirectImage_comp_sub_eq_zero B S hS f t s F)).Exact ∧
      Mono (moduleChartDirectImageUnitArrow B S hS f ((comparisonFunctor B S hS X).obj U).2 F) :=
  ShortComplex.exact_and_mono_of_isLimit_fork _ _ _ _
    (nonempty_isLimitForkModuleChartDirectImage B S hS f hU hR F)

end Sequence

end AlgebraicGeometry.Space

end
