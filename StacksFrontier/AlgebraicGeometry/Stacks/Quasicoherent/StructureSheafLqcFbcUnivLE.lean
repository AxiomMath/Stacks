module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherentModuleUniverse
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageFlatBaseChangeDegrees
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeFreeModules
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentGrothendieck
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeWeakSerre

/-!
# The structure sheaf and the zero modules lie in `LQCoh^fbc(𝒪_𝒳)` above the scheme universe

Let `𝒳` be an algebraic stack over `S`, with schemes in the universe `u`. Its fppf modules with
sections in a universe `t` above `u` (`AlgebraicGeometry.Stack.fppfModulesUnivLE`) contain the
subcategory `LQCoh^fbc(𝒪_𝒳)` of modules whose restriction to the étale site is locally
quasi-coherent (Stacks 06WJ) and has the flat base change property of Stacks 0762
(`AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE`). This file proves
that this subcategory is closed under isomorphisms, contains every zero module, and contains the
structure sheaf `𝒪_𝒳` with its sections lifted to `Type (max u t)`, in particular at module
universe `u + 1`.

For the structure sheaf the argument is the one at the universe of the schemes: the restriction
of the lifted structure sheaf to the small étale site of the scheme below an object is the lifted
structure sheaf of that site, which is quasi-coherent; and the comparison maps `c_φ` of
Stacks 06WC are isomorphisms for every arrow, because the lifted unit module corepresents global
sections at every module universe above that of the rings, and the base change of small étale
sites sends the final object to a final object. A zero module has zero restrictions and zero
comparison maps between zero objects.

## Main results

* `PresheafOfModules.uliftUnitHomEquiv`: morphisms out of the universe lift of the unit
  presheaf of modules are global sections.
* `PresheafOfModules.isIso_homEquiv_symm_uliftUnit`: the pullback of the lifted unit module along
  a functor sending a terminal object to a terminal object is the lifted unit module.
* `AlgebraicGeometry.Stack.isLocallyQuasicoherent_uliftUnitPresheaf` and
  `AlgebraicGeometry.Stack.hasFlatBaseChangePropertyUnivLE_uliftUnitPresheaf`: the lifted
  structure sheaf is locally quasi-coherent and has the flat base change property.
* `AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE_uliftUnit` and
  `AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE_uliftUnit_succ`:
  the structure sheaf lies in `LQCoh^fbc(𝒪_𝒳)` at module universe `max u t`, resp. `u + 1`.
* `AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE_of_isZero`: the
  zero modules lie in `LQCoh^fbc(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE_of_iso` and
  `isClosedUnderIsomorphisms_locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE`:
  `LQCoh^fbc(𝒪_𝒳)` is closed under isomorphisms.

## Implementation notes

The unit module `SheafOfModules.unit` of a sheaf of rings in `RingCat.{u}` has its sections in
`Type u`; the structure sheaf at a larger module universe is its universe lift
`Stacks.SheafOfModules.uliftUnit`, which is what `AlgebraicGeometry.Stack.fppfModulesULiftUnit`
names at module universe `u + 1`.

## References

* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u t v w m

namespace PresheafOfModules

section ULiftUnit

variable {C : Type*} [Category* C] {R₀ : Cᵒᵖ ⥤ RingCat.{u}}

/-- The generator `ULift.up 1` of the universe lift of the unit presheaf of modules over `X`. -/
abbrev uliftUnitGen (R₀ : Cᵒᵖ ⥤ RingCat.{u}) (X : Cᵒᵖ) : ((unit R₀).uliftSections.{t}).obj X :=
  ULift.up (show (unit R₀).obj X from (1 : R₀.obj X))

/-- Morphisms out of the universe lift of the unit presheaf of modules are global sections. -/
def uliftUnitHomEquiv (M : PresheafOfModules.{max u t} R₀) :
    ((unit R₀).uliftSections.{t} ⟶ M) ≃ M.sections where
  toFun f := sectionsMk (fun X => f.app X (uliftUnitGen R₀ X))
    (fun X Y g => by
      rw [← naturality_apply]
      exact congrArg (fun z => f.app Y z) (ULift.ext (unit_map_one _ g)))
  invFun s :=
    { app := fun X => ModuleCat.ofHom
        { toFun := fun y => (ULift.down y : R₀.obj X) • s.eval X
          map_add' := fun y y' => add_smul (ULift.down y : R₀.obj X) (ULift.down y') (s.eval X)
          map_smul' := fun a y => mul_smul a (ULift.down y : R₀.obj X) (s.eval X) }
      naturality := fun {X Y} f => by
        ext y
        change (R₀.map f).hom (ULift.down y : R₀.obj X) • s.eval Y =
          M.map f ((ULift.down y : R₀.obj X) • s.eval X)
        rw [PresheafOfModules.map_smul, sections_property]
        rfl }
  left_inv f := by
    ext X y
    change (ULift.down y : R₀.obj X) • f.app X (uliftUnitGen R₀ X) = f.app X y
    have hy : (ULift.down y : R₀.obj X) • uliftUnitGen.{u, t} R₀ X = y :=
      ULift.ext (mul_one (ULift.down y : R₀.obj X))
    exact ((f.app X).hom.map_smul _ _).symm.trans (congrArg (fun z => f.app X z) hy)
  right_inv s := by
    refine sections_ext _ _ fun X => ?_
    change (1 : R₀.obj X) • s.eval X = s.eval X
    exact one_smul _ _

/-- A presheaf of modules whose modules of sections are all trivial is a zero object. -/
theorem isZero_of_subsingleton {P : PresheafOfModules.{v} R₀}
    (hP : ∀ X, Subsingleton (P.obj X)) : IsZero P :=
  (IsZero.iff_id_eq_zero P).2 (hom_ext fun X =>
    ModuleCat.hom_ext (LinearMap.ext fun _ => (hP X).elim _ _))

end ULiftUnit

section Pullback

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {F : C ⥤ D}
  {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

variable [(pushforward.{max u t} φ).IsRightAdjoint]

/-- **The pullback of the lifted unit module is the lifted unit module**, when `F` sends a
terminal object to a terminal object: the mate of any map from the lifted unit to the
pushforward of the lifted unit which sends the generator `ULift.up 1` to the generator is an
isomorphism. -/
theorem isIso_homEquiv_symm_uliftUnit {T : C} (hT : IsTerminal T) (hFT : IsTerminal (F.obj T))
    (ρ : (unit S).uliftSections.{t} ⟶ (pushforward.{max u t} φ).obj ((unit R).uliftSections.{t}))
    (hρ : ∀ X, ρ.app X (uliftUnitGen S X) = uliftUnitGen R (op (F.obj X.unop))) :
    IsIso (((pullbackPushforwardAdjunction.{max u t} φ).homEquiv _ _).symm ρ) := by
  let adj := pullbackPushforwardAdjunction.{max u t} φ
  refine isIso_of_coyoneda_map_bijective _ fun M => ?_
  refine (Function.Bijective.of_comp_iff'
    (Equiv.bijective ((adj.homEquiv _ M).trans
      (uliftUnitHomEquiv.{u, t} ((pushforward.{max u t} φ).obj M)))) _).1 ?_
  refine (congrArg Function.Bijective ?_).mpr
    ((bijective_sectionsRestriction φ hT hFT M).comp
      (uliftUnitHomEquiv.{u, t} M).bijective)
  funext x
  refine sections_ext _ _ fun X => ?_
  simp only [Function.comp_apply, Equiv.trans_apply]
  rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply]
  change ((pushforward.{max u t} φ).map x).app X (ρ.app X (uliftUnitGen S X)) =
    x.app (op (F.obj X.unop)) (uliftUnitGen R (op (F.obj X.unop)))
  rw [hρ X]
  rfl

/-- The mate of a map `ρ : M ⟶ (pushforward φ).obj N` is an isomorphism when `M` and `N` are
identified with the lifted unit modules, `F` sends a terminal object to a terminal object, and
`ρ` sends the generator to the generator under these identifications. -/
theorem isIso_homEquiv_symm_of_iso_uliftUnit {T : C} (hT : IsTerminal T)
    (hFT : IsTerminal (F.obj T))
    {M : PresheafOfModules.{max u t} S} {N : PresheafOfModules.{max u t} R}
    (α : (unit S).uliftSections.{t} ≅ M) (β : (unit R).uliftSections.{t} ≅ N)
    (ρ : M ⟶ (pushforward.{max u t} φ).obj N)
    (hρ : ∀ X, ρ.app X (α.hom.app X (uliftUnitGen S X)) =
      β.hom.app (op (F.obj X.unop)) (uliftUnitGen R (op (F.obj X.unop)))) :
    IsIso (((pullbackPushforwardAdjunction.{max u t} φ).homEquiv _ _).symm ρ) := by
  let ρ' := α.hom ≫ ρ ≫ (pushforward.{max u t} φ).map β.inv
  have hα : ∀ W (n : M.obj W), α.hom.app W (α.inv.app W n) = n := fun W n =>
    congrArg (fun f => (f.app W).hom n) α.inv_hom_id
  have hβ : ∀ W (n : ((unit R).uliftSections.{t}).obj W), β.inv.app W (β.hom.app W n) = n :=
    fun W n => congrArg (fun f => (f.app W).hom n) β.hom_inv_id
  refine (isIso_homEquiv_symm_iff_of_sections rfl α.symm β.symm ρ ρ' fun W n => ?_).2
    (isIso_homEquiv_symm_uliftUnit φ hT hFT ρ' fun X => ?_)
  · change β.inv.app _ (ρ.app W (α.hom.app W (α.inv.app W n))) = β.inv.app _ (ρ.app W n)
    rw [hα]
  · change β.inv.app _ (ρ.app X (α.hom.app X (uliftUnitGen S X))) = _
    rw [hρ X]
    exact hβ _ _

end Pullback

end PresheafOfModules

namespace SheafOfModules

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- A sheaf of modules whose modules of sections are all trivial is a zero object. -/
theorem isZero_of_subsingleton_val_obj {M : SheafOfModules.{v} R}
    (hM : ∀ X, Subsingleton (M.val.obj X)) : IsZero M :=
  (IsZero.iff_id_eq_zero M).2 (hom_ext (PresheafOfModules.hom_ext fun X =>
    ModuleCat.hom_ext (LinearMap.ext fun _ => (hM X).elim _ _)))

/-- The modules of sections of a zero sheaf of modules are trivial. -/
theorem subsingleton_obj_of_isZero {M : SheafOfModules.{v} R} (hM : IsZero M) (X : Cᵒᵖ) :
    Subsingleton (M.val.obj X) :=
  ModuleCat.isZero_iff_subsingleton.1
    ((forget R ⋙ PresheafOfModules.evaluation R.obj X).map_isZero hM)

end SheafOfModules

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

section Presheaf

variable {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

/-- The structure sheaf of `𝒳`, as a presheaf of modules over itself, with its sections raised
from the universe `u` of the schemes to `max u t`. -/
abbrev uliftUnitPresheaf :
    PresheafOfModules.{max u t} (ringStructureSheafCore B S hS p hp τ hτ).obj :=
  (Stacks.SheafOfModules.presheafULift.{t} _).obj (PresheafOfModules.unit _)

/-- The restriction of the lifted structure sheaf of `𝒳` to the small étale site of the scheme
below `x` is the lifted structure sheaf of that small étale site. -/
def restrictModuleToSmallEtaleULiftUnitIso (x : 𝒳) :
    (PresheafOfModules.unit (SmallEtale.structureSheaf E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj).uliftSections.{t} ≅
      restrictModuleToSmallEtale B E h S hS p hp x τ hτ
        (uliftUnitPresheaf.{u, t} B S hS p hp τ hτ) :=
  (PresheafOfModules.ulift.{t}).mapIso
    (restrictModuleToSmallEtaleUnitIso B E h S hS p hp τ hτ x).symm ≪≫ Iso.refl _


/-- **The comparison map `c_φ` of Stacks 06WC of the lifted structure sheaf is an isomorphism**,
for every arrow `φ` of `𝒳`: the restrictions of the lifted structure sheaf are the lifted
structure sheaves of the small étale sites, and the base change of small étale sites sends the
final object to a final object. -/
theorem isIso_restrictModulePullbackComparisonUnivLE_uliftUnitPresheaf {x y : 𝒳} (φ : x ⟶ y) :
    IsIso (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ τ hτ
      (uliftUnitPresheaf.{u, t} B S hS p hp τ hτ)) := by
  refine PresheafOfModules.isIso_homEquiv_symm_of_iso_uliftUnit
    (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)
    (SmallEtale.finalIsTerminal E (p.obj y).left.1 (contains_base B E h S hS p y))
    (smallEtaleBaseChange_finalIsTerminal E (smallEtaleBaseMorphism B E h S hS p φ))
    (restrictModuleToSmallEtaleULiftUnitIso.{u, t} B E h S hS p hp τ hτ y)
    (restrictModuleToSmallEtaleULiftUnitIso.{u, t} B E h S hS p hp τ hτ x)
    (restrictModulePushforwardComparison B E h S hS p hp φ τ hτ _) fun W => ?_
  obtain ⟨φ', hfac, hbase⟩ := exists_restrictionComparisonLift B E h S hS p hp φ W.unop
  have hmod : (restrictionPushforwardComparison B E h S hS p hp φ
      (PresheafOfModules.unit (ringStructureSheafCore B S hS p hp τ hτ).obj).presheaf).app W =
        (PresheafOfModules.unit (ringStructureSheafCore B S hS p hp τ hτ).obj).presheaf.map
          φ'.op :=
    restrictionPushforwardComparison_app B E h S hS p hp φ _ W.unop φ' hfac hbase
  let ey := localStructurePresheafIso B E h S hS p hp y τ hτ
  let ex := localStructurePresheafIso B E h S hS p hp x τ hτ
  have key : (ringStructureSheafCore B S hS p hp τ hτ).obj.map φ'.op (ey.hom.app W 1) =
      ex.hom.app (op ((smallEtaleBaseChange E
        (smallEtaleBaseMorphism B E h S hS p φ)).obj W.unop)) 1 := by
    rw [map_one, map_one, map_one]
  change ULift.up ((restrictionPushforwardComparison B E h S hS p hp φ
      (PresheafOfModules.unit (ringStructureSheafCore B S hS p hp τ hτ).obj).presheaf).app W
        (ey.hom.app W 1)) = ULift.up (ex.hom.app _ 1)
  rw [hmod]
  exact congrArg ULift.up key

/-- **The lifted structure sheaf has the flat base change property** of Stacks 0762, read at the
module universe `max u t`: its comparison maps are isomorphisms along every arrow, flat or not. -/
theorem hasFlatBaseChangePropertyUnivLE_uliftUnitPresheaf :
    HasFlatBaseChangePropertyUnivLE B E h S hS p hp τ hτ
      (uliftUnitPresheaf.{u, t} B S hS p hp τ hτ) := by
  intro x y φ _
  exact isIso_restrictModulePullbackComparisonUnivLE_uliftUnitPresheaf B E h S hS p hp τ hτ φ

/-- **The lifted structure sheaf is locally quasi-coherent** (Stacks 06WJ): it is an étale sheaf,
and its restriction to the small étale site of the scheme below an object is the lifted
structure sheaf of that site, which is quasi-coherent. -/
theorem isLocallyQuasicoherent_uliftUnitPresheaf :
    IsLocallyQuasicoherent B E h S hS p hp
      (uliftUnitPresheaf.{u, t} B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)) := by
  have h0 : Presheaf.IsSheaf (associatedTopology B S hS p (etaleTopology B))
      (uliftUnitPresheaf.{u, t} B S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B)).presheaf :=
    ((Stacks.SheafOfModules.moduleULift.{t} (ringStructureSheafCore B S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B))).obj (SheafOfModules.unit _)).isSheaf
  refine ⟨h0, fun x => ?_⟩
  have hM := restrictModuleToSmallEtale_isSheaf B E h S hS p hp x _ h0
  refine ⟨hM, ?_⟩
  let Rs := SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)
  let e : SheafOfModules.uliftForPresentation.{_, _, _, _, t} (SheafOfModules.unit Rs) ≅
      ⟨_, hM⟩ :=
    (SheafOfModules.fullyFaithfulForget Rs).preimageIso
      (restrictModuleToSmallEtaleULiftUnitIso.{u, t} B E h S hS p hp _ _ x)
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso e
    (SheafOfModules.isQuasicoherentOnSite_uliftForPresentation'
      (SheafOfModules.isQuasicoherentOnSite_unit Rs))

/-- A presheaf of modules with trivial sections is locally quasi-coherent. -/
theorem isLocallyQuasicoherent_of_subsingleton
    (F : PresheafOfModules.{m}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : ∀ X, Subsingleton (F.obj X)) :
    IsLocallyQuasicoherent B E h S hS p hp F := by
  have hP : IsZero F.presheaf :=
    (PresheafOfModules.toPresheaf _).map_isZero (PresheafOfModules.isZero_of_subsingleton hF)
  have h0 : Presheaf.IsSheaf (associatedTopology B S hS p (etaleTopology B)) F.presheaf :=
    (Presheaf.isSheaf_of_iso_iff (hP.iso (Functor.isZero _ fun _ => isZero_zero _))).2
      (Presheaf.isSheaf_of_isTerminal _ (isZero_zero _).isTerminal)
  refine ⟨h0, fun x => ⟨restrictModuleToSmallEtale_isSheaf B E h S hS p hp x F h0, ?_⟩⟩
  have hR : IsZero (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
      (etaleTopology_le_topology B) F) :=
    (restrictModuleToSmallEtaleFunctor.{u, v, w, m} B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) x).map_isZero (PresheafOfModules.isZero_of_subsingleton hF)
  exact SheafOfModules.IsQuasicoherentOnSite.of_isZero
    (SheafOfModules.isZero_of_subsingleton_val_obj fun W =>
      ModuleCat.isZero_iff_subsingleton.1 ((PresheafOfModules.evaluation _ W).map_isZero hR))

/-- A presheaf of modules with trivial sections has the flat base change property: its
comparison maps are maps between zero objects. -/
theorem hasFlatBaseChangePropertyUnivLE_of_subsingleton [UnivLE.{u, m}]
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ hτ).obj)
    (hF : ∀ X, Subsingleton (F.obj X)) :
    HasFlatBaseChangePropertyUnivLE B E h S hS p hp τ hτ F := by
  intro x y φ _
  have := (PresheafOfModules.pullbackPushforwardAdjunction.{m}
    (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).isLeftAdjoint
  have hF0 := PresheafOfModules.isZero_of_subsingleton hF
  have h₁ : IsZero ((PresheafOfModules.pullback.{m}
      (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ))
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj
        (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)) :=
    Functor.map_isZero _
      ((restrictModuleToSmallEtaleFunctor.{u, v, w, m} B E h S hS p hp τ hτ y).map_isZero hF0)
  have h₂ : IsZero (restrictModuleToSmallEtale B E h S hS p hp x τ hτ F) :=
    (restrictModuleToSmallEtaleFunctor.{u, v, w, m} B E h S hS p hp τ hτ x).map_isZero hF0
  exact ⟨h₂.to_ _, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩

end Presheaf

section AlgebraicStack

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **`LQCoh^fbc(𝒪_𝒳)` at a module universe above that of the schemes is closed under
isomorphisms**: both conditions transport along an isomorphism of the underlying presheaves of
modules. -/
theorem locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE_of_iso [UnivLE.{u, m}]
    {M N : fppfModulesUnivLE.{u, w, m} B S hS 𝒳} (e : M ≅ N)
    (hM : locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE.{u, w, m} B E h S hS 𝒳 M) :
    locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE.{u, w, m} B E h S hS 𝒳 N := by
  let e' : M.val ≅ N.val := (SheafOfModules.forget _).mapIso e
  exact ⟨isLocallyQuasicoherent_of_iso B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids e' hM.1,
    hasFlatBaseChangePropertyUnivLE_of_iso B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      (etaleTopology B) (etaleTopology_le_topology B) e' hM.2⟩

/-- `LQCoh^fbc(𝒪_𝒳)` at a module universe above that of the schemes is closed under
isomorphisms. -/
instance isClosedUnderIsomorphisms_locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE
    [UnivLE.{u, m}] :
    (locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE.{u, w, m} B E h S hS
      𝒳).IsClosedUnderIsomorphisms where
  of_iso e hM := locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE_of_iso B E h S hS 𝒳 e hM

/-- **A zero module lies in `LQCoh^fbc(𝒪_𝒳)`**, at every module universe above that of the
schemes. -/
theorem locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE_of_isZero [UnivLE.{u, m}]
    {M : fppfModulesUnivLE.{u, w, m} B S hS 𝒳} (hM : IsZero M) :
    locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE.{u, w, m} B E h S hS 𝒳 M :=
  ⟨isLocallyQuasicoherent_of_subsingleton B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids M.val
      (SheafOfModules.subsingleton_obj_of_isZero hM),
    hasFlatBaseChangePropertyUnivLE_of_subsingleton B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B)
      (etaleTopology_le_topology B) M.val
      (SheafOfModules.subsingleton_obj_of_isZero hM)⟩

/-- **The structure sheaf of `𝒳`, with its sections lifted to the universe `max u t`, lies in
`LQCoh^fbc(𝒪_𝒳)`** at that module universe. -/
theorem locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE_uliftUnit :
    locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE.{u, w, max u t} B E h S hS 𝒳
      (Stacks.SheafOfModules.uliftUnit.{t} _) :=
  ⟨isLocallyQuasicoherent_uliftUnitPresheaf.{u, t} B E h S hS _ _,
    hasFlatBaseChangePropertyUnivLE_uliftUnitPresheaf.{u, t} B E h S hS _ _ (etaleTopology B)
      (etaleTopology_le_topology B)⟩

/-- **The structure sheaf `𝒪_𝒳` at module universe `u + 1` lies in `LQCoh^fbc(𝒪_𝒳)`**: the
universe lift of the unit module, which is the structure sheaf at that universe. -/
theorem locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE_uliftUnit_succ :
    locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE.{u, w, u + 1} B E h S hS 𝒳
      (Stacks.SheafOfModules.uliftUnit.{u + 1} _) :=
  locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE_uliftUnit.{u, u + 1} B E h S hS 𝒳

end AlgebraicStack

end AlgebraicGeometry.Stack
