module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AwaySections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CechSliceRestriction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.SheafifiedCech
public import StacksFrontier.RingTheory.Cech.PresheafSummand

/-!
# The summands of the presheaf of Čech complexes are the localizations of `𝒪` at the subproducts

Let `(𝒞, 𝒪)` be a ringed site and let `f_1, …, f_r` be global sections of `𝒪`. The presheaf of
extended alternating Čech complexes has, in degree `p`, the direct sum over the `p`-element subsets
`S ⊆ {1, …, r}` of the presheaves `V ↦ 𝒪(V)_{f_S}`. Such a summand is the presheaf of sectionwise
localizations away from the global section `f_S = ∏_{i ∈ S} f_i`, so its sheafification is the
sheaf `𝒪_{f_S}` of `AlgebraicGeometry.RingedSite.awayModule`, and the identification is natural
in `S`.

## Main definitions

* `AlgebraicGeometry.RingedSite.cechSummandPresheaf`: one summand `V ↦ 𝒪(V)_{f_S}` of the
  presheaf of Čech complexes, as a presheaf of `𝒪`-modules, with
  `AlgebraicGeometry.RingedSite.unitToCechSummandPresheaf` the canonical map out of `𝒪`.
* `AlgebraicGeometry.RingedSite.cechSummandTransition` and
  `AlgebraicGeometry.RingedSite.cechSummandFunctor`: the transition map of two summands for
  `S ⊆ T`, and the system of all of them on the poset of subsets.
* `AlgebraicGeometry.RingedSite.cechSummandToAwayModulePresheaf` and
  `AlgebraicGeometry.RingedSite.awayModulePresheafToCechSummand`: the two comparison maps with
  the presheaf of sectionwise localizations away from `f_S`.

## Main results

* `AlgebraicGeometry.RingedSite.isLocalizedModule_unitToCechSummandPresheaf`: over every object
  the canonical map into a Čech summand is the localization of the ring of sections at the powers
  of `f_S` there.
* `AlgebraicGeometry.RingedSite.cechSummandIsoAwayModulePresheaf`: a Čech summand is the
  presheaf of sectionwise localizations away from `f_S`, compatibly with the canonical maps out
  of `𝒪` (`AlgebraicGeometry.RingedSite.unitToCechSummandPresheaf_comp_iso`).
* `AlgebraicGeometry.RingedSite.cechSummandSheafificationIso`: the sheafification of a Čech
  summand is `𝒪_{f_S}`, compatibly with the canonical maps out of `𝒪`
  (`AlgebraicGeometry.RingedSite.toModuleSheafification_comp_cechSummandSheafificationIso`).
* `AlgebraicGeometry.RingedSite.cechSummandFunctorSheafificationIso`: the system of Čech
  summands, sheafified, is the system `S ↦ 𝒪_{f_S}`.
* `AlgebraicGeometry.RingedSite.toModuleSheafification_comp_map`: sheafifying a map of presheaves
  of modules after the canonical map out of a sheaf of modules is the canonical map of the
  composite.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
* [Stacks Project, Tag 0EMC](https://stacks.math.columbia.edu/tag/0EMC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-! ### The summands and their transition maps -/

/-- One summand of the presheaf of Čech complexes of a finite family of global sections of `𝒪`:
over an object `V` it is the localization `𝒪(V)_{f_S}` of the ring of sections at the subproduct
indexed by `S`, as a presheaf of `𝒪`-modules. -/
def cechSummandPresheaf (S : Finset (Fin r)) :
    PresheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj :=
  Stacks.CechPresheaf.cechLocPresheaf X.O.obj (cechFamily X f) (cechFamily_map X f) S

/-- The transition map `𝒪(-)_{f_S} ⟶ 𝒪(-)_{f_T}` of two summands, for `S ⊆ T`: over each object
it is the transition map of the Čech complex of the ring of sections. -/
def cechSummandTransition {S T : Finset (Fin r)} (hST : S ⊆ T) :
    cechSummandPresheaf X f S ⟶ cechSummandPresheaf X f T :=
  Stacks.CechPresheaf.cechLocTransition X.O.obj (cechFamily X f) (cechFamily_map X f) hST

/-- The system of all the summands, as a functor on the poset of subsets of `{1, …, r}` with
values in presheaves of `𝒪`-modules. -/
def cechSummandFunctor :
    Finset (Fin r) ⥤ PresheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj :=
  Stacks.CechPresheaf.cechLocFunctor X.O.obj (cechFamily X f) (cechFamily_map X f)

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The value of the system of summands at a subset is that summand. -/
@[simp]
theorem cechSummandFunctor_obj (S : Finset (Fin r)) :
    (cechSummandFunctor X f).obj S = cechSummandPresheaf X f S :=
  rfl

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The value of the system of summands at an inclusion is the transition map. -/
@[simp]
theorem cechSummandFunctor_map {S T : Finset (Fin r)} (h : S ⟶ T) :
    (cechSummandFunctor X f).map h = cechSummandTransition X f (leOfHom h) :=
  rfl

/-! ### The canonical map out of `𝒪` -/

omit [HasWeakSheafify X.J CommRingCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}] in
/-- The localizing submonoid of the summand indexed by `S` is the one of the structure sheaf away
from the global section `f_S`. -/
theorem cechSub_eq_awayMultiplicativeSubpresheaf (S : Finset (Fin r)) (V : X.Cᵒᵖ) :
    Cech.cechSub (cechFamily X f V) S =
      (awayMultiplicativeSubpresheaf (prodGlobalSection f S)).obj V :=
  (congrArg Submonoid.powers (globalSectionVal_prodGlobalSection f S V)).symm

/-- The canonical map `𝒪 ⟶ 𝒪(-)_{f_S}` into a Čech summand, which over every object is the
localization map of the ring of sections at the powers of the subproduct. -/
def unitToCechSummandPresheaf (S : Finset (Fin r)) :
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))).val ⟶
      cechSummandPresheaf X f S where
  app V := by
    change ModuleCat.of (X.O.obj.obj V) (X.O.obj.obj V) ⟶
      ModuleCat.of (X.O.obj.obj V) (Cech.cechMod (cechFamily X f V) (X.O.obj.obj V) S)
    exact ModuleCat.ofHom
      (LocalizedModule.mkLinearMap (Cech.cechSub (cechFamily X f V) S) (X.O.obj.obj V))
  naturality {V W} a := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact (Stacks.CechSemilinear.locMap_mkLinearMap (X.O.obj.map a).hom
      (Cech.cechSub (cechFamily X f V) S) (Cech.cechSub (cechFamily X f W) S)
      (Stacks.CechSemilinear.cechSub_le_comap (X.O.obj.map a).hom (cechFamily X f V)
        (cechFamily X f W) (cechFamily_map X f a) S) x).symm

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The canonical maps out of `𝒪` are compatible with the transition maps. -/
theorem unitToCechSummandPresheaf_comp_cechSummandTransition {S T : Finset (Fin r)}
    (hST : S ⊆ T) :
    unitToCechSummandPresheaf X f S ≫ cechSummandTransition X f hST =
      unitToCechSummandPresheaf X f T := by
  refine PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  exact Cech.cechι_mk_one (cechFamily X f V) (X.O.obj.obj V) hST x

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- Over every object the canonical map into a Čech summand is a localization of modules: the
module of sections of the summand indexed by `S` over `V` is the localization of `𝒪(V)` at the
powers of the value of `f_S` there. -/
theorem isLocalizedModule_unitToCechSummandPresheaf (S : Finset (Fin r)) (V : X.Cᵒᵖ) :
    IsLocalizedModule ((awayMultiplicativeSubpresheaf (prodGlobalSection f S)).obj V)
      ((unitToCechSummandPresheaf X f S).app V).hom := by
  rw [← cechSub_eq_awayMultiplicativeSubpresheaf X f S V]
  exact inferInstanceAs (IsLocalizedModule (Cech.cechSub (cechFamily X f V) S)
    (LocalizedModule.mkLinearMap (Cech.cechSub (cechFamily X f V) S) (X.O.obj.obj V)))

/-- Elements of the localizing submonoid act bijectively on the target of a localized module. -/
private theorem bijective_smul_of_isLocalizedModule {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] {S : Submonoid R}
    {g : M →ₗ[R] N} (hg : IsLocalizedModule S g) (s : S) :
    Function.Bijective fun t : N => (s : R) • t :=
  (Module.End.isUnit_iff _).1 (hg.map_units s)

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- Every power of `f_S` acts bijectively on the sections of the Čech summand indexed by `S`. -/
theorem bijective_smul_cechSummandPresheaf (S : Finset (Fin r)) (V : X.Cᵒᵖ)
    (s : (awayMultiplicativeSubpresheaf (prodGlobalSection f S)).obj V) :
    Function.Bijective fun t : (cechSummandPresheaf X f S).obj V => (s : X.O.obj.obj V) • t :=
  bijective_smul_of_isLocalizedModule (isLocalizedModule_unitToCechSummandPresheaf X f S V) s

omit [HasWeakSheafify X.J CommRingCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}] in
/-- Every power of `f_S` acts bijectively on the sections of the presheaf of sectionwise
localizations away from `f_S`. -/
theorem bijective_smul_awayModulePresheaf (S : Finset (Fin r)) (V : X.Cᵒᵖ)
    (s : (awayMultiplicativeSubpresheaf (prodGlobalSection f S)).obj V) :
    Function.Bijective fun t : (awayModulePresheaf X (prodGlobalSection f S)).obj V =>
      (s : X.O.obj.obj V) • t :=
  bijective_smul_of_isLocalizedModule
    (isLocalizedModule_unitToAwayModulePresheaf X (prodGlobalSection f S) V) s

/-! ### The identification with the presheaf of sectionwise localizations -/

/-- The comparison of a Čech summand with the presheaf of sectionwise localizations away from
`f_S`: the lift of the canonical map of the latter through the localization map of the former. -/
def cechSummandToAwayModulePresheaf (S : Finset (Fin r)) :
    cechSummandPresheaf X f S ⟶ awayModulePresheaf X (prodGlobalSection f S) :=
  (awayMultiplicativeSubpresheaf (prodGlobalSection f S)).sectionwiseLocalizationLift
    (unitToCechSummandPresheaf X f S) (isLocalizedModule_unitToCechSummandPresheaf X f S)
    (unitToAwayModulePresheaf X (prodGlobalSection f S))
    (bijective_smul_awayModulePresheaf X f S)

/-- The comparison in the other direction: the lift of the canonical map into the Čech summand
through the localization map of the presheaf of sectionwise localizations. -/
def awayModulePresheafToCechSummand (S : Finset (Fin r)) :
    awayModulePresheaf X (prodGlobalSection f S) ⟶ cechSummandPresheaf X f S :=
  (awayMultiplicativeSubpresheaf (prodGlobalSection f S)).sectionwiseLocalizationLift
    (unitToAwayModulePresheaf X (prodGlobalSection f S))
    (isLocalizedModule_unitToAwayModulePresheaf X (prodGlobalSection f S))
    (unitToCechSummandPresheaf X f S) (bijective_smul_cechSummandPresheaf X f S)

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The first comparison map is a map over `𝒪`. -/
theorem unitToCechSummandPresheaf_comp_toAwayModulePresheaf (S : Finset (Fin r)) :
    unitToCechSummandPresheaf X f S ≫ cechSummandToAwayModulePresheaf X f S =
      unitToAwayModulePresheaf X (prodGlobalSection f S) :=
  (awayMultiplicativeSubpresheaf (prodGlobalSection f S)).comp_sectionwiseLocalizationLift _ _ _ _

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The second comparison map is a map over `𝒪`. -/
theorem unitToAwayModulePresheaf_comp_toCechSummandPresheaf (S : Finset (Fin r)) :
    unitToAwayModulePresheaf X (prodGlobalSection f S) ≫ awayModulePresheafToCechSummand X f S =
      unitToCechSummandPresheaf X f S :=
  (awayMultiplicativeSubpresheaf (prodGlobalSection f S)).comp_sectionwiseLocalizationLift _ _ _ _

/-- A Čech summand is isomorphic to the presheaf of sectionwise localizations away from `f_S`. -/
def cechSummandIsoAwayModulePresheaf (S : Finset (Fin r)) :
    cechSummandPresheaf X f S ≅ awayModulePresheaf X (prodGlobalSection f S) where
  hom := cechSummandToAwayModulePresheaf X f S
  inv := awayModulePresheafToCechSummand X f S
  hom_inv_id :=
    (awayMultiplicativeSubpresheaf (prodGlobalSection f S)).hom_ext_of_isLocalizedModule
      (unitToCechSummandPresheaf X f S) (isLocalizedModule_unitToCechSummandPresheaf X f S)
      (bijective_smul_cechSummandPresheaf X f S)
      ((Category.assoc _ _ _).symm.trans
        ((unitToCechSummandPresheaf_comp_toAwayModulePresheaf X f S =≫
            awayModulePresheafToCechSummand X f S).trans
          ((unitToAwayModulePresheaf_comp_toCechSummandPresheaf X f S).trans
            (Category.comp_id _).symm)))
  inv_hom_id :=
    (awayMultiplicativeSubpresheaf (prodGlobalSection f S)).hom_ext_of_isLocalizedModule
      (unitToAwayModulePresheaf X (prodGlobalSection f S))
      (isLocalizedModule_unitToAwayModulePresheaf X (prodGlobalSection f S))
      (bijective_smul_awayModulePresheaf X f S)
      ((Category.assoc _ _ _).symm.trans
        ((unitToAwayModulePresheaf_comp_toCechSummandPresheaf X f S =≫
            cechSummandToAwayModulePresheaf X f S).trans
          ((unitToCechSummandPresheaf_comp_toAwayModulePresheaf X f S).trans
            (Category.comp_id _).symm)))

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The identification of a Čech summand with the presheaf of sectionwise localizations is
compatible with the canonical maps out of `𝒪`. -/
theorem unitToCechSummandPresheaf_comp_iso (S : Finset (Fin r)) :
    unitToCechSummandPresheaf X f S ≫ (cechSummandIsoAwayModulePresheaf X f S).hom =
      unitToAwayModulePresheaf X (prodGlobalSection f S) :=
  unitToCechSummandPresheaf_comp_toAwayModulePresheaf X f S

/-! ### Sheafification -/

omit [HasWeakSheafify X.J CommRingCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}] in
/-- Sheafifying a map of presheaves of modules after the canonical map out of a sheaf of modules
is the canonical map of the composite. -/
theorem toModuleSheafification_comp_map
    {F : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {P Q : PresheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj}
    (can : F.val ⟶ P) (ψ : P ⟶ Q) :
    toModuleSheafification can ≫ (moduleSheafificationFunctor X).map ψ =
      toModuleSheafification (can ≫ ψ) := by
  have key : ∀ ε : F ⟶ (moduleSheafificationFunctor X).obj F.val,
      (ε ≫ (moduleSheafificationFunctor X).map can) ≫ (moduleSheafificationFunctor X).map ψ =
        ε ≫ (moduleSheafificationFunctor X).map (can ≫ ψ) := fun ε => by
    rw [Category.assoc, Functor.map_comp]
  exact key _

/-- The sheafification of a Čech summand is `𝒪_{f_S}`. -/
def cechSummandSheafificationIso (S : Finset (Fin r)) :
    (moduleSheafificationFunctor X).obj (cechSummandPresheaf X f S) ≅
      awayModule X (prodGlobalSection f S) :=
  (moduleSheafificationFunctor X).mapIso (cechSummandIsoAwayModulePresheaf X f S) ≪≫
    awaySheafificationIsoAwayModule X (prodGlobalSection f S)

/-- The identification `AlgebraicGeometry.RingedSite.cechSummandSheafificationIso` is compatible
with the canonical maps out of `𝒪`. -/
theorem toModuleSheafification_comp_cechSummandSheafificationIso (S : Finset (Fin r)) :
    toModuleSheafification (unitToCechSummandPresheaf X f S) ≫
        (cechSummandSheafificationIso X f S).hom =
      unitToAwayModule X (prodGlobalSection f S) := by
  show toModuleSheafification (unitToCechSummandPresheaf X f S) ≫
      ((moduleSheafificationFunctor X).map (cechSummandIsoAwayModulePresheaf X f S).hom ≫
        awaySheafificationToAwayModule X (prodGlobalSection f S)) = _
  rw [← Category.assoc, toModuleSheafification_comp_map, unitToCechSummandPresheaf_comp_iso,
    toModuleSheafification_comp_awaySheafificationToAwayModule]

/-- The identification of the sheafified Čech summands with the localizations of `𝒪` is natural
in the subset. -/
theorem cechSummandSheafificationIso_naturality {S T : Finset (Fin r)} (hST : S ⊆ T) :
    (moduleSheafificationFunctor X).map (cechSummandTransition X f hST) ≫
        (cechSummandSheafificationIso X f T).hom =
      (cechSummandSheafificationIso X f S).hom ≫ awayModuleTransition X f hST := by
  rw [← Iso.inv_comp_eq]
  refine hom_ext_unitToAwayModule X (prodGlobalSection f S) _
    (bijective_smul_awayModule_prodGlobalSection_of_subset X f hST) ?_
  have hS : unitToAwayModule X (prodGlobalSection f S) ≫
      (cechSummandSheafificationIso X f S).inv =
        toModuleSheafification (unitToCechSummandPresheaf X f S) := by
    rw [← toModuleSheafification_comp_cechSummandSheafificationIso X f S, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, hS, ← Category.assoc, toModuleSheafification_comp_map,
    unitToCechSummandPresheaf_comp_cechSummandTransition,
    toModuleSheafification_comp_cechSummandSheafificationIso,
    unitToAwayModule_comp_awayModuleTransition]

/-- The system of Čech summands, sheafified, is the system `S ↦ 𝒪_{f_S}` of localizations of the
structure sheaf. -/
def cechSummandFunctorSheafificationIso :
    cechSummandFunctor X f ⋙ moduleSheafificationFunctor X ≅ awayLocalizationFunctor X f :=
  NatIso.ofComponents (fun S => cechSummandSheafificationIso X f S) fun h =>
    cechSummandSheafificationIso_naturality X f (leOfHom h)

end AlgebraicGeometry.RingedSite

end
