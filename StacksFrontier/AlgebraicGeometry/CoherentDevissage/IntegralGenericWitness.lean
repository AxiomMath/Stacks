module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.GenericStalkCriterion
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.StructureSheafStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The generic test objects of [Stacks, Tag 01YI] on an integral scheme

[Stacks, Tag 01YI] reduces a property `P` of coherent modules to the two-out-of-three condition
in short exact sequences together with one *test object* per integral closed subscheme: a
coherent module supported exactly on that subscheme whose stalk at the generic point is killed by
the maximal ideal and has length one there. This file constructs those test objects when the
ambient scheme is integral: for an integral closed subscheme `i : Z ⟶ X` whose range is all of
`X` the test object is `𝒪_X`, and when the range of `i` is a proper closed subset it is `i_*𝒪_Z`.
The resulting induction principle has as its only inputs `P` on the structure sheaf and `P` on
everything supported in a proper closed subset.

## Main results

* `Stacks.AlgebraicGeometry.CoherentDevissage.property_of_isCoherent_of_isIntegral`: on a
  nonempty integral Noetherian scheme a property of coherent modules satisfying
  two-out-of-three, holding on every module supported in a proper closed subset, and holding on
  `𝒪_X`, holds on every coherent module.

## References

* [Stacks Project, Tag 01YI](https://stacks.math.columbia.edu/tag/01YI)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.CoherentDevissage

/-! ### The local ring at the generic point of an integral scheme -/

/-- The maximal ideal of the local ring of an integral scheme at its generic point is zero. -/
@[ega "I 8.2.1" "partial"]
private theorem maximalIdeal_stalk_eq_bot {X : Scheme.{u}} [IsIntegral X] (ξ : X)
    (hξ : IsGenericPoint ξ (Set.univ : Set X)) :
    IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) = ⊥ := by
  have hfield : IsField (X.presheaf.stalk ξ) := by
    have hξ' : ξ = genericPoint X := hξ.eq (genericPoint_spec X)
    rw [hξ']
    exact Field.toIsField X.functionField
  exact IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield

/-- A local ring whose maximal ideal is zero is a simple module over itself. -/
private theorem isSimpleModule_self_of_maximalIdeal_eq_bot (R : Type u) [CommRing R]
    [IsLocalRing R] (h : IsLocalRing.maximalIdeal R = ⊥) : IsSimpleModule R R := by
  have hnt : (⊥ : Submodule R R) ≠ (⊤ : Submodule R R) := fun hbt =>
    one_ne_zero ((Submodule.mem_bot R).mp (hbt ▸ Submodule.mem_top (x := (1 : R))))
  have : Nontrivial (Submodule R R) := ⟨⊥, ⊤, hnt⟩
  refine (isSimpleModule_iff R R).mpr (IsSimpleOrder.of_forall_eq_top fun I hI => ?_)
  by_contra htop
  exact hI (le_bot_iff.mp (h ▸ IsLocalRing.le_maximalIdeal htop))

/-! ### The test object on the whole space: the structure sheaf -/

/-- **The stalk of `𝒪_X` at the generic point of an integral scheme is killed by the maximal
ideal.** -/
private theorem stalkKilledByMaximalIdeal_unit {X : Scheme.{u}} [IsIntegral X] (ξ : X)
    (hξ : IsGenericPoint ξ (Set.univ : Set X)) :
    Stacks.ClosedImmersion.StalkKilledByMaximalIdeal (SheafOfModules.unit X.ringCatSheaf) ξ := by
  let : Module (X.presheaf.stalk ξ)
      (TopCat.Presheaf.stalk (C := Ab.{u})
        (SheafOfModules.unit X.ringCatSheaf).val.presheaf ξ) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) (SheafOfModules.unit X.ringCatSheaf).val ξ
  intro a ha s
  have ha0 : a = 0 := (Submodule.mem_bot _).mp (maximalIdeal_stalk_eq_bot ξ hξ ▸ ha)
  rw [ha0, zero_smul]

/-- **The stalk of `𝒪_X` at the generic point of an integral scheme has length one.** -/
@[ega "IV 3.2.1" "a) ⇒ c)"]
private theorem length_stalk_unit_eq_one {X : Scheme.{u}} [IsIntegral X] (ξ : X)
    (hξ : IsGenericPoint ξ (Set.univ : Set X)) :
    letI : Module (X.presheaf.stalk ξ)
        (TopCat.Presheaf.stalk (C := Ab.{u})
          (SheafOfModules.unit X.ringCatSheaf).val.presheaf ξ) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) (SheafOfModules.unit X.ringCatSheaf).val ξ
    Module.length (X.presheaf.stalk ξ)
        (TopCat.Presheaf.stalk (C := Ab.{u})
          (SheafOfModules.unit X.ringCatSheaf).val.presheaf ξ) = 1 := by
  have : IsSimpleModule (X.presheaf.stalk ξ) (X.presheaf.stalk ξ) :=
    isSimpleModule_self_of_maximalIdeal_eq_bot _ (maximalIdeal_stalk_eq_bot ξ hξ)
  exact (AlgebraicGeometry.structureSheafStalkLinearEquiv X ξ).length_eq.trans
    (Module.length_eq_one _ _)

/-- **The support of `𝒪_X` is everything.** -/
private theorem supp_unit_eq_univ (X : Scheme.{u}) :
    SheafOfModules.supp (SheafOfModules.unit X.ringCatSheaf) = (Set.univ : Set X) :=
  Set.eq_univ_of_forall (AlgebraicGeometry.mem_supp_structureSheaf X)

/-! ### The test object on a proper closed subscheme: the direct image of its structure sheaf -/

/-- The kernel of the map of local rings induced by a closed immersion of an integral scheme, at
the generic point, is the maximal ideal. -/
private theorem ker_stalkMap_eq_maximalIdeal {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIntegral Z] (z : Z)
    (hz : IsGenericPoint z (Set.univ : Set Z)) :
    RingHom.ker (i.stalkMap z).hom = IsLocalRing.maximalIdeal (X.presheaf.stalk (i z)) := by
  have hbot : (⊥ : Ideal (Z.presheaf.stalk z)).IsMaximal := by
    rw [← maximalIdeal_stalk_eq_bot z hz]
    exact IsLocalRing.maximalIdeal.isMaximal _
  have hkerMax : (RingHom.ker (i.stalkMap z).hom).IsMaximal := by
    change (Ideal.comap (i.stalkMap z).hom (⊥ : Ideal (Z.presheaf.stalk z))).IsMaximal
    exact Ideal.comap_isMaximal_of_surjective _ (i.stalkMap_surjective z) (K := ⊥) (H := hbot)
  exact IsLocalRing.eq_maximalIdeal hkerMax

/-- **The stalk of `i_*𝒪_Z` at the generic point of an integral closed subscheme is killed by the
maximal ideal.** -/
private theorem stalkKilledByMaximalIdeal_pushforward_unit {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIntegral Z] (z : Z)
    (hz : IsGenericPoint z (Set.univ : Set Z)) :
    Stacks.ClosedImmersion.StalkKilledByMaximalIdeal
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)) (i z) := by
  have hi : Topology.IsInducing (ConcreteCategory.hom i.base) :=
    (IsClosedImmersion.isClosedEmbedding i).isInducing
  intro a ha s
  have ha0 : (i.stalkMap z).hom a = 0 := by
    rw [← RingHom.mem_ker, ker_stalkMap_eq_maximalIdeal i z hz]
    exact ha
  have hzero : Stacks.Chow.structureSheafStalkComparison i z 0 = 0 := by
    let : Module (X.presheaf.stalk (i z)) (Z.presheaf.stalk z) :=
      Module.compHom (Z.presheaf.stalk z) (i.stalkMap z).hom
    exact (Stacks.Chow.stalkPushforwardStructureSheafLinearEquiv i z hi).map_zero
  exact (Stacks.Chow.bijective_structureSheafStalkComparison i z hi).1
    ((Stacks.Chow.structureSheafStalkComparison_smul i z a s).trans
      ((mul_eq_zero_of_left ha0 _).trans hzero.symm))

/-- **The stalk of `i_*𝒪_Z` at the generic point of an integral closed subscheme has length
one.** -/
private theorem length_stalk_pushforward_unit_eq_one {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIntegral Z] (z : Z)
    (hz : IsGenericPoint z (Set.univ : Set Z)) :
    letI : Module (X.presheaf.stalk (i z))
        (TopCat.Presheaf.stalk (C := Ab.{u})
          ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)).val.presheaf (i z)) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf)
        ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)).val (i z)
    Module.length (X.presheaf.stalk (i z))
        (TopCat.Presheaf.stalk (C := Ab.{u})
          ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)).val.presheaf (i z))
      = 1 := by
  have hi : Topology.IsInducing (ConcreteCategory.hom i.base) :=
    (IsClosedImmersion.isClosedEmbedding i).isInducing
  let : Module (X.presheaf.stalk (i z)) (Z.presheaf.stalk z) :=
    Module.compHom (Z.presheaf.stalk z) (i.stalkMap z).hom
  have : IsSimpleModule (Z.presheaf.stalk z) (Z.presheaf.stalk z) :=
    isSimpleModule_self_of_maximalIdeal_eq_bot _ (maximalIdeal_stalk_eq_bot z hz)
  have : RingHomSurjective (i.stalkMap z).hom := ⟨i.stalkMap_surjective z⟩
  have : IsSimpleModule (X.presheaf.stalk (i z)) (Z.presheaf.stalk z) :=
    (LinearMap.isSimpleModule_iff_of_bijective
      (σ := (i.stalkMap z).hom)
      (l := { toFun := id, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl })
      Function.bijective_id).mpr inferInstance
  exact (Stacks.Chow.length_stalk_pushforwardStructureSheaf i z hi).trans
    (Module.length_eq_one _ _)

/-! ### [Stacks, Tag 01YI] on an integral scheme -/

/-- **Dévissage on an integral Noetherian scheme.** Let `X` be an integral Noetherian scheme and
let `P` be a property of coherent `𝒪_X`-modules such that two out of three in a short exact
sequence of coherent modules force the third, such that `P` holds on every module supported in a
proper closed subset of `X`, and such that `P 𝒪_X` holds. Then `P` holds on every coherent
`𝒪_X`-module. -/
public theorem property_of_isCoherent_of_isIntegral (X : Scheme.{u}) [IsNoetherian X]
    [IsIntegral X] (P : X.Modules → Prop)
    (hexact : ∀ S : ShortComplex X.Modules, S.ShortExact →
      _root_.SheafOfModules.IsCoherent S.X₁ → _root_.SheafOfModules.IsCoherent S.X₂ →
      _root_.SheafOfModules.IsCoherent S.X₃ →
      ((P S.X₁ ∧ P S.X₂ → P S.X₃) ∧
        (P S.X₁ ∧ P S.X₃ → P S.X₂) ∧
        (P S.X₂ ∧ P S.X₃ → P S.X₁)))
    (hproper : ∀ (G : X.Modules) (Z : Set X), IsClosed Z → Z ≠ Set.univ →
      _root_.SheafOfModules.supp G ⊆ Z → P G)
    (hunit : P (SheafOfModules.unit X.ringCatSheaf)) :
    ∀ F : X.Modules, _root_.SheafOfModules.IsCoherent F → P F := by
  refine property_of_isCoherent_of_generic_stalk_of_nonempty X IsIntegral.nonempty P hexact ?_
  intro Z i hci hint ξ hξ
  have hclosed : IsClosed (Set.range i.base) := i.isClosedEmbedding.isClosed_range
  by_cases hrange : Set.range i.base = (Set.univ : Set X)
  · have hξ' : IsGenericPoint ξ (Set.univ : Set X) := hrange ▸ hξ
    exact ⟨SheafOfModules.unit X.ringCatSheaf,
      Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit,
      (supp_unit_eq_univ X).trans hrange.symm,
      stalkKilledByMaximalIdeal_unit ξ hξ',
      length_stalk_unit_eq_one ξ hξ', hunit⟩
  · have hz : IsGenericPoint (i (genericPoint Z)) (Set.range i.base) := by
      have h := (genericPoint_spec Z).image i.continuous
      rwa [Set.image_univ, hclosed.closure_eq] at h
    obtain rfl : ξ = i (genericPoint Z) := hξ.eq hz
    have hsupp : SheafOfModules.supp
        ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)) =
        Set.range i.base := Stacks.Chow.supp_pushforwardStructureSheaf i
    exact ⟨(Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z), inferInstance, hsupp,
      stalkKilledByMaximalIdeal_pushforward_unit i (genericPoint Z) (genericPoint_spec Z),
      length_stalk_pushforward_unit_eq_one i (genericPoint Z) (genericPoint_spec Z),
      hproper _ (Set.range i.base) hclosed hrange hsupp.le⟩

end Stacks.AlgebraicGeometry.CoherentDevissage

end

end
