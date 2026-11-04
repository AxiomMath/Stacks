module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction
public import StacksFrontier.AlgebraicGeometry.Cohomology.TruncationTowerAnyModel
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.PushforwardBoundedCohomologicalDimension
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.ChaoticComparisonBaseChangeAcyclic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.QuasiCoherentCohomologyUnderFlatRestrictions
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.Exactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.EventuallyConstantCohomology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived objects with cartesian cohomology sheaves

Let `C` carry a Grothendieck topology `τ`, let `τ'` be the chaotic topology and let `O` be a
`τ`-sheaf of rings with commutative sections, with comparison morphism
`ε : (C_τ, O_τ) ⟶ (C_τ', O_τ')`, so that `ε_*` reads a `τ`-sheaf of modules as a presheaf of
modules and `ε^*` is `τ`-sheafification.  A presheaf of `O`-modules `P` is *cartesian* when every
restriction map `P(V) ⟶ P(U)` is a base change, `P(V) ⊗_{O(V)} O(U) ≅ P(U)`.  The subcategory of
`D(C_τ, O_τ)` appearing in Stacks 0GZS consists of the objects `K` with `Rε_*K` in `QC(O)`.

Assume that

* every restriction homomorphism `O(V) ⟶ O(U)` is flat,
* every cartesian presheaf of `O`-modules is a `τ`-sheaf, and
* every sheaf of `O`-modules whose underlying presheaf is cartesian has vanishing higher
  cohomology over every object of `C`.

Then `Rε_*K` lies in `QC(O)` exactly when every cohomology sheaf of `K` is cartesian.  These are
the hypotheses under which the subcategory of 0GZS is the derived category of cartesian modules
in the applications, Stacks 0H0J and 0H0K, where all three are theorems.

## Main definitions

* `Stacks.ModulesOnACategory.ChaoticComparison.IsCartesianPresheaf`: the cartesian condition on a
  presheaf of modules, in the form of a universal property of the restriction maps.
* `Stacks.ModulesOnACategory.ChaoticComparison.cartesianSheaves`: the sheaves of modules whose
  underlying presheaf is cartesian.

## Main results

* `Stacks.ModulesOnACategory.ChaoticComparison.isCartesianPresheaf_iff_isIso_restrictionBaseChange`
  — for a presheaf of commutative rings, the cartesian condition is the invertibility of the
  base-change comparisons `Stacks.PresheafOfModules.restrictionBaseChange`.
* `Stacks.ModulesOnACategory.ChaoticComparison.isQC_iff_forall_isCartesianPresheaf_homology`:
  Stacks 0GZR read on presheaves of modules — under flat restrictions, `QC(O)` consists of the
  objects with cartesian cohomology presheaves.
* `Stacks.ModulesOnACategory.ChaoticComparison.isLE_derivedEpsilonPushforward_obj` and
  `nonempty_iso_homology_derivedEpsilonPushforward_obj`: `Rε_*` has cohomological dimension zero
  on objects with cartesian cohomology sheaves, `Hʲ(Rε_*K) ≅ ε_*Hʲ(K)`.
* `isCartesianPushforward_iff_isCartesianPresheaf_homology`, in the same namespace: the
  characterization above, with its two directions
  `isCartesianPresheaf_homology_of_isCartesianPushforward` and
  `isCartesianPushforward_of_isCartesianPresheaf_homology`.
* `isZero_rightDerived_evaluation_of_isCartesianPresheaf`, in the same namespace: the
  acyclicity hypothesis follows from the slice condition used for Stacks 0H0J — every
  `N ⊗_{O(U)} O_U` on `C/U` a sheaf with vanishing higher cohomology — since the restriction to
  `C/U` of a cartesian sheaf is such a base change, and its cohomology over `id_U` is the
  cohomology over `U`.
* `Stacks.TerminalBaseChange.isIso_baseChangeAdj_counit_app`: on a category with a terminal
  object `X`, a cartesian presheaf of modules `P` is the base change `O ⊗_{O(X)} P(X)`.

## Implementation notes

The direction from `QC(O)` needs only flatness and the sheaf property: by Stacks 0GZR the
cohomology presheaves of `Rε_*K` are cartesian, hence sheaves, and `ε^*` — exact, with
`ε^* ∘ Rε_* = id` — identifies them with the cohomology sheaves of `K`.

The converse is a computation of `Rε_*` on an unbounded object, and the acyclicity assumption is
used twice.  Placed in a single degree, a cartesian sheaf `F` has `Rε_*F = ε_*F`, the higher
direct images being computed sectionwise by the cohomology over the objects of `C`.  So `Rε_*` of
a bounded object with cartesian cohomology is computed by a finite induction on its length.  An
unbounded `K` is the derived limit of its truncations `τ_{≥ -n}K`: this is Stacks 0D6M, whose
cohomological bound is `0` here, the second use of the acyclicity, in the form
`Stacks.TruncationTower.isIso_to_isDerivedLimit_truncGETower`, which is stated at an arbitrary
model of the derived category — the one `Rε_*` is defined on is not the standard one.  `Rε_*`,
a triangulated right adjoint, carries that derived limit to a derived limit of the
`Rε_*(τ_{≥ -n}K)`, whose cohomology towers are eventually constant, and countable products of
presheaves of modules are exact, so the cohomology of the limit is that of one stage.

The cartesian condition is stated as a universal property of the restriction maps, which needs
neither a choice of extension of scalars nor commutativity of the section rings; for a presheaf
of commutative rings it is the invertibility of the comparisons
`Stacks.PresheafOfModules.restrictionBaseChange`.  The commutativity of the section rings is the
class `Stacks.TerminalBaseChange.CommSections`, which supplies the commutative ring structures in
which flatness of the restriction homomorphisms is stated, and the base-change datum on `O` is
arbitrary, the condition `QC(O)` not depending on it.

## References

* [Stacks Project, Tag 0GZS](https://stacks.math.columbia.edu/tag/0GZS)
* [Stacks Project, Tag 0GZR](https://stacks.math.columbia.edu/tag/0GZR)
* [Stacks Project, Tag 0D6M](https://stacks.math.columbia.edu/tag/0D6M)
* [Stacks Project, Tag 0H0J](https://stacks.math.columbia.edu/tag/0H0J)
* [Stacks Project, Tag 0H0K](https://stacks.math.columbia.edu/tag/0H0K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite ZeroObject
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence

universe w m u v r t

namespace Stacks.ModulesOnACategory.ChaoticComparison

/-! ### Cartesian presheaves of modules -/

section Cartesian

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ RingCat.{r}}

/-- A presheaf of `O`-modules `P` is *cartesian* when for every arrow `a : V ⟶ U` of `Cᵒᵖ` the
restriction map `P(V) ⟶ P(U)` is a universal arrow for restriction of scalars along
`O(V) ⟶ O(U)`; equivalently, its adjoint transpose `P(V) ⊗_{O(V)} O(U) ⟶ P(U)` is bijective. -/
def IsCartesianPresheaf (P : PresheafOfModules.{m} O) : Prop :=
  ∀ ⦃U V : Cᵒᵖ⦄ (a : V ⟶ U),
    (ModuleCat.restrictScalars.{m} (O.map a).hom).IsUniversalArrow (P.map a)

/-- Being cartesian is invariant under isomorphism of presheaves of modules. -/
theorem IsCartesianPresheaf.of_iso {P Q : PresheafOfModules.{m} O} (e : P ≅ Q)
    (h : IsCartesianPresheaf P) : IsCartesianPresheaf Q := fun _ _ a =>
  (h a).of_iso ((PresheafOfModules.evaluation O _).mapIso e)
    ((PresheafOfModules.evaluation O _).mapIso e) (e.hom.naturality a)

/-- A zero presheaf of modules is cartesian. -/
theorem isCartesianPresheaf_of_isZero {P : PresheafOfModules.{m} O} (h : IsZero P) :
    IsCartesianPresheaf P := by
  intro U V a Z
  have hU : IsZero (P.obj U) := (PresheafOfModules.evaluation O U).map_isZero h
  have hV : IsZero (P.obj V) := (PresheafOfModules.evaluation O V).map_isZero h
  exact ⟨fun f₁ f₂ _ => hU.eq_of_src f₁ f₂, fun y => ⟨0, hV.eq_of_src _ _⟩⟩

/-- For a presheaf of commutative rings, a presheaf of modules is cartesian exactly when every
base-change comparison `restrictionBaseChange` of its restriction maps is an isomorphism. -/
theorem isCartesianPresheaf_iff_isIso_restrictionBaseChange {R : Cᵒᵖ ⥤ CommRingCat.{r}}
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat)) :
    IsCartesianPresheaf M ↔ ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y),
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange M f) :=
  ⟨fun h _X _Y f => (Functor.isUniversalArrow_iff_isIso
      (ModuleCat.extendRestrictScalarsAdj (R.map f).hom) (M.map f)).1 (h f),
    fun h _U _V a => (Functor.isUniversalArrow_iff_isIso
      (ModuleCat.extendRestrictScalarsAdj (R.map a).hom) (M.map a)).2 (h a)⟩

end Cartesian

/-! ### Quasi-coherent cohomology under flat restrictions -/

section Flat

open Stacks.TerminalBaseChange (CommSections commPresheaf)

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ RingCat.{r}) [CommSections O]

/-- **Stacks 0GZR, for presheaves of modules.** If all restriction homomorphisms of `O` are
flat, an object of `D(O)` lies in `QC(O)` exactly when all of its cohomology presheaves are
cartesian. -/
theorem isQC_iff_forall_isCartesianPresheaf_homology
    (hflat : ∀ ⦃U V : Cᵒᵖ⦄ (a : V ⟶ U), RingHom.Flat (O.map a).hom)
    (bc : BaseChangeData.{w} O) (K : DMod.{w} O) :
    IsQC.{w} bc K ↔ ∀ n : ℤ, IsCartesianPresheaf
      ((DerivedCategory.homologyFunctor (PresheafOfModules.{max u v r w} O) n).obj K) := by
  let X : AlgebraicGeometry.RingedSite.{u, v, r} :=
    ⟨C, ⊥, ⟨commPresheaf O, Presheaf.isSheaf_bot _⟩⟩
  refine (QuasiCoherentCohomology.isQC_iff_hasQuasicoherentCohomology.{w} X rfl
    (fun a => hflat a) bc K).trans ?_
  refine forall_congr' fun n => ⟨?_, fun h => ⟨Presheaf.isSheaf_bot _, ?_⟩⟩
  · rintro ⟨_, hQC⟩
    exact fun _ _ a => (isQuasicoherentOnSite_iff_isUniversalArrow.{u, v, r, w} rfl _).1 hQC a
  · exact (isQuasicoherentOnSite_iff_isUniversalArrow.{u, v, r, w} rfl _).2 fun {_ _} a => h a

end Flat


/-! ### The derived pushforward on objects with cartesian cohomology -/

section Derived

attribute [local instance] Stacks.SheafOfModulesEvaluation.evaluation_additive

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})
  [HasSheafify J AddCommGrpCat.{max u v r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]

/-- The class of sheaves of `O`-modules whose underlying presheaf of modules is cartesian. -/
abbrev cartesianSheaves : ObjectProperty (SheafOfModules.{max u v r w} R) :=
  fun F => IsCartesianPresheaf F.val

/-- Being cartesian is invariant under isomorphism of sheaves of modules. -/
instance cartesianSheaves_isClosedUnderIsomorphisms :
    (cartesianSheaves.{w} R).IsClosedUnderIsomorphisms :=
  ⟨fun e h => h.of_iso ((SheafOfModules.forget R).mapIso e)⟩

/-- A zero sheaf of modules is cartesian. -/
instance cartesianSheaves_containsZero : (cartesianSheaves.{w} R).ContainsZero :=
  ⟨⟨_, isZero_zero (SheafOfModules.{max u v r w} R),
    isCartesianPresheaf_of_isZero ((SheafOfModules.forget R).map_isZero (isZero_zero _))⟩⟩

/-- The shift-compatibility of `Rε_*`, the canonical one of a right derived functor. -/
@[instance_reducible]
def derivedEpsilonPushforwardCommShift : (derivedEpsilonPushforward.{w} R).CommShift ℤ :=
  Functor.IsRightDerivedFunctor.commShift (derivedEpsilonPushforward.{w} R)
    (derivedEpsilonPushforwardUnit.{w} R)
    (HomotopyCategory.quasiIso (SheafOfModules.{max u v r w} R) (ComplexShape.up ℤ)) ℤ

attribute [local instance] derivedEpsilonPushforwardCommShift

/-- `Rε_*` is a triangulated functor. -/
theorem derivedEpsilonPushforward_isTriangulated :
    (derivedEpsilonPushforward.{w} R).IsTriangulated :=
  Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor
    (exists_quasiIso_isKInjective.{w} R) _ (derivedEpsilonPushforward.{w} R)
    (derivedEpsilonPushforwardUnit.{w} R)

/-- `Rε_*` is left t-exact: it carries `D^{≥ n}` into `D^{≥ n}`. -/
theorem isGE_derivedEpsilonPushforward_obj (L : DerivedCategory (SheafOfModules.{max u v r w} R))
    (n : ℤ) [L.IsGE n] : ((derivedEpsilonPushforward.{w} R).obj L).IsGE n :=
  Stacks.DerivedFunctor.isGE_totalRightDerived_obj (epsilonPushforward.{w} R) L n

/-- The sections over `V` of `Rᵖε_*F` vanish exactly when the cohomology of `F` over `V` does. -/
private theorem isZero_evaluation_rightDerived_epsilonPushforward_iff
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D} (S : Sheaf K RingCat.{r})
    (F : SheafOfModules.{max u v r w} S) (V : Dᵒᵖ) (p : ℕ) :
    IsZero ((PresheafOfModules.evaluation S.obj V).obj
      (((epsilonPushforward.{w} S).rightDerived p).obj F)) ↔
    IsZero (((SheafOfModules.evaluation S V).rightDerived p).obj F) := by
  obtain ⟨e⟩ := Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology
    (epsilonPushforward.{w} S) (PresheafOfModules.evaluation S.obj V) p F
  exact ⟨fun h => h.of_iso e.symm, fun h => h.of_iso e⟩

omit [HasSheafify J AddCommGrpCat.{max u v r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r w}] in
/-- The higher right derived functors of `ε_*` vanish at a sheaf of modules whose cohomology over
every object vanishes in positive degrees: they are computed sectionwise. -/
theorem isZero_rightDerived_epsilonPushforward_obj (F : SheafOfModules.{max u v r w} R)
    (hF : ∀ (V : C) (p : ℕ), 0 < p →
      IsZero (((SheafOfModules.evaluation R (op V)).rightDerived p).obj F))
    (p : ℕ) (hp : 0 < p) : IsZero (((epsilonPushforward.{w} R).rightDerived p).obj F) := by
  rw [IsZero.iff_id_eq_zero]
  apply PresheafOfModules.hom_ext
  intro V
  exact ((isZero_evaluation_rightDerived_epsilonPushforward_iff.{w} R F V p).2
    (hF V.unop p hp)).eq_of_src _ _

/-- `Rε_*` of a sheaf of modules placed in degree `n`, whose cohomology over every object
vanishes in positive degrees, lives in degrees `≤ n`. -/
theorem isLE_derivedEpsilonPushforward_singleFunctor_obj (F : SheafOfModules.{max u v r w} R)
    (hF : ∀ (V : C) (p : ℕ), 0 < p →
      IsZero (((SheafOfModules.evaluation R (op V)).rightDerived p).obj F)) (n : ℤ) :
    ((derivedEpsilonPushforward.{w} R).obj
      ((DerivedCategory.singleFunctor (SheafOfModules.{max u v r w} R) n).obj F)).IsLE n := by
  have h0 : ((derivedEpsilonPushforward.{w} R).obj
      ((DerivedCategory.singleFunctor (SheafOfModules.{max u v r w} R) 0).obj F)).IsLE 0 := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact Stacks.DerivedFunctor.isZero_homologyTotalRightDerived_single_of_rightDerived_isZero
      (epsilonPushforward.{w} R) (derivedEpsilonPushforward.{w} R)
      (derivedEpsilonPushforwardUnit.{w} R) (exists_quasiIso_isKInjective.{w} R) F
      (isZero_rightDerived_epsilonPushforward_obj.{w} R F hF) 0 i hi
  simpa using Stacks.Cohomology.OlssonLaszlo.isLE_map_singleFunctor_obj_of_isLE_zero
    (derivedEpsilonPushforward.{w} R) F 0 h0 n

/-- **`Rε_*` keeps the upper bound of an object with cartesian cohomology.** Suppose every sheaf
of modules with cartesian underlying presheaf has vanishing higher cohomology over every object.
If `L` lives in degrees `≤ b` and all its cohomology sheaves are cartesian, then `Rε_*L` lives in
degrees `≤ b`.

For bounded `L` this is a finite induction on the length, `Rε_*` of a cartesian sheaf placed in
degree `n` living in degree `n`. In general `L` is the derived limit of its truncations
`τ_{≥ -n}L` (Stacks 0D6M, whose cohomological bound is `0` here), `Rε_*` carries that derived
limit to a derived limit of the bounded objects `Rε_*(τ_{≥ -n}L)`, and the cohomology towers of
the latter are eventually constant, so the cohomology of the limit is computed by one stage. -/
theorem isLE_derivedEpsilonPushforward_obj
    (hacyc : ∀ F : SheafOfModules.{max u v r w} R, IsCartesianPresheaf F.val →
      ∀ (U : C) (p : ℕ), 0 < p →
        IsZero (((SheafOfModules.evaluation R (op U)).rightDerived p).obj F))
    (L : DerivedCategory (SheafOfModules.{max u v r w} R))
    (hL : ∀ q : ℤ, IsCartesianPresheaf
      ((DerivedCategory.homologyFunctor (SheafOfModules.{max u v r w} R) q).obj L).val)
    (b : ℤ) [L.IsLE b] :
    ((derivedEpsilonPushforward.{w} R).obj L).IsLE b := by
  have := derivedEpsilonPushforward_isTriangulated.{w} R
  have : (derivedEpsilonPushforward.{w} R).IsRightAdjoint :=
    (derivedEpsilonAdjunction.{w} R).isRightAdjoint
  let S := SheafOfModules.{max u v r w} R
  let G := derivedEpsilonPushforward.{w} R
  let t := DerivedCategory.TStructure.t (C := S)
  have hsingle : ∀ (M : S) (n : ℤ), cartesianSheaves.{w} R M →
      (G.obj ((DerivedCategory.singleFunctor S n).obj M)).IsLE (n + 0) := fun M n hM => by
    simpa using isLE_derivedEpsilonPushforward_singleFunctor_obj.{w} R M (hacyc M hM) n
  have hLB : DerivedCategoryB.derivedCategoryB (cartesianSheaves.{w} R) L := hL
  let tower := Stacks.DerivedLimit.truncGETower S L
  have htowerGE : ∀ n : ℕ, (tower.obj ⟨n⟩).IsGE (-(n : ℤ)) := fun n => by
    show ((t.truncGE _).obj L).IsGE _
    infer_instance
  -- every stage of the pushed-forward tower lives in degrees `≤ b`
  have hstage : ∀ n : ℕ, (G.obj (tower.obj ⟨n⟩)).IsLE b := by
    intro n
    let a := min (-(n : ℤ)) b
    have := htowerGE n
    have hGE : (tower.obj ⟨n⟩).IsGE a := t.isGE_of_ge _ a (-(n : ℤ)) (min_le_left _ _)
    have hLE : (tower.obj ⟨n⟩).IsLE b := by
      show ((t.truncGE _).obj L).IsLE b
      infer_instance
    simpa using Stacks.Cohomology.OlssonLaszlo.isLE_map_obj_of_bounded G
      (cartesianSheaves.{w} R) 0 hsingle (b - a).toNat (tower.obj ⟨n⟩)
      (Stacks.Cohomology.OlssonLaszlo.derivedCategoryB_truncGE_mem _ L hLB _) a b hGE hLE
      (by omega)
  -- `L` is the derived limit of its truncation tower
  have : HasLimitsOfShape (Discrete ℕ) S :=
    SheafOfModules.hasLimitsOfShape.{max u v r w} (R := R) (Discrete ℕ)
  obtain ⟨hprod, L', p, δ, hT⟩ := DerivedCategory.exists_isDerivedLimit_of_forall_isGE tower
    (fun n ↦ ⟨-(n : ℤ), htowerGE n⟩)
  let := hprod
  let diff := Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ tower.obj ⟨n⟩) n -
    Pi.π (fun n : ℕ ↦ tower.obj ⟨n⟩) (n + 1) ≫ tower.map (homOfLE (Nat.le_succ n)).op
  let T := Triangle.mk p diff δ
  let qmap : L ⟶ ∏ᶜ fun n : ℕ ↦ tower.obj ⟨n⟩ :=
    Pi.lift (fun n ↦ (t.truncGEπ (-(n : ℤ))).app L)
  have hq (n : ℕ) : qmap ≫ Pi.π (fun n : ℕ ↦ tower.obj ⟨n⟩) n =
      (t.truncGEπ (-(n : ℤ))).app L := Pi.lift_π _ n
  have hzero : qmap ≫ T.mor₂ = 0 := by
    show qmap ≫ diff = 0
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, Pi.lift_π, Preadditive.comp_sub, hq n, ← Category.assoc, hq (n + 1),
      Stacks.DerivedLimit.truncGETower_map_homOfLE_succ, zero_comp]
    exact sub_eq_zero_of_eq (t.π_natTransTruncGEOfLE_app _ _ (by omega) L).symm
  obtain ⟨c, hc⟩ := T.coyoneda_exact₂ hT qmap hzero
  have hcn : ∀ n : ℕ, c ≫ p ≫ Pi.π (fun n : ℕ ↦ tower.obj ⟨n⟩) n =
      (t.truncGEπ (-(n : ℤ))).app L := fun n => by
    rw [← Category.assoc]
    exact (congrArg (· ≫ Pi.π (fun n : ℕ ↦ tower.obj ⟨n⟩) n) hc).symm.trans (hq n)
  have : IsIso c := Stacks.TruncationTower.isIso_to_isDerivedLimit_truncGETower R L Set.univ
    (fun U => ⟨PreZeroHypercover.singleton (𝟙 U), by
      rw [(Sieve.id_mem_iff_eq_top).1 ((PreZeroHypercover.singleton (𝟙 U)).sieve₀_f ⟨⟩)]
      exact J.top_mem U, fun _ => trivial⟩)
    (fun _ _ _ => 0) (fun V _ => {𝒰 | 𝒰.sieve₀ ∈ J V}) (fun _ _ _ h => h)
    (fun _ _ 𝒰 h => ⟨𝒰, h, ⟨PreZeroHypercover.Hom.id 𝒰⟩⟩)
    (fun _ _ 𝒰 _ i p m hm => hacyc _ (hL _) (𝒰.X i) p (by exact_mod_cast hm))
    L' c p δ hT hcn
  -- `Rε_*` carries it to a derived limit of the pushed-forward tower
  obtain ⟨hprod', p', δ', htri', -⟩ :=
    Stacks.Cohomology.OlssonLaszlo.exists_presented_derivedLimit_map G tower L' p δ hT c
      (fun k ↦ (t.truncGEπ (-(k : ℤ))).app L) hcn
  let := hprod'
  let towerR := tower ⋙ G
  let H := fun i : ℤ => DerivedCategory.homologyFunctor (PresheafOfModules.{max u v r w} R.obj) i
  let idx : ℤ → ℕ := fun i ↦ Int.toNat (-i)
  let heventual : ∀ i : ℤ, Stacks.InverseSystem.EventuallyConstantValue (towerR ⋙ H i)
      ((H i).obj (towerR.obj ⟨idx i⟩)) := fun i =>
    ⟨idx i, Stacks.Cohomology.OlssonLaszlo.isEventuallyConstantTo_of_isIso_succ _ _
      (fun k hk => Stacks.Cohomology.OlssonLaszlo.isIso_homologyMap_map_truncGETower_succ G
        (cartesianSheaves.{w} R) 0 hsingle L hLB k i
          (by have := Int.self_le_toNat (-i); dsimp only [idx] at hk; omega)), Iso.refl _⟩
  have : HasExactLimitsOfShape (Discrete ℕ) (PresheafOfModules.{max u v r w} R.obj) :=
    Stacks.TruncationTower.presheafModules_hasExactCountableProducts _
  rw [DerivedCategory.isLE_iff]
  intro i hi
  have hiso := Stacks.InverseSystem.isIso_homologyMap_proj_of_eventuallyConstant towerR
    (G.obj L') p' δ' htri' i _ (heventual (i - 1)) _ (heventual i)
  have hz : IsZero ((H i).obj (towerR.obj ⟨idx i⟩)) := by
    have : (towerR.obj ⟨idx i⟩).IsLE b := hstage (idx i)
    exact DerivedCategory.isZero_of_isLE _ b i hi
  exact (hz.of_iso (@asIso _ _ _ _ _ hiso)).of_iso ((H i).mapIso (G.mapIso (asIso c)))

/-- If all cohomology objects of `X` are cartesian, so are those of a truncation `τ_{< n}X`. -/
private theorem derivedCategoryB_truncLT_obj (X : DerivedCategory (SheafOfModules.{max u v r w} R))
    (hX : DerivedCategoryB.derivedCategoryB (cartesianSheaves.{w} R) X) (n : ℤ) :
    DerivedCategoryB.derivedCategoryB (cartesianSheaves.{w} R)
      ((DerivedCategory.TStructure.t.truncLT n).obj X) := by
  intro i
  by_cases hi : i < n
  · have := DerivedCategory.isIso_homologyMap_truncLTι_app n i hi X
    exact (cartesianSheaves.{w} R).prop_of_iso
      (asIso ((DerivedCategory.homologyFunctor _ i).map
        ((DerivedCategory.TStructure.t.truncLTι n).app X))).symm (hX i)
  · exact (cartesianSheaves.{w} R).prop_of_isZero
      (DerivedCategory.isZero_of_isLE _ (n - 1) i (by omega))

/-- **The cohomology of `Rε_*K` for `K` with cartesian cohomology.** Suppose every sheaf of
modules with cartesian underlying presheaf has vanishing higher cohomology over every object.
If all cohomology sheaves of `K` are cartesian, then `Hʲ(Rε_*K) ≅ ε_*(Hʲ(K))` for every `j`:
`Rε_*` has cohomological dimension zero on such objects.

The truncation triangle `τ_{< j+1}K ⟶ K ⟶ τ_{≥ j+1}K` and left t-exactness of `Rε_*` reduce to
`K' = τ_{< j+1}K`; the triangle `τ_{< j}K' ⟶ K' ⟶ Hʲ(K)[-j]` and the bound of
`isLE_derivedEpsilonPushforward_obj` on `τ_{< j}K'` reduce to `Hʲ(K)[-j]`, whose image under
`Rε_*` has `ε_*Hʲ(K)` in degree `j`. -/
theorem nonempty_iso_homology_derivedEpsilonPushforward_obj
    (hacyc : ∀ F : SheafOfModules.{max u v r w} R, IsCartesianPresheaf F.val →
      ∀ (U : C) (p : ℕ), 0 < p →
        IsZero (((SheafOfModules.evaluation R (op U)).rightDerived p).obj F))
    (K : DerivedCategory (SheafOfModules.{max u v r w} R))
    (hK : ∀ q : ℤ, IsCartesianPresheaf
      ((DerivedCategory.homologyFunctor (SheafOfModules.{max u v r w} R) q).obj K).val)
    (j : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor (PresheafOfModules.{max u v r w} R.obj) j).obj
        ((derivedEpsilonPushforward.{w} R).obj K) ≅
      (epsilonPushforward.{w} R).obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{max u v r w} R) j).obj K)) := by
  have := derivedEpsilonPushforward_isTriangulated.{w} R
  let S := SheafOfModules.{max u v r w} R
  let G := derivedEpsilonPushforward.{w} R
  let t := DerivedCategory.TStructure.t (C := S)
  let HS := fun i : ℤ => DerivedCategory.homologyFunctor S i
  let HP := fun i : ℤ => DerivedCategory.homologyFunctor (PresheafOfModules.{max u v r w} R.obj) i
  have hKB : DerivedCategoryB.derivedCategoryB (cartesianSheaves.{w} R) K := hK
  -- the first truncation triangle
  let T₁ := (t.triangleLTGE (j + 1)).obj K
  have hT₁ : G.mapTriangle.obj T₁ ∈ distTriang _ :=
    G.map_distinguished _ (t.triangleLTGE_distinguished (j + 1) K)
  have : (G.obj T₁.obj₃).IsGE (j + 1) := isGE_derivedEpsilonPushforward_obj.{w} R _ _
  have e₁ : IsIso ((HP j).map (G.map T₁.mor₁)) := by
    have hepi : Epi ((HP j).map (G.map T₁.mor₁)) :=
      (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff _ hT₁ j).2
        ((DerivedCategory.isZero_of_isGE (G.obj T₁.obj₃) (j + 1) j (by omega)).eq_of_tgt _ _)
    have hmono : Mono ((HP j).map (G.map T₁.mor₁)) :=
      (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff _ hT₁ (j - 1) j
        (by omega)).2
        ((DerivedCategory.isZero_of_isGE (G.obj T₁.obj₃) (j + 1) (j - 1) (by omega)).eq_of_src
          _ _)
    exact isIso_of_mono_of_epi _
  -- the second truncation triangle, on `K' = τ_{< j+1}K`
  let K' := T₁.obj₁
  have hK'B : DerivedCategoryB.derivedCategoryB (cartesianSheaves.{w} R) K' :=
    derivedCategoryB_truncLT_obj.{w} R K hKB (j + 1)
  have : K'.IsLE j := by
    show ((t.truncLT (j + 1)).obj K).IsLE j
    infer_instance
  let T₂ := (t.triangleLTGE j).obj K'
  have hT₂ : G.mapTriangle.obj T₂ ∈ distTriang _ :=
    G.map_distinguished _ (t.triangleLTGE_distinguished j K')
  have : T₂.obj₁.IsLE (j - 1) := by
    show ((t.truncLT j).obj K').IsLE (j - 1)
    infer_instance
  have : (G.obj T₂.obj₁).IsLE (j - 1) :=
    isLE_derivedEpsilonPushforward_obj.{w} R hacyc T₂.obj₁
      (derivedCategoryB_truncLT_obj.{w} R K' hK'B j) (j - 1)
  have e₂ : IsIso ((HP j).map (G.map T₂.mor₂)) := by
    have hmono : Mono ((HP j).map (G.map T₂.mor₂)) :=
      (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff _ hT₂ j).2
        ((DerivedCategory.isZero_of_isLE (G.obj T₂.obj₁) (j - 1) j (by omega)).eq_of_src _ _)
    have hepi : Epi ((HP j).map (G.map T₂.mor₂)) :=
      (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff _ hT₂ j (j + 1)
        (by omega)).2
        ((DerivedCategory.isZero_of_isLE (G.obj T₂.obj₁) (j - 1) (j + 1) (by omega)).eq_of_tgt
          _ _)
    exact isIso_of_mono_of_epi _
  -- `τ_{≥ j}K'` is a single object in degree `j`
  have : T₂.obj₃.IsGE j := by
    show ((t.truncGE j).obj K').IsGE j
    infer_instance
  have : T₂.obj₃.IsLE j := by
    show ((t.truncGE j).obj K').IsLE j
    infer_instance
  obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE T₂.obj₃ j
  have i₁ : IsIso ((HS j).map T₂.mor₂) :=
    DerivedCategory.isIso_homologyMap_truncGEπ_app j j le_rfl K'
  have i₂ : IsIso ((HS j).map T₁.mor₁) :=
    DerivedCategory.isIso_homologyMap_truncLTι_app (j + 1) j (by omega) K
  let eM : M ≅ (HS j).obj K :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso S j).app M).symm ≪≫
      (HS j).mapIso e.symm ≪≫ (@asIso _ _ _ _ _ i₁).symm ≪≫ @asIso _ _ _ _ _ i₂
  have : PreservesFiniteLimits (epsilonPushforward.{w} R) := by
    have : PreservesLimitsOfSize.{0, 0} (epsilonPushforward.{w} R) :=
      (epsilonAdjunction.{w} R).rightAdjoint_preservesLimits
    exact PreservesLimitsOfSize.preservesFiniteLimits _
  exact ⟨(@asIso _ _ _ _ _ e₁).symm ≪≫ @asIso _ _ _ _ _ e₂ ≪≫
    (HP j).mapIso (G.mapIso e) ≪≫
    Stacks.DerivedFunctor.homologyTotalRightDerivedSingleSelfIso (epsilonPushforward.{w} R) G
      (derivedEpsilonPushforwardUnit.{w} R) (exists_quasiIso_isKInjective.{w} R) M j ≪≫
    (epsilonPushforward.{w} R).mapIso eM⟩

end Derived

/-! ### Objects with cartesian cohomology -/

section Main

open Stacks.TerminalBaseChange (CommSections commPresheaf)

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})
  [HasSheafify J AddCommGrpCat.{max u v r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r w}] [CommSections R.obj]
  (hflat : ∀ ⦃U V : Cᵒᵖ⦄ (a : V ⟶ U), RingHom.Flat (R.obj.map a).hom)
  (bc : BaseChangeData.{w} R.obj)

include hflat in
/-- **Objects of the subcategory of Stacks 0GZS have cartesian cohomology sheaves.** Suppose the
restriction homomorphisms of `O` are flat and every cartesian presheaf of `O`-modules is a
`τ`-sheaf. If `Rε_*K` lies in `QC(O)`, then every cohomology sheaf of `K` is cartesian.

By Stacks 0GZR the cohomology presheaves `Hⁿ(Rε_*K)` are cartesian, hence sheaves; and
`Hⁿ(K) = Hⁿ(ε^*Rε_*K) = ε^*Hⁿ(Rε_*K)`, `ε^*` being exact with `ε^* ∘ Rε_* = id`, so `Hⁿ(K)` is
the sheaf `Hⁿ(Rε_*K)` itself. -/
theorem isCartesianPresheaf_homology_of_isCartesianPushforward
    (hsheaf : ∀ P : PresheafOfModules.{max u v r w} R.obj, IsCartesianPresheaf P →
      Presheaf.IsSheaf J P.presheaf)
    (K : DerivedCategory (SheafOfModules.{max u v r w} R))
    (hK : IsCartesianPushforward.{w} R bc K) (n : ℤ) :
    IsCartesianPresheaf
      ((DerivedCategory.homologyFunctor (SheafOfModules.{max u v r w} R) n).obj K).val := by
  have hX := (isQC_iff_forall_isCartesianPresheaf_homology.{w} R.obj hflat bc _).1 hK n
  let X := (DerivedCategory.homologyFunctor (PresheafOfModules.{max u v r w} R.obj) n).obj
    ((derivedEpsilonPushforward.{w} R).obj K)
  have : IsIso ((epsilonAdjunction.{w} R).unit.app X) :=
    ((epsilonAdjunction.{w} R).isIso_unit_app_iff_mem_essImage).2
      ⟨⟨X, hsheaf X hX⟩, ⟨Iso.refl _⟩⟩
  let e : (epsilonPullback.{w} R).obj X ≅
      (DerivedCategory.homologyFunctor (SheafOfModules.{max u v r w} R) n).obj K :=
    (((epsilonPullback.{w} R).mapDerivedCategoryHomologyIso n).app
        ((derivedEpsilonPushforward.{w} R).obj K)).symm ≪≫
      (DerivedCategory.homologyFunctor (SheafOfModules.{max u v r w} R) n).mapIso
        ((derivedPushforwardPullbackIso.{w} R).app K)
  exact hX.of_iso (asIso ((epsilonAdjunction.{w} R).unit.app X) ≪≫
    (epsilonPushforward.{w} R).mapIso e)

include hflat in
/-- **Objects with cartesian cohomology sheaves lie in the subcategory of Stacks 0GZS.** Suppose
the restriction homomorphisms of `O` are flat and every sheaf of modules with cartesian
underlying presheaf has vanishing higher cohomology over every object. If every cohomology
sheaf of `K` is cartesian, then `Rε_*K` lies in `QC(O)`.

`Rε_*` has cohomological dimension zero on such `K`
(`nonempty_iso_homology_derivedEpsilonPushforward_obj`), so `Hⁿ(Rε_*K) ≅ ε_*Hⁿ(K)` is cartesian,
and Stacks 0GZR concludes. -/
theorem isCartesianPushforward_of_isCartesianPresheaf_homology
    (hacyc : ∀ F : SheafOfModules.{max u v r w} R, IsCartesianPresheaf F.val →
      ∀ (U : C) (p : ℕ), 0 < p →
        IsZero (((SheafOfModules.evaluation R (op U)).rightDerived p).obj F))
    (K : DerivedCategory (SheafOfModules.{max u v r w} R))
    (hK : ∀ n : ℤ, IsCartesianPresheaf
      ((DerivedCategory.homologyFunctor (SheafOfModules.{max u v r w} R) n).obj K).val) :
    IsCartesianPushforward.{w} R bc K := by
  refine (isQC_iff_forall_isCartesianPresheaf_homology.{w} R.obj hflat bc _).2 fun n => ?_
  obtain ⟨e⟩ := nonempty_iso_homology_derivedEpsilonPushforward_obj.{w} R hacyc K hK n
  exact (hK n).of_iso e.symm

include hflat in
/-- **The subcategory of Stacks 0GZS is the subcategory of objects with cartesian cohomology.**
Let `O` be a `τ`-sheaf of rings with commutative sections and flat restriction homomorphisms,
such that every cartesian presheaf of `O`-modules is a `τ`-sheaf and every sheaf of modules with
cartesian underlying presheaf has vanishing higher cohomology over every object of `C`. Then for
`K` in `D(C_τ, O)`, the object `Rε_*K` lies in `QC(O)` exactly when every cohomology sheaf of `K`
is cartesian. -/
theorem isCartesianPushforward_iff_isCartesianPresheaf_homology
    (hsheaf : ∀ P : PresheafOfModules.{max u v r w} R.obj, IsCartesianPresheaf P →
      Presheaf.IsSheaf J P.presheaf)
    (hacyc : ∀ F : SheafOfModules.{max u v r w} R, IsCartesianPresheaf F.val →
      ∀ (U : C) (p : ℕ), 0 < p →
        IsZero (((SheafOfModules.evaluation R (op U)).rightDerived p).obj F))
    (K : DerivedCategory (SheafOfModules.{max u v r w} R)) :
    IsCartesianPushforward.{w} R bc K ↔ ∀ n : ℤ, IsCartesianPresheaf
      ((DerivedCategory.homologyFunctor (SheafOfModules.{max u v r w} R) n).obj K).val :=
  ⟨isCartesianPresheaf_homology_of_isCartesianPushforward.{w} R hflat bc hsheaf K,
    isCartesianPushforward_of_isCartesianPresheaf_homology.{w} R hflat bc hacyc K⟩

end Main

end Stacks.ModulesOnACategory.ChaoticComparison

/-! ### Cartesian presheaves of modules on a category with a terminal object -/

namespace Stacks.TerminalBaseChange

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ RingCat.{r}) [CommSections O]
  {X : C} (hX : IsTerminal X)

/-- The component over `V` of the counit of `baseChangeAdj` at `P`, with its source spelled as
the extension of scalars along `ρ_V`. -/
noncomputable abbrev baseChangeCounitApp (P : PresheafOfModules.{max t r} O) (V : Cᵒᵖ) :
    (ModuleCat.extendScalars.{r, r, max t r} (rho O hX V)).obj (P.obj (op X)) ⟶ P.obj V :=
  ((baseChangeAdj.{t} O hX).counit.app P).app V

/-- The adjoint transpose of the component over `V` of the counit of `baseChangeAdj` at `P`, under
extension and restriction of scalars along `ρ_V`, is the restriction map of `P` along the unique
arrow `op X ⟶ V`: the counit sends `1 ⊗ x` to the restriction of `x`. -/
theorem homEquiv_baseChangeCounitApp (P : PresheafOfModules.{max t r} O) (V : Cᵒᵖ) :
    (ModuleCat.extendRestrictScalarsAdj.{max t r, r, r} (rho O hX V)).homEquiv _ _
      (baseChangeCounitApp O hX P V) = P.map (iota hX V) := by
  ext x
  show (1 : O.obj V) • (show P.obj V from (P.map (iota hX V)).hom x) =
    (show P.obj V from (P.map (iota hX V)).hom x)
  exact one_smul _ _

/-- **A cartesian presheaf of modules on a category with a terminal object is the base change of
its global sections.** If every restriction map of `P` is a base change, the counit
`O ⊗_{O(X)} P(X) ⟶ P` of `baseChangeAdj` is an isomorphism, its component over `V` being the
base-change comparison of the restriction along `X ⟵ V`. -/
@[sga "7 VII 1.1.2.1" "partial"]
theorem isIso_baseChangeAdj_counit_app (P : PresheafOfModules.{max t r} O)
    (hP : Stacks.ModulesOnACategory.ChaoticComparison.IsCartesianPresheaf P) :
    IsIso ((baseChangeAdj.{t} O hX).counit.app P) := by
  refine Stacks.ModulesOnACategory.ChaoticComparison.isIso_of_forall_isIso_app _ fun V => ?_
  have h := (Functor.isUniversalArrow_iff_isIso
    (ModuleCat.extendRestrictScalarsAdj.{max t r, r, r} (rho O hX V)) (P.map (iota hX V))).1
      (hP (iota hX V))
  rwa [← homEquiv_baseChangeCounitApp, Equiv.symm_apply_apply] at h

end Stacks.TerminalBaseChange

namespace Stacks.ModulesOnACategory.ChaoticComparison

/-! ### Acyclicity of cartesian sheaves from the slice condition -/

section SliceAcyclicity

open Stacks.Sites.OverModules (overRingPresheaf)
open Stacks.ModulesOnACategory.MorphismsOverAnObject
open Stacks.TerminalBaseChange

attribute [local instance] Stacks.SheafOfModulesEvaluation.evaluation_additive

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})
  [HasSheafify J AddCommGrpCat.{max u v r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{max u v r w}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]
  (hO : ∀ (V : Cᵒᵖ) (x y : R.obj.obj V), x * y = y * x)

omit [HasSheafify J AddCommGrpCat.{max u v r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{max u v r w}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max u v r w}] in
/-- The restriction to `C/U` of a sheaf of modules with cartesian underlying presheaf again has
cartesian underlying presheaf. -/
theorem isCartesianPresheaf_sheafRestriction {F : SheafOfModules.{max u v r w} R}
    (hF : IsCartesianPresheaf F.val) (U : C) :
    IsCartesianPresheaf ((sheafRestriction.{w} R U).obj F).val :=
  fun _ _ b => hF ((Over.forget U).op.map b)

/-- **Vanishing of the higher cohomology over `U` read on `C/U`.** If the higher direct images
of `ε_{U*}` vanish at the restriction `F|_U`, then the higher cohomology of `F` over `U`
vanishes: by the Leray identification `(Rε_*F)|_U = Rε_{U*}(F|_U)`, the sections over `U` of
`Rᵖε_*F` are those over `id_U` of `Rᵖε_{U*}(F|_U)`. -/
theorem isZero_rightDerived_evaluation_of_sheafRestriction (F : SheafOfModules.{max u v r w} R)
    (U : C) (p : ℕ)
    (h : IsZero (((epsilonPushforward.{w} (overRingSheaf R U)).rightDerived p).obj
      ((sheafRestriction.{w} R U).obj F))) :
    IsZero (((SheafOfModules.evaluation R (op U)).rightDerived p).obj F) := by
  let S := SheafOfModules.{max u v r w} R
  let S' := SheafOfModules.{max u v r w} (overRingSheaf R U)
  let res := sheafRestriction.{w} R U
  let H := DerivedCategory.homologyFunctor (PresheafOfModules.{max u v r w} R.obj) p
  let H' := DerivedCategory.homologyFunctor
    (PresheafOfModules.{max u v r w} (overRingPresheaf R.obj U)) p
  -- `Hᵖ(Rε_{U*}((F|_U)[0])) = Rᵖε_{U*}(F|_U) = 0`
  have h₁ : IsZero (H'.obj ((derivedEpsilonPushforward.{w} (overRingSheaf R U)).obj
      ((DerivedCategory.singleFunctor S' 0).obj (res.obj F)))) :=
    h.of_iso (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso
      (epsilonPushforward.{w} (overRingSheaf R U)) _
      (derivedEpsilonPushforwardUnit.{w} (overRingSheaf R U))
      (exists_quasiIso_isKInjective.{w} (overRingSheaf R U)) (res.obj F) p)
  -- transport along the Leray identification
  have h₂ : IsZero (H'.obj ((derivedRestriction.{w} R.obj U).obj
      ((derivedEpsilonPushforward.{w} R).obj ((DerivedCategory.singleFunctor S 0).obj F)))) :=
    h₁.of_iso (H'.mapIso ((derivedRestrictionPushforwardIso.{w} R U).app _ ≪≫
      (derivedEpsilonPushforward.{w} (overRingSheaf R U)).mapIso
        ((res.mapDerivedCategorySingleFunctor 0).app F)))
  have h₃ : IsZero ((PresheafOfModules.pushforward₀.{max u v r w} (Over.forget U) R.obj).obj
      (H.obj ((derivedEpsilonPushforward.{w} R).obj
        ((DerivedCategory.singleFunctor S 0).obj F)))) :=
    h₂.of_iso ((((PresheafOfModules.pushforward₀.{max u v r w} (Over.forget U)
      R.obj).mapDerivedCategoryHomologyIso p).app _).symm)
  -- sections over `id_U`, that is over `U`
  have h₄ : IsZero ((H.obj ((derivedEpsilonPushforward.{w} R).obj
      ((DerivedCategory.singleFunctor S 0).obj F))).obj (op U)) :=
    (PresheafOfModules.evaluation _ (op (Over.mk (𝟙 U)))).map_isZero h₃
  have h₅ : IsZero ((PresheafOfModules.evaluation R.obj (op U)).obj
      (((epsilonPushforward.{w} R).rightDerived p).obj F)) :=
    h₄.of_iso ((PresheafOfModules.evaluation R.obj (op U)).mapIso
      (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso (epsilonPushforward.{w} R) _
        (derivedEpsilonPushforwardUnit.{w} R) (exists_quasiIso_isKInjective.{w} R) F p).symm)
  exact (isZero_evaluation_rightDerived_epsilonPushforward_iff.{w} R F (op U) p).1 h₅

/-- **Cartesian sheaves are acyclic, from the slice condition of Stacks 0H0J.** Suppose that for
every object `U` of `C` and every `O(U)`-module `N` the presheaf `N ⊗_{O(U)} O_U` on the
localized site `(C/U, τ)` is a `τ`-sheaf (`hsheaf`) whose cohomology over every object of `C/U`
vanishes in positive degrees (`hacyc`) — the inputs of `isLocallyKFlatAcyclic_of_baseChange`.
Then every sheaf of `O`-modules with cartesian underlying presheaf has vanishing higher
cohomology over every object of `C`.

The restriction `F|_U` of a cartesian `F` is cartesian on `C/U`, whose terminal object is `id_U`,
so it is the base change `F(U) ⊗_{O(U)} O_U` of its global sections
(`Stacks.TerminalBaseChange.isIso_baseChangeAdj_counit_app`); its higher direct images under
`ε_{U*}` therefore vanish, and `isZero_rightDerived_evaluation_of_sheafRestriction` reads that
over `U`. -/
theorem isZero_rightDerived_evaluation_of_isCartesianPresheaf
    (hsheaf : ∀ (U : C) (N : ModuleCat.{max u v r w}
        ((overRingPresheaf R.obj U).obj (op (Over.mk (𝟙 U))))),
      letI := Stacks.ModulesOnACategory.TerminalMorphismOfSites.commSections_of_comm
        (overRingPresheaf R.obj U) (comm_overRingPresheaf R.obj U hO)
      Presheaf.IsSheaf (J.over U) ((baseChangePresheaf.{max u v w} (overRingPresheaf R.obj U)
        (Over.mkIdTerminal (X := U))).obj N).presheaf)
    (hacyc : ∀ (U : C) (N : ModuleCat.{max u v r w}
        ((overRingPresheaf R.obj U).obj (op (Over.mk (𝟙 U))))) (V : Over U) (p : ℕ), 0 < p →
      letI := Stacks.ModulesOnACategory.TerminalMorphismOfSites.commSections_of_comm
        (overRingPresheaf R.obj U) (comm_overRingPresheaf R.obj U hO)
      IsZero (((SheafOfModules.evaluation (overRingSheaf R U) (op V)).rightDerived p).obj
        ⟨(baseChangePresheaf.{max u v w} (overRingPresheaf R.obj U)
          (Over.mkIdTerminal (X := U))).obj N, hsheaf U N⟩))
    (F : SheafOfModules.{max u v r w} R) (hF : IsCartesianPresheaf F.val) (U : C) (p : ℕ)
    (hp : 0 < p) :
    IsZero (((SheafOfModules.evaluation R (op U)).rightDerived p).obj F) := by
  let := Stacks.ModulesOnACategory.TerminalMorphismOfSites.commSections_of_comm
    (overRingPresheaf R.obj U) (comm_overRingPresheaf R.obj U hO)
  let FU := (sheafRestriction.{w} R U).obj F
  let N : ModuleCat.{max u v r w} ((overRingPresheaf R.obj U).obj (op (Over.mk (𝟙 U)))) :=
    FU.val.obj (op (Over.mk (𝟙 U)))
  have hc := isIso_baseChangeAdj_counit_app.{max u v, v, r, max u v w} (overRingPresheaf R.obj U)
    (Over.mkIdTerminal (X := U)) FU.val (isCartesianPresheaf_sheafRestriction.{w} R hF U)
  let e : (⟨(baseChangePresheaf.{max u v w} (overRingPresheaf R.obj U)
      (Over.mkIdTerminal (X := U))).obj N, hsheaf U N⟩ : SheafOfModules (overRingSheaf R U)) ≅
      FU :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (@asIso _ _ _ _ _ hc)
  refine isZero_rightDerived_evaluation_of_sheafRestriction.{w} R F U p
    (isZero_rightDerived_epsilonPushforward_obj.{w} (overRingSheaf R U) FU (fun V q hq => ?_) p hp)
  exact (hacyc U N V q hq).of_iso
    (((SheafOfModules.evaluation (overRingSheaf R U) (op V)).rightDerived q).mapIso e.symm)

end SliceAcyclicity

end Stacks.ModulesOnACategory.ChaoticComparison
