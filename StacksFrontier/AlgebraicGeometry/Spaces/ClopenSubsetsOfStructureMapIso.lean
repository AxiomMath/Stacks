module

public import StacksFrontier.AlgebraicGeometry.Scheme.ClopenIdempotent
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsRingHomChartFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperReducedGlobalFunctionsFiniteOverSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorizationFlatBaseChange

/-!
# Open and closed subsets of the source of a morphism with `f_* 𝒪_X = 𝒪_Y`

Let `f : X ⟶ Y` be a morphism of algebraic spaces whose structure map `𝒪_Y ⟶ f_* 𝒪_X`
(Stacks 03G8) is an isomorphism.  Then pullback of global functions `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)` is
bijective.  Every open and closed subset `C` of `|X|` is the support of an idempotent global
function of `X`; when `Y` is (the algebraic space of) a scheme `T` of the site, that function is
the pullback of a function `ε` of `T`, so `C` is the preimage of the basic open of `ε`.  In
particular two points of `X` with the same image in `T` are both in `C` or both outside it.

This is the step of the connectedness assertion of the Stein factorization (Stacks 0A1B,
clause (1)) at which `f_* 𝒪_X = 𝒪_Y` enters.

## Main results

* `AlgebraicGeometry.Space.exists_isIdempotentElem_sectionSupport_eq`: an open and closed subset
  of `|F|` is the support of an idempotent global function of the algebraic space `F`.
* `AlgebraicGeometry.Space.bijective_globalSectionsRingHom_of_isIso_fSharp` and
  `AlgebraicGeometry.Space.bijective_globalFunctionsMap_of_isIso_fSharp`: pullback of global
  functions is bijective when the structure map is an isomorphism.
* `AlgebraicGeometry.Space.exists_preimage_eq_of_isClopen_of_isIso_fSharp`: the statement about
  open and closed subsets above.

## References

* [Stacks Project, Tag 0A1B](https://stacks.math.columbia.edu/tag/0A1B)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Idempotent

attribute [local instance] pointTopology

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- On an étale chart `U` of `F`, the preimage of an open and closed subset `C` of `|F|` is a
clopen open of the chart scheme. -/
private theorem exists_isClopen_opens_chart_iff (C : Set (points B S hS F)) (hC : IsClopen C)
    (U : SmallEtale B S hS F) :
    ∃ V : ((BigFppfOver.toScheme B S hS).obj U.obj.left).Opens,
      IsClopen (V : Set ((BigFppfOver.toScheme B S hS).obj U.obj.left)) ∧
      ∀ q : points B S hS (yoneda.obj U.obj.left),
        pointsToScheme B S hS U.obj.left q ∈ V ↔
          pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom q ∈ C := by
  -- an open subset of `|F|` pulls back to an open of the chart, compatibly with scheme points
  have key : ∀ D : Set (points B S hS F), IsOpen D →
      ∃ V : ((BigFppfOver.toScheme B S hS).obj U.obj.left).Opens,
        ∀ q : points B S hS (yoneda.obj U.obj.left),
          pointsToScheme B S hS U.obj.left q ∈ V ↔
            pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom q ∈ D := by
    intro D hD
    obtain ⟨V, hV⟩ := exists_opens_chart_of_isOpen B S hS F U D hD
    exact ⟨V, fun q => by
      obtain ⟨p, rfl⟩ := Quot.exists_rep q
      exact (hV p).symm⟩
  obtain ⟨V, hV⟩ := key C hC.2
  obtain ⟨W, hW⟩ := key Cᶜ hC.1.isOpen_compl
  have hcompl : (V : Set ((BigFppfOver.toScheme B S hS).obj U.obj.left))ᶜ = W := by
    ext x
    obtain ⟨q, rfl⟩ := surjective_pointsToScheme B S hS U.obj.left x
    exact (not_congr (hV q)).trans (hW q).symm
  exact ⟨V, ⟨isOpen_compl_iff.1 (hcompl ▸ W.isOpen), V.isOpen⟩, hV⟩

/-- **An open and closed subset of the point space of an algebraic space is the support of an
idempotent global function.**  On every étale chart the preimages of the subset and of its
complement are disjoint opens covering the chart, so the chart carries the idempotent section
which is `1` on the first and `0` on the second; these are compatible, an idempotent section of a
scheme being determined by its basic open. -/
theorem exists_isIdempotentElem_sectionSupport_eq (hF : IsAlgebraicSpace B S hS F)
    (C : Set (points B S hS F)) (hC : IsClopen C) :
    ∃ e : globalFunctions B S hS F, IsIdempotentElem e ∧ sectionSupport B S hS F e = C := by
  choose V hVclopen hV using exists_isClopen_opens_chart_iff B S hS F C hC
  choose E hEidem hEbasic using
    fun U => Scheme.exists_isIdempotentElem_basicOpen_eq _ (hVclopen U)
  -- compatibility along morphisms of charts
  have hcompat : ∀ {U U' : SmallEtale B S hS F} (g : U' ⟶ U),
      ((BigFppfOver.toScheme B S hS).map g.hom.left).appTop (E U) = E U' := by
    intro U U' g
    apply Scheme.eq_of_isIdempotentElem_of_basicOpen_eq ((hEidem U).map _) (hEidem U')
    rw [hEbasic U', ← Scheme.preimage_basicOpen_top]
    change (BigFppfOver.toScheme B S hS).map g.hom.left ⁻¹'
      (((BigFppfOver.toScheme B S hS).obj U.obj.left).basicOpen (E U) : Set _) = _
    rw [hEbasic U]
    ext x
    obtain ⟨q, rfl⟩ := surjective_pointsToScheme B S hS U'.obj.left x
    change (BigFppfOver.toScheme B S hS).map g.hom.left (pointsToScheme B S hS U'.obj.left q) ∈
      V U ↔ _
    rw [← pointsToScheme_pointsMap_yoneda, hV U, pointsMap_chart_hom]
    exact (hV U' q).symm
  refine ⟨⟨fun U => E U.unop, fun {U U'} g => hcompat g.unop⟩,
    Subtype.ext (funext fun U => (hEidem U.unop).eq), ?_⟩
  ext x
  obtain ⟨U, q, rfl⟩ := exists_chart_point B S hS F hF x
  rw [mem_sectionSupport_iff]
  change pointsToScheme B S hS U.obj.left q ∈ (((BigFppfOver.toScheme B S hS).obj
    U.obj.left).basicOpen (E U) : Set _) ↔ _
  rw [hEbasic U]
  exact hV U q

end Idempotent

/-! ### Pullback of global functions along a morphism with `f_* 𝒪_X = 𝒪_Y` -/

/-- If `a ↦ φ a * u` is bijective in a commutative monoid, then so is `φ`. -/
private theorem _root_.Function.Bijective.of_bijective_mul_right {α β : Type*} [Monoid β]
    {φ : α → β} {u : β} (hcomm : ∀ x y : β, x * y = y * x)
    (h : Function.Bijective fun a => φ a * u) :
    Function.Bijective φ := by
  obtain ⟨a₀, ha₀⟩ := h.2 1
  have hu : IsUnit u := ⟨⟨u, φ a₀, (hcomm _ _).trans ha₀, ha₀⟩, rfl⟩
  refine ⟨fun a b hab => h.1 (congrArg (· * u) hab), fun t => ?_⟩
  obtain ⟨a, ha⟩ := h.2 (t * u)
  exact ⟨a, hu.mul_left_injective ha⟩

variable {B S hS} {X Y : AlgebraicSpaces B S hS}

/-- **The ring map on global sections of a morphism with invertible structure map is
bijective.**  The structure map makes `f_* 𝒪_X` free of rank one, so the endomorphisms of the
free module of rank one on `Y` — the global functions of `Y` — are identified with those on `X`
by Stacks 03D7; under this identification the endomorphism given by a global function `a` of `Y`
goes to multiplication by the image of `a` times a fixed global function `u` of `X`, which is
then a unit. -/
theorem bijective_globalSectionsRingHom_of_isIso_fSharp (f : X ⟶ Y)
    [IsIso (smallEtaleRingedToposHom B S hS f).fSharp] :
    Function.Bijective (globalSectionsRingHom
      (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
      (smallEtaleRingedToposModulesHom B S hS f)) := by
  obtain ⟨c⟩ : Nonempty (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS Y).O) ≅
      (Stacks.Sheaves.RingedToposModules.pushforwardModules
        (smallEtaleRingedToposModulesHom B S hS f)).obj (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O))) :=
    ⟨unitIsoModulePushforwardOfIsIsoFSharp f ≪≫ ((modulePushforwardIso B S hS f).app _).symm⟩
  let E := pushforwardUnitHomEquiv (smallEtaleRingedToposModulesHom B S hS f)
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X).O))
  let u := unitEndSection _ (E c.hom)
  let φ := globalSectionsRingHom (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposModulesHom B S hS f)
  change Function.Bijective φ
  have hform : ∀ a, unitEndSection (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS X).O) (E (unitEnd (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS Y).O) a ≫ c.hom)) = φ a * u := by
    intro a
    have h1 : E (unitEnd _ a ≫ c.hom) = unitEnd _ (φ a * u) := by
      refine (pushforwardUnitHomEquiv_unitEnd_comp _ _ a c.hom).trans ?_
      rw [unitEnd_mul]
      exact congrArg₂ (· ≫ ·) (unitEnd_globalSectionsRingHom (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposModulesHom B S hS f) a).symm
        (unitEnd_unitEndSection _ _).symm
    rw [h1, unitEndSection_unitEnd]
  have hbij : Function.Bijective (fun a => φ a * u) := by
    refine ⟨fun a b hab => ?_, fun t => ?_⟩
    · exact (unitEndEquiv (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS Y).O)).injective ((Iso.cancel_iso_hom_right _ _ c).1
        (E.injective ((unitEndEquiv (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS X).O)).symm.injective
          ((hform a).trans (hab.trans (hform b).symm)))))
    · refine ⟨unitEndSection _ (E.symm (unitEnd _ t) ≫ c.inv), ?_⟩
      refine (hform _).symm.trans ?_
      rw [unitEnd_unitEndSection _ (E.symm (unitEnd _ t) ≫ c.inv)]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, E.apply_symm_apply,
        unitEndSection_unitEnd]
  have hcomm : ∀ x y : RingCat.sectionsSubring
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).obj,
      x * y = y * x := fun x y => Subtype.ext (funext fun Z =>
    mul_comm (x.1 Z : (smallEtaleRingedTopos B S hS X).O.obj.obj Z) (y.1 Z))
  exact hbij.of_bijective_mul_right hcomm

/-- **Pullback of global functions along a morphism with invertible structure map is
bijective.**  It is the ring map of
`AlgebraicGeometry.Space.bijective_globalSectionsRingHom_of_isIso_fSharp`, by
`AlgebraicGeometry.Space.globalSectionsRingHom_eq_globalFunctionsMap`. -/
theorem bijective_globalFunctionsMap_of_isIso_fSharp (f : X ⟶ Y)
    [IsIso (smallEtaleRingedToposHom B S hS f).fSharp] :
    Function.Bijective (globalFunctionsMap B S hS f) := by
  have h := bijective_globalSectionsRingHom_of_isIso_fSharp f
  have heq : ∀ b : globalFunctions B S hS Y.1,
      (globalFunctionsMap B S hS f b).1 = (globalSectionsRingHom
        (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
        (smallEtaleRingedToposModulesHom B S hS f) ⟨b.1, b.2⟩).1 := fun b =>
    (globalSectionsRingHom_eq_globalFunctionsMap B S hS f b).symm
  refine ⟨fun a b hab => ?_, fun t => ?_⟩
  · exact Subtype.ext (congrArg Subtype.val
      (h.1 (Subtype.ext ((heq a).symm.trans ((congrArg Subtype.val hab).trans (heq b))))))
  · obtain ⟨a, ha⟩ := h.2 ⟨t.1, t.2⟩
    exact ⟨⟨a.1, a.2⟩, Subtype.ext ((heq _).trans (congrArg Subtype.val ha))⟩

section Clopen

attribute [local instance] pointTopology

/-- **For a morphism `f : X ⟶ T` to a scheme of the site with `f_* 𝒪_X = 𝒪_T`, an open and
closed subset of `|X|` is the preimage of a subset of `T`.**  It is the support of an idempotent
global function of `X`, which is the pullback of a function `ε` of `T` because pullback of global
functions is bijective; the support of a pulled-back function is the preimage of the basic open
of `ε`. -/
theorem exists_preimage_eq_of_isClopen_of_isIso_fSharp {T : BigFppfOver B S hS}
    (f : X ⟶ schemeSpace T) [IsIso (smallEtaleRingedToposHom B S hS f).fSharp]
    (C : Set (points B S hS X.obj)) (hC : IsClopen C) :
    ∃ D : Set ((BigFppfOver.toScheme B S hS).obj T), ∀ x : points B S hS X.obj,
      x ∈ C ↔ pointsToScheme B S hS T (pointsMap B S hS X.obj f.hom x) ∈ D := by
  obtain ⟨e, -, he⟩ := exists_isIdempotentElem_sectionSupport_eq B S hS X.obj X.property C hC
  obtain ⟨a, rfl⟩ := (bijective_globalFunctionsMap_of_isIso_fSharp f).2 e
  -- the global function `a` of `T` is the pullback of its value on the identity chart
  let top : SmallEtale B S hS (schemeSpace T).obj :=
    ⟨CostructuredArrow.mk (𝟙 (yoneda.obj T)), by
      rw [← yoneda.map_id]
      exact (presheaf_yoneda_map_iff B S hS AlgebraicGeometry.Etale.etale_isStableUnderBaseChange
        (𝟙 T)).2 (by rw [CategoryTheory.Functor.map_id]; infer_instance)⟩
  let ε : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) := a.val (op top)
  have ha : a = pullbackToGlobalFunctions B S hS (schemeSpace T) T (𝟙 _) ε := by
    apply injective_globalFunctions_val_of_isSurjective B S hS _ (schemeSpace T).property top
      (isSurjective_id B S hS _)
    change ε = Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (𝟙 (yoneda.obj T) ≫ 𝟙 _)))) ε
    rw [Category.comp_id, Functor.preimage_id, CategoryTheory.Functor.map_id]
    rfl
  refine ⟨((BigFppfOver.toScheme B S hS).obj T).basicOpen ε, fun x => ?_⟩
  have hpull : globalFunctionsMap B S hS f a = pullbackToGlobalFunctions B S hS X T f ε := by
    rw [ha]
    exact (RingHom.congr_fun (pullbackToGlobalFunctions_comp_left B S hS f T (𝟙 _)) ε).symm.trans
      (by rw [Category.comp_id])
  rw [← he, hpull]
  exact mem_sectionSupport_pullbackToGlobalFunctions_iff B S hS X T f ε x

end Clopen

end AlgebraicGeometry.Space

end
