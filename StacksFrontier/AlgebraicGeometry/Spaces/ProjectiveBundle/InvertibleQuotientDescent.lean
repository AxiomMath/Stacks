module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesRightExactSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.InvertibleChartLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.InvertibleQuotientBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SymmetricAlgebraQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartModuleGlueingEquivalence

/-!
# Invertible quotients of a module on an algebraic space descend from the étale charts

Let `X` be an algebraic space and `ℰ` an `𝒪_X`-module.  An isomorphism class of invertible
quotients `ℰ ⟶ ℒ` is determined by its restrictions to the étale scheme charts `U` of `X`, and a
family of classes of invertible quotients of the restrictions `ℰ|_U`, compatible with the
chartwise pullbacks along morphisms of charts, is the family of restrictions of one class on `X`.

The comparison isomorphism between two quotients is unique, the quotient maps being
epimorphisms, so local comparisons automatically form a descent datum; the existence of the
glued quotient is the glueing of modules of Stacks 03LY, and its invertibility is the étale
locality of invertibility.

## Main definitions

* `AlgebraicGeometry.Space.chartRestrictClass`: the restriction of a class of invertible
  quotients to an étale chart.
* `AlgebraicGeometry.Space.IsCompatibleChartQuotientFamily`: compatibility of a chartwise family
  of classes with the chartwise pullbacks.

## Main results

* `AlgebraicGeometry.Space.invertibleQuotientClass_ext_of_chartRestrictClass`: a class is
  determined by its restrictions to the charts.
* `AlgebraicGeometry.Space.exists_chartRestrictClass_eq`: a compatible chartwise family of classes
  is the family of restrictions of a class.

## References

* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : AlgebraicSpaces B S hS) (E : Modules.{u, u} B S hS X.1 X.2)

/-- **The restriction of a class of invertible quotients of `ℰ` to an étale chart `U`**, a class
of invertible quotients of `ℰ|_U`. -/
abbrev chartRestrictClass (U : SmallEtale B S hS X.1) :
    InvertibleQuotientClass X E →
      InvertibleQuotientClass (chartSpace B S hS X U) ((chartModuleRestriction B S hS X U).obj E) :=
  invertibleQuotientBaseChangeClass (chartToSpace B S hS X U) (Iso.refl _)

/-- **A chartwise family of classes of invertible quotients is compatible** when the class on a
chart `V` is the chartwise pullback of the class on `U` along every morphism `V ⟶ U` of charts,
read through the transition isomorphism of the restrictions of `ℰ`. -/
def IsCompatibleChartQuotientFamily
    (c : ∀ U : SmallEtale B S hS X.1,
      InvertibleQuotientClass (chartSpace B S hS X U) ((chartModuleRestriction B S hS X U).obj E)) :
    Prop :=
  ∀ {V U : SmallEtale B S hS X.1} (f : V ⟶ U),
    c V = invertibleQuotientBaseChangeClass (chartMap B S hS X f)
      (chartModuleRestrictionTransitions B S hS X E f).symm (c U)

/-- **A class of invertible quotients is determined by its restrictions to the étale charts.**
The comparison isomorphisms on the charts are unique, the quotient maps being epimorphisms, so
they glue (Stacks 03LY) to an isomorphism on `X` carrying one quotient map to the other. -/
theorem invertibleQuotientClass_ext_of_chartRestrictClass (c c' : InvertibleQuotientClass X E)
    (h : ∀ U : SmallEtale B S hS X.1, chartRestrictClass X E U c = chartRestrictClass X E U c') :
    c = c' := by
  induction c using Quotient.ind with | _ Q => ?_
  induction c' using Quotient.ind with | _ Q' => ?_
  have hQ := Q.epi
  have hU : ∀ U, ∃ α : (chartModuleRestriction B S hS X U).obj Q.L ≅
      (chartModuleRestriction B S hS X U).obj Q'.L,
      (chartModuleRestriction B S hS X U).map Q.q ≫ α.hom =
        (chartModuleRestriction B S hS X U).map Q'.q := fun U => by
    obtain ⟨α, hα⟩ := Quotient.exact (h U)
    refine ⟨α, ?_⟩
    have h2 : (𝟙 _ ≫ (chartModuleRestriction B S hS X U).map Q.q) ≫ α.hom =
        𝟙 _ ≫ (chartModuleRestriction B S hS X U).map Q'.q := hα
    rwa [Category.id_comp, Category.id_comp] at h2
  choose α hα using hU
  let φ : (chartModuleGlueingFunctor B S hS X).obj Q.L ⟶
      (chartModuleGlueingFunctor B S hS X).obj Q'.L :=
    { app := fun U => (α U).hom
      w := fun {V U} f => by
        have : Epi ((chartModuleInverseImage B S hS X f).map
            ((chartModuleRestriction B S hS X U).map Q.q)) :=
          epi_modulePullback_map B S hS (chartMap B S hS X f) _
            (epi_modulePullback_map B S hS (chartToSpace B S hS X U) Q.q hQ)
        show (chartModuleInverseImage B S hS X f).map (α U).hom ≫
            (chartModuleRestrictionTransitions B S hS X Q'.L f).hom =
          (chartModuleRestrictionTransitions B S hS X Q.L f).hom ≫ (α V).hom
        rw [← cancel_epi ((chartModuleInverseImage B S hS X f).map
          ((chartModuleRestriction B S hS X U).map Q.q)), ← Functor.map_comp_assoc, hα,
          chartModuleRestrictionTransitions_naturality, reassoc_of%
          (chartModuleRestrictionTransitions_naturality B S hS X f Q.q), hα] }
  have : IsIso φ := ChartModuleGlueingData.isIso_of_isIso_app B S hS X φ fun U => by
    show IsIso (α U).hom; infer_instance
  let e : Q.L ≅ Q'.L := (chartModuleGlueingFunctor B S hS X).preimageIso (asIso φ)
  refine Quotient.sound ⟨e, (chartModuleGlueingFunctor B S hS X).map_injective ?_⟩
  refine ChartModuleGlueingData.hom_ext B S hS X fun U => ?_
  show (chartModuleRestriction B S hS X U).map (Q.q ≫ e.hom) =
    (chartModuleRestriction B S hS X U).map Q'.q
  rw [Functor.map_comp, ← hα U]
  congr 1
  exact congrArg (fun k => ChartModuleGlueingData.Hom.app k U)
    ((chartModuleGlueingFunctor B S hS X).map_preimage φ)

/-- **Comparison isomorphisms of quotients of the chart restrictions satisfy the cocycle
condition.**  If `q_U : ℰ|_U ⟶ ℒ_U` are epimorphisms and `β_f : f^*ℒ_U ≅ ℒ_V` carry `f^*q_U` to
`q_V` through the transitions of `ℰ`, then the `β_f` form a glueing datum: both sides of the
cocycle condition carry the epimorphism `g^*f^*q_U` to the same map, by the cocycle condition of
the restrictions of `ℰ`. -/
theorem isChartModuleCocycle_of_quotients
    (L : ChartModuleFamily B S hS X)
    (q : ∀ U, (chartModuleRestriction B S hS X U).obj E ⟶ L U) (hq : ∀ U, Epi (q U))
    (β : ChartModuleTransitions B S hS X L)
    (hβ : ∀ {V U : SmallEtale B S hS X.1} (f : V ⟶ U),
      (chartModuleInverseImage B S hS X f).map (q U) ≫ (β f).hom =
        (chartModuleRestrictionTransitions B S hS X E f).hom ≫ q V) :
    IsChartModuleCocycle B S hS X L β := by
  intro W V U f g
  have hE := chartModuleRestrictionTransitions_cocycle B S hS X E f g
  let m := (chartModuleInverseImage B S hS X g).map
      ((chartModuleInverseImage B S hS X f).map (q U))
  have : Epi m := epi_modulePullback_map B S hS (chartMap B S hS X g) _
    (epi_modulePullback_map B S hS (chartMap B S hS X f) _ (hq U))
  rw [← cancel_epi m]
  calc m ≫ (chartModuleInverseImage B S hS X g).map (β f).hom ≫ (β g).hom
      = (chartModuleInverseImage B S hS X g).map
          ((chartModuleInverseImage B S hS X f).map (q U) ≫ (β f).hom) ≫ (β g).hom := by
        rw [Functor.map_comp, Category.assoc]
    _ = (chartModuleInverseImage B S hS X g).map
          (chartModuleRestrictionTransitions B S hS X E f).hom ≫
          (chartModuleInverseImage B S hS X g).map (q V) ≫ (β g).hom := by
        rw [hβ f, Functor.map_comp, Category.assoc]
    _ = (chartModuleInverseImage B S hS X g).map
          (chartModuleRestrictionTransitions B S hS X E f).hom ≫
          (chartModuleRestrictionTransitions B S hS X E g).hom ≫ q W := by
        rw [hβ g]
    _ = chartModuleInverseImageCompApp B S hS X f g ((chartModuleRestriction B S hS X U).obj E) ≫
          (chartModuleRestrictionTransitions B S hS X E (g ≫ f)).hom ≫ q W := by
        rw [← Category.assoc, hE, Category.assoc]
    _ = chartModuleInverseImageCompApp B S hS X f g ((chartModuleRestriction B S hS X U).obj E) ≫
          (chartModuleInverseImage B S hS X (g ≫ f)).map (q U) ≫ (β (g ≫ f)).hom := by
        rw [hβ (g ≫ f)]
    _ = m ≫ chartModuleInverseImageCompApp B S hS X f g (L U) ≫ (β (g ≫ f)).hom := by
        rw [← Category.assoc, ← chartModuleInverseImageCompApp_naturality, Category.assoc]

/-- **A compatible chartwise family of classes of invertible quotients is the family of
restrictions of a class on `X`.**  Representatives on the charts glue (Stacks 03LY) along the
comparison isomorphisms, which satisfy the cocycle condition because they are unique; the glued
quotient map is an epimorphism because it is one on every chart, and the glued module is
invertible because it is on every chart. -/
theorem exists_chartRestrictClass_eq
    (c : ∀ U : SmallEtale B S hS X.1,
      InvertibleQuotientClass (chartSpace B S hS X U) ((chartModuleRestriction B S hS X U).obj E))
    (hc : IsCompatibleChartQuotientFamily X E c) :
    ∃ c₀ : InvertibleQuotientClass X E, ∀ U, chartRestrictClass X E U c₀ = c U := by
  classical
  let Q : ∀ U, InvertibleQuotient (chartSpace B S hS X U)
      ((chartModuleRestriction B S hS X U).obj E) := fun U => (c U).out
  have hQc : ∀ U, Quotient.mk _ (Q U) = c U := fun U => Quotient.out_eq _
  have hβ : ∀ {V U : SmallEtale B S hS X.1} (f : V ⟶ U),
      ∃ β : (chartModuleInverseImage B S hS X f).obj (Q U).L ≅ (Q V).L,
        (chartModuleInverseImage B S hS X f).map (Q U).q ≫ β.hom =
          (chartModuleRestrictionTransitions B S hS X E f).hom ≫ (Q V).q := fun {V U} f => by
    have h := hc f
    rw [← hQc U, ← hQc V] at h
    have h' : Quotient.mk (invertibleQuotientSetoid _ _) (Q V) =
        Quotient.mk (invertibleQuotientSetoid _ _) ((Q U).baseChange (chartMap B S hS X f)
          (chartModuleRestrictionTransitions B S hS X E f).symm) := h
    obtain ⟨β, hβ⟩ := Quotient.exact h'.symm
    let β' : (chartModuleInverseImage B S hS X f).obj (Q U).L ≅ (Q V).L := β
    have hβ' : ((chartModuleRestrictionTransitions B S hS X E f).symm.hom ≫
        (chartModuleInverseImage B S hS X f).map (Q U).q) ≫ β'.hom = (Q V).q := hβ
    refine ⟨β', ?_⟩
    rw [← hβ', Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  choose β hβ using fun (V U : SmallEtale B S hS X.1) (f : V ⟶ U) => hβ f
  have hepi : ∀ U, Epi (Q U).q := fun U => (Q U).epi
  let D : ChartModuleGlueingData B S hS X :=
    ⟨fun U => (Q U).L, fun {V U} f => β V U f,
      isChartModuleCocycle_of_quotients X E (fun U => (Q U).L) (fun U => (Q U).q) hepi
        (fun {V U} f => β V U f) (fun {V U} f => hβ V U f)⟩
  let eqv := (chartModuleGlueingFunctor B S hS X).asEquivalence
  let ψ : @Quiver.Hom _ (ChartModuleGlueingData.instCategory B S hS X).toQuiver
      (eqv.functor.obj E) D :=
    ChartModuleGlueingData.Hom.mk (fun U => (Q U).q) (fun {V U} f => hβ V U f)
  let L : Modules.{u, u} B S hS X.1 X.2 := eqv.inverse.obj D
  obtain ⟨q, hqdef⟩ : ∃ q : E ⟶ L, q = (eqv.toAdjunction.homEquiv E D) ψ := ⟨_, rfl⟩
  have hq : eqv.functor.map q ≫ eqv.counit.app D = ψ := by
    have h := Adjunction.homEquiv_counit eqv.toAdjunction (g := q)
    rw [hqdef] at h
    rw [Equiv.symm_apply_apply] at h
    rw [hqdef]
    exact h.symm
  have hκ : ∀ U, IsIso ((eqv.counit.app D).app U) := fun U =>
    ⟨⟨(eqv.counitInv.app D).app U, by
      rw [← ChartModuleGlueingData.comp_app, Iso.hom_inv_id_app]; rfl, by
      rw [← ChartModuleGlueingData.comp_app, Iso.inv_hom_id_app]; rfl⟩⟩
  have hqU : ∀ U, (chartModuleRestriction B S hS X U).map q ≫ (eqv.counit.app D).app U =
      (Q U).q := fun U => congrArg (fun k => ChartModuleGlueingData.Hom.app k U) hq
  have hψ : Epi ψ := ⟨fun {Z} a b hab => ChartModuleGlueingData.hom_ext B S hS X fun U =>
    (cancel_epi (Q U).q).1 (congrArg (fun k => ChartModuleGlueingData.Hom.app k U) hab)⟩
  have hfq : eqv.functor.map q = ψ ≫ eqv.counitInv.app D :=
    (Iso.eq_comp_inv (eqv.counitIso.app D)).2 hq
  have hqepi : Epi q := ⟨fun {Z} a b hab => by
    apply eqv.functor.map_injective
    have h2 := congrArg eqv.functor.map hab
    rw [Functor.map_comp, Functor.map_comp, hfq, Category.assoc, Category.assoc] at h2
    exact (cancel_epi _).1 ((cancel_epi ψ).1 h2)⟩
  have hLinv : IsInvertibleModule X L :=
    isInvertibleModule_of_forall_chartModuleRestriction X L fun U =>
      isInvertibleModule_of_iso (@asIso _ _ _ _ _ (hκ U)).symm (Q U).invertible
  refine ⟨Quotient.mk _ ⟨L, hLinv, q, hqepi⟩, fun U => ?_⟩
  rw [← hQc U]
  refine Quotient.sound ⟨@asIso _ _ _ _ _ (hκ U), ?_⟩
  show (𝟙 _ ≫ (chartModuleRestriction B S hS X U).map q) ≫ (eqv.counit.app D).app U = (Q U).q
  rw [Category.id_comp, hqU]

end AlgebraicGeometry.Space

end
