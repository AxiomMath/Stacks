module

public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.PullbackCupProductDerived
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.EvenDegreeRing
public import StacksFrontier.AlgebraicGeometry.DeRham.PullbackComposition
public import StacksFrontier.AlgebraicGeometry.DeRham.FormsDirectImageComparisonSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IsIsoLocalCriterion
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingProjectionFormulaDerived

/-!
# Pullback on the ring of even-degree de Rham cohomology

For a commutative square `g' ≫ f = f' ≫ g` of schemes the pullback
`H^m_{dR}(X/S) ⟶ H^m_{dR}(X'/S')` preserves the unit (`deRhamPullbackSquare_one`) and the cup
product (`deRhamPullbackSquare_cup`), so it induces a ring homomorphism
`⨁ H^{2i}_{dR}(X/S) ⟶ ⨁ H^{2i}_{dR}(X'/S')`, which is functorial: the identity square induces the
identity (`deRhamPullbackSquare_id`) and composite squares the composite
(`deRhamPullbackSquare_comp`). This is the contravariant functor `A` of the proofs of Lemmas
0FW9 and 0FWB in the Stacks project.

## Main definitions

* `Stacks.DeRhamBaseChange.evenDeRhamPullback`: the ring homomorphism of a square.

## Main results

* `Stacks.DeRhamBaseChange.deRhamPullbackSquare_globalClass`: the pullback of the class of a
  global cocycle is the class of the pulled-back cocycle.
* `Stacks.DeRhamBaseChange.deRhamPullbackSquare_one`, `deRhamPullbackSquare_comp`,
  `deRhamPullbackSquare_id`.
* `Stacks.DeRhamBaseChange.evenDeRhamPullback_id`, `evenDeRhamPullback_comp`.

## Implementation notes

That the identity square induces the identity is proved by noting that its pullback is
bijective — the canonical map of de Rham complexes is an isomorphism, the pullback of forms along
`𝟙 X` being bijective on sections, and so is the comparison `g₀_* ⟶ Rg₀_*` along the closed
embedding `𝟙` — and idempotent, by functoriality.

## References

* [Stacks Project, Section 0FL6](https://stacks.math.columbia.edu/tag/0FL6)
* [Stacks Project, Section 0FM1](https://stacks.math.columbia.edu/tag/0FM1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.DeRhamDirectImage AlgebraicGeometry.ProperSmoothDeRham
open scoped Stacks.StandardDerivedModel
open Stacks.Cohomology.GlobalKunneth (baseSections baseRing)
open Stacks.Cohomology.DerivedGlobalCupProduct (sectionsComplex globalSections globalClass)

attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

universe u

namespace Stacks.DeRhamBaseChange

variable {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (w : g' ≫ f = f' ≫ g)

/-- The pullback of a commutative square, written out. -/
theorem deRhamPullbackSquare_apply (m : ℤ)
    (z : AlgebraicGeometry.SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) m) :
    deRhamPullbackSquare g' f' f g w m z =
      ((AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
        (Scheme.Hom.deRhamAlgebras f)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) m).inv ≫
      Scheme.Hom.deRhamCohomologyPullback g' f f' g w m ≫
      (AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
        (Scheme.Hom.deRhamAlgebras f')
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential
          (Scheme.Hom.deRhamAlgebras f')) m).hom).hom z :=
  rfl

/-- **The pullback of the class of a global cocycle** is the class of the pulled-back cocycle:
for a global cocycle `s` of `Ω^•_{X/S}` and a global cocycle `s'` of `Ω^•_{X'/S'}` whose underlying
section is the pullback of that of `s`, `g'^*[s] = [s']`. -/
theorem deRhamPullbackSquare_globalClass (m : ℤ)
    (s : (sectionsComplex (inverseImageBase f) (deRhamComplexInt f)).cycles m)
    (s' : (sectionsComplex (inverseImageBase f') (deRhamComplexInt f')).cycles m)
    (hs : ((sectionsComplex (inverseImageBase f') (deRhamComplexInt f')).iCycles m).hom s' =
      ((((globalSections (inverseImageBase f)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (deRhamPushforwardInt g' f' f g w)).f m).hom
        (((sectionsComplex (inverseImageBase f) (deRhamComplexInt f)).iCycles m).hom s)) :
    deRhamPullbackSquare g' f' f g w m (globalClass (deRhamComplexInt f) m s) =
      globalClass (deRhamComplexInt f') m s' := by
  refine (deRhamPullbackSquare_eq_lerayMap g' f' f g w m _).trans ?_
  refine (congrArg (Stacks.Cohomology.LerayCupPairing.lerayMap (inverseImageBaseMap g' f' f g w)
    (DerivedCategory.Q.obj (deRhamComplexModules f')) m)
    ((homologyMap_baseSections_comp_apply (inverseImageBase f) m _ _ _).trans
      (congrArg _ (Stacks.Cohomology.DerivedGlobalCupProduct.globalClass_map
        (inverseImageBase f) (deRhamPushforwardInt g' f' f g w) m s)))).trans ?_
  exact Stacks.Cohomology.LerayCupPairing.lerayCohomologyIso_globalClass _ _ m _ s'
    ((ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i _ m) s).trans hs.symm)

/-- **The canonical map of de Rham complexes preserves the unit**: it sends the section `1` of
`Ω^0_{X/S}` to the section `1` of `Ω^0_{X'/S'}`. -/
theorem deRhamPushforwardInt_one (U : (Opens X.carrier)ᵒᵖ) :
    ((deRhamPushforwardInt g' f' f g w).f 0).val.app U ((deRhamDGA f).one.eval U) =
      (deRhamDGA f').one.eval ((Opens.map g'.base).op.obj U) := by
  have h1 := congrArg (fun φ => φ.val.app U ((deRhamDGA f).one.eval U))
    (deRhamPushforwardInt_f g' f' f g w 0)
  have hz : ((deRhamComplexNat f).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom.val.app U
      ((deRhamDGA f).one.eval U) = (Scheme.Hom.deRhamAlgebras f).exterior.one.eval U :=
    eq_of_heq ((extendXIso_hom_val_app_heq _ 0 U _).trans
      (AlgebraicGeometry.SheafOfModules.deRhamDifferentialGradedAlgebra_one _ _ U))
  have h2 : (formsPushforward g' f' f g w 0).val.app U
      ((Scheme.Hom.deRhamAlgebras f).exterior.one.eval U) =
        (Scheme.Hom.deRhamAlgebras f').exterior.one.eval ((Opens.map g'.base).op.obj U) :=
    (formsPushforward_val_app g' f' f g w 0 U _).trans
      ((Scheme.Hom.deRhamFormsPushforwardHom g' f f' g w).map_one U)
  have h3 := h1.trans (congrArg (fun t => ((deRhamComplexNat f').extendXIso
      ComplexShape.embeddingUpNat (i := 0) rfl).inv.val.app ((Opens.map g'.base).op.obj U) t)
    ((congrArg (fun t => (formsPushforward g' f' f g w 0).val.app U t) hz).trans h2))
  exact eq_of_heq ((heq_of_eq h3).trans ((extendXIso_inv_val_app_heq _ 0 _ _).trans
    (AlgebraicGeometry.SheafOfModules.deRhamDifferentialGradedAlgebra_one _ _ _).symm))

/-- **Pullback preserves the unit**: `g'^*1 = 1` in `H^0_{dR}`. -/
theorem deRhamPullbackSquare_one :
    deRhamPullbackSquare g' f' f g w 0
        (AlgebraicGeometry.SheafOfModules.deRhamOneClass (Scheme.Hom.deRhamAlgebras f)
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f))) =
      AlgebraicGeometry.SheafOfModules.deRhamOneClass (Scheme.Hom.deRhamAlgebras f')
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f')) := by
  have e := AlgebraicGeometry.SheafOfModules.deRhamOneClass_eq_globalClass_one
    (Scheme.Hom.deRhamAlgebras f)
    (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f))
  have e' := AlgebraicGeometry.SheafOfModules.deRhamOneClass_eq_globalClass_one
    (Scheme.Hom.deRhamAlgebras f')
    (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f'))
  have hs := (AlgebraicGeometry.SheafOfModules.iCycles_deRhamOneCycle
    (Scheme.Hom.deRhamAlgebras f')
    (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f'))).trans
    ((deRhamPushforwardInt_one g' f' f g w (op ⊤)).symm.trans (congrArg
      (fun t => ((deRhamPushforwardInt g' f' f g w).f 0).val.app (op ⊤) t)
      (AlgebraicGeometry.SheafOfModules.iCycles_deRhamOneCycle (Scheme.Hom.deRhamAlgebras f)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential
          (Scheme.Hom.deRhamAlgebras f))).symm))
  exact (congrArg (deRhamPullbackSquare g' f' f g w 0) e).trans
    ((deRhamPullbackSquare_globalClass g' f' f g w 0 _ _ hs).trans e'.symm)

/-- **Pullback is functorial for composites of squares**: along `X'' ⟶ X' ⟶ X` over
`S'' ⟶ S' ⟶ S`, pulling back along the right square and then along the left one is pulling back
along the composite square. -/
theorem deRhamPullbackSquare_comp {X'' S'' : Scheme.{u}} (g'' : X'' ⟶ X') (f'' : X'' ⟶ S'')
    (k : S'' ⟶ S') (w' : g'' ≫ f' = f'' ≫ k) (w'' : (g'' ≫ g') ≫ f = f'' ≫ (k ≫ g)) (m : ℤ)
    (z : AlgebraicGeometry.SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) m) :
    deRhamPullbackSquare g'' f'' f' k w' m (deRhamPullbackSquare g' f' f g w m z) =
      deRhamPullbackSquare (g'' ≫ g') f'' f (k ≫ g) w'' m z := by
  rw [deRhamPullbackSquare_apply, deRhamPullbackSquare_apply, deRhamPullbackSquare_apply,
    ← Scheme.Hom.deRhamCohomologyPullback_comp g'' g' f f' f'' g k w w' w'' m]
  simp

/-- Pullback along equal squares agrees. -/
theorem deRhamPullbackSquare_congr {g'₁ g'₂ : X' ⟶ X} {g₁ g₂ : S' ⟶ S} (hg' : g'₁ = g'₂)
    (hg : g₁ = g₂) (w₁ : g'₁ ≫ f = f' ≫ g₁) (w₂ : g'₂ ≫ f = f' ≫ g₂) (m : ℤ)
    (z : AlgebraicGeometry.SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) m) :
    deRhamPullbackSquare g'₁ f' f g₁ w₁ m z = deRhamPullbackSquare g'₂ f' f g₂ w₂ m z := by
  subst hg' hg
  rfl

/-- Along the identity square, the adjoint of the canonical map on forms is an isomorphism: on
sections it is the pullback of forms along `𝟙 X`, which is bijective. -/
instance isIso_formsAdjoint_id (w₀ : 𝟙 X ≫ f = f ≫ 𝟙 S) (p : ℕ) :
    IsIso (formsAdjoint (𝟙 X) f f (𝟙 S) w₀ p) :=
  AlgebraicGeometry.SheafOfModules.isIso_of_bijective_app_of_iSup_eq_top
    (ι := Unit) (fun _ => ⊤) (by simp) _ fun _ V _ =>
      Scheme.Hom.bijective_relativeDifferentialFormsPullback_of_isIso (𝟙 X) f f w₀ (p : ℤ) V

/-- Along the identity square, the degreewise canonical map of de Rham complexes is an
isomorphism. -/
instance isIso_formsPushforward_id (w₀ : 𝟙 X ≫ f = f ≫ 𝟙 S) (p : ℕ) :
    IsIso (formsPushforward (𝟙 X) f f (𝟙 S) w₀ p) := by
  have h1 : IsIso ((_root_.pushforward (toInverseImageBase f)).map
      (formsAdjoint (𝟙 X) f f (𝟙 S) w₀ p)) :=
    @Functor.map_isIso _ _ _ _ _ _ _ _ (isIso_formsAdjoint_id f w₀ p)
  unfold formsPushforward
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1
    ((Iso.app (pushforwardSquareIso (𝟙 X) f f (𝟙 S) w₀) _).isIso_inv)

/-- **Along the identity square, the canonical map of de Rham complexes is an isomorphism.** -/
instance isIso_deRhamPushforwardInt_id (w₀ : 𝟙 X ≫ f = f ≫ 𝟙 S) :
    IsIso (deRhamPushforwardInt (𝟙 X) f f (𝟙 S) w₀) := by
  have : ∀ n : ℤ, IsIso ((deRhamPushforwardInt (𝟙 X) f f (𝟙 S) w₀).f n) := by
    intro n
    by_cases hn : 0 ≤ n
    · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      rw [deRhamPushforwardInt_f]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _
        ((HomologicalComplex.extendXIso (deRhamComplexNat f) ComplexShape.embeddingUpNat
          rfl).isIso_hom)
        (@IsIso.comp_isIso _ _ _ _ _ _ _ (isIso_formsPushforward_id f w₀ p)
          (((modulePushforward (inverseImageBaseMap (𝟙 X) f f (𝟙 S) w₀)).mapIso
            (HomologicalComplex.extendXIso (deRhamComplexNat f) ComplexShape.embeddingUpNat
              rfl)).isIso_inv))
    · have h1 := isZero_deRhamComplexInt_X_of_neg f n (by omega)
      have h2 : Limits.IsZero ((((modulePushforward
          (inverseImageBaseMap (𝟙 X) f f (𝟙 S) w₀)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (deRhamComplexInt f)).X n) :=
        Functor.map_isZero (modulePushforward (inverseImageBaseMap (𝟙 X) f f (𝟙 S) w₀)) h1
      exact isIso_of_source_target_iso_zero _ h1.isoZero h2.isoZero
  exact HomologicalComplex.Hom.isIso_of_components _

/-- Along the identity square, the canonical map `Ω^•_{X/S} ⟶ Rg₀_*Ω^•_{X/S}` is an isomorphism:
the canonical map of complexes is, and so is the comparison `g₀_* ⟶ Rg₀_*`, the underlying map of
`g₀` being the identity, a closed embedding. -/
theorem isIso_deRhamComparisonQ_id (w₀ : 𝟙 X ≫ f = f ≫ 𝟙 S) :
    IsIso (deRhamComparisonQ (𝟙 X) f f (𝟙 S) w₀) := by
  have h1 : IsIso (DerivedCategory.Q.map (deRhamPushforwardModules (𝟙 X) f f (𝟙 S) w₀)) :=
    @Functor.map_isIso _ _ _ _ _ _ _ _ (isIso_deRhamPushforwardInt_id f w₀)
  have h2 : IsIso
      (Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ
      (inverseImageBaseMap (𝟙 X) f f (𝟙 S) w₀) (deRhamComplexModules f)) :=
    Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes.isIso_pushforwardComparisonQ _
      Topology.IsClosedEmbedding.id _
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2

/-- **Pullback along the identity square is the identity.** It is bijective, the canonical map
being an isomorphism, and idempotent, by functoriality. -/
theorem deRhamPullbackSquare_id (w₀ : 𝟙 X ≫ f = f ≫ 𝟙 S) (m : ℤ)
    (z : AlgebraicGeometry.SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) m) :
    deRhamPullbackSquare (𝟙 X) f f (𝟙 S) w₀ m z = z := by
  have hc := isIso_deRhamComparisonQ_id f w₀
  have hH : Function.Bijective ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (inverseImageBase f))) m).map
        ((baseSections (inverseImageBase f)).map (deRhamComparisonQ (𝟙 X) f f (𝟙 S) w₀))).hom :=
    ConcreteCategory.bijective_of_isIso _
  have hL : Function.Bijective (Stacks.Cohomology.LerayCupPairing.lerayMap
      (inverseImageBaseMap (𝟙 X) f f (𝟙 S) w₀) (DerivedCategory.Q.obj (deRhamComplexModules f))
      m) :=
    (Stacks.Cohomology.LerayCupPairing.lerayCohomologyIso
      (inverseImageBaseMap (𝟙 X) f f (𝟙 S) w₀) (DerivedCategory.Q.obj (deRhamComplexModules f))
      m).toLinearEquiv.bijective
  have hinj : Function.Injective (deRhamPullbackSquare (𝟙 X) f f (𝟙 S) w₀ m) := by
    intro a b hab
    rw [deRhamPullbackSquare_eq_lerayMap, deRhamPullbackSquare_eq_lerayMap] at hab
    exact hH.1 (hL.1 hab)
  refine hinj ?_
  refine (deRhamPullbackSquare_comp (𝟙 X) f f (𝟙 S) w₀ (𝟙 X) f (𝟙 S) w₀
    (by simp) m z).trans ?_
  exact deRhamPullbackSquare_congr f f (Category.comp_id _) (Category.comp_id _) _ _ m z

/-! ### The ring homomorphism on even-degree de Rham cohomology -/

/-- The ring `⨁_{i ≥ 0} H^{2i}_{dR}(X/S)` of even-degree relative de Rham cohomology of a morphism
of schemes. -/
abbrev evenDeRhamRing (p : X ⟶ S) : Type u :=
  AlgebraicGeometry.SheafOfModules.evenDeRhamRing (Scheme.Hom.deRhamAlgebras p)
    (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p))

/-- **The pullback `⨁ H^{2i}_{dR}(X/S) ⟶ ⨁ H^{2i}_{dR}(X'/S')` of a commutative square**, a ring
homomorphism: pullback preserves the unit and the cup product. -/
def evenDeRhamPullback : evenDeRhamRing f →+* evenDeRhamRing f' :=
  AlgebraicGeometry.SheafOfModules.evenDeRhamRingHom _ _ _ _ (deRhamPullbackSquare g' f' f g w)
    (deRhamPullbackSquare_one g' f' f g w) (deRhamPullbackSquare_cup g' f' f g w)

/-- On the summand `H^{2i}_{dR}(X/S)`, the even-degree pullback is the degree-`2i` pullback
`deRhamPullbackSquare`. -/
@[simp]
theorem evenDeRhamPullback_of (i : ℕ)
    (a : AlgebraicGeometry.SheafOfModules.evenDeRhamCohomology (Scheme.Hom.deRhamAlgebras f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) i) :
    evenDeRhamPullback g' f' f g w (DirectSum.of _ i a) =
      DirectSum.of _ i (deRhamPullbackSquare g' f' f g w _ a) :=
  AlgebraicGeometry.SheafOfModules.evenDeRhamRingHom_of _ _ _ _ _ _ _ i a

/-- Pullback along the identity square is the identity. -/
theorem evenDeRhamPullback_id (w₀ : 𝟙 X ≫ f = f ≫ 𝟙 S) :
    evenDeRhamPullback (𝟙 X) f f (𝟙 S) w₀ = RingHom.id _ := by
  refine DirectSum.ringHom_ext fun i a => ?_
  rw [evenDeRhamPullback_of, deRhamPullbackSquare_id]
  rfl

/-- Pullback is functorial for composites of squares. -/
theorem evenDeRhamPullback_comp {X'' S'' : Scheme.{u}} (g'' : X'' ⟶ X') (f'' : X'' ⟶ S'')
    (k : S'' ⟶ S') (w' : g'' ≫ f' = f'' ≫ k) (w'' : (g'' ≫ g') ≫ f = f'' ≫ (k ≫ g)) :
    evenDeRhamPullback (g'' ≫ g') f'' f (k ≫ g) w'' =
      (evenDeRhamPullback g'' f'' f' k w').comp (evenDeRhamPullback g' f' f g w) := by
  refine DirectSum.ringHom_ext fun i a => ?_
  rw [RingHom.comp_apply, evenDeRhamPullback_of, evenDeRhamPullback_of, evenDeRhamPullback_of,
    deRhamPullbackSquare_comp]

/-- Pullback preserves the grading. -/
theorem evenDeRhamPullback_mem_grade (i : ℕ) {a : evenDeRhamRing f}
    (ha : a ∈ AlgebraicGeometry.SheafOfModules.evenDeRhamGrade _ _ i) :
    evenDeRhamPullback g' f' f g w a ∈ AlgebraicGeometry.SheafOfModules.evenDeRhamGrade _ _ i :=
  AlgebraicGeometry.SheafOfModules.evenDeRhamRingHom_mem_grade _ _ _ _ _ _ _ i ha

end Stacks.DeRhamBaseChange
