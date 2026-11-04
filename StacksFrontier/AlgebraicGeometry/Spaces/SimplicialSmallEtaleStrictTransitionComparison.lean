module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleStrictDegree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.TwoIsoCoherenceOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHomSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackProjectionFormula
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# Comparison formulas on complexes for the strict transitions of a simplicial space

Let `X` be a simplicial algebraic space with an augmentation `a : X → Z`, `b = a ∘ e⁻¹` its
augmentation on the strict total site, `g_n` the component morphisms, `realize_n` the realization
equivalences and `f_φ` the transition morphisms of the strict components. This file computes, on
complexes and after the comparisons of Stacks 06YY, the isomorphisms that enter the transition
coherence of the system of `Lb^*K`: the derived transition of Stacks 0D9P, the derived square of
the strict transitions, the component isomorphisms `Lb^* ⋙ D(g_n^{-1}) ⋙ L realize_n^* ≅ La_n^*`,
and the isomorphisms `La_m^* ⋙ LX(φ)^* ≅ La_n^*` of the augmentation.

## Main definitions

* `Space.SimplicialSpacesEtaleSite.augmentationTransitionTwoIso`:
  `a_m ∘ X(φ) ≅ a_n` as morphisms of ringed topoi.
* `Space.SimplicialSpacesEtaleSite.augmentationTransitionDerivedIso`:
  `La_m^* ⋙ LX(φ)^* ≅ La_n^*` (Stacks 0D6D).

## Main results

* `CategoryTheory.transition_transport_comparison`: a transition read through componentwise
  comparisons is determined by its upstairs form.
* `Space.SimplicialSpacesEtaleSite.strictAugmentationDegreeDerivedIso_hom_app_Qh`:
  the component isomorphism on a complex.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 0D9P](https://stacks.math.columbia.edu/tag/0D9P)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CategoryTheory.Limits AlgebraicGeometry.RingedToposHom

namespace CategoryTheory

universe v₀ v₁ v₂ v₃ v₄ v₅ w₀ w₁ w₂ w₃ w₄ w₅ u₀ u₁ u₂ u₃ u₄ u₅ t₀ t₁ t₂ t₃ t₄ t₅

variable {H₀ : Type u₀} {H₁ : Type u₁} {H₂ : Type u₂} {H₃ : Type u₃} {H₄ : Type u₄}
  {H₅ : Type u₅} [Category.{v₀} H₀] [Category.{v₁} H₁] [Category.{v₂} H₂] [Category.{v₃} H₃]
  [Category.{v₄} H₄] [Category.{v₅} H₅]
  {D₀ : Type t₀} {D₁ : Type t₁} {D₂ : Type t₂} {D₃ : Type t₃} {D₄ : Type t₄}
  {D₅ : Type t₅} [Category.{w₀} D₀] [Category.{w₁} D₁] [Category.{w₂} D₂] [Category.{w₃} D₃]
  [Category.{w₄} D₄] [Category.{w₅} D₅]
  {q₀ : H₀ ⥤ D₀} {q₁ : H₁ ⥤ D₁} {q₂ : H₂ ⥤ D₂} {q₃ : H₃ ⥤ D₃} {q₄ : H₄ ⥤ D₄} {q₅ : H₅ ⥤ D₅}

/-- **Transport of a transition through componentwise comparisons.** Let `Lb`, `Rm`, `Rn`, `Lf`,
`Lsn`, `Lsm`, `Lx`, `Lam`, `Lan` be functors between the categories `D_i`, compared with functors
`b`, `rm`, … between categories `H_i` through localization-like functors `q_i`, and let `T`, `cn`,
`cm`, `β`, `θ` be transformations of the `L`-functors read upstairs as `τ`, `γn`, `γm`, `β₀`,
`θ₀`. If upstairs `sn τ ≫ γn = β₀ ≫ x γm ≫ θ₀`, then downstairs, after the comparison of `Lan`,
`Lsn T ≫ cn = β ≫ Lx cm ≫ θ` at every object `q₀ M`. -/
theorem transition_transport_comparison
    {Lb : D₀ ⥤ D₁} {Rm : D₁ ⥤ D₂} {Rn : D₁ ⥤ D₃} {Lf : D₂ ⥤ D₃} {Lsn : D₃ ⥤ D₅}
    {Lsm : D₂ ⥤ D₄} {Lx : D₄ ⥤ D₅} {Lam : D₀ ⥤ D₄} {Lan : D₀ ⥤ D₅}
    {b : H₀ ⥤ H₁} {rm : H₁ ⥤ H₂} {rn : H₁ ⥤ H₃} {f : H₂ ⥤ H₃} {sn : H₃ ⥤ H₅}
    {sm : H₂ ⥤ H₄} {x : H₄ ⥤ H₅} {am : H₀ ⥤ H₄} {an : H₀ ⥤ H₅}
    (αb : q₀ ⋙ Lb ⟶ b ⋙ q₁) (eRm : q₁ ⋙ Rm ⟶ rm ⋙ q₂) (eRn : q₁ ⋙ Rn ⟶ rn ⋙ q₃)
    (αf : q₂ ⋙ Lf ⟶ f ⋙ q₃) (αsn : q₃ ⋙ Lsn ⟶ sn ⋙ q₅) (αsm : q₂ ⋙ Lsm ⟶ sm ⋙ q₄)
    (αx : q₄ ⋙ Lx ⟶ x ⋙ q₅) (αam : q₀ ⋙ Lam ⟶ am ⋙ q₄) (αan : q₀ ⋙ Lan ⟶ an ⋙ q₅)
    (T : Rm ⋙ Lf ⟶ Rn) (τ : rm ⋙ f ⟶ rn)
    (cn : Lb ⋙ Rn ⋙ Lsn ⟶ Lan) (γn : ∀ M, sn.obj (rn.obj (b.obj M)) ⟶ an.obj M)
    (cm : Lb ⋙ Rm ⋙ Lsm ⟶ Lam) (γm : ∀ M, sm.obj (rm.obj (b.obj M)) ⟶ am.obj M)
    (β : Lf ⋙ Lsn ⟶ Lsm ⋙ Lx) (β₀ : f ⋙ sn ⟶ sm ⋙ x)
    (θ : Lam ⋙ Lx ⟶ Lan) (θ₀ : am ⋙ x ⟶ an)
    (hT : ∀ X, T.app (q₁.obj X) ≫ eRn.app X =
      Lf.map (eRm.app X) ≫ αf.app (rm.obj X) ≫ q₃.map (τ.app X))
    (hcn : ∀ M, cn.app (q₀.obj M) ≫ αan.app M =
      Lsn.map (Rn.map (αb.app M) ≫ eRn.app (b.obj M)) ≫ αsn.app (rn.obj (b.obj M)) ≫
        q₅.map (γn M))
    (hcm : ∀ M, cm.app (q₀.obj M) ≫ αam.app M =
      Lsm.map (Rm.map (αb.app M) ≫ eRm.app (b.obj M)) ≫ αsm.app (rm.obj (b.obj M)) ≫
        q₄.map (γm M))
    (hβ : ∀ N, β.app (q₂.obj N) ≫ Lx.map (αsm.app N) ≫ αx.app (sm.obj N) =
      Lsn.map (αf.app N) ≫ αsn.app (f.obj N) ≫ q₅.map (β₀.app N))
    (hθ : ∀ M, θ.app (q₀.obj M) ≫ αan.app M =
      Lx.map (αam.app M) ≫ αx.app (am.obj M) ≫ q₅.map (θ₀.app M))
    (hS : ∀ M, sn.map (τ.app (b.obj M)) ≫ γn M =
      β₀.app (rm.obj (b.obj M)) ≫ x.map (γm M) ≫ θ₀.app M)
    (M : H₀) :
    (Lsn.map (T.app (Lb.obj (q₀.obj M))) ≫ cn.app (q₀.obj M)) ≫ αan.app M =
      (β.app (Rm.obj (Lb.obj (q₀.obj M))) ≫ Lx.map (cm.app (q₀.obj M)) ≫
        θ.app (q₀.obj M)) ≫ αan.app M := by
  have hTn := T.naturality (αb.app M)
  have hβn := β.naturality (Rm.map (αb.app M) ≫ eRm.app (b.obj M))
  have hsn := αsn.naturality (τ.app (b.obj M))
  have hxn := αx.naturality (γm M)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hTn hβn hsn hxn
  simp only [Category.assoc]
  rw [hcn, hθ, ← Lx.map_comp_assoc, hcm, ← Lsn.map_comp_assoc, ← reassoc_of% hTn, hT]
  simp only [Functor.map_comp, Category.assoc] at hβn ⊢
  rw [reassoc_of% hsn, ← reassoc_of% hβn, reassoc_of% hxn, reassoc_of% (hβ (rm.obj (b.obj M))),
    ← Functor.map_comp, ← Functor.map_comp, hS]
  simp only [Functor.map_comp]

/-- Precomposing an identity. -/
theorem chase_one {C : Type*} [Category C] {A B E : C} (e₀ : A ⟶ A) (c : A ⟶ B) (d : B ⟶ E)
    (r : A ⟶ E) (h₀ : e₀ = 𝟙 A) (h : c ≫ d = r) : (e₀ ≫ c) ≫ d = r := by
  rw [h₀, Category.id_comp, h]

/-- **The comparison formula of a composite `Lb ⋙ (R ⋙ Ls) ≅ Lan` assembled from three squares.**
If `c = Lb σ⁻¹ ≫ Ld ε ≫ ν` with `σ : Le ⋙ Ld ≅ R ⋙ Ls`, `ε : Lb ⋙ Le ≅ La` and `ν : La ⋙ Ld ≅ Lan`
read upstairs as `σ₀`, `ε₀`, `ν₀`, then `c` is read upstairs as `b σ₀⁻¹ ≫ d ε₀ ≫ ν₀`. -/
theorem transport_comparison_three {H₀ : Type u₀} {H₁ : Type u₁} {H₂ : Type u₂} {H₃ : Type u₃}
    {H₄ : Type u₄} [Category.{v₀} H₀] [Category.{v₁} H₁] [Category.{v₂} H₂] [Category.{v₃} H₃]
    [Category.{v₄} H₄] {D₀ : Type t₀} {D₁ : Type t₁} {D₂ : Type t₂} {D₃ : Type t₃}
    {D₄ : Type t₄} [Category.{w₀} D₀] [Category.{w₁} D₁] [Category.{w₂} D₂] [Category.{w₃} D₃]
    [Category.{w₄} D₄] {q₀ : H₀ ⥤ D₀} {q₁ : H₁ ⥤ D₁} {q₂ : H₂ ⥤ D₂} {q₃ : H₃ ⥤ D₃}
    {q₄ : H₄ ⥤ D₄}
    {Lb : D₀ ⥤ D₁} {Le : D₁ ⥤ D₂} {La : D₀ ⥤ D₂} {Ld : D₂ ⥤ D₄} {R : D₁ ⥤ D₃}
    {Ls : D₃ ⥤ D₄} {Lan : D₀ ⥤ D₄}
    {b : H₀ ⥤ H₁} {e : H₁ ⥤ H₂} {a : H₀ ⥤ H₂} {d : H₂ ⥤ H₄} {r : H₁ ⥤ H₃}
    {s : H₃ ⥤ H₄} {an : H₀ ⥤ H₄}
    (αb : q₀ ⋙ Lb ⟶ b ⋙ q₁) (αe : q₁ ⋙ Le ⟶ e ⋙ q₂) (αa : q₀ ⋙ La ⟶ a ⋙ q₂)
    (αd : q₂ ⋙ Ld ⟶ d ⋙ q₄) (αR : q₁ ⋙ R ⟶ r ⋙ q₃) (αs : q₃ ⋙ Ls ⟶ s ⋙ q₄)
    (αan : q₀ ⋙ Lan ⟶ an ⋙ q₄)
    (σ : Le ⋙ Ld ≅ R ⋙ Ls) (σ₀ : e ⋙ d ≅ r ⋙ s) (ε : Lb ⋙ Le ≅ La) (ε₀ : b ⋙ e ⟶ a)
    (ν : La ⋙ Ld ≅ Lan) (ν₀ : a ⋙ d ⟶ an) (c : Lb ⋙ R ⋙ Ls ⟶ Lan)
    (hc : ∀ K, c.app K = σ.inv.app (Lb.obj K) ≫ 𝟙 _ ≫ Ld.map (ε.hom.app K) ≫ ν.hom.app K)
    (hσ : ∀ N, σ.hom.app (q₁.obj N) ≫ Ls.map (αR.app N) ≫ αs.app (r.obj N) =
      Ld.map (αe.app N) ≫ αd.app (e.obj N) ≫ q₄.map (σ₀.hom.app N))
    (hε : ∀ M, ε.hom.app (q₀.obj M) ≫ αa.app M =
      Le.map (αb.app M) ≫ αe.app (b.obj M) ≫ q₂.map (ε₀.app M))
    (hν : ∀ M, ν.hom.app (q₀.obj M) ≫ αan.app M =
      Ld.map (αa.app M) ≫ αd.app (a.obj M) ≫ q₄.map (ν₀.app M)) (M : H₀) :
    c.app (q₀.obj M) ≫ αan.app M =
      Ls.map (R.map (αb.app M) ≫ αR.app (b.obj M)) ≫ αs.app (r.obj (b.obj M)) ≫
        q₄.map (σ₀.inv.app (b.obj M) ≫ d.map (ε₀.app M) ≫ ν₀.app M) := by
  have hσi : ∀ N, σ.inv.app (q₁.obj N) ≫ Ld.map (αe.app N) ≫ αd.app (e.obj N) =
      Ls.map (αR.app N) ≫ αs.app (r.obj N) ≫ q₄.map (σ₀.inv.app N) := fun N ↦ by
    rw [← cancel_epi (σ.hom.app (q₁.obj N)), Iso.hom_inv_id_app_assoc, reassoc_of% (hσ N),
      ← Functor.map_comp, Iso.hom_inv_id_app]
    simp only [Functor.comp_obj, CategoryTheory.Functor.map_id, Category.comp_id]
  have hn := σ.inv.naturality (αb.app M)
  have hdn := αd.naturality (ε₀.app M)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn hdn
  rw [hc, Category.id_comp, Category.assoc, Category.assoc, hν, ← Ld.map_comp_assoc, hε]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hdn, ← reassoc_of% hn, reassoc_of% (hσi (b.obj M))]

/-- The chase behind the comparison formula of a square followed by the derived form of an
isomorphism with an exact functor. -/
theorem chase_square_exact {D : Type*} [Category D]
    {H : Type*} [Category H] {H' : Type*} [Category H'] {D' : Type*} [Category D']
    (F : D ⥤ D') (Q : H ⥤ D) (Q' : H' ⥤ D') (G : H ⥤ H')
    {P₀ P₁ : D} {R₀ R₁ : H} {Y₀ Y₀' Y₀'' Y₁ Y₂ : D'}
    (s₁ : Y₀ ⟶ Y₀') (s₂ : Y₀' ⟶ Y₀'') (s₃ : Y₀'' ⟶ F.obj P₀) (p : P₀ ⟶ P₁)
    (r : P₁ ⟶ Q.obj R₁) (ag : P₀ ⟶ Q.obj R₀) (mi : R₀ ⟶ R₁)
    (t : F.obj (Q.obj R₁) ⟶ Q'.obj (G.obj R₁))
    (t' : F.obj (Q.obj R₀) ⟶ Q'.obj (G.obj R₀)) (A : Y₀ ⟶ Y₁) (B : Y₁ ⟶ Y₂)
    (x : Y₂ ⟶ Q'.obj (G.obj R₀)) (hρ : p ≫ r = ag ≫ Q.map mi)
    (hnat : F.map (Q.map mi) ≫ t = t' ≫ Q'.map (G.map mi))
    (hsq : s₁ ≫ s₂ ≫ s₃ ≫ F.map ag ≫ t' = A ≫ B ≫ x) :
    (s₁ ≫ s₂ ≫ s₃ ≫ F.map p) ≫ F.map r ≫ t = A ≫ B ≫ (x ≫ Q'.map (G.map mi)) := by
  rw [Category.assoc, Category.assoc, Category.assoc, ← F.map_comp_assoc, hρ,
    F.map_comp_assoc, hnat, ← reassoc_of% hsq]


/-- Equality of morphisms from an equation sandwiched between two heterogeneous equalities. -/
private theorem eq_of_heq_of_eq_of_heq {α β : Sort u₀} {a d : α} {b c : β} (h₁ : HEq a b)
    (h₂ : b = c) (h₃ : HEq c d) : a = d :=
  eq_of_heq (h₁.trans (heq_of_eq h₂ |>.trans h₃))

end CategoryTheory

open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe u

-- no global `HasDerivedCategory` instance at this universe
attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})
  [∀ (m n : SimplexCategory) (φ : m ⟶ n),
    (Stacks.Cohomology.DerivedPushforward.pullbackOnHomotopy
      (S.transitionRingedToposHom O φ)).HasLeftDerivedFunctor
      (Stacks.Cohomology.DerivedPushforward.targetQuasiIso (S.componentRingedTopos O m))]

/-- **The derived transition of Stacks 0D9P on a complex.** At the image of a complex, the
derived transition followed by the comparison of the derived restriction is the comparison of the
derived restriction, then the comparison of `Lf_φ^*`, then the transition of complexes. -/
theorem derivedComponentModuleTransition_app_Qh {m n : SimplexCategory} (φ : m ⟶ n)
    (M : HomotopyCategory ((S.totalRingedTopos O).Modules) (ComplexShape.up ℤ)) :
    (S.derivedComponentModuleTransition O φ).app (DerivedCategory.Qh.obj M) ≫
        (S.componentModulesRestriction O n).mapDerivedCategoryFactorsh.hom.app M =
      (S.derivedTransitionPullback O φ).map
          ((S.componentModulesRestriction O m).mapDerivedCategoryFactorsh.hom.app M) ≫
        (S.derivedTransitionComparison O φ).app
          (((S.componentModulesRestriction O m).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
        DerivedCategory.Qh.map ((mapHomotopyCategoryTransition (ComplexShape.up ℤ)
          (S.componentModulesRestriction O m)
          (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules
          (S.componentModulesRestriction O n) (S.componentModulesTransition O φ)).app M) := by
  have h := liftedTransition_app_q (S.componentModulesRestriction O m).mapDerivedCategoryFactorsh
    (S.derivedTransitionComparison O φ)
    (S.componentModulesRestriction O n).mapDerivedCategoryFactorsh
    (mapHomotopyCategoryTransition (ComplexShape.up ℤ) (S.componentModulesRestriction O m)
      (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules
      (S.componentModulesRestriction O n) (S.componentModulesTransition O φ))
    (HomotopyCategory.quasiIso ((S.totalRingedTopos O).Modules) (ComplexShape.up ℤ)) M
  refine (congrArg (· ≫ (S.componentModulesRestriction O n).mapDerivedCategoryFactorsh.hom.app M)
    h).trans ?_
  simp only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id]

omit [∀ (m n : SimplexCategory) (φ : m ⟶ n),
    (Stacks.Cohomology.DerivedPushforward.pullbackOnHomotopy
      (S.transitionRingedToposHom O φ)).HasLeftDerivedFunctor
      (Stacks.Cohomology.DerivedPushforward.targetQuasiIso (S.componentRingedTopos O m))] in
/-- **The derived restriction to a component on a complex.** The isomorphism
`Lg_n^* ≅ D(g_n^{-1})`, followed by the comparison of the derived restriction, is the comparison
of `Lg_n^*` followed by the degreewise identification of `g_n^*` with restriction. -/
theorem derivedPullbackComponentIso_hom_app_Qh (n : SimplexCategory)
    (K : HomotopyCategory (S.totalRingedTopos O).Modules (ComplexShape.up ℤ)) :
    (S.derivedPullbackComponentIsoSimplicialSmallEtaleStrictDegree O n).hom.app
      (DerivedCategory.Qh.obj K) ≫
        (S.componentModulesRestriction O n).mapDerivedCategoryFactorsh.hom.app K =
      (derivedPullbackComparison (X := S.componentRingedTopos O n) (Y := S.totalRingedTopos O)
          (S.componentRingedToposHom O n)).app K ≫
        DerivedCategory.Qh.map ((Stacks.Homology.mapHomotopyCategoryIso
          (S.componentPullbackModulesRestrictionIso O n).symm (ComplexShape.up ℤ)).inv.app K) := by
  have h := Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso_hom_app_Qh _
    (S.componentModulesRestriction O n)
    (derivedPullback (X := S.componentRingedTopos O n) (Y := S.totalRingedTopos O)
      (S.componentRingedToposHom O n))
    (derivedPullbackComparison (X := S.componentRingedTopos O n) (Y := S.totalRingedTopos O)
      (S.componentRingedToposHom O n))
    (S.componentPullbackModulesRestrictionIso O n) K
  rw [← h]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app, Functor.comp_obj,
    CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

end CategoryTheory.SimplicialSiteSituation

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : SimplicialObject (AlgebraicSpaces B S hS)) {Z : AlgebraicSpaces B S hS}


/-- Pullback of modules from a strict component to a degree is additive. -/
instance pullbackModules_additive_spacesEtale_strictComponent (V : AlgebraicSpaces B S hS)
    (m : SimplexCategory)
    (f : RingedToposHom (spacesEtaleRingedTopos B S hS V)
      ((strictSituation X).componentRingedTopos (strictStructureSheaf X) m)) :
    f.toModulesHom.pullbackModules.Additive :=
  pullbackModules_additive (X := spacesEtaleRingedTopos B S hS V)
    (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) m) f

example (V : AlgebraicSpaces B S hS) :
    (inferInstance : HasDerivedCategory (spacesEtaleRingedTopos B S hS V).Modules) =
      HasDerivedCategory.standard _ := rfl

example (m : SimplexCategory) :
    (inferInstance : HasDerivedCategory
      ((strictSituation X).componentRingedTopos (strictStructureSheaf X) m).Modules) =
      HasDerivedCategory.standard _ := rfl

/-- Pullback of modules from the total site of `X` to a spaces-étale topos is additive. -/
instance pullbackModules_additive_ringedTopos_spacesEtale (V : AlgebraicSpaces B S hS)
    (f : RingedToposHom (ringedTopos X) (spacesEtaleRingedTopos B S hS V)) :
    f.toModulesHom.pullbackModules.Additive :=
  pullbackModules_additive (X := ringedTopos X) (Y := spacesEtaleRingedTopos B S hS V) f

/-- Pullback of modules between spaces-étale topoi is additive. -/
instance pullbackModules_additive_spacesEtale_spacesEtale (V W : AlgebraicSpaces B S hS)
    (f : RingedToposHom (spacesEtaleRingedTopos B S hS V) (spacesEtaleRingedTopos B S hS W)) :
    f.toModulesHom.pullbackModules.Additive :=
  pullbackModules_additive (X := spacesEtaleRingedTopos B S hS V)
    (Y := spacesEtaleRingedTopos B S hS W) f

/-- Pullback of modules from the strict total site to a degree is additive. -/
instance pullbackModules_additive_spacesEtale_strictRingedTopos (V : AlgebraicSpaces B S hS)
    (f : RingedToposHom (spacesEtaleRingedTopos B S hS V) (strictRingedTopos X)) :
    f.toModulesHom.pullbackModules.Additive :=
  pullbackModules_additive (X := spacesEtaleRingedTopos B S hS V) (Y := strictRingedTopos X) f

/-- **The derived square of the strict transitions on a complex.** -/
theorem strictComponentDerivedTransitionIso_hom_app_Qh {m n : SimplexCategory} (φ : m ⟶ n)
    (N : HomotopyCategory
      ((strictSituation X).componentRingedTopos (strictStructureSheaf X) m).Modules
      (ComplexShape.up ℤ)) :
    (strictComponentDerivedTransitionIso X φ).hom.app (DerivedCategory.Qh.obj N) ≫
        (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
          (Y := spacesEtaleRingedTopos B S hS (X.obj (op m)))
          (spacesEtaleRingedToposHom (X.map φ.op))).map
          ((derivedPullbackComparison (strictComponentRingedToposHom X m)).app N) ≫
        (derivedPullbackComparison (spacesEtaleRingedToposHom (X.map φ.op))).app
          ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
            (strictComponentRingedToposHom X m)).obj N) =
      (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
          (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
          (strictComponentRingedToposHom X n)).map
          (((strictSituation X).derivedTransitionComparison (strictStructureSheaf X) φ).app N) ≫
        (derivedPullbackComparison (strictComponentRingedToposHom X n)).app
          ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
            ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ)).obj N) ≫
        DerivedCategory.Qh.map ((pullbackMapHomotopySquareIso (strictComponentRingedToposHom X n)
          ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ)
          (spacesEtaleRingedToposHom (X.map φ.op)) (strictComponentRingedToposHom X m)
          (strictComponentPullbackModulesTransitionIso X φ)).hom.app N) := by
  have := hasLeftDerivedFunctor_pullbackOnHomotopy
    (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
        (Z := (strictSituation X).componentRingedTopos (strictStructureSheaf X) m)
        ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ)
        (strictComponentRingedToposHom X n))
  have := hasLeftDerivedFunctor_pullbackOnHomotopy
    (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := spacesEtaleRingedTopos B S hS (X.obj (op m)))
        (Z := (strictSituation X).componentRingedTopos (strictStructureSheaf X) m)
        (strictComponentRingedToposHom X m) (spacesEtaleRingedToposHom (X.map φ.op)))
  have h := derivedPullbackSquareIso_hom_app_comparison (strictComponentRingedToposHom X n)
    ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ)
    (spacesEtaleRingedToposHom (X.map φ.op)) (strictComponentRingedToposHom X m)
    (strictComponentPullbackModulesTransitionIso X φ) N
  have hdef : (strictComponentDerivedTransitionIso X φ).hom.app (DerivedCategory.Qh.obj N) =
      (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
          (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
          (strictComponentRingedToposHom X n)).map (𝟙 _) ≫
        (derivedPullbackCompIso (strictComponentRingedToposHom X n)
          ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ) ≪≫
        derivedPullbackIsoOfPullbackModulesIso
          (φ := RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
            (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
            (Z := (strictSituation X).componentRingedTopos (strictStructureSheaf X) m)
            ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ)
            (strictComponentRingedToposHom X n))
          (ψ := RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
            (Y := spacesEtaleRingedTopos B S hS (X.obj (op m)))
            (Z := (strictSituation X).componentRingedTopos (strictStructureSheaf X) m)
            (strictComponentRingedToposHom X m) (spacesEtaleRingedToposHom (X.map φ.op)))
          (strictComponentPullbackModulesTransitionIso X φ) ≪≫
        (derivedPullbackCompIso (spacesEtaleRingedToposHom (X.map φ.op))
          (strictComponentRingedToposHom X m)).symm).hom.app (DerivedCategory.Qh.obj N) := rfl
  exact (eq_whisker hdef _).trans
    (CategoryTheory.chase_one _ _ _ _ ((derivedPullback
      (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
      (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
      (strictComponentRingedToposHom X n)).map_id _) h)

/-- **The comparison of `Le^* ⋙ Ld_n^* ≅ D(g_n^{-1}) ⋙ L realize_n^*` on a complex.** -/
theorem strictDegreeDerivedIso_hom_app_Qh (n : SimplexCategory)
    (N : HomotopyCategory (strictRingedTopos X).Modules (ComplexShape.up ℤ)) :
    (strictDegreeDerivedIso X n).hom.app (DerivedCategory.Qh.obj N) ≫
        (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
          (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
          (strictComponentRingedToposHom X n)).map
          (((strictSituation X).componentModulesRestriction (strictStructureSheaf X)
            n).mapDerivedCategoryFactorsh.hom.app N) ≫
        (derivedPullbackComparison (strictComponentRingedToposHom X n)).app
          ((((strictSituation X).componentModulesRestriction (strictStructureSheaf X)
            n).mapHomotopyCategory (ComplexShape.up ℤ)).obj N) =
      (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
          (Y := ringedTopos X) (degreeRingedToposHom X n)).map
          ((derivedPullbackComparison (strictRingedToposHom X)).app N) ≫
        (derivedPullbackComparison (degreeRingedToposHom X n)).app
          ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
            (strictRingedToposHom X)).obj N) ≫
        (DerivedCategory.Qh.map ((pullbackMapHomotopySquareIso (degreeRingedToposHom X n)
            (strictRingedToposHom X) (strictComponentRingedToposHom X n)
            ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) n)
            (strictDegreeTwoIso X n).pullbackModulesIso).hom.app N) ≫
          DerivedCategory.Qh.map ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
              (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
              (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
              (strictComponentRingedToposHom X n)).map
            ((Stacks.Homology.mapHomotopyCategoryIso
              ((strictSituation X).componentPullbackModulesRestrictionIso (strictStructureSheaf X)
                n).symm (ComplexShape.up ℤ)).inv.app N))) := by
  have := hasLeftDerivedFunctor_pullbackOnHomotopy
    (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := ringedTopos X) (Z := strictRingedTopos X)
        (strictRingedToposHom X) (degreeRingedToposHom X n))
  have := hasLeftDerivedFunctor_pullbackOnHomotopy
    (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
        (Z := strictRingedTopos X)
        ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) n)
        (strictComponentRingedToposHom X n))
  have hdef : (strictDegreeDerivedIso X n).hom.app (DerivedCategory.Qh.obj N) =
      (derivedPullbackCompIso (degreeRingedToposHom X n) (strictRingedToposHom X)).hom.app
          (DerivedCategory.Qh.obj N) ≫
        (derivedPullbackIsoOfPullbackModulesIso
          (φ := RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
            (Y := ringedTopos X) (Z := strictRingedTopos X)
            (strictRingedToposHom X) (degreeRingedToposHom X n))
          (ψ := RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
            (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
            (Z := strictRingedTopos X)
            ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) n)
            (strictComponentRingedToposHom X n))
          (strictDegreeTwoIso X n).pullbackModulesIso).hom.app (DerivedCategory.Qh.obj N) ≫
        (derivedPullbackCompIso (strictComponentRingedToposHom X n)
          ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) n)).inv.app
          (DerivedCategory.Qh.obj N) ≫
        (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
          (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
          (strictComponentRingedToposHom X n)).map
          (((strictSituation X).derivedPullbackComponentIsoSimplicialSmallEtaleStrictDegree
            (strictStructureSheaf X) n).hom.app
            (DerivedCategory.Qh.obj N)) := rfl
  have hsq := derivedPullbackSquareIso_hom_app_comparison (degreeRingedToposHom X n)
    (strictRingedToposHom X) (strictComponentRingedToposHom X n)
    ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) n)
    (strictDegreeTwoIso X n).pullbackModulesIso N
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc] at hsq
  have hρ := (strictSituation X).derivedPullbackComponentIso_hom_app_Qh (strictStructureSheaf X) n N
  have hnat := (derivedPullbackComparison (strictComponentRingedToposHom X n)).naturality
    ((Stacks.Homology.mapHomotopyCategoryIso
      ((strictSituation X).componentPullbackModulesRestrictionIso (strictStructureSheaf X) n).symm
      (ComplexShape.up ℤ)).inv.app N)
  exact (eq_whisker hdef _).trans (CategoryTheory.chase_square_exact
    (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
      (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
      (strictComponentRingedToposHom X n))
    DerivedCategory.Qh DerivedCategory.Qh
    (Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
      (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
      (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
      (strictComponentRingedToposHom X n)) _ _ _ _ _ _ _ _ _ _ _ _ hρ hnat hsq)

/-- `strictDegreeDerivedIso_hom_app_Qh` with the degreewise factor written as one isomorphism. -/
theorem strictDegreeDerivedIso_hom_app_Qh' (n : SimplexCategory)
    (N : HomotopyCategory (strictRingedTopos X).Modules (ComplexShape.up ℤ)) :
    (strictDegreeDerivedIso X n).hom.app (DerivedCategory.Qh.obj N) ≫
        (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
          (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
          (strictComponentRingedToposHom X n)).map
          (((strictSituation X).componentModulesRestriction (strictStructureSheaf X)
            n).mapDerivedCategoryFactorsh.hom.app N) ≫
        (derivedPullbackComparison (strictComponentRingedToposHom X n)).app
          ((((strictSituation X).componentModulesRestriction (strictStructureSheaf X)
            n).mapHomotopyCategory (ComplexShape.up ℤ)).obj N) =
      (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
          (Y := ringedTopos X) (degreeRingedToposHom X n)).map
          ((derivedPullbackComparison (strictRingedToposHom X)).app N) ≫
        (derivedPullbackComparison (degreeRingedToposHom X n)).app
          ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
            (strictRingedToposHom X)).obj N) ≫
        DerivedCategory.Qh.map ((pullbackMapHomotopySquareIso (degreeRingedToposHom X n)
            (strictRingedToposHom X) (strictComponentRingedToposHom X n)
            ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) n)
            (strictDegreeTwoIso X n).pullbackModulesIso ≪≫
          Functor.isoWhiskerRight (Stacks.Homology.mapHomotopyCategoryIso
            ((strictSituation X).componentPullbackModulesRestrictionIso (strictStructureSheaf X)
              n).symm (ComplexShape.up ℤ)).symm
            (Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
              (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
              (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
              (strictComponentRingedToposHom X n))).hom.app N) :=
  (strictDegreeDerivedIso_hom_app_Qh X n N).trans
    (whisker_eq _ (whisker_eq _ (DerivedCategory.Qh.map_comp _ _).symm))

section Augmentation

variable {X} (a : X ⟶ (Functor.const _).obj Z)

/-- The homotopy-level form of `strictAugmentationDegreeDerivedIso a n`: the composite of
degreewise compositors and degreewise 2-isomorphisms underlying it. -/
abbrev strictAugmentationDegreeHomotopyHom (n : SimplexCategory) :=
  ((pullbackMapHomotopySquareIso (degreeRingedToposHom X n)
      (strictRingedToposHom X) (strictComponentRingedToposHom X n)
      ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) n)
      (strictDegreeTwoIso X n).pullbackModulesIso ≪≫
    Functor.isoWhiskerRight (Stacks.Homology.mapHomotopyCategoryIso
      ((strictSituation X).componentPullbackModulesRestrictionIso (strictStructureSheaf X)
        n).symm (ComplexShape.up ℤ)).symm
      (Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
        (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
        (strictComponentRingedToposHom X n))).inv)

/-- The derived pullback along `a ∘ d_n` exists. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_augmentation_comp_degree (n : SimplexCategory) :
    (pullbackOnHomotopy (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
      (Y := ringedTopos X) (Z := spacesEtaleRingedTopos B S hS Z)
      (augmentationRingedToposHom a) (degreeRingedToposHom X n))).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := spacesEtaleRingedTopos B S hS Z)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy
    (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
      (Y := ringedTopos X) (Z := spacesEtaleRingedTopos B S hS Z)
      (augmentationRingedToposHom a) (degreeRingedToposHom X n))

/-- The derived pullback along `b ∘ e` exists. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_strictAugmentation_comp :
    (pullbackOnHomotopy (RingedToposHom.comp (X := ringedTopos X) (Y := strictRingedTopos X)
      (Z := spacesEtaleRingedTopos B S hS Z) (strictAugmentationRingedToposHom a)
      (strictRingedToposHom X))).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := spacesEtaleRingedTopos B S hS Z)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy
    (RingedToposHom.comp (X := ringedTopos X) (Y := strictRingedTopos X)
      (Z := spacesEtaleRingedTopos B S hS Z) (strictAugmentationRingedToposHom a)
      (strictRingedToposHom X))

/-- The comparison formula of `La^* ⋙ Ld_n^* ≅ La_n^*` on a complex. -/
theorem augmentationDegreeDerivedIso_hom_app_Qh (n : SimplexCategory)
    (M : HomotopyCategory (spacesEtaleRingedTopos B S hS Z).Modules (ComplexShape.up ℤ)) :
    (derivedPullbackCompIso (degreeRingedToposHom X n) (augmentationRingedToposHom a) ≪≫
      derivedPullbackIsoOfPullbackModulesIso
        (φ := RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
          (Y := ringedTopos X) (Z := spacesEtaleRingedTopos B S hS Z)
          (augmentationRingedToposHom a) (degreeRingedToposHom X n))
        (ψ := spacesEtaleRingedToposHom (a.app (op n)))
        (augmentationDegreeTwoIso a n).pullbackModulesIso).hom.app (DerivedCategory.Qh.obj M) ≫
      (derivedPullbackComparison (spacesEtaleRingedToposHom (a.app (op n)))).app M =
    (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
          (Y := ringedTopos X) (degreeRingedToposHom X n)).map
        ((derivedPullbackComparison (augmentationRingedToposHom a)).app M) ≫
      (derivedPullbackComparison (degreeRingedToposHom X n)).app
        ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
          (augmentationRingedToposHom a)).obj M) ≫
      DerivedCategory.Qh.map ((pullbackMapHomotopyCompIso (degreeRingedToposHom X n)
        (augmentationRingedToposHom a) ≪≫
      Stacks.Homology.mapHomotopyCategoryIso (augmentationDegreeTwoIso a n).pullbackModulesIso
        (ComplexShape.up ℤ)).hom.app M) :=
  (Category.assoc _ _ _).trans
    (derivedPullbackCompComparison_app_comp_isoOfPullbackModulesIso_comparison_app
      (degreeRingedToposHom X n) (augmentationRingedToposHom a)
      (h := spacesEtaleRingedToposHom (a.app (op n)))
      (augmentationDegreeTwoIso a n).pullbackModulesIso M)

/-- **The component isomorphism on a complex.** `Lb^* ⋙ D(g_n^{-1}) ⋙ L realize_n^* ≅ La_n^*`,
followed by the comparison of `La_n^*`, is the composite comparison followed by the degreewise
isomorphism. -/
theorem strictAugmentationDegreeDerivedIso_hom_app_Qh (n : SimplexCategory)
    (M : HomotopyCategory (spacesEtaleRingedTopos B S hS Z).Modules (ComplexShape.up ℤ)) :
    (strictAugmentationDegreeDerivedIso a n).hom.app (DerivedCategory.Qh.obj M) ≫
        (derivedPullbackComparison (spacesEtaleRingedToposHom (a.app (op n)))).app M =
      (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
          (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
          (strictComponentRingedToposHom X n)).map
          (((strictSituation X).derivedComponentModuleRestriction (strictStructureSheaf X) n).map
            ((derivedPullbackComparison (strictAugmentationRingedToposHom a)).app M) ≫
          ((strictSituation X).componentModulesRestriction (strictStructureSheaf X)
            n).mapDerivedCategoryFactorsh.hom.app
            ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
              (strictAugmentationRingedToposHom a)).obj M)) ≫
        (derivedPullbackComparison (strictComponentRingedToposHom X n)).app
          ((((strictSituation X).componentModulesRestriction (strictStructureSheaf X)
            n).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
              (strictAugmentationRingedToposHom a)).obj M)) ≫
        DerivedCategory.Qh.map
          ((strictAugmentationDegreeHomotopyHom n).app
              ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
                (strictAugmentationRingedToposHom a)).obj M) ≫
            (Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
              (degreeRingedToposHom X n)).map
              ((pullbackMapHomotopyCompIso (strictRingedToposHom X)
                (strictAugmentationRingedToposHom a) ≪≫
                Stacks.Homology.mapHomotopyCategoryIso
                  (strictAugmentationTwoIso a).pullbackModulesIso
                  (ComplexShape.up ℤ)).hom.app M) ≫
            (pullbackMapHomotopyCompIso (degreeRingedToposHom X n)
                (augmentationRingedToposHom a) ≪≫
              Stacks.Homology.mapHomotopyCategoryIso
                (augmentationDegreeTwoIso a n).pullbackModulesIso
                (ComplexShape.up ℤ)).hom.app M) := by
  have KEY := CategoryTheory.transport_comparison_three
    (derivedPullbackComparison (strictAugmentationRingedToposHom a))
    (derivedPullbackComparison (strictRingedToposHom X))
    (derivedPullbackComparison (augmentationRingedToposHom a))
    (derivedPullbackComparison (degreeRingedToposHom X n))
    ((strictSituation X).componentModulesRestriction (strictStructureSheaf X)
      n).mapDerivedCategoryFactorsh.hom
    (derivedPullbackComparison (strictComponentRingedToposHom X n))
    (derivedPullbackComparison (spacesEtaleRingedToposHom (a.app (op n))))
    (strictDegreeDerivedIso X n)
    (pullbackMapHomotopySquareIso (degreeRingedToposHom X n)
      (strictRingedToposHom X) (strictComponentRingedToposHom X n)
      ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) n)
      (strictDegreeTwoIso X n).pullbackModulesIso ≪≫
    Functor.isoWhiskerRight (Stacks.Homology.mapHomotopyCategoryIso
      ((strictSituation X).componentPullbackModulesRestrictionIso (strictStructureSheaf X)
        n).symm (ComplexShape.up ℤ)).symm
      (Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
        (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
        (strictComponentRingedToposHom X n)))
    (derivedPullbackCompIso (strictRingedToposHom X) (strictAugmentationRingedToposHom a) ≪≫
        derivedPullbackIsoOfPullbackModulesIso
          (φ := RingedToposHom.comp (X := ringedTopos X) (Y := strictRingedTopos X)
            (Z := spacesEtaleRingedTopos B S hS Z) (strictAugmentationRingedToposHom a)
            (strictRingedToposHom X))
          (ψ := augmentationRingedToposHom a)
          (strictAugmentationTwoIso a).pullbackModulesIso)
    (pullbackMapHomotopyCompIso (strictRingedToposHom X)
      (strictAugmentationRingedToposHom a) ≪≫
      Stacks.Homology.mapHomotopyCategoryIso (strictAugmentationTwoIso a).pullbackModulesIso
        (ComplexShape.up ℤ)).hom
    (derivedPullbackCompIso (degreeRingedToposHom X n) (augmentationRingedToposHom a) ≪≫
      derivedPullbackIsoOfPullbackModulesIso
        (φ := RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
          (Y := ringedTopos X) (Z := spacesEtaleRingedTopos B S hS Z)
          (augmentationRingedToposHom a) (degreeRingedToposHom X n))
        (ψ := spacesEtaleRingedToposHom (a.app (op n)))
        (augmentationDegreeTwoIso a n).pullbackModulesIso)
    (pullbackMapHomotopyCompIso (degreeRingedToposHom X n)
        (augmentationRingedToposHom a) ≪≫
      Stacks.Homology.mapHomotopyCategoryIso (augmentationDegreeTwoIso a n).pullbackModulesIso
        (ComplexShape.up ℤ)).hom
    (strictAugmentationDegreeDerivedIso a n).hom (fun _ ↦ rfl)
    (fun N ↦ eq_of_heq_of_eq_of_heq (by heq_congr) (strictDegreeDerivedIso_hom_app_Qh' X n N)
      (by heq_congr))
    (fun M ↦ (Category.assoc _ _ _).trans
      (derivedPullbackCompComparison_app_comp_isoOfPullbackModulesIso_comparison_app
        (strictRingedToposHom X) (strictAugmentationRingedToposHom a)
        (h := augmentationRingedToposHom a) (strictAugmentationTwoIso a).pullbackModulesIso M))
    (augmentationDegreeDerivedIso_hom_app_Qh a n) M
  exact eq_of_heq_of_eq_of_heq (by heq_congr) KEY (by heq_congr)

/-- The simplicial identity `X(φ) ≫ a_m = a_n` of an augmentation. -/
theorem augmentation_map_comp_app {m n : SimplexCategory} (φ : m ⟶ n) :
    X.map φ.op ≫ a.app (op m) = a.app (op n) :=
  (a.naturality φ.op).trans (Category.comp_id _)

/-- **The augmentation commutes with the transitions** as morphisms of ringed topoi:
`a_m ∘ X(φ) ≅ a_n`, the composition 2-isomorphism of the spaces-étale topoi followed by the
simplicial identity `X(φ) ≫ a_m = a_n`. -/
def augmentationTransitionTwoIso {m n : SimplexCategory} (φ : m ⟶ n) :
    TwoIso (A := spacesEtaleRingedTopos B S hS (X.obj (op n)))
      (B := spacesEtaleRingedTopos B S hS Z)
      (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := spacesEtaleRingedTopos B S hS (X.obj (op m))) (Z := spacesEtaleRingedTopos B S hS Z)
        (spacesEtaleRingedToposHom (a.app (op m))) (spacesEtaleRingedToposHom (X.map φ.op)))
      (spacesEtaleRingedToposHom (a.app (op n))) :=
  (spacesEtaleRingedToposHomCompTwoIsoSpacesEtaleRingedToposHomComp (X.map φ.op)
      (a.app (op m))).symm.trans
    (TwoIso.ofEq (A := spacesEtaleRingedTopos B S hS (X.obj (op n)))
      (B := spacesEtaleRingedTopos B S hS Z)
      (congrArg (spacesEtaleRingedToposHom (Z₁ := X.obj (op n)) (Z₂ := Z))
        (augmentation_map_comp_app a φ)))

/-- The derived pullback along `a_m ∘ X(φ)` exists. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_augmentation_comp_transition
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (pullbackOnHomotopy (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := spacesEtaleRingedTopos B S hS (X.obj (op m))) (Z := spacesEtaleRingedTopos B S hS Z)
        (spacesEtaleRingedToposHom (a.app (op m)))
        (spacesEtaleRingedToposHom (X.map φ.op)))).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := spacesEtaleRingedTopos B S hS Z)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy
    (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := spacesEtaleRingedTopos B S hS (X.obj (op m))) (Z := spacesEtaleRingedTopos B S hS Z)
        (spacesEtaleRingedToposHom (a.app (op m))) (spacesEtaleRingedToposHom (X.map φ.op)))

/-- **The derived pullbacks of an augmentation commute with the transitions**:
`La_m^* ⋙ LX(φ)^* ≅ La_n^*` (Stacks 0D6D and `X(φ) ≫ a_m = a_n`). -/
def augmentationTransitionDerivedIso {m n : SimplexCategory} (φ : m ⟶ n) :
    derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op m)))
        (Y := spacesEtaleRingedTopos B S hS Z) (spacesEtaleRingedToposHom (a.app (op m))) ⋙
      derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := spacesEtaleRingedTopos B S hS (X.obj (op m)))
        (spacesEtaleRingedToposHom (X.map φ.op)) ≅
      derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := spacesEtaleRingedTopos B S hS Z) (spacesEtaleRingedToposHom (a.app (op n))) :=
  derivedPullbackCompIso (spacesEtaleRingedToposHom (X.map φ.op))
      (spacesEtaleRingedToposHom (a.app (op m))) ≪≫
    derivedPullbackIsoOfPullbackModulesIso
      (φ := RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := spacesEtaleRingedTopos B S hS (X.obj (op m))) (Z := spacesEtaleRingedTopos B S hS Z)
        (spacesEtaleRingedToposHom (a.app (op m))) (spacesEtaleRingedToposHom (X.map φ.op)))
      (ψ := spacesEtaleRingedToposHom (a.app (op n)))
      (augmentationTransitionTwoIso a φ).pullbackModulesIso

/-- The comparison formula of `augmentationTransitionDerivedIso` on a complex. -/
theorem augmentationTransitionDerivedIso_hom_app_Qh {m n : SimplexCategory} (φ : m ⟶ n)
    (M : HomotopyCategory (spacesEtaleRingedTopos B S hS Z).Modules (ComplexShape.up ℤ)) :
    (augmentationTransitionDerivedIso a φ).hom.app (DerivedCategory.Qh.obj M) ≫
        (derivedPullbackComparison (spacesEtaleRingedToposHom (a.app (op n)))).app M =
      (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
          (Y := spacesEtaleRingedTopos B S hS (X.obj (op m)))
          (spacesEtaleRingedToposHom (X.map φ.op))).map
          ((derivedPullbackComparison (spacesEtaleRingedToposHom (a.app (op m)))).app M) ≫
        (derivedPullbackComparison (spacesEtaleRingedToposHom (X.map φ.op))).app
          ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
            (spacesEtaleRingedToposHom (a.app (op m)))).obj M) ≫
        DerivedCategory.Qh.map ((pullbackMapHomotopyCompIso (spacesEtaleRingedToposHom (X.map φ.op))
            (spacesEtaleRingedToposHom (a.app (op m))) ≪≫
          Stacks.Homology.mapHomotopyCategoryIso
            (augmentationTransitionTwoIso a φ).pullbackModulesIso
            (ComplexShape.up ℤ)).hom.app M) := by
  have hdef : (augmentationTransitionDerivedIso a φ).hom.app (DerivedCategory.Qh.obj M) =
      (derivedPullbackCompComparison (spacesEtaleRingedToposHom (X.map φ.op))
          (spacesEtaleRingedToposHom (a.app (op m)))).app (DerivedCategory.Qh.obj M) ≫
        (derivedPullbackIsoOfPullbackModulesIso
          (φ := RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
            (Y := spacesEtaleRingedTopos B S hS (X.obj (op m)))
            (Z := spacesEtaleRingedTopos B S hS Z)
            (spacesEtaleRingedToposHom (a.app (op m))) (spacesEtaleRingedToposHom (X.map φ.op)))
          (ψ := spacesEtaleRingedToposHom (a.app (op n)))
          (augmentationTransitionTwoIso a φ).pullbackModulesIso).hom.app
          (DerivedCategory.Qh.obj M) := rfl
  have KEY := derivedPullbackCompComparison_app_comp_isoOfPullbackModulesIso_comparison_app
      (spacesEtaleRingedToposHom (X.map φ.op)) (spacesEtaleRingedToposHom (a.app (op m)))
      (h := spacesEtaleRingedToposHom (a.app (op n)))
      (augmentationTransitionTwoIso a φ).pullbackModulesIso M
  refine (eq_whisker hdef _).trans ((Category.assoc _ _ _).trans ?_)
  exact eq_of_heq_of_eq_of_heq (by heq_congr) KEY (by heq_congr)

/-- The degreewise map `b^* g_n^* realize_n^* ⟶ a_n^*` underlying
`strictAugmentationDegreeDerivedIso a n`, at a complex. -/
abbrev strictAugmentationDegreeHomotopyComp (n : SimplexCategory)
    (M : HomotopyCategory (spacesEtaleRingedTopos B S hS Z).Modules (ComplexShape.up ℤ)) :
    (Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
        (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
        (strictComponentRingedToposHom X n)).obj
        ((((strictSituation X).componentModulesRestriction (strictStructureSheaf X)
        n).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
          (X := strictRingedTopos X) (Y := spacesEtaleRingedTopos B S hS Z)
          (strictAugmentationRingedToposHom a)).obj M)) ⟶
      (Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
        (X := spacesEtaleRingedTopos B S hS (X.obj (op n))) (Y := spacesEtaleRingedTopos B S hS Z)
        (spacesEtaleRingedToposHom (a.app (op n)))).obj M :=
  (strictAugmentationDegreeHomotopyHom n).app
      ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
        (X := strictRingedTopos X) (Y := spacesEtaleRingedTopos B S hS Z)
        (strictAugmentationRingedToposHom a)).obj M) ≫
    (Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
      (X := spacesEtaleRingedTopos B S hS (X.obj (op n))) (Y := ringedTopos X)
      (degreeRingedToposHom X n)).map
      ((pullbackMapHomotopyCompIso (strictRingedToposHom X)
        (strictAugmentationRingedToposHom a) ≪≫
        Stacks.Homology.mapHomotopyCategoryIso (strictAugmentationTwoIso a).pullbackModulesIso
          (ComplexShape.up ℤ)).hom.app M) ≫
    (pullbackMapHomotopyCompIso (degreeRingedToposHom X n)
        (augmentationRingedToposHom a) ≪≫
      Stacks.Homology.mapHomotopyCategoryIso (augmentationDegreeTwoIso a n).pullbackModulesIso
        (ComplexShape.up ℤ)).hom.app M

end Augmentation

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite
