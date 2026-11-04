module

public import StacksFrontier.Topology.Sheaves.Cohomology.GlueingComplexes.Pullback

/-!
# A coherence of comparison isomorphisms over a cube of morphisms of ringed spaces

Given morphisms of ringed spaces `pW : W' ⟶ W`, `tC : W ⟶ Wᵢ`, `iU : W ⟶ U`, `tA : U ⟶ Uᵢ`,
`iUᵢ : Wᵢ ⟶ Uᵢ`, `iU' : W' ⟶ U'`, `pU : U' ⟶ U` and composites `pCᵢ = pW ≫ tC`,
`pAᵢ = pU ≫ tA` forming commutative squares, the comparison isomorphisms of derived pullback
attached to the two ways of going from `W'` to `Uᵢ` agree. This is the associativity of the
composition isomorphisms of Tag 0D5S, applied three times.

## Main results

* `Stacks.Cohomology.GlueingComplexes.cube_path_coherence`: the coherence.
* `Stacks.Cohomology.GlueingComplexes.inv_comp_inv_comp_inv_comp_inv`: inverting a composite of
  four isomorphisms.

## References

* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.DerivedPullback (factorIso factorIso_assoc)

universe u

namespace Stacks.Cohomology.GlueingComplexes

attribute [local instance] HasDerivedCategory.standard

section Coherence

variable {W' W Wi U' U Ui : RingedSpace.{u, u}} (pW : W' ⟶ W) (tC : W ⟶ Wi) (pCi : W' ⟶ Wi)
  (iU : W ⟶ U) (tA : U ⟶ Ui) (iUi : Wi ⟶ Ui) (iU' : W' ⟶ U') (pU : U' ⟶ U) (pAi : U' ⟶ Ui)
  (e1 : pW ≫ tC = pCi) (e2 : pU ≫ tA = pAi) (e3 : iU ≫ tA = tC ≫ iUi)
  (e4 : pW ≫ iU = iU' ≫ pU) (e5 : pCi ≫ iUi = iU' ≫ pAi) (M : DerivedModules Ui)

/-- The square comparison followed by the comparison of its second path is the comparison of
its first path. -/
private theorem squareIso_hom_app_comp_factorIso :
    (derivedRestrictSquareIso pCi iUi iU' pAi e5).hom.app M ≫
        (factorIso iU' pAi (pCi ≫ iUi) e5.symm).hom.app M =
      (factorIso pCi iUi (pCi ≫ iUi) rfl).hom.app M := by
  simp only [derivedRestrictSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- **The comparison isomorphisms of the two paths from `W'` to `Uᵢ` agree.** -/
theorem cube_path_coherence :
    (derivedRestrictSquareIso pW iU iU' pU e4).inv.app ((derivedRestrict tA).obj M) ≫
        (derivedRestrict pW).map ((derivedRestrictSquareIso iU tA tC iUi e3).hom.app M) ≫
        (factorIso pW tC pCi e1).hom.app ((derivedRestrict iUi).obj M) ≫
        (derivedRestrictSquareIso pCi iUi iU' pAi e5).hom.app M =
      (derivedRestrict iU').map ((factorIso pU tA pAi e2).hom.app M) := by
  have hκ : pW ≫ (tC ≫ iUi) = pCi ≫ iUi := by rw [← Category.assoc, e1]
  have hκ' : (pW ≫ iU) ≫ tA = pCi ≫ iUi := by rw [Category.assoc, e3, ← Category.assoc, e1]
  have s₁ := squareIso_hom_app_comp_factorIso pCi iUi iU' pAi e5 M
  have s₂ := pathIsoInner_eq_pathIsoOuter pW tC iUi (tC ≫ iUi) rfl pCi e1 (pCi ≫ iUi) hκ rfl M
  have s₃ := derivedRestrict_map_squareIso_comp_pathIsoInner pW iU tA tC iUi e3 (tC ≫ iUi) e3
    rfl (pCi ≫ iUi) hκ M
  have s₄ := pathIsoInner_eq_pathIsoOuter pW iU tA (tC ≫ iUi) e3 (pW ≫ iU) rfl (pCi ≫ iUi) hκ
    hκ' M
  have s₅ := squareIso_inv_app_comp_pathIsoOuter pW iU iU' pU tA e4 (pW ≫ iU) rfl e4.symm
    (pCi ≫ iUi) hκ' M
  have s₆ := pathIsoInner_eq_pathIsoOuter iU' pU tA pAi e2 (pW ≫ iU) e4.symm (pCi ≫ iUi)
    e5.symm hκ' M
  rw [← cancel_mono ((factorIso iU' pAi (pCi ≫ iUi) e5.symm).hom.app M)]
  simp only [Category.assoc, s₁]
  have t₂ : (factorIso pW tC pCi e1).hom.app ((derivedRestrict iUi).obj M) ≫
      (factorIso pCi iUi (pCi ≫ iUi) rfl).hom.app M =
        (pathIsoInner pW tC iUi (tC ≫ iUi) rfl (pCi ≫ iUi) hκ M).hom := by
    rw [s₂]; rfl
  rw [t₂, s₃, s₄, s₅, ← s₆]
  rfl

end Coherence

/-- Inverting a composite of four isomorphisms. -/
theorem inv_comp_inv_comp_inv_comp_inv {C : Type*} [Category* C] {P₀ P₁ P₂ P₃ P₄ : C}
    (a : P₀ ≅ P₁) (b : P₁ ≅ P₂) (c : P₂ ≅ P₃) (d : P₃ ≅ P₄) (e : P₀ ≅ P₄)
    (h : a.hom ≫ b.hom ≫ c.hom ≫ d.hom = e.hom) :
    d.inv ≫ c.inv ≫ b.inv ≫ a.inv = e.inv := by
  have := congrArg Iso.inv (show a ≪≫ b ≪≫ c ≪≫ d = e from Iso.ext (by simpa using h))
  simpa using this

/-- A composite of nine morphisms regrouped around its middle three. -/
theorem comp_nine_eq {C : Type*} [Category* C] {P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇ P₈ P₉ : C}
    (u : P₀ ⟶ P₁) (s : P₁ ⟶ P₂) (f : P₂ ⟶ P₃) (q : P₃ ⟶ P₄) (x : P₄ ⟶ P₅) (q' : P₅ ⟶ P₆)
    (f' : P₆ ⟶ P₇) (s' : P₇ ⟶ P₈) (u' : P₈ ⟶ P₉) (τ : P₀ ⟶ P₄) (τ' : P₅ ⟶ P₉)
    (hA : u ≫ s ≫ f ≫ q = τ) (hB : q' ≫ f' ≫ s' ≫ u' = τ') :
    u ≫ (s ≫ (f ≫ (q ≫ x ≫ q') ≫ f') ≫ s') ≫ u' = τ ≫ x ≫ τ' := by
  rw [← hA, ← hB]
  simp only [Category.assoc]

section Compatibility

variable {W' Wj Wi UA' UjA UiA UB' UjB UiB X' : RingedSpace.{u, u}}
  (pW : W' ⟶ Wj) (tC : Wj ⟶ Wi) (pCi : W' ⟶ Wi) (e1 : pW ≫ tC = pCi)
  (iUj : Wj ⟶ UjA) (tA : UjA ⟶ UiA) (iUi : Wi ⟶ UiA) (iU' : W' ⟶ UA') (pUj : UA' ⟶ UjA)
  (pUi : UA' ⟶ UiA) (e2A : pUj ≫ tA = pUi) (e3A : iUj ≫ tA = tC ≫ iUi)
  (e4A : pW ≫ iUj = iU' ≫ pUj) (e5A : pCi ≫ iUi = iU' ≫ pUi)
  (iVj : Wj ⟶ UjB) (tB : UjB ⟶ UiB) (iVi : Wi ⟶ UiB) (iV' : W' ⟶ UB') (pVj : UB' ⟶ UjB)
  (pVi : UB' ⟶ UiB) (e2B : pVj ≫ tB = pVi) (e3B : iVj ≫ tB = tC ≫ iVi)
  (e4B : pW ≫ iVj = iV' ≫ pVj) (e5B : pCi ≫ iVi = iV' ≫ pVi)
  (jU' : UA' ⟶ X') (jV' : UB' ⟶ X') (h' : iU' ≫ jU' = iV' ≫ jV')
  (EA : DerivedModules UiA) (EB : DerivedModules UiB) (E : DerivedModules X')
  (a : (derivedRestrict pUi).obj EA ≅ (derivedRestrict jU').obj E)
  (b : (derivedRestrict pVi).obj EB ≅ (derivedRestrict jV').obj E)
  (c : (derivedRestrict tC).obj ((derivedRestrict iUi).obj EA) ≅
    (derivedRestrict tC).obj ((derivedRestrict iVi).obj EB))

/-- The comparison on `W'` of the identifications `a` and `b`, read through the square
comparisons of the faces over `W'` at the stage `i`. -/
def overlapComparison :
    (derivedRestrict pCi).obj ((derivedRestrict iUi).obj EA) ≅
      (derivedRestrict pCi).obj ((derivedRestrict iVi).obj EB) :=
  (derivedRestrictSquareIso pCi iUi iU' pUi e5A).app EA ≪≫ (derivedRestrict iU').mapIso a ≪≫
    (overlapIso jU' jV' iU' iV' h').app E ≪≫ ((derivedRestrict iV').mapIso b).symm ≪≫
    ((derivedRestrictSquareIso pCi iVi iV' pVi e5B).app EB).symm

/-- **The compatibility on the overlap, moved to a later stage.** Let `c` be an isomorphism at
a later stage whose pullback is, through the comparison of the factorisation `pW ≫ tC = pCᵢ`,
the comparison on `W'` of the identifications `a` and `b`. Then its transport to the pullbacks
of `EA` and `EB` along `tA` and `tB` is, through the square comparisons of the faces over `W'`,
the comparison on `W'` of the transported identifications. -/
theorem squareIso_inv_comp_map_comp_squareIso_hom_of_factorIso
    (hcθ : (factorIso pW tC pCi e1).inv.app ((derivedRestrict iUi).obj EA) ≫
        (derivedRestrict pW).map c.hom ≫
        (factorIso pW tC pCi e1).hom.app ((derivedRestrict iVi).obj EB) =
      (derivedRestrictSquareIso pCi iUi iU' pUi e5A).hom.app EA ≫
        (derivedRestrict iU').map a.hom ≫ (overlapIso jU' jV' iU' iV' h').hom.app E ≫
        (derivedRestrict iV').map b.inv ≫
        (derivedRestrictSquareIso pCi iVi iV' pVi e5B).inv.app EB) :
    (derivedRestrictSquareIso pW iUj iU' pUj e4A).inv.app ((derivedRestrict tA).obj EA) ≫
        (derivedRestrict pW).map ((derivedRestrictSquareIso iUj tA tC iUi e3A).app EA ≪≫ c ≪≫
          ((derivedRestrictSquareIso iVj tB tC iVi e3B).app EB).symm).hom ≫
        (derivedRestrictSquareIso pW iVj iV' pVj e4B).hom.app ((derivedRestrict tB).obj EB) =
      (derivedRestrict iU').map (((factorIso pUj tA pUi e2A).app EA ≪≫ a).hom) ≫
        (overlapIso jU' jV' iU' iV' h').hom.app E ≫
        (derivedRestrict iV').map (((factorIso pVj tB pVi e2B).app EB ≪≫ b).inv) := by
  have hc : (derivedRestrict pW).map c.hom =
      (factorIso pW tC pCi e1).hom.app ((derivedRestrict iUi).obj EA) ≫
        ((derivedRestrictSquareIso pCi iUi iU' pUi e5A).hom.app EA ≫
          (derivedRestrict iU').map a.hom ≫ (overlapIso jU' jV' iU' iV' h').hom.app E ≫
          (derivedRestrict iV').map b.inv) ≫
        (derivedRestrictSquareIso pCi iVi iV' pVi e5B).inv.app EB ≫
        (factorIso pW tC pCi e1).inv.app ((derivedRestrict iVi).obj EB) := by
    rw [← cancel_epi ((factorIso pW tC pCi e1).inv.app ((derivedRestrict iUi).obj EA)),
      ← cancel_mono ((factorIso pW tC pCi e1).hom.app ((derivedRestrict iVi).obj EB))]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
    rw [hcθ]
    simp only [← Category.assoc]
    exact (Category.comp_id _).symm
  have kA := cube_path_coherence pW tC pCi iUj tA iUi iU' pUj pUi e1 e2A e3A e4A e5A EA
  have kB := inv_comp_inv_comp_inv_comp_inv
    ((derivedRestrictSquareIso pW iVj iV' pVj e4B).app ((derivedRestrict tB).obj EB)).symm
    ((derivedRestrict pW).mapIso ((derivedRestrictSquareIso iVj tB tC iVi e3B).app EB))
    ((factorIso pW tC pCi e1).app ((derivedRestrict iVi).obj EB))
    ((derivedRestrictSquareIso pCi iVi iV' pVi e5B).app EB)
    ((derivedRestrict iV').mapIso ((factorIso pVj tB pVi e2B).app EB))
    (cube_path_coherence pW tC pCi iVj tB iVi iV' pVj pVi e1 e2B e3B e4B e5B EB)
  simp only [Iso.symm_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_inv] at kB
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Iso.trans_inv,
    Functor.map_comp, hc, Category.assoc]
  rw [← Category.assoc ((derivedRestrict iU').map _) ((derivedRestrict iU').map a.hom),
    ← kA]
  simp only [Category.assoc, ← kB]

include e2A e4A e2B e4B in
/-- **The glued object at a later stage pulls back to the given object.** -/
theorem nonempty_iso_derivedRestrict_glueing_of_factorIso {Xj : RingedSpace.{u, u}}
    {jU : UjA ⟶ Xj} {jV : UjB ⟶ Xj} {p : X' ⟶ Xj}
    [SheafedSpace.IsOpenImmersion jU'] [SheafedSpace.IsOpenImmersion jV']
    (hpb' : IsPullback iU' iV' jU' jV')
    (cover : Set.range jU'.hom.base ∪ Set.range jV'.hom.base = Set.univ)
    (hU : jU' ≫ p = pUj ≫ jU) (hV : jV' ≫ p = pVj ≫ jV) {hj : iUj ≫ jU = iVj ≫ jV}
    (hcθ : (factorIso pW tC pCi e1).inv.app ((derivedRestrict iUi).obj EA) ≫
        (derivedRestrict pW).map c.hom ≫
        (factorIso pW tC pCi e1).hom.app ((derivedRestrict iVi).obj EB) =
      (derivedRestrictSquareIso pCi iUi iU' pUi e5A).hom.app EA ≫
        (derivedRestrict iU').map a.hom ≫ (overlapIso jU' jV' iU' iV' hpb'.w).hom.app E ≫
        (derivedRestrict iV').map b.inv ≫
        (derivedRestrictSquareIso pCi iVi iV' pVi e5B).inv.app EB)
    (G : Glueing jU jV iUj iVj hj ((derivedRestrict tA).obj EA) ((derivedRestrict tB).obj EB)
      ((derivedRestrictSquareIso iUj tA tC iUi e3A).app EA ≪≫ c ≪≫
        ((derivedRestrictSquareIso iVj tB tC iVi e3B).app EB).symm)) :
    Nonempty ((derivedRestrict p).obj G.F ≅ E) := by
  obtain ⟨φ, -, -⟩ := exists_iso_derivedRestrict_glueing hpb' cover hU hV e4A e4B G E
    ((factorIso pUj tA pUi e2A).app EA ≪≫ a) ((factorIso pVj tB pVi e2B).app EB ≪≫ b)
    (squareIso_inv_comp_map_comp_squareIso_hom_of_factorIso pW tC pCi e1 iUj tA iUi iU' pUj pUi
      e2A e3A e4A e5A iVj tB iVi iV' pVj pVi e2B e3B e4B e5B jU' jV' hpb'.w EA EB E a b c hcθ)
  exact ⟨φ⟩

include e2A e3A e4A e2B e3B e4B in
/-- **Glueing at a later stage.** If the pullback of `c` to `W'`, read through the comparison of
the factorisation `pW ≫ tC = pCᵢ`, is the comparison on `W'` of `a` and `b`, the pullbacks of `EA`
and `EB` to the later stage glue, along the transport of `c`, to an object whose pullback to `X'`
is `E`. -/
theorem exists_glueing_derivedRestrict_iso_of_homCongr {Xj : RingedSpace.{u, u}}
    {jU : UjA ⟶ Xj} {jV : UjB ⟶ Xj} {p : X' ⟶ Xj}
    [SheafedSpace.IsOpenImmersion jU] [SheafedSpace.IsOpenImmersion jV]
    [SheafedSpace.IsOpenImmersion jU'] [SheafedSpace.IsOpenImmersion jV']
    (hpb : IsPullback iUj iVj jU jV) (hpb' : IsPullback iU' iV' jU' jV')
    (cover : Set.range jU'.hom.base ∪ Set.range jV'.hom.base = Set.univ)
    (hU : jU' ≫ p = pUj ≫ jU) (hV : jV' ≫ p = pVj ≫ jV)
    (hcθ : (((factorIso pW tC pCi e1).app ((derivedRestrict iUi).obj EA)).homCongr
        ((factorIso pW tC pCi e1).app ((derivedRestrict iVi).obj EB)))
        ((derivedRestrict pW).map c.hom) =
      (overlapComparison pCi iUi iU' pUi e5A iVi iV' pVi e5B jU' jV' hpb'.w EA EB E a b).hom) :
    ∃ F : DerivedModules Xj, Nonempty ((derivedRestrict jU).obj F ≅ (derivedRestrict tA).obj EA) ∧
      Nonempty ((derivedRestrict jV).obj F ≅ (derivedRestrict tB).obj EB) ∧
        Nonempty ((derivedRestrict p).obj F ≅ E) := by
  obtain ⟨G⟩ := exists_glueing jU jV iUj iVj hpb ((derivedRestrict tA).obj EA)
    ((derivedRestrict tB).obj EB)
    ((derivedRestrictSquareIso iUj tA tC iUi e3A).app EA ≪≫ c ≪≫
      ((derivedRestrictSquareIso iVj tB tC iVi e3B).app EB).symm)
  have h₁ := (Iso.homCongr_apply _ _ _).symm.trans hcθ
  exact ⟨G.F, ⟨G.f⟩, ⟨G.g⟩, nonempty_iso_derivedRestrict_glueing_of_factorIso pW tC pCi e1 iUj tA
    iUi iU' pUj pUi e2A e3A e4A e5A iVj tB iVi iV' pVj pVi e2B e3B e4B e5B jU' jV' EA EB E a b c
    hpb' cover hU hV h₁ G⟩

end Compatibility

end Stacks.Cohomology.GlueingComplexes

end
