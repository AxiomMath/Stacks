module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseBaseFieldTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseSheafStalkNaturality

/-!
# The lisse sheaf of a module over the Galois group of a finite field, over `k̄`, naturally

Over `k̄` the lisse sheaf `ℱ_{Q₀}` of a finite `ℤ/m`-module `Q₀` with a continuous action of
`π₁(Spec k)` becomes the constant sheaf `Q₀`, carrying the Frobenius twist to `Φ⁻¹` followed by the
twist of the constant sheaf
(`Stacks.EtaleCohomology.exists_isIso_twist_lisseEtaleSheaf_baseField`). This file shows that the
identification can be chosen natural in `Q₀`.

## Main definitions

* `Stacks.EtaleCohomology.lisseBaseFieldModuleMap`: the endomorphism of the descended module `Q₀`
  given by an endomorphism of `Q`.

## Main results

* `Stacks.EtaleCohomology.exists_iso_rationalPointSections_lisseEtaleSheaf_natural`: the sections
  of `ℱ_P|_{k̄}` over `ȳ` are `P`, carrying the twist to `Φ⁻¹`, naturally in `P`.
* `Stacks.EtaleCohomology.exists_isIso_twist_of_rationalPointSections_natural`: the twisted
  identification over `k̄` adjoint to an identification of the sections at `ȳ` is natural.
* `Stacks.EtaleCohomology.exists_isIso_twist_lisseEtaleSheaf_baseField_natural`: over `k̄` the
  lisse sheaf of the descended module is the constant sheaf `Q`, naturally in `Q`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology

/-! ### The sections over the `k̄`-point, naturally -/

section Sections

attribute [local instance] ModuleCat.hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (U : B.Scheme) {k : Type u} [Field k] [Fintype k]
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (m : ℕ) [NeZero m]
  (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)
  (z' : GeometricPoint (Spec (.of k)))
  (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) (EtaleFundamentalGroup (Spec (.of k))
      z'))

/-- **The sections of `ℱ_P|_{k̄}` over `ȳ` are `P`, carrying the twist to `Φ⁻¹`, naturally in
`P`**: the identification of
`Stacks.EtaleCohomology.exists_iso_rationalPointSections_lisseEtaleSheaf` can be chosen to
intertwine the maps induced by every endomorphism of `P`. -/
theorem exists_iso_rationalPointSections_lisseEtaleSheaf_natural :
    ∃ W : (etaleModuleInverseImage.{u, 0} (ZMod m)
        (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar) ⋙
        sheafToPresheaf _ (ModuleCat.{u + 1} (ZMod m)) ⋙
          (CategoryTheory.evaluation _ (ModuleCat.{u + 1} (ZMod m))).obj
            (op (rationalPointBaseChangeObj (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
              (baseFieldOver_id_comp_hom k)))).obj
          ((lisseEtaleSheaf B (BigEtaleSite.specField B U k) z' (ZMod m)).obj P) ≅
        P.obj.obj.obj.V,
      (rationalPointFrobeniusEndo (ZMod m) (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
          (baseFieldOver_id_comp_hom k) p q hcard).app
            ((lisseEtaleSheaf B (BigEtaleSite.specField B U k) z' (ZMod m)).obj P) ≫ W.hom =
        W.hom ≫ (P.obj.obj.obj.ρ (finiteFieldFrobenius p q hcard z')⁻¹).asHom ∧
      ∀ g : P ⟶ P, (etaleModuleInverseImage.{u, 0} (ZMod m)
          (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar) ⋙
          sheafToPresheaf _ (ModuleCat.{u + 1} (ZMod m)) ⋙
            (CategoryTheory.evaluation _ (ModuleCat.{u + 1} (ZMod m))).obj
              (op (rationalPointBaseChangeObj (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
                (baseFieldOver_id_comp_hom k)))).map
            ((lisseEtaleSheaf B (BigEtaleSite.specField B U k) z' (ZMod m)).map g) ≫ W.hom =
        W.hom ≫ g.hom.hom.hom.hom := by
  obtain ⟨t⟩ := nonempty_finiteEtaleFiberFunctorIso (Spec (.of k))
    (baseFieldGeometricPoint (k := k) kbar) z'
  have R1 : (rationalPointFrobeniusEndo (ZMod m) (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
      (baseFieldOver_id_comp_hom k) p q hcard).app
        ((lisseEtaleSheaf B (BigEtaleSite.specField B U k) z' (ZMod m)).obj P) ≫
      ((rationalPointSectionsStalkIso (ZMod m) (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
        (baseFieldOver_id_comp_hom k)).app
          ((lisseEtaleSheaf B (BigEtaleSite.specField B U k) z' (ZMod m)).obj P)).hom =
      ((rationalPointSectionsStalkIso (ZMod m) (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
        (baseFieldOver_id_comp_hom k)).app
          ((lisseEtaleSheaf B (BigEtaleSite.specField B U k) z' (ZMod m)).obj P)).hom ≫
        (GrothendieckTopology.Point.Hom.sheafFiber (smallEtalePointHom (Spec (.of k))
          (galoisPointHom kbar (arithmeticFrobenius k kbar p q hcard).symm
            (𝟙 (Spec (.of k)))))).app
          ((lisseEtaleSheaf B (BigEtaleSite.specField B U k) z' (ZMod m)).obj P) :=
    rationalPointFrobeniusEndo_comp_rationalPointSectionsStalkIso_hom (ZMod m)
      (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _) (baseFieldOver_id_comp_hom k) p q hcard
      ((lisseEtaleSheaf B (BigEtaleSite.specField B U k) z' (ZMod m)).obj P)
  have h₂ := sheafFiber_comp_lisseEtaleSheafFiberIso_hom B (BigEtaleSite.specField B U k) z' m t
    (galoisPointHom kbar (arithmeticFrobenius k kbar p q hcard).symm (𝟙 (Spec (.of k)))) _
    (inv_finiteFieldFrobenius_hom kbar p q hcard) P
  have htr : etaleFundamentalGroupMulEquiv t
      (finiteFieldFrobenius p q hcard (baseFieldGeometricPoint (k := k) kbar))⁻¹ =
      (finiteFieldFrobenius p q hcard z')⁻¹ := by
    rw [map_inv, etaleFundamentalGroupMulEquiv_finiteFieldFrobenius]
  rw [htr] at h₂
  refine ⟨_, iso_trans_hom_comm _ _ _ _ _ R1 h₂, fun g => ?_⟩
  exact iso_trans_hom_comm _ _ _ _ _
    ((rationalPointSectionsStalkIso (ZMod m) (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
      (baseFieldOver_id_comp_hom k)).hom.naturality
        ((lisseEtaleSheaf B (BigEtaleSite.specField B U k) z' (ZMod m)).map g))
    (lisseEtaleSheafFiberIso_hom_naturality B (BigEtaleSite.specField B U k) z' m t g)

end Sections

/-! ### The twisted identification over `k̄`, naturally -/

section Twist

attribute [local instance] ModuleCat.hasLimitsOfSize

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar]
  [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- **The twisted identification over `k̄` adjoint to a given identification of the sections at
`ȳ`, naturally**: the isomorphism `u₀` of
`Stacks.EtaleCohomology.exists_isIso_twist_of_rationalPointSections` also intertwines `s` and `s₀`
whenever the identification `W` of the sections at `ȳ` does. -/
theorem exists_isIso_twist_of_rationalPointSections_natural
    (F₀ : EtaleModules.{u, 0} Λ (Spec (.of k))) (M : ModuleCat.{u + 1} Λ) (B : M ⟶ M)
    (W : (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar) ⋙
        sheafToPresheaf _ (ModuleCat.{u + 1} Λ) ⋙
          (CategoryTheory.evaluation _ (ModuleCat.{u + 1} Λ)).obj
            (op (rationalPointBaseChangeObj (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
              (baseFieldOver_id_comp_hom k)))).obj F₀ ≅ M)
    (hW : (rationalPointFrobeniusEndo Λ (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
        (baseFieldOver_id_comp_hom k) p q hcard).app F₀ ≫ W.hom = W.hom ≫ B) :
    ∃ u₀ : (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k))))
        kbar)).obj
        (etaleModuleConstantSheaf Λ M (Spec (.of k))) ⟶
      (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k))))
          kbar)).obj F₀,
      IsIso u₀ ∧ u₀ ≫ (frobeniusBaseChangeTwist.{u, 0} Λ (Over.mk (𝟙 (Spec (.of k)))) kbar p q
          hcard).app F₀ =
        (frobeniusBaseChangeTwist.{u, 0} Λ (Over.mk (𝟙 (Spec (.of k)))) kbar p q hcard).app
            (etaleModuleConstantSheaf Λ M (Spec (.of k))) ≫
          (etaleModuleDirectImage.{u, 0} Λ
            (geometricFrobeniusBaseChange (Over.mk (𝟙 (Spec (.of k)))) kbar p q hcard)).map
            ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k))))
                kbar)).map
              ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).map B)) ≫
          (etaleModuleDirectImage.{u, 0} Λ
            (geometricFrobeniusBaseChange (Over.mk (𝟙 (Spec (.of k)))) kbar p q hcard)).map u₀ ∧
      ∀ (s : M ⟶ M) (s₀ : F₀ ⟶ F₀),
        (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar) ⋙
          sheafToPresheaf _ (ModuleCat.{u + 1} Λ) ⋙
            (CategoryTheory.evaluation _ (ModuleCat.{u + 1} Λ)).obj
              (op (rationalPointBaseChangeObj (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
                (baseFieldOver_id_comp_hom k)))).map s₀ ≫ W.hom = W.hom ≫ s →
        (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k))))
            kbar)).map ((constantSheaf (Spec (.of k)).smallEtaleTopology
              (ModuleCat.{u + 1} Λ)).map s) ≫ u₀ =
          u₀ ≫ (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k))))
            kbar)).map s₀ := by
  have hT : IsTerminal ((smallEtaleBaseChange (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k))))
      kbar)).obj
      (Scheme.Etale.mk (𝟙 (Over.mk (𝟙 (Spec (.of k)))).left))) :=
    (isTerminalEtaleMkId _).isTerminalObj _
  have hO := isTerminalRationalPointBaseChangeObj (k := k) kbar
  have hΦT : IsTerminal ((smallEtaleBaseChange
      (geometricFrobeniusBaseChange (Over.mk (𝟙 (Spec (.of k)))) kbar p q hcard)).obj
      ((smallEtaleBaseChange (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).obj
        (Scheme.Etale.mk (𝟙 (Over.mk (𝟙 (Spec (.of k)))).left)))) := hT.isTerminalObj _
  have hi : IsIso (hT.from (rationalPointBaseChangeObj (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
      (baseFieldOver_id_comp_hom k))) := ⟨⟨hO.from _, hO.hom_ext _ _, hT.hom_ext _ _⟩⟩
  have : IsIso (rationalPointFrobeniusLift (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
      (baseFieldOver_id_comp_hom k) p q hcard ≫
        (smallEtaleBaseChange (geometricFrobeniusBaseChange (Over.mk (𝟙 (Spec (.of k)))) kbar p q
            hcard)).map
          (hT.from (rationalPointBaseChangeObj (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
            (baseFieldOver_id_comp_hom k)))) := ⟨⟨hO.from _, hO.hom_ext _ _, hΦT.hom_ext _ _⟩⟩
  obtain ⟨ρ, hρ⟩ := exists_pulledBackConstantSection_comp_frobeniusBaseChangeTwist Λ M
    (Over.mk (𝟙 (Spec (.of k)))) kbar p q hcard
  let adj := (constantSheafAdj (Over.mk (𝟙 (Spec (.of k)))).left.smallEtaleTopology
      (ModuleCat.{u + 1} Λ) (isTerminalEtaleMkId (Over.mk (𝟙 (Spec (.of k)))).left)).comp
      (etaleModuleInverseImageAdj.{u, 0} Λ (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar))
  let u₀ := (adj.homEquiv M ((etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).obj F₀)).symm
    (W.inv ≫ ((etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).obj F₀).obj.map
        (inv (hT.from (rationalPointBaseChangeObj (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
          (baseFieldOver_id_comp_hom k)))).op)
  have hu : pulledBackConstantSection Λ M (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar) ≫
      u₀.hom.app (op ((smallEtaleBaseChange (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k))))
          kbar)).obj
        (Scheme.Etale.mk (𝟙 (Over.mk (𝟙 (Spec (.of k)))).left)))) =
      W.inv ≫ ((etaleModuleInverseImage.{u, 0} Λ
        (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).obj F₀).obj.map
          (inv (hT.from (rationalPointBaseChangeObj (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
            (baseFieldOver_id_comp_hom k)))).op := by
    have h := (adj.homEquiv M ((etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).obj F₀)).apply_symm_apply
        (W.inv ≫ ((etaleModuleInverseImage.{u, 0} Λ
          (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).obj F₀).obj.map
            (inv (hT.from (rationalPointBaseChangeObj (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
              (baseFieldOver_id_comp_hom k)))).op)
    simp only [adj, Adjunction.homEquiv_unit, Adjunction.comp_unit_app,
      Stacks.ConstantSheaf.constantSheafAdj_unit_app] at h
    exact (Category.assoc _ _ _).trans h
  refine ⟨u₀, ?_, ?_, fun s s₀ hs => ?_⟩
  rotate_left 2
  · apply hom_ext_inverseImage_constant Λ M (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)
    have hWs : W.inv ≫ ((etaleModuleInverseImage.{u, 0} Λ
        (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).map s₀).hom.app
          (op (rationalPointBaseChangeObj (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
            (baseFieldOver_id_comp_hom k))) = s ≫ W.inv :=
      inv_comp_eq_of_hom_comp W _ s hs
    have n1 : pulledBackConstantSection Λ M (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k))))
          kbar) ≫
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k))))
          kbar)).map ((constantSheaf (Spec (.of k)).smallEtaleTopology
            (ModuleCat.{u + 1} Λ)).map s)).hom.app
          (op ((smallEtaleBaseChange (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).obj
            (Scheme.Etale.mk (𝟙 (Over.mk (𝟙 (Spec (.of k)))).left)))) =
        s ≫ pulledBackConstantSection Λ M (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k))))
          kbar) :=
      pulledBackConstantSection_naturality Λ (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k))))
        kbar) s
    have n2 := ((etaleModuleInverseImage.{u, 0} Λ
        (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).map s₀).hom.naturality
      (inv (hT.from (rationalPointBaseChangeObj (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
        (baseFieldOver_id_comp_hom k)))).op
    have lhs : pulledBackConstantSection Λ M (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k))))
          kbar) ≫
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k))))
          kbar)).map ((constantSheaf (Spec (.of k)).smallEtaleTopology
            (ModuleCat.{u + 1} Λ)).map s)).hom.app
          (op ((smallEtaleBaseChange (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).obj
            (Scheme.Etale.mk (𝟙 (Over.mk (𝟙 (Spec (.of k)))).left)))) ≫
        u₀.hom.app (op ((smallEtaleBaseChange (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k))))
          kbar)).obj (Scheme.Etale.mk (𝟙 (Over.mk (𝟙 (Spec (.of k)))).left)))) =
        s ≫ W.inv ≫ ((etaleModuleInverseImage.{u, 0} Λ
          (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).obj F₀).obj.map
            (inv (hT.from (rationalPointBaseChangeObj (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
              (baseFieldOver_id_comp_hom k)))).op := by
      rw [reassoc_of% n1, hu]
    have rhs : pulledBackConstantSection Λ M (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k))))
          kbar) ≫
        u₀.hom.app (op ((smallEtaleBaseChange (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k))))
          kbar)).obj (Scheme.Etale.mk (𝟙 (Over.mk (𝟙 (Spec (.of k)))).left)))) ≫
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k))))
          kbar)).map s₀).hom.app
          (op ((smallEtaleBaseChange (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).obj
            (Scheme.Etale.mk (𝟙 (Over.mk (𝟙 (Spec (.of k)))).left)))) =
        s ≫ W.inv ≫ ((etaleModuleInverseImage.{u, 0} Λ
          (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).obj F₀).obj.map
            (inv (hT.from (rationalPointBaseChangeObj (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
              (baseFieldOver_id_comp_hom k)))).op := by
      rw [reassoc_of% hu, n2, reassoc_of% hWs]
    exact ((Category.assoc _ _ _).symm.trans (lhs.trans rhs.symm)).trans (Category.assoc _ _ _)
  · have : IsIso ((inverseImageEtaleModuleConstantSheafIso Λ M
        (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).inv ≫ u₀) := by
      refine isIso_of_isIso_app_etaleMk Λ
        (rationalPointBaseChangeLift (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
          (baseFieldOver_id_comp_hom k)) (surjective_rationalPointBaseChangeLift_baseFieldOver kbar)
        _ ?_
      have := isIso_constantSheafSection_etaleMk Λ
        (rationalPointBaseChangeLift (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
          (baseFieldOver_id_comp_hom k)) M
      have hc := constantSectionChase _ _ _ _ _ _ _ _ _
        (constantSheafSection_comp_inverseImageConstantIso_inv Λ M
          (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)
          (hT.from (rationalPointBaseChangeObj (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
            (baseFieldOver_id_comp_hom k))))
        (u₀.hom.naturality (hT.from (rationalPointBaseChangeObj (Over.mk (𝟙 (Spec (.of k)))) kbar
          (𝟙 _) (baseFieldOver_id_comp_hom k))).op) hu (by
            rw [← CategoryTheory.Functor.map_comp, ← op_comp, IsIso.hom_inv_id, op_id,
              CategoryTheory.Functor.map_id])
      have : IsIso (constantSheafSection Λ M (Scheme.Etale.mk
          (rationalPointBaseChangeLift (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
            (baseFieldOver_id_comp_hom k))) ≫
          ((inverseImageEtaleModuleConstantSheafIso Λ M
            (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).inv ≫ u₀).hom.app
            (op (Scheme.Etale.mk (rationalPointBaseChangeLift (Over.mk (𝟙 (Spec (.of k)))) kbar
              (𝟙 _) (baseFieldOver_id_comp_hom k))))) := by
        have e : constantSheafSection Λ M (Scheme.Etale.mk
            (rationalPointBaseChangeLift (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
              (baseFieldOver_id_comp_hom k))) ≫
            ((inverseImageEtaleModuleConstantSheafIso Λ M
              (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).inv ≫ u₀).hom.app
              (op (Scheme.Etale.mk (rationalPointBaseChangeLift (Over.mk (𝟙 (Spec (.of k)))) kbar
                (𝟙 _) (baseFieldOver_id_comp_hom k)))) = W.inv := hc
        rw [e]
        infer_instance
      exact IsIso.of_isIso_comp_left (constantSheafSection Λ M (Scheme.Etale.mk
        (rationalPointBaseChangeLift (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
            (baseFieldOver_id_comp_hom k)))) _
    have he : u₀ = (inverseImageEtaleModuleConstantSheafIso Λ M
        (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).hom ≫
        (inverseImageEtaleModuleConstantSheafIso Λ M
          (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).inv ≫ u₀ := by
      rw [Iso.hom_inv_id_assoc]
    rw [he]
    infer_instance
  · apply hom_ext_inverseImage_constant Λ M (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)
    have hW' := inv_comp_eq_of_hom_comp W _ B hW
    have key2 := twist_comp_of_isTerminal ((etaleModuleInverseImage.{u, 0} Λ
        (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).obj F₀).obj
      (smallEtaleBaseChange (geometricFrobeniusBaseChange (Over.mk (𝟙 (Spec (.of k)))) kbar p q
          hcard))
      ((frobeniusBaseChangeTwist.{u, 0} Λ (Over.mk (𝟙 (Spec (.of k)))) kbar p q hcard).app F₀).hom
          hT
      (hT.from (rationalPointBaseChangeObj (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
        (baseFieldOver_id_comp_hom k)))
      (rationalPointFrobeniusLift (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
          (baseFieldOver_id_comp_hom k) p q
        hcard) ρ W.inv B hW'
    have key := constantTwistChase _ _ _ _ _ _ _ _ B _ hρ
      (((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k))))
          kbar)).map
        ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
            B)).hom.naturality
          ρ.op)
      (u₀.hom.naturality ρ.op)
      (pulledBackConstantSection_naturality Λ (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k))))
          kbar) B) hu
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hu).trans
      (key2.trans (key.symm.trans (Category.assoc _ _ _))))

end Twist

/-! ### The lisse sheaf of the descended module, naturally -/

section Lisse

variable (B : BigEtaleSite.{u}) (U : B.Scheme) [ConnectedSpace U.1] {k : Type u} [Field k]
  [Fintype k] (f : U.1 ⟶ Spec (.of k)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  [IsAlgClosed kbar] (m : ℕ) [NeZero m] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q) (x : GeometricPoint U.1)
  (hs : Function.Surjective (etaleFundamentalGroupMap f x))
  (Q : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) (EtaleFundamentalGroup U.1 x))
  (hQ : ∀ g, etaleFundamentalGroupMap f x g = 1 → Q.obj.obj.obj.ρ g = 1)

/-- **The endomorphism of the descended module `Q₀` given by an endomorphism `g` of `Q`**: the same
map of underlying modules, which commutes with the descended action. -/
def lisseBaseFieldModuleMap (g : Q ⟶ Q) :
    lisseBaseFieldModule B U k f x hs (ZMod m) Q hQ ⟶
      lisseBaseFieldModule B U k f x hs (ZMod m) Q hQ :=
  ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := g.hom.hom.hom.hom
      comm := fun h => by
        obtain ⟨a, rfl⟩ := hs h
        ext v
        have hc := ConcreteCategory.congr_hom (g.hom.hom.hom.comm a) v
        change g.hom.hom.hom.hom.hom
            (((lisseBaseFieldModule B U k f x hs (ZMod m) Q hQ).obj.obj.obj.ρ
              (etaleFundamentalGroupMap f x a)).asHom.hom v) =
          ((lisseBaseFieldModule B U k f x hs (ZMod m) Q hQ).obj.obj.obj.ρ
            (etaleFundamentalGroupMap f x a)).asHom.hom (g.hom.hom.hom.hom.hom v)
        exact (congrArg g.hom.hom.hom.hom.hom
          (lisseBaseFieldModule_ρ_apply B U k f x hs (ZMod m) Q hQ a v)).trans
          (hc.trans (lisseBaseFieldModule_ρ_apply B U k f x hs (ZMod m) Q hQ a _).symm) }))

/-- **Over `k̄` the lisse sheaf `ℱ_{Q₀}` of the descended module is the constant sheaf `Q`,
naturally in `Q`**: the identification of
`Stacks.EtaleCohomology.exists_isIso_twist_lisseEtaleSheaf_baseField` can be chosen to intertwine
the maps induced by every endomorphism of `Q`. -/
theorem exists_isIso_twist_lisseEtaleSheaf_baseField_natural (φ : EtaleFundamentalGroup U.1 x)
    (hφ : etaleFundamentalGroupMap f x φ = (finiteFieldFrobenius p q hcard (x.map f))⁻¹) :
    ∃ (u₀ : (etaleModuleInverseImage.{u, 0} (ZMod m)
        (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).obj
          (etaleModuleConstantSheaf (ZMod m) Q.obj.obj.obj.V (Spec (.of k))) ⟶
      (etaleModuleInverseImage.{u, 0} (ZMod m)
        (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).obj
        ((lisseEtaleSheaf B (BigEtaleSite.specField B U k) (x.map f) (ZMod m)).obj
          (lisseBaseFieldModule B U k f x hs (ZMod m) Q hQ))), IsIso u₀ ∧
      u₀ ≫ (frobeniusBaseChangeTwist.{u, 0} (ZMod m) (Over.mk (𝟙 (Spec (.of k)))) kbar p q
          hcard).app ((lisseEtaleSheaf B (BigEtaleSite.specField B U k) (x.map f) (ZMod m)).obj
            (lisseBaseFieldModule B U k f x hs (ZMod m) Q hQ)) =
      (frobeniusBaseChangeTwist.{u, 0} (ZMod m) (Over.mk (𝟙 (Spec (.of k)))) kbar p q hcard).app
          (etaleModuleConstantSheaf (ZMod m) Q.obj.obj.obj.V (Spec (.of k))) ≫
        (etaleModuleDirectImage.{u, 0} (ZMod m)
          (geometricFrobeniusBaseChange (Over.mk (𝟙 (Spec (.of k)))) kbar p q hcard)).map
          ((etaleModuleInverseImage.{u, 0} (ZMod m)
            (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).map
            ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} (ZMod m))).map
              (Q.obj.obj.obj.ρ φ).asHom)) ≫
        (etaleModuleDirectImage.{u, 0} (ZMod m)
          (geometricFrobeniusBaseChange (Over.mk (𝟙 (Spec (.of k)))) kbar p q hcard)).map u₀ ∧
      ∀ g : Q ⟶ Q,
        (etaleModuleInverseImage.{u, 0} (ZMod m)
            (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).map
            ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} (ZMod m))).map
              g.hom.hom.hom.hom) ≫ u₀ =
          u₀ ≫ (etaleModuleInverseImage.{u, 0} (ZMod m)
            (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).map
            ((lisseEtaleSheaf B (BigEtaleSite.specField B U k) (x.map f) (ZMod m)).map
              (lisseBaseFieldModuleMap B U f m x hs Q hQ g)) := by
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  obtain ⟨W, hW, hWn⟩ := exists_iso_rationalPointSections_lisseEtaleSheaf_natural B U kbar m p q
    hcard (x.map f) (lisseBaseFieldModule B U k f x hs (ZMod m) Q hQ)
  have hB : (lisseBaseFieldModule B U k f x hs (ZMod m) Q hQ).obj.obj.obj.ρ
      (finiteFieldFrobenius p q hcard (x.map f))⁻¹ = Q.obj.obj.obj.ρ φ := by
    refine End.ext (ModuleCat.hom_ext (LinearMap.ext fun v => ?_))
    rw [← hφ]
    exact lisseBaseFieldModule_ρ_apply B U k f x hs (ZMod m) Q hQ φ v
  rw [hB] at hW
  obtain ⟨u₀, hiso, h₀, hn⟩ := exists_isIso_twist_of_rationalPointSections_natural (ZMod m) kbar p q
    hcard _ _ _ W hW
  exact ⟨u₀, hiso, h₀, fun g => hn _ _ (hWn (lisseBaseFieldModuleMap B U f m x hs Q hQ g))⟩

end Lisse

end Stacks.EtaleCohomology

end
