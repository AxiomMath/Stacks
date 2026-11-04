module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantTwistComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantModuleSheafIrreducibleSections

/-!
# A twist of a sheaf, read on the constant sheaf of its global sections

Let `s : X ⟶ X` be an endomorphism of a scheme, `G` a sheaf of `Λ`-modules on `X_étale` and
`β : G ⟶ s_* G` a map (a twist, for instance the canonical one of a sheaf pulled back along a
morphism `pr` with `s ≫ pr = pr`). Let `E = Γ(X, G)`, `ε : E_X ⟶ G` the counit of the constant
sheaf adjunction and `a : E ⟶ E` the map `β` induces on global sections, `Γ(β)` followed by
`Γ(X, s_* -) = Γ(X, -)`. Then `ε` carries the twist `E_X ⟶ s_* E_X` of the constant sheaf
(`Stacks.EtaleCohomology.constantSelfMapTwist`, adjoint to `s^{-1} E_X ≅ E_X`), composed with
`a`, to `β`:

`ε ≫ β = constantSelfMapTwist ≫ s_*(a_X ≫ ε)`.

So when `G` is constant and `ε` is an isomorphism, a twist of `G` is the canonical twist of a
constant sheaf followed by an automorphism of its value, namely the action on global sections.

## Main results

* `Stacks.EtaleCohomology.constantSheafSection_terminal_comp_constantSelfMapTwist` — the
  canonical twist sends the constant section over the terminal object to the constant section.
* `Stacks.EtaleCohomology.constantSheafΓUnit_comp_constantSelfMapTwist` — the same on global
  sections.
* `Stacks.EtaleCohomology.constantSheafΓCounit_comp_twist` — the identity above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- `ModuleCat.{u + 1} Λ` has colimits of size `u + 1` at the universe levels of the constant
sheaf adjunction of a small étale site. -/
abbrev moduleCatHasColimitsOfSizeSmallEtale (Λ : Type) [Ring Λ] :
    HasColimitsOfSize.{u + 1, u + 1, u + 1, u + 2} (ModuleCat.{u + 1, 0} Λ) :=
  ModuleCat.hasColimitsOfSize.{u + 1, 0, u + 1, u + 1} Λ

/-- Sheaves of `ModuleCat.{u + 1} Λ` on a small étale site have a global sections functor. -/
abbrev hasGlobalSectionsFunctorSmallEtaleModuleCat (Λ : Type) [Ring Λ] (Z : Scheme.{u}) :
    HasGlobalSectionsFunctor Z.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  hasGlobalSectionsFunctor_of_hasTerminal _ _

attribute [local instance] moduleCatHasColimitsOfSizeSmallEtale
  hasGlobalSectionsFunctorSmallEtaleModuleCat

variable (Λ : Type) [Ring Λ] {X : Scheme.{u}} (s : X ⟶ X)

/-- `f ≫ g = (f ≫ g ≫ e.hom) ≫ e.inv`. -/
lemma comp_eq_comp_comp_hom_comp_inv {𝒞 : Type*} [Category* 𝒞] {A B C D : 𝒞} (f : A ⟶ B)
    (g : B ⟶ C) (e : C ≅ D) : f ≫ g = (f ≫ g ≫ e.hom) ≫ e.inv := by
  simp

/-- **The canonical twist sends the constant section over the terminal object to the constant
section over its base change.** -/
lemma constantSheafSection_terminal_comp_constantSelfMapTwist (M : ModuleCat.{u + 1} Λ) :
    constantSheafSection.{u, 0} Λ M (⊤_ X.Etale) ≫
        (constantSelfMapTwist.{u, 0} Λ M s).hom.app (op (⊤_ X.Etale)) =
      constantSheafSection.{u, 0} Λ M ((smallEtaleBaseChange s).obj (⊤_ X.Etale)) := by
  let m : ⊤_ X.Etale ⟶ Scheme.Etale.mk (𝟙 X) := (isTerminalEtaleMkId X).from _
  rw [← constantSheafSection_comp_map.{u, 0} Λ M m, Category.assoc,
    (constantSelfMapTwist.{u, 0} Λ M s).hom.naturality m.op,
    reassoc_of% (constantSheafSection_comp_constantSelfMapTwist.{u, 0} Λ M s)]
  exact constantSheafSection_comp_map.{u, 0} Λ M ((smallEtaleBaseChange s).map m)

/-- The unit of `constantSheafΓAdj` followed by the identification of its right adjoint with the
one of `constantSheafAdj` at a terminal object is the unit of `constantSheafAdj`. -/
private lemma unit_comp_rightAdjointUniq_hom_app_constantSheafAdj {T : X.Etale} (hT : IsTerminal T)
    (M : ModuleCat.{u + 1} Λ) :
    (constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).unit.app M ≫
        ((constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightAdjointUniq
          (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT)).hom.app
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) =
      (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT).unit.app M :=
  Adjunction.unit_rightAdjointUniq_hom_app _ _ M

/-- **The canonical twist preserves the constant global sections**: the unit `M ⟶ Γ(X, M_X)`
followed by `Γ` of the twist `M_X ⟶ s_* M_X` and `Γ(X, s_* -) = Γ(X, -)` is the unit. -/
lemma constantSheafΓUnit_comp_constantSelfMapTwist (M : ModuleCat.{u + 1} Λ) :
    (constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).unit.app M ≫
        (etaleModuleGlobalSections.{u, 0} Λ X).map (constantSelfMapTwist.{u, 0} Λ M s) ≫
        (etaleModuleGlobalSectionsDirectImageIso.{u, 0} s Λ).hom.app
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) =
      (constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).unit.app M := by
  let hterm : IsTerminal ((smallEtaleBaseChange s).obj (⊤_ X.Etale)) :=
    IsTerminal.isTerminalObj (smallEtaleBaseChange s) _ terminalIsTerminal
  have h₁ := unit_comp_rightAdjointUniq_hom_app_constantSheafAdj (X := X) Λ terminalIsTerminal M
  have h₂ := unit_comp_rightAdjointUniq_hom_app_constantSheafAdj (X := X) Λ hterm M
  have hnat := (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    terminalIsTerminal).hom.naturality (constantSelfMapTwist.{u, 0} Λ M s)
  let C := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  let η := (constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).unit.app M
  let ΓT := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    (terminalIsTerminal (C := X.Etale))
  let Γh := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ) hterm
  let t := (etaleModuleGlobalSections.{u, 0} Λ X).map (constantSelfMapTwist.{u, 0} Λ M s)
  let p := ΓT.hom.app ((etaleModuleDirectImage.{u, 0} Λ s).obj C)
  have hD : (etaleModuleGlobalSectionsDirectImageIso.{u, 0} s Λ).hom.app C =
      p ≫ Γh.inv.app C := rfl
  have hL0 : (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
      terminalIsTerminal).unit.app M ≫
        (constantSelfMapTwist.{u, 0} Λ M s).hom.app (Opposite.op (⊤_ X.Etale)) =
      (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ) hterm).unit.app M := by
    rw [Stacks.ConstantSheaf.constantSheafAdj_unit_app,
      Stacks.ConstantSheaf.constantSheafAdj_unit_app]
    exact constantSheafSection_terminal_comp_constantSelfMapTwist Λ s M
  have key : η ≫ t ≫ p = η ≫ Γh.hom.app C :=
    (congrArg (η ≫ ·) hnat).trans ((Category.assoc _ _ _).symm.trans
      (((congrArg (· ≫ (constantSelfMapTwist.{u, 0} Λ M s).hom.app
        (Opposite.op (⊤_ X.Etale))) h₁).trans hL0).trans h₂.symm))
  calc η ≫ t ≫ (etaleModuleGlobalSectionsDirectImageIso.{u, 0} s Λ).hom.app C
      = η ≫ t ≫ (p ≫ Γh.inv.app C) := by rw [hD]
    _ = (η ≫ t ≫ p) ≫ Γh.inv.app C :=
        (congrArg (η ≫ ·) (Category.assoc t p (Γh.inv.app C)).symm).trans
          (Category.assoc η (t ≫ p) (Γh.inv.app C)).symm
    _ = (η ≫ Γh.hom.app C) ≫ Γh.inv.app C := congrArg (· ≫ Γh.inv.app C) key
    _ = η := (Category.assoc _ _ _).trans
        ((congrArg (η ≫ ·) (Iso.hom_inv_id_app Γh C)).trans (Category.comp_id η))

/-- **A twist of `G`, read on the constant sheaf of its global sections.** For `β : G ⟶ s_* G`,
the counit `ε : Γ(X, G)_X ⟶ G` carries the canonical twist of the constant sheaf followed by the
action `a = Γ(β) ≫ (Γ(X, s_* -) = Γ(X, -))` on `Γ(X, G)` to `β`. -/
theorem constantSheafΓCounit_comp_twist (G : EtaleModules.{u, 0} Λ X)
    (β : G ⟶ (etaleModuleDirectImage.{u, 0} Λ s).obj G) :
    (constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G ≫ β =
      constantSelfMapTwist.{u, 0} Λ ((etaleModuleGlobalSections.{u, 0} Λ X).obj G) s ≫
        (etaleModuleDirectImage.{u, 0} Λ s).map
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
              ((etaleModuleGlobalSections.{u, 0} Λ X).map β ≫
                (etaleModuleGlobalSectionsDirectImageIso.{u, 0} s Λ).hom.app G) ≫
            (constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G) := by
  let adj := constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let iso := etaleModuleGlobalSectionsDirectImageIso.{u, 0} s Λ
  let E := (etaleModuleGlobalSections.{u, 0} Λ X).obj G
  let a := (etaleModuleGlobalSections.{u, 0} Λ X).map β ≫ iso.hom.app G
  let c := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map a
  let ε := adj.counit.app G
  let τ := constantSelfMapTwist.{u, 0} Λ E s
  let Γ := etaleModuleGlobalSections.{u, 0} Λ X
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hU := constantSheafΓUnit_comp_constantSelfMapTwist Λ s E
  have hU' : adj.unit.app E ≫ Γ.map τ = adj.unit.app E ≫
      iso.inv.app ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E) :=
    (comp_eq_comp_comp_hom_comp_inv _ _ (iso.app _)).trans (congrArg (· ≫ _) hU)
  have hn₁ : Γ.map (c ≫ ε) ≫ iso.inv.app G = iso.inv.app _ ≫
      Γ.map ((etaleModuleDirectImage.{u, 0} Λ s).map (c ≫ ε)) :=
    iso.inv.naturality (c ≫ ε)
  have hηa : adj.unit.app E ≫ Γ.map (c ≫ ε) = a :=
    (congrArg (adj.unit.app E ≫ ·) (Γ.map_comp c ε)).trans <|
      (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ Γ.map ε) (adj.unit.naturality a).symm).trans <|
      (Category.assoc _ _ _).trans <|
      (congrArg (a ≫ ·) (adj.right_triangle_components G)).trans (Category.comp_id a)
  have hL : adj.unit.app E ≫ Γ.map (ε ≫ β) = Γ.map β :=
    (congrArg (adj.unit.app E ≫ ·) (Γ.map_comp ε β)).trans <|
      (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ Γ.map β) (adj.right_triangle_components G)).trans (Category.id_comp _)
  have hR : adj.unit.app E ≫ Γ.map (τ ≫ (etaleModuleDirectImage.{u, 0} Λ s).map (c ≫ ε)) =
      Γ.map β :=
    (congrArg (adj.unit.app E ≫ ·) (Γ.map_comp _ _)).trans <|
      (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ _) hU').trans <|
      (Category.assoc _ _ _).trans <|
      (congrArg (adj.unit.app E ≫ ·) hn₁.symm).trans <|
      (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ iso.inv.app G) hηa).trans <|
      (Category.assoc _ _ _).trans <|
      (congrArg (Γ.map β ≫ ·) (iso.hom_inv_id_app G)).trans (Category.comp_id _)
  exact hL.trans hR.symm

/-! ### The unit of the constant sheaf on a nonempty scheme is injective -/

/-- **The empty sieve does not cover a nonempty object of the small étale site.** -/
theorem bot_not_mem_smallEtaleTopology (T : X.Etale) [Nonempty T.left] :
    (⊥ : CategoryTheory.Sieve T) ∉ X.smallEtaleTopology T := by
  intro h
  obtain ⟨𝒰, _, p, hle⟩ := (Scheme.mem_smallGrothendieckTopology _ _).mp h
  obtain ⟨x⟩ := ‹Nonempty T.left›
  obtain ⟨i, -⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).mp 𝒰.mem₀).1 x
  exact hle _ _ (by use i)

/-- **The unit `M ⟶ Γ(X, M_X)` is injective** on a nonempty scheme. -/
theorem injective_constantSheafΓAdj_unit_app [Nonempty X] (M : ModuleCat.{u + 1} Λ) :
    Function.Injective
      ((constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).unit.app M) := by
  have : Nonempty (⊤_ X.Etale).left :=
    ⟨(terminalIsTerminal.uniqueUpToIso (isTerminalEtaleMkId X)).inv.left
      (Classical.arbitrary X)⟩
  have h₁ := unit_comp_rightAdjointUniq_hom_app_constantSheafAdj (X := X) Λ terminalIsTerminal M
  have h₂ : Function.Injective ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
      terminalIsTerminal).unit.app M) := by
    rw [Stacks.ConstantSheaf.constantSheafAdj_unit_app]
    intro x y hxy
    by_contra hne
    apply bot_not_mem_smallEtaleTopology (⊤_ X.Etale)
    have : Presheaf.IsLocallyInjective X.smallEtaleTopology
        (toSheafify X.smallEtaleTopology ((Functor.const (X.Etale)ᵒᵖ).obj M)) :=
      Presheaf.isLocallyInjective_toSheafify'.{u + 1, u} X.smallEtaleTopology _
    have hS := Presheaf.equalizerSieve_mem X.smallEtaleTopology
      (toSheafify X.smallEtaleTopology ((Functor.const (X.Etale)ᵒᵖ).obj M)) x y hxy
    convert hS using 1
    ext V g
    simp only [Sieve.bot_apply, Presheaf.equalizerSieve_apply, Functor.const_obj_map, false_iff]
    exact hne
  rw [← h₁] at h₂
  exact Function.Injective.of_comp (f := ConcreteCategory.hom (((constantSheafΓAdj
    X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightAdjointUniq (constantSheafAdj
      X.smallEtaleTopology (ModuleCat.{u + 1} Λ) terminalIsTerminal)).hom.app
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) h₂

/-- **The counit `Γ(X, G)_X ⟶ G` is an isomorphism when `G` is isomorphic to a constant sheaf
whose unit is an isomorphism.** -/
theorem isIso_constantSheafΓAdj_counit_app_of_iso {G : EtaleModules.{u, 0} Λ X}
    {M : ModuleCat.{u + 1} Λ}
    (e : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M ≅ G)
    (hM : IsIso ((constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).unit.app M)) :
    IsIso ((constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G) := by
  let adj := constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  have : IsIso (adj.counit.app ((constantSheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).obj M)) :=
    IsIso.eq_inv_of_hom_inv_id (adj.left_triangle_components M) ▸ inferInstance
  have hc : adj.counit.app G = inv ((constantSheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).map ((Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map e.hom)) ≫
        adj.counit.app _ ≫ e.hom := by
    rw [IsIso.eq_inv_comp]
    exact adj.counit.naturality e.hom
  rw [hc]
  infer_instance

end Stacks.EtaleCohomology

end
