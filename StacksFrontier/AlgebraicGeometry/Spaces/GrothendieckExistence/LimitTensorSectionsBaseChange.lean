module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.PerfectSectionsOfLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.TensorSectionsDerivedLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.StageTensorSectionsPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.StageTensorSectionsTransition
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.AffineBaseSectionsRingTower
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.PerfectOfIso

/-!
# `RΓ(X, E ⊗^𝐋 K)` is perfect and its base change to `Aₙ` is `RΓ(Xₙ, E|_{Xₙ} ⊗^𝐋 Fₙ)`

In Situation [Stacks, Tag 0CX4] let `K = DQ_X(L)` for a derived limit `L = R lim (iₙ,* Fₙ)` and
`E` a perfect object of `D(𝒪_X)`. Following the proof of [Stacks, Tag 0CX6]:

* `RΓ(X, E ⊗^𝐋 -)` carries the derived-limit triangle of `L` to a derived-limit triangle of the
  system `RΓ(X, E ⊗^𝐋 iₙ,* Fₙ) = Mₙ = RΓ(Xₙ, E|_{Xₙ} ⊗^𝐋 Fₙ)` in `D(A)`, and inverts the counit
  `K ⟶ L` (`FlatSheafExistenceSituation.tensorSections_derivedLimit_triangle`,
  `…isIso_tensorSectionsFunctor_map_counit`);
* the `Mₙ` are perfect (Stacks 0A1P) and `Mₙ₊₁ ⊗^𝐋_{Aₙ₊₁} Aₙ ≅ Mₙ`
  (`FlatSheafExistenceSituation.isIso_homEquiv_symm_stageTensorSectionsTransition`);
* so [Stacks, Tag 0CQG] applies to the tower `Aₙ` of Situation 0CX4.

The two inputs not yet available as theorems, the compatibility of the identifications
`RΓ(X, E ⊗^𝐋 iₙ,* Fₙ) ≅ Mₙ` with the transitions and the single-degree counit compatibility
`StageTransitionCounitCompatible`, are hypotheses of the intermediate result here.

## Main results

* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.isPerfect_limitTensorSections_and_isIso_of`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace CategoryTheory.Adjunction

variable {𝒜 ℬ 𝒞 : Type*} [Category* 𝒜] [Category* ℬ] [Category* 𝒞] {Lg : 𝒜 ⥤ ℬ} {Rg : ℬ ⥤ 𝒜}
  (ag : Lg ⊣ Rg) (G : 𝒞 ⥤ 𝒜)

/-- **The transpose of `G(u ≫ p ≫ πₙ) ≫ ψ`** is invertible when `G(u)` is and the transpose of
`(G(p) ≫ comparison) ≫ πₙ ≫ ψ` is: the first factor `G(p) ≫ comparison ≫ πₙ` is `G(p ≫ πₙ)`. -/
theorem isIso_homEquiv_symm_map_comp_pi_π {P : ℕ → 𝒞} [HasProduct P]
    [HasProduct fun n : ℕ => G.obj (P n)] {Y Z : 𝒞} (u : Y ⟶ Z) (p : Z ⟶ ∏ᶜ P) (n : ℕ)
    {W : ℬ} (ψ : G.obj (P n) ⟶ Rg.obj W) (hu : IsIso (G.map u))
    (h : IsIso ((ag.homEquiv _ _).symm
      ((G.map p ≫ piComparison G P) ≫ Pi.π (fun n : ℕ => G.obj (P n)) n ≫ ψ))) :
    IsIso ((ag.homEquiv _ _).symm (G.map (u ≫ p ≫ Pi.π P n) ≫ ψ)) := by
  have e : G.map (u ≫ p ≫ Pi.π P n) ≫ ψ =
      G.map u ≫ (G.map p ≫ piComparison G P) ≫ Pi.π (fun n : ℕ => G.obj (P n)) n ≫ ψ := by
    rw [Category.assoc, piComparison_comp_π_assoc, G.map_comp, G.map_comp, Category.assoc,
      Category.assoc]
  rw [e, Adjunction.homEquiv_naturality_left_symm]
  exact IsIso.comp_isIso' (Functor.map_isIso _ _) h

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Space

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u})
  {DQ : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left ⥤
    (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).FullSubcategory}
  (adj : (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι ⊣ DQ)
  (L : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left)
  (E : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left)

/-- **The identifications `RΓ(X, E ⊗^𝐋 iₙ,* Fₙ) ≅ RΓ(Xₙ, E|_{Xₙ} ⊗^𝐋 Fₙ)` are compatible with the
transitions**: `RΓ(X, E ⊗^𝐋 -)` of the transition `iₙ₊₁,* Fₙ₊₁ ⟶ iₙ,* Fₙ` corresponds to the
transition map `Mₙ₊₁ ⟶ Mₙ` read in `D(A)`. -/
def StageTensorSectionsTransitionCompatible (n : ℕ) : Prop :=
  (D.tensorSectionsFunctor E).map
      ((spaceDerivedSingle D.B D.S D.containsLimitBase D.X.left 0).map
        (D.pushforwardTransition n)) ≫
    D.stageTensorSectionsMap n E =
  D.stageTensorSectionsMap (n + 1) E ≫
    (StacksDraft.ringRestrictScalars (representedAffineCommRingCatHom D.B D.S D.containsLimitBase
        (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt (n + 1))).hom).map
      (D.stageTensorSectionsTransition n E) ≫
    (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u}
      (representedAffineCommRingCatHom D.B D.S D.containsLimitBase
        (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt (n + 1))).hom
      (representedAffineCommRingCatHom D.B D.S D.containsLimitBase
        (baseObjectTransition D.system D.B D.containsLimitBase D.containsBaseAt n)).hom
      (representedAffineCommRingCatHom D.B D.S D.containsLimitBase
        (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)).hom
      (D.stageRingHom_eq_comp n)).hom.app (D.stageTensorSectionsTarget n E)

/-- **[Stacks, Tag 0CX6] (1), given the two compatibilities of the transitions**: for a perfect
`E`, `RΓ(X, E ⊗^𝐋 K)` is perfect and the canonical map
`RΓ(X, E ⊗^𝐋 K) ⊗^𝐋_A Aₙ ⟶ RΓ(Xₙ, E|_{Xₙ} ⊗^𝐋 Fₙ)` is an isomorphism for every `n`, where
`K = DQ_X(L)` and `p` presents `L` as the derived limit of `(iₙ,* Fₙ)`. -/
theorem isPerfect_limitTensorSections_and_isIso_of
    (hE : spaceIsPerfect D.B D.S D.containsLimitBase D.X.left E)
    (p : L ⟶ ∏ᶜ fun n : ℕ => D.derivedSystem.obj ⟨n⟩)
    (hp : ∃ δ : (∏ᶜ fun n : ℕ => D.derivedSystem.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => D.derivedSystem.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ => D.derivedSystem.obj ⟨n⟩) (n + 1) ≫
          D.derivedSystem.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left))
    (hcc : ∀ n : ℕ, D.StageTransitionCounitCompatible n)
    (htr : ∀ n : ℕ, D.StageTensorSectionsTransitionCompatible E n) :
    StacksDraft.ringIsPerfect (D.limitTensorSections DQ L E) ∧
      ∀ n : ℕ, IsIso (D.limitTensorSectionsBaseChangeMap adj L E p n) := by
  obtain ⟨hprod, δ, hT⟩ := D.tensorSections_derivedLimit_triangle E hE L p hp
  have := hprod
  have hqc : QcohDerived D.B D.S D.containsLimitBase D.X.left E :=
    qcohDerived_of_isPerfect D.B D.S D.containsLimitBase D.X.left E hE
  have hψ : ∀ n : ℕ, IsIso (D.stageTensorSectionsMap n E) := fun n =>
    D.isIso_stageTensorSectionsMap n E hqc
  have hu := D.isIso_tensorSectionsFunctor_map_counit E hE adj L
  have key := StacksDraft.DerivedInverseLimit.isPerfect_and_isIso_derivedBaseChangeComparison_of_iso
    (baseSectionsSystem D.system) (baseSectionsCone D.system)
    (fun n => D.stageTensorSectionsTarget n E) (fun n => D.stageTensorSectionsTransition n E)
    (isLimitBaseSectionsCone D.system)
    (fun n => surjective_baseSectionsSystem_map D.system _ (D.transition_surjective n))
    (fun n => isLocallyNilpotent_ker_baseSectionsSystem_map D.system _
      (fun x hx => D.transition_locallyNilpotent n x hx))
    (fun n => D.ringIsPerfect_stageTensorSectionsTarget n E hE)
    (fun n => D.isIso_homEquiv_symm_stageTensorSectionsTransition n E hE (hcc n))
    (fun n => (D.tensorSectionsFunctor E).obj (D.derivedSystem.obj ⟨n⟩))
    (fun n => (D.tensorSectionsFunctor E).map (D.derivedSystem.map (homOfLE (Nat.le_succ n)).op))
    (fun n => @asIso _ _ _ _ (D.stageTensorSectionsMap n E) (hψ n))
    (fun n => by
      have h := htr n
      rw [StageTensorSectionsTransitionCompatible, ← pushforwardSystem_map_succ] at h
      exact h)
    _ _ δ hT
  refine ⟨@StacksDraft.Perfect.isPerfect_of_iso _ _ (StacksDraft.ringHasDerivedCategory _) _ _
    (@asIso _ _ _ _ ((D.tensorSectionsFunctor E).map (adj.counit.app L)) hu) key.1, fun n => ?_⟩
  exact CategoryTheory.Adjunction.isIso_homEquiv_symm_map_comp_pi_π
    (RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
      (representedAffineCommRingCatHom D.B D.S D.containsLimitBase
        (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)).hom)
    (D.tensorSectionsFunctor E) (adj.counit.app L) p n (D.stageTensorSectionsMap n E) hu (key.2 n)

/-- **[Stacks, Tag 0CX6] (1) for every perfect `E` at once, given the two compatibilities of the
transitions**: the canonical maps `RΓ(X, E ⊗^𝐋 K) ⊗^𝐋_A Aₙ ⟶ RΓ(Xₙ, E|_{Xₙ} ⊗^𝐋 Fₙ)` are
isomorphisms. -/
theorem isIso_limitTensorSectionsBaseChangeMap_of
    (p : L ⟶ ∏ᶜ fun n : ℕ => D.derivedSystem.obj ⟨n⟩)
    (hp : ∃ δ : (∏ᶜ fun n : ℕ => D.derivedSystem.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => D.derivedSystem.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ => D.derivedSystem.obj ⟨n⟩) (n + 1) ≫
          D.derivedSystem.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left))
    (hcc : ∀ n : ℕ, D.StageTransitionCounitCompatible n)
    (htr : ∀ (E : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left) (n : ℕ),
      D.StageTensorSectionsTransitionCompatible E n) (n : ℕ) :
    ∀ E : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left,
      spaceIsPerfect D.B D.S D.containsLimitBase D.X.left E →
        IsIso (D.limitTensorSectionsBaseChangeMap adj L E p n) := fun E hE =>
  (D.isPerfect_limitTensorSections_and_isIso_of adj L E hE p hp hcc (htr E)).2 n

/-- **[Stacks, Tag 0CX6] (1) at a derived limit, given the two compatibilities of the
transitions**: if `L` is a derived limit of `(iₙ,* Fₙ)` then, for the first component `p` of a
presentation of `L` as such, `RΓ(X, E ⊗^𝐋 K)` is perfect and the canonical maps
`RΓ(X, E ⊗^𝐋 K) ⊗^𝐋_A Aₙ ⟶ RΓ(Xₙ, E|_{Xₙ} ⊗^𝐋 Fₙ)` are isomorphisms for every perfect `E`. -/
theorem isPerfect_limitTensorSections_and_isIso_of_isDerivedLimit_of
    (hL : IsDerivedLimit D.derivedSystem L)
    (hcc : ∀ n : ℕ, D.StageTransitionCounitCompatible n)
    (htr : ∀ (E : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left) (n : ℕ),
      D.StageTensorSectionsTransitionCompatible E n) :
    ∃ p : L ⟶ ∏ᶜ fun n : ℕ => D.derivedSystem.obj ⟨n⟩,
      (∃ δ : (∏ᶜ fun n : ℕ => D.derivedSystem.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
        Triangle.mk p (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => D.derivedSystem.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ => D.derivedSystem.obj ⟨n⟩) (n + 1) ≫
            D.derivedSystem.map (homOfLE (Nat.le_succ n)).op) δ ∈
          distTriang (spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left)) ∧
      ∀ (n : ℕ) (E : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left),
        spaceIsPerfect D.B D.S D.containsLimitBase D.X.left E →
          StacksDraft.ringIsPerfect (D.limitTensorSections DQ L E) ∧
            IsIso (D.limitTensorSectionsBaseChangeMap adj L E p n) := by
  obtain ⟨p, δ, hT⟩ := hL
  exact ⟨p, ⟨δ, hT⟩, fun n E hE =>
    (D.isPerfect_limitTensorSections_and_isIso_of adj L E hE p ⟨δ, hT⟩ hcc (htr E)).imp_right
      (· n)⟩

include adj in
/-- **`RΓ(X, E ⊗^𝐋 K)` is perfect for every perfect `E`** ([Stacks, Tag 0CX6] (1), perfectness),
for `K = DQ_X(L)` and `L` a derived limit of `(iₙ,* Fₙ)`, given the two compatibilities of the
transitions. -/
theorem ringIsPerfect_limitTensorSections_of (hL : IsDerivedLimit D.derivedSystem L)
    (hcc : ∀ n : ℕ, D.StageTransitionCounitCompatible n)
    (htr : ∀ (E : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left) (n : ℕ),
      D.StageTensorSectionsTransitionCompatible E n) :
    ∀ E : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left,
      spaceIsPerfect D.B D.S D.containsLimitBase D.X.left E →
        StacksDraft.ringIsPerfect (D.limitTensorSections DQ L E) := by
  obtain ⟨p, δ, hT⟩ := hL
  exact fun E hE => (D.isPerfect_limitTensorSections_and_isIso_of adj L E hE p ⟨δ, hT⟩ hcc
    (htr E)).1

end FlatSheafExistenceSituation

end AlgebraicGeometry.Space
