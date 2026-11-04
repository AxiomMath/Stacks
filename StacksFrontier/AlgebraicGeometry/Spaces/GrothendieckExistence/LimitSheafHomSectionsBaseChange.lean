module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.LimitTensorSectionsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackDualHom

/-!
# `RHom_X(E, K)` is perfect and its base change to `Aₙ` is `RHom_{Xₙ}(E|_{Xₙ}, Fₙ)`

In Situation [Stacks, Tag 0CX4] let `K = DQ_X(L)` for a derived limit `L = R lim (iₙ,* Fₙ)` and
`E` a perfect object of `D(𝒪_X)`, with `RHom_X(E, -) = RΓ(X, R𝓗om(E, -))` read in `D(A)`. This is
[Stacks, Tag 0CX6] (2), obtained from (1) at the dual `E^∨` by Stacks 08JJ, as the proof of the
tag indicates (Cohomology on Sites, Lemma 21.48.4):

* `R𝓗om(E, K) ≅ E^∨ ⊗^𝐋 K` on `X` and `R𝓗om(E|_{Xₙ}, Fₙ) ≅ (E|_{Xₙ})^∨ ⊗^𝐋 Fₙ` on `Xₙ`
  (Stacks 08JJ);
* `(E^∨)|_{Xₙ} ≅ (E|_{Xₙ})^∨` (`AlgebraicGeometry.Space.smallEtaleDerivedPullbackDualIso`).

The **canonical map** `RHom_X(E, K) ⊗^𝐋_A Aₙ ⟶ RHom_{Xₙ}(E|_{Xₙ}, Fₙ)` is the canonical map of (1)
at `E^∨` read through these identifications.

## Main definitions

* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.limitSheafHomSections`: `RHom_X(E, K)`.
* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.stageSheafHomSectionsTarget`:
  `RHom_{Xₙ}(E|_{Xₙ}, Fₙ)`.
* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.limitSheafHomSectionsBaseChangeMap`: the
  canonical map.

## Main results

* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.isPerfect_limitSheafHomSections_and_isIso_of`
  is [Stacks, Tag 0CX6] (2), given the two compatibilities of the transitions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry.Space

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u})
  {DQ : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left ⥤
    (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).FullSubcategory}
  (adj : (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι ⊣ DQ)
  (L : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left)
  (E : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left)

variable (DQ) in
/-- `RHom_X(E, K) = RΓ(X, R𝓗om(E, K))` in `D(A)`, for `K = DQ_X(L)`. -/
abbrev limitSheafHomSections :
    StacksDraft.ringDerivedCategory Γ((BigFppfOver.toScheme D.B D.S D.containsLimitBase).obj
      (limitBaseObject D.system D.B D.containsLimitBase), ⊤) :=
  (representedAffineDerivedSections D.B D.S D.containsLimitBase
      (limitBaseObject D.system D.B D.containsLimitBase)).obj
    ((derivedModulePushforward D.B D.S D.containsLimitBase D.X.hom).obj
      (((smallEtaleDerivedSheafHom D.B D.S D.containsLimitBase D.X.left).obj (op E)).obj
        ((spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι.obj (DQ.obj L))))

/-- `RHom_{Xₙ}(E|_{Xₙ}, Fₙ) = RΓ(Xₙ, R𝓗om(Liₙ^*E, Fₙ[0]))` in `D(Aₙ)`. -/
abbrev stageSheafHomSectionsTarget (n : ℕ) :
    StacksDraft.ringDerivedCategory Γ((BigFppfOver.toScheme D.B D.S D.containsLimitBase).obj
      (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n), ⊤) :=
  (representedAffineDerivedSections D.B D.S D.containsLimitBase
      (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)).obj
    ((derivedModulePushforward D.B D.S D.containsLimitBase (D.stageToBase n)).obj
      (((smallEtaleDerivedSheafHom D.B D.S D.containsLimitBase (D.stage n)).obj
          (op ((smallEtaleDerivedModulePullback D.B D.S D.containsLimitBase
            (D.closedImmersion n)).obj E))).obj
        ((spaceDerivedSingle D.B D.S D.containsLimitBase (D.stage n) 0).obj (D.F n))))

/-- **The canonical map of [Stacks, Tag 0CX6] (2)**,
`RHom_X(E, K) ⊗^𝐋_A Aₙ ⟶ RHom_{Xₙ}(E|_{Xₙ}, Fₙ)`, for a perfect `E`: the canonical map of
[Stacks, Tag 0CX6] (1) at `E^∨` (`limitTensorSectionsBaseChangeMap`), read through
`R𝓗om(E, K) ≅ E^∨ ⊗^𝐋 K`, `(E^∨)|_{Xₙ} ≅ (E|_{Xₙ})^∨` and
`(E|_{Xₙ})^∨ ⊗^𝐋 Fₙ ≅ R𝓗om(E|_{Xₙ}, Fₙ)` (Stacks 08JJ). -/
def limitSheafHomSectionsBaseChangeMap
    (hE : spaceIsPerfect D.B D.S D.containsLimitBase D.X.left E)
    (p : L ⟶ ∏ᶜ fun n : ℕ => D.derivedSystem.obj ⟨n⟩) (n : ℕ) :
    (StacksDraft.ringExtendScalars (representedAffineCommRingCatHom D.B D.S D.containsLimitBase
        (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)).hom).obj
        (D.limitSheafHomSections DQ L E) ⟶
      D.stageSheafHomSectionsTarget E n :=
  ((StacksDraft.ringExtendScalars (representedAffineCommRingCatHom D.B D.S D.containsLimitBase
      (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)).hom).mapIso
    ((derivedModulePushforward D.B D.S D.containsLimitBase D.X.hom ⋙
        representedAffineDerivedSections D.B D.S D.containsLimitBase
          (limitBaseObject D.system D.B D.containsLimitBase)).mapIso
      (smallEtaleDerivedSheafHomIsoTensorDual D.B D.S D.containsLimitBase D.X.left E
        ((spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι.obj (DQ.obj L)) hE))).hom ≫
    D.limitTensorSectionsBaseChangeMap adj L
      (smallEtaleDerivedDual D.B D.S D.containsLimitBase D.X.left E) p n ≫
    ((derivedModulePushforward D.B D.S D.containsLimitBase (D.stageToBase n) ⋙
        representedAffineDerivedSections D.B D.S D.containsLimitBase
          (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)).mapIso
      (((smallEtaleDerivedTensor D.B D.S D.containsLimitBase (D.stage n)).mapIso
          (smallEtaleDerivedPullbackDualIso (D.closedImmersion n) E hE)).app
          ((spaceDerivedSingle D.B D.S D.containsLimitBase (D.stage n) 0).obj (D.F n)) ≪≫
        (smallEtaleDerivedSheafHomIsoTensorDual D.B D.S D.containsLimitBase (D.stage n)
          ((smallEtaleDerivedModulePullback D.B D.S D.containsLimitBase
            (D.closedImmersion n)).obj E)
          ((spaceDerivedSingle D.B D.S D.containsLimitBase (D.stage n) 0).obj (D.F n))
          (isPerfect_smallEtaleDerivedModulePullback (D.closedImmersion n) E hE)).symm)).hom

/-- **[Stacks, Tag 0CX6] (2), given the two compatibilities of the transitions**: for a perfect
`E`, `RHom_X(E, K)` is perfect and the canonical map
`RHom_X(E, K) ⊗^𝐋_A Aₙ ⟶ RHom_{Xₙ}(E|_{Xₙ}, Fₙ)` is an isomorphism for every `n`, where
`K = DQ_X(L)` and `p` presents `L` as the derived limit of `(iₙ,* Fₙ)`. -/
theorem isPerfect_limitSheafHomSections_and_isIso_of
    (hE : spaceIsPerfect D.B D.S D.containsLimitBase D.X.left E)
    (p : L ⟶ ∏ᶜ fun n : ℕ => D.derivedSystem.obj ⟨n⟩)
    (hp : ∃ δ : (∏ᶜ fun n : ℕ => D.derivedSystem.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => D.derivedSystem.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ => D.derivedSystem.obj ⟨n⟩) (n + 1) ≫
          D.derivedSystem.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left))
    (hcc : ∀ n : ℕ, D.StageTransitionCounitCompatible n)
    (htr : ∀ n : ℕ, D.StageTensorSectionsTransitionCompatible
      (smallEtaleDerivedDual D.B D.S D.containsLimitBase D.X.left E) n) :
    StacksDraft.ringIsPerfect (D.limitSheafHomSections DQ L E) ∧
      ∀ n : ℕ, IsIso (D.limitSheafHomSectionsBaseChangeMap adj L E hE p n) := by
  have h := D.isPerfect_limitTensorSections_and_isIso_of adj L
    (smallEtaleDerivedDual D.B D.S D.containsLimitBase D.X.left E)
    (isPerfect_smallEtaleDerivedDual D.B D.S D.containsLimitBase D.X.left E hE) p hp hcc htr
  exact ⟨@StacksDraft.Perfect.isPerfect_of_iso _ _ (StacksDraft.ringHasDerivedCategory _) _ _
    ((derivedModulePushforward D.B D.S D.containsLimitBase D.X.hom ⋙
        representedAffineDerivedSections D.B D.S D.containsLimitBase
          (limitBaseObject D.system D.B D.containsLimitBase)).mapIso
      (smallEtaleDerivedSheafHomIsoTensorDual D.B D.S D.containsLimitBase D.X.left E
        ((spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι.obj (DQ.obj L)) hE))
    h.1, fun n => IsIso.comp_isIso' (Iso.isIso_hom _) (IsIso.comp_isIso' (h.2 n) (Iso.isIso_hom _))⟩

end FlatSheafExistenceSituation

end AlgebraicGeometry.Space
