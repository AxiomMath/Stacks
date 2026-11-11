module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceAffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceBoundedLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceEtaleSectionsHocolim
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistencePseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceTensorSectionsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceTheorem
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceTowerConjugate
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# The derived Grothendieck existence theorem for algebraic spaces

In Situation [Stacks, Tag 0DIK] let `K = DQ_X(R lim Kₙ)` be the object of [Stacks, Tag 0DIL],
for the chosen coherator `DQ_X`, and `τₙ : Ljₙ^* K ⟶ Kₙ` the adjoint of the projection
`K ⟶ Rjₙ,* Kₙ`. The proof of the derived Grothendieck existence theorem [Stacks, Tag 0DIQ] reads:
"Apply Lemmas 0DIL, 0DIM, 0DIN to get a pseudo-coherent object `K` of `D(𝒪_X)`. Choosing affine
`U` in Lemma 0DIP it follows immediately that `K` restricts to `Kₙ` over `Xₙ`."

This file carries out that proof. "Choosing affine `U`": for `j : U ⟶ X` étale with `U` affine,
the canonical map `RΓ(U, K) ⊗^L_A Aₙ ⟶ RΓ(Uₙ, Kₙ)` of [Stacks, Tag 0DIP] is the base change map
of `RΓ` (invertible, `U` being flat over `A`), followed by the restriction-identification
isomorphism, followed by `RΓ(Uₙ, τₙ|_{Uₙ})`; so `RΓ(Uₙ, τₙ|_{Uₙ})` is invertible, and then `τₙ` is
(`isIso_coheratorLimitPullbackMap_of_forall_isAffineSpace`, through an affine étale atlas of the
quasi-compact `X`). The `τₙ` are compatible with the `φₙ` by the conjugate identity of the
composition isomorphisms (`conjugateEquiv_stageDerivedPullbackCompIso_hom`).

## Main results

* `…isIso_etaleStageSections_map_of_isIso_etaleSectionsBaseChangeMap`: if the canonical map of
  Stacks 0DIP is invertible, so is `RΓ_{Aₙ}(Uₙ, τₙ|_{Uₙ})`.
* `…isIso_coheratorLimitPullbackMap_of_forall_isIso_etaleSectionsBaseChangeMap`: every `τₙ` is
  invertible once the canonical map of Stacks 0DIP is, for every affine `U` étale over `X`.
* `…isIso_coheratorLimitPullbackMap`: every `τₙ` is invertible, for every coherator, with no
  hypothesis: the input from [Stacks, Tag 0DIM] is discharged by
  `…isIso_stageSections_map_tensor_coheratorLimitPullbackMap`.
* `…exists_isPseudoCoherent_isCompatibleRestriction_of_forall`: the conclusion of Stacks 0DIQ,
  from the statement of [Stacks, Tag 0DIN] (`h0DIN`) and the part of [Stacks, Tag 0DIM] that
  Stacks 0DIP uses (`h0DIM`). Both inputs are proved in the library: 0DIN is
  `…isPseudoCoherentOnLimit_coheratorObj` and 0DIM is
  `…isPseudoCoherent_and_isIso_stageTensorSectionsBaseChange`; the unconditional form is
  `…exists_isPseudoCoherent_stageDerivedPullback_iso`.
* `…exists_isPseudoCoherent_stageDerivedPullback_iso`: **[Stacks, Tag 0DIQ]**, the derived
  Grothendieck existence theorem.

## References

* [Stacks Project, Tag 0DIQ](https://stacks.math.columbia.edu/tag/0DIQ)
* [Stacks Project, Tag 0DIP](https://stacks.math.columbia.edu/tag/0DIP)
* [Stacks Project, Tag 0DIN](https://stacks.math.columbia.edu/tag/0DIN)
* [Stacks Project, Tag 0DIM](https://stacks.math.columbia.edu/tag/0DIM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace SeparatedDerivedExistenceSystem

variable (D : SeparatedDerivedExistenceSystem.{u})

section Coherator

variable (DQ : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left ⥤
    (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).FullSubcategory)
  (adj : (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι ⊣ DQ)

/-- **`RΓ_{Aₙ}(Uₙ, τₙ|_{Uₙ})` is invertible when the canonical map of Stacks 0DIP is**, for
`j : U ⟶ X` étale with `U` quasi-compact and quasi-separated. The canonical map
`RΓ_A(U, K) ⊗^L_A Aₙ ⟶ RΓ_{Aₙ}(Uₙ, Kₙ)` is the base change map of `RΓ` along
`Spec Aₙ ⟶ Spec A` at `K|_U` (invertible, `U` being flat over `A`), followed by `RΓ_{Aₙ}(Uₙ, -)`
of the isomorphism `qₙ^*(K|_U) ≅ jₙ^*(K|_{Xₙ})`, followed by `RΓ_{Aₙ}(Uₙ, τₙ|_{Uₙ})`. -/
theorem isIso_etaleStageSections_map_of_isIso_etaleSectionsBaseChangeMap
    {U : AlgebraicSpaces D.B (limitBase D.system) D.containsLimitBase} (j : U ⟶ D.X.left)
    (hj : IsEtale D.B (limitBase D.system) D.containsLimitBase j.hom)
    (hUqc : IsQuasiCompactSpace D.B (limitBase D.system) D.containsLimitBase U.1)
    (hUqs : IsAbsolutelyQuasiSeparated D.B (limitBase D.system) D.containsLimitBase
      D.B.contains_terminal U.1) (n : ℕ)
    (h : IsIso (D.etaleSectionsBaseChangeMap j DQ adj n)) :
    IsIso ((representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
        (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)).map
      ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
          (D.etaleStageBaseProjection j n)).map
        ((smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase
          (D.etaleStageToStage j n)).map (D.coheratorLimitPullbackMap DQ adj n)))) := by
  have h₁ := isIso_etaleStageSectionsBaseChangeMap hj hUqc hUqs n _
    (derivedQuasicoherent_smallEtaleDerivedModulePullback D.B (limitBase D.system)
      D.containsLimitBase j _ (D.coheratorLimit DQ).property)
  -- Cancel the first two factors of the canonical map as it is elaborated (every object and
  -- morphism is solved by unification from its unfolded definition, so that no restated factor
  -- has to be compared with it).
  have h' := h
  unfold etaleSectionsBaseChangeMap at h'
  have h₃ := @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ h₁ h'
  have h₄ := @IsIso.of_isIso_comp_left _ _ _ _ _ _ _
    (@Functor.map_isIso _ _ _ _ _ _ _ _ (NatIso.hom_app_isIso _ _)) h₃
  exact h₄

/-- **Every `τₙ` is invertible once the canonical map of Stacks 0DIP is, for every affine `U`
étale over `X`** ("choosing affine `U` in Lemma 0DIP", Stacks 0DIQ): an affine `U` is
quasi-compact and quasi-separated, so `RΓ_{Aₙ}(Uₙ, τₙ|_{Uₙ})` is invertible
(`isIso_etaleStageSections_map_of_isIso_etaleSectionsBaseChangeMap`), and then so is `τₙ`
(`isIso_coheratorLimitPullbackMap_of_forall_isAffineSpace`). -/
theorem isIso_coheratorLimitPullbackMap_of_forall_isIso_etaleSectionsBaseChangeMap
    (h : ∀ (n : ℕ) (U : AlgebraicSpaces D.B (limitBase D.system) D.containsLimitBase)
      (j : U ⟶ D.X.left), IsEtale D.B (limitBase D.system) D.containsLimitBase j.hom →
      IsAffineSpace D.B (limitBase D.system) D.containsLimitBase U.1 →
      IsIso (D.etaleSectionsBaseChangeMap j DQ adj n))
    (n : ℕ) : IsIso (D.coheratorLimitPullbackMap DQ adj n) :=
  D.isIso_coheratorLimitPullbackMap_of_forall_isAffineSpace DQ adj (fun m U j hj hU =>
    D.isIso_etaleStageSections_map_of_isIso_etaleSectionsBaseChangeMap DQ adj j hj
      hU.isQuasiCompactSpace
      (isAbsolutelyQuasiSeparated_of_isAffineSpace D.B (limitBase D.system) D.containsLimitBase
        D.B.contains_terminal hU) m (h m U j hj hU)) n

/-- **Every `τₙ` is invertible, given the part of Stacks 0DIM that Stacks 0DIP uses**: if for
every `n` and every perfect `E` on `X` the map `RΓ_{Aₙ}(Xₙ, Lpₙ^*E ⊗^L τₙ)` is invertible, then
the canonical map of Stacks 0DIP is invertible for every `j : U ⟶ X` étale with `U` affine
(`isIso_etaleSectionsBaseChangeMap_of_isIso`), hence every `τₙ` is. The hypothesis is proved
([Stacks, Tag 0DIM], `isPseudoCoherent_and_isIso_stageTensorSectionsBaseChange`): the
unconditional form is `isIso_coheratorLimitPullbackMap`. -/
theorem isIso_coheratorLimitPullbackMap_of_forall_isPerfect
    (h0DIM : ∀ (n : ℕ) (E : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase
        D.X.left),
      spaceIsPerfect D.B (limitBase D.system) D.containsLimitBase D.X.left E →
      IsIso ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
          (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n) ⋙
        representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
          (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)).map
        (((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase (D.stage n)).obj
          ((D.stageDerivedPullback n).obj E)).map (D.coheratorLimitPullbackMap DQ adj n))))
    (n : ℕ) : IsIso (D.coheratorLimitPullbackMap DQ adj n) :=
  D.isIso_coheratorLimitPullbackMap_of_forall_isIso_etaleSectionsBaseChangeMap DQ adj
    (fun m U j hj hU =>
      isIso_etaleSectionsBaseChangeMap_of_isIso (D := D) (U := U) (j := j) DQ adj hj
        hU.isQuasiCompactSpace
        (isAbsolutelyQuasiSeparated_of_isAffineSpace D.B (limitBase D.system)
          D.containsLimitBase D.B.contains_terminal hU) m (h0DIM m)) n

end Coherator

/-- **The derived Grothendieck existence theorem (Stacks 0DIQ), from 0DIN and 0DIM.** In
Situation 0DIK let `K = DQ_X(R lim Kₙ)`, for the chosen coherator `DQ_X` and derived limit.
Assume the statement `h0DIN` of [Stacks, Tag 0DIN] (for every coherator `DQ` and every derived
limit `L` of the tower `Rjₙ,* Kₙ`, `DQ(L)` is pseudo-coherent on `X`; the shape of
`isPseudoCoherentOnLimit_coheratorObj_of_forall_isDerivedLimit`), and the part `h0DIM` of
[Stacks, Tag 0DIM] that Stacks 0DIP uses (for every perfect `E` on `X`,
`RΓ_{Aₙ}(Xₙ, Lpₙ^*E ⊗^L τₙ)` is invertible; the hypothesis of
`isIso_etaleSectionsBaseChangeMap_of_isIso`). Then there is a pseudo-coherent `K` in `D(𝒪_X)` with
isomorphisms `ψₙ : Ljₙ^* K ≅ Kₙ`, compatible with the `φₙ`:
`ψₙ = (Ljₙ^* ≅ Liₙ^* Ljₙ₊₁^*) ≫ Liₙ^* ψₙ₊₁ ≫ φₙ`. Both hypotheses are proved in the library
(0DIN: `isPseudoCoherentOnLimit_coheratorObj`; 0DIM:
`isPseudoCoherent_and_isIso_stageTensorSectionsBaseChange`), and the unconditional statement is
`exists_isPseudoCoherent_stageDerivedPullback_iso`. -/
theorem exists_isPseudoCoherent_isCompatibleRestriction_of_forall
    (h0DIN : ∀ (DQ : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left ⥤
        (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
          D.X.left).FullSubcategory)
      (_ : (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι ⊣ DQ)
      (L : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left),
      IsDerivedLimit D.spaceTower L →
      D.IsPseudoCoherentOnLimit
        ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι.obj
          (DQ.obj L)))
    (h0DIM : ∀ (n : ℕ) (E : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase
        D.X.left),
      spaceIsPerfect D.B (limitBase D.system) D.containsLimitBase D.X.left E →
      IsIso ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
          (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n) ⋙
        representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
          (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)).map
        (((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase (D.stage n)).obj
          ((D.stageDerivedPullback n).obj E)).map
            (D.coheratorLimitPullbackMap D.coherator D.coheratorAdjunction n)))) :
    ∃ (K : D.limitDerivedCategory) (ψ : ∀ n : ℕ, (D.stageDerivedPullback n).obj K ≅ D.K n),
      D.IsPseudoCoherentOnLimit K ∧ D.IsCompatibleRestriction fun n => (ψ n).hom :=
  D.exists_isPseudoCoherent_of_isIso D.coherator D.coheratorAdjunction
    (h0DIN D.coherator D.coheratorAdjunction D.derivedLimit D.isDerivedLimit_derivedLimit)
    (fun n => D.conjugateEquiv_stageDerivedPullbackCompIso_hom n)
    (D.isIso_coheratorLimitPullbackMap_of_forall_isPerfect D.coherator D.coheratorAdjunction
      h0DIM)

section Sections

/- The derived sections `RΓ(X, -)` into `D(A)` of [Stacks, Tag 0DIM] are read at the standard model
of `D(A)`, as in `isPseudoCoherentOnLimit_coheratorObj_of_forall_isDerivedLimit`. -/
attribute [local instance] HasDerivedCategory.standard

/-- **The derived Grothendieck existence theorem (Stacks 0DIQ), from the two halves of 0DIM.**
In Situation 0DIK take as hypotheses the two statements of [Stacks, Tag 0DIM] for every perfect
`E` on `X` (both are proved in the library, as
`isPseudoCoherent_and_isIso_stageTensorSectionsBaseChange`; the unconditional statement is
`exists_isPseudoCoherent_stageDerivedPullback_iso`):
`h0DIMpc`, that `RΓ(X, E ⊗^𝐋 K)` is pseudo-coherent in `D(A)` for every derived limit `K` of the
tower `Rjₙ,* Kₙ` in `D_QCoh(𝒪_X)`, and `h0DIM`, that `RΓ_{Aₙ}(Xₙ, Lpₙ^*E ⊗^L τₙ)` is invertible
(the form [Stacks, Tag 0DIP] uses). Then there is a pseudo-coherent `K` in `D(𝒪_X)` with
isomorphisms `ψₙ : Ljₙ^* K ≅ Kₙ`, compatible with the `φₙ`:
`ψₙ = (Ljₙ^* ≅ Liₙ^* Ljₙ₊₁^*) ≫ Liₙ^* ψₙ₊₁ ≫ φₙ`. This is
`exists_isPseudoCoherent_isCompatibleRestriction_of_forall` with [Stacks, Tag 0DIN] given by
`isPseudoCoherentOnLimit_coheratorObj_of_forall_isDerivedLimit`. -/
theorem exists_isPseudoCoherent_isCompatibleRestriction_of_isPseudoCoherent_of_isIso
    (h0DIMpc : ∀ (_ : HasProduct fun n : ℕ => D.quasicoherentTower.obj ⟨n⟩)
      (K : (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
        D.X.left).FullSubcategory),
      IsDerivedLimit D.quasicoherentTower K →
      ∀ E : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left,
      spaceIsPerfect D.B (limitBase D.system) D.containsLimitBase D.X.left E →
        StacksDraft.PseudoCoherence.IsPseudoCoherent
          ((D.limitTensorSections E).obj
            ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
              D.X.left).ι.obj K)))
    (h0DIM : ∀ (n : ℕ) (E : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase
        D.X.left),
      spaceIsPerfect D.B (limitBase D.system) D.containsLimitBase D.X.left E →
      IsIso ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
          (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n) ⋙
        representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
          (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)).map
        (((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase (D.stage n)).obj
          ((D.stageDerivedPullback n).obj E)).map
            (D.coheratorLimitPullbackMap D.coherator D.coheratorAdjunction n)))) :
    ∃ (K : D.limitDerivedCategory) (ψ : ∀ n : ℕ, (D.stageDerivedPullback n).obj K ≅ D.K n),
      D.IsPseudoCoherentOnLimit K ∧ D.IsCompatibleRestriction fun n => (ψ n).hom :=
  D.exists_isPseudoCoherent_isCompatibleRestriction_of_forall
    (D.isPseudoCoherentOnLimit_coheratorObj_of_forall_isDerivedLimit h0DIMpc) h0DIM

/-- **The derived Grothendieck existence theorem for `X` separated over `A`, given the
pseudo-coherence of the `Mₙ`.** In the situation of
`AlgebraicGeometry.Space.SeparatedDerivedExistenceSystem`, if `RΓ(Xₙ, Lpₙ^*E ⊗^L Kₙ)` is
pseudo-coherent for every perfect `E` and every `n`, then there is a pseudo-coherent `K` in
`D(𝒪_X)` with isomorphisms `ψₙ : Ljₙ^* K ≅ Kₙ` such that
`ψₙ = (Ljₙ^* ≅ Liₙ^* Ljₙ₊₁^*) ≫ Liₙ^* ψₙ₊₁ ≫ φₙ`. The proof is the source's proof of
Stacks 0DIQ, in which properness of `X` enters only through that pseudo-coherence. -/
theorem exists_isPseudoCoherent_stageDerivedPullback_iso_of_stageSectionsPseudoCoherent
    (hpc : D.StageSectionsPseudoCoherent) :
    ∃ (K : D.limitDerivedCategory) (ψ : ∀ n : ℕ, (D.stageDerivedPullback n).obj K ≅ D.K n),
      D.IsPseudoCoherentOnLimit K ∧
        ∀ n : ℕ, (ψ n).hom = (D.stageDerivedPullbackCompIso n).inv.app K ≫
          (transitionDerivedPullback D.system D.B D.containsLimitBase D.containsBaseAt D.X n).map
            (ψ (n + 1)).hom ≫ D.φ n :=
  D.exists_isPseudoCoherent_isCompatibleRestriction_of_isPseudoCoherent_of_isIso
    (fun hp K hK E hE => D.isPseudoCoherent_limitTensorSections_of_isDerivedLimit hpc hp K hK E hE)
    (fun n E hE => D.isIso_stageSections_map_tensor_coheratorLimitPullbackMap D.coherator
      D.coheratorAdjunction hpc n E hE)

end Sections

end SeparatedDerivedExistenceSystem

namespace DerivedExistenceSystem

/-- **Every `τₙ : Ljₙ^* K ⟶ Kₙ` is invertible**, for every coherator `adj : ι ⊣ DQ_X` and
`K = DQ_X(R lim Kₙ)`: `isIso_coheratorLimitPullbackMap_of_forall_isPerfect` with its hypothesis
discharged by [Stacks, Tag 0DIM]
(`isIso_stageSections_map_tensor_coheratorLimitPullbackMap`). -/
theorem isIso_coheratorLimitPullbackMap (D : DerivedExistenceSystem.{u})
    (DQ : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left ⥤
      (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
        D.X.left).FullSubcategory)
    (adj : (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι ⊣ DQ)
    (n : ℕ) : IsIso (D.toSeparated.coheratorLimitPullbackMap DQ adj n) :=
  D.toSeparated.isIso_coheratorLimitPullbackMap_of_forall_isPerfect DQ adj
    (fun m E hE => D.toSeparated.isIso_stageSections_map_tensor_coheratorLimitPullbackMap DQ adj
      D.stageSectionsPseudoCoherent m E hE) n

/-- **The derived Grothendieck existence theorem.** In Situation 0DIK there is a
pseudo-coherent `K` in `D(𝒪_X)` with `Kₙ = K ⊗^L_{𝒪_X} 𝒪_{Xₙ}` for all `n`, compatibly with the
maps `φₙ`: isomorphisms `ψₙ : Ljₙ^* K ≅ Kₙ` (`Ljₙ^*` the derived pullback along `jₙ : Xₙ ⟶ X`) with
`ψₙ = (Ljₙ^* ≅ Liₙ^* Ljₙ₊₁^*) ≫ Liₙ^* ψₙ₊₁ ≫ φₙ`, where `Ljₙ^* ≅ Liₙ^* Ljₙ₊₁^*` is the composition
isomorphism of derived pullbacks along `iₙ ≫ jₙ₊₁ = jₙ`.

Proof as in the source: `K = DQ_X(R lim Kₙ)` is pseudo-coherent by [Stacks, Tag 0DIN] (from both
halves of [Stacks, Tag 0DIM]), and the maps `τₙ : Ljₙ^* K ⟶ Kₙ` are isomorphisms by
[Stacks, Tag 0DIP] over affine `U` étale over `X`, compatible with the `φₙ`. -/
@[stacks 0DIQ "the full statement in Situation 0DIK with no further hypotheses: a pseudo-coherent \
  K on X with isomorphisms Lj_n^* K = K_n for all n, compatible with the phi_n through the \
  composition isomorphism of derived pullbacks"]
theorem exists_isPseudoCoherent_stageDerivedPullback_iso (D : DerivedExistenceSystem.{u}) :
    ∃ (K : D.limitDerivedCategory) (ψ : ∀ n : ℕ, (D.stageDerivedPullback n).obj K ≅ D.K n),
      D.IsPseudoCoherentOnLimit K ∧
        ∀ n : ℕ, (ψ n).hom = (D.stageDerivedPullbackCompIso n).inv.app K ≫
          (transitionDerivedPullback D.system D.B D.containsLimitBase D.containsBaseAt D.X n).map
            (ψ (n + 1)).hom ≫ D.φ n :=
  D.toSeparated.exists_isPseudoCoherent_stageDerivedPullback_iso_of_stageSectionsPseudoCoherent
    D.stageSectionsPseudoCoherent

end DerivedExistenceSystem


end AlgebraicGeometry.Space

end
