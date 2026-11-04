module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.RelativePseudoCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedChow.RelativePseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PseudoCoherentSectionsTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.PerfectSectionsOfLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.LimitTensorSectionsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.FlatSheafDerivedLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceDerivedCategoryPerfect

/-!
# [Stacks, Tag 0CX7]: relative pseudo-coherence of `K` from perfectness of `RΓ(X, E ⊗ K)`

In Situation [Stacks, Tag 0CX4] let `K = DQ_X(L)` be the object of [Stacks, Tag 0CX5]. The proof of
[Stacks, Tag 0CX7] combines [Stacks, Tag 0CX6] (1), that `RΓ(X, E ⊗^𝐋 K)` is perfect in `D(A)` for
every perfect `E`, with [Stacks, Tag 0CWH] (`K` being bounded above by [Stacks, Tag 0CX5]) to get
`RΓ(X, E ⊗^𝐋 K)` pseudo-coherent for every pseudo-coherent `E`, and concludes by
[Stacks, Tag 0CTT].

## Main results

* `FlatSheafExistenceSituation.isRelativelyPseudoCoherent_coheratorObj_of_ringIsPerfect`:
  `K` is pseudo-coherent relative to `A` once `RΓ(X, E ⊗^𝐋 K)` is perfect for every perfect `E`.
* `FlatSheafExistenceSituation.isRelativelyPseudoCoherent_coheratorObj_of_transitionCompatible`:
  the same, from the two compatibilities of the transitions under which the perfectness half of
  [Stacks, Tag 0CX6] (1) holds.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u})

attribute [local instance] HasDerivedCategory.standard

/-- The structure morphism `X ⟶ Spec A` of Situation 0CX4 is the unique morphism to the base. -/
theorem hom_eq_toBase : D.X.hom = DerivedChow.toBase D.B D.S D.containsLimitBase D.X.left :=
  ObjectProperty.hom_ext _ ((isTerminal_yoneda_obj_base D.B D.S D.containsLimitBase).hom_ext _ _)

/-- **The proof of [Stacks, Tag 0CX7] from [Stacks, Tag 0CX6] (1).**  In Situation 0CX4 let
`K = DQ_X(L)` be the object of [Stacks, Tag 0CX5], for a coherator `adj : ι ⊣ DQ_X` and a derived
limit `L` of `(iₙ,* Fₙ)`.  If `RΓ(X, E ⊗^𝐋 K)` is perfect in `D(A)` for every perfect `E` in
`D(𝒪_X)` (the first half of [Stacks, Tag 0CX6] (1)), then `K` is pseudo-coherent relative to `A`:
by [Stacks, Tag 0CWH], `K` being bounded above ([Stacks, Tag 0CX5]), `RΓ(X, E ⊗^𝐋 K)` is
pseudo-coherent for every pseudo-coherent `E`, and [Stacks, Tag 0CTT] applies. -/
theorem isRelativelyPseudoCoherent_coheratorObj_of_ringIsPerfect
    {DQ : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left ⥤
      (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).FullSubcategory}
    (adj : (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι ⊣ DQ)
    (L : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left)
    (hL : IsDerivedLimit D.derivedSystem L)
    (h : ∀ E : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left,
      spaceIsPerfect D.B D.S D.containsLimitBase D.X.left E →
        StacksDraft.ringIsPerfect (D.limitTensorSections DQ L E)) :
    IsRelativelyPseudoCoherent D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2 D.X.hom.hom
      D.isLocallyOfFiniteType_structureMorphism (D.coheratorObj DQ L) := by
  have : IsAffine ((BigFppfOver.toScheme D.B D.S D.containsLimitBase).obj
      (baseSiteObj D.B D.S D.containsLimitBase)) := D.isAffine_limitBaseObject
  obtain ⟨-, -, h0CX5, -⟩ := D.derivedLimit_bounded
  obtain ⟨-, -, c, hc⟩ := h0CX5 DQ adj L hL
  have hX := D.hom_eq_toBase
  have hsep : IsSeparated D.B D.S D.containsLimitBase
      (DerivedChow.toBase D.B D.S D.containsLimitBase D.X.left).hom := hX ▸ D.separated
  have hfp : IsFinitePresentation D.B D.S D.containsLimitBase
      (DerivedChow.toBase D.B D.S D.containsLimitBase D.X.left).hom := hX ▸ D.finitePresentation
  have hKb : ∃ b : ℤ, (D.coheratorObj DQ L).obj.IsLE b :=
    ⟨c, (DerivedCategory.isLE_iff _ c).2 fun i hi => hc i hi⟩
  have hperf : ∀ E : DerivedCategory
      (Modules.{u, u} D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2),
      (smallEtaleRingedSite D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2).IsPerfect E →
        StacksDraft.PseudoCoherence.IsPseudoCoherent
          ((representedAffineDerivedSections D.B D.S D.containsLimitBase
            (baseSiteObj D.B D.S D.containsLimitBase)).obj
            ((derivedModulePushforward D.B D.S D.containsLimitBase
              (DerivedChow.toBase D.B D.S D.containsLimitBase D.X.left)).obj
              (((smallEtaleDerivedTensor D.B D.S D.containsLimitBase D.X.left).obj E).obj
                (D.coheratorObj DQ L).obj))) := by
    intro E hE
    have := h E hE
    rw [limitTensorSections, hX] at this
    exact StacksDraft.Perfect.isPseudoCoherent_of_isPerfect.{u, u} _ this
  have hpc := fun E hE => isPseudoCoherent_representedAffineDerivedSections_tensor
    (U := baseSiteObj D.B D.S D.containsLimitBase)
    (DerivedChow.toBase D.B D.S D.containsLimitBase D.X.left) D.isQuasiCompactSpace
    D.isAbsolutelyQuasiSeparated (D.coheratorObj DQ L).obj (D.coheratorObj DQ L).property hKb
    hperf E hE
  have h0CTT' : ∀ (R : CommRingCat.{u}) (hR : D.B.Contains (Spec R))
      [IsAffine ((BigFppfOver.toScheme D.B (Spec R) hR).obj (baseSiteObj D.B (Spec R) hR))]
      (X : AlgebraicSpaces D.B (Spec R) hR)
      (_ : IsSeparated D.B _ hR (DerivedChow.toBase D.B _ hR X).hom)
      (hfp : IsFinitePresentation D.B _ hR (DerivedChow.toBase D.B _ hR X).hom)
      (K : DerivedCategory (Modules.{u, u} D.B _ hR X.1 X.2)) (hK : QcohDerived D.B _ hR X K)
      (_ : ∀ E : DerivedCategory (Modules.{u, u} D.B _ hR X.1 X.2),
        (smallEtaleRingedSite D.B _ hR X.1 X.2).IsPseudoCoherent E →
          StacksDraft.PseudoCoherence.IsPseudoCoherent
            ((representedAffineDerivedSections D.B _ hR (baseSiteObj D.B _ hR)).obj
              ((derivedModulePushforward D.B _ hR (DerivedChow.toBase D.B _ hR X)).obj
                (((smallEtaleDerivedTensor D.B _ hR X).obj E).obj K)))),
      IsRelativelyPseudoCoherent D.B _ hR X.1 X.2 (DerivedChow.toBase D.B _ hR X).hom
        (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation D.B _ hR hfp.1) ⟨K, hK⟩ :=
    fun R hR _ X hsep hfp K hK h =>
      isRelativelyPseudoCoherent_of_isPseudoCoherent_derivedSections_tensor D.B (A := R) hR
        hsep hfp K hK h
  have h0CTT := h0CTT' (limit D.system) D.containsLimitBase D.X.left hsep hfp
    (D.coheratorObj DQ L).obj (D.coheratorObj DQ L).property hpc
  have key : ∀ (g : D.X.left ⟶ schemeSpace (baseSiteObj D.B D.S D.containsLimitBase))
      (_ : g = DerivedChow.toBase D.B D.S D.containsLimitBase D.X.left)
      (hg : IsLocallyOfFiniteType D.B D.S D.containsLimitBase g.hom),
      IsRelativelyPseudoCoherent D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2 g.hom hg
        (D.coheratorObj DQ L) := by
    rintro g rfl hg
    exact h0CTT
  exact key D.X.hom hX _

/-- **[Stacks, Tag 0CX7], given the two compatibilities of the transitions.**  In Situation 0CX4
let `K = DQ_X(L)` be the object of [Stacks, Tag 0CX5], for a coherator `adj : ι ⊣ DQ_X` and a
derived limit `L` of `(iₙ,* Fₙ)`.  Then `K` is pseudo-coherent relative to `A`, provided the
transitions of the system satisfy `hcc` and `htr`, the two compatibilities under which the
perfectness half of [Stacks, Tag 0CX6] (1) holds
(`AlgebraicGeometry.Space.FlatSheafExistenceSituation.ringIsPerfect_limitTensorSections_of`). -/
theorem isRelativelyPseudoCoherent_coheratorObj_of_transitionCompatible
    {DQ : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left ⥤
      (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).FullSubcategory}
    (adj : (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι ⊣ DQ)
    (L : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left)
    (hL : IsDerivedLimit D.derivedSystem L)
    (hcc : ∀ n : ℕ, D.StageTransitionCounitCompatible n)
    (htr : ∀ (E : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left) (n : ℕ),
      D.StageTensorSectionsTransitionCompatible E n) :
    IsRelativelyPseudoCoherent D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2 D.X.hom.hom
      D.isLocallyOfFiniteType_structureMorphism (D.coheratorObj DQ L) :=
  D.isRelativelyPseudoCoherent_coheratorObj_of_ringIsPerfect adj L hL
    (D.ringIsPerfect_limitTensorSections_of adj L hL hcc htr)

end FlatSheafExistenceSituation

end AlgebraicGeometry.Space

end
