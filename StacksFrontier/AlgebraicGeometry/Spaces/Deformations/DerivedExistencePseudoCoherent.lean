module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceTensorSectionsLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSectionsLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceTheorem
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedChow.RelativePseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PseudoCoherentSectionsTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeAbsoluteChartDictionary

/-!
# The derived limit of Situation 0DIK is pseudo-coherent

In Situation [Stacks, Tag 0DIK] let `K = R lim_{D_QCoh(𝒪_X)}(Kₙ)` be the object of
[Stacks, Tag 0DIL]. Then `K` is pseudo-coherent on `X`.

## Main results

* `DerivedExistenceSystem.isPseudoCoherentOnLimit_coheratorObj`: `K = DQ_X(L)` is
  pseudo-coherent on `X`, at every coherator `DQ_X` and every derived limit `L` in `D(𝒪_X)`.
* `DerivedExistenceSystem.isPseudoCoherentOnLimit_of_isPseudoCoherent_tensorSections`: a derived
  limit `K` of the tower `(Rjₙ,* Kₙ)` in `D_QCoh(𝒪_X)` is pseudo-coherent on `X` once
  `RΓ(X, E ⊗^𝐋 K)` is pseudo-coherent over `A` for every perfect `E`.
* `DerivedExistenceSystem.isPseudoCoherentOnLimit_of_forall_isDerivedLimit`: every derived limit
  of the tower in `D_QCoh(𝒪_X)` is pseudo-coherent on `X`, given that `RΓ(X, E ⊗^𝐋 K)` is
  pseudo-coherent for every such derived limit `K` and every perfect `E`.
* `DerivedExistenceSystem.isPseudoCoherentOnLimit_coheratorObj_of_forall_isDerivedLimit`: the
  same for `K = DQ_X(L)`, at every coherator `DQ_X` and every derived limit `L` in `D(𝒪_X)`.

## References

* [Stacks Project, Tag 0DIK](https://stacks.math.columbia.edu/tag/0DIK)
* [Stacks Project, Tag 0DIL](https://stacks.math.columbia.edu/tag/0DIL)
* [Stacks Project, Tag 0DIM](https://stacks.math.columbia.edu/tag/0DIM)
* [Stacks Project, Tag 0DIN](https://stacks.math.columbia.edu/tag/0DIN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.GrothendieckExistence (limitBase)

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory

namespace DerivedExistenceSystem

variable (D : DerivedExistenceSystem.{u})

attribute [local instance] HasDerivedCategory.standard

/-- In Situation 0DIK let `K` be a derived limit of the tower `(Rjₙ,* Kₙ)` in `D_QCoh(𝒪_X)`. If
`RΓ(X, E ⊗^𝐋 K)` is pseudo-coherent in `D(A)` for every perfect `E` in `D(𝒪_X)`, then `K` is
pseudo-coherent on `X`. -/
theorem isPseudoCoherentOnLimit_of_isPseudoCoherent_tensorSections
    [HasProduct fun n : ℕ => D.quasicoherentTower.obj ⟨n⟩]
    (K : (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
      D.X.left).FullSubcategory)
    (hK : IsDerivedLimit D.quasicoherentTower K)
    (h : ∀ E : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left,
      spaceIsPerfect D.B (limitBase D.system) D.containsLimitBase D.X.left E →
        StacksDraft.PseudoCoherence.IsPseudoCoherent
          ((D.limitTensorSections E).obj
            ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
              D.X.left).ι.obj K))) :
    D.IsPseudoCoherentOnLimit
      ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι.obj K) := by
  have : IsAffine ((BigFppfOver.toScheme D.B (limitBase D.system) D.containsLimitBase).obj
      (baseSiteObj D.B (limitBase D.system) D.containsLimitBase)) := D.isAffine_limitBaseObject
  obtain ⟨c, hc⟩ := D.derivedLimit_isBoundedAbove.2.2.2 ‹_› K hK
  have hX : D.X.hom = DerivedChow.toBase D.B (limitBase D.system) D.containsLimitBase D.X.left :=
    ObjectProperty.hom_ext _
      ((isTerminal_yoneda_obj_base D.B (limitBase D.system) D.containsLimitBase).hom_ext _ _)
  have hsep : IsSeparated D.B (limitBase D.system) D.containsLimitBase
      (DerivedChow.toBase D.B (limitBase D.system) D.containsLimitBase D.X.left).hom :=
    hX ▸ D.proper.1
  have hfp : IsFinitePresentation D.B (limitBase D.system) D.containsLimitBase
      (DerivedChow.toBase D.B (limitBase D.system) D.containsLimitBase D.X.left).hom :=
    hX ▸ D.finitePresentation
  have hfl : IsFlat D.B (limitBase D.system) D.containsLimitBase
      (DerivedChow.toBase D.B (limitBase D.system) D.containsLimitBase D.X.left).hom :=
    hX ▸ D.flat
  have hKb : ∃ b : ℤ, K.obj.IsLE b :=
    ⟨c, (DerivedCategory.isLE_iff _ c).2 fun i hi ↦ hc i hi⟩
  have key : ∀ (g : D.X.left ⟶ schemeSpace (baseSiteObj D.B (limitBase D.system)
        D.containsLimitBase))
      (_ : g = DerivedChow.toBase D.B (limitBase D.system) D.containsLimitBase D.X.left)
      (E : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left),
      StacksDraft.PseudoCoherence.IsPseudoCoherent
          ((representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
            (baseSiteObj D.B (limitBase D.system) D.containsLimitBase)).obj
            ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase g).obj
              (((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase
                D.X.left).obj E).obj K.obj))) →
      StacksDraft.PseudoCoherence.IsPseudoCoherent
          ((representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
            (baseSiteObj D.B (limitBase D.system) D.containsLimitBase)).obj
            ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
              (DerivedChow.toBase D.B (limitBase D.system) D.containsLimitBase D.X.left)).obj
              (((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase
                D.X.left).obj E).obj K.obj))) := by
    rintro g rfl E hE
    exact hE
  have hperf := fun E hE ↦ key D.X.hom hX E (h E hE)
  have hpc := fun E hE ↦ isPseudoCoherent_representedAffineDerivedSections_tensor
    (U := baseSiteObj D.B (limitBase D.system) D.containsLimitBase)
    (DerivedChow.toBase D.B (limitBase D.system) D.containsLimitBase D.X.left)
    D.isQuasiCompactSpace_X D.isAbsolutelyQuasiSeparated K.obj K.property hKb hperf E hE
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
    fun R hR _ X hsep hfp K hK h ↦
      isRelativelyPseudoCoherent_of_isPseudoCoherent_derivedSections_tensor D.B (A := R) hR
        hsep hfp K hK h
  have h0CTT := h0CTT' (limit D.system) D.containsLimitBase D.X.left hsep hfp K.obj K.property hpc
  exact (isRelativelyPseudoCoherent_iff_isPseudoCoherent D.B (limitBase D.system)
    D.containsLimitBase (DerivedChow.toBase D.B (limitBase D.system) D.containsLimitBase D.X.left)
    hfl hfp.1 K).1 h0CTT

/-- In Situation 0DIK every derived limit `K` of the tower `(Rjₙ,* Kₙ)` in `D_QCoh(𝒪_X)` is
pseudo-coherent on `X`, provided that for every such derived limit `RΓ(X, E ⊗^𝐋 K)` is
pseudo-coherent in `D(A)` for every perfect `E`. -/
theorem isPseudoCoherentOnLimit_of_forall_isDerivedLimit
    (h0DIM : ∀ (_ : HasProduct fun n : ℕ => D.quasicoherentTower.obj ⟨n⟩)
      (K : (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
        D.X.left).FullSubcategory),
      IsDerivedLimit D.quasicoherentTower K →
      ∀ E : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left,
      spaceIsPerfect D.B (limitBase D.system) D.containsLimitBase D.X.left E →
        StacksDraft.PseudoCoherence.IsPseudoCoherent
          ((D.limitTensorSections E).obj
            ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
              D.X.left).ι.obj K)))
    (_ : HasProduct fun n : ℕ => D.quasicoherentTower.obj ⟨n⟩)
    (K : (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
      D.X.left).FullSubcategory)
    (hK : IsDerivedLimit D.quasicoherentTower K) :
    D.IsPseudoCoherentOnLimit
      ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι.obj K) :=
  D.isPseudoCoherentOnLimit_of_isPseudoCoherent_tensorSections K hK (h0DIM ‹_› K hK)

/-- In Situation 0DIK, for every coherator `adj : ι ⊣ DQ_X` and every derived limit
`L = R lim_{D(𝒪_X)} Kₙ` of the tower `(Rjₙ,* Kₙ)`, the object `K = DQ_X(L)` is pseudo-coherent on
`X`, provided that `RΓ(X, E ⊗^𝐋 K')` is pseudo-coherent in `D(A)` for every perfect `E` and every
derived limit `K'` of the tower `(Rjₙ,* Kₙ)` in `D_QCoh(𝒪_X)`. -/
theorem isPseudoCoherentOnLimit_coheratorObj_of_forall_isDerivedLimit
    (h0DIM : ∀ (_ : HasProduct fun n : ℕ => D.quasicoherentTower.obj ⟨n⟩)
      (K : (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
        D.X.left).FullSubcategory),
      IsDerivedLimit D.quasicoherentTower K →
      ∀ E : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left,
      spaceIsPerfect D.B (limitBase D.system) D.containsLimitBase D.X.left E →
        StacksDraft.PseudoCoherence.IsPseudoCoherent
          ((D.limitTensorSections E).obj
            ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
              D.X.left).ι.obj K)))
    (DQ : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left ⥤
      (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
        D.X.left).FullSubcategory)
    (adj : (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι ⊣ DQ)
    (L : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left)
    (hL : IsDerivedLimit D.spaceTower L) :
    D.IsPseudoCoherentOnLimit
      ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι.obj
        (DQ.obj L)) := by
  obtain ⟨hp, hK⟩ := (D.derivedLimit_isBoundedAbove.2.2.1 DQ adj L hL).1
  exact D.isPseudoCoherentOnLimit_of_forall_isDerivedLimit h0DIM hp _ hK

/-- In Situation 0DIK let `K = R lim_{D_QCoh(𝒪_X)}(Kₙ) = DQ_X(L)` be the object of
[Stacks, Tag 0DIL], for a coherator `adj : ι ⊣ DQ_X` and a derived limit `L = R lim_{D(𝒪_X)} Kₙ`
of the tower `(Rjₙ,* Kₙ)`. Then `K` is pseudo-coherent on `X`. -/
@[stacks 0DIN "K = R lim_{D_QCoh} K_n = DQ_X(R lim_{D(O_X)} K_n) is pseudo-coherent on X, for every \
  choice of coherator and of derived limit; nothing is granted or assumed"]
theorem isPseudoCoherentOnLimit_coheratorObj
    (DQ : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left ⥤
      (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
        D.X.left).FullSubcategory)
    (adj : (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι ⊣ DQ)
    (L : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left)
    (hL : IsDerivedLimit D.spaceTower L) :
    D.IsPseudoCoherentOnLimit
      ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι.obj
        (DQ.obj L)) :=
  D.isPseudoCoherentOnLimit_coheratorObj_of_forall_isDerivedLimit
    D.isPseudoCoherent_limitTensorSections_of_isDerivedLimit DQ adj L hL

end DerivedExistenceSystem

end AlgebraicGeometry.Space

end
