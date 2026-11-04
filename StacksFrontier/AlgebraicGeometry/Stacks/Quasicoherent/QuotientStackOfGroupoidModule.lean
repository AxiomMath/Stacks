module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackPointSectionsCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackPointwiseExtension
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackGroupoidFunctor

/-!
# The quasi-coherent module on the quotient stack attached to a module on the groupoid

Let `(𝒢, α)` be a quasi-coherent module on a groupoid `(U, R, s, t, c)` in algebraic spaces. The
proof of Stacks 06WT constructs a quasi-coherent module on `[U/R]` from it: the presheaf
`(T, a) ↦ Γ(T, a^*𝒢)` on the affine points of the pointwise quotient `[U/_pR]` is cartesian
(`AlgebraicGeometry.Stack.isIso_canonicalMap_pointModuleSheaf`), so by Stacks 0H0E it is the
restriction of a quasi-coherent module on `[U/_pR]`; and `[U/_pR] ⟶ [U/R]` is a dense subsite, so
by the Comparison Lemma that module is the restriction of a unique module on `[U/R]`, which is
quasi-coherent because its restriction is (`AlgebraicGeometry.Stack.FibredDenseSubsite`).

## Main definitions

* `AlgebraicGeometry.Stack.pointwiseModule`: the quasi-coherent module on `[U/_pR]`.
* `AlgebraicGeometry.Stack.pointwiseModuleAffineIso`: its restriction to the affine points is
  `(T, a) ↦ Γ(T, a^*𝒢)`.
* `AlgebraicGeometry.Stack.quotientStackModuleOfGroupoid`: the module on `[U/R]`.

## Main results

* `AlgebraicGeometry.Stack.isQuasicoherentOnSite_quotientStackModuleOfGroupoid`: it is
  quasi-coherent.

## References

* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
* [Stacks Project, Tag 0H0E](https://stacks.math.columbia.edu/tag/0H0E)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
  (M : Space.QuasicoherentModule C S hS G)

/-- **Condition (8) of Stacks 0H0E for `(T, a) ↦ Γ(T, a^*𝒢)`**: it is the restriction to the affine
points of a quasi-coherent module on the pointwise quotient `[U/_pR]`. -/
theorem exists_quasicoherent_pointModuleSheaf :
    ∃ h : Presheaf.IsSheaf (AffineCategory.siteKindRingedSite C S hS (presheafOfGroupoids
        (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
        (isFiberedInGroupoids_presheafOfGroupoids _) .fppf).J (pointModuleSheaf G M).val.presheaf,
      letI := AffineCategory.isDenseSubsite_inclusion_siteKind C S hS (presheafOfGroupoids
        (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
        (isFiberedInGroupoids_presheafOfGroupoids _) .fppf
      ∃ G₀ : SheafOfModules.{u} (FibredSite.ringStructureSheafCore C S hS (presheafOfGroupoids
          (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
          (isFiberedInGroupoids_presheafOfGroupoids _) .fppf),
        G₀.IsQuasicoherentOnSite ∧
          Nonempty ((Stacks.DenseSubsiteModules.moduleRestriction
            (AffineCategory.siteKindRingedSite C S hS (presheafOfGroupoids
              (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
              (isFiberedInGroupoids_presheafOfGroupoids _) .fppf).J
            (BigFppfOver.associatedTopology C S hS (presheafOfGroupoids
              (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p .fppf)
            (AffineCategory.inclusion C S hS (presheafOfGroupoids
              (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p)
            (FibredSite.ringStructureSheafCore C S hS (presheafOfGroupoids
              (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
              (isFiberedInGroupoids_presheafOfGroupoids _) .fppf)).obj G₀ ≅
            (⟨(pointModuleSheaf G M).val, h⟩ : SheafOfModules.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf (AffineCategory.siteKindRingedSite C S hS
                (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
                (isFiberedInGroupoids_presheafOfGroupoids _) .fppf).O))) :=
  ((AffineCategory.tfae_isQuasicoherent C S hS _ (isFiberedInGroupoids_presheafOfGroupoids _)
    (pointModuleSheaf G M)) _ List.mem_cons_self _
    (List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <|
      List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <|
      List.mem_cons_of_mem _ List.mem_cons_self)).mp
    (fun _ _ f => isIso_canonicalMap_pointModuleSheaf G M f)

/-- The quasi-coherent module on `[U/_pR]` extending `(T, a) ↦ Γ(T, a^*𝒢)`. -/
def pointwiseModule : SheafOfModules.{u} (FibredSite.ringStructureSheafCore C S hS
    (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
    (isFiberedInGroupoids_presheafOfGroupoids _) .fppf) :=
  (exists_quasicoherent_pointModuleSheaf G M).choose_spec.choose

/-- The module `pointwiseModule` on `[U/_pR]` is quasi-coherent. -/
theorem isQuasicoherentOnSite_pointwiseModule : (pointwiseModule G M).IsQuasicoherentOnSite :=
  (exists_quasicoherent_pointModuleSheaf G M).choose_spec.choose_spec.1

/-- The identification of the restriction of `pointwiseModule` to the affine points with
`(T, a) ↦ Γ(T, a^*𝒢)`. -/
def pointwiseModuleAffineIso :=
  Classical.choice (exists_quasicoherent_pointModuleSheaf G M).choose_spec.choose_spec.2

/-- The morphism `[U/_pR] ⟶ [U/R]` is a dense subsite for the fppf topologies. -/
instance : (pointwiseToQuotientStack G).IsDenseSubsite
    (BigFppfOver.associatedTopology C S hS
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p .fppf)
    (BigFppfOver.associatedTopology C S hS (quotientStack G).p .fppf) :=
  isDenseSubsite_pointwiseToQuotientStack G

/-- Restriction of modules from `[U/R]` to `[U/_pR]`. -/
abbrev pointwiseRestriction :=
  Stacks.DenseSubsiteModules.moduleRestriction
    (BigFppfOver.associatedTopology C S hS
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p .fppf)
    (BigFppfOver.associatedTopology C S hS (quotientStack G).p .fppf) (pointwiseToQuotientStack G)
    (FibredSite.ringStructureSheafCore C S hS (quotientStack G).p
      (isFiberedInGroupoids_quotientStack G) .fppf)

/-- Restriction of modules from `[U/R]` to `[U/_pR]` is an equivalence of categories. -/
instance : (pointwiseRestriction G).IsEquivalence :=
  FibredDenseSubsite.isEquivalence_moduleRestriction (quotientStack G).p
    (isFiberedInGroupoids_quotientStack G) (pointwiseToQuotientStack G) _ _ _

/-- **The module on `[U/R]` attached to a quasi-coherent module on the groupoid**: the module on
`[U/R]` whose restriction to `[U/_pR]` is `pointwiseModule`. -/
def quotientStackModuleOfGroupoid : QuotientStackModules G :=
  (pointwiseRestriction G).objPreimage (pointwiseModule G M)

/-- The module `quotientStackModuleOfGroupoid` on `[U/R]` is quasi-coherent. -/
theorem isQuasicoherentOnSite_quotientStackModuleOfGroupoid :
    (quotientStackModuleOfGroupoid G M).IsQuasicoherentOnSite :=
  FibredDenseSubsite.isQuasicoherentOnSite_of_moduleRestriction _ (quotientStack G).p
    (isFiberedInGroupoids_presheafOfGroupoids _) (isFiberedInGroupoids_quotientStack G)
    (pointwiseToQuotientStack G) _ _ _ _
    (SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((pointwiseRestriction G).objObjPreimageIso (pointwiseModule G M)).symm
      (isQuasicoherentOnSite_pointwiseModule G M))

end AlgebraicGeometry.Stack

end
