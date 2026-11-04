module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NormalizedExistenceNagata
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NormalizedProper

/-!
# The normalized dualizing complex of a scheme separated over the base is `f^! ω_S^•`

In Situation [Stacks, Tag 0AU4] (`S` Noetherian with a dualizing complex `ω_S^•`), let
`p : X ⟶ S` be separated and of finite type and `ω_X^•` a dualizing complex normalized relative
to `ω_S^•` for the upper shriek functors of Nagata compactifications. Then `ω_X^• ≅ p^! ω_S^•`,
where `p^! = j^* ∘ ā` is the upper shriek functor of [Stacks, Tag 0A9Y] at *any*
compactification `j` of `p`. The isomorphism is unique once it is required to carry the
normalization `α_W` of `ω_X^•` to the canonical `(p^! ω_S^•)|_W ≅ (W → S)^! ω_S^•`, for every open
`W` separated over `S`. This is the closing remark of [Stacks, Tag 0AUE] on the separated case.

## Main results

* `Stacks.Duality.NormalizedOnOpens.existsUnique_iso_upperShriekPlus_nagata`: the unique
  isomorphism `ω_X^• ≅ p^!_j ω_S^•` compatible with the normalizations, for a compactification
  `j` of `p`.
* `Stacks.Duality.NormalizedOnOpens.isoUpperShriekPlusNagata`: that isomorphism.

## References

* [Stacks Project, Tag 0A9Y](https://stacks.math.columbia.edu/tag/0A9Y)
* [Stacks Project, Tag 0AA0](https://stacks.math.columbia.edu/tag/0AA0)
* [Stacks Project, Tag 0AUE](https://stacks.math.columbia.edu/tag/0AUE)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

namespace NormalizedOnOpens

variable {X S : Scheme.{u}} {p : X ⟶ S} {hp : IsFiniteTypeOverNoetherian p}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}

/-- **`ω_X^• ≅ p^! ω_S^•` for `X` separated over `S`, at any compactification.** In Situation
0AU4, let `p : X ⟶ S` be separated and of finite type, `ω_X^•` a dualizing complex normalized
relative to `ω_S^•` for the Nagata upper shriek functors, and `j` any compactification of `p`.
There is exactly one isomorphism `e : ω_X^• ≅ p^!_j ω_S^•` which, followed by the comparison
`p^!_j ≅ p^!` of [Stacks, Tag 0AA0] with the Nagata compactification, carries `α_W` to the
canonical `(p^! ω_S^•)|_W ≅ (W → S)^! ω_S^•` for every open `W` separated over `S`. -/
theorem existsUnique_iso_upperShriekPlus_nagata
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) (hps : IsShriekable p)
    (𝒦 : NormalizedOnOpens UpperShriek.nagata hp ωS) (j : CompactificationOf (Over.mk p)) :
    haveI := hps.target_noetherian
    ∃! e : 𝒦.complex ≅ (upperShriekPlus (ftsHomOf p hps.separatedFiniteType
        (isSeparatedFiniteType_id S) (Category.comp_id p)) j).obj ωS,
      ∀ (W : X.Opens) (hW : IsShriekable (W.ι ≫ p)),
        (UpperShriek.nagata.shriek W.ι (hp.isShriekable_ι W)).mapIso
            (e ≪≫ (DominatingCompactification.upperShriekPlusIso (ftsHomOf p
              hps.separatedFiniteType (isSeparatedFiniteType_id S) (Category.comp_id p)) j
              (nagataCompactification p hps)).app ωS) ≪≫
          upperShriekLocalIso UpperShriek.nagata hp hps ωS hW =
        𝒦.localIso W hW := by
  have := hps.target_noetherian
  obtain ⟨e₀, he₀, hu⟩ :=
    existsUnique_iso_shriek_ofCompactifications nagataCompactification hωS hps 𝒦
  let c := (DominatingCompactification.upperShriekPlusIso
    (ftsHomOf p hps.separatedFiniteType (isSeparatedFiniteType_id S) (Category.comp_id p)) j
    (nagataCompactification p hps)).app ωS
  refine ⟨e₀ ≪≫ c.symm, fun W hW => ?_, fun e he => ?_⟩
  · have hc : (e₀ ≪≫ c.symm) ≪≫ c = e₀ :=
      ((Iso.trans_assoc _ _ _).trans (congrArg (e₀ ≪≫ ·) (Iso.symm_self_id c))).trans
        (Iso.trans_refl e₀)
    exact (congrArg (fun x => (UpperShriek.nagata.shriek W.ι (hp.isShriekable_ι W)).mapIso x ≪≫
      upperShriekLocalIso UpperShriek.nagata hp hps ωS hW) hc).trans (he₀ W hW)
  · have h : e ≪≫ c = e₀ := hu _ he
    subst h
    exact (((Iso.trans_assoc e c c.symm).trans (congrArg (e ≪≫ ·) (Iso.self_symm_id c))).trans
      (Iso.trans_refl e)).symm

/-- **The isomorphism `ω_X^• ≅ p^!_j ω_S^•`** of
`Stacks.Duality.NormalizedOnOpens.existsUnique_iso_upperShriekPlus_nagata`, for `X` separated
over `S`, a dualizing complex `ω_X^•` normalized relative to `ω_S^•` and any compactification `j`
of the structure morphism `p`. -/
def isoUpperShriekPlusNagata
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) (hps : IsShriekable p)
    (𝒦 : NormalizedOnOpens UpperShriek.nagata hp ωS) (j : CompactificationOf (Over.mk p)) :
    haveI := hps.target_noetherian
    𝒦.complex ≅ (upperShriekPlus (ftsHomOf p hps.separatedFiniteType
      (isSeparatedFiniteType_id S) (Category.comp_id p)) j).obj ωS :=
  (existsUnique_iso_upperShriekPlus_nagata hωS hps 𝒦 j).exists.choose

/-- `Stacks.Duality.NormalizedOnOpens.isoUpperShriekPlusNagata` carries the normalization `α_W`
of `ω_X^•` to the canonical `(p^! ω_S^•)|_W ≅ (W → S)^! ω_S^•`. -/
theorem isoUpperShriekPlusNagata_spec
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) (hps : IsShriekable p)
    (𝒦 : NormalizedOnOpens UpperShriek.nagata hp ωS) (j : CompactificationOf (Over.mk p))
    (W : X.Opens) (hW : IsShriekable (W.ι ≫ p)) :
    haveI := hps.target_noetherian
    (UpperShriek.nagata.shriek W.ι (hp.isShriekable_ι W)).mapIso
        (isoUpperShriekPlusNagata hωS hps 𝒦 j ≪≫
          (DominatingCompactification.upperShriekPlusIso (ftsHomOf p
            hps.separatedFiniteType (isSeparatedFiniteType_id S) (Category.comp_id p)) j
            (nagataCompactification p hps)).app ωS) ≪≫
      upperShriekLocalIso UpperShriek.nagata hp hps ωS hW =
    𝒦.localIso W hW :=
  (existsUnique_iso_upperShriekPlus_nagata hωS hps 𝒦 j).exists.choose_spec W hW

end NormalizedOnOpens

end Stacks.Duality

end
