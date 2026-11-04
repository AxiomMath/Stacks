module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.LocallyConstantStep
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstantExtensionByZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.FiniteCompactification
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleLocalDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.GenericFibrePoint

/-!
# Stacks Tag 03SD, assembled

Let `X` be separated of finite type over an algebraically closed field `k` with `dim X ≤ 1`, let
`U ⊆ X` be an open subscheme and `G` an abelian sheaf on `X` killed by a prime `ℓ` whose
restriction to `U` is finite locally constant. This file assembles the proof of Tag 03SD for
`j_! j⁻¹ G`:

* the restriction is a finite type locally constant sheaf of `F_ℓ`-vector spaces
  (`Stacks.EtaleCohomology.isFiniteTypeLocallyConstant_sheafOfEndAction_zmod`);
* Tag 0A3R gives a finite étale `g : T ⟶ U` of degree prime to `ℓ` and a filtration of `g⁻¹`
  with quotients `Z/ℓ` (taken as the hypothesis `h0A3R`, which is the statement of Tag 0A3R);
* the relative normalization `Yb` of `X` in `T` is a finite compactification, normal when `T` is;
* the trace, Tag 0GJ1, Tag 0A5D, Tag 0A5C and Tag 0GJA reduce everything to the eight
  assertions for the constant sheaf `Z/ℓ` on the normal scheme `Yb` (Tag 0A5B, the hypothesis
  `h0A5B`).

## Main results

* `Stacks.EtaleCohomology.TorsionCurveAssertions.extensionByZero_of_isFiniteLocallyConstant`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- A finite morphism does not increase the dimension. -/
theorem topologicalKrullDim_le_of_isIntegralHom {T S : Scheme.{u}} (i : T ⟶ S)
    [IsIntegralHom i] : topologicalKrullDim T ≤ topologicalKrullDim S :=
  Topology.topologicalKrullDim_le_of_continuous_of_specializes_injective i.base i.continuous
    fun _ _ h hi => eq_of_specializes_of_base_eq_of_isIntegralHom i h hi

/-- Sheafification of presheaves of `F_ℓ`-modules on a slice of a small étale site. -/
instance hasSheafify_smallEtale_over_moduleCat_zmod (Y : Scheme.{u}) (V : Y.Etale) (ℓ : ℕ) :
    HasSheafify (Y.smallEtaleTopology.over V) (ModuleCat.{u + 1} (ZMod ℓ)) :=
  Stacks.ConstantSheaf.hasSheafify_moduleCat.{u + 1, u, 0, u + 1} _ _

/-- Sheafification of presheaves of `F_ℓ`-modules on a small étale site. -/
instance hasSheafify_smallEtale_moduleCat_zmod (Y : Scheme.{u}) (ℓ : ℕ) :
    HasSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ)) :=
  Stacks.ConstantSheaf.hasSheafify_moduleCat.{u + 1, u, 0, u + 1} _ _

namespace TorsionCurveAssertions

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **Stacks Tag 03SD**, given Tag 0A3R (`h0A3R`), Tag 0A5B (`h0A5B`) and the normality of the
étale covers of `U` (`hnormal`). -/
theorem extensionByZero_of_isFiniteLocallyConstant {X : Scheme.{u}} (fX : X ⟶ Spec (.of k))
    [IsSeparated fX] [LocallyOfFiniteType fX] [QuasiCompact fX]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (hdim : topologicalKrullDim X ≤ 1) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hℓG : ℓ • 𝟙 G = 0) (U : X.Opens)
    (hlcc : Stacks.ConstantSheaf.IsFiniteLocallyConstant (U : Scheme.{u}).smallEtaleTopology
      ((etaleRestriction.{u, u + 1} U.ι).obj G))
    (h0A3R : ∀ F : Sheaf (smallEtaleTopology (U : Scheme.{u})) (ModuleCat.{u + 1} (ZMod ℓ)),
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ)
        (smallEtaleTopology (U : Scheme.{u})) F →
      ∃ (T : Scheme.{u}) (g : T ⟶ (U : Scheme.{u})) (d : ℕ), IsFinite g ∧ Etale g ∧
        Stacks.Morphisms.IsFiniteLocallyFreeOfRank g d ∧ ¬ ℓ ∣ d ∧
        ∃ S : RelSeries (ConstantRankOneStep.{u + 1, u} ℓ
            ((smallEtalePullbackZMod.{u + 1, u} ℓ g).obj F)),
          IsZero (Subobject.underlying.obj S.head) ∧ IsIso S.last.arrow)
    (hnormal : ∀ (T : Scheme.{u}) (g : T ⟶ (U : Scheme.{u})), Etale g → IsNormal T)
    (h0A5B : ∀ (Yb : Scheme.{u}) (pY : Yb ⟶ Spec (.of k)) [IsSeparated pY]
      [LocallyOfFiniteType pY] [QuasiCompact pY]
      [HasExt.{u + 1} (Sheaf Yb.smallEtaleTopology AddCommGrpCat.{u + 1})],
      topologicalKrullDim Yb ≤ 1 → IsNormal Yb →
        TorsionCurveAssertions pY (StrongTorsionCurveAssertions.constantZModAb Yb ℓ)) :
    TorsionCurveAssertions fX ((extensionByZero.{u, u + 1} U.ι).obj
      ((etaleRestriction.{u, u + 1} U.ι).obj G)) := by
  have : IsNoetherian X := isNoetherian_of_finiteType fX
  set H := (etaleRestriction.{u, u + 1} U.ι).obj G
  have hH : ℓ • 𝟙 H = 0 := nsmul_id_map_eq_zero _ hℓG
  set F := Stacks.ModuleCatLift.sheafOfEndAction (ZMod ℓ) (smallEtaleTopology (U : Scheme.{u})) H
    (zmodEndRingHomOf ℓ H hH)
  have hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ)
      (smallEtaleTopology (U : Scheme.{u})) F :=
    isFiniteTypeLocallyConstant_sheafOfEndAction_zmod ℓ _ H hH hlcc
  obtain ⟨T, g, d, hg, hge, hrk, hd, S, hhead, hlast⟩ := h0A3R F hF
  have := hg
  have := hge
  have := hrk
  have : IsNormal T := hnormal T g hge
  obtain ⟨Yb, π, j', hπ, hj', sq, hdom, hnorm⟩ :=
    exists_isPullback_isFinite_relativeNormalization k fX U.ι g
  have := hπ
  have := hj'
  have : IsNormal Yb := hnorm ‹_›
  have := hasExt_of_enoughInjectives.{u + 1} (Sheaf Yb.smallEtaleTopology AddCommGrpCat.{u + 1})
  have : IsNoetherian Yb := isNoetherian_of_finiteType (π ≫ fX)
  have hdimYb : topologicalKrullDim Yb ≤ 1 := (topologicalKrullDim_le_of_isIntegralHom π).trans hdim
  have hden : Dense (Set.range j'.base) := hdom.denseRange
  have hbase := StrongTorsionCurveAssertions.extensionByZero_constant_of_dense (π ≫ fX) hdimYb j'
    hden hℓ (h0A5B Yb (π ≫ fX) hdimYb ‹_›)
  have hL : ℓ • 𝟙 ((forgetZModSheaf T ℓ).obj (constantZMod.{u + 1, u} ℓ T)) = 0 :=
    nsmul_id_forgetZModSheaf_eq_zero _
  refine (StrongTorsionCurveAssertions.extensionByZero_of_finiteEtaleCover fX U.ι g d π j' sq hℓ hd
    H hH _ hL ?_ hbase).toTorsionCurveAssertions
  intro P h0 hiso hext hP
  have h1 := forget₂_mem_of_relSeries_constantRankOneStep
    ((smallEtalePullbackZMod.{u + 1, u} ℓ g).obj F) S hhead hlast P h0 hiso hext hP
  obtain ⟨e⟩ := nonempty_forgetZMod_pullback_iso g F
  exact hiso _ _ e h1

end TorsionCurveAssertions

end Stacks.EtaleCohomology

end
