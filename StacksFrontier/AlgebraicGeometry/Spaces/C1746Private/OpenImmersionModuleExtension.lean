/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.FiniteTilde

/-!
# Extending a module of finite type along a quasi-compact open immersion

Stacks 0G41 (1) extends a quasi-coherent module of finite type from a quasi-compact open `U` of a
quasi-compact and quasi-separated scheme `X` to `X`
(`AlgebraicGeometry.exists_finiteTypeQuasicoherent_extension`). This file restates it for a
quasi-compact open immersion `j : U ⟶ X`, with the inverse image `j^*` in place of the
restriction to an open subscheme: this is the form used in the proof of Stacks 0DPD, where `U`
is a scheme open in the scheme-theoretic closure of an immersion.

## Main results

* `AlgebraicGeometry.exists_finiteType_pullback_iso_of_isOpenImmersion`.

## References

* [Stacks Project, Tag 0G41](https://stacks.math.columbia.edu/tag/0G41)
* [Stacks Project, Tag 0DPD](https://stacks.math.columbia.edu/tag/0DPD)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks 0G41 (1) along a quasi-compact open immersion.** Let `j : U ⟶ X` be a quasi-compact
open immersion into a quasi-compact and quasi-separated scheme. Every quasi-coherent
`𝒪_U`-module `G` of finite type is `j^*G'` for a quasi-coherent `𝒪_X`-module `G'` of finite
type. -/
theorem exists_finiteType_pullback_iso_of_isOpenImmersion {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] [CompactSpace X] [QuasiSeparatedSpace X]
    (G : U.Modules) [G.IsQuasicoherent] [G.IsFiniteType] :
    ∃ (G' : X.Modules) (_ : G'.IsQuasicoherent) (_ : G'.IsFiniteType),
      Nonempty ((Scheme.Modules.pullback j).obj G' ≅ G) := by
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace j
  let O := j.opensRange
  have hO : IsCompact O.1 := isCompact_range j.continuous
  let e := j.isoOpensRange
  let G₀ : O.toScheme.Modules := (Scheme.Modules.restrictFunctor e.inv).obj G
  have : G₀.IsFiniteType := Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_restrict e.inv G
  obtain ⟨G', hG'qc, hG'ft, ⟨e'⟩⟩ := exists_finiteTypeQuasicoherent_extension O hO G₀
  exact ⟨G', hG'qc, hG'ft, ⟨(Scheme.Modules.pullbackCongr (j.isoOpensRange_hom_ι).symm).app G' ≪≫
    ((Scheme.Modules.pullbackComp e.hom O.ι).app G').symm ≪≫
    (Scheme.Modules.pullback e.hom).mapIso
      (((Scheme.Modules.restrictFunctorIsoPullback O.ι).app G').symm ≪≫ e' ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback e.inv).app G) ≪≫
    (Scheme.Modules.pullbackComp e.hom e.inv).app G ≪≫
    (Scheme.Modules.pullbackCongr e.hom_inv_id).app G ≪≫
    (Scheme.Modules.pullbackId (X := U)).app G⟩⟩

end AlgebraicGeometry

end
