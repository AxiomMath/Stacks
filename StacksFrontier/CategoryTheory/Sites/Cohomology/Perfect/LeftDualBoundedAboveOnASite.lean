module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LeftDualLocalRetractOnASite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionWithFlatTermsSurjective
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LeftDualBoundedAbove

/-!
# The first truncation of Stacks 0FPV, on a ringed site

Let `(C, O)` be a ringed site and let `N` be a left dual of `M` in the monoidal category `D(O)`
of Stacks 0FPT. Then every object `V` of `C` admits a covering family over each member of which
`M` is **concentrated in degrees `≤ b`** for some `b`.

This is the source's first truncation: the sections `fᵢ` occurring in `η(1) = ∑ᵢ fᵢ ⊗ gᵢ` sit in
finitely many degrees, so they all lift through the canonical truncation `τ_{≤ b} M^•` of a K-flat
representative for `b` large enough, and `M` is then a retract of that truncation — by
`AlgebraicGeometry.RingedSite.exists_presieve_localRetract`, whose mono hypothesis is supplied by
flatness of the terms of the representative of `N`.

It is the site analogue of `Stacks.Cohomology.LeftDualPerfect.exists_isLE_restrict`. Nothing
below is a clause of a tag; this is a step of a proof, so no `@[stacks …]` attribute is attached.

## Main results

* `AlgebraicGeometry.RingedSite.exists_presieve_isLE`: the statement above.

## Implementation notes

**The representatives.** Both `M` and `N` are resolved by
`Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution`, Stacks 06YS on a ringed site,
which delivers a K-flat complex *with flat terms*. The flatness of the terms of the
representative of `N` is used once, to see that the inclusion of the truncation stays a
monomorphism after `- ⊗ N^•`
(`Stacks.Cohomology.LeftDualPerfect.mono_mapBifunctorMap_f_general`); K-flatness of both is what
the comparison of Stacks 0FPT needs.

**The two comparison factors.** The isomorphism `Q(M^•) ≅ M` handed to the retract step is
`asIso (Q.map p) ≪≫ Q.objObjPreimageIso M`: the quasi-isomorphism of the resolution onto the
chosen representative `Q.objPreimage M`, followed by the identification of that representative's
image with `M`. Neither factor may be dropped — the resolution resolves the *representative*, not
`M`.

## References

* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry.RingedSite

open Stacks.SheafOfModules.DerivedMonoidal
open Stacks.DerivedTensor.ExtensionByZero (restriction)

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{u}]
  [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K L : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **The first truncation of the proof of Stacks 0FPV, on a ringed site.** If `M` has a left
dual in `D(O)`, then every object `V` of `C` admits a covering family over each member `W` of
which `M|_W` is concentrated in degrees `≤ b` for some `b`: it is a retract of the canonical
truncation `τ_{≤ b} M^•|_W` of a K-flat representative. -/
theorem exists_presieve_isLE (V : X.C)
    (M N : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules X.O)
    (pair : letI := derivedMonoidal X.O; ExactPairing M N) :
    ∃ S : Presieve V, Sieve.generate S ∈ X.J V ∧
      ∀ ⦃W : X.C⦄ (h : W ⟶ V), S h →
        ∃ b : ℤ, ((restriction X W).mapDerivedCategory.obj M).IsLE b := by
  classical
  obtain ⟨Mc, pM, hMk, -, hpM, -⟩ :=
    Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution X.O
      (DerivedCategory.Q.objPreimage M)
  obtain ⟨Nc, pN, hNk, hNflat, hpN, -⟩ :=
    Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution X.O
      (DerivedCategory.Q.objPreimage N)
  have resolve {K} (E : DerivedModules X) (p : K ⟶ DerivedCategory.Q.objPreimage E) [QuasiIso p] :
      DerivedCategory.Q.obj K ≅ E :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso E
  have := hpM
  have := hpN
  obtain ⟨S, hS, hdata⟩ := exists_presieve_localRetract X V M N pair Mc Nc
    (resolve M pM) (resolve N pN) hMk hNk
  refine ⟨S, hS, fun {W} h hh => ?_⟩
  obtain ⟨κ, hκ, deg, a, hR⟩ := hdata h hh
  obtain ⟨c, hc⟩ : ∃ c : ℤ, ∀ i, deg i ≤ c :=
    ⟨∑ i : κ, |deg i|, fun i => (le_abs_self _).trans
      (Finset.single_le_sum (f := fun i : κ => |deg i|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ i))⟩
  refine ⟨c + 1, ?_⟩
  have hmono : Mono ((Mc.ιTruncLE (c + 1) ▷ Nc).f 1) :=
    Stacks.Cohomology.LeftDualPerfect.mono_mapBifunctorMap_f_general (Mc.ιTruncLE (c + 1)) hNflat 1
  have hiso : ∀ i : κ, IsIso ((Mc.ιTruncLE (c + 1)).f (deg i)) := fun i =>
    CochainComplex.isIso_ιTruncLE_f Mc (c + 1) _ (by have := hc i; lia)
  obtain ⟨r⟩ := hR (Mc.truncLE (c + 1)) (Mc.ιTruncLE (c + 1)) hmono fun i =>
    ⟨(@inv _ _ _ _ ((Mc.ιTruncLE (c + 1)).f (deg i)) (hiso i)).val.app (op W) (a i),
      congrArg (fun ψ => ψ.val.app (op W) (a i))
        (@IsIso.inv_hom_id _ _ _ _ _ (hiso i))⟩
  exact DerivedCategory.isLE_of_retract r _
    ((restriction X W).isLE_mapDerivedCategory_obj_Q_obj (Mc.truncLE (c + 1)) (c + 1))

end AlgebraicGeometry.RingedSite

end
