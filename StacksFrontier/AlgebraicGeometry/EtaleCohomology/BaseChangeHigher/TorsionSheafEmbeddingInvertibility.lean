module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.TorsionSheafEmbedding

/-!
# Invertibility of the base change map through an injective embedding

`Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_iff_map_eq_zero`: in the situation of
[Stacks, Tag 0F03], the base change map in degree `q + 1` is invertible exactly when
`R^{q+1}h_* e⁻¹(F ⟶ I)` vanishes, for an embedding of `F` into an injective sheaf `I` of
`ℤ/nℤ`-modules. (Ported from the C1103b work, as an addition to `TorsionSheafEmbedding.lean`.)

## References

* [Stacks Project, Tag 0F03](https://stacks.math.columbia.edu/tag/0F03)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.ZModSheaf

universe u

namespace Stacks.EtaleCohomology

variable {X S S' X' T Y : Scheme.{u}} (f : X ⟶ S) (n : ℤ) (q : ℕ)
  (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S') (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T)

/-- **The base change map in degree `q + 1` is invertible exactly when it is killed by an
embedding into an injective.** In the situation of
`mono_higherBaseChangeMapAb_app_of_injective` — `BC(f, n, q)`, both squares cartesian, `g`
quasi-compact and quasi-separated, `F` annihilated by `n` and contained in the underlying
abelian sheaf of an injective sheaf `I` of `ℤ/nℤ`-modules — the base change map
`(f')⁻¹R^{q+1}g_* F ⟶ R^{q+1}h_* e⁻¹F` is an isomorphism if and only if
`R^{q+1}h_* e⁻¹(F ⟶ I)` is zero.

The base change map is injective (part (1) of [Stacks, Tag 0F03]) and its cokernel embeds into
`R^{q+1}h_* e⁻¹I` through the map induced by `R^{q+1}h_* e⁻¹(F ⟶ I)` (part (3)); so it is
surjective exactly when that induced map, equivalently `R^{q+1}h_* e⁻¹(F ⟶ I)` itself, vanishes.
The criterion involves the target of the base change map only, which is what makes it
transportable along an identification of higher direct images that is not known to be
compatible with base change maps. -/
public theorem isIso_higherBaseChangeMapAb_app_iff_map_eq_zero
    (hbc : BaseChangeHolds f n (q : ℤ))
    (sq₁ : IsPullback p f' f s) (sq : IsPullback h e f' g)
    [QuasiCompact g] [QuasiSeparated g]
    {F : Sheaf (smallEtaleTopology T) Ab.{u + 1}}
    (hF : ∀ (U : T.Etale) (x : F.obj.obj (op U)), n • x = 0)
    (I : SheafOfModules.{u + 1} (etaleZModRingSheaf T n)) [Injective I]
    (k : F ⟶ (SheafOfModules.toSheaf.{u + 1} (etaleZModRingSheaf T n)).obj I) (hk : Mono k) :
    IsIso ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).app F) ↔
      (higherBaseChangeTarget h e (q + 1)).map k = 0 := by
  have hmono := mono_higherBaseChangeMapAb_app_of_injective f n q s p f' g h e hbc sq₁ sq hF
    I k hk
  have hcok := mono_cokernelDesc_higherBaseChangeMapAb_app_of_injective f n q s p f' g h e hbc
    sq₁ sq hF I k hk
  have hz := higherBaseChangeMapAb_app_comp_map_eq_zero_of_injective n q f' g h e sq I k hk
  refine ⟨fun _ => ?_, fun h0 => ?_⟩
  · rw [← cancel_epi ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).app F), hz, comp_zero]
  have hdesc : cokernel.desc ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).app F)
      ((higherBaseChangeTarget h e (q + 1)).map k) hz = 0 :=
    coequalizer.hom_ext (by rw [cokernel.π_desc, h0, comp_zero])
  rw [hdesc] at hcok
  have : Epi ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).app F) :=
    (Preadditive.epi_iff_isZero_cokernel _).2 (IsZero.of_mono_zero _
      ((higherBaseChangeTarget h e (q + 1)).obj
        ((SheafOfModules.toSheaf.{u + 1} (etaleZModRingSheaf T n)).obj I)))
  exact isIso_of_mono_of_epi _

end Stacks.EtaleCohomology

end
