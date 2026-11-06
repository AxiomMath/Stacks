module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.RefinementKilledSubsheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ProperModelLerayVanishing

/-!
# The geometric half of the Zariski–Riemann limit step, from a system of killed subsheaves

Travaux de Gabber, Exposé XVIII-A, last remark of §2, passes to the limit over all proper models
`Y` of `η = Spec (Frac B)`: the colimit of `H^p(Y, R^q j_{Y*} F)` is the cohomology of a limit
sheaf `A_q` on the closed fibre of the Zariski–Riemann space, whose support has transcendence
degree at most `δ = min(e - 1, e - q)`, and `H^p` of such a sheaf vanishes for `p > 2δ`.

This file does the passage to the limit at finite level, without topos limits (SGA 4, Exposé VI,
8.7.4, read on one model). Fix a model `M` with `G = R^q j_* F` and a degree `q`. Suppose given a
filtered system of sheaves `K_i ⟶ G`, each killed by some refinement of `M`
(`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.Kills`), whose colimit maps
monomorphically to `G`, and whose cokernel `Q` (in the limit, the image of `G` in the direct image
of `A_q`) restricted to the geometric closed fibre `Y_Ω` is supported at points `y` with
`trdeg_Ω κ(y) ≤ min(e - 1, e - q)`. Then for `p + q ≥ 2e`:

* `H^p(Y, Q) = H^p(Y_Ω, Q|_{Y_Ω}) = 0` by proper base change
  (`Stacks.EtaleCohomology.subsingleton_sheafH_iff_geometricClosedFibre_of_isProper`) and Gabber's
  `δ`-claim at finite level
  (`AlgebraicGeometry.subsingleton_H_of_forall_mem_smallEtaleSupport_two_mul_lt`), since
  `p > 2 min(e - 1, e - q)`;
* so every class of `H^p(Y, G)` comes from some `H^p(Y, K_i)`
  (`Stacks.EtaleCohomology.exists_sheafH_map_eq_of_mono_colimitDesc`), and dies on the refinement
  killing `K_i`
  (`Scheme.ZariskiRiemann.ProperModel.Refinement.lerayTermMap_sheafHMap_eq_zero_of_kills`).

The existence of such a system is
`AlgebraicGeometry.Scheme.ZariskiRiemann.KilledSubsheafSystemBound`.

## Main definitions

* `AlgebraicGeometry.Scheme.ZariskiRiemann.KilledSubsheafSystemBound` — the existence of the
  killed system with the support bound on its cokernel.

## Main results

* `Scheme.ZariskiRiemann.ProperModel.exists_refinement_lerayTermMap_eq_zero_of_killedSystem`
  — at one model: such a system kills every class of `H^p(Y, R^q j_* F)` with `p + q ≥ 2e`.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.zariskiRiemannKilling_of_killedSubsheafSystemBound` —
  `ZariskiRiemannKilling n` from `KilledSubsheafSystemBound n`.

## References

* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
* SGA 4, Exposé VI, 8.7.4
* [Stacks Project, Tag 03Q5](https://stacks.math.columbia.edu/tag/03Q5)
* [Stacks Project, Tag 0DDF](https://stacks.math.columbia.edu/tag/0DDF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

open Stacks.EtaleCohomology

namespace ProperModel

variable {B : Type u} [CommRing B] [IsDomain B] [StrictlyHenselianLocalRing B]

/-- A sheaf killed by `n` has cokernels of maps into it killed by `n`. -/
theorem nsmul_id_cokernel_eq_zero {Y : Scheme.{u}}
    {K G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} (d : K ⟶ G) {n : ℕ}
    (hG : n • 𝟙 G = 0) : n • 𝟙 (cokernel d) = 0 := by
  rw [← cancel_epi (cokernel.π d), Preadditive.comp_nsmul, Category.comp_id, comp_zero]
  calc n • cokernel.π d = (n • 𝟙 G) ≫ cokernel.π d := by
        rw [Preadditive.nsmul_comp, Category.id_comp]
    _ = 0 := by rw [hG, zero_comp]

omit [IsDomain B] in
/-- **At one model, a killed system with the `δ`-bound on its cokernel kills every class of
`H^p(Y, R^q j_* F)` with `p + q ≥ 2e`.** Let `B` be strictly henselian local, `M` a proper model
with `G = R^q j_* F`, `F` killed by `n > 0`, `x : Spec Ω ⟶ Spec B` a geometric point over the
closed point, and `K_i ⟶ G` a filtered system, each killed by some refinement, with monomorphic
colimit map whose cokernel, restricted to `Y_Ω`, is supported at points `y` with
`trdeg_Ω κ(y) + q ≤ e` and `trdeg_Ω κ(y) + 1 ≤ e`. If `2e ≤ p + q`, every class
`c ∈ H^p(Y, G)` dies on some refinement. -/
theorem exists_refinement_lerayTermMap_eq_zero_of_killedSystem (M : ProperModel B)
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1})
    {n : ℕ} (hn : 0 < n)
    (hF : ∀ (T : (Spec (.of (FractionRing B))).Etale) (s : F.obj.obj (op T)), n • s = 0)
    (e p q : ℕ) (hpq : 2 * e ≤ p + q) {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (K : I ⥤ Sheaf M.Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (ι : K ⟶ (Functor.const I).obj (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F))
    (hkill : ∀ i, ∃ (M' : ProperModel B) (φ : Refinement M' M), φ.Kills F q (ι.app i))
    [Mono (colimit.desc K (Cocone.mk _ ι))] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ Spec (.of B)) (hx : x (default : Spec (.of Ω)) = IsLocalRing.closedPoint B)
    (hsupp : ∀ y ∈ smallEtaleSupport ((etaleAbelianInverseImage.{u, 0} (pullback.fst M.f x)).obj
        (cokernel (colimit.desc K (Cocone.mk _ ι)))),
      ∃ a : ℕ, a + q ≤ e ∧ a + 1 ≤ e ∧ y ∈ Scheme.trdegLESet Ω (pullback.snd M.f x) a)
    (c : Sheaf.H.{u + 1} (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F) p) :
    ∃ (M' : ProperModel B) (φ : Refinement M' M), φ.lerayTermMap F p q c = 0 := by
  have : CompactSpace M.Y := QuasiCompact.compactSpace_of_compactSpace M.f
  have : QuasiSeparatedSpace (Spec (.of B)) :=
    inferInstanceAs (QuasiSeparatedSpace (PrimeSpectrum B))
  have : IsSeparated M.f := M.isProper.toIsSeparated
  have : QuasiSeparated M.f := IsSeparated.instQuasiSeparated M.f
  have : QuasiSeparatedSpace M.Y := quasiSeparatedSpace_of_quasiSeparated M.f
  set d := colimit.desc K (Cocone.mk _ ι)
  have hG : n • 𝟙 (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F) = 0 :=
    nsmul_id_obj_eq_zero _ ((forall_nsmul_eq_zero_iff_nsmul_id_eq_zero F).1 hF)
  have hQ : Stacks.Torsion.torsionSheafProperty M.Y.smallEtaleTopology (cokernel d) :=
    torsionSheafProperty_of_forall_nsmul_eq_zero hn
      ((forall_nsmul_eq_zero_iff_nsmul_id_eq_zero _).2 (nsmul_id_cokernel_eq_zero d hG))
  have hHQ : Subsingleton (Sheaf.H.{u + 1} (cokernel d) p) := by
    refine (subsingleton_sheafH_iff_geometricClosedFibre_of_isProper M.f x hx _ hQ p).2 ?_
    have hT := torsionSheafProperty_etaleAbelianInverseImage.{u, 0} (pullback.fst M.f x) _ hQ
    have key := @subsingleton_H_of_forall_mem_smallEtaleSupport_two_mul_lt Ω _ inferInstance _
      (pullback.snd M.f x) ?_ ?_ _ hT p fun y hy ↦ by
        obtain ⟨a, haq, ha1, hya⟩ := hsupp y hy
        exact ⟨a, by omega, hya⟩
    · exact key
    · have : IsProper (pullback.snd M.f x) := inferInstance
      exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd M.f x)
    · have : IsProper (pullback.snd M.f x) := inferInstance
      exact this.toLocallyOfFiniteType
  obtain ⟨i, z, hz⟩ := exists_sheafH_map_eq_of_mono_colimitDesc K ι p hHQ c
  obtain ⟨M', φ, hφ⟩ := hkill i
  exact ⟨M', φ, hz ▸ φ.lerayTermMap_sheafHMap_eq_zero_of_kills F p q (ι.app i) hφ z⟩

end ProperModel

/-- **The killed-subsheaf system with Gabber's `δ`-bound on its cokernel.** For `B` a strictly
henselian Noetherian local domain of dimension `e ≥ 1` with `n` invertible, `F` killed by `n` on
`η = Spec (Frac B)`, every proper model `M` and every degree `q`, there are: a filtered system of
abelian sheaves `K_i` on `Y_étale` with maps `ι_i : K_i ⟶ R^q j_* F`, each killed by some
refinement of `M`, whose colimit maps monomorphically to `R^q j_* F`, and a geometric point
`x : Spec Ω ⟶ Spec B` over the closed point, such that every point `y` of the support of the
cokernel restricted to `Y_Ω` has `trdeg_Ω κ(y) ≤ min(e - 1, e - q)` (written without truncated
subtraction: `a + q ≤ e` and `a + 1 ≤ e`). -/
def KilledSubsheafSystemBound (n : ℕ) : Prop :=
  ∀ (B : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B] [StrictlyHenselianLocalRing B]
    (e : ℕ), ringKrullDim B = e → 0 < e → IsUnit (n : B) →
    ∀ (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}),
      (∀ (T : (Spec (.of (FractionRing B))).Etale) (s : F.obj.obj (op T)), n • s = 0) →
      ∀ (M : ProperModel B) (q : ℕ),
        ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
          (K : I ⥤ Sheaf M.Y.smallEtaleTopology AddCommGrpCat.{u + 1})
          (ι : K ⟶ (Functor.const I).obj
            (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F)),
          (∀ i, ∃ (M' : ProperModel B) (φ : ProperModel.Refinement M' M),
            φ.Kills F q (ι.app i)) ∧
          Mono (colimit.desc K (Cocone.mk _ ι)) ∧
          ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω) (x : Spec (.of Ω) ⟶ Spec (.of B)),
            x (default : Spec (.of Ω)) = IsLocalRing.closedPoint B ∧
            ∀ y ∈ smallEtaleSupport ((etaleAbelianInverseImage.{u, 0} (pullback.fst M.f x)).obj
                (cokernel (colimit.desc K (Cocone.mk _ ι)))),
              ∃ a : ℕ, a + q ≤ e ∧ a + 1 ≤ e ∧ y ∈ Scheme.trdegLESet Ω (pullback.snd M.f x) a

/-- **The geometric half of the Zariski–Riemann limit step from the killed-subsheaf system**:
`KilledSubsheafSystemBound n` implies `ZariskiRiemannKilling n`. -/
theorem zariskiRiemannKilling_of_killedSubsheafSystemBound {n : ℕ}
    (h : KilledSubsheafSystemBound.{u} n) : ZariskiRiemannKilling.{u} n := by
  intro B _ _ _ _ e he he0 hn F hF M p q hpq c
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at hn
  obtain ⟨I, _, _, K, ι, hkill, hmono, Ω, _, _, x, hx, hsupp⟩ := h B e he he0 hn F hF M q
  exact M.exists_refinement_lerayTermMap_eq_zero_of_killedSystem F hn0 hF e p q hpq K ι hkill
    x hx hsupp c

end AlgebraicGeometry.Scheme.ZariskiRiemann

end
