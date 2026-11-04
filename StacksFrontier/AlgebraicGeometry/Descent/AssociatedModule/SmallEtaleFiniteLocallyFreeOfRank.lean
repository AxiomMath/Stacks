module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteLocallyFree
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRankUnique

/-!
# The rank of a quasi-coherent module is the same étale-locally and Zariski-locally

Let `S` be a scheme and `𝓕` a quasi-coherent `𝒪_S`-module, with associated module `𝓕^a` on the
small étale site of `S` (Stacks 03DU (4)). Then `𝓕^a` is finite locally free of rank `r` on the
small étale site (Stacks 0409) if and only if `𝓕` is finite locally free of rank `r` on the
small Zariski site. The forward direction is
`AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOfRank_associatedModule`. For the converse,
`𝓕` is finite locally free by fpqc descent of finite local freeness along an étale covering
(Stacks 05B2, through
`AlgebraicGeometry.SmallEtale.isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite_associatedModule`).
Over each nonempty member `V` of a covering on which `𝓕|_V` is free of some rank `n`, the module
`𝓕^a` restricted to `V` is free of rank `n` as well, and since `𝓕^a` has rank `r` étale locally
and `V` is nonempty, `n = r`. Empty members are dropped from the covering.

## Main results

* `AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOfRank_of_associatedModule`: étale rank `r`
  implies Zariski rank `r`.
* `AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOfRank_associatedModule_iff`: the two
  agree.

## References

* [Stacks Project, Tag 05B2](https://stacks.math.columbia.edu/tag/05B2)
* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A covering sieve of an object of the small étale site of `S` whose scheme is nonempty
contains an arrow out of an object whose scheme is nonempty. -/
theorem exists_mem_nonempty_of_mem_topology {W : SmallEtale B S hS} {R : Sieve W}
    (hR : R ∈ topology B S hS W) (x : (toScheme B S hS).obj W) :
    ∃ (W' : SmallEtale B S hS) (g : W' ⟶ W), R g ∧ Nonempty ((toScheme B S hS).obj W') := by
  obtain ⟨E, hE, hle⟩ := exists_isCovering_sieve₀_le B S hS hR
  obtain ⟨i, y, -⟩ := jointlySurjective_of_isCovering B S hS hE x
  exact ⟨E.X i, E.f i, hle _ (Sieve.ofArrows_mk _ _ i), ⟨y⟩⟩

/-- **Étale rank `r` implies Zariski rank `r`.** A quasi-coherent `𝒪_S`-module whose associated
module on the small étale site of `S` is finite locally free of rank `r` is finite locally free
of rank `r` on the small Zariski site. -/
theorem isFiniteLocallyFreeOfRank_of_associatedModule (𝓕 : S.Modules) [𝓕.IsQuasicoherent]
    (r : ℕ) (h : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS)
      ((associatedModule B S hS).obj 𝓕) r) :
    RingedSite.IsFiniteLocallyFreeOfRank S.zariskiRingedSite 𝓕 r := by
  have hlf := isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite_associatedModule B S hS 𝓕
    h.isFiniteLocallyFreeOnSite
  have hsite := (SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isColimit 𝓕).1
    (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_isFiniteLocallyFree 𝓕 hlf)
  intro U
  obtain ⟨I, V, f, hf, hfree⟩ := hsite U
  refine ⟨{i : I // Nonempty (V i)}, fun i => V i.1, fun i => f i.1, ?_, fun i => ?_⟩
  · intro x hx
    obtain ⟨V', g, hg, hxV'⟩ := hf x hx
    obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff V f g).1 hg
    have hxi : x ∈ V i := leOfHom a hxV'
    exact ⟨V i, f i, Sieve.ofArrows_mk (fun i : {i : I // Nonempty (V i)} => V i.1)
      (fun i => f i.1) ⟨i, ⟨⟨x, hxi⟩⟩⟩, hxi⟩
  · obtain ⟨n, ι, ⟨hc⟩⟩ := hfree i.1
    obtain ⟨ι', ⟨hc'⟩⟩ := Stacks.SheafOfModules.exists_isColimitCofan_of_iso
      (associatedModuleOverObjIso B S hS (V i.1) 𝓕)
      (Stacks.SheafOfModules.exists_isColimitCofan_pullback
        (sliceStructureMap B S hS (V i.1)) _ (I := ULift.{u} (Fin n))
        ⟨fun j => ι j.down, ⟨(Cofan.isColimitEquivOfEquiv Equiv.ulift (Cofan.mk _ ι)) hc⟩⟩)
    have hn : n = r := h.eq_of_isColimit_cofan_over
      (fun W => Nonempty ((toScheme B S hS).obj W))
      (fun W ⟨x⟩ _ hR => exists_mem_nonempty_of_mem_topology B S hS hR x)
      (fun W ⟨x⟩ => by
        have : Nonempty (⊤ : ((toScheme B S hS).obj W).Opens) := ⟨⟨x, trivial⟩⟩
        show Nontrivial Γ((toScheme B S hS).obj W, ⊤)
        infer_instance)
      (U := (opensToSmallEtale B S hS).obj (V i.1)) i.2
      ⟨fun j => ι' ⟨j⟩, ⟨(Cofan.isColimitEquivOfEquiv Equiv.ulift.symm _) hc'⟩⟩
    subst hn
    exact ⟨ι, ⟨hc⟩⟩

/-- **The rank of a quasi-coherent module is the same étale-locally and Zariski-locally.** A
quasi-coherent `𝒪_S`-module is finite locally free of rank `r` on the small Zariski site of `S`
if and only if its associated module is finite locally free of rank `r` on the small étale
site. -/
theorem isFiniteLocallyFreeOfRank_associatedModule_iff (𝓕 : S.Modules) [𝓕.IsQuasicoherent]
    (r : ℕ) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS)
        ((associatedModule B S hS).obj 𝓕) r ↔
      RingedSite.IsFiniteLocallyFreeOfRank S.zariskiRingedSite 𝓕 r :=
  ⟨isFiniteLocallyFreeOfRank_of_associatedModule B S hS 𝓕 r,
    isFiniteLocallyFreeOfRank_associatedModule B S hS 𝓕 r⟩

end AlgebraicGeometry.SmallEtale
