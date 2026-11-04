module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSheafEtaleLocality
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSheafSliceComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSheafWeakSerre

/-!
# Internal Hom and the flat base change property (Stacks 0764, part (6))

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids. **Stacks 0764** part (6) says
that for `F`, `G` in `Mod(𝒳_étale, 𝒪_𝒳)` with `F` of finite presentation and `G` having the flat
base change property of **Stacks 0762**, the sheaf `𝓗om_{𝒪_𝒳}(F, G)` has the flat base change
property. The property is `AlgebraicGeometry.Stack.HasFlatBaseChangePropertySheafUnivLE`, read in
the source's ambient category, and the internal Hom is `AlgebraicGeometry.Stack.etaleInternalHom`,
the one of **Stacks 06WM** (5).

The argument is local on the target of an arrow, as in the 06WM (5) argument for local
quasi-coherence, rather than the source's identification of the restriction of `𝓗om(F, G)` with
an internal Hom on the small étale site followed by **Stacks 0GN2**. Over an object `y` at which
`F` has a finite presentation `𝒪^k ⟶ 𝒪^n ⟶ F|_{𝒳/y} ⟶ 0`, the restriction of `𝓗om(F, G)` to the
slice `𝒳/y` is the kernel of a map `G^n ⟶ G^k` of sheaves on `𝒳/y`
(`AlgebraicGeometry.Stack.exists_etaleInternalHom_over_iso_kernel`). The comparison map `c_φ` of
**Stacks 0761** at an arrow `φ : x ⟶ y`, read on `𝒳/y`, is natural in the sheaf on `𝒳/y`
(`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FlatBaseChangeSheafSliceComparison.lean`),
and both its source and target are left exact when `φ` lies over a flat morphism, the source by
`AlgebraicGeometry.Stack.preservesFiniteLimits_sheafifiedPullbackComparison`; so `c_φ` is
invertible at `𝓗om(F, G)` once it is at `G`. A general arrow is reduced to this case by base
change along an étale covering of its target on which `F` is finitely presented, by the
étale-local criterion `AlgebraicGeometry.Stack.isIso_restrictSheafPullbackComparison_of_etaleCover`
(the argument of part (3)).

## Main results

* `AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_etaleInternalHom`: **Stacks 0764**,
  part (6), with no hypothesis beyond the source's, for any category fibred in groupoids (the
  source states it for an algebraic stack).
* `AlgebraicGeometry.Stack.exists_etaleInternalHom_over_iso_kernel`: the internal Hom out of a
  module finitely presented over `y`, restricted to `𝒳/y`, as a kernel.
* `isIso_restrictSheafPullbackComparison_etaleInternalHom_of_hasFiniteGlobalPresentation`:
  part (6) at arrows into an object over which `F` is finitely presented.

## References

* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 06WM](https://stacks.math.columbia.edu/tag/06WM)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **The internal Hom out of a module finitely presented over `y`, restricted to `𝒳/y`.** If the
restriction of `F` to the slice `𝒳/y` is the cokernel of a map between finite free modules, then
the restriction of `𝓗om(F, G)` to `𝒳/y` is the kernel of a map between finite products of copies
of the restriction of `G`. -/
theorem exists_etaleInternalHom_over_iso_kernel (y : 𝒳)
    (F G : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)))
    (hy : (F.over y).HasFiniteGlobalPresentation) :
    ∃ (n k : ℕ) (f : (∏ᶜ fun _ : Fin n => G.over y) ⟶ ∏ᶜ fun _ : Fin k => G.over y),
      Nonempty ((etaleInternalHom B S hS p hp F G).over y ≅ kernel f) := by
  classical
  let X := etaleRingedSite B S hS p hp
  let Rs := ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)
  let H := etaleInternalHom B S hS p hp F G
  obtain ⟨n, k, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hb⟩⟩ := hy
  let L := Stacks.SheafOfModules.moduleULift.{max (max v w) w u, u} (Rs.over y)
  have hL : L.FullyFaithful := Stacks.SheafOfModules.moduleULiftFullyFaithful _
  have : PreservesFiniteLimits L := Stacks.SheafOfModules.preservesFiniteLimits_moduleULift
  let IH : SheafOfModules.{max (max v w) w u} (Rs.over y) :=
    (X.over y).internalHomSheaf (F.over y).uliftForPresentation (L.obj (G.over y))
  obtain ⟨f', ⟨e'⟩⟩ : ∃ f' : (∏ᶜ fun _ : Fin n => L.obj (G.over y)) ⟶
      ∏ᶜ fun _ : Fin k => L.obj (G.over y), Nonempty (IH ≅ kernel f') :=
    RingedSite.exists_internalHomSheaf_iso_kernel (X.over y) ι hP κ hQ a b hab hb
      (L.obj (G.over y))
  let eH : L.obj (H.over y) ≅ kernel f' :=
    (SheafOfModules.overFunctor Rs y).mapIso (etaleInternalHomIso B S hS p hp F G) ≪≫
      RingedSite.internalHomSheafOverIso X y F G ≪≫
      (RingedSite.internalHomSheafULiftIso (X.over y) (F.over y) (G.over y)).symm ≪≫ e'
  let eP (m : ℕ) : L.obj (∏ᶜ fun _ : Fin m => G.over y) ≅ ∏ᶜ fun _ : Fin m => L.obj (G.over y) :=
    PreservesProduct.iso L _
  let f : (∏ᶜ fun _ : Fin n => G.over y) ⟶ ∏ᶜ fun _ : Fin k => G.over y :=
    hL.preimage ((eP n).hom ≫ f' ≫ (eP k).inv)
  let eK : L.obj (kernel f) ≅ kernel f' :=
    PreservesKernel.iso L f ≪≫ kernel.mapIso _ _ (eP n) (eP k) (by
      simp [f])
  exact ⟨n, k, f, ⟨hL.preimageIso (eH ≪≫ eK.symm)⟩⟩

variable {x y : 𝒳} (φ : x ⟶ y)

/-- **Stacks 0764, part (6), over an object at which the source is finitely presented.** Let
`φ : x ⟶ y` be an arrow of `𝒳` lying over a flat morphism of schemes, and let `F` be finitely
presented on the slice `𝒳/y`. If the comparison map of `G` at `φ` is invertible, so is the
comparison map of `𝓗om(F, G)` at `φ`. -/
theorem isIso_restrictSheafPullbackComparison_etaleInternalHom_of_hasFiniteGlobalPresentation
    (hflat : Flat (B.inclusion.map (p.map φ).left))
    (F G : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)))
    (hy : (F.over y).HasFiniteGlobalPresentation)
    (hG : IsIso (restrictSheafPullbackComparison B E h S hS p hp φ G)) :
    IsIso (restrictSheafPullbackComparison B E h S hS p hp φ
      (etaleInternalHom B S hS p hp F G)) := by
  have : PreservesFiniteLimits (sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) φ) :=
    preservesFiniteLimits_sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) φ hflat
  obtain ⟨n, k, f, ⟨e⟩⟩ := exists_etaleInternalHom_over_iso_kernel B S hS p hp y F G hy
  let η := sliceSheafComparisonNatTrans B E h S hS p hp φ
  have hG' : IsIso (η.app (G.over y)) :=
    isIso_sliceSheafComparison_of_iso B E h S hS p hp φ
      (overIsoSliceOver B S hS p hp y G).symm
      ((isIso_restrictSheafPullbackComparison_iff_sliceSheafComparison
        B E h S hS p hp φ G).1 hG)
  have hprod : ∀ m : ℕ, IsIso (η.app (∏ᶜ fun _ : Fin m => G.over y)) := fun m =>
    NatTrans.isIso_app_limit η (Discrete.functor fun _ : Fin m => G.over y)
      (fun _ => hG')
  have hker : IsIso (η.app (kernel f)) :=
    NatTrans.isIso_app_limit η (parallelPair f 0) (by
      rintro (_ | _)
      · exact hprod n
      · exact hprod k)
  have hH : IsIso (sliceSheafComparison B E h S hS p hp φ
      (sliceOver B S hS p hp y (etaleInternalHom B S hS p hp F G))) :=
    isIso_sliceSheafComparison_of_iso B E h S hS p hp φ
      (e.symm ≪≫ overIsoSliceOver B S hS p hp y _) hker
  exact (isIso_restrictSheafPullbackComparison_iff_sliceSheafComparison
    B E h S hS p hp φ _).2 hH

/-- **Stacks 0764, part (6).** Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and
let `F`, `G` be étale sheaves of `𝒪_𝒳`-modules, with `F` of finite presentation on `𝒳_étale`
(Stacks 03DL) and `G` with the flat base change property of Stacks 0762. Then the internal Hom
`𝓗om_{𝒪_𝒳}(F, G)` of `Mod(𝒳_étale, 𝒪_𝒳)` has the flat base change property.

Let `φ : x ⟶ y` lie over a flat morphism, and let `{e_j : y_j ⟶ y}` be an étale covering on
whose members `F` has a finite presentation. At every arrow into some `y_j` lying over a flat
morphism the comparison map of `𝓗om(F, G)` is invertible by the presented case proved above, and
that suffices for `c_φ` by the étale-local criterion
`AlgebraicGeometry.Stack.isIso_restrictSheafPullbackComparison_of_etaleCover`. -/
@[stacks 0764 "part (6): for F, G in Mod(𝒳_étale, 𝒪_𝒳) with F of finite presentation and G \
with the flat base change property, the internal Hom 𝓗om_{𝒪_𝒳}(F, G) of Mod(𝒳_étale, 𝒪_𝒳) has \
the flat base change property"]
theorem hasFlatBaseChangePropertySheaf_etaleInternalHom
    (F G : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)))
    (hfp : F.IsFinitePresentationOnSite)
    (hG : HasFlatBaseChangePropertySheafUnivLE B E h S hS p hp G) :
    HasFlatBaseChangePropertySheafUnivLE B E h S hS p hp (etaleInternalHom B S hS p hp F G) := by
  intro x y φ hflat
  obtain ⟨I, V, f, hcov, hpres⟩ := hfp.locally_hasFiniteGlobalPresentation y
  obtain ⟨E', hE', hle⟩ := exists_etaleCovering_le_of_mem_associatedTopology B S hS p hp _ hcov
  have hmem : ((E'.map p).map (BigFppfOver.forget B S hS)).presieve₀ ∈
      etalePrecoverage B ((BigFppfOver.forget B S hS).obj (p.obj y)) := ⟨_, rfl, hE'⟩
  have hetale : ∀ j, Etale (B.inclusion.map (p.map (E'.f j)).left) := fun j =>
    etale_of_mem_etalePrecoverage B _ hmem _ (Presieve.ofArrows.mk j)
  have hsurj := map_mem_schemeEtalePrecoverage_of_mem_etalePrecoverage B _ hmem
  rw [PreZeroHypercover.presieve₀, Presieve.map_ofArrows] at hsurj
  replace hsurj := (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).mp hsurj
  have hpresE : ∀ j, (F.over (E'.X j)).HasFiniteGlobalPresentation := fun j => by
    obtain ⟨W, g, fi, hfi, -⟩ := hle _ _ (Presieve.ofArrows.mk j)
    obtain ⟨i⟩ := hfi
    exact Stacks.SheafOfModules.FinitePresentationTransport.hasFiniteGlobalPresentation_overMap
      F g (hpres i)
  exact isIso_restrictSheafPullbackComparison_of_etaleCover B E h S hS p hp φ hflat E'.f hetale
    hsurj.1 _ fun j _ φ' hφ' =>
      isIso_restrictSheafPullbackComparison_etaleInternalHom_of_hasFiniteGlobalPresentation
        B E h S hS p hp φ' hφ' F G (hpresE j) (hG φ' hφ')

end AlgebraicGeometry.Stack

end
