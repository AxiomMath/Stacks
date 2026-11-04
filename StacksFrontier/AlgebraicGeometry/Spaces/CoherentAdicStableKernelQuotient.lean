module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.StableKernelLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicAffineQuotientSections
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicStableKernelChartData
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleSectionsInjective

/-!
# The second stabilization of Stacks 087X on an algebraic space

Let `F` be a Noetherian algebraic space, `𝓘 ⊆ 𝒪_F` a quasi-coherent sheaf of ideals and
`α : E ⟶ E'` a morphism of coherent `𝓘`-adic systems.  The first stabilization produced the
stable kernel images `AlgebraicGeometry.Space.stableKernelImage` and their inverse system
`AlgebraicGeometry.Space.stableKernelImageSystem`, a subsystem of `E` with coherent terms
annihilated by `α`.  That system is **not** a coherent adic system — its term at `n` need not be
the quotient of its term at `n + 1` by `𝓘 ^ (n + 1)` — and Stacks 087X repairs this by passing to
the adic quotients: for each fixed exponent `n + 1` the transition maps

    (E_l ⊇) S_l / 𝓘 ^ (n + 1) S_l ⟶ S_m / 𝓘 ^ (n + 1) S_m,    n ≤ m ≤ l,

of the adic quotients of the stable kernel images are eventually isomorphisms in the image level.
**This file proves that.**

The scheme-level counterpart is `Stacks.Coherent.stableKernelImageQuotientMap_eventually_isIso`,
whose proof runs through the affine comparison of Stacks 087W
(`Stacks.Coherent.affineStableKernelImageQuotientMap_bijective`).  An algebraic space has no such
comparison, and the substitute is the chart presentation of
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicStableKernelChartData`: over a Noetherian
affine étale chart `V` there is one module `M` with surjective projections `p k : M ⟶ E_k(V)` and
one submodule `K ⊆ M` whose images `p k '' K` are the sections of the stable kernel images, with
`ker p k ∩ K ⊆ 𝓘(V) ^ (n + 1) K` once `k` is large.  Both `S_l(V) / 𝓘(V) ^ (n + 1) S_l(V)` and
`S_m(V) / 𝓘(V) ^ (n + 1) S_m(V)` are then the intrinsic quotient `K / 𝓘(V) ^ (n + 1) K`, and the
transition between them matches the two presentations; that diagram chase is
`Stacks.AdicCompletion.linearMap_bijective_of_quotient_images`, which is exactly what the scheme
proof consumes after Stacks 087W.  The sections of the adic quotients over an affine chart are
computed by `StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicAffineQuotientSections`.

Being an isomorphism is checked on the finitely many Noetherian affine charts of a covering
family, exactly as in
`AlgebraicGeometry.Space.kernelImages_eventuallyConstant`, and the maximum of the finitely many
chart-local Artin–Rees constants serves globally.

## Main results

* `AlgebraicGeometry.Space.exists_chartStableKernelImageQuotientMap_bijective` — the second
  stabilization on the sections over a Noetherian affine chart.
* `AlgebraicGeometry.Space.stableKernelImageQuotientMap_eventually_isIso` — **the second
  stabilization of Stacks 087X on a Noetherian algebraic space**: for each exponent there is a
  constant past which every transition of the adic quotients of the stable kernel images is an
  isomorphism of `𝒪_F`-modules.

## Implementation notes

The system is indexed by `ℕᵒᵖ` and is zero-indexed: the term at `n` is the Stacks source's
`E_{n + 1}`, which is why the exponent at quotient level `n` is `n + 1`.

The three purely module-theoretic lemmas of `Stacks.AdicCompletion` used here are stated and
proved in
`StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.StableKernelLimit`; they are
about a map between two quotients of two images of one submodule and have nothing to do with
schemes, so they are reused rather than restated.

The Noetherian hypothesis of Stacks 089P is carried as the pair of explicit arguments `hZ`, `hN`
spelling `AlgebraicGeometry.Space.IsNoetherian`, together with quasi-coherence of `𝓘` in the form
`AlgebraicGeometry.Space.IsCartesianOnAffineCharts`, as throughout this development.

## References

* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 089P](https://stacks.math.columbia.edu/tag/089P)
* [Stacks Project, Tag 07UL](https://stacks.math.columbia.edu/tag/07UL)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    (hZ : B.Contains (⊤_ Scheme.{u})) (hN : IsNoetherian B S hS hZ F)
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    {E E' : CoherentAdicSystems B S hS F hF 𝓘}

/-! ### The chart-local statement -/

/-- **The second stabilization of Stacks 087X on the sections over a Noetherian affine chart.**

For an exponent `n` there is a constant `c` such that for all levels `n + c ≤ m ≤ l` the induced
map `S_l / 𝓘 ^ (n + 1) S_l ⟶ S_m / 𝓘 ^ (n + 1) S_m` of adic quotients of the stable kernel
images is bijective on the sections over the chart.

The chart presentation of
`AlgebraicGeometry.Space.exists_chartStableKernelImagePresentation` exhibits both sides as the
intrinsic `𝓘(V) ^ (n + 1)`-adic quotient of one submodule `K` of one module, and
`Stacks.AdicCompletion.linearMap_bijective_of_quotient_images` reads the bijectivity off that;
the sections of the adic quotients are computed by
`AlgebraicGeometry.Space.surjective_val_app_idealPowerQuotient_π` and
`AlgebraicGeometry.Space.ker_val_app_idealPowerQuotient_π`. -/
theorem exists_chartStableKernelImageQuotientMap_bijective (α : E ⟶ E') (n : ℕ)
    {V : SmallEtale B S hS F} (hV : IsNoetherianAffineChart B S hS F V) :
    ∃ c : ℕ, ∀ m : ℕ, n + c ≤ m → ∀ l : ℕ, ∀ hml : m ≤ l,
      Function.Bijective ((idealPowerQuotientMapOfHom B S hS F hF 𝓘 (n + 1)
        (stableKernelImage_project B S hS F hF 𝓘 hZ hN hIcart α m l hml)).val.app (op V)) := by
  obtain ⟨K, p, hpsurj, hptrans, hprange, hpAR⟩ :=
    exists_chartStableKernelImagePresentation B S hS F hF 𝓘 hZ hN hIcart α hV
  obtain ⟨c, hc⟩ := hpAR n
  refine ⟨c, fun m hm l hml => ?_⟩
  -- the two stable kernel images, their inclusions and their quotient projections
  have hScart : ∀ k : ℕ,
      IsCartesianOnAffineCharts (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α k) := fun k =>
    isCartesianOnAffineCharts_stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α k
  have hinj : ∀ k : ℕ, Function.Injective
      ((stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α k).val.app (op V)) := fun k =>
    injective_val_app_of_mono B S hS
      (stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α k) (op V)
  have hrange : ∀ k : ℕ, LinearMap.range
        ((stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α k).val.app (op V)).hom =
      LinearMap.range ((p k).comp K.subtype) := by
    intro k
    rw [LinearMap.range_comp, Submodule.range_subtype]
    exact hprange k
  have hker : ∀ k : ℕ, n + c ≤ k →
      LinearMap.ker ((p k).comp K.subtype) ≤
        chartSectionIdeal B S hS F hF 𝓘 V ^ (n + 1) •
          (⊤ : Submodule (chartRing B S hS F hF V) K) := by
    intro k hk
    rw [LinearMap.ker_comp]
    exact hc k hk
  have hqker : ∀ k : ℕ, LinearMap.ker
        ((cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n + 1)
          (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α k)).ι).val.app (op V)).hom =
      chartSectionIdeal B S hS F hF 𝓘 V ^ (n + 1) •
        (⊤ : Submodule (chartRing B S hS F hF V)
          ((stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α k).val.obj (op V))) := fun k =>
    ker_val_app_idealPowerQuotient_π B S hS F hF 𝓘 hIcart _ (hScart k) (n + 1) hV.1
  have hqsurj : ∀ k : ℕ, Function.Surjective
      ((cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n + 1)
        (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α k)).ι).val.app (op V)) := fun k =>
    surjective_val_app_idealPowerQuotient_π B S hS F hF 𝓘 hIcart _ (hScart k) (n + 1) hV.1
  -- the transition map of the stable kernel images lies over the transition map of `E`
  have hj : ((stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α m).val.app (op V)).hom.comp
        ((stableKernelImage_project B S hS F hF 𝓘 hZ hN hIcart α m l hml).val.app (op V)).hom =
      (((chartSectionsSystem B S hS F hF E.obj V).map (homOfLE hml).op).hom).comp
        ((stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α l).val.app (op V)).hom :=
    congrArg (fun φ : stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α l ⟶ E.obj.obj (op m) =>
        (φ.val.app (op V)).hom)
      (stableKernelImage_project_comp B S hS F hF 𝓘 hZ hN hIcart α m l hml)
  -- the induced map on quotients is compatible with the quotient projections
  have hf : ((idealPowerQuotientMapOfHom B S hS F hF 𝓘 (n + 1)
            (stableKernelImage_project B S hS F hF 𝓘 hZ hN hIcart α m l hml)).val.app
          (op V)).hom.comp
        ((cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n + 1)
          (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α l)).ι).val.app (op V)).hom =
      ((cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n + 1)
            (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m)).ι).val.app (op V)).hom.comp
        ((stableKernelImage_project B S hS F hF 𝓘 hZ hN hIcart α m l hml).val.app (op V)).hom :=
    congrArg (fun φ : stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α l ⟶
          idealPowerQuotient B S hS F hF 𝓘 (n + 1)
            (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m) => (φ.val.app (op V)).hom)
      (π_comp_idealPowerQuotientMapOfHom B S hS F hF 𝓘 (n + 1)
        (stableKernelImage_project B S hS F hF 𝓘 hZ hN hIcart α m l hml))
  -- the projections of the chart presentation are compatible with the transitions of `E`
  have ht : (((chartSectionsSystem B S hS F hF E.obj V).map (homOfLE hml).op).hom).comp
      ((p l).comp K.subtype) = (p m).comp K.subtype := by
    rw [← LinearMap.comp_assoc, hptrans m l hml]
  exact Stacks.AdicCompletion.linearMap_bijective_of_quotient_images
    (chartSectionIdeal B S hS F hF 𝓘 V ^ (n + 1))
    ((p l).comp K.subtype) ((p m).comp K.subtype)
    ((stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α l).val.app (op V)).hom
    ((stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α m).val.app (op V)).hom
    ((cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n + 1)
      (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α l)).ι).val.app (op V)).hom
    ((cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n + 1)
      (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m)).ι).val.app (op V)).hom
    (((chartSectionsSystem B S hS F hF E.obj V).map (homOfLE hml).op).hom)
    ((stableKernelImage_project B S hS F hF 𝓘 hZ hN hIcart α m l hml).val.app (op V)).hom
    ((idealPowerQuotientMapOfHom B S hS F hF 𝓘 (n + 1)
      (stableKernelImage_project B S hS F hF 𝓘 hZ hN hIcart α m l hml)).val.app (op V)).hom
    (hinj l) (hinj m) (hrange l) (hrange m) (hker l (hm.trans hml)) (hker m hm)
    (hqker l) (hqker m) (hqsurj l) (hqsurj m) ht hj hf

/-! ### The global statement -/

/-- **The second stabilization of Stacks 087X on a Noetherian algebraic space.**

For a morphism `α : E ⟶ E'` of coherent `𝓘`-adic systems and an exponent `n` there is a constant
`c` such that for all levels `n + c ≤ m ≤ l` the induced map
`S_l / 𝓘 ^ (n + 1) S_l ⟶ S_m / 𝓘 ^ (n + 1) S_m` of adic quotients of the stable kernel images is
an isomorphism of `𝒪_F`-modules.

Quasi-compactness provides an affine chart with surjective étale structure morphism, local
Noetherianity refines it by finitely many Noetherian affine charts, and on each of those
`AlgebraicGeometry.Space.exists_chartStableKernelImageQuotientMap_bijective` supplies a local
constant; the maximum of those finitely many constants makes the map bijective on the sections
over each of them, hence — both sides being cartesian on affine charts by
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_idealPowerQuotient` — over every affine chart
above one of them, hence invertible on the slice at each, hence invertible. -/
theorem stableKernelImageQuotientMap_eventually_isIso (α : E ⟶ E') (n : ℕ) :
    ∃ c : ℕ, ∀ m : ℕ, n + c ≤ m → ∀ l : ℕ, ∀ hml : m ≤ l,
      IsIso (idealPowerQuotientMapOfHom B S hS F hF 𝓘 (n + 1)
        (stableKernelImage_project B S hS F hF 𝓘 hZ hN hIcart α m l hml)) := by
  classical
  -- an affine chart whose structure morphism is surjective étale
  obtain ⟨U₀, f₀, hU₀aff, hU₀surj, hU₀et⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS F hF).1 hN.1
  let U : SmallEtale B S hS F :=
    ⟨CostructuredArrow.mk f₀, presheaf_etale_of_isEtale B S hS hU₀et⟩
  have hUaff : IsAffine
      ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) := hU₀aff
  have hUsurj : IsSurjective B S hS U.1.hom :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS F hF U₀ f₀).1 hU₀surj
  -- refine it by finitely many Noetherian affine charts
  obtain ⟨Sv, hSv, hfac⟩ := exists_covering_through_noetherianAffine B S hS F hF hN.2.2 U
  obtain ⟨ι, hιfin, V, fV, -, hVle, hVcov⟩ :=
    SmallEtale.exists_finite_affine_refinement B S hS F U hUaff Sv hSv
  choose A lift mc hA hfactor using fun i => hfac (fV i) (hVle _ (Sieve.ofArrows_mk V fV i))
  have hAcov : Sieve.ofArrows A mc ∈ SmallEtale.topology B S hS F U := by
    refine (SmallEtale.topology B S hS F).superset_covering ?_ hVcov
    rintro Y k ⟨W', t, p, ⟨i⟩, hcomp⟩
    refine ⟨A i, t ≫ lift i, mc i, ⟨i⟩, ?_⟩
    rw [Category.assoc, ← hfactor i]
    exact hcomp
  have hAtop := ofObjects_mem_topology_of_ofArrows B S hS F hF hUsurj A mc hAcov
  -- the chart-local constant on each member of the covering
  choose ci hci using fun i =>
    exists_chartStableKernelImageQuotientMap_bijective B S hS F hF 𝓘 hZ hN hIcart α n (hA i)
  obtain ⟨d, hd⟩ := Finite.exists_le ci
  refine ⟨d, fun m hm l hml => ?_⟩
  have hcart : ∀ k : ℕ, IsCartesianOnAffineCharts (idealPowerQuotient B S hS F hF 𝓘 (n + 1)
      (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α k)) := fun k =>
    isCartesianOnAffineCharts_idealPowerQuotient B S hS F hF 𝓘 hIcart _
      (isCartesianOnAffineCharts_stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α k) (n + 1)
  refine Stacks.SheafOfModules.isIso_of_isIso_overFunctor_map hAtop _ fun i => ?_
  refine SmallEtale.isIso_of_bijective_app_of_isAffine B S hS F hF (A i) _ fun Z hZaff => ?_
  exact bijective_val_app_of_bijective_of_cartesian B S hS F hF _ (hcart l) (hcart m)
    (hA i).1 hZaff Z.hom (hci i m ((Nat.add_le_add_left (hd i) n).trans hm) l hml)

end AlgebraicGeometry.Space

end
