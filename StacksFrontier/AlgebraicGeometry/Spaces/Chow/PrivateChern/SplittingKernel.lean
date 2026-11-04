module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Module
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartwiseRankCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedInjective
public import StacksFrontier.Homology.Perfect.BoundedComplexCokernelRank
public import StacksFrontier.RingTheory.Module.LocallyFree.FiniteLocallyFreeOfRank

/-!
# The kernel of a surjection of locally free modules

Let `F` be an algebraic space and let `p : E → L` be an epimorphism of quasi-coherent
`𝒪_F`-modules, with `E` locally free of rank `r + s` and `L` locally free of rank `s`. Then the
kernel of `p` is locally free of rank `r`. In the proof of the splitting principle (Stacks 0ESC)
this is applied to the tautological quotient `π^*E → 𝒪_P(1)` of a projective bundle, whose
kernel is locally free of rank one less than `E`.

Over an affine chart the sequence of sections `0 → (ker p)(W) → E(W) → L(W) → 0` is exact, the
last map being surjective because `E` and `L` are quasi-coherent; as `L(W)` is projective it
splits, so `(ker p)(W)` is finite projective with rank function `(r + s) - s = r`. The affine
charts over which `E` and `L` have sections of the ranks `r + s` and `s` cover every chart, and
`ker p` is cartesian on affine charts, so the rank of its sections there is its rank.

## Main results

* `Module.IsFiniteLocallyFreeOfRank.ker_of_surjective`: over a commutative ring the kernel of a
  surjection from a module of rank `r + s` onto a module of rank `s` has rank `r`.
* `AlgebraicGeometry.Space.PrivateChern.isFiniteLocallyFreeOfRank_kernel`: the same for an
  epimorphism of quasi-coherent modules on an algebraic space.

## References

* [Stacks Project, Tag 0ESC](https://stacks.math.columbia.edu/tag/0ESC)
* [Stacks Project, Tag 00NX](https://stacks.math.columbia.edu/tag/00NX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-- **The kernel of a surjection of finite locally free modules.** Over a commutative ring, the
kernel of a surjection `M → N` from a module finite locally free of rank `r + s` onto a module
finite locally free of rank `s` is finite locally free of rank `r`: the surjection splits since
`N` is projective, so the kernel is finite projective and its rank adds up with that of `N`. -/
theorem Module.IsFiniteLocallyFreeOfRank.ker_of_surjective {A M N : Type u} [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] {r s : ℕ}
    (hM : Module.IsFiniteLocallyFreeOfRank A M (r + s))
    (hN : Module.IsFiniteLocallyFreeOfRank A N s) (g : M →ₗ[A] N)
    (hg : Function.Surjective g) :
    Module.IsFiniteLocallyFreeOfRank A (LinearMap.ker g) r := by
  obtain ⟨hMf, hMp⟩ := Module.IsFiniteLocallyFreeOfRank.finite_and_projective hM
  obtain ⟨-, hNp⟩ := Module.IsFiniteLocallyFreeOfRank.finite_and_projective hN
  obtain ⟨hfin, hproj, hrank⟩ :=
    Stacks.CokernelRank.finite_projective_ker_and_rankAtStalk_of_surjective g hg
  have := hfin
  have := hproj
  refine Module.isFiniteLocallyFreeOfRank_of_rankAtStalk_eq r fun p => ?_
  have h := congrFun hrank p
  simp only [Pi.add_apply] at h
  rw [Module.rankAtStalk_eq_of_isFiniteLocallyFreeOfRank _ hM p,
    Module.rankAtStalk_eq_of_isFiniteLocallyFreeOfRank _ hN p] at h
  omega

namespace AlgebraicGeometry.Space.PrivateChern

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The abelian structure of the `𝒪_F`-modules, in which the kernel is formed. -/
local instance (priority := 10000) abelian_modules : Abelian (Modules.{u, u} B S hS F hF) :=
  smallEtaleModulesAbelian B S hS (X := (⟨F, hF⟩ : AlgebraicSpaces B S hS))

/-- The sections of a module of rank `d` over an affine chart `W` lying over an affine chart `V`
over which its sections have rank `d` have rank `d`, for a module cartesian on affine charts:
they are the base change of the sections over `V`. -/
theorem isFiniteLocallyFreeOfRank_sections_of_isCartesianOnAffineCharts
    {G : Modules.{u, u} B S hS F hF} (hG : IsCartesianOnAffineCharts G) {V W : SmallEtale B S hS F}
    (k : W ⟶ V) (hV : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V))
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W)) {d : ℕ}
    (h : Module.IsFiniteLocallyFreeOfRank (chartRing B S hS F hF V) (G.val.obj (op V)) d) :
    Module.IsFiniteLocallyFreeOfRank (chartRing B S hS F hF W) (G.val.obj (op W)) d := by
  let := chartAlgebra (hF := hF) k
  have := (Module.IsFiniteLocallyFreeOfRank.finite_and_projective h).1
  exact Module.IsFiniteLocallyFreeOfRank.of_linearEquiv
    (LinearEquiv.ofBijective (sectionsBaseChange G k) (hG V W hV hW k))
    (h.baseChange (chartRing B S hS F hF W))

/-- **The kernel of a surjection of locally free modules is locally free.** Let `p : E → L` be an
epimorphism of quasi-coherent `𝒪_F`-modules with `E` of rank `r + s` and `L` of rank `s`. Then
`ker p` has rank `r`. -/
theorem isFiniteLocallyFreeOfRank_kernel {E L : Modules.{u, u} B S hS F hF} (p : E ⟶ L) [Epi p]
    (hE : E.IsQuasicoherentOnSite) (hL : L.IsQuasicoherentOnSite) {r s : ℕ}
    (hEr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS F hF) E (r + s))
    (hLs : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS F hF) L s) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS F hF) (kernel p) r := by
  have hEc := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF E hE
  have hLc := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF L hL
  have hKc : IsCartesianOnAffineCharts (kernel p) := isCartesianOnAffineCharts_kernel p hEc hLc
  -- the rank of the sections of the kernel over a good affine chart
  have hW : ∀ W : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
      Module.IsFiniteLocallyFreeOfRank (chartRing B S hS F hF W) (E.val.obj (op W)) (r + s) →
      Module.IsFiniteLocallyFreeOfRank (chartRing B S hS F hF W) (L.val.obj (op W)) s →
      Module.IsFiniteLocallyFreeOfRank (chartRing B S hS F hF W)
        ((kernel p).val.obj (op W)) r := by
    intro W hWa hEW hLW
    have hsurj := surjective_val_app_of_epi_of_isQuasicoherentOnSite p ‹_› hE hL W hWa
    have hex := SheafOfModules.exact_kernel_ι_val_app p (op W)
    have hinj : Function.Injective ((kernel.ι p).val.app (op W)) :=
      PresheafOfModules.injective_of_mono
        ((SheafOfModules.forget _).map (kernel.ι p)) (op W)
    have hrange : LinearMap.range ((kernel.ι p).val.app (op W)).hom =
        LinearMap.ker (p.val.app (op W)).hom :=
      SetLike.ext fun x => (hex x).symm
    exact Module.IsFiniteLocallyFreeOfRank.of_linearEquiv
      ((LinearEquiv.ofEq _ _ hrange).symm.trans (LinearEquiv.ofInjective _ hinj).symm)
      (Module.IsFiniteLocallyFreeOfRank.ker_of_surjective hEW hLW _ hsurj)
  refine isFiniteLocallyFreeOfRank_of_chartwise B S hS F hF (kernel p) hKc r fun U => ?_
  have hSE := freeRankPresieve_mem_topology_of_isFiniteLocallyFreeOfRank B S hS F hF E (r + s)
    hEr U
  refine (SmallEtale.topology B S hS F).transitive hSE _ fun W f hf => ?_
  obtain ⟨VE, gE, hE', ⟨hVEa, hVE⟩, rfl⟩ := hf
  have hSL := freeRankPresieve_mem_topology_of_isFiniteLocallyFreeOfRank B S hS F hF L s hLs U
  refine (SmallEtale.topology B S hS F).transitive
    ((SmallEtale.topology B S hS F).pullback_stable (gE ≫ hE') hSL) _ fun W' f' hf' => ?_
  obtain ⟨VL, gL, hL', ⟨hVLa, hVL⟩, hfac⟩ := hf'
  rw [← Sieve.pullback_comp]
  refine (SmallEtale.topology B S hS F).superset_covering ?_
    (affineChartSieve_mem_topology B S hS F W')
  rintro W'' k ⟨Z, a, b, hZa, rfl⟩
  refine ⟨Z, a, (b ≫ f' ≫ gE ≫ hE'), ⟨hZa, hW Z hZa ?_ ?_⟩, by simp⟩
  · exact isFiniteLocallyFreeOfRank_sections_of_isCartesianOnAffineCharts B S hS F hF hEc
      (b ≫ f' ≫ gE) hVEa hZa hVE
  · exact isFiniteLocallyFreeOfRank_sections_of_isCartesianOnAffineCharts B S hS F hF hLc
      (b ≫ gL) hVLa hZa hVL

/-- **The kernel of a surjection of locally free modules is locally free**, quasi-coherence being
automatic: a finite locally free module is quasi-coherent (Stacks 03DL). -/
theorem isFiniteLocallyFreeOfRank_kernel_of_epi {E L : Modules.{u, u} B S hS F hF} (p : E ⟶ L)
    [Epi p] {r s : ℕ}
    (hEr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS F hF) E (r + s))
    (hLs : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS F hF) L s) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS F hF) (kernel p) r := by
  have := SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite
    hEr.isFiniteLocallyFreeOnSite
  have := SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite
    hLs.isFiniteLocallyFreeOnSite
  exact isFiniteLocallyFreeOfRank_kernel B S hS F hF p inferInstance inferInstance hEr hLs

end AlgebraicGeometry.Space.PrivateChern

end
