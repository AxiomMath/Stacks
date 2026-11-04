module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Module
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.RingTheory.Module.LocallyFree.FiniteLocallyFreeOfRank
public import StacksFrontier.RingTheory.Norm.Projective

/-!
# The rank of a module on an algebraic space is the rank of its sections over every chart

Let `F` be an algebraic space over a scheme `S` and `G` an `𝒪_F`-module on its small étale site
which is cartesian on affine charts and finite locally free of rank `r` in the sense of the rank
clause of Stacks 0409.  If over a nonempty affine étale chart `A` the sections `G(A)` form a
finite locally free `𝒪_F(A)`-module of some rank `m`, then `m = r`.

The affine charts over which the sections have rank `r` cover `A`
(`AlgebraicGeometry.Space.freeRankPresieve_mem_topology_of_isFiniteLocallyFreeOfRank`), so a
point of `A` lifts to a nonempty affine chart `T` mapping both to one of them and to `A`.  By
cartesianness the sections over `T` are the base change of those over either chart, so they are
finite locally free of rank `r` and of rank `m` over the nonzero ring `𝒪_F(T)`, and the rank at
a prime of that ring computes both.

## Main results

* `Module.IsFiniteLocallyFreeOfRank.eq_of_nontrivial`: a finite locally free module over a
  nonzero commutative ring has only one rank.
* `AlgebraicGeometry.Space.eq_of_isFiniteLocallyFreeOfRank_sections`: the rank of the sections
  over a nonempty affine chart is the rank of the module.
-/

@[expose] public section

open CategoryTheory Opposite

universe u v

/-- **A finite locally free module over a nonzero commutative ring has a unique rank**: the rank
at any prime is both. -/
theorem Module.IsFiniteLocallyFreeOfRank.eq_of_nontrivial {R : Type u} [CommRing R]
    [Nontrivial R] {M : Type u} [AddCommGroup M] [Module R M] {m r : ℕ}
    (hm : Module.IsFiniteLocallyFreeOfRank R M m) (hr : Module.IsFiniteLocallyFreeOfRank R M r) :
    m = r := by
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum R) := inferInstance
  exact (rankAtStalk_eq_of_isFiniteLocallyFreeOfRank m hm p).symm.trans
    (rankAtStalk_eq_of_isFiniteLocallyFreeOfRank r hr p)

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The sections over an affine chart `T` of a module cartesian on affine charts are the base
change of its sections over an affine chart `W` below which `T` lies, so they inherit a rank. -/
theorem isFiniteLocallyFreeOfRank_sections_of_hom (G : Modules.{u, u} B S hS F hF)
    (hcart : IsCartesianOnAffineCharts G) {W T : SmallEtale B S hS F} (f : T ⟶ W)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W))
    (hT : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj T)) {d : ℕ}
    (h : Module.IsFiniteLocallyFreeOfRank (chartRing B S hS F hF W) (G.val.obj (op W)) d) :
    Module.IsFiniteLocallyFreeOfRank (chartRing B S hS F hF T) (G.val.obj (op T)) d := by
  let := chartAlgebra (hF := hF) f
  have : Module.Finite (chartRing B S hS F hF W) (G.val.obj (op W)) :=
    (Module.IsFiniteLocallyFreeOfRank.finite_and_projective h).1
  exact (h.baseChange (chartRing B S hS F hF T)).of_linearEquiv
    (LinearEquiv.ofBijective (sectionsBaseChange G f) (hcart W T hW hT f))

/-- **The rank of the sections of `G` over a nonempty affine chart is the rank of `G`**, for `G`
cartesian on affine charts and finite locally free of rank `r` in the sense of Stacks 0409. -/
theorem eq_of_isFiniteLocallyFreeOfRank_sections (G : Modules.{u, u} B S hS F hF)
    (hcart : IsCartesianOnAffineCharts G) {m r : ℕ}
    (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS F hF) G r)
    (A : SmallEtale B S hS F)
    (hA : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj A))
    (hm : Module.IsFiniteLocallyFreeOfRank (chartRing B S hS F hF A) (G.val.obj (op A)) m)
    (z : (BigFppfOver.toScheme B S hS).obj A.1.left) : m = r := by
  obtain ⟨V₁, g₁, hg₁, z₁, -⟩ := exists_mem_sieve_scheme_point B S hS F A
    (freeRankPresieve_mem_topology_of_isFiniteLocallyFreeOfRank B S hS F hF G r hr A) z
  obtain ⟨W, t, ff, ⟨hWaff, hWr⟩, -⟩ := hg₁
  obtain ⟨T₀, j, hT₀aff, w₀, -⟩ := exists_affine_chart_at B S hS F V₁ z₁
  have h₁ := isFiniteLocallyFreeOfRank_sections_of_hom B S hS F hF G hcart (j ≫ t) hWaff hT₀aff hWr
  have h₂ := isFiniteLocallyFreeOfRank_sections_of_hom B S hS F hF G hcart (j ≫ g₁) hA hT₀aff hm
  have : Nontrivial (chartRing B S hS F hF T₀) :=
    (((BigFppfOver.toScheme B S hS).obj T₀.1.left).presheaf.germ ⊤ w₀ trivial).hom.domain_nontrivial
  exact h₂.eq_of_nontrivial h₁

end AlgebraicGeometry.Space

end
