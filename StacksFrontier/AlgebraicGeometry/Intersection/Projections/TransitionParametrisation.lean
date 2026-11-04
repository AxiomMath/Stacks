module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.TwoPointFibre

/-!
# A bilinear parametrisation of the endomorphisms carrying one point to another

The incidence correspondence of Tag 0B1S is the set of triples `([f], [f'], [g])` with
`f ∘ g ∈ k ∙ f'`, that is with `g` in the subspace
`AlgebraicGeometry.ProjectiveSpaceOfModule.transitionSubmodule k V f f'` of `End V`. The fibre of
the correspondence over a pair of closed points is therefore a projective linear subspace, but
the subspace *moves* with the pair, and a scheme-theoretic handle on the correspondence needs
that movement written down by a formula which is **polynomial in `f` and `f'`** — otherwise the
total space cannot be exhibited as the image of a product.

This file writes such a formula. For scalars and vectors `c, u, u', w` and an endomorphism `h` put

`G(z) = (c · f u) · f'(z) · u' + f'(w) · (f(u) · h(z) - f(h z) · u)`.

Then

* `f ∘ G = (c · f u · f u') · f'`, so `G` lies in `transitionSubmodule k V f f'` for **every**
  value of the parameters, with no condition relating them to `f` and `f'`
  (`AlgebraicGeometry.ProjectiveSpaceOfModule.comp_transitionEnd`); and
* every element of `transitionSubmodule k V f f'` is a value of `G`
  (`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_transitionEnd_eq`), the parameters being
  read off from the element itself.

`G` is bilinear in `(f, f')` — each of its three terms is a product of one value of `f` and one
value of `f'` — which is what makes its coordinates sections of `𝒪(1,1)` on a product of two
projective spaces, and which is why the parameters `u` and `u'` are kept separate even though
`u' = u` already suffices for the second point above: with `u' = u` the leading coefficient
`c · f u · f u` would be *quadratic* in `f`.

The two points together say that the parametrisation hits the fibre over `([f], [f'])` exactly,
for every pair of nonzero functionals, including the degenerate case `f ∘ g = 0` — which is the
case `c = 0` and is the reason the parametrisation carries a separate scalar slot rather than
normalising `f'(w) = 1`.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionEnd`: the endomorphism `G` above.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.comp_transitionEnd`: the identity
  `f ∘ G = (c · f u · f u') · f'`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionEnd_mem_transitionSubmodule`: `G` always
  carries `[f]` to `[f']`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_transitionEnd_eq`: the parametrisation is onto
  the subspace.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionEnd_eq_sum_basis` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.apply_transitionEnd_eq_sum_basis`: **the bilinear
  expansion in a basis.** Each coordinate `φ(G)` of the parametrisation is the double sum
  `∑ p, ∑ q, f (bₚ) · f' (b_q) · φ(G(εₚ, ε_q))` over a basis `b` of `V` and its dual
  coordinates `ε`, with the parameters untouched. This is the shape that makes `φ(G)` a global
  section of `𝒪(1,1)` on the source of the parametrisation: the coefficients
  `φ(G(εₚ, ε_q))` do not involve `f` or `f'` at all, so they are functions of the parameters
  alone, and the double sum is a combination of the tensors
  `AlgebraicGeometry.ProjectiveSpaceOfModule.pairTautSection bₚ b_q`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.apply_transitionEnd_coord_eq_cubic`: **those
  coefficients as explicit cubics.** `φ(G(εₚ, ε_q))` is a polynomial of degree three in the
  coordinates of `(c, u, u', w, h)` whose own coefficients are the values of `φ` on the
  elementary endomorphisms `LinearMap.smulRight εₜ bᵢ`. Degree three and no higher because the
  two terms of `G` are each trilinear — the first in `(c, u, u')`, the second in `(w, u, h)`.
  Substituting the coordinate functions of the affine parameter factor into this cubic is what
  produces the global functions the classifying morphism's linear map is assembled from; no basis
  of `End V` is needed, the coordinates of `h` being `εᵢ (h (b t))`.

## References

* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 0B2U](https://stacks.math.columbia.edu/tag/0B2U)
-/

@[expose] public section

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- **The bilinear parametrisation of the endomorphisms carrying `[f]` to `[f']`.** For scalars
and vectors `c, u, u', w` and an endomorphism `h` it is

`G(z) = (c · f u) · f'(z) · u' + f'(w) · (f(u) · h(z) - f(h z) · u)`,

a formula bilinear in the pair `(f, f')` whose values fill out
`AlgebraicGeometry.ProjectiveSpaceOfModule.transitionSubmodule k V f f'`. The first term supplies
the component of an endomorphism along which `f` is carried onto `f'`, and the second the
component killing `f`, namely `h` corrected by the projection onto the hyperplane `f = 0`. -/
public noncomputable def transitionEnd (f f' : Module.Dual k V) (c : k) (u u' w : V)
    (h : V →ₗ[k] V) : V →ₗ[k] V :=
  (c * f u) • LinearMap.smulRight f' u' +
    f' w • (f u • h - LinearMap.smulRight (f ∘ₗ h) u)

/-- The value of `transitionEnd k V f f' c u u' w h` at `z` is
`(c · f u) · f'(z) · u' + f'(w) · (f(u) · h(z) - f(h z) · u)`. -/
@[simp]
public theorem transitionEnd_apply (f f' : Module.Dual k V) (c : k) (u u' w : V)
    (h : V →ₗ[k] V) (z : V) :
    transitionEnd k V f f' c u u' w h z =
      (c * f u) • (f' z • u') + f' w • (f u • h z - f (h z) • u) := rfl

/-- **The defining identity of the parametrisation:** composing `G` with `f` returns a multiple
of `f'`, the multiple being `c · f u · f u'`. The second term of `G` contributes nothing, its two
halves having the same composite `f(u) · f(h z)` with opposite signs. -/
public theorem comp_transitionEnd (f f' : Module.Dual k V) (c : k) (u u' w : V)
    (h : V →ₗ[k] V) :
    f ∘ₗ transitionEnd k V f f' c u u' w h = (c * f u * f u') • f' := by
  refine LinearMap.ext fun z => ?_
  rw [LinearMap.comp_apply, transitionEnd_apply, LinearMap.smul_apply]
  simp only [map_add, map_smul, map_sub, smul_eq_mul]
  ring

/-- **The parametrisation lands in the subspace:** every value of `G` carries `[f]` to `[f']`,
for every value of the parameters. -/
public theorem transitionEnd_mem_transitionSubmodule (f f' : Module.Dual k V) (c : k)
    (u u' w : V) (h : V →ₗ[k] V) :
    transitionEnd k V f f' c u u' w h ∈ transitionSubmodule k V f f' := by
  rw [mem_transitionSubmodule_iff, comp_transitionEnd]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self f')

/-- **The parametrisation is onto the subspace.** Given `g` with `f ∘ g ∈ k ∙ f'`, normalise
`u = u'` with `f u = 1` and `w` with `f' w = 1`, take `h = g`, and let `c` be the scalar with
`f ∘ g = c · f'`: then the correction term of `G` cancels the first term exactly and `G = g`.
The case `f ∘ g = 0` is `c = 0`. -/
public theorem exists_transitionEnd_eq {f f' : Module.Dual k V} (hf : f ≠ 0) (hf' : f' ≠ 0)
    {g : V →ₗ[k] V} (hg : g ∈ transitionSubmodule k V f f') :
    ∃ (c : k) (u u' w : V), transitionEnd k V f f' c u u' w g = g := by
  have hone : ∀ {φ : Module.Dual k V}, φ ≠ 0 → ∃ v, φ v = 1 := by
    intro φ hφ
    obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
      by_contra hcon
      exact hφ (LinearMap.ext fun v => not_not.mp (not_exists.mp hcon v))
    exact ⟨(φ v)⁻¹ • v, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hv]⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ((mem_transitionSubmodule_iff _ _ _ _ _).mp hg)
  obtain ⟨u, hu⟩ := hone hf
  obtain ⟨w, hw⟩ := hone hf'
  refine ⟨c, u, u, w, LinearMap.ext fun z => ?_⟩
  have hfg : f (g z) = c * f' z := by
    have hz := LinearMap.congr_fun hc z
    rw [LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply] at hz
    exact hz.symm
  rw [transitionEnd_apply, hu, hw, hfg]
  simp only [mul_one, one_smul, smul_smul]
  abel

/-! ### Bilinearity in the pair of functionals, and the expansion in a basis -/

/-- **The parametrisation as a bilinear map in `(f, f')`.** Each of the three terms of
`AlgebraicGeometry.ProjectiveSpaceOfModule.transitionEnd` is a product of one value of `f` and one
value of `f'`, so for fixed parameters it is bilinear. This is what makes its coordinates sections
of `𝒪(1,1)` on a product of two projective spaces. -/
public noncomputable def transitionEndBilin (c : k) (u u' w : V) (h : V →ₗ[k] V) :
    Module.Dual k V →ₗ[k] Module.Dual k V →ₗ[k] (V →ₗ[k] V) :=
  LinearMap.mk₂ k (fun f f' => transitionEnd k V f f' c u u' w h)
    (fun f₁ f₂ f' => by
      refine LinearMap.ext fun z => ?_
      simp only [transitionEnd_apply, LinearMap.add_apply, LinearMap.add_apply]
      module)
    (fun r f f' => by
      refine LinearMap.ext fun z => ?_
      simp only [transitionEnd_apply, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
      module)
    (fun f f₁' f₂' => by
      refine LinearMap.ext fun z => ?_
      simp only [transitionEnd_apply, LinearMap.add_apply, LinearMap.add_apply]
      module)
    (fun r f f' => by
      refine LinearMap.ext fun z => ?_
      simp only [transitionEnd_apply, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
      module)

/-- Evaluating `transitionEndBilin k V c u u' w h` at `(f, f')` gives
`transitionEnd k V f f' c u u' w h`. -/
@[simp]
public theorem transitionEndBilin_apply (f f' : Module.Dual k V) (c : k) (u u' w : V)
    (h : V →ₗ[k] V) :
    transitionEndBilin k V c u u' w h f f' = transitionEnd k V f f' c u u' w h := rfl

/-- **The expansion of the parametrisation in a basis.** For a basis `b` of `V` with dual
coordinates `b.coord`,

`G(f, f') = ∑ p, ∑ q, (f (b p) · f' (b q)) · G(b.coord p, b.coord q)`,

the parameters being the same throughout. So a linear functional on `End V` applied to `G` is a
combination of the products `f (b p) · f' (b q)` — the values of the tensors of two tautological
sections — whose coefficients `φ (G(b.coord p, b.coord q))` depend on the parameters only, and
polynomially. That is the form the classifying morphism's linear system is assembled in: the
coefficients become global functions on the parameter space, and the products become the sections
`AlgebraicGeometry.ProjectiveSpaceOfModule.pairTautGlobal (b p) (b q)`. -/
public theorem transitionEnd_eq_sum_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι k V)
    (f f' : Module.Dual k V) (c : k) (u u' w : V) (h : V →ₗ[k] V) :
    transitionEnd k V f f' c u u' w h =
      ∑ p, ∑ q, (f (b p) * f' (b q)) •
        transitionEnd k V (b.coord p) (b.coord q) c u u' w h := by
  conv_lhs => rw [← transitionEndBilin_apply, ← b.sum_dual_apply_smul_coord f,
    ← b.sum_dual_apply_smul_coord f']
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smul, LinearMap.smul_apply,
    smul_smul, transitionEndBilin_apply]
  rw [Finset.sum_comm]

/-- **The expansion read through a functional on `End V`**: the coefficients are the values of the
functional on the parametrisation at the pairs of dual basis vectors, and they are linear in the
functional. -/
public theorem apply_transitionEnd_eq_sum_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι k V)
    (φ : Module.Dual k (V →ₗ[k] V)) (f f' : Module.Dual k V) (c : k) (u u' w : V)
    (h : V →ₗ[k] V) :
    φ (transitionEnd k V f f' c u u' w h) =
      ∑ p, ∑ q, f (b p) * f' (b q) *
        φ (transitionEnd k V (b.coord p) (b.coord q) c u u' w h) := by
  rw [transitionEnd_eq_sum_basis k V b f f' c u u' w h, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_smul, smul_eq_mul]

/-! ### The coefficients as cubics in the coordinates of the parameters -/

section Coefficients

variable {ι : Type*} [Fintype ι] (b : Module.Basis ι k V)

/-- `LinearMap.smulRight g v` is linear in `v`, expanded over a basis. -/
private theorem smulRight_eq_sum_coord_vector (g : Module.Dual k V) (v : V) :
    LinearMap.smulRight g v = ∑ i, b.coord i v • LinearMap.smulRight g (b i) := by
  have hv : ∑ i, b.coord i v • b i = v := by
    simpa [Module.Basis.coord_apply] using b.sum_repr v
  refine LinearMap.ext fun z => ?_
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply]
  calc g z • v = g z • ∑ i, b.coord i v • b i := by rw [hv]
    _ = ∑ i, b.coord i v • (g z • b i) := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

/-- `LinearMap.smulRight g v` is linear in `g`, expanded over the dual basis. -/
private theorem smulRight_eq_sum_coord_functional (g : Module.Dual k V) (v : V) :
    LinearMap.smulRight g v = ∑ t, g (b t) • LinearMap.smulRight (b.coord t) v := by
  refine LinearMap.ext fun z => ?_
  have hg : ∑ t, g (b t) * b.coord t z = g z := by
    conv_rhs => rw [← b.sum_dual_apply_smul_coord g]
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun t _ => by rw [LinearMap.smul_apply, smul_eq_mul]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, smul_smul,
    ← Finset.sum_smul, hg]

/-- **An endomorphism is the sum of its rows.** -/
private theorem eq_sum_smulRight_comp (h : V →ₗ[k] V) :
    h = ∑ i, LinearMap.smulRight (b.coord i ∘ₗ h) (b i) := by
  refine LinearMap.ext fun z => ?_
  simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.comp_apply,
    Module.Basis.coord_apply]
  exact (b.sum_repr (h z)).symm

/-- `φ` of a `smulRight` whose functional is a row of `h`, expanded over the elementary
endomorphisms. -/
private theorem apply_smulRight_comp_eq_sum (φ : Module.Dual k (V →ₗ[k] V)) (p : ι) (v : V)
    (h : V →ₗ[k] V) :
    φ (LinearMap.smulRight (b.coord p ∘ₗ h) v) =
      ∑ t, b.coord p (h (b t)) * φ (LinearMap.smulRight (b.coord t) v) := by
  rw [smulRight_eq_sum_coord_functional k V b (b.coord p ∘ₗ h) v, map_sum]
  exact Finset.sum_congr rfl fun t _ => by rw [map_smul, smul_eq_mul]; rfl

/-- **The coefficient of the parametrisation as a cubic in the coordinates of the parameters.**
Writing `E i t = LinearMap.smulRight (εₜ, bᵢ)` for the elementary endomorphism carrying `b t` to
`b i` and killing the other basis vectors, and writing `u_i = εᵢ u`, `h_{it} = εᵢ (h (b t))` for
the coordinates of the parameters,

`φ(G(εₚ, ε_q)) = c · u_p · ∑ j, u'_j · φ(E j q)`
`            + w_q · (u_p · ∑ i, ∑ t, h_{it} · φ(E i t) − ∑ i, u_i · ∑ t, h_{pt} · φ(E i t))`,

a polynomial of degree three in `(c, u, u', w, h)` whose coefficients `φ(E i t)` depend on
nothing but `φ` and the basis. Together with
`AlgebraicGeometry.ProjectiveSpaceOfModule.apply_transitionEnd_eq_sum_basis` this writes every
coordinate of the parametrisation as a combination of the tensors `pairTautSection bₚ b_q` whose
coefficients are cubics in the coordinate functions of the affine parameter factor, which is what
makes them global sections of `𝒪(1,1)` on the source.

The two pieces of `G` are each *trilinear* — the first in `(c, u, u')` and the second in
`(w, u, h)` — which is why the degree is three and no higher, and why the expansion needs only
the linearity of `LinearMap.smulRight` in each of its two arguments together with the expansion
of an endomorphism into its rows. -/
public theorem apply_transitionEnd_coord_eq_cubic (φ : Module.Dual k (V →ₗ[k] V)) (p q : ι)
    (c : k) (u u' w : V) (h : V →ₗ[k] V) :
    φ (transitionEnd k V (b.coord p) (b.coord q) c u u' w h) =
      c * b.coord p u * ∑ j, b.coord j u' * φ (LinearMap.smulRight (b.coord q) (b j)) +
        b.coord q w *
          ((b.coord p u *
              ∑ i, ∑ t, b.coord i (h (b t)) * φ (LinearMap.smulRight (b.coord t) (b i))) -
            ∑ i, b.coord i u *
              ∑ t, b.coord p (h (b t)) * φ (LinearMap.smulRight (b.coord t) (b i))) := by
  have hone : φ (LinearMap.smulRight (b.coord q) u') =
      ∑ j, b.coord j u' * φ (LinearMap.smulRight (b.coord q) (b j)) := by
    rw [smulRight_eq_sum_coord_vector k V b (b.coord q) u', map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]
  have htwo : φ h =
      ∑ i, ∑ t, b.coord i (h (b t)) * φ (LinearMap.smulRight (b.coord t) (b i)) := by
    conv_lhs => rw [eq_sum_smulRight_comp k V b h]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => apply_smulRight_comp_eq_sum k V b φ i (b i) h
  have hthree : φ (LinearMap.smulRight (b.coord p ∘ₗ h) u) =
      ∑ i, b.coord i u *
        ∑ t, b.coord p (h (b t)) * φ (LinearMap.smulRight (b.coord t) (b i)) := by
    rw [smulRight_eq_sum_coord_vector k V b (b.coord p ∘ₗ h) u, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, apply_smulRight_comp_eq_sum k V b φ p (b i) h]
  rw [transitionEnd, map_add, map_smul, map_smul, map_sub, map_smul, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, hone, htwo, hthree, mul_assoc]

end Coefficients

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
