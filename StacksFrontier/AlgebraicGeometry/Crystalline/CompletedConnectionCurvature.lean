module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionDeRham

/-!
# Integrability of a completed connection as the vanishing of its curvature

Remark [Stacks, Tag 07I0] calls a connection `∇ : M → M ⊗ Ω` **integrable** when the composite

`M --∇--> M ⊗ Ω¹ --∇--> M ⊗ Ω²`

is zero, the second map being `m ⊗ ω ↦ ∇(m) ∧ ω + m ⊗ d ω`.  For a connection with values in the
completed tensor product `M ⊗̂_D Ω¹` the second map is the degree-one differential
`Crystalline.CompletedDeRham.differential` of the completed de Rham complex, and this module names
the condition: `Crystalline.CompletedDeRham.IsCurvatureZero`.

Unlike `Crystalline.IsIntegrable`, which is stated in coordinates `x_i` of `D`, this condition
needs no coordinates, which is what makes it the reading of [Stacks, Tag 07JD] over the ring `D'`
of [Stacks, Lemma 60.17.5, Tag 07L5], whose module of differentials has no coordinates of its own.

## References

* [Stacks Project, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
* [Stacks Project, Tag 07JD](https://stacks.math.columbia.edu/tag/07JD)
* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
-/

@[expose] public section

universe u v w

namespace Crystalline

namespace CompletedDeRham

variable (p : ℕ) (D : Type u) [CommRing D] (Om : ℕ → Type v) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module D (Om i)] (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) {dmap : D → Om 1} (M : Type w) [AddCommGroup M]
  [Module D M] (nabla : CompletedConnection p D (Om 1) dmap M)
  (hleib : IsGradedLeibniz D Om wedge deRham dmap)

/-- **A completed connection is integrable** in the sense of Remark [Stacks, Tag 07I0] when its
curvature vanishes: the composite `M --∇--> M ⊗̂ Ω¹ --∇--> M ⊗̂ Ω²` of the connection with the
degree-one differential of the completed de Rham complex is zero. -/
public def IsCurvatureZero : Prop :=
  ∀ m : M, differential p D Om wedge deRham M nabla hleib 1 (nabla m) = 0

end CompletedDeRham

end Crystalline

end
