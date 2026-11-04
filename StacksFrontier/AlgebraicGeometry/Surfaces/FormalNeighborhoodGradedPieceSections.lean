module

public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveThickeningSurjective
public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodGradedPiece
public import StacksFrontier.AlgebraicGeometry.Surfaces.RestrictedNegativeTwistSections

/-!
# The graded pieces of the projection-kernel filtration are the sections of a twist

Let `D` be an ideal sheaf on a scheme `X`, let `Eₙ₊₁ = (D ^ (n + 1)).subscheme` be its
infinitesimal thickenings and let `A` be
`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodRing D`, filtered by the projection
kernels `Iₙ₊₁ = ker (A ⟶ Γ(Eₙ₊₁, 𝒪))`.

`StacksFrontier/AlgebraicGeometry/Surfaces/FormalNeighborhoodGradedPiece.lean` exhibits the graded
piece `Iₙ₊₁ / Iₙ₊₂` as the kernel of the restriction `Γ(Eₙ₊₂, 𝒪) ⟶ Γ(Eₙ₊₁, 𝒪)`, and
`StacksFrontier/AlgebraicGeometry/Surfaces/RestrictedNegativeTwistSections.lean` exhibits that
kernel as the global sections of `𝒪_X(-D ^ (n + 1))|_D`. This file composes the two: for an
exceptional curve of the first kind the projections of `A` are surjective, so the graded piece
and those sections are the same additive group, elementwise.

That identification is also compatible with the scalars. The sections carry an action of
`Γ(E, 𝒪_E)`, which is `k` for an exceptional curve of the first kind, and the action on the
graded piece is multiplication inside `Γ(Eₙ₊₂, 𝒪)`; the map of [Stacks, Tag 0C4T] is
`𝒪_X`-linear, not visibly `𝒪_E`-linear, but it is nevertheless semilinear for `Γ(E, 𝒪_E)`, by
`Stacks.Divisors.sectionsAddMonoidHom_smul`. That is the second result below.

The sections themselves are computed elsewhere: `𝒪_X(-D ^ (n + 1))|_D` is only
*non-canonically* isomorphic to `𝒪(n + 1)` on `𝐏¹_k`, by
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.nonempty_pullback_negativeTwist_pow_iso_twistingSheaf`, which is enough for a dimension count.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.exists_addMonoidHom_formalNeighborhoodProjection_graded` — the graded piece `Iₙ₊₁ / Iₙ₊₂` and
  the global sections of `𝒪_X(-D ^ (n + 1))|_D` are the same additive group: there is an
  injective additive map from the sections to `Γ(Eₙ₊₂, 𝒪)` whose image is exactly the set of
  projections of elements of `Iₙ₊₁`, and whose zero fibre over `Iₙ₊₁` is `Iₙ₊₂`.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.exists_addMonoidHom_smul_formalNeighborhoodProjection_graded` — **the same map, together
  with its semilinearity over the global functions on `E`.**

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
* [Stacks Project, Tag 0C4T](https://stacks.math.columbia.edu/tag/0C4T)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} {D : X.IdealSheafData} {k : Type u} [Field k]
  {e : projectiveLineProj k ≅ D.subscheme}

namespace IsExceptionalCurveOfFirstKind

/-- An element of `Iₙ₊₁` projecting to `ψ x` lies in `Iₙ₊₂` exactly when `x = 0`, for injective
additive `ψ`. -/
private theorem mem_formalNeighborhoodFiltration_succ_iff_of_injective {M : Type*} [AddZeroClass M]
    (n : ℕ) {ψ : M →+ Γ(thickening D (n + 1), (⊤ : (thickening D (n + 1)).Opens))}
    (hinj : Function.Injective ψ) {x : M} {a : formalNeighborhoodRing D}
    (hax : formalNeighborhoodProjection D (n + 1) a = ψ x) :
    a ∈ formalNeighborhoodFiltration D (n + 2) ↔ x = 0 := by
  rw [show a ∈ formalNeighborhoodFiltration D (n + 2) ↔
      formalNeighborhoodProjection D (n + 1) a = 0 from RingHom.mem_ker, hax]
  exact ⟨fun h => hinj (h.trans (map_zero ψ).symm), fun h => by rw [h, map_zero]⟩

/-- **The graded piece `Iₙ₊₁ / Iₙ₊₂` is the group of global sections of
`𝒪_X(-D ^ (n + 1))|_D`.** For an exceptional curve of the first kind there is an injective
additive map `ψ` from those sections to the global functions on the `(n + 2)`-nd thickening such
that

* every section is the projection of an element of `Iₙ₊₁`, and every element of `Iₙ₊₁` projects
  to a section; and
* an element of `Iₙ₊₁` projecting to `ψ x` lies in `Iₙ₊₂` exactly when `x = 0`.

The first point is [Stacks, Tag 0C4T] with the left exactness of global sections,
`AlgebraicGeometry.Scheme.IdealSheafData`
`.exists_sections_addMonoidHom_ker_thickeningRestriction`, together with the surjectivity of the
projections out of `A`, and the second is the definition of the filtration. -/
theorem exists_addMonoidHom_formalNeighborhoodProjection_graded
    (hE : IsExceptionalCurveOfFirstKind D k e) (n : ℕ) :
    ∃ ψ : Γ(restrictedNegativeTwist (D ^ (n + 1)) D, (⊤ : X.Opens)) →+
        Γ(thickening D (n + 1), (⊤ : (thickening D (n + 1)).Opens)),
      Function.Injective ψ ∧
      (∀ x, ∃ a ∈ formalNeighborhoodFiltration D (n + 1),
        formalNeighborhoodProjection D (n + 1) a = ψ x) ∧
      (∀ a ∈ formalNeighborhoodFiltration D (n + 1),
        ∃ x, ψ x = formalNeighborhoodProjection D (n + 1) a) ∧
      (∀ x, ∀ a ∈ formalNeighborhoodFiltration D (n + 1),
        formalNeighborhoodProjection D (n + 1) a = ψ x →
          (a ∈ formalNeighborhoodFiltration D (n + 2) ↔ x = 0)) := by
  have : Stacks.Divisors.IsEffectiveCartierDivisor D := hE.1
  obtain ⟨ψ, hinj, hker⟩ :=
    exists_sections_addMonoidHom_ker_thickeningRestriction D n
  refine ⟨ψ, hinj, fun x => ?_, fun a ha => ?_, fun x a ha hax => ?_⟩
  · exact exists_projection_eq_of_thickeningRestriction_eq_zero D n
      hE.surjective_thickeningRestriction ((hker (ψ x)).2 ⟨x, rfl⟩)
  · exact (hker _).1 (thickeningRestriction_projection_eq_zero D n ha)
  · exact mem_formalNeighborhoodFiltration_succ_iff_of_injective n hinj hax

/-! ### The named injection, and the three clauses an exceptional curve supplies -/

section Named

variable [Stacks.Divisors.IsEffectiveCartierDivisor D]

/-- **Every section of `𝒪_X(-D ^ (n + 1))|_D` is the projection of an element of `Iₙ₊₁`.** The
named injection of
`AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHom` lands in the kernel of the
thickening restriction, and the projections out of `A` are onto. -/
theorem exists_mem_gradedSectionsHom (hE : IsExceptionalCurveOfFirstKind D k e) (n : ℕ)
    (x : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1))),
      (⊤ : D.subscheme.Opens))) :
    ∃ a ∈ formalNeighborhoodFiltration D (n + 1),
      formalNeighborhoodProjection D (n + 1) a = gradedSectionsHom D n x :=
  exists_projection_eq_of_thickeningRestriction_eq_zero D n hE.surjective_thickeningRestriction
    ((gradedSectionsHom_eq_iff D n _).2 ⟨x, rfl⟩)

/-- **Every element of `Iₙ₊₁` projects to a section of `𝒪_X(-D ^ (n + 1))|_D`.** -/
theorem exists_gradedSectionsHom_eq (n : ℕ) {a : formalNeighborhoodRing D}
    (ha : a ∈ formalNeighborhoodFiltration D (n + 1)) :
    ∃ x, gradedSectionsHom D n x = formalNeighborhoodProjection D (n + 1) a :=
  (gradedSectionsHom_eq_iff D n _).1 (thickeningRestriction_projection_eq_zero D n ha)

/-- **An element of `Iₙ₊₁` lies in `Iₙ₊₂` exactly when the section it projects to vanishes.** -/
theorem mem_succ_iff_gradedSectionsHom (n : ℕ)
    (x : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1))),
      (⊤ : D.subscheme.Opens)))
    {a : formalNeighborhoodRing D}
    (hax : formalNeighborhoodProjection D (n + 1) a = gradedSectionsHom D n x) :
    a ∈ formalNeighborhoodFiltration D (n + 2) ↔ x = 0 := by
  exact mem_formalNeighborhoodFiltration_succ_iff_of_injective n
    (gradedSectionsHom_injective D n) hax

end Named

/-- **The graded piece `Iₙ₊₁ / Iₙ₊₂` is the group of global sections of `𝒪_X(-D ^ (n + 1))|_D`,
compatibly with the scalars.** The same statement as
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.exists_addMonoidHom_formalNeighborhoodProjection_graded`, with one more clause: for every
global function `u` on `Eₙ₊₁` and its restriction `ū` to `E`,

`ψ (ū · x) = u · ψ x`.

Since the action on the graded piece is multiplication inside `Γ(Eₙ₊₁, 𝒪)` and the action on the
sections is that of `Γ(E, 𝒪_E)`, this is what lets the `k`-vector space structure of the
sections — and so the dimension computed by
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.finrank_restrictedNegativeTwistSections` — be read on the graded piece. It is
`Stacks.Divisors.sectionsAddMonoidHom_smul`.

The sections are written as the sections over `E` of the pullback of the ideal sheaf rather than
as the sections of the sealed module `Stacks.Divisors.restrictedNegativeTwist`: the two are the
same type, but the action of `Γ(E, 𝒪_E)` is visible only on the former.

The map is `AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHom`. -/
theorem exists_addMonoidHom_smul_formalNeighborhoodProjection_graded
    (hE : IsExceptionalCurveOfFirstKind D k e) (n : ℕ) :
    ∃ ψ : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1))),
          (⊤ : D.subscheme.Opens)) →+
        Γ(thickening D (n + 1), (⊤ : (thickening D (n + 1)).Opens)),
      Function.Injective ψ ∧
      (∀ x, ∃ a ∈ formalNeighborhoodFiltration D (n + 1),
        formalNeighborhoodProjection D (n + 1) a = ψ x) ∧
      (∀ a ∈ formalNeighborhoodFiltration D (n + 1),
        ∃ x, ψ x = formalNeighborhoodProjection D (n + 1) a) ∧
      (∀ x, ∀ a ∈ formalNeighborhoodFiltration D (n + 1),
        formalNeighborhoodProjection D (n + 1) a = ψ x →
          (a ∈ formalNeighborhoodFiltration D (n + 2) ↔ x = 0)) ∧
      (∀ (u : Γ(thickening D (n + 1), (⊤ : (thickening D (n + 1)).Opens))) x,
        ψ ((inclusion (pow_succ_le_self D (n + 1))).appTop.hom u • x) = u * ψ x) := by
  have : Stacks.Divisors.IsEffectiveCartierDivisor D := hE.1
  exact ⟨gradedSectionsHom D n, gradedSectionsHom_injective D n,
    exists_mem_gradedSectionsHom hE n, fun _ ha => exists_gradedSectionsHom_eq n ha,
    fun x _ _ hax => mem_succ_iff_gradedSectionsHom n x hax,
    fun u x => gradedSectionsHom_smul D n u x⟩

end IsExceptionalCurveOfFirstKind

end AlgebraicGeometry.Scheme.IdealSheafData

end
