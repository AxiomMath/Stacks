module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupChowFormula
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupDimension
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ClosedImmersionClass

/-!
# The conormal class of the diagonal

For a smooth projective scheme `X` over `k` with diagonal `Δ : X ⟶ X × X`, the conormal sheaf
`𝒞_{X/X×X}` of `Δ` is the sheaf of differentials `Ω_{X/k}` (Stacks 08S2), so its class in
`K₀(Vect(X))` extends to `X × X`: it is `Δ^*α` for `α = p₁^*[Ω_{X/k}]`, since `p₁ ∘ Δ = id`.
This is the hypothesis on the centre that the blow-up formula of Lemma 0FIH needs when the centre
is the diagonal. When `X` has dimension `d ≥ 1` the diagonal is moreover nowhere dense in
`X × X`, the other hypothesis on the centre: `X × X` has local dimension `2d` everywhere, while an
open subset of `X × X` inside `Δ(X)` would be homeomorphic to an open subset of `X`, of local
dimension `d`.

The conormal sheaf is taken in the presentation `centreConormal` of the blow-up files, the
pullback along the closed factor of `Δ` of its ideal sheaf; the comparison with `Ω_{X/k}` is
`Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal`.

## Main results

* `Stacks.WeilCohomology.SmoothProjectiveScheme.relativeDifferentialsIsoCentreConormalDiag`:
  `Ω_{X/k} ≅ 𝒞_{X/X×X}`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.pullback_diag_pullback_fst_classOf`:
  `Δ^*(p₁^*[Ω_{X/k}]) = [𝒞_{X/X×X}]` in `K₀(Vect(X))`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.exists_pullback_diag_eq_classOf_centreConormal`:
  the class of the conormal sheaf of `Δ` extends to `X × X`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.isNowhereDense_range_diag`: `Δ(X)` is nowhere
  dense in `X × X` when `X` has dimension `d ≥ 1`.

## References

* [Stacks Project, Lemma 0FIH](https://stacks.math.columbia.edu/tag/0FIH)
* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

universe u

namespace Stacks.WeilCohomology.SmoothProjectiveScheme

open AlgebraicGeometry.VectorBundleKZero

variable {k : Type u} [Field k] (X : (SmoothProjectiveScheme k).FullSubcategory)

/-- **`Ω_{X/k} ≅ 𝒞_{X/X×X}`** (Stacks 08S2): the sheaf of differentials of `X` over `k` is the
conormal sheaf of the diagonal, in the presentation `centreConormal`. -/
def relativeDifferentialsIsoCentreConormalDiag :
    Scheme.Hom.relativeDifferentials X.obj.hom ≅ centreConormal (diag X) :=
  Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal X.obj.hom

/-- **`Δ^*(p₁^*[Ω_{X/k}]) = [𝒞_{X/X×X}]`** in `K₀(Vect(X))`: pullback is functorial, `p₁ ∘ Δ` is
the identity, and `Ω_{X/k}` is the conormal sheaf of `Δ` (Stacks 08S2). -/
theorem pullback_diag_pullback_fst_classOf :
    VectorBundleKZero.pullback (diag X).hom.left
        (VectorBundleKZero.pullback (fst X X).hom.left
          (classOf X.obj.left (Scheme.Hom.relativeDifferentials X.obj.hom))) =
      classOf X.obj.left (centreConormal (diag X)) := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Scheme.Hom.relativeDifferentials X.obj.hom) :=
    Scheme.Hom.isFiniteLocallyFree_relativeDifferentials X.obj.hom
  rw [← VectorBundleKZero.pullback_comp,
    show (diag X).hom.left ≫ (fst X X).hom.left = 𝟙 X.obj.left from pullback.diagonal_fst _,
    VectorBundleKZero.pullback_classOf]
  exact (Stacks.Perfect.BoundedLocallyFreeComplexes.classOf_eq_of_iso' _
    ((Scheme.Modules.pullbackId X.obj.left).app _)).trans
    (Stacks.Perfect.BoundedLocallyFreeComplexes.classOf_eq_of_iso' _
      (relativeDifferentialsIsoCentreConormalDiag X))

/-- **The class of the conormal sheaf of the diagonal extends to `X × X`**: some
`α ∈ K₀(Vect(X × X))`, namely `p₁^*[Ω_{X/k}]`, has `Δ^*α = [𝒞_{X/X×X}]`. -/
theorem exists_pullback_diag_eq_classOf_centreConormal :
    ∃ α : VectorBundleKZero (prod X X).obj.left,
      VectorBundleKZero.pullback (diag X).hom.left α =
        classOf X.obj.left (centreConormal (diag X)) :=
  ⟨_, pullback_diag_pullback_fst_classOf X⟩

/-- **The diagonal of a smooth projective scheme of dimension `d ≥ 1` is nowhere dense** in
`X × X`. It is closed, and an open subset `U ⊆ Δ(X)` of `X × X` would be homeomorphic, through
`Δ`, to the open subset `Δ⁻¹(U)` of `X`; at a point of `U` the local dimension of `X × X` is
`2d` and that of `X` is `d`, so `U` is empty. -/
theorem isNowhereDense_range_diag {d : ℕ} (hX : RelativeDimension X.obj.hom d) (hd : 1 ≤ d) :
    IsNowhereDense (Set.range (diag X).hom.left.base) := by
  set Δ := (diag X).hom.left
  have hemb : IsClosedEmbedding Δ.base := Δ.isClosedEmbedding
  rw [hemb.isClosed_range.isNowhereDense_iff, ← Set.not_nonempty_iff_eq_empty]
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := interior_subset hy
  set V : Set X.obj.left := Δ.base ⁻¹' interior (Set.range Δ.base)
  have hVo : IsOpen V := isOpen_interior.preimage Δ.base.hom.continuous
  have hf : IsOpenEmbedding (fun v : V => Δ.base v.1) := by
    refine ⟨hemb.isEmbedding.comp IsEmbedding.subtypeVal, ?_⟩
    convert (isOpen_interior : IsOpen (interior (Set.range Δ.base))) using 1
    ext z
    refine ⟨?_, fun hz => ?_⟩
    · rintro ⟨v, rfl⟩
      exact v.2
    · obtain ⟨w, rfl⟩ := interior_subset hz
      exact ⟨⟨w, hz⟩, rfl⟩
  have h1 := hf.topologicalKrullDimAt_eq (⟨x, hy⟩ : V)
  have h2 := hVo.isOpenEmbedding_subtypeVal.topologicalKrullDimAt_eq (⟨x, hy⟩ : V)
  have hXX := (relativeDimension_iff_forall_topologicalKrullDimAt_of_field
    (prod X X).obj.hom (d + d)).1 (relativeDimension_prodBase k X.obj.hom X.obj.hom hX hX)
    (Δ.base x)
  have hX' := (relativeDimension_iff_forall_topologicalKrullDimAt_of_field
    X.obj.hom d).1 hX x
  simp only at h1 h2
  rw [h1, ← h2, hX'] at hXX
  have : d = d + d := by exact_mod_cast hXX
  omega

end Stacks.WeilCohomology.SmoothProjectiveScheme

end
