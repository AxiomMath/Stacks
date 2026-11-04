module

public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.ClosedImmersionLimit
public import StacksFrontier.AlgebraicGeometry.Limits.EventuallyClosedImmersion

/-!
# Closed subschemes cut out by an increasing family of ideal sheaves

Let `X` be a scheme and `K : ι → X.IdealSheafData` a monotone family of ideal sheaves indexed by
a directed preorder. The closed subschemes `V(K i)` form an inverse system of closed subschemes
of `X` with closed immersions as transition morphisms, and the closed subscheme cut out by the
supremum `⨆ i, K i` is its limit.

If `j : X ⟶ P` is an immersion into a quasi-compact quasi-separated scheme, `X` is quasi-compact
and quasi-separated, and `V(⨆ i, K i) ⟶ P` is a closed immersion, then `V(K i) ⟶ P` is a closed
immersion for every sufficiently large `i`. This is Tag 0A0N applied to that inverse system; it
is the scheme case of the last step of the proof of Stacks 0A0W, where `X` is the source of a
Chow cover and `P` is a projective space over an affine scheme.

## Main definitions

* `AlgebraicGeometry.monotoneSubschemeDiagram`: the inverse system of the closed subschemes cut
  out by a monotone family of ideal sheaves.
* `AlgebraicGeometry.monotoneSubschemeDiagramι`: its closed immersions into `X`.
* `AlgebraicGeometry.monotoneSubschemeCone`: the cone over it with vertex the closed subscheme
  cut out by an ideal sheaf containing every member.

## Main results

* `AlgebraicGeometry.isLimitMonotoneSubschemeCone`: the cone is a limit cone when that ideal
  sheaf is the supremum of the family.
* `AlgebraicGeometry.exists_forall_ge_isClosedImmersion_subschemeι_comp`: the eventual closed
  immersion statement above.

## References

* [Stacks Project, Tag 0A0N](https://stacks.math.columbia.edu/tag/0A0N)
* [Stacks Project, Tag 0A0W](https://stacks.math.columbia.edu/tag/0A0W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} {ι : Type u} [Preorder ι] (K : ι → X.IdealSheafData) (hK : Monotone K)

/-- The inverse system of the closed subschemes cut out by a monotone family of ideal sheaves,
with the inclusions of closed subschemes as transition morphisms. -/
noncomputable def monotoneSubschemeDiagram : ιᵒᵖ ⥤ Scheme.{u} where
  obj i := (K i.unop).subscheme
  map f := Scheme.IdealSheafData.inclusion (hK (leOfHom f.unop))
  map_id i := (cancel_mono (K i.unop).subschemeι).1 (by simp)
  map_comp f g := (cancel_mono (K _).subschemeι).1 (by simp)

/-- The closed immersions of the members of `AlgebraicGeometry.monotoneSubschemeDiagram`
into `X`. -/
noncomputable def monotoneSubschemeDiagramι :
    monotoneSubschemeDiagram K hK ⟶ (Functor.const ιᵒᵖ).obj X where
  app i := (K i.unop).subschemeι
  naturality i j f := by simp [monotoneSubschemeDiagram]

/-- The component of `AlgebraicGeometry.monotoneSubschemeDiagramι` at `i` is the closed immersion
of the closed subscheme cut out by `K i` into `X`. -/
@[simp]
theorem monotoneSubschemeDiagramι_app (i : ιᵒᵖ) :
    (monotoneSubschemeDiagramι K hK).app i = (K i.unop).subschemeι :=
  rfl

/-- The cone over `AlgebraicGeometry.monotoneSubschemeDiagram` whose vertex is the closed
subscheme cut out by an ideal sheaf containing every member of the family. -/
noncomputable def monotoneSubschemeCone (K₀ : X.IdealSheafData) (hle : ∀ i, K i ≤ K₀) :
    Cone (monotoneSubschemeDiagram K hK) where
  pt := K₀.subscheme
  π :=
    { app i := Scheme.IdealSheafData.inclusion (hle i.unop)
      naturality i j f := (cancel_mono (K j.unop).subschemeι).1 (by
        simp [monotoneSubschemeDiagram]) }

/-- **The closed subscheme cut out by the supremum of a directed family of ideal sheaves is the
limit of the closed subschemes cut out by the members.** -/
noncomputable def isLimitMonotoneSubschemeCone [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (K₀ : X.IdealSheafData) (hle : ∀ i, K i ≤ K₀) (hsup : ⨆ i, K i = K₀) :
    IsLimit (monotoneSubschemeCone K hK K₀ hle) :=
  isLimit_of_iSup_ker_eq K₀.subschemeι (monotoneSubschemeDiagramι K hK)
    (monotoneSubschemeCone K hK K₀ hle).π
    (fun i => Scheme.IdealSheafData.inclusion_subschemeι (hle i.unop))
    (by
      have hk : ∀ i : ιᵒᵖ, ((monotoneSubschemeDiagramι K hK).app i).ker = K i.unop :=
        fun i => (K i.unop).ker_subschemeι
      rw [Scheme.IdealSheafData.ker_subschemeι, ← hsup]
      refine le_antisymm (iSup_le fun i => ?_) (iSup_le fun i => ?_)
      · rw [hk]
        exact le_iSup K i.unop
      · refine le_trans ?_ (le_iSup _ (op i))
        rw [hk])
    (fun i => inferInstanceAs (Mono (K i.unop).subschemeι))

include hK in
/-- **The scheme case of the last step of Stacks 0A0W.** Let `j : X ⟶ P` be an immersion of
quasi-compact quasi-separated schemes and let `K` be a monotone family of ideal sheaves on `X`,
indexed by a nonempty directed preorder, with supremum `K₀`. If the closed subscheme cut out by
`K₀` is a closed subscheme of `P` along `j`, then so is the closed subscheme cut out by `K i`,
for every sufficiently large `i`.

This is Tag 0A0N for the inverse system of the closed subschemes cut out by the `K i`, whose
limit is the closed subscheme cut out by `K₀`
(`AlgebraicGeometry.isLimitMonotoneSubschemeCone`). -/
theorem exists_forall_ge_isClosedImmersion_subschemeι_comp [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {P : Scheme.{u}} (j : X ⟶ P) [IsImmersion j] [CompactSpace P] [QuasiSeparatedSpace P]
    [CompactSpace X] [QuasiSeparatedSpace X] (K₀ : X.IdealSheafData) (hsup : ⨆ i, K i = K₀)
    (hK₀ : IsClosedImmersion (K₀.subschemeι ≫ j)) :
    ∃ i₀ : ι, ∀ i, i₀ ≤ i → IsClosedImmersion ((K i).subschemeι ≫ j) := by
  have hle : ∀ i, K i ≤ K₀ := fun i => hsup ▸ le_iSup K i
  have hc := isLimitMonotoneSubschemeCone K hK K₀ hle hsup
  have hf : (monotoneSubschemeCone K hK K₀ hle).π ≫
      (monotoneSubschemeDiagramι K hK ≫ (Functor.const ιᵒᵖ).map j) =
      (Functor.const ιᵒᵖ).map (K₀.subschemeι ≫ j) := by
    ext i
    show Scheme.IdealSheafData.inclusion (hle i.unop) ≫ (K i.unop).subschemeι ≫ j =
      K₀.subschemeι ≫ j
    rw [Scheme.IdealSheafData.inclusion_subschemeι_assoc]
  have hD₁ : ∀ i, CompactSpace ((monotoneSubschemeDiagram K hK).obj i) := fun i => by
    show CompactSpace (K i.unop).subscheme
    exact QuasiCompact.compactSpace_of_compactSpace (K i.unop).subschemeι
  have hD₂ : ∀ i, QuasiSeparatedSpace ((monotoneSubschemeDiagram K hK).obj i) := fun i => by
    show QuasiSeparatedSpace (K i.unop).subscheme
    exact quasiSeparatedSpace_of_quasiSeparated (K i.unop).subschemeι
  have hD₃ : ∀ {i i' : ιᵒᵖ} (g : i ⟶ i'),
      IsClosedImmersion ((monotoneSubschemeDiagram K hK).map g) := fun {i i'} g => by
    show IsClosedImmersion (Scheme.IdealSheafData.inclusion (hK (leOfHom g.unop)))
    have : IsClosedImmersion (Scheme.IdealSheafData.inclusion (hK (leOfHom g.unop)) ≫
        (K i'.unop).subschemeι) := by
      rw [Scheme.IdealSheafData.inclusion_subschemeι]
      infer_instance
    exact IsClosedImmersion.of_comp_isClosedImmersion _ (K i'.unop).subschemeι
  have hD₄ : ∀ i, LocallyOfFiniteType
      ((monotoneSubschemeDiagramι K hK ≫ (Functor.const ιᵒᵖ).map j).app i) := fun i => by
    show LocallyOfFiniteType ((K i.unop).subschemeι ≫ j)
    infer_instance
  have hK₀' : IsClosedImmersion (X := (monotoneSubschemeCone K hK K₀ hle).pt)
      (K₀.subschemeι ≫ j) := hK₀
  obtain ⟨i₀, hi₀⟩ := eventually_isClosedImmersion_app_of_isLimit (monotoneSubschemeDiagram K hK)
    (monotoneSubschemeDiagramι K hK ≫ (Functor.const ιᵒᵖ).map j) _ hc
    (K₀.subschemeι ≫ j) hf
  exact ⟨i₀.unop, fun i hi => (hi₀ (homOfLE hi).op : IsClosedImmersion
    ((monotoneSubschemeDiagramι K hK ≫ (Functor.const ιᵒᵖ).map j).app (op i)))⟩

end AlgebraicGeometry

end
