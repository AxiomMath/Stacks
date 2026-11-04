module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.ConormalClass.ConormalWedge

/-!
# Charts of a closed immersion by generators of its ideal

Let `i : Z ⟶ X` be a closed immersion.  A *chart* is an open `W ⊆ X` together with sections
`f₁, …, f_c ∈ Γ(W, 𝒪_X)` generating the ideal sheaf of `Z` over `W`.  On a chart the closed
subset `T_{W,f}` outside of which the splice of the Čech complex of the `fᵢ` is acyclic contains
`Z` and meets `W` exactly in `Z ∩ W`, so the change of support `ℋ^c_Z ⟶ ℋ^c_{T_{W,f}}` is an
isomorphism over `W`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.RingedSpace

universe u

namespace Stacks.Perfect.ConormalClass

attribute [local instance 10000] HasDerivedCategory.standard

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The closed subset `Z ⊆ X` underlying the closed immersion. -/
def zeroLocus : Set X := Set.range i.base

/-- The image of a closed immersion is closed. -/
theorem isClosed_zeroLocus : IsClosed (zeroLocus i) :=
  i.isClosedEmbedding.isClosed_range

section Chart

variable {i} (W : X.Opens) {c : ℕ} (f : Fin c → Γ(X, W))

/-- The image in `X` of the union of the principal opens of the equations is the union of the
principal opens of `X`. -/
theorem mem_image_iSup_basicOpen (x : X) :
    x ∈ W.ι ''ᵁ (⨆ j, W.toScheme.basicOpen (chartEq W f j)) ↔ ∃ j, x ∈ X.basicOpen (f j) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨j, hj⟩ := (Opens.mem_iSup).1 hy
    have e1 := (Scheme.Opens.mem_basicOpen_toScheme (U := W) (V := ⊤) (r := chartEq W f j)
      (x := y)).1 hj
    exact ⟨j, ((Scheme.basicOpen_res X (f := f j) (homOfLE W.ι_image_top.le).op).le e1).2⟩
  · rintro ⟨j, hj⟩
    have hxW : x ∈ W := X.basicOpen_le (f j) hj
    refine ⟨⟨x, hxW⟩, (Opens.mem_iSup).2 ⟨j, ?_⟩, rfl⟩
    refine (Scheme.Opens.mem_basicOpen_toScheme (U := W) (V := ⊤) (r := chartEq W f j)
      (x := ⟨x, hxW⟩)).2 ?_
    refine (Scheme.basicOpen_res X (f := f j) (homOfLE W.ι_image_top.le).op).ge ⟨?_, hj⟩
    rwa [W.ι_image_top]

/-- A point lies in the support of the chart if and only if it lies in none of the principal
opens `X.basicOpen (f j)`. -/
theorem mem_chartSupport_iff (x : X) :
    x ∈ chartSupport W (chartEq W f) ↔ ∀ j, x ∉ X.basicOpen (f j) := by
  rw [chartSupport, Set.mem_compl_iff, SetLike.mem_coe, mem_image_iSup_basicOpen, not_exists]

variable (hgen : IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) W f)

omit [IsClosedImmersion i] in
include hgen in
/-- The generators vanish on `Z`. -/
theorem app_chart_eq_zero (j : Fin c) : (i.app W).hom (f j) = 0 := by
  have h := mem_generatedIdealOn X.toRingedSpace W f j
  rwa [← hgen W le_rfl] at h

omit [IsClosedImmersion i] in
include hgen in
/-- **`Z` lies in the support of the chart.** -/
theorem zeroLocus_subset_chartSupport : zeroLocus i ⊆ chartSupport W (chartEq W f) := by
  rintro _ ⟨z, rfl⟩
  refine (mem_chartSupport_iff W f _).2 fun j hj => ?_
  have hxW : i.base z ∈ W := X.basicOpen_le (f j) hj
  have hu := (X.mem_basicOpen (f j) (i.base z) hxW).1 hj
  have hu' := hu.map (i.stalkMap z).hom
  rw [Scheme.Hom.germ_stalkMap_apply, app_chart_eq_zero W f hgen j, map_zero] at hu'
  exact not_isUnit_zero hu'

include hgen in
/-- **The support of the chart meets `W` only in `Z`.** -/
theorem mem_zeroLocus_of_mem_chartSupport (x : X) (hxW : x ∈ W)
    (hx : x ∈ chartSupport W (chartEq W f)) : x ∈ zeroLocus i := by
  by_contra hxZ
  let O : X.Opens := W ⊓ ⟨_, (isClosed_zeroLocus i).isOpen_compl⟩
  have hxO : x ∈ O := ⟨hxW, hxZ⟩
  have hempty : i ⁻¹ᵁ O = ⊥ :=
    eq_bot_iff.2 fun z hz => absurd ⟨z, rfl⟩ hz.2
  have h1 : (i.app O).hom 1 = 0 := by
    have : Subsingleton Γ(Z, i ⁻¹ᵁ O) := by
      rw [hempty]
      infer_instance
    exact Subsingleton.elim _ _
  have hmem : (1 : Γ(X, O)) ∈ (generatedIdealOn X.toRingedSpace W f).obj (op O) := by
    rwa [← hgen O inf_le_left]
  have hg := germ_mem_of_mem_generatedIdealOn W f O 1 hmem x hxO hxW
  rw [map_one] at hg
  have hle : Jid (germFamily X.toRingedSpace W f x hxW) ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    exact fun hu => (mem_chartSupport_iff W f x).1 hx j ((X.mem_basicOpen (f j) x hxW).2 hu)
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    ((Ideal.eq_top_iff_one _).2 (hle hg))

end Chart

end Stacks.Perfect.ConormalClass
