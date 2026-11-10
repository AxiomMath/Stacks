module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.InvariantOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageValuativeDiagram

/-!
# Invariant open neighbourhoods of quasi-compact opens in a flat groupoid

Let `G` be a groupoid scheme whose source and target maps are quasi-compact and flat and whose
object scheme is quasi-separated.  Then every quasi-compact open `W` of the object scheme is
contained in an invariant open which is in turn contained in a quasi-compact open.

## Main results

* `AlgebraicGeometry.GroupoidScheme.exists_invariant_open_between_compact_opens`: the invariant
  open neighbourhood of a quasi-compact open, bounded by a quasi-compact open.

## Implementation notes

The inclusions are expressed in the order on open subsets of the object scheme; the inclusion of
the outer open into the object scheme is automatic.

## References

* [Stacks Project, Tag 0APB](https://stacks.math.columbia.edu/tag/0APB)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Stacks.Groupoids

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}}

/-- The source of the identity arrow at an object is that object. -/
private theorem source_identity_apply (G : GroupoidScheme S) (x : G.objects.left) :
    G.source.left.base (G.identity.left.base x) = x := by
  simpa [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] using
    congrArg (fun f => f.left.base x) G.source_identity

/-- The target of the identity arrow at an object is that object. -/
private theorem target_identity_apply (G : GroupoidScheme S) (x : G.objects.left) :
    G.target.left.base (G.identity.left.base x) = x := by
  simpa [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] using
    congrArg (fun f => f.left.base x) G.target_identity

/-- The source of the inverse of an arrow is the target of that arrow. -/
theorem source_inverse_apply (G : GroupoidScheme S) (r : G.arrows.left) :
    G.source.left.base (G.inverse.left.base r) = G.target.left.base r := by
  simpa [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] using
    congrArg (fun f => f.left.base r) G.source_inverse

/-- The target of the inverse of an arrow is the source of that arrow. -/
private theorem target_inverse_apply (G : GroupoidScheme S) (r : G.arrows.left) :
    G.target.left.base (G.inverse.left.base r) = G.source.left.base r := by
  simpa [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] using
    congrArg (fun f => f.left.base r) G.target_inverse

/-- A point in the closure of the saturation of a closed set is a specialization of a point of
that saturation. -/
private theorem exists_specializes_of_mem_target_image_source_preimage_closure
    (G : GroupoidScheme S)
    [QuasiCompact G.target.left] [QuasiCompact G.source.left]
    (Z : Closeds G.objects.left) (x : G.objects.left)
    (hx : x ∈ closure (G.target.left.base ''
      (G.source.left.base ⁻¹' (Z : Set G.objects.left)))) :
    ∃ y ∈ G.target.left.base ''
      (G.source.left.base ⁻¹' (Z : Set G.objects.left)), y ⤳ x := by
  let F : Closeds G.arrows.left :=
    ⟨G.source.left.base ⁻¹' (Z : Set G.objects.left),
      Z.2.preimage G.source.left.continuous⟩
  let J : G.arrows.left.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal F
  let j : J.subscheme ⟶ G.arrows.left := J.subschemeι
  let f : J.subscheme ⟶ G.objects.left := j ≫ G.target.left
  have hrange : Set.range f.base = G.target.left.base ''
      (G.source.left.base ⁻¹' (Z : Set G.objects.left)) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    rw [Scheme.IdealSheafData.range_subschemeι]
    simp [J, F]
  have hx' : x ∈ f.ker.support := by
    change x ∈ (f.ker.support : Set G.objects.left)
    rw [Scheme.Hom.support_ker]
    simpa [hrange] using hx
  have hxrange : x ∈ Set.range f.imageι.base := by
    rw [Scheme.Hom.imageι, Scheme.IdealSheafData.range_subschemeι]
    exact hx'
  obtain ⟨z, rfl⟩ := hxrange
  obtain ⟨a, ha⟩ := exists_specializes_of_image_point f z
  refine ⟨f.base a, ?_, ha⟩
  rw [Set.mem_image]
  refine ⟨j.base a, ?_, rfl⟩
  have hJ : (J.support : Set G.arrows.left) = (F : Set G.arrows.left) := by
    simp [J]
  change j.base a ∈ (F : Set G.arrows.left)
  rw [← hJ, ← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨a, rfl⟩

/-- When the target map is flat, the saturation of an open set is stable under
generalization. -/
private theorem target_image_source_preimage_is_generization_closed
    (G : GroupoidScheme S) [Flat G.target.left] (W : G.objects.left.Opens) :
    ∀ ⦃x y : G.objects.left⦄, x ∈ G.target.left.base ''
      (G.source.left.base ⁻¹' (W : Set G.objects.left)) → y ⤳ x →
        y ∈ G.target.left.base ''
          (G.source.left.base ⁻¹' (W : Set G.objects.left)) := by
  rintro x y ⟨r, hrW, rfl⟩ hxy
  obtain ⟨r', hrr', htr'⟩ := (Flat.generalizingMap G.target.left) hxy
  exact ⟨r', (hrr'.map G.source.left.continuous).mem_open W.2 hrW, htr'⟩

/-- **Stacks Project, Tag 0APB.** A quasi-compact open in the object scheme of a quasi-compact
flat groupoid scheme has an invariant open neighbourhood contained in a quasi-compact open. -/
@[stacks 0APB]
theorem exists_invariant_open_between_compact_opens
    (G : GroupoidScheme S)
    [QuasiCompact G.source.left] [Flat G.source.left]
    [QuasiCompact G.target.left] [Flat G.target.left]
    [QuasiSeparatedSpace G.objects.left]
    (W : G.objects.left.Opens) (hW : IsCompact (W : Set G.objects.left)) :
    ∃ (V W' : G.objects.left.Opens),
      IsInvariantOpen G V ∧ IsCompact (W' : Set G.objects.left) ∧
        W ≤ V ∧ V ≤ W' := by
  classical
  let E : Set G.objects.left := G.target.left.base ''
    (G.source.left.base ⁻¹' (W : Set G.objects.left))
  obtain ⟨I, hI, K, hK, hE⟩ :=
    target_image_source_preimage_eq_iInter_compact_open G W hW
  let i : I := Classical.choice hI
  let W' : G.objects.left.Opens := ⟨K i, (hK i).1⟩
  have hEsub : E ⊆ (W' : Set G.objects.left) := fun x hx => Set.mem_iInter.mp (hE ▸ hx) i
  let Z : Closeds G.objects.left :=
    ⟨(W' : Set G.objects.left)ᶜ, isClosed_compl_iff.mpr W'.2⟩
  let T : Set G.objects.left := G.target.left.base ''
    (G.source.left.base ⁻¹' (Z : Set G.objects.left))
  let V : G.objects.left.Opens := ⟨(closure T)ᶜ, isClosed_closure.isOpen_compl⟩
  have hEinv : IsInvariantSet G E :=
    isInvariantSet_target_image_source_preimage G W
  have hTinv : IsInvariantSet G T :=
    isInvariantSet_target_image_source_preimage G (Z : Set G.objects.left)
  have hETdisj : Disjoint E T := by
    apply Set.disjoint_left.mpr
    intro x hxE hxT
    obtain ⟨r, hrZ, rfl⟩ := hxT
    have hsourceE : G.source.left.base r ∈ E := by
      simpa [target_inverse_apply] using
        hEinv (G.inverse.left.base r) (source_inverse_apply G r ▸ hxE)
    exact hrZ (hEsub hsourceE)
  have hEgen : ∀ ⦃x y : G.objects.left⦄, x ∈ E → y ⤳ x → y ∈ E :=
    target_image_source_preimage_is_generization_closed G W
  have hEdisjClosure : Disjoint E (closure T) := by
    apply Set.disjoint_left.mpr
    intro x hxE hxClosure
    obtain ⟨y, hyT, hyx⟩ :=
      exists_specializes_of_mem_target_image_source_preimage_closure G Z x hxClosure
    exact (Set.disjoint_left.mp hETdisj) (hEgen hxE hyx) hyT
  have hClosureInv : ∀ r : G.arrows.left,
      G.source.left.base r ∈ closure T → G.target.left.base r ∈ closure T := by
    intro r hr
    obtain ⟨y, hyT, hys⟩ :=
      exists_specializes_of_mem_target_image_source_preimage_closure G Z
        (G.source.left.base r) hr
    obtain ⟨r', hrr', hsr'⟩ := (Flat.generalizingMap G.source.left) hys
    have htargetT : G.target.left.base r' ∈ T := hTinv r' (hsr' ▸ hyT)
    exact closure_mono (Set.singleton_subset_iff.mpr htargetT)
      (specializes_iff_mem_closure.mp (hrr'.map G.target.left.continuous))
  have hClosureBack : ∀ r : G.arrows.left,
      G.target.left.base r ∈ closure T → G.source.left.base r ∈ closure T := by
    intro r htr
    simpa [target_inverse_apply] using
      hClosureInv (G.inverse.left.base r)
        (by simpa [source_inverse_apply] using htr)
  have hsubset : ∀ A : Set G.objects.left,
      A ⊆ G.target.left.base '' (G.source.left.base ⁻¹' A) := fun A x hx =>
    ⟨G.identity.left.base x, by simpa [source_identity_apply] using hx,
      target_identity_apply G x⟩
  refine ⟨V, W', ?_, (hK i).2, ?_, ?_⟩
  · change IsInvariantSet G (V : Set G.objects.left)
    intro r hr
    change G.target.left.base r ∈ (closure T)ᶜ
    by_contra htr
    exact hr (hClosureBack r (by simpa [V] using htr))
  · intro x hx
    change x ∈ (closure T)ᶜ
    intro hxClosure
    exact (Set.disjoint_left.mp hEdisjClosure) (hsubset _ hx) hxClosure
  · intro x hx
    by_contra hxW'
    exact hx (subset_closure (hsubset _ hxW'))

end AlgebraicGeometry.GroupoidScheme

end
