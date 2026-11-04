module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoverCompactification
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.FiniteReducedEtale

/-!
# The boundary of the compactification of a finite étale cover

For a smooth projective compactification `j : V ⟶ V̄` of a finite étale cover of a smooth curve
(`AlgebraicGeometry.CoverCompactification`), the complement `W = V̄ ∖ V` with its reduced induced
structure is a finite reduced, hence (over a perfect field) étale, `k`-scheme, and every
extended automorphism `σ_a` of `V̄` restricts to `W`. This is the closed complement `Y - V` of
Step 9 of the proof of [Stacks, Tag 03UG].

## Main definitions

* `AlgebraicGeometry.CoverCompactification.boundary`, `boundaryι`: `W` and `W ⟶ V̄`.
* `AlgebraicGeometry.CoverCompactification.boundaryExtend`: the restriction of `σ_a` to `W`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 9.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.CoverCompactification

variable {k : Type u} [Field k] [PerfectField k] {U Ub V : Scheme.{u}} {pU : U ⟶ Spec (.of k)}
  [IsCurve k pU] [Smooth pU] {pUb : Ub ⟶ Spec (.of k)} [IsProper pUb] {jU : U ⟶ Ub}
  [IsOpenImmersion jU] (hjU : jU ≫ pUb = pU) {f : V ⟶ U} [IsFinite f] [Etale f]
  [ConnectedSpace V] (C : CoverCompactification k pUb jU f)

/-- The complement of `V` in `V̄`, as a closed subset. -/
def boundaryCloseds : Closeds C.Vb :=
  ⟨(Set.range C.j.base)ᶜ, C.j.isOpenEmbedding.isOpen_range.isClosed_compl⟩

/-- **The boundary `W = V̄ ∖ V`**, with its reduced induced closed subscheme structure. -/
abbrev boundary : Scheme.{u} := (Scheme.IdealSheafData.vanishingIdeal C.boundaryCloseds).subscheme

/-- The closed immersion `W ⟶ V̄`. -/
abbrev boundaryι : C.boundary ⟶ C.Vb :=
  (Scheme.IdealSheafData.vanishingIdeal C.boundaryCloseds).subschemeι

/-- The image of `W ⟶ V̄` is the complement of the image of `j : V ⟶ V̄`. -/
lemma range_boundaryι : Set.range C.boundaryι.base = (Set.range C.j.base)ᶜ :=
  Scheme.IdealSheafData.range_subschemeι_vanishingIdeal _

/-- `V` and `W` are complementary. -/
lemma range_j_eq_compl : Set.range C.j.base = (Set.range C.boundaryι.base)ᶜ := by
  rw [range_boundaryι, compl_compl]

/-- The boundary has finitely many points. -/
instance : Finite C.boundary := by
  have h : Set.Finite (Set.range C.boundaryι.base) := by
    rw [range_boundaryι]; exact C.finite_compl
  haveI := h.to_subtype
  exact Finite.of_injective_finite_range C.boundaryι.isClosedEmbedding.injective

/-- The boundary is finite over `k`. -/
instance : IsFinite (C.boundaryι ≫ C.q) := by
  haveI : LocallyQuasiFinite (C.boundaryι ≫ C.q) :=
    (locallyQuasiFinite_iff_finite_preimage_singleton).2 fun _ => Set.toFinite _
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-- The boundary is finite étale over `k`. -/
instance : Etale (C.boundaryι ≫ C.q) :=
  Stacks.AlgebraicGeometry.ProperSectionsGeom.etale_of_isFinite_of_isReduced (C.boundaryι ≫ C.q)

omit [PerfectField k] [IsCurve k pU] [Smooth pU] [IsOpenImmersion jU] [IsFinite f] [Etale f] in
include hjU in
/-- **`σ_a` maps the boundary to the boundary.** -/
lemma extend_mem_boundary (a : V ≅ V) (ha : a.hom ≫ f = f) (w : C.Vb)
    (hw : w ∉ Set.range C.j.base) : (C.extend pU hjU a.hom ha).base w ∉ Set.range C.j.base := by
  have ha' : a.inv ≫ f = f := by rw [Iso.inv_comp_eq]; exact ha.symm
  have hinv : C.extend pU hjU a.hom ha ≫ C.extend pU hjU a.inv ha' = 𝟙 _ :=
    (C.extendIso pU hjU a ha).hom_inv_id
  refine fun ⟨v, hv⟩ => hw ⟨a.inv.base v, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← C.j_comp_extend pU hjU a.inv ha', Scheme.Hom.comp_apply, hv,
    ← Scheme.Hom.comp_apply, hinv]
  rfl

omit [IsCurve k pU] [Smooth pU] in
include hjU in
/-- The kernel of `W ⟶ V̄` is contained in the kernel of its composite with `σ_a : V̄ ⟶ V̄`. -/
lemma ker_boundaryι_le_ker (a : V ≅ V) (ha : a.hom ≫ f = f) :
    C.boundaryι.ker ≤ (C.boundaryι ≫ C.extend pU hjU a.hom ha).ker := by
  rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
  refine Scheme.IdealSheafData.vanishingIdeal_antimono ?_
  show closure (Set.range (C.boundaryι ≫ C.extend pU hjU a.hom ha).base) ⊆ _
  refine closure_minimal ?_ C.boundaryCloseds.isClosed
  rintro _ ⟨w, rfl⟩
  exact C.extend_mem_boundary hjU a ha _
    (by rw [← Set.mem_compl_iff, ← range_boundaryι]; exact ⟨w, rfl⟩)

/-- **The restriction `σ_a|_W : W ⟶ W`** of the extension of an automorphism `a` of `V`. -/
def boundaryExtend (a : V ≅ V) (ha : a.hom ≫ f = f) : C.boundary ⟶ C.boundary :=
  IsClosedImmersion.lift C.boundaryι (C.boundaryι ≫ C.extend pU hjU a.hom ha)
    (C.ker_boundaryι_le_ker hjU a ha)

omit [IsCurve k pU] [Smooth pU] in
/-- `σ_a|_W` is compatible with `σ_a` along the closed immersion `W ⟶ V̄`. -/
@[reassoc (attr := simp)]
lemma boundaryExtend_comp_ι (a : V ≅ V) (ha : a.hom ≫ f = f) :
    C.boundaryExtend hjU a ha ≫ C.boundaryι = C.boundaryι ≫ C.extend pU hjU a.hom ha :=
  IsClosedImmersion.lift_fac _ _ _

end AlgebraicGeometry.CoverCompactification

end
