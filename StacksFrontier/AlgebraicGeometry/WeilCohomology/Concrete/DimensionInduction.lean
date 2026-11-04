module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Coproduct
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DimensionPart
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.GraphCodimension
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.FibrePowerProjective

/-!
# Induction on the parts of constant dimension of a smooth projective scheme

A smooth projective scheme `X` over `k` is the disjoint union of its open and closed parts
`X_d` of dimension `d` (Stacks 02NM), and only finitely many of them are nonempty, `X` being
quasi-compact. Hence a property of smooth projective schemes which is invariant under
isomorphism, stable under binary disjoint unions and true for every equidimensional scheme holds
for every smooth projective scheme. This is the reduction "let `X = ∐ X_i` be the decomposition
of `X` ... it suffices to show the claim for each `X_i`" made in the proof of Stacks 0FGJ (and of
Stacks 0FHJ).

## Main definitions

* `Stacks.WeilCohomology.SmoothProjectiveScheme.clopenObj`: an open and closed subscheme of a
  smooth projective scheme, as a smooth projective scheme.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.clopenHomOfLE`: the inclusion of one open and
  closed subscheme into a larger one.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.clopenTopIso`: the open and closed subscheme `⊤`
  of `X` is `X`.

## Main results

* `Stacks.WeilCohomology.SmoothProjectiveScheme.nonempty_isColimit_clopen`: if `W` is the
  disjoint union of open and closed `U` and `V`, then `W` is the coproduct of `U` and `V`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.induction_relativeDimension`: the induction
  principle above.

## References

* [Stacks Project, Tag 02NM](https://stacks.math.columbia.edu/tag/02NM)
* [Stacks Project, Tag 0FGJ](https://stacks.math.columbia.edu/tag/0FGJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.WeilCohomology.SmoothProjectiveScheme

variable {k : Type u} [Field k]

/-- An open and closed subscheme `U` of a smooth projective scheme `X` over `k`, as a smooth
projective scheme over `k`: its inclusion is an open immersion, hence smooth, and a closed
immersion, hence H-projective. -/
def clopenObj (X : (SmoothProjectiveScheme k).FullSubcategory) (U : X.obj.left.Opens)
    (hU : IsClopen (U : Set X.obj.left)) : (SmoothProjectiveScheme k).FullSubcategory :=
  haveI := isClosedImmersion_ι_of_isClopen hU
  ⟨Over.mk (U.ι ≫ X.obj.hom), (inferInstance : Smooth (U.ι ≫ X.obj.hom)),
    (isProjectiveMorphism_isClosedImmersion_comp _ _
        ((isProjective_iff_isProjectiveMorphism_of_isAffine _).1
        (SmoothProjectiveScheme.isProjective X))).isProjective⟩

/-- The underlying scheme of `clopenObj X U hU` is `U`. -/
@[simp]
theorem clopenObj_left (X : (SmoothProjectiveScheme k).FullSubcategory) (U : X.obj.left.Opens)
    (hU : IsClopen (U : Set X.obj.left)) : (clopenObj X U hU).obj.left = U.toScheme :=
  rfl

/-- The structure morphism of `clopenObj X U hU` is the inclusion of `U` followed by the
structure morphism of `X`. -/
@[simp]
theorem clopenObj_hom (X : (SmoothProjectiveScheme k).FullSubcategory) (U : X.obj.left.Opens)
    (hU : IsClopen (U : Set X.obj.left)) : (clopenObj X U hU).obj.hom = U.ι ≫ X.obj.hom :=
  rfl

variable {X : (SmoothProjectiveScheme k).FullSubcategory}

/-- The inclusion `U ⟶ V` of open and closed subschemes `U ≤ V` of `X`. -/
def clopenHomOfLE {U V : X.obj.left.Opens} (hU : IsClopen (U : Set X.obj.left))
    (hV : IsClopen (V : Set X.obj.left)) (e : U ≤ V) : clopenObj X U hU ⟶ clopenObj X V hV :=
  ObjectProperty.homMk (Over.homMk (U := (clopenObj X U hU).obj) (V := (clopenObj X V hV).obj)
    (X.obj.left.homOfLE e) (by simp))

/-- The morphism of schemes underlying `clopenHomOfLE hU hV e` is the inclusion `U ⟶ V`. -/
@[simp]
theorem clopenHomOfLE_hom_left {U V : X.obj.left.Opens} (hU : IsClopen (U : Set X.obj.left))
    (hV : IsClopen (V : Set X.obj.left)) (e : U ≤ V) :
    (clopenHomOfLE hU hV e).hom.left = X.obj.left.homOfLE e :=
  rfl

/-- If the open and closed subscheme `W` of `X` is the disjoint union of the open and closed
subschemes `U` and `V`, then `W` is the coproduct of `U` and `V` in the category of smooth
projective schemes over `k`. -/
theorem nonempty_isColimit_clopen {U V W : X.obj.left.Opens} (hU : IsClopen (U : Set X.obj.left))
    (hV : IsClopen (V : Set X.obj.left)) (hW : IsClopen (W : Set X.obj.left)) (hUW : U ≤ W)
    (hVW : V ≤ W) (hdisj : Disjoint U V) (hsup : U ⊔ V = W) :
    Nonempty (IsColimit (BinaryCofan.mk (clopenHomOfLE hU hW hUW) (clopenHomOfLE hV hW hVW))) := by
  obtain ⟨h⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl (X.obj.left.homOfLE hUW)
    (X.obj.left.homOfLE hVW) (by
      rw [Scheme.opensRange_homOfLE, Scheme.opensRange_homOfLE]
      constructor
      · rw [disjoint_iff]
        ext x
        simp only [TopologicalSpace.Opens.coe_inf, Scheme.Hom.coe_preimage, Set.mem_inter_iff,
          Set.mem_preimage, SetLike.mem_coe, TopologicalSpace.Opens.coe_bot,
          Set.mem_empty_iff_false, iff_false, not_and]
        intro hx hx'
        exact (Set.disjoint_left.1 (TopologicalSpace.Opens.coe_disjoint.2 hdisj)) hx hx'
      · rw [codisjoint_iff]
        ext x
        simp only [TopologicalSpace.Opens.coe_sup, Scheme.Hom.coe_preimage, Set.mem_union,
          Set.mem_preimage, SetLike.mem_coe, TopologicalSpace.Opens.coe_top, Set.mem_univ,
          iff_true]
        have hx : W.ι x ∈ W := by
          rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι W]
          exact Set.mem_range_self x
        exact hsup ▸ hx)
  exact ⟨isColimitOfIsColimitMapCofan h⟩

/-- Open and closed subschemes cut out by equal opens are isomorphic. -/
def clopenIsoOfEq {U V : X.obj.left.Opens} (hU : IsClopen (U : Set X.obj.left))
    (hV : IsClopen (V : Set X.obj.left)) (h : U = V) : clopenObj X U hU ≅ clopenObj X V hV := by
  subst h
  exact Iso.refl _

variable (X) in
/-- The open and closed subscheme `⊤` of `X` is `X` itself. -/
def clopenTopIso : clopenObj X ⊤ isClopen_univ ≅ X :=
  (ObjectProperty.fullyFaithfulι _).preimageIso
    (Over.isoMk (f := (clopenObj X ⊤ isClopen_univ).obj) (g := X.obj) X.obj.left.topIso
      (by simp))

/-- The union `X_{<n}` of the parts of `X` of dimension `< n`. -/
def lowDimPart (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℕ) : X.obj.left.Opens :=
  (Finset.range n).sup (dimPart X.obj.hom)

variable (X) in
/-- The union `X_{<n}` of the parts of `X` of dimension `< n` is open and closed. -/
theorem isClopen_lowDimPart (n : ℕ) : IsClopen (lowDimPart X n : Set X.obj.left) := by
  induction n with
  | zero => simpa [lowDimPart] using isClopen_empty
  | succ n ih =>
    rw [lowDimPart, Finset.range_add_one, Finset.sup_insert, TopologicalSpace.Opens.coe_sup]
    exact (relativeDimensionOpen_isClopen _ _ n).union ih

variable (X) in
/-- `X_{<n+1}` is the union of the part `X_n` of dimension `n` and `X_{<n}`. -/
theorem lowDimPart_succ (n : ℕ) : lowDimPart X (n + 1) = dimPart X.obj.hom n ⊔ lowDimPart X n := by
  rw [lowDimPart, Finset.range_add_one, Finset.sup_insert]
  rfl

variable (X) in
/-- The part `X_n` of dimension `n` is disjoint from `X_{<n}`. -/
theorem disjoint_dimPart_lowDimPart (n : ℕ) : Disjoint (dimPart X.obj.hom n) (lowDimPart X n) := by
  rw [lowDimPart, Finset.disjoint_sup_right]
  intro d hd
  exact (isClopenDecomposition_dimPart X.obj.hom).disjoint _ _
    (Nat.ne_of_gt (Finset.mem_range.1 hd))

variable (X) in
/-- Only finitely many parts of `X` of constant dimension are nonempty, `X` being quasi-compact:
`X_{<n} = X` for `n` large. -/
theorem exists_lowDimPart_eq_top : ∃ n, lowDimPart X n = ⊤ := by
  have : CompactSpace X.obj.left := QuasiCompact.compactSpace_of_compactSpace X.obj.hom
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun d : ℕ ↦ ((dimPart X.obj.hom d : X.obj.left.Opens) : Set X.obj.left))
    (fun d ↦ (dimPart X.obj.hom d).isOpen) (by
      intro x _
      have hx : x ∈ (⨆ d, dimPart X.obj.hom d) := by
        rw [(isClopenDecomposition_dimPart X.obj.hom).iSup_eq_top]
        trivial
      rw [TopologicalSpace.Opens.mem_iSup] at hx
      obtain ⟨d, hd⟩ := hx
      exact Set.mem_iUnion.2 ⟨d, (hd : x ∈ ((dimPart X.obj.hom d : X.obj.left.Opens) :
        Set X.obj.left))⟩)
  refine ⟨t.sup id + 1, eq_top_iff.2 fun x _ ↦ ?_⟩
  obtain ⟨d, hd, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact Finset.le_sup (f := dimPart X.obj.hom)
    (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hd))) hx

/-- **Induction on the parts of constant dimension.** A property of smooth projective schemes
over `k` which is invariant under isomorphism, holds for the coproduct of two schemes as soon as
it holds for both, and holds for every scheme equidimensional of some dimension `d` (relative
dimension `d` over `k`, Stacks 02NJ (3); the empty scheme is among them), holds for every smooth
projective scheme over `k`. -/
theorem induction_relativeDimension (P : (SmoothProjectiveScheme k).FullSubcategory → Prop)
    (hiso : ∀ {X Y : (SmoothProjectiveScheme k).FullSubcategory}, (X ≅ Y) → P X → P Y)
    (hcoprod : ∀ {X Y : (SmoothProjectiveScheme k).FullSubcategory} (c : BinaryCofan X Y),
        IsColimit c →
      P X → P Y → P c.pt)
    (hdim : ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ),
        RelativeDimension X.obj.hom d → P X)
    (X : (SmoothProjectiveScheme k).FullSubcategory) : P X := by
  have key (n : ℕ) : P (clopenObj X (lowDimPart X n) (isClopen_lowDimPart X n)) := by
    induction n with
    | zero =>
      -- `X_{<0}` is empty, so it has relative dimension `0`: it has no nonempty fibre.
      refine hdim _ 0 ?_
      rintro s ⟨y⟩
      let z : (lowDimPart X 0).toScheme :=
        (clopenObj X (lowDimPart X 0) (isClopen_lowDimPart X 0)).obj.hom.fiberι s y
      have hz : (lowDimPart X 0).ι z ∈ lowDimPart X 0 := by
        rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]
        exact Set.mem_range_self z
      simp [lowDimPart] at hz
    | succ n ih =>
      have hD := relativeDimensionOpen_isClopen X.obj.hom
        (fun s ↦ isCohenMacaulay_fiber_of_smooth X.obj.hom s) n
      obtain ⟨hc⟩ := nonempty_isColimit_clopen (X := X) hD (isClopen_lowDimPart X n)
        (isClopen_lowDimPart X (n + 1))
        ((lowDimPart_succ X n).symm ▸ le_sup_left) ((lowDimPart_succ X n).symm ▸ le_sup_right)
        (disjoint_dimPart_lowDimPart X n) (lowDimPart_succ X n).symm
      exact hcoprod _ hc (hdim _ n (relativeDimension_partBase X.obj.hom n)) ih
  obtain ⟨n, hn⟩ := exists_lowDimPart_eq_top X
  exact hiso ((clopenIsoOfEq _ isClopen_univ hn) ≪≫ clopenTopIso X) (key n)

end Stacks.WeilCohomology.SmoothProjectiveScheme
