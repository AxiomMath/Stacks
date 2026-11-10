module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober
public import StacksFrontier.Topology.Dimension.DimensionLEOne

/-!
# The fibres of a contraction are determined by its contracted locus

Let `X` be a Noetherian sober `T₀` space in which every point is closed or the generic point of
an irreducible component (as for a scheme of dimension one), and let `f : X → Y` be a continuous
closed map whose fibres are preconnected. Call the union of the irreducible components of `X` on
which `f` is constant the *contracted locus* of `f`. Then two distinct points of `X` have the
same image exactly when they lie in the same connected component of the contracted locus.

In particular two such maps out of `X` with the same contracted locus identify the same pairs of
points. Together with the descent of morphisms along a contraction this shows that a contraction
of a curve is determined, up to unique isomorphism, by the components it contracts.

## Main definitions

* `contractedLocus f`: the union of the irreducible components of `X` with subsingleton image.

## Main results

* `apply_eq_apply_iff_of_isClosedMap`: the fibres of `f` are the connected components of the
  contracted locus together with the singletons.
* `apply_eq_apply_iff_of_contractedLocus_eq`: two such maps with the same contracted locus have
  the same fibres.
* `IsPreconnected.subsingleton_of_subset_finite`: a preconnected subset of a finite set of closed
  points has at most one point.
* `isClosed_singleton_or_closure_mem_irreducibleComponents`: in a `T₀` space of Krull dimension
  at most one every point is closed or the generic point of an irreducible component.
* `preimage_singleton_eq_singleton_of_mem_diff`: for `X = C ∪ X'` with `C`, `X'` closed and `f`
  with preconnected fibres, a point of `C ∖ X'` whose fibre meets `C` discretely is alone in its
  fibre.
-/

@[expose] public section

open Set Topology TopologicalSpace

variable {X Y Y' : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Y']

/-- The union of the irreducible components of `X` on which `f` is constant. -/
def contractedLocus (f : X → Y) : Set X :=
  ⋃₀ {C | C ∈ irreducibleComponents X ∧ (f '' C).Subsingleton}

omit [TopologicalSpace Y] in
/-- A point lies in the contracted locus of `f` if and only if it lies in an irreducible component
of `X` whose image under `f` is a subsingleton. -/
theorem mem_contractedLocus_iff {f : X → Y} {x : X} :
    x ∈ contractedLocus f ↔
      ∃ C ∈ irreducibleComponents X, (f '' C).Subsingleton ∧ x ∈ C := by
  simp [contractedLocus, and_assoc]

/-- A preconnected set covered by a closed point `z` and a closed set `B`, and containing a point
other than `z`, has `z` in `B`. -/
private theorem IsPreconnected.mem_of_subset_singleton_union {F B : Set Y} {z w : Y}
    (hF : IsPreconnected F) (hz : IsClosed ({z} : Set Y)) (hB : IsClosed B)
    (hcover : F ⊆ {z} ∪ B) (hzF : z ∈ F) (hwF : w ∈ F) (hwz : w ≠ z) : z ∈ B := by
  obtain ⟨v, -, hvz, hvB⟩ := isPreconnected_closed_iff.mp hF {z} B hz hB hcover
    ⟨z, hzF, rfl⟩ ⟨w, hwF, (hcover hwF).resolve_left hwz⟩
  exact mem_singleton_iff.1 hvz ▸ hvB

/-- A preconnected subset of a finite set of closed points has at most one point. -/
theorem IsPreconnected.subsingleton_of_subset_finite {S T : Set Y} (hS : S.Finite)
    (hcl : ∀ y ∈ S, IsClosed ({y} : Set Y)) (hT : IsPreconnected T) (hTS : T ⊆ S) :
    T.Subsingleton := by
  intro a ha b hb
  by_contra hab
  have hB : IsClosed (S \ {a}) := by
    rw [← biUnion_of_singleton (S \ {a})]
    exact hS.sdiff.isClosed_biUnion fun y hy ↦ hcl y hy.1
  exact (hT.mem_of_subset_singleton_union (hcl a (hTS ha)) hB
    (fun z hz ↦ (em (z = a)).imp id fun h ↦ ⟨hTS hz, h⟩) ha hb fun h ↦ hab h.symm).2 rfl

/-- In a `T₀` space of Krull dimension at most one every point is closed or the generic point of
an irreducible component. -/
theorem isClosed_singleton_or_closure_mem_irreducibleComponents [T0Space X]
    (hdim : topologicalKrullDim X ≤ 1) (x : X) :
    IsClosed ({x} : Set X) ∨ closure {x} ∈ irreducibleComponents X := by
  by_cases h : closure ({x} : Set X) ∈ irreducibleComponents X
  · exact Or.inr h
  refine Or.inl (Stacks.Topology.Dimension.isClosed_singleton_of_not_irreducibleComponent_subset
    (T := closure ({x} : Set X)) hdim isClosed_closure (fun C hC hCsub ↦ h ?_)
    (subset_closure (mem_singleton x)))
  rwa [← hC.eq_of_le isIrreducible_singleton.closure hCsub]

/-- The image under a continuous closed map of a connected component of its contracted locus is a
subsingleton. -/
private theorem subsingleton_image_connectedComponentIn_contractedLocus [NoetherianSpace X]
    {f : X → Y} (hf : Continuous f) (hcl : IsClosedMap f) (x : X) :
    (f '' connectedComponentIn (contractedLocus f) x).Subsingleton := by
  set Z := contractedLocus f
  have hfinC : {C | C ∈ irreducibleComponents X ∧ (f '' C).Subsingleton}.Finite :=
    NoetherianSpace.finite_irreducibleComponents.subset fun _ h ↦ h.1
  have hS : (f '' Z).Finite := by
    refine (hfinC.biUnion fun C hC ↦ hC.2.finite).subset ?_
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨C, hC, hsub, hzC⟩ := mem_contractedLocus_iff.1 hz
    exact mem_biUnion ⟨hC, hsub⟩ ⟨z, hzC, rfl⟩
  have hScl : ∀ y ∈ f '' Z, IsClosed ({y} : Set Y) := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨C, hC, hsub, hzC⟩ := mem_contractedLocus_iff.1 hz
    have hCc : IsClosed (f '' C) := hcl _ (isClosed_of_mem_irreducibleComponents C hC)
    rwa [hsub.eq_singleton_of_mem (mem_image_of_mem f hzC)] at hCc
  exact (isPreconnected_connectedComponentIn.image f hf.continuousOn).subsingleton_of_subset_finite
    hS hScl (image_mono (connectedComponentIn_subset Z x))

section Fibres

variable [NoetherianSpace X] [QuasiSober X] [T0Space X]

omit [NoetherianSpace X] [T0Space X] in
/-- In a Noetherian sober space where every point is closed or generic in a component, every
irreducible closed set is a closed point or an irreducible component. -/
theorem IsIrreducible.eq_singleton_or_mem_irreducibleComponents
    (hdim : ∀ x : X, IsClosed ({x} : Set X) ∨ closure {x} ∈ irreducibleComponents X)
    {T : Set X} (hT : IsIrreducible T) (hTc : IsClosed T) :
    (∃ t, T = {t} ∧ IsClosed ({t} : Set X)) ∨ T ∈ irreducibleComponents X := by
  have hg := hT.isGenericPoint_genericPoint_closure
  rw [hTc.closure_eq] at hg
  rcases hdim hT.genericPoint with h | h
  · exact Or.inl ⟨_, hg.def.symm.trans h.closure_eq, h⟩
  · exact Or.inr (hg.def ▸ h)

omit [NoetherianSpace X] [QuasiSober X] in
/-- Two points whose closures are irreducible components, one specializing to the other, are
equal. -/
theorem eq_of_mem_closure_of_closure_mem_irreducibleComponents {x w : X}
    (hw : closure {w} ∈ irreducibleComponents X) (hwx : w ∈ closure {x}) : w = x :=
  (inseparable_iff_closure_eq.2 (hw.eq_of_le isIrreducible_singleton.closure
    (closure_minimal (singleton_subset_iff.2 hwx) isClosed_closure))).eq

omit [TopologicalSpace Y] [T0Space X] in
/-- A closed preconnected set with at least two points on which `f` is constant lies in the
contracted locus of `f`. -/
private theorem IsPreconnected.subset_contractedLocus
    (hdim : ∀ x : X, IsClosed ({x} : Set X) ∨ closure {x} ∈ irreducibleComponents X)
    {f : X → Y} {F : Set X} (hFc : IsClosed F) (hFconn : IsPreconnected F)
    (hFnt : F.Nontrivial) (hFf : (f '' F).Subsingleton) : F ⊆ contractedLocus f := by
  obtain ⟨S, hSfin, hSc, hSirr, hFS⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hFc
  -- every piece of `F` is a closed point or a component contracted by `f`
  have hpiece : ∀ T ∈ S, (∃ t, T = {t} ∧ IsClosed ({t} : Set X)) ∨
      T ⊆ contractedLocus f := by
    intro T hT
    refine (hSirr T hT).eq_singleton_or_mem_irreducibleComponents hdim (hSc T hT) |>.imp
      id fun hcomp ↦ ?_
    have hTF : T ⊆ F := hFS ▸ subset_sUnion_of_mem hT
    exact fun z hz ↦ mem_contractedLocus_iff.2 ⟨T, hcomp, hFf.anti (image_mono hTF), hz⟩
  intro z hz
  by_contra hzZ
  -- `z` is an isolated point of `F`
  have hzS : ∀ T ∈ S, z ∈ T → T = {z} := by
    intro T hT hzT
    rcases hpiece T hT with ⟨t, rfl, -⟩ | h
    · rw [mem_singleton_iff.1 hzT]
    · exact absurd (h hzT) hzZ
  obtain ⟨T₀, hT₀, hzT₀⟩ : ∃ T ∈ S, z ∈ T := by rwa [hFS] at hz
  have hzc : IsClosed ({z} : Set X) := hzS T₀ hT₀ hzT₀ ▸ hSc T₀ hT₀
  set B := ⋃₀ {T | T ∈ S ∧ z ∉ T}
  have hBc : IsClosed B :=
    (hSfin.subset fun _ h ↦ h.1).isClosed_sUnion fun T hT ↦ hSc T hT.1
  have hcover : F ⊆ {z} ∪ B := by
    intro w hw
    rw [hFS] at hw
    obtain ⟨T, hT, hwT⟩ := hw
    by_cases hzT : z ∈ T
    · exact Or.inl (by rwa [hzS T hT hzT] at hwT)
    · exact Or.inr ⟨T, ⟨hT, hzT⟩, hwT⟩
  obtain ⟨w, hwF, hwz⟩ := hFnt.exists_ne z
  obtain ⟨T, ⟨-, hzT⟩, hzT'⟩ := hFconn.mem_of_subset_singleton_union hzc hBc hcover hz hwF hwz
  exact hzT hzT'

omit [QuasiSober X] in
/-- If two distinct points have the same image under a closed map `f` whose fibre through them is
preconnected, then that image is a closed point. -/
private theorem isClosed_singleton_apply_of_apply_eq_apply
    (hdim : ∀ x : X, IsClosed ({x} : Set X) ∨ closure {x} ∈ irreducibleComponents X)
    {f : X → Y} (hcl : IsClosedMap f) {x x' : X} (hFconn : IsPreconnected (f ⁻¹' {f x}))
    (hxx' : f x = f x') (hxe : x ≠ x') : IsClosed ({f x} : Set Y) := by
  by_contra hy
  set F := f ⁻¹' {f x}
  have hxF : x ∈ F := rfl
  have hx'F : x' ∈ F := hxx'.symm
  have hgen : ∀ z ∈ F, closure {z} ∈ irreducibleComponents X := by
    intro z hz
    refine (hdim z).resolve_left fun hzc ↦ hy ?_
    have := hcl _ hzc
    rwa [image_singleton, show f z = f x from hz] at this
  have hfin : {T | ∃ w ∈ F, w ≠ x ∧ T = closure {w}}.Finite :=
    NoetherianSpace.finite_irreducibleComponents.subset fun T ⟨w, hw, _, hT⟩ ↦
      hT ▸ hgen w hw
  set B := ⋃₀ {T | ∃ w ∈ F, w ≠ x ∧ T = closure {w}}
  have hBc : IsClosed B := hfin.isClosed_sUnion fun T ⟨_, _, _, hT⟩ ↦ hT ▸ isClosed_closure
  have hcover : F ⊆ closure {x} ∪ B := by
    intro w hw
    by_cases h : w = x
    · exact Or.inl (h ▸ subset_closure rfl)
    · exact Or.inr ⟨closure {w}, ⟨w, hw, h, rfl⟩, subset_closure rfl⟩
  obtain ⟨v, hvF, hvx, hvB⟩ := isPreconnected_closed_iff.mp hFconn _ B isClosed_closure hBc
    hcover ⟨x, hxF, subset_closure rfl⟩
    ⟨x', hx'F, closure {x'}, ⟨x', hx'F, Ne.symm hxe, rfl⟩, subset_closure rfl⟩
  obtain ⟨T, ⟨w, hwF, hwx, rfl⟩, hvT⟩ := hvB
  exact hwx ((eq_of_mem_closure_of_closure_mem_irreducibleComponents (hgen v hvF) hvT).symm.trans
    (eq_of_mem_closure_of_closure_mem_irreducibleComponents (hgen v hvF) hvx))

/-- **The fibres of a contraction.** Let `f : X → Y` be a continuous closed map with preconnected
fibres, on a Noetherian sober `T₀` space in which every point is closed or the generic point of
an irreducible component. Two distinct points have the same image exactly when they lie in the
same connected component of the contracted locus of `f`. -/
theorem apply_eq_apply_iff_of_isClosedMap
    (hdim : ∀ x : X, IsClosed ({x} : Set X) ∨ closure {x} ∈ irreducibleComponents X)
    {f : X → Y} (hf : Continuous f) (hcl : IsClosedMap f)
    (hconn : ∀ y, IsPreconnected (f ⁻¹' {y})) {x x' : X} :
    f x = f x' ↔
      x = x' ∨ (x ∈ contractedLocus f ∧ x' ∈ connectedComponentIn (contractedLocus f) x) := by
  constructor
  · intro hxx'
    refine or_iff_not_imp_left.2 fun hxe ↦ ?_
    have hFconn := hconn (f x)
    have hxF : x ∈ f ⁻¹' {f x} := rfl
    have hFZ := hFconn.subset_contractedLocus hdim
      ((isClosed_singleton_apply_of_apply_eq_apply hdim hcl hFconn hxx' hxe).preimage hf)
      ⟨x, hxF, x', hxx'.symm, hxe⟩ ((subsingleton_singleton (a := f x)).anti
        (image_preimage_subset _ _))
    exact ⟨hFZ hxF, hFconn.subset_connectedComponentIn hxF hFZ hxx'.symm⟩
  · rintro (rfl | ⟨hx, hx'⟩)
    · rfl
    exact subsingleton_image_connectedComponentIn_contractedLocus hf hcl x
      (mem_image_of_mem f (mem_connectedComponentIn hx)) (mem_image_of_mem f hx')

/-- **Two contractions with the same contracted locus have the same fibres.** -/
theorem apply_eq_apply_iff_of_contractedLocus_eq
    (hdim : ∀ x : X, IsClosed ({x} : Set X) ∨ closure {x} ∈ irreducibleComponents X)
    {f : X → Y} {f' : X → Y'} (hf : Continuous f) (hcl : IsClosedMap f)
    (hconn : ∀ y, IsPreconnected (f ⁻¹' {y})) (hf' : Continuous f') (hcl' : IsClosedMap f')
    (hconn' : ∀ y, IsPreconnected (f' ⁻¹' {y})) (h : contractedLocus f = contractedLocus f')
    (x x' : X) : f x = f x' ↔ f' x = f' x' := by
  rw [apply_eq_apply_iff_of_isClosedMap hdim hf hcl hconn,
    apply_eq_apply_iff_of_isClosedMap hdim hf' hcl' hconn', h]

end Fibres

omit [TopologicalSpace Y] in
/-- **A point of a closed piece off the rest is alone in its fibre**: let `X = C ∪ X'` with `C`
and `X'` closed, and `f : X → Y` with preconnected fibres. If `p ∈ C ∖ X'` and the fibre of `f`
through `p` meets `C` in a discrete set, then that fibre is `{p}`: `{p}` is open in the fibre
(isolated in its trace on `C`, and away from `X'`) and closed in it (closed in the discrete trace
on the closed set `C`). -/
theorem preimage_singleton_eq_singleton_of_mem_diff {f : X → Y} {C X' : Set X} (hC : IsClosed C)
    (hX' : IsClosed X') (hcov : C ∪ X' = univ) {p : X} (hpC : p ∈ C) (hpX' : p ∉ X')
    (hconn : IsPreconnected (f ⁻¹' {f p})) (hdisc : IsDiscrete (C ∩ f ⁻¹' {f p})) :
    f ⁻¹' {f p} = {p} := by
  set F := f ⁻¹' {f p}
  have hpF : p ∈ C ∩ F := ⟨hpC, rfl⟩
  obtain ⟨O, hO, hOF⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hdisc p hpF
  obtain ⟨K, hK, hKF⟩ := isDiscrete_iff_forall_mem_exists_isClosed.mp hdisc {p}
    (singleton_subset_iff.mpr hpF)
  have hcompl : X'ᶜ ⊆ C := fun z hz ↦ (hcov ▸ mem_univ z : z ∈ C ∪ X').resolve_right hz
  -- the trace of `O ∩ X'ᶜ` on the fibre is `{p}`, and so is that of `K ∩ C`
  have hU : ∀ U, U ∩ (C ∩ F) = {p} → p ∈ U ∧ ∀ z ∈ F, z ∈ U → z ∈ C → z = p := fun U hU ↦
    ⟨(hU.symm ▸ rfl : p ∈ U ∩ (C ∩ F)).1, fun z hz hzU hzC ↦ by
      have : z ∈ U ∩ (C ∩ F) := ⟨hzU, hzC, hz⟩
      rwa [hU] at this⟩
  obtain ⟨hpO, hO''⟩ := hU O hOF
  obtain ⟨hpK, hK'⟩ := hU K hKF
  have hO' : ∀ z ∈ F, z ∈ O → z ∉ X' → z = p := fun z hz hzO hzX' ↦ hO'' z hz hzO (hcompl hzX')
  rcases isPreconnected_iff_subset_of_disjoint.mp hconn (O ∩ X'ᶜ) (K ∩ C)ᶜ
      (hO.inter hX'.isOpen_compl) (hK.inter hC).isOpen_compl
      (fun z hz ↦ by
        by_cases hzK : z ∈ K ∩ C
        · obtain rfl := hK' z hz hzK.1 hzK.2
          exact Or.inl ⟨hpO, hpX'⟩
        · exact Or.inr hzK)
      (by
        ext z
        simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false]
        rintro ⟨hz, ⟨hzO, hzX'⟩, hzKC⟩
        obtain rfl := hO' z hz hzO hzX'
        exact hzKC ⟨hpK, hpC⟩) with h | h
  · exact Subset.antisymm (fun z hz ↦ hO' z hz (h hz).1 (h hz).2) (singleton_subset_iff.mpr rfl)
  · exact (h (rfl : p ∈ F) ⟨hpK, hpC⟩).elim
