module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecialFibreDimension
public import StacksFrontier.AlgebraicGeometry.IrreducibleComponentSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.GenericConstancy
public import StacksFrontier.AlgebraicGeometry.Variety.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Variety.ImageDimension
public import StacksFrontier.Data.ENat.WithBotNatCast
public import StacksFrontier.Topology.Dimension.ClosedSubsetDimension

/-!
# The generic fibre of a morphism with a reducible source, and the dimension of its image

Tag 05F7 bounds the fibres of a morphism over a nonempty open subset of the target by the
dimension of the generic fibre, and the generic fibre of a morphism from an *irreducible* source
has dimension `dim X - dim Y` (Tag 0B2L). This file removes the irreducibility of the source:
over a nonempty open subset of an irreducible target, every fibre of a morphism from a
quasi-compact source of finite type has dimension at most `dim X - dim Y`, and so does the
closure of the image of that fibre under any second morphism.

The source is decomposed into finitely many irreducible closed pieces and each is treated
separately: a piece dominating the target has generic fibre of dimension `dim C - dim Y` by
Tag 0B2L, so Tag 05F7 applies to it, and a piece that does not dominate has *empty* fibre over
every point outside the closure of its image. The generic point of the target lies in each of
the finitely many nonempty opens so produced, which is what makes their intersection nonempty
without an irreducibility argument about finite intersections.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_subscheme_vanishingIdeal`: the dimension of the reduced
  induced subscheme on a closed subset is the dimension of that subset.
* `AlgebraicGeometry.exists_nonempty_open_topologicalKrullDim_inter_fiber_le`: **the fibre bound
  for one irreducible closed piece of the source.**
* `AlgebraicGeometry.exists_nonempty_open_topologicalKrullDim_fiber_le`: **the fibre bound with
  no irreducibility hypothesis on the source.**
* `AlgebraicGeometry.exists_nonempty_open_topologicalKrullDim_closure_image_fiber_le`: **the
  same for the closure of the image of the fibre** under a second morphism over the base field.

## Implementation notes

The bound is stated additively, `dim + n ≤ m`, and not with the truncated natural subtraction
`m - n`: the truncation loses the case `n > m`, where the conclusion is that the fibre is *empty*
and its dimension is `⊥` rather than `0`. That case is not idle — it is exactly the one where no
irreducible piece of the source dominates the target. Internally the subtracted form is used,
because that is the shape `AlgebraicGeometry.exists_nonempty_open_fiberDimension_le` consumes,
and the passage between the two is guarded by `n ≤ dim C`, which dominance supplies.

The piece `C` is given its reduced induced scheme structure, the subscheme of
`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal`, so that Tag 0B2L applies to it; its
dimension is the dimension of `C` because the inclusion is a closed immersion onto `C`.
The passage between the scheme-theoretic fibre and the set-theoretic one is
`AlgebraicGeometry.Scheme.Hom.fiberHomeo`, and between the fibre of the piece and the
intersection of the piece with the fibre of the whole is the closed embedding of the piece.

The fibre over a point is only used where that point is closed, because the image-dimension
bound `AlgebraicGeometry.topologicalKrullDim_closure_image_le` needs the subset of the source to
be closed, and the set-theoretic fibre over a point is closed exactly when the point is.

## References

* [Stacks Project, Tag 05F7](https://stacks.math.columbia.edu/tag/05F7)
* [Stacks Project, Tag 0B2L](https://stacks.math.columbia.edu/tag/0B2L)
-/

@[expose] public section

open CategoryTheory Set TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The dimension of a reduced induced subscheme -/

/-- The dimension of the reduced induced subscheme on a closed subset is the dimension of that
subset. -/
public theorem topologicalKrullDim_subscheme_vanishingIdeal {X : Scheme.{u}}
    (Z : Closeds X) :
    topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme =
      topologicalKrullDim (Z : Set X) := by
  rw [Stacks.Chow.topologicalKrullDim_subscheme]
  exact congrArg (fun s : Set X => topologicalKrullDim (↥s))
    (Scheme.IdealSheafData.coe_support_vanishingIdeal Z)

/-! ### Bookkeeping between `WithBot ℕ∞` and `ℕ` -/

/-- A dimension bounded by a natural number has that bound after truncation to `ℕ`. -/
private theorem toNat_unbotD_le {x : WithBot ℕ∞} {m : ℕ} (hx : x ≤ (m : WithBot ℕ∞)) :
    (x.unbotD 0).toNat ≤ m := by
  cases x with
  | bot => simp
  | coe a =>
    have ha : a ≤ (m : ℕ∞) := by exact_mod_cast hx
    rw [WithBot.unbotD_coe]
    exact ENat.toNat_le_toNat ha (by simp)

/-- A finite dimension bounded below by a natural number keeps that bound after truncation. -/
private theorem le_toNat_unbotD {x : WithBot ℕ∞} {n m : ℕ} (hn : (n : WithBot ℕ∞) ≤ x)
    (hm : x ≤ (m : WithBot ℕ∞)) : n ≤ (x.unbotD 0).toNat := by
  cases x with
  | bot => exact absurd hn (by simp)
  | coe a =>
    have ha : (n : ℕ∞) ≤ a := by exact_mod_cast hn
    have ham : a ≤ (m : ℕ∞) := by exact_mod_cast hm
    rw [WithBot.unbotD_coe]
    exact ENat.toNat_le_toNat ha (fun h => by simp [h] at ham)

/-- A bound by a truncated difference becomes an additive bound. -/
private theorem add_le_of_le_sub {x : WithBot ℕ∞} {d n m : ℕ}
    (hx : x ≤ ((d - n : ℕ) : WithBot ℕ∞)) (hnd : n ≤ d) (hdm : d ≤ m) :
    x + (n : WithBot ℕ∞) ≤ (m : WithBot ℕ∞) := by
  refine le_trans (add_le_add hx (le_refl ((n : ℕ) : WithBot ℕ∞))) ?_
  have hcast : ((d - n : ℕ) : WithBot ℕ∞) + ((n : ℕ) : WithBot ℕ∞) = ((d : ℕ) : WithBot ℕ∞) := by
    refine Eq.trans (WithBot.coe_add _ _).symm ?_
    refine congrArg (fun z : ℕ∞ => (z : WithBot ℕ∞)) ?_
    rw [← Nat.cast_add, Nat.sub_add_cancel hnd]
  rw [hcast]
  exact_mod_cast hdm

/-- An additive bound becomes a bound by a truncated difference. -/
private theorem le_sub_of_add_le {x : WithBot ℕ∞} {n m : ℕ}
    (h : x + (n : WithBot ℕ∞) ≤ (m : WithBot ℕ∞)) : x ≤ ((m - n : ℕ) : WithBot ℕ∞) := by
  cases x with
  | bot => exact bot_le
  | coe a =>
    cases a with
    | top =>
      exfalso
      rw [show ((⊤ : ℕ∞) : WithBot ℕ∞) + ((n : ℕ) : WithBot ℕ∞) = (⊤ : WithBot ℕ∞) from rfl] at h
      exact natCast_ne_top_withBot m (top_le_iff.mp h)
    | coe b =>
      have hb : b + n ≤ m := by exact_mod_cast h
      have hcast : ((b : ℕ) : WithBot ℕ∞) ≤ ((m - n : ℕ) : WithBot ℕ∞) := by
        exact_mod_cast Nat.le_sub_of_add_le hb
      exact hcast

/-- The empty subset satisfies every additive dimension bound. -/
private theorem empty_add_le {X : Type*} [TopologicalSpace X] (n m : ℕ) :
    topologicalKrullDim (∅ : Set X) + (n : WithBot ℕ∞) ≤ (m : WithBot ℕ∞) := by
  rw [(topologicalKrullDim_eq_bot_iff_isEmpty (↥(∅ : Set X))).mpr inferInstance]
  simp

/-- **The dimension of a closed subset in additive form, from the closures of its points.** -/
private theorem add_le_of_forall_closure {X : Type*} [TopologicalSpace X] [QuasiSober X]
    {S : Set X} (hS : IsClosed S) {n m : ℕ}
    (h : ∀ x ∈ S, topologicalKrullDim (closure ({x} : Set X)) + (n : WithBot ℕ∞) ≤
      (m : WithBot ℕ∞)) :
    topologicalKrullDim S + (n : WithBot ℕ∞) ≤ (m : WithBot ℕ∞) := by
  rcases Set.eq_empty_or_nonempty S with rfl | ⟨x₀, hx₀⟩
  · exact empty_add_le n m
  · have hne : topologicalKrullDim (closure ({x₀} : Set X)) ≠ ⊥ := by
      rw [Ne, topologicalKrullDim_eq_bot_iff_isEmpty]
      exact fun hemp => hemp.false ⟨x₀, subset_closure rfl⟩
    have h0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDim (closure ({x₀} : Set X)) := by
      cases hc : topologicalKrullDim (closure ({x₀} : Set X)) with
      | bot => exact absurd hc hne
      | coe a => exact WithBot.coe_le_coe.mpr (by simp)
    have hnm : n ≤ m := by
      have hle := le_trans (add_le_add h0 (le_refl ((n : ℕ) : WithBot ℕ∞))) (h x₀ hx₀)
      rw [zero_add] at hle
      exact_mod_cast hle
    have hbound : topologicalKrullDim S ≤ ((m - n : ℕ) : WithBot ℕ∞) :=
      topologicalKrullDim_le_of_forall_closure hS fun x hx => le_sub_of_add_le (h x hx)
    exact add_le_of_le_sub hbound hnm le_rfl

/-! ### The fibre bound over one irreducible closed piece -/

/-- **The fibre bound for one irreducible closed piece of the source.** Let `g : X ⟶ Y` be a
morphism of schemes of finite type over a field with `Y` irreducible of dimension `n`, and let
`C ⊆ X` be irreducible closed of dimension at most `m`. Then over a nonempty open subset of `Y`
the piece `C` meets every fibre in dimension at most `m - n`, stated additively. -/
public theorem exists_nonempty_open_topologicalKrullDim_inter_fiber_le
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY] [CompactSpace X] [IrreducibleSpace Y]
    (g : X ⟶ Y) (hg : g ≫ pY = pX) {C : Set X} (hCcl : IsClosed C) (hCirr : IsIrreducible C)
    {m n : ℕ} (hC : topologicalKrullDim C ≤ (m : WithBot ℕ∞))
    (hY : topologicalKrullDim Y = (n : WithBot ℕ∞)) :
    ∃ U : Set Y, IsOpen U ∧ U.Nonempty ∧ ∀ p ∈ U,
      topologicalKrullDim (C ∩ g.base ⁻¹' {p} : Set X) + (n : WithBot ℕ∞) ≤
        (m : WithBot ℕ∞) := by
  have : LocallyOfFiniteType (g ≫ pY) := hg ▸ inferInstance
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g pY
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pX
  have : IsNoetherian X := ⟨⟩
  -- the reduced induced structure on the piece
  set I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨C, hCcl⟩ with hI
  set D : Scheme.{u} := I.subscheme with hD
  set ι : D ⟶ X := I.subschemeι with hιdef
  have hrange : Set.range ι.base = C :=
    Scheme.IdealSheafData.range_subschemeι_vanishingIdeal ⟨C, hCcl⟩
  have : IsClosedImmersion ι := inferInstanceAs (IsClosedImmersion I.subschemeι)
  have : IrreducibleSpace D :=
    Scheme.IdealSheafData.irreducibleSpace_subscheme X I (hrange ▸ hCirr)
  have : CompactSpace D := StacksTag09NX.compactSpace_of_isClosedImmersion ι
  have : IsNoetherian D := StacksTag09NX.isNoetherian_subscheme I
  set pD : D ⟶ Spec (.of k) := ι ≫ pX with hpD
  have : LocallyOfFiniteType pD := by rw [hpD]; infer_instance
  set gD : D ⟶ Y := ι ≫ g with hgD
  have hgDbase : gD ≫ pY = pD := by rw [hgD, hpD, Category.assoc, hg]
  have : LocallyOfFiniteType gD := by rw [hgD]; infer_instance
  have hdimD : topologicalKrullDim D ≤ (m : WithBot ℕ∞) := by
    rw [hD, hI, topologicalKrullDim_subscheme_vanishingIdeal]
    exact hC
  -- the set-theoretic fibre of `gD` is the intersection of the piece with the fibre of `g`
  have hfib : ∀ p : Y, topologicalKrullDim (gD.base ⁻¹' {p}) =
      topologicalKrullDim (C ∩ g.base ⁻¹' {p} : Set X) := by
    intro p
    refine IsHomeomorph.topologicalKrullDim_eq _
      (((ι.isEmbedding.homeomorphImage (gD.base ⁻¹' {p})).trans
        (Homeomorph.setCongr ?_)).isHomeomorph)
    have hpre : gD.base ⁻¹' {p} = ι.base ⁻¹' (g.base ⁻¹' {p}) := rfl
    rw [hpre, Set.image_preimage_eq_inter_range, hrange, Set.inter_comm]
  by_cases hdom : closure (Set.range gD.base) = Set.univ
  · -- the piece dominates the target: Tag 0B2L gives the generic fibre, Tag 05F7 the open
    have : QuasiCompact gD := inferInstance
    set η : D := genericPoint D with hη
    have hηspec : IsGenericPoint η Set.univ := genericPoint_spec D
    have himg : IsGenericPoint (gD.base η) Set.univ := by
      refine isGenericPoint_def.mpr (Set.Subset.antisymm (Set.subset_univ _) ?_)
      rw [← hdom]
      refine closure_minimal ?_ isClosed_closure
      rintro _ ⟨d, rfl⟩
      refine specializes_iff_mem_closure.mp ?_
      exact (hηspec.specializes (Set.mem_univ d)).map gD.base.hom.continuous
    -- the closure of the image is the whole target
    have hclosedsEq : Closeds.closure (Set.range gD.base) = (⊤ : Closeds Y) := by
      ext y
      simp only [Closeds.coe_closure, Closeds.coe_top, Set.mem_univ, iff_true]
      rw [hdom]; trivial
    have hdimimg : topologicalKrullDim
        (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure (Set.range gD.base))).subscheme = (n : WithBot ℕ∞) := by
      rw [hclosedsEq, topologicalKrullDim_subscheme_vanishingIdeal]
      refine Eq.trans ?_ hY
      refine Eq.trans (congrArg (fun s : Set Y => topologicalKrullDim (↥s)) ?_)
        topologicalKrullDim_univ
      exact Closeds.coe_top
    have hgen := topologicalKrullDim_fiber_genericPoint_eq_imageClosure_sub k pD pY gD hgDbase
      η hηspec
    rw [hdimimg] at hgen
    -- the two natural numbers
    set d : ℕ := ((topologicalKrullDim D).unbotD 0).toNat with hd
    have hdm : d ≤ m := toNat_unbotD_le hdimD
    have hnd : n ≤ d := by
      have hle := topologicalKrullDim_closure_range_le k gD pD pY hgDbase
      rw [hdom, topologicalKrullDim_univ, hY] at hle
      exact le_toNat_unbotD hle hdimD
    have hnn : (WithBot.unbotD 0 ((n : ℕ) : WithBot ℕ∞)).toNat = n := by simp
    have hgen' : gD.fiberDimension (gD.base η) ≤ ((d - n : ℕ) : WithBot ℕ∞) := by
      refine le_of_eq ?_
      rw [show gD.fiberDimension (gD.base η) =
        topologicalKrullDim (gD.fiber (gD.base η)) from rfl, hgen, hnn]
    obtain ⟨W, hWne, hWdim⟩ :=
      exists_nonempty_open_fiberDimension_le gD (d - n) (gD.base η) himg hgen'
    refine ⟨(W : Set Y), W.is_open', hWne, fun p hp => ?_⟩
    refine add_le_of_le_sub (d := d) ?_ hnd hdm
    rw [← hfib p]
    refine le_trans (le_of_eq ?_) (hWdim p hp)
    exact (IsHomeomorph.topologicalKrullDim_eq _ (gD.fiberHomeo p).isHomeomorph).symm
  · -- the piece does not dominate: the fibre is empty off the closure of its image
    refine ⟨(closure (Set.range gD.base))ᶜ, isClosed_closure.isOpen_compl,
      Set.nonempty_compl.mpr hdom, fun p hp => ?_⟩
    have hempty : (C ∩ g.base ⁻¹' {p} : Set X) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => hp ?_
      obtain ⟨d, hd⟩ : x ∈ Set.range ι.base := hrange ▸ hx.1
      refine subset_closure ⟨d, ?_⟩
      have : g.base (ι.base d) = p := by rw [hd]; exact hx.2
      exact this
    rw [hempty]
    exact empty_add_le n m

/-! ### The fibre bound with a reducible source -/

/-- **The fibre bound with no irreducibility hypothesis on the source.** Over a nonempty open
subset of an irreducible target of dimension `n`, every fibre of a morphism from a quasi-compact
source of finite type and dimension at most `m` has dimension at most `m - n`. -/
public theorem exists_nonempty_open_topologicalKrullDim_fiber_le
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY] [CompactSpace X] [IrreducibleSpace Y]
    (g : X ⟶ Y) (hg : g ≫ pY = pX)
    {m n : ℕ} (hX : topologicalKrullDim X ≤ (m : WithBot ℕ∞))
    (hY : topologicalKrullDim Y = (n : WithBot ℕ∞)) :
    ∃ U : Set Y, IsOpen U ∧ U.Nonempty ∧ ∃ S : Set (Set X), S.Finite ∧
      (∀ C ∈ S, IsClosed C) ∧ (Set.univ : Set X) = ⋃₀ S ∧
      ∀ p ∈ U, ∀ C ∈ S,
        topologicalKrullDim (C ∩ g.base ⁻¹' {p} : Set X) + (n : WithBot ℕ∞) ≤
          (m : WithBot ℕ∞) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pX
  have : IsNoetherian X := ⟨⟩
  obtain ⟨S, hSfin, hScl, hSirr, hSuniv⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible (isClosed_univ (X := X))
  -- one nonempty open for each piece
  have hpiece : ∀ C ∈ S, ∃ U : Set Y, IsOpen U ∧ U.Nonempty ∧ ∀ p ∈ U,
      topologicalKrullDim (C ∩ g.base ⁻¹' {p} : Set X) + (n : WithBot ℕ∞) ≤
        (m : WithBot ℕ∞) := by
    intro C hC
    exact exists_nonempty_open_topologicalKrullDim_inter_fiber_le k pX pY g hg (hScl C hC)
      (hSirr C hC) (le_trans (topologicalKrullDim_subspace_le X C) hX) hY
  choose! U hUopen hUne hUdim using hpiece
  refine ⟨⋂ C ∈ S, U C, hSfin.isOpen_biInter fun C hC => hUopen C hC, ?_, S, hSfin, hScl,
    hSuniv, fun p hp C hC => hUdim C hC p (Set.mem_iInter₂.mp hp C hC)⟩
  -- the generic point of the target lies in every nonempty open
  refine ⟨genericPoint Y, Set.mem_iInter₂.mpr fun C hC => ?_⟩
  refine ((genericPoint_spec Y).mem_open_set_iff (hUopen C hC)).mpr ?_
  obtain ⟨y, hy⟩ := hUne C hC
  exact ⟨y, Set.mem_univ y, hy⟩

/-- **The dimension of the closure of the image of a general fibre.** Let `g : X ⟶ Y` and
`h : X ⟶ W` be morphisms of schemes of finite type over a field, with `X` quasi-compact of
dimension at most `m` and `Y` irreducible of dimension `n`. Then over a nonempty open subset of
`Y` the closure of the image under `h` of the fibre of `g` over a closed point has dimension at
most `m - n`. -/
public theorem exists_nonempty_open_topologicalKrullDim_closure_image_fiber_le
    (k : Type u) [Field k] {X Y W : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) (pW : W ⟶ Spec (.of k))
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY] [LocallyOfFiniteType pW]
    [CompactSpace X] [IrreducibleSpace Y]
    (g : X ⟶ Y) (hg : g ≫ pY = pX) (h : X ⟶ W) (hh : h ≫ pW = pX)
    {m n : ℕ} (hX : topologicalKrullDim X ≤ (m : WithBot ℕ∞))
    (hY : topologicalKrullDim Y = (n : WithBot ℕ∞)) :
    ∃ U : Set Y, IsOpen U ∧ U.Nonempty ∧ ∀ p ∈ U, IsClosed ({p} : Set Y) →
      topologicalKrullDim (closure (h.base '' (g.base ⁻¹' {p})) : Set W) +
        (n : WithBot ℕ∞) ≤ (m : WithBot ℕ∞) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pX
  have : IsNoetherian X := ⟨⟩
  obtain ⟨U, hUopen, hUne, S, hSfin, hScl, hSuniv, hdim⟩ :=
    exists_nonempty_open_topologicalKrullDim_fiber_le k pX pY g hg hX hY
  refine ⟨U, hUopen, hUne, fun p hp hpcl => ?_⟩
  -- the image of the fibre lies in the finite union of the images of its pieces
  have hcover : h.base '' (g.base ⁻¹' {p}) ⊆
      ⋃ C ∈ S, closure (h.base '' (C ∩ g.base ⁻¹' {p})) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨C, hCS, hxC⟩ : ∃ C ∈ S, x ∈ C := by
      have : x ∈ ⋃₀ S := hSuniv ▸ Set.mem_univ x
      exact this
    exact Set.mem_biUnion hCS (subset_closure ⟨x, ⟨hxC, hx⟩, rfl⟩)
  have hUcl : IsClosed (⋃ C ∈ S, closure (h.base '' (C ∩ g.base ⁻¹' {p})) : Set W) :=
    hSfin.isClosed_biUnion fun _ _ => isClosed_closure
  refine add_le_of_forall_closure isClosed_closure fun y hy => ?_
  obtain ⟨C, hCS, hyC⟩ := Set.mem_iUnion₂.mp (closure_minimal hcover hUcl hy)
  refine le_trans (add_le_add (topologicalKrullDim_le_of_subset
    (closure_minimal (Set.singleton_subset_iff.mpr hyC) isClosed_closure))
    (le_refl ((n : ℕ) : WithBot ℕ∞))) ?_
  exact le_trans (add_le_add (topologicalKrullDim_closure_image_le k h pX pW hh
    ((hScl C hCS).inter (hpcl.preimage (Scheme.Hom.continuous g))))
    (le_refl ((n : ℕ) : WithBot ℕ∞))) (hdim p hp C hCS)

end AlgebraicGeometry

end
