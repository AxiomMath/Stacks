module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecialFibreDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.GenericConstancy
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.GenericFibre
public import StacksFrontier.AlgebraicGeometry.Variety.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Variety.ImageDimension

/-!
# The dimension of a general fibre, without irreducibility of the source

Let `f : X ⟶ S` be a morphism of finite type of schemes locally of finite type over a field,
with `S` irreducible of dimension `n`, and suppose `dim X ≤ D`. Then the fibres of `f` over a
nonempty open subset of `S` all satisfy `dim X_p + n ≤ D`.

## Main results

* `AlgebraicGeometry.exists_isOpen_forall_topologicalKrullDim_fiber_add_le`: the bound above.
* `AlgebraicGeometry.exists_isOpen_forall_topologicalKrullDim_fiber_add_le_of_ne_top`: the same
  bound with `D` an arbitrary element of `WithBot ℕ∞` other than `⊤`, which is the form a
  dimension count reading its bound off other dimensions can use.

## Implementation notes

The source is **not** assumed irreducible, which is what makes the statement usable. Tag 0B2L
part (2b) and Tag 05F7 between them give the bound at once when `X` is irreducible: the former
pins the local fibre dimension at `dim X - dim S` on a dense open subset of `X`, and the latter
transports the resulting generic-fibre dimension to a nonempty open subset of `S`. Of these two,
only part (2b) needs irreducibility of the source, and it is applied here to the irreducible
components of `X` one at a time, each carrying the reduced induced structure
`Stacks.Chow.integralComponentAt` of its generic point. Tag 05F7, whose irreducibility
hypothesis is on the *target*, is then applied once to `f` itself.

The dimension of the generic fibre of `f` is bounded by those of the generic fibres of the
components because the dimension of a space is the supremum of the dimensions of its irreducible
components, `AlgebraicGeometry.topologicalKrullDim_eq_iSup_irreducibleComponents`: a component of
the fibre is irreducible in `X`, hence lies in a component `C` of `X`, hence in the trace of the
fibre on `C`. Components whose image is not dense miss the generic fibre altogether, since the
only closed subset of `S` containing its generic point is `S`.

Dimensions take values in `WithBot ℕ∞`, which has no subtraction, so the conclusion is stated
additively; the natural number `D - n` that appears in the proof is truncated subtraction, which
is harmless because a component with dense image has dimension at least `n`.

## References

* [Stacks Project, Tag 0B2L](https://stacks.math.columbia.edu/tag/0B2L)
* [Stacks Project, Tag 05F7](https://stacks.math.columbia.edu/tag/05F7)
* [Stacks Project, Tag 01RL](https://stacks.math.columbia.edu/tag/01RL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Reading dimensions in `WithBot ℕ∞` as natural numbers -/

/-- A dimension bounded by a natural number has its truncation to `ℕ` bounded by it. -/
private lemma unbotD_toNat_le_of_le {a : WithBot ℕ∞} {D : ℕ} (h : a ≤ (D : WithBot ℕ∞)) :
    (a.unbotD 0).toNat ≤ D := by
  induction a using WithBot.recBotCoe with
  | bot => simp
  | coe b =>
    have hb : b ≤ (D : ℕ∞) := WithBot.coe_le_coe.mp h
    lift b to ℕ using ne_top_of_le_ne_top (ENat.natCast_ne_top D) hb
    simpa using hb

/-- A dimension that is neither `⊥` nor larger than a natural number is a natural number. -/
private lemma exists_nat_eq_of_ne_bot_of_le {a : WithBot ℕ∞} {d : ℕ} (hbot : a ≠ ⊥)
    (h : a ≤ (d : WithBot ℕ∞)) : ∃ m : ℕ, m ≤ d ∧ a = (m : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact absurd rfl hbot
  | coe b =>
    have hb : b ≤ (d : ℕ∞) := WithBot.coe_le_coe.mp h
    lift b to ℕ using ne_top_of_le_ne_top (ENat.natCast_ne_top d) hb
    exact ⟨b, by exact_mod_cast hb, rfl⟩

/-- An empty space has dimension `⊥`, so it stays below any bound after adding anything. -/
private lemma topologicalKrullDim_add_le_of_isEmpty {T : Type*} [TopologicalSpace T] (h : IsEmpty T)
    (a d : WithBot ℕ∞) : topologicalKrullDim T + a ≤ d := by
  rw [(topologicalKrullDim_eq_bot_iff_isEmpty T).mpr h]
  exact bot_le

/-! ### Dimension and irreducible components -/

/-- **A subset is no larger than its traces on the irreducible components.** The dimension of a
subset of a topological space is at most `d` as soon as its intersection with every irreducible
component of the ambient space has dimension at most `d`: an irreducible component of the subset
is irreducible in the ambient space, so it lies in some ambient component. -/
private lemma topologicalKrullDim_le_of_forall_irreducibleComponents_inter
    {X : Type*} [TopologicalSpace X] (F : Set X) {d : WithBot ℕ∞}
    (h : ∀ C ∈ irreducibleComponents X, topologicalKrullDim ((C ∩ F : Set X)) ≤ d) :
    topologicalKrullDim F ≤ d := by
  rw [topologicalKrullDim_eq_iSup_irreducibleComponents ↥F]
  refine iSup_le fun W => iSup_le fun hW => ?_
  have hirr : IsIrreducible ((Subtype.val : ↥F → X) '' W) :=
    hW.1.image _ continuous_subtype_val.continuousOn
  obtain ⟨C, hC, hWC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hirr
  refine le_trans ?_ (h C hC)
  have hm : Topology.IsInducing
      (fun w : ↥W => (⟨((w : ↥F) : X), hWC ⟨(w : ↥F), w.2, rfl⟩, (w : ↥F).2⟩ : ↥(C ∩ F))) := by
    refine Topology.IsInducing.subtypeVal.of_comp_iff.mp ?_
    change Topology.IsInducing ((Subtype.val : ↥F → X) ∘ (Subtype.val : ↥W → ↥F))
    exact Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  exact hm.topologicalKrullDim_le

/-- The preimage of a set along an embedding has the dimension of the part of that set lying in
the range. -/
private lemma topologicalKrullDim_preimage_eq_range_inter {W X : Type*} [TopologicalSpace W]
    [TopologicalSpace X] {g : W → X} (hg : Topology.IsEmbedding g) (A : Set X) :
    topologicalKrullDim (g ⁻¹' A) = topologicalKrullDim (Set.range g ∩ A : Set X) := by
  have hm : Topology.IsEmbedding
      (fun w : ↥(g ⁻¹' A) => (⟨g w, ⟨w, rfl⟩, w.2⟩ : ↥(Set.range g ∩ A))) := by
    refine Topology.IsEmbedding.subtypeVal.of_comp_iff.mp ?_
    change Topology.IsEmbedding (g ∘ (Subtype.val : ↥(g ⁻¹' A) → W))
    exact hg.comp Topology.IsEmbedding.subtypeVal
  have hsurj : Function.Surjective
      (fun w : ↥(g ⁻¹' A) => (⟨g w, ⟨w, rfl⟩, w.2⟩ : ↥(Set.range g ∩ A))) := by
    rintro ⟨x, ⟨w, rfl⟩, hxA⟩
    exact ⟨⟨w, hxA⟩, rfl⟩
  exact (hm.toHomeomorphOfSurjective hsurj).isHomeomorph.topologicalKrullDim_eq

/-- The fibre of a closed subscheme over a point of the base is the trace of the fibre on the
support of that subscheme. -/
private lemma topologicalKrullDim_fiber_subschemeι_comp {X S : Scheme.{u}} (f : X ⟶ S)
    (I : X.IdealSheafData) (p : S) :
    topologicalKrullDim ((I.subschemeι ≫ f).fiber p) =
      topologicalKrullDim (((I.support : Set X) ∩ f.base ⁻¹' {p} : Set X)) := by
  rw [((I.subschemeι ≫ f).fiberHomeo p).isHomeomorph.topologicalKrullDim_eq]
  have hpre : ((I.subschemeι ≫ f).base ⁻¹' {p} : Set I.subscheme) =
      I.subschemeι.base ⁻¹' (f.base ⁻¹' {p}) := rfl
  rw [hpre, topologicalKrullDim_preimage_eq_range_inter I.subschemeι.isClosedEmbedding.isEmbedding,
    I.range_subschemeι]

/-! ### The dimension of the generic fibre of a component -/

/-- **The generic fibre of an irreducible component.** For a morphism of finite type over a field
with irreducible target of dimension `n`, the fibre over the generic point of the target of the
integral closed subscheme attached to a point `x` of the source has dimension at most
`dim closure {x} - n`. If that subscheme does not dominate the target the fibre is empty; if it
does, Tag 0B2L part (2b) applies to it, since it is irreducible. -/
private lemma topologicalKrullDim_fiber_genericPoint_integralComponent_le
    (k : Type u) [Field k] {X S : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pS] [IrreducibleSpace S]
    (f : X ⟶ S) [QuasiCompact f] [LocallyOfFiniteType f] (hf : f ≫ pS = pX)
    {D n : ℕ} (hS : topologicalKrullDim S = (n : WithBot ℕ∞))
    (x : X) (hx : topologicalKrullDim (closure ({x} : Set X)) ≤ (D : WithBot ℕ∞)) :
    topologicalKrullDim
        (((Stacks.Chow.integralComponentAt x).subschemeι ≫ f).fiber (genericPoint S)) ≤
      ((D - n : ℕ) : WithBot ℕ∞) := by
  set I := Stacks.Chow.integralComponentAt x with hI
  have hint : IsIntegral I.subscheme := Stacks.Chow.isIntegral_integralComponentAt x
  have hdimW : topologicalKrullDim I.subscheme ≤ (D : WithBot ℕ∞) := by
    rwa [Stacks.Chow.topologicalKrullDim_subscheme I, hI,
      Stacks.Chow.coe_support_integralComponentAt x]
  have hfW : (I.subschemeι ≫ f) ≫ pS = I.subschemeι ≫ pX := by rw [Category.assoc, hf]
  by_cases hd : closure (Set.range (I.subschemeι ≫ f).base) = Set.univ
  · have : IsDominant (I.subschemeι ≫ f) := ⟨dense_iff_closure_eq.mpr hd⟩
    have himg : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure (Set.range
          (fun z : I.subscheme => (I.subschemeι ≫ f) z)))).subscheme = (n : WithBot ℕ∞) := by
      rw [Stacks.Chow.topologicalKrullDim_subscheme,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      have huniv : (Closeds.closure (Set.range
          (fun z : I.subscheme => (I.subschemeι ≫ f) z)) : Set S) = Set.univ := hd
      rw [huniv, (Homeomorph.Set.univ S).isHomeomorph.topologicalKrullDim_eq]
      exact hS
    obtain ⟨-, hdense⟩ := isOpen_and_dense_setOf_topologicalKrullDimAt_fiber_eq k
      (I.subschemeι ≫ pX) pS (I.subschemeι ≫ f) hfW
      (((topologicalKrullDim I.subscheme).unbotD 0).toNat - n) (by rw [himg]; simp)
    obtain ⟨z, hz⟩ := hdense.nonempty
    exact ((topologicalKrullDim_fiber_genericPoint_le (I.subschemeι ≫ f) z).trans hz.le).trans
      (by exact_mod_cast Nat.sub_le_sub_right (unbotD_toNat_le_of_le hdimW) n)
  · have hempty : IsEmpty ((I.subschemeι ≫ f).fiber (genericPoint S)) := by
      refine ⟨fun z => hd (Set.eq_univ_of_univ_subset ?_)⟩
      calc (Set.univ : Set S) = closure {genericPoint S} := (genericPoint_spec S).symm
        _ ⊆ closure (Set.range (I.subschemeι ≫ f).base) :=
            closure_mono (Set.singleton_subset_iff.mpr ⟨_, Stacks.Chow.base_fiberι _ _ z⟩)
    simpa using topologicalKrullDim_add_le_of_isEmpty hempty 0 _

/-! ### The bound on a general fibre -/

/-- **The dimension of a general fibre, with no irreducibility of the source.** Let
`f : X ⟶ S` be a morphism of finite type of schemes locally of finite type over a field, with
`S` irreducible of dimension `n` and `dim X ≤ D`. Then there is a nonempty open subset of `S`
over which every fibre `X_p` satisfies `dim X_p + n ≤ D`.

The bound is what the dimension count of [Stacks, Tag 0B1R] asks of its incidence variety, whose
irreducibility is not available. -/
public theorem exists_isOpen_forall_topologicalKrullDim_fiber_add_le
    (k : Type u) [Field k] {X S : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pS] [NoetherianSpace X] [IrreducibleSpace S]
    (f : X ⟶ S) [QuasiCompact f] (hf : f ≫ pS = pX)
    {D n : ℕ} (hX : topologicalKrullDim X ≤ (D : WithBot ℕ∞))
    (hS : topologicalKrullDim S = (n : WithBot ℕ∞)) :
    ∃ U : Set S, IsOpen U ∧ U.Nonempty ∧ ∀ p ∈ U,
      topologicalKrullDim (f.fiber p) + (n : WithBot ℕ∞) ≤ (D : WithBot ℕ∞) := by
  let : LocallyOfFiniteType (f ≫ pS) := hf ▸ (inferInstance : LocallyOfFiniteType pX)
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f pS
  by_cases hdom : closure (Set.range f.base) = Set.univ
  · -- `f` is dominant, so it hits the generic point of `S` and the generic fibre is nonempty.
    have : IsDominant f := ⟨dense_iff_closure_eq.mpr hdom⟩
    have hnle : n ≤ D := by
      have h1 : topologicalKrullDim (closure (Set.range f.base) : Set S) ≤ topologicalKrullDim X :=
        topologicalKrullDim_closure_range_le k f pX pS hf
      rw [hdom, (Homeomorph.Set.univ S).isHomeomorph.topologicalKrullDim_eq, hS] at h1
      exact_mod_cast h1.trans hX
    -- The generic fibre is bounded, component by component.
    have hgen : topologicalKrullDim (f.fiber (genericPoint S)) ≤ ((D - n : ℕ) : WithBot ℕ∞) := by
      rw [(f.fiberHomeo (genericPoint S)).isHomeomorph.topologicalKrullDim_eq]
      refine topologicalKrullDim_le_of_forall_irreducibleComponents_inter _ fun C hC => ?_
      obtain ⟨x, hx⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents C hC)
      have hsupp : ((Stacks.Chow.integralComponentAt x).support : Set X) = C := by
        rw [Stacks.Chow.coe_support_integralComponentAt, hx]
      have hdimC : topologicalKrullDim (closure ({x} : Set X)) ≤ (D : WithBot ℕ∞) :=
        (topologicalKrullDim_le_of_subset (Set.subset_univ _)).trans
          (le_of_eq ((Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq) |>.trans hX)
      have hcomp := topologicalKrullDim_fiber_genericPoint_integralComponent_le k pX pS f hf
        (D := D) (n := n) hS x hdimC
      rwa [topologicalKrullDim_fiber_subschemeι_comp f _ (genericPoint S), hsupp] at hcomp
    -- The generic fibre is nonempty, so its dimension is a natural number.
    obtain ⟨x, hx⟩ := (isDominant_iff_genericPoints_subset_range f).mp inferInstance
      (mem_genericPoints_of_isGenericPoint_univ (genericPoint_spec S))
    have hne : Nonempty (f.fiber (genericPoint S)) := ⟨hx ▸ f.asFiber x⟩
    obtain ⟨m, hmd, hm⟩ := exists_nat_eq_of_ne_bot_of_le
      (fun hb => (not_isEmpty_of_nonempty _) ((topologicalKrullDim_eq_bot_iff_isEmpty _).mp hb))
      hgen
    obtain ⟨V, hVne, hV⟩ := exists_nonempty_open_fiberDimension_eq f m (genericPoint S)
      (genericPoint_spec S) hm
    refine ⟨(V : Set S), V.2, hVne, fun p hp => ?_⟩
    rw [show topologicalKrullDim (f.fiber p) = (m : WithBot ℕ∞) from hV p hp]
    exact_mod_cast (by omega : m + n ≤ D)
  · -- `f` is not dominant: the fibres over the complement of the closure of its image are empty.
    refine ⟨(closure (Set.range f.base))ᶜ, isClosed_closure.isOpen_compl,
      Set.nonempty_compl.mpr hdom, fun p hp => ?_⟩
    exact topologicalKrullDim_add_le_of_isEmpty
      ⟨fun z => hp (subset_closure ⟨f.fiberι p z, Stacks.Chow.base_fiberι f p z⟩)⟩ _ _

/-- **The dimension of a general fibre, against a bound taken in `WithBot ℕ∞`.** The form of
`AlgebraicGeometry.exists_isOpen_forall_topologicalKrullDim_fiber_add_le` that a dimension count
can use, the bound on the source being read off from other dimensions rather than named by a
natural number. Only finiteness of the bound is needed: a bound of `⊥` forces the source, and
hence every fibre, to be empty. -/
public theorem exists_isOpen_forall_topologicalKrullDim_fiber_add_le_of_ne_top
    (k : Type u) [Field k] {X S : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pS] [NoetherianSpace X] [IrreducibleSpace S]
    (f : X ⟶ S) [QuasiCompact f] (hf : f ≫ pS = pX)
    {d : WithBot ℕ∞} {n : ℕ} (hd : d ≠ ⊤) (hX : topologicalKrullDim X ≤ d)
    (hS : topologicalKrullDim S = (n : WithBot ℕ∞)) :
    ∃ U : Set S, IsOpen U ∧ U.Nonempty ∧ ∀ p ∈ U,
      topologicalKrullDim (f.fiber p) + (n : WithBot ℕ∞) ≤ d := by
  rcases eq_or_ne d ⊥ with rfl | hbot
  · have hXempty : IsEmpty X :=
      (topologicalKrullDim_eq_bot_iff_isEmpty X).mp (le_bot_iff.mp hX)
    refine ⟨Set.univ, isOpen_univ, Set.univ_nonempty, fun p _ => ?_⟩
    exact topologicalKrullDim_add_le_of_isEmpty ⟨fun z => hXempty.elim (f.fiberι p z)⟩ _ _
  · obtain ⟨D, -, rfl⟩ := exists_nat_eq_of_ne_bot_of_le (d := (d.unbotD 0).toNat) hbot
      (by
        induction d using WithBot.recBotCoe with
        | bot => exact absurd rfl hbot
        | coe b =>
          lift b to ℕ using (by simpa using hd)
          simp)
    exact exists_isOpen_forall_topologicalKrullDim_fiber_add_le k pX pS f hf hX hS

end AlgebraicGeometry

end
