module

public import Mathlib.Topology.LocallyConstant.Algebra
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingCochainGroups
public import StacksFrontier.Topology.Dimension.DimensionFunctionDifference

/-!
# The obstruction to a global dimension function is a Čech class (Stacks 02ID)

Let `X` be a locally Noetherian sober topological space. Tag 02IC produces, around every point, an
open neighbourhood carrying a dimension function; tag 02IB says two dimension functions on such a
space differ by a locally constant function. So for a cover `U : I → Opens X` together with
dimension functions `δ i` on the members, the differences `δ i - δ j` are locally constant on
`U i ∩ U j`, i.e. they form a Čech `1`-cocycle valued in the constant sheaf `ℤ`. This file proves
that a *global* dimension function on `X` exists precisely when the class of that cocycle vanishes
in `Ȟ¹`, and that on a catenary space such a cover always exists — which is the content of the
remark 02ID.

The Čech complex is the one of tag 01FJ (`CechCochains.Cochain`, `CechCochains.cechD`), which is
defined for an arbitrary abelian presheaf on a space. Its first cohomology group
`CechCochains.CechH1` is defined here as `ker d¹ / im d⁰`, using 01FJ's `cechD_cechD`; tag 01EU
only provides the proposition `CechH1IsZero` asserting `ker d¹ ⊆ im d⁰`.

## Main results

* `CechCochains.CechH1`: first Čech cohomology of an abelian presheaf with respect to a family of
  opens, as an honest abelian group, with `CechCochains.cls_eq_zero_iff` characterising the
  vanishing of a class.
* `TopologicalSpace.DimensionFunction.discrepancy`: the Čech `1`-cocycle `δ i - δ j`, its local
  constancy being exactly tag 02IB.
* `TopologicalSpace.DimensionFunction.obstruction`: its class in `Ȟ¹(𝒰, ℤ)`.
* `TopologicalSpace.DimensionFunction.exists_dimensionFunction_iff_obstruction_eq_zero`
  (**02ID**): a global dimension function exists if and only if the obstruction class vanishes.
* `TopologicalSpace.DimensionFunction.exists_cover_dimensionFunction_iff_obstruction_eq_zero`
  (**02ID**): the same statement on a catenary space, where tag 02IC supplies the cover.
* `TopologicalSpace.DimensionFunction.obstruction_eq_zero_congr`: vanishing does not depend on the
  chosen cover, so the obstruction is intrinsic to `X`.

## Implementation notes

Two points where this is weaker than the literal phrase "an element of `H¹(X, ℤ)`".

1. The group is *Čech* cohomology of a chosen cover, not the derived-functor `H¹(X, ℤ)`
   (`CategoryTheory.Sheaf.H`), since the comparison `Ȟ¹(𝒰, ℱ) → H¹(X, ℱ)` is not in Mathlib.
   `obstruction_eq_zero_congr` recovers the part of the intended meaning that matters — the
   obstruction does not depend on the cover.
2. The coefficients are `locallyConstantIntPresheaf`, the presheaf of locally constant `ℤ`-valued
   functions, which is the constant sheaf `ℤ` presented so that its sections are computable. It is
   *not* identified with `constantSheafOnSpace`; that identification is a stalkwise comparison.
-/

@[expose] public section

/-- A locally constant function is constant along specializations: `x ⤳ y` puts `x` and `y` in the
irreducible — hence connected — set `closure {x}`. -/
theorem IsLocallyConstant.eq_of_specializes {X Y : Type*} [TopologicalSpace X] {f : X → Y}
    (hf : IsLocallyConstant f) {x y : X} (h : x ⤳ y) : f x = f y :=
  hf.apply_eq_of_isPreconnected isPreconnected_singleton.closure
    (subset_closure rfl) h.mem_closure

/-- A locally constant function is constant along specializations. -/
theorem LocallyConstant.eq_of_specializes {X Y : Type*} [TopologicalSpace X]
    (f : LocallyConstant X Y) {x y : X} (h : x ⤳ y) : f x = f y :=
  f.isLocallyConstant.eq_of_specializes h

namespace TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-! ## Immediate specializations and dimension functions on open subspaces -/

/-- An immediate specialization is carried to an immediate specialization by an open embedding: an
intermediate point of the images lies in the (open) range, hence is the image of an intermediate
point. -/
theorem IsImmediateSpecialization.map_of_isOpenEmbedding {Y : Type*} [TopologicalSpace Y]
    {f : Y → X} (hf : Topology.IsOpenEmbedding f) {y₁ y₂ : Y}
    (h : IsImmediateSpecialization y₁ y₂) : IsImmediateSpecialization (f y₁) (f y₂) := by
  obtain ⟨hspec, hne, hmid⟩ := h
  refine ⟨hf.isInducing.specializes_iff.mpr hspec, fun he => hne (hf.injective he), ?_⟩
  intro z hz₁ hz₂
  obtain ⟨y₃, rfl⟩ : z ∈ Set.range f :=
    hz₂.mem_open hf.isOpen_range (Set.mem_range_self _)
  rcases hmid y₃ (hf.isInducing.specializes_iff.mp hz₁)
    (hf.isInducing.specializes_iff.mp hz₂) with h | h
  · exact Or.inl (congrArg f h)
  · exact Or.inr (congrArg f h)

/-- An immediate specialization of `X` whose closed point lies in an open `V` is an immediate
specialization of the subspace `V`. Its generic point lies in `V` automatically, an open set being
stable under generization. -/
theorem IsImmediateSpecialization.subtype_of_isOpen {V : Set X} (hV : IsOpen V) {x y : X}
    (h : IsImmediateSpecialization x y) (hy : y ∈ V) :
    IsImmediateSpecialization (⟨x, h.1.mem_open hV hy⟩ : V) ⟨y, hy⟩ := by
  obtain ⟨hspec, hne, hmid⟩ := h
  refine ⟨Topology.IsInducing.subtypeVal.specializes_iff.mp hspec,
    fun he => hne (congrArg Subtype.val he), ?_⟩
  intro z hz₁ hz₂
  rcases hmid z.1 (Topology.IsInducing.subtypeVal.specializes_iff.mpr hz₁)
    (Topology.IsInducing.subtypeVal.specializes_iff.mpr hz₂) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

/-- A dimension function pulls back along an open embedding. Both defining properties transfer
because an open embedding reflects specializations and preserves immediateness. -/
def DimensionFunction.comp {Y : Type*} [TopologicalSpace Y] {f : Y → X}
    (hf : Topology.IsOpenEmbedding f) (d : DimensionFunction X) : DimensionFunction Y where
  toFun := d ∘ f
  strictAnti_specializes := by
    intro _ _ h hne
    exact d.strictAnti_specializes (hf.isInducing.specializes_iff.mpr h) fun he =>
      hne (hf.injective he)
  step_immediate := by
    intro _ _ h
    exact d.step_immediate (h.map_of_isOpenEmbedding hf)

/-- The pulled-back dimension function `d.comp hf` is `d ∘ f`. -/
@[simp]
theorem DimensionFunction.comp_apply {Y : Type*} [TopologicalSpace Y] {f : Y → X}
    (hf : Topology.IsOpenEmbedding f) (d : DimensionFunction X) (y : Y) :
    d.comp hf y = d (f y) := rfl

/-- The inclusion of one open subset of `X` into a larger one is an open embedding. -/
theorem isOpenEmbedding_inclusion {S T : Set X} (hS : IsOpen S) (hT : IsOpen T) (h : T ⊆ S) :
    Topology.IsOpenEmbedding (fun t : T => (⟨t.1, h t.2⟩ : S)) :=
  (Topology.IsOpenEmbedding.of_comp_iff _ hS.isOpenEmbedding_subtypeVal).mp
    hT.isOpenEmbedding_subtypeVal

/-- Every subspace of a locally Noetherian space is locally Noetherian: intersecting a Noetherian
open neighbourhood with the subspace gives a subspace of a Noetherian space. -/
theorem IsLocallyNoetherianSpace.subtype (hX : IsLocallyNoetherianSpace X) (S : Set X) :
    IsLocallyNoetherianSpace S := by
  intro x
  obtain ⟨U, hUopen, hxU, hUnoeth⟩ := hX x.1
  refine ⟨Subtype.val ⁻¹' U, hUopen.preimage continuous_subtype_val, hxU, ?_⟩
  have hi : Topology.IsInducing
      (fun p : (Subtype.val ⁻¹' U : Set S) => (⟨p.1.1, p.2⟩ : U)) := by
    refine Topology.IsInducing.of_comp (by fun_prop) continuous_subtype_val ?_
    have h : Topology.IsInducing ((Subtype.val : S → X) ∘
        (Subtype.val : (Subtype.val ⁻¹' U : Set S) → S)) :=
      Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
    exact h
  exact hi.noetherianSpace

/-- Restriction of a locally constant `ℤ`-valued function along an inclusion of subsets. -/
def locallyConstantRes {S T : Set X} (h : T ⊆ S) :
    LocallyConstant S ℤ →+ LocallyConstant T ℤ where
  toFun a := LocallyConstant.comap ⟨fun t => ⟨t.1, h t.2⟩, by fun_prop⟩ a
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Restriction along `T ⊆ S` evaluates the function at the same point, viewed in `S`. -/
@[simp]
theorem locallyConstantRes_apply {S T : Set X} (h : T ⊆ S) (a : LocallyConstant S ℤ) (t : T) :
    locallyConstantRes h a t = a ⟨t.1, h t.2⟩ := rfl

end TopologicalSpace

open CategoryTheory TopologicalSpace Opposite

/-! ## The constant sheaf `ℤ`, presented with computable sections -/

/-- The presheaf of locally constant `ℤ`-valued functions on `X`, i.e. the constant sheaf `ℤ`
presented so that its sections over an open `V` are literally `LocallyConstant V ℤ`. -/
abbrev locallyConstantIntPresheaf (X : TopCat) : TopCat.Presheaf Ab X where
  obj V := AddCommGrpCat.of (LocallyConstant (V.unop : Set X) ℤ)
  map {_ W} h := AddCommGrpCat.ofHom
    (locallyConstantRes (T := (W.unop : Set X)) fun _ hx => (leOfHom h.unop) hx)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The restriction maps of `locallyConstantIntPresheaf` are restriction of functions. -/
@[simp]
theorem locallyConstantIntPresheaf_restr {X : TopCat} {V W : Opens X} (h : W ≤ V)
    (a : LocallyConstant (V : Set X) ℤ) (x : (W : Set X)) :
    CechCochains.restr (locallyConstantIntPresheaf X) h a x = a ⟨x.1, h x.2⟩ := rfl

/-! ## First Čech cohomology of an abelian presheaf -/

namespace CechCochains

variable {X : TopCat} {I : Type*} (U : I → Opens X) (ℱ : TopCat.Presheaf Ab X)

/-- Each member of the cover contains the intersection over any tuple through it. -/
theorem inter_le {p : ℕ} (i : Fin p → I) (k : Fin p) : inter U i ≤ U (i k) :=
  iInf_le _ k

/-- The intersection over a constant `1`-tuple is the member itself. -/
theorem le_inter_const (k : I) : U k ≤ inter U (fun _ : Fin 1 => k) :=
  le_iInf fun _ => le_rfl

/-- A point lying in every member of a tuple lies in their intersection. -/
theorem mem_inter {p : ℕ} {i : Fin p → I} {y : X} (h : ∀ k, y ∈ U (i k)) : y ∈ inter U i := by
  rw [inter, ← SetLike.mem_coe, Opens.coe_iInf]
  exact Set.mem_iInter.mpr h

/-- The value of a cochain at a point depends only on the index tuple, not on the proof that the
point lies in the corresponding intersection. -/
theorem cochain_congr_apply {p : ℕ} (s : Cochain U (locallyConstantIntPresheaf X) p)
    {i i' : Fin (p + 1) → I} (h : i = i') {y : X}
    (hy : y ∈ inter U i) (hy' : y ∈ inter U i') :
    s i ⟨y, hy⟩ = s i' ⟨y, hy'⟩ := by
  subst h; rfl

/-- The Čech `1`-cocycles: the kernel of `d¹`. -/
def cocycles1 : AddSubgroup (Cochain U ℱ 1) := (cechD U ℱ 1).ker

/-- A `1`-cochain is a cocycle exactly when its Čech differential vanishes. -/
theorem mem_cocycles1_iff (c : Cochain U ℱ 1) :
    c ∈ cocycles1 U ℱ ↔ cechD U ℱ 1 c = 0 := Iff.rfl

/-- Coboundaries are cocycles, because the Čech differential squares to zero. -/
theorem cechD_zero_mem_cocycles1 (t : Cochain U ℱ 0) : cechD U ℱ 0 t ∈ cocycles1 U ℱ :=
  cechD_cechD U ℱ 0 t

/-- The Čech `1`-coboundaries, as a subgroup of the cocycles. -/
def coboundaries1 : AddSubgroup (cocycles1 U ℱ) :=
  (cechD U ℱ 0).range.comap (cocycles1 U ℱ).subtype

/-- First Čech cohomology `Ȟ¹(𝒰, ℱ) = ker d¹ / im d⁰`. -/
abbrev CechH1 : Type _ := cocycles1 U ℱ ⧸ coboundaries1 U ℱ

/-- The class in `Ȟ¹(𝒰, ℱ)` of a Čech `1`-cocycle. -/
def cls (c : cocycles1 U ℱ) : CechH1 U ℱ := QuotientAddGroup.mk c

/-- A cocycle has vanishing Čech class exactly when it is a coboundary. -/
theorem cls_eq_zero_iff (c : cocycles1 U ℱ) :
    cls U ℱ c = 0 ↔ ∃ t : Cochain U ℱ 0, cechD U ℱ 0 t = (c : Cochain U ℱ 1) := by
  rw [cls, QuotientAddGroup.eq_zero_iff, coboundaries1, AddSubgroup.mem_comap]
  exact AddMonoidHom.mem_range

/-- Evaluation of a locally-constant-`ℤ` Čech cochain at a point of the relevant intersection.
Bundling this makes every statement below speak of the same syntactic form. -/
def evalAt {p : ℕ} (s : Cochain U (locallyConstantIntPresheaf X) p) (i : Fin (p + 1) → I)
    {y : X} (hy : y ∈ inter U i) : ℤ := s i ⟨y, hy⟩

/-- `evalAt` at the point underlying an element of the intersection is evaluation there. -/
theorem evalAt_val {p : ℕ} (s : Cochain U (locallyConstantIntPresheaf X) p) (i : Fin (p + 1) → I)
    (x : (inter U i : Set X)) : evalAt U s i x.2 = s i x :=
  rfl

/-- The value of a cochain depends only on the index tuple, not on the containment proof. -/
theorem evalAt_congr {p : ℕ} (s : Cochain U (locallyConstantIntPresheaf X) p)
    {i i' : Fin (p + 1) → I} (h : i = i') {y : X}
    (hy : y ∈ inter U i) (hy' : y ∈ inter U i') : evalAt U s i hy = evalAt U s i' hy' := by
  subst h; rfl

/-- The Čech differential of a cochain, as the alternating sum of the restricted faces. -/
theorem cechD_apply {ℱ : TopCat.Presheaf Ab X} {p : ℕ} (s : Cochain U ℱ p)
    (i : Fin (p + 1 + 1) → I) :
    cechD U ℱ p s i =
      ∑ j : Fin (p + 2),
        ((-1 : ℤ) ^ (j : ℕ)) • restr ℱ (inter_le_omit U i j) (s (i ∘ j.succAbove)) :=
  rfl

/-- The Čech differential, evaluated at a point: the alternating sum of the values of the faces. -/
theorem evalAt_cechD {p : ℕ} (s : Cochain U (locallyConstantIntPresheaf X) p)
    (i : Fin (p + 1 + 1) → I) {y : X} (hy : y ∈ inter U i) :
    evalAt U (cechD U (locallyConstantIntPresheaf X) p s) i hy =
      ∑ j : Fin (p + 1 + 1), ((-1 : ℤ) ^ (j : ℕ)) *
        evalAt U s (i ∘ j.succAbove) (inter_le_omit U i j hy) := by
  rw [evalAt, cechD_apply, ← LocallyConstant.evalAddMonoidHom_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, zsmul_eq_mul, Int.cast_id]
  rfl

end CechCochains

namespace TopologicalSpace.DimensionFunction

variable {X : TopCat} {I : Type*}

/-! ## The discrepancy cocycle of a family of local dimension functions -/

/-- The Čech `1`-cochain of local discrepancies: on `U i₀ ∩ U i₁` it is `δ i₀ - δ i₁`, which is
locally constant by Stacks 02IB. -/
noncomputable def discrepancy [QuasiSober X] [T0Space X]
    (hX : IsLocallyNoetherianSpace X) (U : I → Opens X)
    (δ : ∀ i, DimensionFunction (U i : Set X)) :
    CechCochains.Cochain U (locallyConstantIntPresheaf X) 1 := fun i =>
  { toFun := fun p => δ (i 0) ⟨p.1, CechCochains.inter_le U i 0 p.2⟩
      - δ (i 1) ⟨p.1, CechCochains.inter_le U i 1 p.2⟩
    isLocallyConstant := by
      have hV : IsOpen (CechCochains.inter U i : Set X) := (CechCochains.inter U i).isOpen
      have : QuasiSober (CechCochains.inter U i : Set X) :=
        Topology.IsOpenEmbedding.quasiSober hV.isOpenEmbedding_subtypeVal
      exact isLocallyConstant_sub (hX.subtype _)
        ((δ (i 0)).comp (isOpenEmbedding_inclusion (U (i 0)).isOpen hV
          (CechCochains.inter_le U i 0)))
        ((δ (i 1)).comp (isOpenEmbedding_inclusion (U (i 1)).isOpen hV
          (CechCochains.inter_le U i 1))) }

/-- On `U i₀ ∩ U i₁` the discrepancy cochain is `δ i₀ - δ i₁`. -/
@[simp]
theorem discrepancy_apply [QuasiSober X] [T0Space X] (hX : IsLocallyNoetherianSpace X)
    (U : I → Opens X) (δ : ∀ i, DimensionFunction (U i : Set X)) (i : Fin 2 → I)
    (p : (CechCochains.inter U i : Set X)) :
    discrepancy hX U δ i p =
      δ (i 0) ⟨p.1, CechCochains.inter_le U i 0 p.2⟩
        - δ (i 1) ⟨p.1, CechCochains.inter_le U i 1 p.2⟩ := rfl

/-- The value of the discrepancy cochain at a point. -/
theorem evalAt_discrepancy [QuasiSober X] [T0Space X] (hX : IsLocallyNoetherianSpace X)
    (U : I → Opens X) (δ : ∀ i, DimensionFunction (U i : Set X)) (i : Fin 2 → I) {y : X}
    (hy : y ∈ CechCochains.inter U i) :
    CechCochains.evalAt U (discrepancy hX U δ) i hy =
      δ (i 0) ⟨y, CechCochains.inter_le U i 0 hy⟩ -
        δ (i 1) ⟨y, CechCochains.inter_le U i 1 hy⟩ := rfl

/-- The discrepancy cochain is a Čech `1`-cocycle. -/
theorem discrepancy_mem_cocycles1 [QuasiSober X] [T0Space X] (hX : IsLocallyNoetherianSpace X)
    (U : I → Opens X) (δ : ∀ i, DimensionFunction (U i : Set X)) :
    discrepancy hX U δ ∈ CechCochains.cocycles1 U (locallyConstantIntPresheaf X) := by
  rw [CechCochains.mem_cocycles1_iff]
  funext i
  refine LocallyConstant.ext fun x => ?_
  have hx : ∀ k, x.1 ∈ U (i k) := fun k => CechCochains.inter_le U i k x.2
  rw [← CechCochains.evalAt_val, CechCochains.evalAt_cechD, Fin.sum_univ_three]
  have h0 : CechCochains.evalAt U (discrepancy hX U δ) (i ∘ (0 : Fin 3).succAbove)
      (CechCochains.inter_le_omit U i 0 x.2)
      = δ (i 1) ⟨x.1, hx 1⟩ - δ (i 2) ⟨x.1, hx 2⟩ := rfl
  have h1 : CechCochains.evalAt U (discrepancy hX U δ) (i ∘ (1 : Fin 3).succAbove)
      (CechCochains.inter_le_omit U i 1 x.2)
      = δ (i 0) ⟨x.1, hx 0⟩ - δ (i 2) ⟨x.1, hx 2⟩ := rfl
  have h2 : CechCochains.evalAt U (discrepancy hX U δ) (i ∘ (2 : Fin 3).succAbove)
      (CechCochains.inter_le_omit U i 2 x.2)
      = δ (i 0) ⟨x.1, hx 0⟩ - δ (i 1) ⟨x.1, hx 1⟩ := rfl
  rw [h0, h1, h2]
  norm_num

/-- The **obstruction class** of a family of local dimension functions: the class in `Ȟ¹(𝒰, ℤ)` of
the discrepancy cocycle. -/
noncomputable def obstruction [QuasiSober X] [T0Space X] (hX : IsLocallyNoetherianSpace X)
    (U : I → Opens X) (δ : ∀ i, DimensionFunction (U i : Set X)) :
    CechCochains.CechH1 U (locallyConstantIntPresheaf X) :=
  CechCochains.cls U _ ⟨discrepancy hX U δ, discrepancy_mem_cocycles1 hX U δ⟩

/-- **Stacks 02ID.** For a cover of a locally Noetherian sober space by opens carrying dimension
functions `δ i`, a global dimension function on `X` exists if and only if the class of the
discrepancy cocycle `δ i - δ j` vanishes in `Ȟ¹(𝒰, ℤ)`.

Both directions use tag 02IB. Forward: if `d` is global then `d - δ i` is locally constant on
`U i`, and these functions are a `0`-cochain whose coboundary is the discrepancy. Backward: a
`0`-cochain `t` with `d⁰ t` the discrepancy makes `δ i + t i` independent of `i`, hence a global
function; it is a dimension function because an open set is stable under generization (so both
ends of a specialization lie in a common member of the cover) and because a locally constant
function is constant along specializations. -/
@[stacks 02ID]
theorem exists_dimensionFunction_iff_obstruction_eq_zero [QuasiSober X] [T0Space X]
    (hX : IsLocallyNoetherianSpace X) (U : I → Opens X) (hcov : ∀ x : X, ∃ i, x ∈ U i)
    (δ : ∀ i, DimensionFunction (U i : Set X)) :
    Nonempty (DimensionFunction X) ↔ obstruction hX U δ = 0 := by
  rw [obstruction, CechCochains.cls_eq_zero_iff]
  constructor
  · rintro ⟨d⟩
    have hlc : ∀ k : I, IsLocallyConstant (fun p : (U k : Set X) => d p.1 - δ k p) := by
      intro k
      have : QuasiSober (U k : Set X) :=
        Topology.IsOpenEmbedding.quasiSober (U k).isOpen.isOpenEmbedding_subtypeVal
      exact isLocallyConstant_sub (hX.subtype _)
        (d.comp (U k).isOpen.isOpenEmbedding_subtypeVal) (δ k)
    set t : CechCochains.Cochain U (locallyConstantIntPresheaf X) 0 :=
      fun k => locallyConstantRes (CechCochains.inter_le U k 0) ⟨_, hlc (k 0)⟩ with ht
    refine ⟨t, ?_⟩
    funext i
    refine LocallyConstant.ext fun x => ?_
    have hx : ∀ k, x.1 ∈ U (i k) := fun k => CechCochains.inter_le U i k x.2
    rw [← CechCochains.evalAt_val, ← CechCochains.evalAt_val, CechCochains.evalAt_cechD,
      Fin.sum_univ_two, evalAt_discrepancy]
    have h0 : CechCochains.evalAt U t (i ∘ (0 : Fin 2).succAbove)
        (CechCochains.inter_le_omit U i 0 x.2) = d x.1 - δ (i 1) ⟨x.1, hx 1⟩ := rfl
    have h1 : CechCochains.evalAt U t (i ∘ (1 : Fin 2).succAbove)
        (CechCochains.inter_le_omit U i 1 x.2) = d x.1 - δ (i 0) ⟨x.1, hx 0⟩ := rfl
    rw [h0, h1]
    norm_num
  · rintro ⟨t, ht⟩
    classical
    have key : ∀ (k l : I) (y : X) (hk : y ∈ U k) (hl : y ∈ U l),
        δ k ⟨y, hk⟩ + CechCochains.evalAt U t (fun _ => k) (CechCochains.le_inter_const U k hk)
          = δ l ⟨y, hl⟩ + CechCochains.evalAt U t (fun _ => l)
              (CechCochains.le_inter_const U l hl) := by
      intro k l y hk hl
      set i : Fin 2 → I := fun m => if m = 0 then k else l with hidef
      have hmem : y ∈ CechCochains.inter U i := CechCochains.mem_inter U (by
        intro m
        fin_cases m
        · exact hk
        · exact hl)
      have hface0 : (i ∘ (0 : Fin 2).succAbove) = (fun _ : Fin 1 => l) := by
        funext m; fin_cases m; rfl
      have hface1 : (i ∘ (1 : Fin 2).succAbove) = (fun _ : Fin 1 => k) := by
        funext m; fin_cases m; rfl
      have h : CechCochains.evalAt U (CechCochains.cechD U _ 0 t) i hmem
          = CechCochains.evalAt U (discrepancy hX U δ) i hmem :=
        congrArg (fun c => CechCochains.evalAt U c i hmem) ht
      rw [CechCochains.evalAt_cechD, Fin.sum_univ_two, evalAt_discrepancy] at h
      have e0 := CechCochains.evalAt_congr U t hface0
        (CechCochains.inter_le_omit U i 0 hmem) (CechCochains.le_inter_const U l hl)
      have e1 := CechCochains.evalAt_congr U t hface1
        (CechCochains.inter_le_omit U i 1 hmem) (CechCochains.le_inter_const U k hk)
      have hd0 : δ (i 0) ⟨y, CechCochains.inter_le U i 0 hmem⟩ = δ k ⟨y, hk⟩ := rfl
      have hd1 : δ (i 1) ⟨y, CechCochains.inter_le U i 1 hmem⟩ = δ l ⟨y, hl⟩ := rfl
      simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, neg_mul] at h
      rw [e0, e1, hd0, hd1] at h
      linarith [h]
    choose idx hidx using hcov
    have hkey : ∀ y z : X, y ⤳ z → ∃ hym : y ∈ U (idx z),
        δ (idx y) ⟨y, hidx y⟩ + CechCochains.evalAt U t (fun _ => idx y)
            (CechCochains.le_inter_const U (idx y) (hidx y)) -
          (δ (idx z) ⟨z, hidx z⟩ + CechCochains.evalAt U t (fun _ => idx z)
            (CechCochains.le_inter_const U (idx z) (hidx z))) =
        δ (idx z) ⟨y, hym⟩ - δ (idx z) ⟨z, hidx z⟩ := by
      intro y z hspec
      have hzm : z ∈ U (idx z) := hidx z
      have hym : y ∈ U (idx z) := hspec.mem_open (U (idx z)).isOpen hzm
      refine ⟨hym, ?_⟩
      have hs' : (⟨y, CechCochains.le_inter_const U (idx z) hym⟩ :
          (CechCochains.inter U (fun _ : Fin 1 => idx z) : Set X))
          ⤳ ⟨z, CechCochains.le_inter_const U (idx z) hzm⟩ :=
        Topology.IsInducing.subtypeVal.specializes_iff.mp hspec
      have h2 : CechCochains.evalAt U t (fun _ => idx z)
          (CechCochains.le_inter_const U (idx z) hym)
          = CechCochains.evalAt U t (fun _ => idx z)
              (CechCochains.le_inter_const U (idx z) hzm) :=
        (t (fun _ => idx z)).eq_of_specializes hs'
      have h3 := key (idx y) (idx z) y (hidx y) hym
      have h4 := key (idx z) (idx z) z (hidx z) hzm
      omega
    refine ⟨⟨fun y => δ (idx y) ⟨y, hidx y⟩
      + CechCochains.evalAt U t (fun _ => idx y)
          (CechCochains.le_inter_const U (idx y) (hidx y)), ?_, ?_⟩⟩
    · intro y z hspec hne
      obtain ⟨hym, h⟩ := hkey y z hspec
      have hs : (⟨y, hym⟩ : (U (idx z) : Set X)) ⤳ ⟨z, hidx z⟩ :=
        Topology.IsInducing.subtypeVal.specializes_iff.mp hspec
      have h1 := (δ (idx z)).strictAnti_specializes hs fun h => hne (congrArg Subtype.val h)
      omega
    · intro y z himm
      obtain ⟨hym, h⟩ := hkey y z himm.1
      have h1 := (δ (idx z)).step_immediate (himm.subtype_of_isOpen (U (idx z)).isOpen (hidx z))
      omega

/-- Whether the obstruction vanishes does not depend on the chosen cover or on the chosen local
dimension functions: it is a property of `X`. -/
theorem obstruction_eq_zero_congr [QuasiSober X] [T0Space X] (hX : IsLocallyNoetherianSpace X)
    {J : Type*} (U : I → Opens X) (hcov : ∀ x : X, ∃ i, x ∈ U i)
    (δ : ∀ i, DimensionFunction (U i : Set X)) (V : J → Opens X)
    (hcov' : ∀ x : X, ∃ j, x ∈ V j) (ε : ∀ j, DimensionFunction (V j : Set X)) :
    obstruction hX U δ = 0 ↔ obstruction hX V ε = 0 :=
  (exists_dimensionFunction_iff_obstruction_eq_zero hX U hcov δ).symm.trans
    (exists_dimensionFunction_iff_obstruction_eq_zero hX V hcov' ε)

/-- Tag 02IC, packaged as a cover: on a locally Noetherian sober catenary space every point has an
open neighbourhood carrying a dimension function, so the neighbourhoods of all points form a cover
by opens with dimension functions. -/
theorem exists_cover_dimensionFunction [QuasiSober X] [T0Space X]
    (hLN : IsLocallyNoetherianSpace X) (hCat : IsTopologicallyCatenary X) :
    ∃ (U : X → Opens X) (_δ : ∀ x, DimensionFunction (U x : Set X)), ∀ x, x ∈ U x := by
  choose V hVopen hxV hVdim using
    fun x => exists_open_nhd_with_dimension_function (X : Type _) hLN hCat x
  exact ⟨fun x => ⟨V x, hVopen x⟩, fun x => (hVdim x).some, hxV⟩

/-- **Stacks 02ID.** On a catenary, locally Noetherian, sober topological space there is a cover by
opens carrying dimension functions (tag 02IC), and a global dimension function exists exactly when
the obstruction class of that cover vanishes in `Ȟ¹(𝒰, ℤ)`. By `obstruction_eq_zero_congr` the
vanishing is independent of the cover, so this single class is *the* obstruction. -/
@[stacks 02ID]
theorem exists_cover_dimensionFunction_iff_obstruction_eq_zero [QuasiSober X] [T0Space X]
    (hLN : IsLocallyNoetherianSpace X) (hCat : IsTopologicallyCatenary X) :
    ∃ (U : X → Opens X) (δ : ∀ x, DimensionFunction (U x : Set X)),
      (∀ x, x ∈ U x) ∧ (Nonempty (DimensionFunction X) ↔ obstruction hLN U δ = 0) := by
  obtain ⟨U, δ, hxU⟩ := exists_cover_dimensionFunction hLN hCat
  exact ⟨U, δ, hxU, exists_dimensionFunction_iff_obstruction_eq_zero hLN U
    (fun x => ⟨x, hxU x⟩) δ⟩

end TopologicalSpace.DimensionFunction
