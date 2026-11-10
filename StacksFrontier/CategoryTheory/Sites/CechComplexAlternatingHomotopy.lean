module

public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.GroupTheory.FreeAbelianGroup
public import StacksFrontier.CategoryTheory.Sites.CechComplexAlternating
import StacksCore.Tactic.StacksAttribute

/-!
# The alternating Čech complex of a family in a category is homotopy equivalent to the full one

[Stacks, Tag 01FM] says that for a family `U : I → Opens X` of open subsets of a topological
space and an abelian presheaf the canonical inclusion of the alternating Čech complex into the
full Čech complex is a homotopy equivalence. This file proves the same for a family `U : ι → C`
of subterminal objects of a category with finite products, in which the `p`-fold intersection is
the product `inter U t` and restriction along a reindexing is `tres`. The family need not cover
anything.

`Contained V W` is the proposition that there is a morphism `V ⟶ W`. When `W` is subterminal that
morphism is unique, so restriction along `Contained V W` is well defined; this replaces the
containment `V ≤ W` of opens. Without subterminality the alternating cochains are not a subcomplex
of the full ones.

## Main definitions

Everything lives in the namespace `Stacks.CategoryTheory.CechComplex.Alternating`.

* `Contained V W` — the proposition that there is *some* morphism `V ⟶ W`, and `restr` — the
  restriction `P(W) ⟶ P(V)` along it.
* `cechCochainComplex`, `cechCochainComplexAlt` and `cechCochainComplexOrd` — the full, the
  alternating and the ordered Čech cochain complexes of the family, assembled from `cechDiff`,
  `cechDiffAlt` and `cechDiffOrd`, together with the canonical inclusion `cechAltInclusion` of
  the second into the first.
* `cechComparisonProjection` — the endomorphism `c ∘ π` of the full Čech complex, and
  `cochainHomotopy` — the homotopy contracting it to the identity.

## Main results

* `cechComparisonProjectionHomotopy` — **[Stacks, Tag 01FM]**, chain-level form: an explicit
  homotopy from `c ∘ π` to the identity.
* `cechAltInclusionHomotopyEquiv` and `cechAltInclusion_homotopyEquivalence` — **[Stacks,
  Tag 01FM] for a family in an arbitrary category**: the canonical inclusion of the
  alternating Čech complex is a homotopy equivalence, with `c ∘ π` as a homotopy inverse.
* `cochainHomotopy_identity` — the cochain-level identity: in positive degree the differential of
  the homotopy plus the homotopy of the differential is the identity minus `c ∘ π`.
* `cechProjAltComplexIso` — [Stacks, Tag 01FK] (2) assembled into an isomorphism of
  complexes, and hence `cechOrdHomotopyEquiv` and `cechCochainComplexOrdHomologyIso`: **the
  ordered Čech complex is homotopy equivalent to the full one, and has its cohomology in every
  degree.** The ordered complex is the one indexing the double complex of [Stacks, Tag 07MN].
* `cechComp_comp_cechDiffOrd` and `cechComp_cechProj_comp_cechDiff` — `c` and `c ∘ π` are
  morphisms of complexes.

All of these carry the hypothesis `hU : ∀ i, IsSubterminal (U i)`.

## References

* [Stacks Project, Tag 01FJ](https://stacks.math.columbia.edu/tag/01FJ)
* [Stacks Project, Tag 01FK](https://stacks.math.columbia.edu/tag/01FK)
* [Stacks Project, Tag 01FM](https://stacks.math.columbia.edu/tag/01FM)
* [Stacks Project, Tag 07MN](https://stacks.math.columbia.edu/tag/07MN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w' w v u

namespace Stacks.CategoryTheory.CechComplex.Alternating

noncomputable section

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {ι : Type w} [LinearOrder ι]

/-! ### The preorder underlying the category, and restriction along it -/

/-- `Contained V W` says that there is a morphism `V ⟶ W`.

Over a topological space, where the only morphisms of `Opens X` are the inclusions, this is
the containment `V ≤ W`.  In a general category it forgets which morphism is meant; when `W`
is subterminal there is nothing to forget. -/
def Contained (V W : C) : Prop := Nonempty (V ⟶ W)

omit [HasFiniteProducts C] in
/-- Any morphism witnesses `Contained`. -/
theorem Contained.of_hom {V W : C} (f : V ⟶ W) : Contained V W := ⟨f⟩

/-- The chosen morphism witnessing `Contained V W`.  When `W` is subterminal it is the only
morphism `V ⟶ W`, by `Contained.hom_eq`. -/
def Contained.hom {V W : C} (h : Contained V W) : V ⟶ W := Nonempty.some h

omit [HasFiniteProducts C] in
/-- When `W` is subterminal the chosen witness is the only morphism `V ⟶ W`. -/
theorem Contained.hom_eq {V W : C} (hW : IsSubterminal W) (h : Contained V W) (f : V ⟶ W) :
    h.hom = f := hW _ _

omit [HasFiniteProducts C] in
/-- Every object contains itself. -/
@[refl]
theorem Contained.refl (V : C) : Contained V V := ⟨𝟙 V⟩

omit [HasFiniteProducts C] in
/-- `Contained` is transitive. -/
theorem Contained.trans {V W T : C} (h : Contained V W) (h' : Contained W T) :
    Contained V T := ⟨h.hom ≫ h'.hom⟩

variable (P : Cᵒᵖ ⥤ AddCommGrpCat.{w'}) (U : ι → C)

/-- The restriction `P(W) ⟶ P(V)` along the chosen morphism `V ⟶ W`.  Over a topological
space this is the restriction map of the presheaf along an inclusion of opens. -/
def restr {V W : C} (h : Contained V W) :
    (P.obj (op W) : Type w') →+ (P.obj (op V) : Type w') :=
  (P.map h.hom.op).hom

omit [HasFiniteProducts C] in
/-- **Restriction along `Contained V W` is restriction along every morphism `V ⟶ W`, as soon
as `W` is subterminal.** -/
theorem restr_eq {V W : C} (hW : IsSubterminal W) (h : Contained V W) (f : V ⟶ W) :
    restr P h = (P.map f.op).hom := by
  rw [restr, h.hom_eq hW f]

omit [HasFiniteProducts C] in
/-- Restriction is functorial. -/
theorem restr_restr {V W T : C} (hT : IsSubterminal T) (h : Contained V W)
    (h' : Contained W T) (x : (P.obj (op T) : Type w')) :
    restr P h (restr P h' x) = restr P (h.trans h') x := by
  rw [restr_eq P hT (h.trans h') (h.hom ≫ h'.hom), restr, restr, ← CategoryTheory.comp_apply,
    ← Functor.map_comp, ← op_comp]

omit [LinearOrder ι] in
/-- Restriction along a reindexing, followed by restriction to `V`, is restriction to `V`
along the composite. -/
theorem restr_tres (hU : ∀ i, IsSubterminal (U i)) {V : C} {m n : ℕ} (φ : Fin m → Fin n)
    (t : Fin n → ι) (h : Contained V (inter U t))
    (x : (P.obj (op (inter U (t ∘ φ))) : Type w')) :
    restr P h (tres P U φ t x) =
      restr P (h.trans (Contained.of_hom (interMap U t φ))) x := by
  have e : tres P U φ t = restr P (Contained.of_hom (interMap U t φ)) :=
    (restr_eq P (isSubterminal_inter U hU (t ∘ φ)) _ (interMap U t φ)).symm
  rw [e, restr_restr P (isSubterminal_inter U hU (t ∘ φ))]

omit [HasFiniteProducts C] in
/-- Restriction along the chosen endomorphism of a subterminal object is the identity. -/
theorem restr_refl {V : C} (hV : IsSubterminal V) (x : (P.obj (op V) : Type w')) :
    restr P (Contained.refl V) x = x := by
  rw [restr_eq P hV _ (𝟙 V)]
  simp

omit [LinearOrder ι] in
/-- The vertices of a supported tuple are themselves containers of `V`. -/
theorem contained_vertex {V : C} {n : ℕ} {t : Fin n → ι} (h : Contained V (inter U t))
    (a : Fin n) : Contained V (U (t a)) :=
  Contained.of_hom (h.hom ≫ interπ U t a)

omit [LinearOrder ι] in
/-- Prepending a vertex to a supported tuple keeps it supported. -/
theorem contained_cons {V : C} {x : ι} (hx : Contained V (U x)) {n : ℕ} {t : Fin n → ι}
    (ht : Contained V (inter U t)) : Contained V (inter U (Fin.cons x t)) :=
  Contained.of_hom (interLift U fun a => Fin.cases hx.hom (fun k => ht.hom ≫ interπ U t k) a)

/-! ### Formal chains supported over an object -/

/-- A tuple of indices whose intersection receives a morphism from `V`: the space-level
`{t // V ≤ U_{t_0 … t_p}}` with `Contained` in place of `≤`. -/
abbrev SupportedTuple (U : ι → C) (V : C) (p : ℕ) :=
  {t : Fin (p + 1) → ι // Contained V (inter U t)}

/-- The formal chains supported over `V`: the free abelian group on the supported tuples. -/
abbrev SupportedChain (U : ι → C) (V : C) (p : ℕ) :=
  FreeAbelianGroup (SupportedTuple U V p)

/-- The `j`-th face of a supported tuple: the tuple with its `j`-th entry deleted, again
supported over `V`. -/
def faceTuple {V : C} {p : ℕ} (t : SupportedTuple U V (p + 1))
    (j : Fin (p + 2)) : SupportedTuple U V p :=
  ⟨t.1 ∘ j.succAbove, t.2.trans (Contained.of_hom (interMap U t.1 j.succAbove))⟩

/-- The boundary of supported chains: the alternating sum of the faces of a tuple. -/
def boundary (V : C) (p : ℕ) :
    SupportedChain U V (p + 1) →+ SupportedChain U V p :=
  FreeAbelianGroup.lift fun t =>
    ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) • FreeAbelianGroup.of (faceTuple U t j)

/-- Signed sorting of supported chains: an injective tuple goes to its sorted tuple times the sign
of the sorting permutation, a tuple with a repeated index to zero. -/
def projection (V : C) (p : ℕ) :
    SupportedChain U V p →+ SupportedChain U V p :=
  FreeAbelianGroup.lift fun t =>
    if _h : Function.Injective t.1 then
      (Equiv.Perm.sign (Tuple.sort t.1) : ℤ) • FreeAbelianGroup.of
        ⟨t.1 ∘ Tuple.sort t.1,
          t.2.trans (Contained.of_hom (interMap U t.1 (Tuple.sort t.1)))⟩
    else 0

/-- The map of supported chains given by `Contained V W`: a tuple supported over `W` is supported
over `V`. -/
def chainMap {V W : C} (h : Contained V W) (p : ℕ) :
    SupportedChain U W p →+ SupportedChain U V p :=
  FreeAbelianGroup.lift fun t => FreeAbelianGroup.of ⟨t.1, h.trans t.2⟩

/-- The pairing of a cochain `s` with the chains supported over `V`: a supported tuple `t` goes to
the restriction of `s t` to `V`. -/
def chainEval (V : C) (p : ℕ) (s : Alternating.CechCochain P U p) :
    SupportedChain U V p →+ (P.obj (op V) : Type w') :=
  FreeAbelianGroup.lift fun t => restr P t.2 (s t.1)

/-- The presheaf whose sections over `W` are the functions on the proofs that `W` contains `V`. -/
def probePresheaf (V : C) (A : Type w') [AddCommGroup A] :
    Cᵒᵖ ⥤ AddCommGrpCat.{w'} where
  obj W := AddCommGrpCat.of (PLift (Contained V W.unop) → A)
  map f := AddCommGrpCat.ofHom
    { toFun := fun s h => s ⟨h.down.trans (Contained.of_hom f.unop)⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

/-- The universal supported cochain: its component at a tuple `t` sends a proof that
`inter U t` contains `V` to the chain of `t`. -/
def probeCochain (V : C) (p : ℕ) :
    Alternating.CechCochain (probePresheaf (C := C) V (SupportedChain U V p)) U p :=
  fun t h => FreeAbelianGroup.of ⟨t, h.down⟩

omit [LinearOrder ι] in
/-- The pairing of `s` with a supported tuple `t` is the restriction of `s t` to `V`. -/
theorem chainEval_of (V : C) (p : ℕ) (s : Alternating.CechCochain P U p)
    (t : SupportedTuple U V p) :
    chainEval P U V p s (FreeAbelianGroup.of t) = restr P t.2 (s t.1) :=
  FreeAbelianGroup.lift_apply_of _ _

/-- Two additive maps out of a free abelian group agreeing on generators agree everywhere. -/
private theorem free_abelian_apply_eq {α A : Type*} [AddCommGroup A] (f g : FreeAbelianGroup α →+ A)
    (h : ∀ x, f (.of x) = g (.of x)) (a : FreeAbelianGroup α) : f a = g a :=
  DFunLike.congr_fun (FreeAbelianGroup.lift_ext f g h) a

omit [LinearOrder ι] in
/-- Pairing a cochain with the boundary of a chain is pairing its Čech differential with the
chain. -/
theorem eval_boundary (hU : ∀ i, IsSubterminal (U i)) (V : C) (p : ℕ)
    (s : Alternating.CechCochain P U p) (a : SupportedChain U V (p + 1)) :
    chainEval P U V p s (boundary U V p a) =
      chainEval P U V (p + 1) (Alternating.cechDiff P U p s) a := by
  refine free_abelian_apply_eq ((chainEval P U V p s).comp (boundary U V p))
    (chainEval P U V (p + 1) (Alternating.cechDiff P U p s)) (fun t => ?_) a
  rw [AddMonoidHom.comp_apply, boundary, FreeAbelianGroup.lift_apply_of, map_sum, chainEval_of]
  change (∑ j : Fin (p + 2), chainEval P U V p s ((-1 : ℤ) ^ (j : ℕ) •
      FreeAbelianGroup.of (faceTuple U t j))) =
    restr P t.2 (∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
      tres P U (Fin.succAbove j) t.1 (s (t.1 ∘ Fin.succAbove j)))
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, map_zsmul, chainEval_of, restr_tres P U hU]
  rfl

omit [LinearOrder ι] in
/-- Pairing the universal supported cochain with a chain, at the proof that `V` contains itself,
gives back the chain. -/
theorem eval_probe (V : C) (p : ℕ) (a : SupportedChain U V p) :
    chainEval (probePresheaf (C := C) V (SupportedChain U V p)) U V p
      (probeCochain U V p) a ⟨Contained.refl V⟩ = a := by
  exact free_abelian_apply_eq ((Pi.evalAddMonoidHom _ (PLift.up (Contained.refl V))).comp
    (chainEval (probePresheaf (C := C) V (SupportedChain U V p)) U V p
      (probeCochain U V p))) (AddMonoidHom.id _) (fun _ => rfl) a

omit [LinearOrder ι] in
/-- The boundary of supported chains squares to zero. -/
theorem boundary_boundary (hU : ∀ i, IsSubterminal (U i)) (V : C) (p : ℕ)
    (a : SupportedChain U V (p + 2)) :
    boundary U V p (boundary U V (p + 1) a) = 0 := by
  rw [← eval_probe U V p (boundary U V p (boundary U V (p + 1) a)),
    eval_boundary _ U hU, eval_boundary _ U hU]
  have hd : Alternating.cechDiff (probePresheaf (C := C) V (SupportedChain U V p)) U (p + 1)
      (Alternating.cechDiff (probePresheaf (C := C) V (SupportedChain U V p)) U p
        (probeCochain U V p)) = 0 :=
    DFunLike.congr_fun (Alternating.cechDiff_comp_cechDiff _ U p) (probeCochain U V p)
  rw [hd]
  have hz : chainEval (probePresheaf (C := C) V (SupportedChain U V p)) U V (p + 2) 0 = 0 := by
    apply FreeAbelianGroup.lift_ext
    intro t
    simp only [chainEval_of, AddMonoidHom.zero_apply]
    rfl
  rw [hz]
  rfl

/-- Pairing a cochain with the signed sorting of a chain is pairing `c ∘ π` of the cochain with
the chain. -/
theorem eval_projection (hU : ∀ i, IsSubterminal (U i)) (V : C) (p : ℕ)
    (s : Alternating.CechCochain P U p) (a : SupportedChain U V p) :
    chainEval P U V p s (projection U V p a) =
      chainEval P U V p (Alternating.cechComp P U p (Alternating.cechProj P U p s)) a := by
  classical
  refine free_abelian_apply_eq ((chainEval P U V p s).comp (projection U V p))
    (chainEval P U V p (Alternating.cechComp P U p (Alternating.cechProj P U p s)))
    (fun t => ?_) a
  rw [AddMonoidHom.comp_apply, projection, FreeAbelianGroup.lift_apply_of, chainEval_of]
  change _ = restr P t.2 (if h : Function.Injective t.1 then
      (Equiv.Perm.sign (Tuple.sort t.1) : ℤ) • tres P U (Tuple.sort t.1) t.1
        (Alternating.cechProj P U p s ⟨t.1 ∘ Tuple.sort t.1, strictMono_comp_sort t.1 h⟩)
    else 0)
  by_cases ht : Function.Injective t.1
  · simp only [dite_eq_left ht, map_zsmul, chainEval_of, restr_tres P U hU]
    rfl
  · simp only [dite_eq_right ht, map_zero]

/-- **The comparison map `c` is a morphism of complexes**, `c ∘ d_ord = d ∘ c`, for a family of
subterminal objects. -/
theorem cechComp_comp_cechDiffOrd (hU : ∀ i, IsSubterminal (U i)) (p : ℕ)
    (r : Alternating.CechCochainOrd P U p) :
    Alternating.cechComp P U (p + 1) (Alternating.cechDiffOrd P U p r) =
      Alternating.cechDiff P U p (Alternating.cechComp P U p r) := by
  have halt : Alternating.cechDiff P U p (Alternating.cechComp P U p r) ∈
      Alternating.CechCochainAlt P U (p + 1) :=
    Alternating.cechDiff_mem_alt P U hU p _ (Alternating.isAlt_cechComp P U p r)
  have h1 : Alternating.cechComp P U (p + 1) (Alternating.cechProj P U (p + 1)
      (Alternating.cechDiff P U p (Alternating.cechComp P U p r))) =
        Alternating.cechDiff P U p (Alternating.cechComp P U p r) :=
    Alternating.cechComp_cechProj_of_isAlt P U _ halt
  rw [← h1]
  congr 1
  have h2 := DFunLike.congr_fun (Alternating.cechProj_comp_cechDiff P U p)
    (Alternating.cechComp P U p r)
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply] at h2
  have h3 := DFunLike.congr_fun (Alternating.cechProj_comp_cechComp P U p) r
  rw [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at h3
  rw [h2, h3]

/-- **The endomorphism `c ∘ π` of the full Čech cochains commutes with the differential.** -/
theorem cechComp_cechProj_comp_cechDiff (hU : ∀ i, IsSubterminal (U i)) (p : ℕ)
    (s : Alternating.CechCochain P U p) :
    Alternating.cechComp P U (p + 1)
        (Alternating.cechProj P U (p + 1) (Alternating.cechDiff P U p s)) =
      Alternating.cechDiff P U p (Alternating.cechComp P U p (Alternating.cechProj P U p s)) := by
  have h2 := DFunLike.congr_fun (Alternating.cechProj_comp_cechDiff P U p) s
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply] at h2
  rw [h2, cechComp_comp_cechDiffOrd P U hU]

/-- Signed sorting commutes with the boundary of supported chains. -/
theorem boundary_projection (hU : ∀ i, IsSubterminal (U i)) (V : C) (p : ℕ)
    (a : SupportedChain U V (p + 1)) :
    boundary U V p (projection U V (p + 1) a) =
      projection U V p (boundary U V p a) := by
  rw [← eval_probe U V p (boundary U V p _), eval_boundary _ U hU,
    eval_projection _ U hU, ← eval_probe U V p (projection U V p _),
    eval_projection _ U hU, eval_boundary _ U hU,
    cechComp_cechProj_comp_cechDiff _ U hU]

/-- In degree zero signed sorting of supported chains is the identity. -/
theorem projection_zero (V : C) (a : SupportedChain U V 0) :
    projection U V 0 a = a := by
  refine free_abelian_apply_eq (projection U V 0) (AddMonoidHom.id _) (fun t => ?_) a
  have hi : Function.Injective t.1 := fun _ _ _ => Fin.ext (by omega)
  have hs : Tuple.sort t.1 = 1 := Equiv.ext fun j => Fin.ext (by omega)
  rw [projection, FreeAbelianGroup.lift_apply_of, dite_eq_left hi]
  have h1 : (Equiv.Perm.sign (Tuple.sort t.1) : ℤ) = 1 := by rw [hs]; simp
  rw [h1, one_smul, AddMonoidHom.id_apply]
  congr 1
  exact Subtype.ext (by simp [hs])

/-! ### Coning at a vertex contracts the supported chains -/

/-- The cone of a supported tuple at a vertex `x` that contains `V`: the tuple with `x`
prepended. -/
def coneTuple {V : C} (x : ι) (hx : Contained V (U x)) {p : ℕ}
    (t : SupportedTuple U V p) : SupportedTuple U V (p + 1) :=
  ⟨Fin.cons x t.1, contained_cons U hx t.2⟩

/-- Coning at a vertex `x` that contains `V`, on supported chains. -/
def cone {V : C} (x : ι) (hx : Contained V (U x)) (p : ℕ) :
    SupportedChain U V p →+ SupportedChain U V (p + 1) :=
  FreeAbelianGroup.lift fun t => FreeAbelianGroup.of (coneTuple U x hx t)

omit [LinearOrder ι] in
/-- The `0`-th face of the cone of a tuple is the tuple. -/
theorem faceTuple_cone_zero {V : C} (x : ι) (hx : Contained V (U x)) {p : ℕ}
    (t : SupportedTuple U V (p + 1)) :
    faceTuple U (coneTuple U x hx t) 0 = t := by
  apply Subtype.ext; funext j; simp [faceTuple, coneTuple]

omit [LinearOrder ι] in
/-- The `(j + 1)`-st face of the cone of a tuple is the cone of its `j`-th face. -/
theorem faceTuple_cone_succ {V : C} (x : ι) (hx : Contained V (U x)) {p : ℕ}
    (t : SupportedTuple U V (p + 1)) (j : Fin (p + 2)) :
    faceTuple U (coneTuple U x hx t) j.succ = coneTuple U x hx (faceTuple U t j) :=
  Subtype.ext (Fin.cons_comp_succ_succAbove x t.1 j)

omit [LinearOrder ι] in
/-- The boundary of the cone of a chain `a` of positive degree is `a` minus the cone of the
boundary of `a`. -/
theorem boundary_cone {V : C} (x : ι) (hx : Contained V (U x)) (p : ℕ)
    (a : SupportedChain U V (p + 1)) :
    boundary U V (p + 1) (cone U x hx (p + 1) a) =
      a - cone U x hx p (boundary U V p a) := by
  refine free_abelian_apply_eq ((boundary U V (p + 1)).comp (cone U x hx (p + 1)))
    (AddMonoidHom.id _ - (cone U x hx p).comp (boundary U V p)) (fun t => ?_) a
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.sub_apply, AddMonoidHom.id_apply,
    cone, boundary, FreeAbelianGroup.lift_apply_of, map_sum, map_zsmul]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, faceTuple_cone_zero, faceTuple_cone_succ,
    Fin.val_succ, pow_succ, mul_neg_one, neg_smul]
  rw [Finset.sum_neg_distrib, sub_eq_add_neg]

/-! ### Compatibility with restriction of the supporting object -/

omit [LinearOrder ι] in
/-- The map of supported chains given by `Contained V W` commutes with the boundary. -/
theorem chainMap_boundary {V W : C} (h : Contained V W) (p : ℕ)
    (a : SupportedChain U W (p + 1)) :
    chainMap U h p (boundary U W p a) = boundary U V p (chainMap U h (p + 1) a) := by
  refine free_abelian_apply_eq ((chainMap U h p).comp (boundary U W p))
    ((boundary U V p).comp (chainMap U h (p + 1))) (fun t => ?_) a
  simp only [AddMonoidHom.comp_apply, chainMap, boundary, FreeAbelianGroup.lift_apply_of,
    map_sum, map_zsmul]
  rfl

/-- The map of supported chains given by `Contained V W` commutes with signed sorting. -/
theorem chainMap_projection {V W : C} (h : Contained V W) (p : ℕ)
    (a : SupportedChain U W p) :
    chainMap U h p (projection U W p a) = projection U V p (chainMap U h p a) := by
  classical
  refine free_abelian_apply_eq ((chainMap U h p).comp (projection U W p))
    ((projection U V p).comp (chainMap U h p)) (fun t => ?_) a
  simp only [AddMonoidHom.comp_apply, chainMap, projection, FreeAbelianGroup.lift_apply_of]
  split_ifs <;> simp only [map_zsmul, map_zero, FreeAbelianGroup.lift_apply_of]

omit [LinearOrder ι] in
/-- The map of supported chains given by `Contained V W` commutes with coning. -/
theorem chainMap_cone {V W : C} (h : Contained V W) (x : ι)
    (hx : Contained W (U x)) (p : ℕ) (a : SupportedChain U W p) :
    chainMap U h (p + 1) (cone U x hx p a) =
      cone U x (h.trans hx) p (chainMap U h p a) := by
  refine free_abelian_apply_eq ((chainMap U h (p + 1)).comp (cone U x hx p))
    ((cone U x (h.trans hx) p).comp (chainMap U h p)) (fun t => ?_) a
  simp only [AddMonoidHom.comp_apply, chainMap, cone, FreeAbelianGroup.lift_apply_of]
  rfl

omit [LinearOrder ι] in
/-- Pairing a cochain with the image of a chain supported over `W` is the restriction to `V` of
its pairing over `W`. -/
theorem eval_chainMap (hU : ∀ i, IsSubterminal (U i)) {V W : C}
    (h : Contained V W) (p : ℕ) (s : Alternating.CechCochain P U p) (a : SupportedChain U W p) :
    chainEval P U V p s (chainMap U h p a) =
      restr P h (chainEval P U W p s a) := by
  refine free_abelian_apply_eq ((chainEval P U V p s).comp (chainMap U h p))
    ((restr P h).comp (chainEval P U W p s)) (fun t => ?_) a
  rw [AddMonoidHom.comp_apply, chainMap, FreeAbelianGroup.lift_apply_of, chainEval_of,
    AddMonoidHom.comp_apply, chainEval_of, restr_restr P (isSubterminal_inter U hU t.1)]

/-! ### The chain homotopy from signed sorting to the identity -/

/-- The cone on the discrepancy in the preceding degree gives the next component of the
homotopy from signed sorting to the identity.  Coning is at the `0`-th vertex of the tuple,
which is a vertex the supporting object maps into (`contained_vertex`). -/
def chainHomotopy (V : C) :
    (p : ℕ) → (SupportedChain U V p →+ SupportedChain U V (p + 1))
  | 0 => 0
  | p + 1 => FreeAbelianGroup.lift fun t =>
      cone U (t.1 0) (contained_vertex U t.2 0) (p + 1)
        (FreeAbelianGroup.of t - projection U V (p + 1) (FreeAbelianGroup.of t) -
          chainHomotopy V p (boundary U V p (FreeAbelianGroup.of t)))

omit [LinearOrder ι] in
/-- The map of supported chains given by `Contained V W` sends a tuple supported over `W` to the
same tuple, supported over `V`. -/
theorem chainMap_of {V W : C} (h : Contained V W) (p : ℕ)
    (t : SupportedTuple U W p) :
    chainMap U h p (FreeAbelianGroup.of t) =
      FreeAbelianGroup.of ⟨t.1, h.trans t.2⟩ :=
  FreeAbelianGroup.lift_apply_of _ _

/-- In positive degree the chain homotopy sends a supported tuple `t` to the cone at its `0`-th
vertex of `t`, minus its signed sorting, minus the homotopy of its boundary. -/
theorem chainHomotopy_succ_of (V : C) (p : ℕ) (t : SupportedTuple U V (p + 1)) :
    chainHomotopy U V (p + 1) (FreeAbelianGroup.of t) =
      cone U (t.1 0) (contained_vertex U t.2 0) (p + 1)
        (FreeAbelianGroup.of t - projection U V (p + 1) (FreeAbelianGroup.of t) -
          chainHomotopy U V p (boundary U V p (FreeAbelianGroup.of t))) :=
  FreeAbelianGroup.lift_apply_of _ _

/-- The chain homotopy commutes with the map of supported chains given by `Contained V W`. -/
theorem chainMap_homotopy {V W : C} (h : Contained V W) (p : ℕ)
    (a : SupportedChain U W p) :
    chainMap U h (p + 1) (chainHomotopy U W p a) =
      chainHomotopy U V p (chainMap U h p a) := by
  induction p with
  | zero => simp only [chainHomotopy, AddMonoidHom.zero_apply, map_zero]
  | succ p ih =>
    refine free_abelian_apply_eq ((chainMap U h (p + 2)).comp (chainHomotopy U W (p + 1)))
      ((chainHomotopy U V (p + 1)).comp (chainMap U h (p + 1))) (fun t => ?_) a
    simp only [AddMonoidHom.comp_apply, chainMap_of, chainHomotopy_succ_of]
    rw [chainMap_cone]
    simp only [map_sub, chainMap_projection, ih, chainMap_boundary, chainMap_of]

/-- **The contraction identity for supported chains.**  In positive degree the boundary of
the homotopy, plus the homotopy of the boundary, is the difference between a chain and its
signed sorting. -/
theorem chainHomotopy_identity (hU : ∀ i, IsSubterminal (U i)) (V : C) (p : ℕ)
    (a : SupportedChain U V (p + 1)) :
    boundary U V (p + 1) (chainHomotopy U V (p + 1) a) +
        chainHomotopy U V p (boundary U V p a) =
      a - projection U V (p + 1) a := by
  induction p with
  | zero =>
    refine free_abelian_apply_eq ((boundary U V 1).comp (chainHomotopy U V 1) +
        (chainHomotopy U V 0).comp (boundary U V 0))
      (AddMonoidHom.id _ - projection U V 1) (fun t => ?_) a
    simp only [AddMonoidHom.add_apply, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, chainHomotopy, FreeAbelianGroup.lift_apply_of,
      AddMonoidHom.zero_apply, sub_zero, add_zero]
    have hc : boundary U V 0 (FreeAbelianGroup.of t -
        projection U V 1 (FreeAbelianGroup.of t)) = 0 := by
      rw [map_sub, boundary_projection U hU, projection_zero, sub_self]
    rw [boundary_cone, hc, map_zero, sub_zero]
  | succ p ih =>
    refine free_abelian_apply_eq ((boundary U V (p + 2)).comp (chainHomotopy U V (p + 2)) +
        (chainHomotopy U V (p + 1)).comp (boundary U V (p + 1)))
      (AddMonoidHom.id _ - projection U V (p + 2)) (fun t => ?_) a
    simp only [AddMonoidHom.add_apply, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, chainHomotopy_succ_of]
    have hi := ih (boundary U V (p + 1) (FreeAbelianGroup.of t))
    rw [boundary_boundary U hU, map_zero, add_zero] at hi
    have hc : boundary U V (p + 1)
        (FreeAbelianGroup.of t - projection U V (p + 2) (FreeAbelianGroup.of t) -
          chainHomotopy U V (p + 1)
            (boundary U V (p + 1) (FreeAbelianGroup.of t))) = 0 := by
      simp only [map_sub, boundary_projection U hU, hi, sub_self]
    rw [boundary_cone, hc, map_zero, sub_zero]
    abel

/-! ### Pairing the formal chains against cochains -/

omit [LinearOrder ι] in
/-- Pairing `s` with the tuple `t`, supported over `inter U t` itself, gives `s t`. -/
theorem chainEval_self (hU : ∀ i, IsSubterminal (U i)) (p : ℕ)
    (s : Alternating.CechCochain P U p) (t : Fin (p + 1) → ι) :
    chainEval P U (inter U t) p s
        (FreeAbelianGroup.of ⟨t, Contained.refl (inter U t)⟩) = s t := by
  rw [chainEval_of]
  exact restr_refl P (isSubterminal_inter U hU t) (s t)

/-- The pairing of Čech cochains with the chains supported over `V`, as an additive map in the
cochain. -/
def chainPairing (V : C) (p : ℕ) :
    Alternating.CechCochain P U p →+ (SupportedChain U V p →+ (P.obj (op V) : Type w')) where
  toFun := chainEval P U V p
  map_zero' := by
    apply FreeAbelianGroup.lift_ext
    intro t
    rw [chainEval_of]
    change restr P t.2 ((0 : Alternating.CechCochain P U p) t.1) = _
    rw [show ((0 : Alternating.CechCochain P U p) t.1) = 0 from rfl, map_zero]
    rfl
  map_add' s r := by
    apply FreeAbelianGroup.lift_ext
    intro t
    rw [AddMonoidHom.add_apply, chainEval_of, chainEval_of, chainEval_of]
    change restr P t.2 (s t.1 + r t.1) = _
    rw [map_add]

/-- The homotopy on Čech cochains: the component at a tuple `t` is the pairing of the given
cochain against the universal supported chain's homotopy over `inter U t`. -/
def cochainHomotopy (p : ℕ) :
    Alternating.CechCochain P U (p + 1) →+ Alternating.CechCochain P U p :=
  AddMonoidHom.pi fun t =>
    (AddMonoidHom.eval (chainHomotopy U (inter U t) p
      (FreeAbelianGroup.of ⟨t, Contained.refl (inter U t)⟩))).comp
        (chainPairing P U (inter U t) (p + 1))

/-- The component at a tuple `t` of the cochain homotopy is the pairing of the cochain with the
chain homotopy of `t`, over `inter U t`. -/
theorem cochainHomotopy_apply (p : ℕ) (s : Alternating.CechCochain P U (p + 1))
    (t : Fin (p + 1) → ι) :
    cochainHomotopy P U p s t =
      chainEval P U (inter U t) (p + 1) s
        (chainHomotopy U (inter U t) p
          (FreeAbelianGroup.of ⟨t, Contained.refl (inter U t)⟩)) := rfl

/-- The cochain homotopy from degree one to degree zero is zero. -/
theorem cochainHomotopy_zero (s : Alternating.CechCochain P U 1) :
    cochainHomotopy P U 0 s = 0 := by
  funext t
  rw [cochainHomotopy_apply]
  exact map_zero _

/-- Pairing the cochain homotopy of `s` with a chain is pairing `s` with the chain homotopy of
the chain. -/
theorem eval_homotopy (hU : ∀ i, IsSubterminal (U i)) (V : C) (p : ℕ)
    (s : Alternating.CechCochain P U (p + 1)) (a : SupportedChain U V p) :
    chainEval P U V p (cochainHomotopy P U p s) a =
      chainEval P U V (p + 1) s (chainHomotopy U V p a) := by
  refine free_abelian_apply_eq (chainEval P U V p (cochainHomotopy P U p s))
    ((chainEval P U V (p + 1) s).comp (chainHomotopy U V p)) (fun t => ?_) a
  rw [chainEval_of, AddMonoidHom.comp_apply, cochainHomotopy_apply,
    ← eval_chainMap P U hU t.2, chainMap_homotopy]
  rfl

/-- **The cochain-level content of [Stacks, Tag 01FM].**  In positive degree the Čech
differential of the homotopy, plus the homotopy of the differential, is the difference
between a cochain and its signed sorting `c ∘ π`. -/
theorem cochainHomotopy_identity (hU : ∀ i, IsSubterminal (U i)) (p : ℕ)
    (s : Alternating.CechCochain P U (p + 1)) :
    cochainHomotopy P U (p + 1) (Alternating.cechDiff P U (p + 1) s) +
        Alternating.cechDiff P U p (cochainHomotopy P U p s) =
      s - Alternating.cechComp P U (p + 1) (Alternating.cechProj P U (p + 1) s) := by
  funext t
  have h := congrArg (chainEval P U (inter U t) (p + 1) s)
    (chainHomotopy_identity U hU (inter U t) p
      (FreeAbelianGroup.of ⟨t, Contained.refl (inter U t)⟩))
  simp only [map_add, map_sub, eval_boundary P U hU, ← eval_homotopy P U hU,
    eval_projection P U hU, chainEval_self P U hU] at h
  exact h

/-- In degree zero signed sorting is already the identity. -/
theorem cechComp_cechProj_zero (hU : ∀ i, IsSubterminal (U i))
    (s : Alternating.CechCochain P U 0) :
    Alternating.cechComp P U 0 (Alternating.cechProj P U 0 s) = s := by
  funext t
  have h := eval_projection P U hU (inter U t) 0 s
    (FreeAbelianGroup.of ⟨t, Contained.refl (inter U t)⟩)
  rw [projection_zero, chainEval_self P U hU, chainEval_self P U hU] at h
  exact h.symm

/-! ### The Čech cochain complexes and the homotopy equivalence -/

/-- The full Čech cochain complex of the family, with differential `cechDiff`. -/
@[implicit_reducible, ega "0 11.8.7" "more general"]
def cechCochainComplex : CochainComplex AddCommGrpCat.{max w w'} ℕ :=
  CochainComplex.of
    (fun p => AddCommGrpCat.of (Alternating.CechCochain P U p))
    (fun p => AddCommGrpCat.ofHom (Alternating.cechDiff P U p))
    (fun p => by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      exact DFunLike.congr_fun (Alternating.cechDiff_comp_cechDiff P U p))

omit [LinearOrder ι] in
/-- The degree-`p` object of the full Čech cochain complex is the group of all cochains. -/
@[simp]
theorem cechCochainComplex_X (p : ℕ) :
    (cechCochainComplex P U).X p = AddCommGrpCat.of (Alternating.CechCochain P U p) := by
  simp [cechCochainComplex]

omit [LinearOrder ι] in
/-- The differential of the full Čech cochain complex is `cechDiff`. -/
@[simp]
theorem cechCochainComplex_d (p : ℕ) :
    (cechCochainComplex P U).d p (p + 1) = AddCommGrpCat.ofHom (Alternating.cechDiff P U p) :=
  CochainComplex.of_d
    (fun p => AddCommGrpCat.of (Alternating.CechCochain P U p))
    (fun p => AddCommGrpCat.ofHom (Alternating.cechDiff P U p)) p

/-- The differential of the alternating Čech cochains, as a morphism of `AddCommGrpCat`. -/
def cechDifferentialAlt (hU : ∀ i, IsSubterminal (U i)) (p : ℕ) :
    AddCommGrpCat.of (Alternating.CechCochainAlt P U p) ⟶
      AddCommGrpCat.of (Alternating.CechCochainAlt P U (p + 1)) :=
  AddCommGrpCat.ofHom (Alternating.cechDiffAlt P U hU p)

/-- **The alternating Čech cochain complex of a family of subterminal objects in a category.**
For such a family the alternating cochains form a subcomplex, as in [Stacks, Tag 01FK]. -/
@[implicit_reducible, ega "0 11.8.7" "more general", ega "0 12.1.2" "more general"]
def cechCochainComplexAlt (hU : ∀ i, IsSubterminal (U i)) :
    CochainComplex AddCommGrpCat.{max w w'} ℕ :=
  CochainComplex.of
    (fun p => AddCommGrpCat.of (Alternating.CechCochainAlt P U p))
    (cechDifferentialAlt P U hU)
    (fun p => by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro s
      apply Subtype.ext
      exact DFunLike.congr_fun (Alternating.cechDiff_comp_cechDiff P U p) s.1)

omit [LinearOrder ι] in
/-- The degree-`p` object of the alternating Čech cochain complex is the group of
alternating cochains. -/
@[simp]
theorem cechCochainComplexAlt_X (hU : ∀ i, IsSubterminal (U i)) (p : ℕ) :
    (cechCochainComplexAlt P U hU).X p = AddCommGrpCat.of (Alternating.CechCochainAlt P U p) := by
  simp [cechCochainComplexAlt]

omit [LinearOrder ι] in
/-- The differential of the alternating Čech cochain complex is `cechDifferentialAlt`. -/
@[simp]
theorem cechCochainComplexAlt_d (hU : ∀ i, IsSubterminal (U i)) (p : ℕ) :
    (cechCochainComplexAlt P U hU).d p (p + 1) = cechDifferentialAlt P U hU p :=
  CochainComplex.of_d
    (fun p => AddCommGrpCat.of (Alternating.CechCochainAlt P U p))
    (cechDifferentialAlt P U hU) p

/-- The canonical inclusion of the alternating Čech cochain complex into the full one. -/
def cechAltInclusion (hU : ∀ i, IsSubterminal (U i)) :
    cechCochainComplexAlt P U hU ⟶ cechCochainComplex P U :=
  CochainComplex.ofHom
    (fun p => AddCommGrpCat.ofHom (Alternating.CechCochainAlt P U p).subtype)
    (fun p => by
      rw [cechCochainComplexAlt_d, cechCochainComplex_d]
      rfl)

/-- The comparison map `c` from ordered to full Čech cochains, composed with the projection
`π` from full to ordered cochains, as an endomorphism of the full Čech complex. -/
def cechComparisonProjection (hU : ∀ i, IsSubterminal (U i)) :
    cechCochainComplex P U ⟶ cechCochainComplex P U :=
  CochainComplex.ofHom
    (fun p => AddCommGrpCat.ofHom ((Alternating.cechComp P U p).comp (Alternating.cechProj P U p)))
    (fun p => by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro s
      rw [cechCochainComplex_d]
      exact (cechComp_cechProj_comp_cechDiff P U hU p s).symm)

/-- The components of the homotopy on the full Čech complex: `cochainHomotopy` from degree
`j + 1` to degree `j`, and zero otherwise. -/
def cochainHomotopyComponent (i j : ℕ) :
    (cechCochainComplex P U).X i ⟶ (cechCochainComplex P U).X j :=
  if h : j + 1 = i then h ▸ AddCommGrpCat.ofHom (cochainHomotopy P U j) else 0

/-- From degree `j + 1` to degree `j` the homotopy is `cochainHomotopy`. -/
theorem cochainHomotopyComponent_succ (j : ℕ) :
    cochainHomotopyComponent P U (j + 1) j =
      AddCommGrpCat.ofHom (cochainHomotopy P U j) := by
  simp only [cochainHomotopyComponent, dite_true]

/-- **[Stacks, Tag 01FM] for a family in an arbitrary category, chain-level form.**  An
explicit homotopy from the endomorphism `c ∘ π` to the identity of the full Čech cochain
complex.  Its component from degree `j + 1` to degree `j` is `cochainHomotopy`. -/
@[stacks 01FM "c after projection is homotopic to the identity"]
def cechComparisonProjectionHomotopy (hU : ∀ i, IsSubterminal (U i)) :
    Homotopy (cechComparisonProjection P U hU) (𝟙 (cechCochainComplex P U)) := by
  refine Homotopy.symm { hom := cochainHomotopyComponent P U, zero := ?_, comm := ?_ }
  · exact fun i j h => dite_eq_right h
  · intro i
    rw [Homotopy.dNext_cochainComplex, cochainHomotopyComponent_succ]
    cases i with
    | zero =>
      rw [Homotopy.prevD_zero_cochainComplex, add_zero, cechCochainComplex_d]
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro s
      change s = cochainHomotopy P U 0 (Alternating.cechDiff P U 0 s) +
        Alternating.cechComp P U 0 (Alternating.cechProj P U 0 s)
      rw [cochainHomotopy_zero, zero_add, cechComp_cechProj_zero P U hU]
    | succ p =>
      rw [Homotopy.prevD_succ_cochainComplex, cochainHomotopyComponent_succ,
        cechCochainComplex_d, cechCochainComplex_d]
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro s
      change s = cochainHomotopy P U (p + 1) (Alternating.cechDiff P U (p + 1) s) +
        Alternating.cechDiff P U p (cochainHomotopy P U p s) +
          Alternating.cechComp P U (p + 1) (Alternating.cechProj P U (p + 1) s)
      rw [cochainHomotopy_identity P U hU, sub_add_cancel]

/-- **[Stacks, Tag 01FM] for a family in an arbitrary category.**  The canonical inclusion
of the alternating Čech cochain complex into the full Čech cochain complex is a homotopy
equivalence; signed sorting `c ∘ π`, corestricted to the alternating cochains, is a homotopy
inverse.  The family need not cover anything. -/
@[stacks 01FM "the canonical inclusion is a homotopy equivalence", ega "0 11.8.7" "more general"]
def cechAltInclusionHomotopyEquiv (hU : ∀ i, IsSubterminal (U i)) :
    HomotopyEquiv (cechCochainComplexAlt P U hU) (cechCochainComplex P U) where
  hom := cechAltInclusion P U hU
  inv :=
    CochainComplex.ofHom
      (fun p => AddCommGrpCat.ofHom
        ((Alternating.cechCompAlt P U p).comp (Alternating.cechProj P U p)))
      (fun p => by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro s
        apply Subtype.ext
        simp only [cechCochainComplexAlt_d, cechCochainComplex_d, cechDifferentialAlt]
        exact (cechComp_cechProj_comp_cechDiff P U hU p s).symm)
  homotopyHomInvId := Homotopy.ofEq (by
    apply HomologicalComplex.Hom.ext
    funext p
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    apply Subtype.ext
    exact Alternating.cechComp_cechProj_of_isAlt P U s.1 s.2)
  homotopyInvHomId := by
    convert cechComparisonProjectionHomotopy P U hU using 1
    apply HomologicalComplex.Hom.ext
    funext p
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    rfl

/-- **[Stacks, Tag 01FM] for a family in an arbitrary category**, in the `homotopyEquivalences`
morphism-property spelling. -/
@[stacks 01FM "the canonical inclusion lies in homotopyEquivalences"]
theorem cechAltInclusion_homotopyEquivalence (hU : ∀ i, IsSubterminal (U i)) :
    (HomologicalComplex.homotopyEquivalences AddCommGrpCat.{max w w'} (ComplexShape.up ℕ))
      (cechAltInclusion P U hU) :=
  (cechAltInclusionHomotopyEquiv P U hU).homotopyEquivalences_hom

/-! ### The ordered Čech complex -/

/-- The ordered Čech cochain complex of the family: the components at strictly increasing
tuples only.  It needs no hypothesis on the family. -/
@[implicit_reducible, ega "III 6.6.4"]
def cechCochainComplexOrd : CochainComplex AddCommGrpCat.{max w w'} ℕ :=
  CochainComplex.of
    (fun p => AddCommGrpCat.of (Alternating.CechCochainOrd P U p))
    (fun p => AddCommGrpCat.ofHom (Alternating.cechDiffOrd P U p))
    (fun p => by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      exact DFunLike.congr_fun (Alternating.cechDiffOrd_comp_cechDiffOrd P U p))

/-- The degree-`p` object of the ordered Čech cochain complex. -/
@[simp]
theorem cechCochainComplexOrd_X (p : ℕ) :
    (cechCochainComplexOrd P U).X p = AddCommGrpCat.of (Alternating.CechCochainOrd P U p) := by
  simp [cechCochainComplexOrd]

/-- The differential of the ordered Čech cochain complex is `cechDiffOrd`. -/
@[simp]
theorem cechCochainComplexOrd_d (p : ℕ) :
    (cechCochainComplexOrd P U).d p (p + 1) = AddCommGrpCat.ofHom (Alternating.cechDiffOrd P U p) :=
  CochainComplex.of_d
    (fun p => AddCommGrpCat.of (Alternating.CechCochainOrd P U p))
    (fun p => AddCommGrpCat.ofHom (Alternating.cechDiffOrd P U p)) p

/-- **[Stacks, Tag 01FK] (2) as an isomorphism of complexes.**  The projection `π` from the
alternating to the ordered Čech cochains is an isomorphism of complexes. -/
@[stacks 01FK "(2) as an isomorphism of complexes"]
def cechProjAltComplexIso (hU : ∀ i, IsSubterminal (U i)) :
    cechCochainComplexAlt P U hU ≅ cechCochainComplexOrd P U :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (Alternating.cechProjAltEquiv P U p).toAddCommGrpIso)
    (fun i j hij => by
      obtain rfl : j = i + 1 := hij.symm
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro s
      simp only [cechCochainComplexAlt_d, cechCochainComplexOrd_d, cechDifferentialAlt]
      rfl)

/-- **The ordered Čech complex is homotopy equivalent to the full Čech complex.**  The
isomorphism of complexes `π : C^•_alt ≅ C^•_ord` of [Stacks, Tag 01FK] (2), composed with the
homotopy equivalence of [Stacks, Tag 01FM].  The ordered complex is the one indexing the double
complex of [Stacks, Tag 07MN]. -/
def cechOrdHomotopyEquiv (hU : ∀ i, IsSubterminal (U i)) :
    HomotopyEquiv (cechCochainComplexOrd P U) (cechCochainComplex P U) :=
  (HomotopyEquiv.ofIso (cechProjAltComplexIso P U hU).symm).trans
    (cechAltInclusionHomotopyEquiv P U hU)

/-- **The ordered Čech complex has the cohomology of the full Čech complex, in every degree.**
It is induced by the homotopy equivalence `cechOrdHomotopyEquiv`. -/
def cechCochainComplexOrdHomologyIso (hU : ∀ i, IsSubterminal (U i)) (j : ℕ)
    [(cechCochainComplexOrd P U).HasHomology j]
    [(cechCochainComplex P U).HasHomology j] :
    (cechCochainComplexOrd P U).homology j ≅ (cechCochainComplex P U).homology j :=
  (cechOrdHomotopyEquiv P U hU).toHomologyIso j

end

end Stacks.CategoryTheory.CechComplex.Alternating

end
