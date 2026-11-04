module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Topology.Sheaves.Flasque
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.CechComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.CechVanishingCriteria.OnABasisDegreeOne

/-!
# Čech acyclicity of flasque sheaves

A flasque sheaf of abelian groups on a topological space has vanishing Čech cohomology in
every positive degree, for every family of open subsets.

## Main definitions

* `shrink P Z` is the presheaf `W ↦ P(W ⊓ Z)`, so that the Čech complex of a family `U` with
  coefficients in `shrink P Z` is the Čech complex of `U` *relative to* the open `Z`;
  `RelCochain U P q Z` is a degree-`q` cochain of that complex, `rcomp` takes its components,
  `rmk` builds a cochain from prescribed components and `rd` is its differential.
* `part U A` is the union of the members of `U` indexed by a subset `A` of the index set, and
  `PartialPrimitive U F Z e` is a primitive of the relative cocycle `e` defined over the part
  of `Z` covered by such a subset.
* `Vanishing U F Cls q` says that relative cocycles of degree `q + 1` are coboundaries over
  every open in the class `Cls`, and `CocycleExt U F Cls q` says that relative cocycles of
  degree `q` extend from a smaller open of the class to a larger one.
* `Extends U F Cls` is the extension property of sections of `F` that the induction actually
  consumes: the two conjuncts are exactly the two restrictions at which flasqueness is used.

## Main results

* `isZero_cechComplex_homology_of_isFlasque` is Stacks Tag 09SZ: the positive-degree homology
  of the Čech complex of a flasque sheaf of abelian groups vanishes.
* `vanishing` is the same statement for the relative Čech complexes, in element form, from
  `Extends U F Cls` rather than from flasqueness, and `vanishing_of_cocycleExt`,
  `cocycleExt_zero` and `cocycleExt_succ` are the three steps of its proof;
  `vanishing_isFlasque` is its flasque instance, at the trivial class.
* `extends_of_isFlasque` says a flasque sheaf has the extension property for every class.
* `res_rcomp_of_rd_eq_zero` is the cocycle identity, the source of the local primitives.

## Implementation notes

The proof is the classical dimension-shifting argument of Godement, carried out at the level of
cochains so that it needs no injective resolutions, no quotient sheaves and no Čech-to-derived
spectral sequence: the index type of the family and the coefficients live in a universe
unrelated to that of the space, where injective resolutions and the Godement resolution are not
available.

Two statements are proved together by induction on the degree. `Vanishing U F Cls q` says that a
relative cocycle of degree `q + 1` is a coboundary; `CocycleExt U F Cls q` says that a relative
cocycle of degree `q` over a smaller open is the restriction of one over a larger open.
`CocycleExt U F Cls 0` is gluing followed by one extension of a section, and `CocycleExt U F Cls
(q + 1)` follows from `Vanishing U F Cls q` by writing the cocycle as a coboundary, extending its
primitive componentwise — no cocycle condition is needed of the extension — and taking the
coboundary again, which is a cocycle because the Čech differential squares to zero.
`Vanishing U F Cls q` follows from `CocycleExt U F Cls q` by Zorn's lemma applied to the partial
primitives: a chain of them glues, and a maximal one is defined over every member of the
family, because over `U α` the cocycle identity produces a primitive whose difference with the
given one is a cocycle of degree `q` on the overlap, which `CocycleExt U F Cls q` extends, after
which the corrected primitives glue.

The relative open is restricted to a class `Cls` because the induction is also the engine of
Stacks 0A36, whose hypothesis gives surjective restrictions only onto the unions of finite
intersections of the members of `U`; the Zorn step needs the class closed under meeting with a
member `U α` and with a `part U A`, which are the two hypotheses `hinf` and `hpart` of
`vanishing`. Flasqueness gives `Extends U F Cls` for every class, so Tag 09SZ itself is the
instance at the class `fun _ => True`, where both closure hypotheses are trivial.

Relative cochains are elements of Mathlib's `cechComplexFunctor` applied to `shrink F.obj Z`;
in this way the differential, its square being zero, and the degreewise description of the
complex are all inherited rather than reproved, while the components of a relative cochain are
*literally* sections of `F` over the opens `inter U y ⊓ Z`. Sections are handled through
`Stacks.Cohomology.Basis.res`, which makes every inclusion of opens appear as a proof argument
and hence irrelevant; equalities of opens therefore need no `eqToHom`. Gluing and separatedness
are taken from `StacksDraft.Ch20.Sec11.Tag01EW`, whose statements carry no universe restriction
on the indexing type of the cover.

The hypothesis that `U` covers `V` is not used: the Čech complex of `U` is built from the
intersections of the members of `U`, and `V` occurs nowhere in it. The statement is the one of
the tag, so the hypothesis is kept.

## References

* [Stacks Project, Tag 09SZ](https://stacks.math.columbia.edu/tag/09SZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex
open Stacks.Cohomology.Basis (res res_id res_res res_sub res_app res_add res_sum
  res_zsmul eq_of_res_eq
  exists_res_eq_of_compatible ofElt ofElt_apply ofElt_comp hom_sum_apply eq_of_ofElt)

universe u v

namespace Stacks.Cohomology.FlasqueCech

noncomputable section

variable {X : TopCat.{u}} {ι : Type v} (U : ι → Opens X)

/-! ### Intersections of the members of a family -/

/-- The intersection selected by a tuple is contained in each of the members it selects. -/
theorem inter_le {m : ℕ} (x : Fin m → ι) (a : Fin m) : inter U x ≤ U (x a) :=
  leOfHom (interπ U x a)

/-- An open contained in every member selected by a tuple is contained in the intersection. -/
theorem le_inter {m : ℕ} {x : Fin m → ι} {W : Opens X} (h : ∀ a, W ≤ U (x a)) :
    W ≤ inter U x := by
  rw [inter_eq_iInf]
  exact le_iInf h

/-- Reindexing a tuple enlarges the intersection it selects. -/
theorem inter_le_inter {m m' : ℕ} (x : Fin m → ι) (h : Fin m' → Fin m) :
    inter U x ≤ inter U (x ∘ h) :=
  le_inter U fun a => inter_le U x (h a)

/-- The intersection selected by a nonempty tuple is contained in the union of the family. -/
theorem inter_le_iSup {m : ℕ} (x : Fin (m + 1) → ι) : inter U x ≤ ⨆ i, U i :=
  (inter_le U x 0).trans (le_iSup U (x 0))

/-- Prefixing an index to a tuple intersects the selected open with the corresponding member. -/
theorem inter_cons_le {m : ℕ} (i : ι) (y : Fin m → ι) :
    inter U (Fin.cons i y) ≤ inter U y ⊓ U i := by
  refine le_inf (le_inter U fun a => ?_) ?_
  · simpa using inter_le U (Fin.cons i y) a.succ
  · simpa using inter_le U (Fin.cons i y) 0

/-- Prefixing an index to a tuple intersects the selected open with the corresponding member. -/
theorem le_inter_cons {m : ℕ} (i : ι) (y : Fin m → ι) :
    inter U y ⊓ U i ≤ inter U (Fin.cons i y) := by
  refine le_inter U fun a => ?_
  induction a using Fin.cases with
  | zero => simp
  | succ b => simpa using inf_le_left.trans (inter_le U y b)

/-- Prefixing an index to a tuple and then deleting the prefixed entry gives the tuple back. -/
theorem cons_comp_zero_succAbove {m : ℕ} (i : ι) (x : Fin (m + 1) → ι) :
    (Fin.cons i x : Fin (m + 2) → ι) ∘ (0 : Fin (m + 2)).succAbove = x := by
  funext c
  simp

/-- Prefixing an index commutes with deleting an entry. -/
theorem cons_comp_succ_succAbove {m : ℕ} (i : ι) (x : Fin (m + 1) → ι) (a : Fin (m + 1)) :
    (Fin.cons i x : Fin (m + 2) → ι) ∘ (a.succ).succAbove = Fin.cons i (x ∘ a.succAbove) := by
  funext c
  induction c using Fin.cases with
  | zero => simp
  | succ b => simp

/-- The tuple of length one with value `i`. -/
def single (i : ι) : Fin 1 → ι := fun _ => i

/-- The only entry of `single i` is `i`. -/
@[simp]
theorem single_apply (i : ι) (a : Fin 1) : single i a = i := rfl

/-- A tuple of length one is the constant tuple at its only entry. -/
theorem eq_single (x : Fin 1 → ι) : x = single (x 0) :=
  funext fun c => by rw [Fin.eq_zero c]; rfl

/-- Prefixing an index to the empty tuple gives the constant tuple of length one. -/
theorem cons_comp_eq_single (i : ι) (x : Fin 1 → ι) :
    Fin.cons i (x ∘ (0 : Fin 1).succAbove) = single i :=
  funext fun c => by rw [Fin.eq_zero c]; rfl

/-- Prefixing an index to a tuple and to one of its faces: the intersection selected by the
former is contained in the intersection selected by the latter. -/
theorem inter_cons_le_cons {m : ℕ} (i : ι) (x : Fin (m + 1) → ι) (a : Fin (m + 1)) :
    inter U (Fin.cons i x) ≤ inter U (Fin.cons i (x ∘ a.succAbove)) := by
  rw [← cons_comp_succ_succAbove i x a]
  exact inter_le_inter U _ _

/-! ### The presheaf of sections over the intersection with a fixed open -/

variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v})

/-- The presheaf `W ↦ P(W ⊓ Z)`, the pushforward of the restriction of `P` to the open `Z`.
Its sections over `W` are *literally* the sections of `P` over `W ⊓ Z`; the definition is
reducible so that this coincidence is seen by rewriting and by instance search. -/
@[reducible]
def shrink (Z : Opens X) : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v} where
  obj W := P.obj (op (W.unop ⊓ Z))
  map f := P.map (homOfLE (inf_le_inf_right Z (leOfHom f.unop))).op
  map_id _ := P.map_id _
  map_comp _ _ := by
    rw [← P.map_comp]
    exact congrArg P.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

/-! ### Relative Čech cochains -/

/-- The Čech cochain complex of the family `U` with coefficients in `shrink P Z`: its degree-`q`
term is the product, over the tuples `y`, of the sections of `P` over `inter U y ⊓ Z`. -/
abbrev relComplex (Z : Opens X) : CochainComplex AddCommGrpCat.{v} ℕ :=
  (cechComplexFunctor U).obj (shrink P Z)

/-- A degree-`q` Čech cochain of `P` for the family `U`, relative to the open `Z`. -/
abbrev RelCochain (q : ℕ) (Z : Opens X) : Type v := ToType ((relComplex U P Z).X q)

variable {U P}

/-- The component of a relative cochain at a tuple: a section of `P` over `inter U y ⊓ Z`. -/
def rcomp {q : ℕ} {Z : Opens X} (s : RelCochain U P q Z) (y : Fin (q + 1) → ι) :
    ToType (P.obj (op (inter U y ⊓ Z))) :=
  ConcreteCategory.hom (π U (shrink P Z) q y) s

/-- The relative cochain with prescribed components. -/
def rmk {q : ℕ} {Z : Opens X}
    (f : ∀ y : Fin (q + 1) → ι, ToType (P.obj (op (inter U y ⊓ Z)))) : RelCochain U P q Z :=
  ConcreteCategory.hom (lift U (shrink P Z) fun y => ofElt (f y)) (ULift.up 1)

/-- The components of `rmk` are the prescribed sections. -/
@[simp]
theorem rcomp_rmk {q : ℕ} {Z : Opens X}
    (f : ∀ y : Fin (q + 1) → ι, ToType (P.obj (op (inter U y ⊓ Z)))) (y : Fin (q + 1) → ι) :
    rcomp (rmk f) y = f y := by
  rw [rcomp, rmk, ← ConcreteCategory.comp_apply, lift_comp_π, ofElt_apply]

/-- A relative cochain is determined by its components. -/
theorem rcochain_ext {q : ℕ} {Z : Opens X} (s t : RelCochain U P q Z)
    (h : ∀ y, rcomp s y = rcomp t y) : s = t :=
  eq_of_ofElt (hom_ext U (shrink P Z) fun y => by
    rw [ofElt_comp, ofElt_comp]
    exact congrArg ofElt (h y))

/-- Taking components is additive. -/
@[simp]
theorem rcomp_add {q : ℕ} {Z : Opens X} (s t : RelCochain U P q Z) (y : Fin (q + 1) → ι) :
    rcomp (s + t) y = rcomp s y + rcomp t y := map_add _ _ _

/-- Taking components kills the zero cochain. -/
@[simp]
theorem rcomp_zero {q : ℕ} {Z : Opens X} (y : Fin (q + 1) → ι) :
    rcomp (0 : RelCochain U P q Z) y = 0 := map_zero _

/-- The relative Čech differential. -/
def rd {q : ℕ} {Z : Opens X} (s : RelCochain U P q Z) : RelCochain U P (q + 1) Z :=
  ConcreteCategory.hom ((relComplex U P Z).d q (q + 1)) s

/-- **The relative Čech differential, componentwise.** It is the alternating sum of the
restrictions along the face maps of the tuple. -/
theorem rcomp_rd {q : ℕ} {Z : Opens X} (s : RelCochain U P q Z) (x : Fin (q + 2) → ι) :
    rcomp (rd s) x = ∑ a : Fin (q + 2), (-1 : ℤ) ^ (a : ℕ) •
      res P (inf_le_inf_right Z (inter_le_inter U x a.succAbove)) (rcomp s (x ∘ a.succAbove)) := by
  rw [rd, rcomp, ← ConcreteCategory.comp_apply, d_comp_π, hom_sum_apply]
  exact Finset.sum_congr rfl fun a _ => rfl

/-- The relative Čech differential is additive. -/
@[simp]
theorem rd_add {q : ℕ} {Z : Opens X} (s t : RelCochain U P q Z) : rd (s + t) = rd s + rd t :=
  map_add _ _ _

/-- The relative Čech differential squares to zero. -/
theorem rd_rd {q : ℕ} {Z : Opens X} (s : RelCochain U P q Z) : rd (rd s) = 0 := by
  rw [rd, rd, ← ConcreteCategory.comp_apply, HomologicalComplex.d_comp_d]
  rfl

/-! ### The cocycle identity -/

/-- Components of a relative cochain at equal tuples, restricted to a common open, agree. -/
theorem res_rcomp_congr {q : ℕ} {Z W : Opens X} (s : RelCochain U P q Z)
    {y y' : Fin (q + 1) → ι} (hyy' : y = y') (hy : W ≤ inter U y ⊓ Z)
    (hy' : W ≤ inter U y' ⊓ Z) : res P hy (rcomp s y) = res P hy' (rcomp s y') := by
  subst hyy'
  rfl

/-- **The cocycle identity.** If `s` is a relative Čech cocycle of degree `q`, then over the
intersection selected by the tuple `x` with an index `i` prefixed, the component of `s` at `x`
is the alternating sum of its components at the tuples obtained by prefixing `i` to the faces
of `x`. -/
theorem res_rcomp_of_rd_eq_zero {q : ℕ} {Z : Opens X} {s : RelCochain U P q Z} (hs : rd s = 0)
    (i : ι) (x : Fin (q + 1) → ι) :
    res P (inf_le_inf_right Z ((inter_cons_le U i x).trans inf_le_left)) (rcomp s x) =
      ∑ a : Fin (q + 1), (-1 : ℤ) ^ (a : ℕ) • res P (inf_le_inf_right Z
        (inter_cons_le_cons U i x a)) (rcomp s (Fin.cons i (x ∘ a.succAbove))) := by
  have h0 : rcomp (rd s) (Fin.cons i x) = 0 := by rw [hs, rcomp_zero]
  rw [rcomp_rd, Fin.sum_univ_succ] at h0
  have c1 : (-1 : ℤ) ^ (((0 : Fin (q + 2))) : ℕ) • res P
      (inf_le_inf_right Z (inter_le_inter U (Fin.cons i x) (0 : Fin (q + 2)).succAbove))
      (rcomp s ((Fin.cons i x) ∘ (0 : Fin (q + 2)).succAbove)) =
      res P (inf_le_inf_right Z ((inter_cons_le U i x).trans inf_le_left)) (rcomp s x) := by
    rw [res_rcomp_congr s (cons_comp_zero_succAbove i x) _
      (inf_le_inf_right Z ((inter_cons_le U i x).trans inf_le_left))]
    simp
  have c2 : ∀ a : Fin (q + 1), (-1 : ℤ) ^ ((a.succ : Fin (q + 2)) : ℕ) • res P
      (inf_le_inf_right Z (inter_le_inter U (Fin.cons i x) (a.succ).succAbove))
      (rcomp s ((Fin.cons i x) ∘ (a.succ).succAbove)) =
      -((-1 : ℤ) ^ (a : ℕ) • res P (inf_le_inf_right Z (inter_cons_le_cons U i x a))
        (rcomp s (Fin.cons i (x ∘ a.succAbove)))) := by
    intro a
    rw [res_rcomp_congr s (cons_comp_succ_succAbove i x a) _
      (inf_le_inf_right Z (inter_cons_le_cons U i x a)), Fin.val_succ, pow_succ]
    simp
  rw [c1, Finset.sum_congr rfl fun a _ => c2 a, Finset.sum_neg_distrib] at h0
  exact sub_eq_zero.mp (by rw [sub_eq_add_neg]; exact h0)

/-! ### Flasque sheaves and the two inductive properties -/

variable (U) (F : TopCat.Sheaf AddCommGrpCat.{v} X)

/-- **Separatedness.** Two sections of `F` over an open that agree on the members of a cover of
it are equal. This is the form of `Stacks.Cohomology.Basis.eq_of_res_eq` used below. -/
theorem eq_of_res_eq' {κ : Type*} (V : κ → Opens X) {W : Opens X} (hle : ∀ j, V j ≤ W)
    (hsup : W ≤ ⨆ j, V j) (s t : ToType (F.obj.obj (op W)))
    (h : ∀ j, res F.obj (hle j) s = res F.obj (hle j) t) : s = t :=
  eq_of_res_eq F V hle hsup s t h

/-- **Gluing.** A compatible family of sections of `F` over the members of a cover glues. This is
the form of `Stacks.Cohomology.Basis.exists_res_eq_of_compatible` used below. -/
theorem exists_res_eq_of_compatible' {κ : Type*} (V : κ → Opens X) {W : Opens X}
    (hle : ∀ j, V j ≤ W) (hsup : W ≤ ⨆ j, V j) (sf : ∀ j, ToType (F.obj.obj (op (V j))))
    (hc : ∀ (j k : κ) (Y : Opens X) (h₁ : Y ≤ V j) (h₂ : Y ≤ V k),
      res F.obj h₁ (sf j) = res F.obj h₂ (sf k)) :
    ∃ t : ToType (F.obj.obj (op W)), ∀ j, res F.obj (hle j) t = sf j :=
  exists_res_eq_of_compatible F V hle hsup sf hc

/-- The sections of a flasque sheaf extend along any inclusion of opens. -/
theorem exists_res_eq [F.IsFlasque] {W W' : Opens X} (h : W' ≤ W)
    (s : ToType (F.obj.obj (op W'))) : ∃ t : ToType (F.obj.obj (op W)), res F.obj h t = s := by
  have hepi : Epi (F.obj.map (homOfLE h).op) := inferInstance
  exact (AddCommGrpCat.epi_iff_surjective (F.obj.map (homOfLE h).op)).1 hepi s

/-- `Extends U F Cls` asserts the two extension properties of sections of `F` that the induction
below consumes, for relative opens `Z` in the class `Cls`: a section over `inter U y ⊓ Z`, and a
section over `⨆ i, inter U (single i) ⊓ Z`, each extends along any inclusion of opens.

Flasqueness of `F` gives both, for every class (`extends_of_isFlasque`). The point of isolating
exactly these two is that they also follow from surjectivity of the restriction maps of `F` onto
the *unions of finite intersections* of the members of `U` alone, which is the hypothesis of
Stacks 0A36; the two opens above are of that shape when `Z` is. -/
def Extends (Cls : Opens X → Prop) : Prop :=
  (∀ (Z Z' : Opens X), Cls Z → Cls Z' → ∀ {m : ℕ} (y : Fin (m + 1) → ι)
      (h : inter U y ⊓ Z' ≤ inter U y ⊓ Z) (s : ToType (F.obj.obj (op (inter U y ⊓ Z')))),
      ∃ t : ToType (F.obj.obj (op (inter U y ⊓ Z))), res F.obj h t = s) ∧
    ∀ (Z Z' : Opens X), Cls Z → Cls Z' →
      ∀ (h : (⨆ i, inter U (single i) ⊓ Z') ≤ (⨆ i, U i) ⊓ Z)
      (s : ToType (F.obj.obj (op (⨆ i, inter U (single i) ⊓ Z')))),
      ∃ t : ToType (F.obj.obj (op ((⨆ i, U i) ⊓ Z))), res F.obj h t = s

/-- A flasque sheaf has both extension properties, for every class of relative opens. -/
theorem extends_of_isFlasque [F.IsFlasque] (Cls : Opens X → Prop) : Extends U F Cls := by
  constructor
  · intro _ _ _ _ _ _ h s
    exact exists_res_eq F h s
  · intro _ _ _ _ h s
    exact exists_res_eq F h s

/-- `Vanishing U F Cls q` asserts that, over every open subset in the class `Cls`, every relative
Čech cocycle of degree `q + 1` for the family `U` with coefficients in `F` is a relative
coboundary. -/
def Vanishing (Cls : Opens X → Prop) (q : ℕ) : Prop :=
  ∀ (Z : Opens X), Cls Z → ∀ (e : RelCochain U F.obj (q + 1) Z), rd e = 0 →
    ∃ b : RelCochain U F.obj q Z, rd b = e

/-- `CocycleExt U F Cls q` asserts that every relative Čech cocycle of degree `q` over an open
subset `Z'` in the class `Cls` is the restriction of a relative Čech cocycle of degree `q` over
any larger open subset `Z` in the class. -/
def CocycleExt (Cls : Opens X → Prop) (q : ℕ) : Prop :=
  ∀ (Z Z' : Opens X), Cls Z → Cls Z' → Z' ≤ Z → ∀ δ : RelCochain U F.obj q Z', rd δ = 0 →
    ∃ f : RelCochain U F.obj q Z, rd f = 0 ∧
      ∀ (y : Fin (q + 1) → ι) (hy : inter U y ⊓ Z' ≤ inter U y ⊓ Z),
        res F.obj hy (rcomp f y) = rcomp δ y

/-- **The inductive step for cocycle extension.** If relative Čech cocycles of degree `q + 1`
are coboundaries over every open, then they extend from a smaller open to a larger one: write
the cocycle as a coboundary, extend the primitive componentwise using flasqueness — no cocycle
condition is required of it — and take the coboundary of the extension. -/
theorem cocycleExt_succ {Cls : Opens X → Prop} (hE : Extends U F Cls) {q : ℕ}
    (h : Vanishing U F Cls q) : CocycleExt U F Cls (q + 1) := by
  intro Z Z' hZcls hZ'cls hZ δ hδ
  obtain ⟨ρ, hρ⟩ := h Z' hZ'cls δ hδ
  choose ρ' hρ' using fun y : Fin (q + 1) → ι =>
    hE.1 Z Z' hZcls hZ'cls y (inf_le_inf_left (inter U y) hZ) (rcomp ρ y)
  refine ⟨rd (rmk ρ'), rd_rd _, fun y hy => ?_⟩
  have hδy : rcomp δ y = rcomp (rd ρ) y := by rw [hρ]
  rw [hδy, rcomp_rd, rcomp_rd, res_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [res_zsmul, rcomp_rmk, res_res, ← hρ' (y ∘ a.succAbove), res_res]

/-- **The base case for cocycle extension.** A relative Čech cocycle of degree `0` over `Z'` is
a compatible family of sections, so it glues to a section over the part of `Z'` covered by the
family; flasqueness extends that section to the corresponding part of `Z`, and the restrictions
of the extension are the required cocycle of degree `0` over `Z`. -/
theorem cocycleExt_zero {Cls : Opens X → Prop} (hE : Extends U F Cls) :
    CocycleExt U F Cls 0 := by
  intro Z Z' hZcls hZ'cls hZ δ hδ
  have hcompat : ∀ (j k : ι) (Y : Opens X) (h₁ : Y ≤ inter U (single j) ⊓ Z')
      (h₂ : Y ≤ inter U (single k) ⊓ Z'),
      res F.obj h₁ (rcomp δ (single j)) = res F.obj h₂ (rcomp δ (single k)) := by
    intro j k Y h₁ h₂
    have hj : Y ≤ U j := (h₁.trans inf_le_left).trans (inter_le U (single j) 0)
    have hk : Y ≤ U k := (h₂.trans inf_le_left).trans (inter_le U (single k) 0)
    have hY : Y ≤ inter U (Fin.cons k (single j)) ⊓ Z' := by
      refine le_inf (le_inter U fun a => ?_) (h₁.trans inf_le_right)
      induction a using Fin.cases with
      | zero => simpa using hk
      | succ b => simpa using hj
    calc res F.obj h₁ (rcomp δ (single j))
        = res F.obj hY (res F.obj (inf_le_inf_right Z'
            ((inter_cons_le U k (single j)).trans inf_le_left)) (rcomp δ (single j))) :=
          (res_res F.obj _ _ _).symm
      _ = res F.obj hY ((-1 : ℤ) ^ (((0 : Fin 1)) : ℕ) • res F.obj (inf_le_inf_right Z'
            (inter_cons_le_cons U k (single j) 0))
            (rcomp δ (Fin.cons k (single j ∘ (0 : Fin 1).succAbove)))) := by
          rw [res_rcomp_of_rd_eq_zero hδ k (single j), Fin.sum_univ_one]
      _ = res F.obj h₂ (rcomp δ (single k)) := by
          rw [show ((-1 : ℤ) ^ (((0 : Fin 1)) : ℕ)) = 1 by simp, one_zsmul, res_res,
            res_rcomp_congr δ (cons_comp_eq_single k (single j)) _ h₂]
  obtain ⟨σ, hσ⟩ := exists_res_eq_of_compatible' F (fun i => inter U (single i) ⊓ Z')
    (fun i => le_iSup (fun i' => inter U (single i') ⊓ Z') i) le_rfl
    (fun i => rcomp δ (single i)) hcompat
  have hsuple : (⨆ i, (inter U (single i) ⊓ Z')) ≤ (⨆ i, U i) ⊓ Z := by
    refine iSup_le fun i => le_inf ?_ (inf_le_right.trans hZ)
    exact (inf_le_left.trans (inter_le U (single i) 0)).trans (le_iSup U i)
  obtain ⟨σ', hσ'⟩ := hE.2 Z Z' hZcls hZ'cls hsuple σ
  refine ⟨rmk fun y => res F.obj (inf_le_inf_right Z (inter_le_iSup U y)) σ', ?_, ?_⟩
  · refine rcochain_ext _ _ fun x => ?_
    rw [rcomp_rd, rcomp_zero, Fin.sum_univ_two, rcomp_rmk, rcomp_rmk, res_res, res_res]
    simp
  · intro y hy
    have hy0' : inter U y ⊓ Z' ≤ inter U (single (y 0)) ⊓ Z' :=
      inf_le_inf_right Z' (le_of_eq (congrArg (inter U) (eq_single y)))
    have e1 : rcomp δ y = res F.obj hy0' (rcomp δ (single (y 0))) :=
      (res_id F.obj (rcomp δ y)).symm.trans (res_rcomp_congr δ (eq_single y) (le_refl _) hy0')
    rw [rcomp_rmk, res_res, e1, ← hσ (y 0), res_res, ← hσ', res_res]

/-! ### Tools for the main induction -/

/-- The coboundary of a relative cochain, restricted to an open contained in all the relevant
intersections: the alternating sum of the restrictions of the components. -/
theorem res_rcomp_rd {q : ℕ} {Z W : Opens X} (s : RelCochain U F.obj q Z)
    (x : Fin (q + 2) → ι) (hW : W ≤ inter U x ⊓ Z)
    (hWa : ∀ a : Fin (q + 2), W ≤ inter U (x ∘ a.succAbove) ⊓ Z) :
    res F.obj hW (rcomp (rd s) x) =
      ∑ a : Fin (q + 2), (-1 : ℤ) ^ (a : ℕ) • res F.obj (hWa a) (rcomp s (x ∘ a.succAbove)) := by
  rw [rcomp_rd, res_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [res_zsmul, res_res]

/-- The two-element family of opens with values `W₁` and `W₂`. -/
def pair (W₁ W₂ : Opens X) : Fin 2 → Opens X := Fin.cons W₁ fun _ => W₂

/-- The first member of `pair W₁ W₂`. -/
@[simp]
theorem pair_zero (W₁ W₂ : Opens X) : pair W₁ W₂ 0 = W₁ := rfl

/-- The second member of `pair W₁ W₂`. -/
@[simp]
theorem pair_one (W₁ W₂ : Opens X) : pair W₁ W₂ 1 = W₂ := rfl

/-- The members of `pair W₁ W₂` are contained in any open containing both. -/
theorem pair_le {W W₁ W₂ : Opens X} (h₁ : W₁ ≤ W) (h₂ : W₂ ≤ W) (j : Fin 2) :
    pair W₁ W₂ j ≤ W := by
  induction j using Fin.cases with
  | zero => exact h₁
  | succ b => exact h₂

/-- An open contained in the union of two opens is contained in the union of `pair`. -/
theorem le_iSup_pair {W W₁ W₂ : Opens X} (hW : W ≤ W₁ ⊔ W₂) : W ≤ ⨆ j, pair W₁ W₂ j := by
  refine hW.trans (sup_le ?_ ?_)
  · exact le_iSup_of_le 0 (by rw [pair_zero])
  · exact le_iSup_of_le 1 (by rw [pair_one])

/-- **Separatedness for a cover by two opens.** -/
theorem eq_of_res_eq_pair {W W₁ W₂ : Opens X} (h₁ : W₁ ≤ W) (h₂ : W₂ ≤ W) (hW : W ≤ W₁ ⊔ W₂)
    (s t : ToType (F.obj.obj (op W))) (e₁ : res F.obj h₁ s = res F.obj h₁ t)
    (e₂ : res F.obj h₂ s = res F.obj h₂ t) : s = t := by
  refine eq_of_res_eq' F (pair W₁ W₂) (pair_le h₁ h₂) (le_iSup_pair hW) s t fun j => ?_
  induction j using Fin.cases with
  | zero => exact e₁
  | succ b => exact e₂

/-- **Gluing for a cover by two opens.** -/
theorem exists_res_eq_pair {W W₁ W₂ : Opens X} (h₁ : W₁ ≤ W) (h₂ : W₂ ≤ W) (hW : W ≤ W₁ ⊔ W₂)
    (s₁ : ToType (F.obj.obj (op W₁))) (s₂ : ToType (F.obj.obj (op W₂)))
    (hc : ∀ (Y : Opens X) (k₁ : Y ≤ W₁) (k₂ : Y ≤ W₂), res F.obj k₁ s₁ = res F.obj k₂ s₂) :
    ∃ t : ToType (F.obj.obj (op W)), res F.obj h₁ t = s₁ ∧ res F.obj h₂ t = s₂ := by
  obtain ⟨t, ht⟩ := exists_res_eq_of_compatible' F (pair W₁ W₂) (pair_le h₁ h₂)
    (le_iSup_pair hW)
    (Fin.cases (motive := fun j => ToType (F.obj.obj (op (pair W₁ W₂ j)))) s₁ fun _ => s₂)
    (fun j k Y k₁ k₂ => by
      induction j using Fin.cases with
      | zero =>
        induction k using Fin.cases with
        | zero => rfl
        | succ b => exact hc Y k₁ k₂
      | succ b =>
        induction k using Fin.cases with
        | zero => exact (hc Y k₂ k₁).symm
        | succ b' => rfl)
  exact ⟨t, ht 0, ht 1⟩

/-- The union of the members of the family indexed by a subset of the index set. -/
def part (A : Set ι) : Opens X := ⨆ i ∈ A, U i

/-- A member indexed by an element of the subset is contained in the union. -/
theorem le_part {A : Set ι} {i : ι} (hi : i ∈ A) : U i ≤ part U A :=
  le_iSup_of_le i (le_iSup_of_le hi (le_refl _))

/-- The union over a subset is monotone in the subset. -/
theorem part_mono {A A' : Set ι} (h : A ⊆ A') : part U A ≤ part U A' :=
  iSup₂_le fun _i hi => le_part U (h hi)

/-- The union over the whole index set is the union of the family. -/
theorem part_univ : part U Set.univ = ⨆ i, U i := by
  simp [part]

/-- The union over a subset with one more element. -/
theorem part_insert (A : Set ι) (α : ι) : part U (insert α A) = U α ⊔ part U A :=
  show (⨆ i ∈ insert α A, U i) = U α ⊔ ⨆ i ∈ A, U i from iSup_insert

/-- Enlarging the subset enlarges the relative open cut out by the part of the family. -/
private theorem inter_inf_part_le {A A' : Set ι} (h : A ⊆ A') {m : ℕ} (y : Fin m → ι)
    {Z : Opens X} : inter U y ⊓ (Z ⊓ part U A) ≤ inter U y ⊓ (Z ⊓ part U A') :=
  inf_le_inf_left _ (inf_le_inf_left _ (part_mono U h))

/-- If the components of a relative cochain `s` are restrictions of the components of `t`, then
the components of the coboundary of `s` are restrictions of those of the coboundary of `t`. -/
theorem res_rcomp_rd_of_res_eq {q : ℕ} {Z Z' : Opens X} (s : RelCochain U F.obj q Z')
    (t : RelCochain U F.obj q Z)
    (hle : ∀ {m : ℕ} (y : Fin (m + 1) → ι), inter U y ⊓ Z' ≤ inter U y ⊓ Z)
    (hres : ∀ y : Fin (q + 1) → ι, res F.obj (hle y) (rcomp t y) = rcomp s y)
    (x : Fin (q + 2) → ι) :
    res F.obj (hle x) (rcomp (rd t) x) = rcomp (rd s) x := by
  rw [res_rcomp_rd U F t x (hle x)
      fun a => (hle x).trans (inf_le_inf_right Z (inter_le_inter U x a.succAbove)), rcomp_rd]
  exact Finset.sum_congr rfl fun a _ => by rw [← hres (x ∘ a.succAbove), res_res]

/-! ### Partial primitives -/

/-- A partial primitive of a relative Čech cocycle `e` of degree `q + 1`: a relative cochain of
degree `q`, living over the part of `Z` covered by a subset of the index set, whose coboundary
is the restriction of `e` there. -/
structure PartialPrimitive {q : ℕ} (Z : Opens X) (e : RelCochain U F.obj (q + 1) Z) where
  /-- The subset of the index set over which the partial primitive is defined. -/
  support : Set ι
  /-- The partial primitive itself. -/
  val : RelCochain U F.obj q (Z ⊓ part U support)
  /-- Its coboundary is the restriction of `e`. -/
  isPrimitive : ∀ (x : Fin (q + 2) → ι)
    (hx : inter U x ⊓ (Z ⊓ part U support) ≤ inter U x ⊓ Z),
    rcomp (rd val) x = res F.obj hx (rcomp e x)

/-- One partial primitive extends another: its support is larger, and its components restrict to
those of the other one. -/
def PartialPrimitive.Le {q : ℕ} {Z : Opens X} {e : RelCochain U F.obj (q + 1) Z}
    (d d' : PartialPrimitive U F Z e) : Prop :=
  d.support ⊆ d'.support ∧ ∀ (y : Fin (q + 1) → ι)
    (hy : inter U y ⊓ (Z ⊓ part U d.support) ≤ inter U y ⊓ (Z ⊓ part U d'.support)),
    res F.obj hy (rcomp d'.val y) = rcomp d.val y

/-- Extension of partial primitives is transitive. -/
theorem PartialPrimitive.le_trans {q : ℕ} {Z : Opens X} {e : RelCochain U F.obj (q + 1) Z}
    {a b d : PartialPrimitive U F Z e} (hab : PartialPrimitive.Le U F a b)
    (hbd : PartialPrimitive.Le U F b d) : PartialPrimitive.Le U F a d := by
  refine ⟨hab.1.trans hbd.1, fun y hy => ?_⟩
  rw [← hab.2 y (inter_inf_part_le U hab.1 y), ← hbd.2 y (inter_inf_part_le U hbd.1 y), res_res]

/-- **Chains of partial primitives are bounded.** Over a chain the supports increase and the
components form compatible families of sections over increasing opens, so they glue; the
resulting cochain is a primitive over the union of the supports because being one is a local
condition. -/
theorem PartialPrimitive.exists_ub {q : ℕ} {Z : Opens X} {e : RelCochain U F.obj (q + 1) Z}
    (c : Set (PartialPrimitive U F Z e))
    (hc : IsChain (fun d d' : PartialPrimitive U F Z e => PartialPrimitive.Le U F d d') c) :
    ∃ ub, ∀ a ∈ c, PartialPrimitive.Le U F a ub := by
  obtain ⟨A, hA⟩ : ∃ A : Set ι, ∀ i, i ∈ A ↔ ∃ d ∈ c, i ∈ d.support :=
    ⟨{i | ∃ d ∈ c, i ∈ d.support}, fun _ => Iff.rfl⟩
  have hsub : ∀ d : c, (d : PartialPrimitive U F Z e).support ⊆ A :=
    fun d _ hi => (hA _).2 ⟨d, d.2, hi⟩
  have hled : ∀ (d : c) {m : ℕ} (y : Fin (m + 1) → ι),
      inter U y ⊓ (Z ⊓ part U (d : PartialPrimitive U F Z e).support) ≤
        inter U y ⊓ (Z ⊓ part U A) := by
    intro d m y
    exact inter_inf_part_le U (hsub d) y
  have hcov : ∀ {m : ℕ} (y : Fin m → ι), inter U y ⊓ (Z ⊓ part U A) ≤
      ⨆ d : c, inter U y ⊓ (Z ⊓ part U (d : PartialPrimitive U F Z e).support) := by
    intro m y
    calc inter U y ⊓ (Z ⊓ part U A)
        ≤ inter U y ⊓ (Z ⊓ ⨆ d : c, part U (d : PartialPrimitive U F Z e).support) := by
          refine inf_le_inf_left _ (inf_le_inf_left _ (iSup₂_le fun i hi => ?_))
          obtain ⟨d, hd, hid⟩ := (hA i).1 hi
          exact (le_part U hid).trans
            (le_iSup (fun d : c => part U (d : PartialPrimitive U F Z e).support) ⟨d, hd⟩)
      _ = ⨆ d : c, inter U y ⊓ (Z ⊓ part U (d : PartialPrimitive U F Z e).support) := by
          rw [inf_iSup_eq, inf_iSup_eq]
  have hglue : ∀ y : Fin (q + 1) → ι,
      ∃ t : ToType (F.obj.obj (op (inter U y ⊓ (Z ⊓ part U A)))), ∀ (d : c)
        (hd : inter U y ⊓ (Z ⊓ part U (d : PartialPrimitive U F Z e).support) ≤
          inter U y ⊓ (Z ⊓ part U A)),
        res F.obj hd t = rcomp (d : PartialPrimitive U F Z e).val y := by
    intro y
    have hcompat : ∀ (d d' : c) (Y : Opens X)
        (k₁ : Y ≤ inter U y ⊓ (Z ⊓ part U (d : PartialPrimitive U F Z e).support))
        (k₂ : Y ≤ inter U y ⊓ (Z ⊓ part U (d' : PartialPrimitive U F Z e).support)),
        res F.obj k₁ (rcomp (d : PartialPrimitive U F Z e).val y) =
          res F.obj k₂ (rcomp (d' : PartialPrimitive U F Z e).val y) := by
      intro d d' Y k₁ k₂
      rcases eq_or_ne d d' with rfl | hne
      · rfl
      · rcases hc d.2 d'.2 (fun h => hne (Subtype.ext h)) with hdd | hdd <;>
          rw [← hdd.2 y (inter_inf_part_le U hdd.1 y), res_res]
    obtain ⟨t, ht⟩ := exists_res_eq_of_compatible' F
      (fun d : c => inter U y ⊓ (Z ⊓ part U (d : PartialPrimitive U F Z e).support))
      (fun d => hled d y) (hcov y)
      (fun d => rcomp (d : PartialPrimitive U F Z e).val y) hcompat
    exact ⟨t, fun d _ => ht d⟩
  choose val hval using hglue
  refine ⟨⟨A, rmk val, fun x hx => ?_⟩, fun a ha => ⟨fun _ hi => (hA _).2 ⟨a, ha, hi⟩,
    fun y hy => ?_⟩⟩
  · refine eq_of_res_eq' F
      (fun d : c => inter U x ⊓ (Z ⊓ part U (d : PartialPrimitive U F Z e).support))
      (fun d => hled d x) (hcov x) _ _ fun d => ?_
    rw [res_rcomp_rd_of_res_eq U F (d : PartialPrimitive U F Z e).val (rmk val) (hled d)
      (fun y => by rw [rcomp_rmk]; exact hval y d (hled d y)) x,
      (d : PartialPrimitive U F Z e).isPrimitive x (inf_le_inf_left _ inf_le_left), res_res]
  · rw [rcomp_rmk]
    exact hval y ⟨a, ha⟩ hy

/-! ### The Zorn step -/

/-- **The Zorn step.** If relative Čech cocycles of degree `q` extend from a smaller open to a
larger one, then every relative Čech cocycle `e` of degree `q + 1` is a coboundary over every
open. By Zorn's lemma there is a maximal partial primitive of `e`; it is defined over the whole
index set, because a partial primitive whose support misses an index `α` can be extended by
`α`: over `U α` the cocycle identity provides the primitive `c₀` with components
`e (α, y)`, the difference of the two primitives on the overlap is a cocycle of degree `q`,
extending that cocycle by hypothesis corrects `c₀` so that it agrees with the given primitive
on the overlap, and the two then glue. -/
theorem vanishing_of_cocycleExt {Cls : Opens X → Prop}
    (hinf : ∀ {Z : Opens X}, Cls Z → ∀ α : ι, Cls (Z ⊓ U α))
    (hpart : ∀ {Z : Opens X}, Cls Z → ∀ A : Set ι, Cls (Z ⊓ part U A))
    {q : ℕ} (hext : CocycleExt U F Cls q) : Vanishing U F Cls q := by
  intro Z hZcls e he
  obtain ⟨mx, hmx⟩ := exists_maximal_of_chains_bounded
    (r := fun d d' : PartialPrimitive U F Z e => PartialPrimitive.Le U F d d')
    (PartialPrimitive.exists_ub U F) fun hab hbd => PartialPrimitive.le_trans U F hab hbd
  have hfull : ∀ α : ι, α ∈ mx.support := by
    intro α
    have hcons : ∀ {m : ℕ} (y : Fin m → ι),
        inter U y ⊓ (Z ⊓ U α) ≤ inter U (Fin.cons α y) ⊓ Z := by
      intro m y
      exact le_inf ((inf_le_inf_left _ inf_le_right).trans (le_inter_cons U α y))
        (inf_le_right.trans inf_le_left)
    have hinter : ∀ {m : ℕ} (x : Fin (m + 1) → ι),
        inter U x ⊓ (Z ⊓ U α) ≤ inter U x ⊓ Z := fun x => inf_le_inf_left _ inf_le_left
    obtain ⟨c₀, hc₀⟩ : ∃ c₀ : RelCochain U F.obj q (Z ⊓ U α),
        ∀ y, rcomp c₀ y = res F.obj (hcons y) (rcomp e (Fin.cons α y)) :=
      ⟨rmk fun y => res F.obj (hcons y) (rcomp e (Fin.cons α y)), fun y => rcomp_rmk _ y⟩
    have hdc₀ : ∀ x : Fin (q + 2) → ι, rcomp (rd c₀) x = res F.obj (hinter x) (rcomp e x) := by
      intro x
      have hid := congrArg (res F.obj (hcons x)) (res_rcomp_of_rd_eq_zero he α x)
      rw [res_res, res_sum] at hid
      rw [rcomp_rd, hid]
      exact Finset.sum_congr rfl fun a _ => by rw [res_zsmul, res_res, hc₀, res_res]
    have h₁ : ∀ {m : ℕ} (y : Fin (m + 1) → ι),
        inter U y ⊓ (Z ⊓ part U mx.support ⊓ U α) ≤ inter U y ⊓ (Z ⊓ part U mx.support) :=
      fun y => inf_le_inf_left _ inf_le_left
    have h₂ : ∀ {m : ℕ} (y : Fin (m + 1) → ι),
        inter U y ⊓ (Z ⊓ part U mx.support ⊓ U α) ≤ inter U y ⊓ (Z ⊓ U α) :=
      fun y => inf_le_inf_left _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
    obtain ⟨δ, hδ⟩ : ∃ δ : RelCochain U F.obj q (Z ⊓ part U mx.support ⊓ U α),
        ∀ y, rcomp δ y = res F.obj (h₁ y) (rcomp mx.val y) - res F.obj (h₂ y) (rcomp c₀ y) :=
      ⟨rmk fun y => res F.obj (h₁ y) (rcomp mx.val y) - res F.obj (h₂ y) (rcomp c₀ y),
        fun y => rcomp_rmk _ y⟩
    have hδ0 : rd δ = 0 := by
      refine rcochain_ext _ _ fun x => ?_
      have hA₁ : ∀ a : Fin (q + 2), inter U x ⊓ (Z ⊓ part U mx.support ⊓ U α) ≤
          inter U (x ∘ a.succAbove) ⊓ (Z ⊓ part U mx.support) :=
        fun a => (inf_le_inf_right _ (inter_le_inter U x a.succAbove)).trans (h₁ _)
      have hA₂ : ∀ a : Fin (q + 2), inter U x ⊓ (Z ⊓ part U mx.support ⊓ U α) ≤
          inter U (x ∘ a.succAbove) ⊓ (Z ⊓ U α) :=
        fun a => (inf_le_inf_right _ (inter_le_inter U x a.succAbove)).trans (h₂ _)
      have key : ∀ a : Fin (q + 2), (-1 : ℤ) ^ (a : ℕ) •
          res F.obj (inf_le_inf_right (Z ⊓ part U mx.support ⊓ U α)
            (inter_le_inter U x a.succAbove)) (rcomp δ (x ∘ a.succAbove)) =
          (-1 : ℤ) ^ (a : ℕ) • res F.obj (hA₁ a) (rcomp mx.val (x ∘ a.succAbove)) -
            (-1 : ℤ) ^ (a : ℕ) • res F.obj (hA₂ a) (rcomp c₀ (x ∘ a.succAbove)) := by
        intro a
        rw [hδ, res_sub, res_res, res_res, smul_sub]
      rw [rcomp_zero, rcomp_rd, Finset.sum_congr rfl fun a _ => key a, Finset.sum_sub_distrib,
        ← res_rcomp_rd U F mx.val x (h₁ x) hA₁, ← res_rcomp_rd U F c₀ x (h₂ x) hA₂,
        mx.isPrimitive x (inf_le_inf_left _ inf_le_left), hdc₀ x, res_res, res_res, sub_self]
    obtain ⟨f, hf0, hfres⟩ := hext (Z ⊓ U α) (Z ⊓ part U mx.support ⊓ U α)
      (hinf hZcls α) (hinf (hpart hZcls mx.support) α)
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right) δ hδ0
    have hγ : ∀ y : Fin (q + 1) → ι,
        res F.obj (h₂ y) (rcomp (c₀ + f) y) = res F.obj (h₁ y) (rcomp mx.val y) := by
      intro y
      rw [rcomp_add, res_add, hfres y (h₂ y), hδ]
      abel
    have hk₁ : ∀ {m : ℕ} (y : Fin (m + 1) → ι), inter U y ⊓ (Z ⊓ part U mx.support) ≤
        inter U y ⊓ (Z ⊓ part U (insert α mx.support)) :=
      fun y => inter_inf_part_le U (Set.subset_insert _ _) y
    have hk₂ : ∀ {m : ℕ} (y : Fin (m + 1) → ι), inter U y ⊓ (Z ⊓ U α) ≤
        inter U y ⊓ (Z ⊓ part U (insert α mx.support)) :=
      fun y => inf_le_inf_left _ (inf_le_inf_left _ (le_part U (Set.mem_insert α mx.support)))
    have hcover : ∀ {m : ℕ} (y : Fin m → ι),
        inter U y ⊓ (Z ⊓ part U (insert α mx.support)) ≤
          inter U y ⊓ (Z ⊓ part U mx.support) ⊔ inter U y ⊓ (Z ⊓ U α) := by
      intro m y
      rw [part_insert, inf_sup_left, inf_sup_left]
      exact le_of_eq (sup_comm _ _)
    have hglue : ∀ y : Fin (q + 1) → ι,
        ∃ t : ToType (F.obj.obj (op (inter U y ⊓ (Z ⊓ part U (insert α mx.support))))),
          res F.obj (hk₁ y) t = rcomp mx.val y ∧ res F.obj (hk₂ y) t = rcomp (c₀ + f) y := by
      intro y
      refine exists_res_eq_pair F (hk₁ y) (hk₂ y) (hcover y) _ _ fun Y j₁ j₂ => ?_
      have hY : Y ≤ inter U y ⊓ (Z ⊓ part U mx.support ⊓ U α) :=
        le_inf (j₁.trans inf_le_left)
          (le_inf (j₁.trans inf_le_right) ((j₂.trans inf_le_right).trans inf_le_right))
      calc res F.obj j₁ (rcomp mx.val y)
          = res F.obj hY (res F.obj (h₁ y) (rcomp mx.val y)) := (res_res F.obj hY (h₁ y) _).symm
        _ = res F.obj hY (res F.obj (h₂ y) (rcomp (c₀ + f) y)) := by rw [hγ y]
        _ = res F.obj j₂ (rcomp (c₀ + f) y) := res_res F.obj hY (h₂ y) _
    choose gl hgl₁ hgl₂ using hglue
    refine (hmx ⟨insert α mx.support, rmk gl, fun x hx => ?_⟩
      ⟨Set.subset_insert _ _, fun y hy => ?_⟩).1 (Set.mem_insert α mx.support)
    · refine eq_of_res_eq_pair F (hk₁ x) (hk₂ x) (hcover x) _ _ ?_ ?_
      · rw [res_rcomp_rd_of_res_eq U F mx.val (rmk gl) hk₁
          (fun y => by rw [rcomp_rmk]; exact hgl₁ y) x,
          mx.isPrimitive x (inf_le_inf_left _ inf_le_left), res_res]
      · rw [res_rcomp_rd_of_res_eq U F (c₀ + f) (rmk gl) hk₂
          (fun y => by rw [rcomp_rmk]; exact hgl₂ y) x, rd_add, hf0, add_zero, hdc₀ x, res_res]
    · rw [rcomp_rmk]
      exact hgl₁ y
  have hsupp : part U mx.support = ⨆ i, U i := by
    rw [Set.eq_univ_of_forall hfull]
    exact part_univ U
  have hb : ∀ {m : ℕ} (y : Fin (m + 1) → ι),
      inter U y ⊓ Z ≤ inter U y ⊓ (Z ⊓ part U mx.support) := by
    intro m y
    refine le_inf inf_le_left (le_inf inf_le_right ?_)
    rw [hsupp]
    exact inf_le_left.trans (inter_le_iSup U y)
  refine ⟨rmk fun y => res F.obj (hb y) (rcomp mx.val y), rcochain_ext _ _ fun x => ?_⟩
  rw [← res_rcomp_rd_of_res_eq U F (rmk fun y => res F.obj (hb y) (rcomp mx.val y)) mx.val hb
      (fun y => (rcomp_rmk (fun y => res F.obj (hb y) (rcomp mx.val y)) y).symm) x,
    mx.isPrimitive x (inf_le_inf_left _ inf_le_left), res_res, res_id]

/-- **Vanishing of the relative Čech cohomology of a flasque sheaf in positive degrees.** By
induction on the degree: cocycles of degree `0` extend by gluing and flasqueness, which gives
the vanishing in degree `1` by the Zorn step; and each further degree of vanishing lets the
cocycles of that degree be extended, which gives the vanishing one degree up. -/
theorem vanishing {Cls : Opens X → Prop}
    (hinf : ∀ {Z : Opens X}, Cls Z → ∀ α : ι, Cls (Z ⊓ U α))
    (hpart : ∀ {Z : Opens X}, Cls Z → ∀ A : Set ι, Cls (Z ⊓ part U A))
    (hE : Extends U F Cls) (q : ℕ) : Vanishing U F Cls q := by
  induction q with
  | zero => exact vanishing_of_cocycleExt U F hinf hpart (cocycleExt_zero U F hE)
  | succ n ih => exact vanishing_of_cocycleExt U F hinf hpart (cocycleExt_succ U F hE ih)

/-- **Vanishing of the relative Čech cohomology of a flasque sheaf in positive degrees**, at the
trivial class of relative opens. -/
theorem vanishing_isFlasque [F.IsFlasque] (q : ℕ) : Vanishing U F (fun _ => True) q :=
  vanishing U F (fun _ _ => trivial) (fun _ _ => trivial) (extends_of_isFlasque U F _) q

/-! ### The Čech complex of the sheaf itself -/

/-- Restricting to the whole space does nothing: `shrink P ⊤` is isomorphic to `P`. -/
def shrinkTopIso : shrink P ⊤ ≅ P :=
  NatIso.ofComponents (fun W => P.mapIso (eqToIso (congrArg op (inf_top_eq (unop W)))))
    (fun f => by
      dsimp [shrink]
      rw [← P.map_comp, ← P.map_comp]
      exact congrArg P.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _)))

end

section

/-- **Stacks 09SZ.** A flasque sheaf has zero Čech cohomology in every positive degree. -/
@[stacks 09SZ]
public lemma isZero_cechComplex_homology_of_isFlasque
    {X : TopCat.{u}} {ι : Type v} (F : TopCat.Sheaf AddCommGrpCat.{v} X)
    (V : Opens X) (U : ι → Opens X) (hU : V = ⨆ i, U i) [F.IsFlasque]
    (p : ℕ) (hp : 0 < p) :
    IsZero (((cechComplexFunctor U).obj F.obj).homology p) := by
  -- The covering hypothesis is not needed: the Čech complex of `U` is assembled from the
  -- intersections of the members of `U` alone, and the open `V` does not occur in it.
  have := hU
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp).symm⟩
  have key : IsZero ((relComplex U F.obj ⊤).homology (n + 1)) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology,
      HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
      ShortComplex.ab_exact_iff]
    intro s hs
    obtain ⟨b, hb⟩ := vanishing_isFlasque U F n ⊤ trivial s hs
    exact ⟨b, hb⟩
  refine IsZero.of_iso key ?_
  exact (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℕ) (n + 1)).mapIso
    ((cechComplexFunctor U).mapIso (shrinkTopIso (P := F.obj)).symm)

end

end Stacks.Cohomology.FlasqueCech

end
