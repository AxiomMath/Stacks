module
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.SetTheory.ZFC.PSet
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.CategoryTheory.Sites.Point.Conservative
public import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute
import all StacksFrontier.CategoryTheory.Sites.Point.CriterionForExistenceOfPoints.RefinementStep

/-!
# Wide fibre products of instructions and the refined index category

The wide fibre product attached to a finite set of instructions, and the refined index category of
nodes with its refined system, used in the proof of Stacks 00YP.
Split out of `StacksFrontier.CategoryTheory.Sites.Point.CriterionForExistenceOfPoints`.
-/

section

universe w w' v u t u₁ v₂ u₂
open CategoryTheory Limits Opposite

namespace Stacks.SitePoints.UniformRefinement

/-! ### The wide fibre product attached to a finite set of instructions -/

section Inter

variable {C : Type u} [Category.{v} C] {N : Type u₁} [SmallCategory N] {J : GrothendieckTopology C}
  {p : N ⥤ C}

/-- The wide fibre product of `p j` along a finite set `S` of instructions at `j`: an object over
`p j` with a morphism to each prescribed member of a covering, compatible with the structure
morphisms, and universal among such. It is a limit, so it is unique up to unique isomorphism over
`p j`; the universal property is carried as data because the shape of the limit varies with `S`. -/
private structure Inter (j : N) (S : Finset (Instr J p j)) where
  /-- The underlying object. -/
  X : C
  /-- The structure morphism to `p j`. -/
  π : X ⟶ p.obj j
  /-- The morphism to the member of the covering prescribed by an instruction of `S`. -/
  y : ∀ i : S, X ⟶ mid (i : Instr J p j)
  /-- The defining square of the fibre product. -/
  fac : ∀ i : S, y i ≫ leg (i : Instr J p j) = toBase (i : Instr J p j) π
  /-- The universal property: a compatible family factors through `X`. -/
  lift :
    ∀ {Z : C} (z : Z ⟶ p.obj j) (c : ∀ i : S, Z ⟶ mid (i : Instr J p j)),
      (∀ i : S, c i ≫ leg (i : Instr J p j) = toBase (i : Instr J p j) z) → (Z ⟶ X)
  /-- The factorisation is over `p j`. -/
  lift_π :
    ∀ {Z : C} (z : Z ⟶ p.obj j) (c : ∀ i : S, Z ⟶ mid (i : Instr J p j)) (hc), lift z c hc ≫ π = z
  /-- The factorisation is compatible with the projections. -/
  lift_y :
    ∀ {Z : C} (z : Z ⟶ p.obj j) (c : ∀ i : S, Z ⟶ mid (i : Instr J p j)) (hc) (i : S),
      lift z c hc ≫ y i = c i
  /-- The factorisation is unique. -/
  hom_ext : ∀ {Z : C} (m m' : Z ⟶ X), m ≫ π = m' ≫ π → (∀ i : S, m ≫ y i = m' ≫ y i) → m = m'

/-- The projections of a wide fibre product at two equal instructions agree. The types of the two
sides are definitionally equal — `mid` does not see the morphism `φ` of an instruction — so this is
the equality one wants, but it has to be proved as a `HEq` because the family `Inter.y` is
dependent. -/
private lemma Inter.y_heq {j : N} {S : Finset (Instr J p j)} (M : Inter j S) {i i' : S}
    (h : i = i') : HEq (M.y i) (M.y i') := by
  subst h; rfl

/-- The projection at an instruction pulled back along an identity is the projection at the
instruction. -/
private lemma Inter.y_pullInstr_id {j : N} {S : Finset (Instr J p j)} (M : Inter j S) {ψ : j ⟶ j}
    (hψ : ψ = 𝟙 j) {i : Instr J p j} (hi : pullInstr ψ i ∈ S) (hi' : i ∈ S) :
    M.y ⟨pullInstr ψ i, hi⟩ = M.y ⟨i, hi'⟩ :=
  eq_of_heq (M.y_heq (Subtype.ext (show pullInstr ψ i = i by rw [hψ, pullInstr_id])))

/-- The projection at an instruction pulled back along a composite is the projection at the
twice-pulled-back instruction. -/
private lemma Inter.y_pullInstr_comp {j j' j'' : N} {S : Finset (Instr J p j)} (M : Inter j S)
    {ψ : j ⟶ j''} {ψ₁ : j ⟶ j'} {ψ₂ : j' ⟶ j''} (hψ : ψ = ψ₁ ≫ ψ₂) {i : Instr J p j''}
    (hi : pullInstr ψ i ∈ S) (hi' : pullInstr ψ₁ (pullInstr ψ₂ i) ∈ S) :
    M.y ⟨pullInstr ψ i, hi⟩ = M.y ⟨pullInstr ψ₁ (pullInstr ψ₂ i), hi'⟩ :=
  eq_of_heq
    (M.y_heq
      (Subtype.ext
        (show pullInstr ψ i = pullInstr ψ₁ (pullInstr ψ₂ i) by rw [hψ, pullInstr_comp])))

/-- Pullbacks along the members of the coverings of the covering data exist, as soon as they exist
for every finite covering of the site. -/
private lemma hasPullback_covData
    (hpb :
      ∀ {W : C} {ι : Type t} [Finite ι] {Y : ι → C} (g : ∀ k, Y k ⟶ W),
        Sieve.ofArrows Y g ∈ J W → ∀ (X : C) (h : X ⟶ W) (k : ι), HasPullback h (g k))
    (c : CovData J p) (X : C) (h : X ⟶ c.W) (k : Fin c.n) : HasPullback h (c.g k) :=
  hpb (ι := ULift.{t} (Fin c.n)) (fun k => c.g k.down)
    (by
      rw [sieve_ofArrows_ulift]; exact c.covering)
    X h ⟨k⟩

/-- The fibre product an instruction prescribes exists, for any object given over `p j`. This is
the form `Stacks.SitePoints.UniformRefinement.insertInter` asks for. -/
private lemma hasPullback_instr
    (hpb :
      ∀ {W : C} {ι : Type t} [Finite ι] {Y : ι → C} (g : ∀ k, Y k ⟶ W),
        Sieve.ofArrows Y g ∈ J W → ∀ (X : C) (h : X ⟶ W) (k : ι), HasPullback h (g k))
    {j : N} (i : Instr J p j) {X : C} (π : X ⟶ p.obj j) : HasPullback (toBase i π) (leg i) :=
  hasPullback_covData hpb i.c X (toBase i π) i.k

/-! #### The wide fibre product as an iterated fibre product

The two lemmas below are the only places where an equality of instructions has to be transported,
and
they are what make the case distinction in `Stacks.SitePoints.UniformRefinement.insertY` harmless.
    -/

/-- A family of morphisms to the prescribed members of the coverings takes equal values at equal
instructions, `eqToHom` mediating between the two members. -/
private lemma comp_eqToHom_eq {j : N} {S : Finset (Instr J p j)} {Z : C}
    (cc : ∀ i : S, Z ⟶ mid (i : Instr J p j)) (i i' : S)
    (he : (i : Instr J p j) = (i' : Instr J p j)) : cc i ≫ eqToHom (congrArg mid he) = cc i' := by
  obtain rfl : i = i' := Subtype.ext he
  simp

/-- The defining square of a wide fibre product is transported along an equality of
instructions. -/
private lemma comp_eqToHom_leg_eq {j : N} {i i' : Instr J p j} (he : i = i') {X : C}
    (m : X ⟶ mid i) (π : X ⟶ p.obj j) (h : m ≫ leg i = toBase i π) :
    (m ≫ eqToHom (congrArg mid he)) ≫ leg i' = toBase i' π := by
  cases he
  simpa using h

/-- The wide fibre product over no instruction at all is `p j` itself. -/
private noncomputable def emptyInter (j : N) : Inter j (∅ : Finset (Instr J p j)) where
  X := p.obj j
  π := 𝟙 _
  y i := notMem_empty_elim i.2
  fac i := notMem_empty_elim i.2
  lift := fun z _ _ => z
  lift_π := fun _ _ _ => Category.comp_id _
  lift_y := fun _ _ _ i => notMem_empty_elim i.2
  hom_ext := fun _ _ h _ => by simpa using h

open scoped Classical in
/-- The projection of the fibre product of `M.X` along the member of the covering prescribed by an
instruction `i₀` to the member prescribed by an instruction of `insert i₀ S`: the second projection
at `i₀` itself, and the first projection followed by the projection of `M` at any other. -/
private noncomputable def insertY {j : N} {S : Finset (Instr J p j)} (M : Inter j S)
    (i₀ : Instr J p j) [HasPullback (toBase i₀ M.π) (leg i₀)] (i : ↥(insert i₀ S)) :
    pullback (toBase i₀ M.π) (leg i₀) ⟶ mid (i : Instr J p j) :=
  if h : (i : Instr J p j) ∈ S then
    pullback.fst (toBase i₀ M.π) (leg i₀) ≫ M.y ⟨(i : Instr J p j), h⟩
  else
    pullback.snd (toBase i₀ M.π) (leg i₀) ≫
      eqToHom (congrArg mid ((Finset.mem_insert.1 i.2).resolve_right h)).symm

open scoped Classical in
private lemma insertY_of_mem {j : N} {S : Finset (Instr J p j)} (M : Inter j S) (i₀ : Instr J p j)
    [HasPullback (toBase i₀ M.π) (leg i₀)] (i : ↥(insert i₀ S)) (h : (i : Instr J p j) ∈ S) :
    insertY M i₀ i = pullback.fst (toBase i₀ M.π) (leg i₀) ≫ M.y ⟨(i : Instr J p j), h⟩ :=
  dite_eq_left h

open scoped Classical in
private lemma insertY_of_notMem {j : N} {S : Finset (Instr J p j)} (M : Inter j S)
    (i₀ : Instr J p j) [HasPullback (toBase i₀ M.π) (leg i₀)] (i : ↥(insert i₀ S))
    (h : (i : Instr J p j) ∉ S) :
    insertY M i₀ i =
      pullback.snd (toBase i₀ M.π) (leg i₀) ≫
        eqToHom (congrArg mid ((Finset.mem_insert.1 i.2).resolve_right h)).symm :=
  dite_eq_right h

open scoped Classical in
/-- At the new instruction itself the projection is the second projection of the fibre product: the
`eqToHom` of `Stacks.SitePoints.UniformRefinement.insertY` is then the identity, by proof
irrelevance. -/
private lemma insertY_self {j : N} {S : Finset (Instr J p j)} (M : Inter j S) (i₀ : Instr J p j)
    [HasPullback (toBase i₀ M.π) (leg i₀)] (hi₀ : i₀ ∉ S) (hi : i₀ ∈ insert i₀ S) :
    insertY M i₀ ⟨i₀, hi⟩ = pullback.snd (toBase i₀ M.π) (leg i₀) :=
  (insertY_of_notMem M i₀ ⟨i₀, hi⟩ hi₀).trans (Category.comp_id _)

/-- The defining square of the fibre product along the member prescribed by `i₀`, in the form
`Stacks.SitePoints.UniformRefinement.Inter.fac` asks for. -/
private lemma insertInter_fac_self {j : N} {S : Finset (Instr J p j)} (M : Inter j S)
    (i₀ : Instr J p j) [HasPullback (toBase i₀ M.π) (leg i₀)] :
    pullback.snd (toBase i₀ M.π) (leg i₀) ≫ leg i₀ =
      toBase i₀ (pullback.fst (toBase i₀ M.π) (leg i₀) ≫ M.π) := by
  rw [← pullback.condition, toBase_comp]

open scoped Classical in
/-- The wide fibre product over `insert i₀ S` is the fibre product of the one over `S` along the
member of the covering prescribed by `i₀`. -/
private noncomputable def insertInter {j : N} {S : Finset (Instr J p j)} (M : Inter j S)
    (i₀ : Instr J p j) (hi₀ : i₀ ∉ S) [HasPullback (toBase i₀ M.π) (leg i₀)] :
    Inter j (insert i₀ S)
    where
  X := pullback (toBase i₀ M.π) (leg i₀)
  π := pullback.fst (toBase i₀ M.π) (leg i₀) ≫ M.π
  y := insertY M i₀
  fac := by
    intro i
    by_cases h : (i : Instr J p j) ∈ S
    · rw [insertY_of_mem M i₀ i h, Category.assoc, M.fac ⟨(i : Instr J p j), h⟩, ← toBase_comp]
    · rw [insertY_of_notMem M i₀ i h]
      exact
        comp_eqToHom_leg_eq ((Finset.mem_insert.1 i.2).resolve_right h).symm _ _
          (insertInter_fac_self M i₀)
  lift := fun z c hc =>
    pullback.lift
      (M.lift z (fun i => c ⟨(i : Instr J p j), Finset.mem_insert_of_mem i.2⟩)
        (fun i => hc ⟨(i : Instr J p j), Finset.mem_insert_of_mem i.2⟩))
      (c ⟨i₀, Finset.mem_insert_self i₀ S⟩)
      (by
        rw [← toBase_comp, M.lift_π]
        exact (hc ⟨i₀, Finset.mem_insert_self i₀ S⟩).symm)
  lift_π := fun z c hc => by rw [pullback.lift_fst_assoc, M.lift_π]
  lift_y := fun z c hc i => by
    by_cases h : (i : Instr J p j) ∈ S
    · rw [insertY_of_mem M i₀ i h, pullback.lift_fst_assoc]
      exact M.lift_y _ _ _ _
    · rw [insertY_of_notMem M i₀ i h, pullback.lift_snd_assoc]
      exact
        comp_eqToHom_eq c ⟨i₀, Finset.mem_insert_self i₀ S⟩ i
          ((Finset.mem_insert.1 i.2).resolve_right h).symm
  hom_ext := fun m m' hπ hy => by
    refine pullback.hom_ext ?_ ?_
    · refine M.hom_ext _ _ ?_ (fun i => ?_)
      · rw [Category.assoc, Category.assoc]
        exact hπ
      · have hi := hy ⟨(i : Instr J p j), Finset.mem_insert_of_mem i.2⟩
        rw [insertY_of_mem M i₀ ⟨(i : Instr J p j), Finset.mem_insert_of_mem i.2⟩ i.2] at hi
        rw [Category.assoc, Category.assoc]
        exact hi
    · have h₀ := hy ⟨i₀, Finset.mem_insert_self i₀ S⟩
      rwa [insertY_self M i₀ hi₀ (Finset.mem_insert_self i₀ S)] at h₀

/-- The underlying object of `Stacks.SitePoints.UniformRefinement.insertInter` is the fibre
product, and its structure morphism the first projection followed by that of `M`; both hold by
definitional unfolding, and the statements below that mix the two spellings rest on that. -/
private lemma insertInter_π {j : N} {S : Finset (Instr J p j)} (M : Inter j S) (i₀ : Instr J p j)
    (hi₀ : i₀ ∉ S) [HasPullback (toBase i₀ M.π) (leg i₀)] :
    (insertInter M i₀ hi₀).π = pullback.fst (toBase i₀ M.π) (leg i₀) ≫ M.π :=
  rfl

open scoped Classical in
/-- The wide fibre product exists: it is the iterated fibre product along the instructions of `S`,
one at a time. -/
private lemma nonempty_inter
    (hpb :
      ∀ {W : C} {ι : Type t} [Finite ι] {Y : ι → C} (g : ∀ k, Y k ⟶ W),
        Sieve.ofArrows Y g ∈ J W → ∀ (X : C) (h : X ⟶ W) (k : ι), HasPullback h (g k))
    (j : N) (S : Finset (Instr J p j)) : Nonempty (Inter j S) := by
  induction S using Finset.induction with
  | empty => exact ⟨emptyInter j⟩
  | insert i₀ S hi₀ ih =>
    obtain ⟨M⟩ := ih
    have : HasPullback (toBase i₀ M.π) (leg i₀) := hasPullback_instr hpb i₀ M.π
    exact ⟨insertInter M i₀ hi₀⟩

/-- A choice of wide fibre product. -/
private noncomputable def inter
    (hpb :
      ∀ {W : C} {ι : Type t} [Finite ι] {Y : ι → C} (g : ∀ k, Y k ⟶ W),
        Sieve.ofArrows Y g ∈ J W → ∀ (X : C) (h : X ⟶ W) (k : ι), HasPullback h (g k))
    (j : N) (S : Finset (Instr J p j)) : Inter j S :=
  (nonempty_inter hpb j S).some

/-! #### Morphisms of wide fibre products -/

/-- The morphism of wide fibre products induced by a morphism `ψ : j ⟶ j'` of `N` along which the
instructions of `S'` pull back into those of `S`: the projections of the source are then a family
compatible with the instructions of the target. -/
private noncomputable def Inter.map {j j' : N} {S : Finset (Instr J p j)}
    {S' : Finset (Instr J p j')} (M : Inter j S) (M' : Inter j' S') (ψ : j ⟶ j')
    (hψ : ∀ i ∈ S', pullInstr ψ i ∈ S) : M.X ⟶ M'.X :=
  M'.lift (M.π ≫ p.map ψ) (fun i => M.y ⟨pullInstr ψ i, hψ i i.2⟩)
    (fun i => (M.fac ⟨pullInstr ψ i, hψ i i.2⟩).trans (toBase_pullInstr _ _ _))

private lemma Inter.map_π {j j' : N} {S : Finset (Instr J p j)} {S' : Finset (Instr J p j')}
    (M : Inter j S) (M' : Inter j' S') (ψ : j ⟶ j') (hψ : ∀ i ∈ S', pullInstr ψ i ∈ S) :
    M.map M' ψ hψ ≫ M'.π = M.π ≫ p.map ψ :=
  M'.lift_π _ _ _

private lemma Inter.map_y {j j' : N} {S : Finset (Instr J p j)} {S' : Finset (Instr J p j')}
    (M : Inter j S) (M' : Inter j' S') (ψ : j ⟶ j') (hψ : ∀ i ∈ S', pullInstr ψ i ∈ S) (i : S') :
    M.map M' ψ hψ ≫ M'.y i = M.y ⟨pullInstr ψ i, hψ i i.2⟩ :=
  M'.lift_y _ _ _ _

/-- The wide fibre product over the empty set of instructions is `p j`. -/
private noncomputable def interEmptyIso
    (hpb :
      ∀ {W : C} {ι : Type t} [Finite ι] {Y : ι → C} (g : ∀ k, Y k ⟶ W),
        Sieve.ofArrows Y g ∈ J W → ∀ (X : C) (h : X ⟶ W) (k : ι), HasPullback h (g k))
    (j : N) : (inter hpb j (∅ : Finset (Instr J p j))).X ≅ p.obj j
    where
  hom := (inter hpb j ∅).π
  inv :=
    (inter hpb j ∅).lift (𝟙 _) (fun i => notMem_empty_elim i.2) (fun i => notMem_empty_elim i.2)
  hom_inv_id := by
    refine (inter hpb j ∅).hom_ext _ _ ?_ (fun i => notMem_empty_elim i.2)
    rw [Category.assoc, (inter hpb j ∅).lift_π, Category.id_comp, Category.comp_id]
  inv_hom_id := by rw [(inter hpb j ∅).lift_π]

open scoped Classical in
/-- **The fibre product along a prescribed member maps to the refinements prescribing it.** Let `S`
be a finite set of instructions at `z` not containing `i₀ = ⟨c, k, φ⟩`, and let `ψ : z ⟶ j'` be a
morphism of `N` along which a finite set `S'` of instructions at `j'` pulls back into
`insert i₀ S`. Then the fibre product of the wide fibre product of `S` along the `k`-th member of
the covering of `c` maps to the wide fibre product of `S'`, over `p ψ`.

The wide fibre product of `insert i₀ S` *is* that fibre product
(`Stacks.SitePoints.UniformRefinement.insertInter`), so this is
`Stacks.SitePoints.UniformRefinement.Inter.map`; it is stated as an existential because the object
of `insert i₀ S` is the one place where a caller would otherwise have to name
`Stacks.SitePoints.UniformRefinement.insertInter` and to produce the fibre product in both of the
two spellings `Stacks.SitePoints.UniformRefinement.toBase` mediates between. -/
private lemma exists_hom_comp_π_eq
    (hpb :
      ∀ {W : C} {ι : Type t} [Finite ι] {Y : ι → C} (g : ∀ k, Y k ⟶ W),
        Sieve.ofArrows Y g ∈ J W → ∀ (X : C) (h : X ⟶ W) (k : ι), HasPullback h (g k))
    {z j' : N} {S : Finset (Instr J p z)} {S' : Finset (Instr J p j')} {c : CovData J p}
    {k : Fin c.n} {φ : z ⟶ (sk N).obj c.jj} (hi₀ : (⟨c, k, φ⟩ : Instr J p z) ∉ S) (ψ : z ⟶ j')
    (hψ : ∀ i ∈ S', pullInstr ψ i ∈ insert (⟨c, k, φ⟩ : Instr J p z) S)
    [HasPullback ((inter hpb z S).π ≫ p.map φ ≫ c.f) (c.g k)] :
    ∃ q : pullback ((inter hpb z S).π ≫ p.map φ ≫ c.f) (c.g k) ⟶ (inter hpb j' S').X,
      q ≫ (inter hpb j' S').π =
        pullback.fst ((inter hpb z S).π ≫ p.map φ ≫ c.f) (c.g k) ≫
          (inter hpb z S).π ≫ p.map ψ := by
  have := hasPullback_instr hpb (⟨c, k, φ⟩ : Instr J p z) (inter hpb z S).π
  refine
    ⟨(insertInter (inter hpb z S) (⟨c, k, φ⟩ : Instr J p z) hi₀).map (inter hpb j' S') ψ hψ, ?_⟩
  have h :=
    Inter.map_π (insertInter (inter hpb z S) (⟨c, k, φ⟩ : Instr J p z) hi₀) (inter hpb j' S') ψ hψ
  rw [insertInter_π] at h
  exact h.trans (Category.assoc _ _ _)

end Inter

/-! ### The refined index category -/

section Node

variable {C : Type u} [Category.{v} C] {N : Type u₁} [SmallCategory N] {J : GrothendieckTopology C}
  {p : N ⥤ C}

/-- A *node*: an index `j` of `N` together with a finite set of instructions at `j` whose chosen
members are the ones prescribed by the global choice `κ`. -/
private structure Node (J : GrothendieckTopology C) (p : N ⥤ C)
    (κ : ∀ c : CovData J p, Fin c.n) where
  /-- The underlying index of `N`. -/
  j : N
  /-- The finite set of instructions imposed at `j`. -/
  S : Finset (Instr J p j)
  /-- The chosen members are the globally prescribed ones. -/
  consistent : ∀ i ∈ S, i.k = κ i.c
  /-- No covering datum is prescribed twice: an instruction of `S` is determined by its covering
  datum. This is what makes a single global choice `κ` enough; see
  `Stacks.SitePoints.UniformRefinement.exists_good`. -/
  inj : ∀ i ∈ S, ∀ i' ∈ S, i.c = i'.c → i = i'

variable {κ : ∀ c : CovData J p, Fin c.n}

/-- The category of nodes: a morphism is a morphism of `N` along which the instructions of the
target pull back into those of the source. -/
@[instance_reducible] private def nodeCategory (J : GrothendieckTopology C) (p : N ⥤ C)
    (κ : ∀ c : CovData J p, Fin c.n) : SmallCategory (Node J p κ)
    where
  Hom x y := ULift.{max u v} { ψ : x.j ⟶ y.j // ∀ i ∈ y.S, pullInstr ψ i ∈ x.S }
  id x :=
    ⟨⟨𝟙 x.j, fun i hi => by
        rw [pullInstr_id]; exact hi⟩⟩
  comp {x y z} m₁ m₂ :=
    ⟨⟨m₁.down.1 ≫ m₂.down.1, fun i hi => by
        rw [pullInstr_comp]; exact m₁.down.2 _ (m₂.down.2 i hi)⟩⟩
  id_comp _ := congrArg ULift.up (Subtype.ext (Category.id_comp _))
  comp_id _ := congrArg ULift.up (Subtype.ext (Category.comp_id _))
  assoc _ _ _ := congrArg ULift.up (Subtype.ext (Category.assoc _ _ _))

attribute [local instance] nodeCategory

/-- A morphism of `N` along which the instructions of the target pull back into those of the source
is a morphism of nodes; its underlying morphism of `N` is that morphism, by definition. -/
private def nodeHom {x y : Node J p κ} (ψ : x.j ⟶ y.j) (hψ : ∀ i ∈ y.S, pullInstr ψ i ∈ x.S) :
    x ⟶ y :=
  ⟨⟨ψ, hψ⟩⟩

private lemma nodeHom_ext {x y : Node J p κ} (m₁ m₂ : x ⟶ y)
    (h : (m₁.down : x.j ⟶ y.j) = m₂.down) : m₁ = m₂ :=
  congrArg ULift.up (Subtype.ext h)

private lemma nodeId_down (x : Node J p κ) : ((𝟙 x : x ⟶ x).down : x.j ⟶ x.j) = 𝟙 x.j :=
  rfl

private lemma nodeComp_down {x y z : Node J p κ} (m₁ : x ⟶ y) (m₂ : y ⟶ z) :
    (((m₁ ≫ m₂).down : x.j ⟶ z.j)) = (m₁.down : x.j ⟶ y.j) ≫ m₂.down :=
  rfl

private lemma nodeHom_down_congr {x y : Node J p κ} {m m' : x ⟶ y} (h : m = m') :
    (m.down : x.j ⟶ y.j) = m'.down :=
  congrArg (fun n : ULift _ => (n.down : Subtype _).1) h

open scoped Classical in
/-- **A node pulled back along a morphism of `N`.** The instructions of a node `x`, pulled back
along
`ψ : j ⟶ x.j`, are again a node at `j`: pulling back changes neither the covering datum nor the
chosen
member of an instruction, and is injective on the instructions prescribing a fixed covering datum.
It
is a node below `x`, over `ψ`, and every node below `x` is built from one of these. -/
private noncomputable def Node.pull (x : Node J p κ) {j : N} (ψ : j ⟶ x.j) : Node J p κ where
  j := j
  S := x.S.image (pullInstr ψ)
  consistent i hi := by
    obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.1 hi
    exact x.consistent i₀ hi₀
  inj i hi i' hi' h := by
    obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.1 hi
    obtain ⟨i₀', hi₀', rfl⟩ := Finset.mem_image.1 hi'
    exact congrArg (pullInstr ψ) (x.inj i₀ hi₀ i₀' hi₀' h)

/-- In a cofiltered category, finitely many pairs of parallel morphisms out of a single object are
equalized simultaneously by one morphism into it: the pairs are equalized one at a time by
`CategoryTheory.IsCofiltered.eqHom`, and postcomposition preserves the equalities already
obtained. -/
private lemma exists_forall_comp_eq [IsCofiltered N] {ι : Type*} [Finite ι] {b : N} {A : ι → N}
    (f g : ∀ t, b ⟶ A t) : ∃ (b' : N) (r : b' ⟶ b), ∀ t, r ≫ f t = r ≫ g t := by
  classical
  cases nonempty_fintype ι
  suffices h : ∀ s : Finset ι, ∃ (b' : N) (r : b' ⟶ b), ∀ t ∈ s, r ≫ f t = r ≫ g t
    by
    obtain ⟨b', r, hr⟩ := h Finset.univ
    exact ⟨b', r, fun t => hr t (Finset.mem_univ t)⟩
  intro s
  induction s using Finset.induction with
  | empty => exact ⟨b, 𝟙 b, by simp⟩
  | insert t s _ ih =>
    obtain ⟨b', r, hr⟩ := ih
    refine
      ⟨IsCofiltered.eq (r ≫ f t) (r ≫ g t), IsCofiltered.eqHom (r ≫ f t) (r ≫ g t) ≫ r,
        fun t' ht' => ?_⟩
    simp only [Category.assoc]
    rcases Finset.mem_insert.1 ht' with rfl | ht'
    · exact IsCofiltered.eq_condition _ _
    · rw [hr t' ht']

/-- In a cofiltered category, a finite nonempty family of objects, each equipped with a morphism to
each of two fixed objects, admits a single object below all of them at which both families of
composites become independent of the index: the first family is made independent by
`CategoryTheory.IsCofiltered.wideCospan`, and the second by
`Stacks.SitePoints.UniformRefinement.exists_forall_comp_eq` applied to the composites and to a
fixed one among them. -/
private lemma exists_cone_forall_comp_eq [IsCofiltered N] {ι : Type*} [Finite ι] [Nonempty ι]
    (A : ι → N) (b₁ b₂ : N) (g₁ : ∀ t, A t ⟶ b₁) (g₂ : ∀ t, A t ⟶ b₂) :
    ∃ (z : N) (u : ∀ t, z ⟶ A t) (f₁ : z ⟶ b₁) (f₂ : z ⟶ b₂),
      (∀ t, u t ≫ g₁ t = f₁) ∧ (∀ t, u t ≫ g₂ t = f₂) := by
  classical
  obtain ⟨w, f₁, c, hc⟩ := IsCofiltered.wideCospan g₁
  obtain ⟨z, r, hr⟩ :=
    exists_forall_comp_eq (b := w) (A := fun _ : ι => b₂) (fun t => c t ≫ g₂ t)
      (fun _ => c (Classical.arbitrary ι) ≫ g₂ (Classical.arbitrary ι))
  refine
    ⟨z, fun t => r ≫ c t, r ≫ f₁, r ≫ c (Classical.arbitrary ι) ≫ g₂ (Classical.arbitrary ι),
      fun t => ?_, fun t => ?_⟩
  · rw [Category.assoc, hc t]
  · rw [Category.assoc]
    exact hr t

/-- Two instructions sharing a covering datum and a chosen member on the nose pull back to the same
instruction as soon as their transport morphisms agree after pullback. The shared datum is a binder
rather than a hypothesis `i.c = i'.c`, so that no transport appears in the statement. -/
private lemma pullInstr_eq_pullInstr {j j' j'' : N} {c : CovData J p} {k k' : Fin c.n}
    {φ : j' ⟶ (sk N).obj c.jj} {φ' : j'' ⟶ (sk N).obj c.jj} (U : j ⟶ j') (V : j ⟶ j'')
    (hk : k = k') (hφ : U ≫ φ = V ≫ φ') :
    pullInstr U (⟨c, k, φ⟩ : Instr J p j') = pullInstr V (⟨c, k', φ'⟩ : Instr J p j'') := by
  subst hk
  exact congrArg (fun m => (⟨c, k, m⟩ : Instr J p j)) hφ

/-- Two nodes admit a common lower bound. Their instruction sets are pulled back to a common index
of `N`, chosen small enough that the two prescriptions of a covering datum prescribed by both nodes
become equal there (`Stacks.SitePoints.UniformRefinement.exists_forall_comp_eq`), so that the union
of the two pullbacks again prescribes each covering datum at most once. -/
private lemma node_cone_objs [IsCofiltered N] (x y : Node J p κ) :
    ∃ (z : Node J p κ) (_ : z ⟶ x) (_ : z ⟶ y), True := by
  classical
  obtain ⟨b₀, u₀, v₀, -⟩ := IsCofilteredOrEmpty.cone_objs x.j y.j
  obtain ⟨b₁, r, hr⟩ :=
    exists_forall_comp_eq (ι := { q : ↥x.S × ↥y.S // q.1.1.c = q.2.1.c }) (A := fun q =>
      (sk N).obj q.1.1.1.c.jj) (fun q => u₀ ≫ q.1.1.1.φ)
      (fun q =>
        v₀ ≫ q.1.2.1.φ ≫ eqToHom (congrArg (fun c : CovData J p => (sk N).obj c.jj) q.2).symm)
  have key : ∀ i ∈ (x.pull (r ≫ u₀)).S, ∀ i' ∈ (y.pull (r ≫ v₀)).S, i.c = i'.c → i = i' := by
    rintro i hi i' hi' hcc
    obtain ⟨⟨ca, ka, φa⟩, ha, rfl⟩ := Finset.mem_image.1 hi
    obtain ⟨⟨cb, kb, φb⟩, hb, rfl⟩ := Finset.mem_image.1 hi'
    have hka : ka = κ ca := x.consistent _ ha
    have hkb : kb = κ cb := y.consistent _ hb
    obtain rfl : ca = cb := hcc
    have h := hr ⟨(⟨_, ha⟩, ⟨_, hb⟩), rfl⟩
    simp only [eqToHom_refl, Category.comp_id] at h
    exact pullInstr_eq_pullInstr _ _ (hka.trans hkb.symm) (by simpa only [Category.assoc] using h)
  refine
    ⟨⟨b₁, (x.pull (r ≫ u₀)).S ∪ (y.pull (r ≫ v₀)).S, ?_, ?_⟩,
      nodeHom (r ≫ u₀) (fun i hi => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hi)),
      nodeHom (r ≫ v₀) (fun i hi => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi)),
      trivial⟩
  · intro i hi
    rcases Finset.mem_union.1 hi with hi | hi
    · exact (x.pull _).consistent i hi
    · exact (y.pull _).consistent i hi
  · intro i hi i' hi' hcc
    rcases Finset.mem_union.1 hi with h₁ | h₁ <;> rcases Finset.mem_union.1 hi' with h₂ | h₂
    · exact (x.pull _).inj i h₁ i' h₂ hcc
    · exact key i h₁ i' h₂ hcc
    · exact (key i' h₂ i h₁ hcc.symm).symm
    · exact (y.pull _).inj i h₁ i' h₂ hcc

/-- Two parallel morphisms of nodes are equalized by a morphism from a third node: an index of `N`
equalizing the two underlying morphisms, carrying the pullback of the source's instructions, which
prescribes each covering datum at most once because the source's does. -/
private lemma node_cone_maps [IsCofiltered N] ⦃x y : Node J p κ⦄ (m₁ m₂ : x ⟶ y) :
    ∃ (z : Node J p κ) (r : z ⟶ x), r ≫ m₁ = r ≫ m₂ := by
  classical
  obtain ⟨b₀, r₀, hr₀⟩ :=
    IsCofilteredOrEmpty.cone_maps (m₁.down.1 : x.j ⟶ y.j) (m₂.down.1 : x.j ⟶ y.j)
  exact ⟨x.pull r₀, nodeHom r₀ (fun _ hi => Finset.mem_image_of_mem _ hi), nodeHom_ext _ _ hr₀⟩

private lemma node_nonempty [IsCofiltered N] : Nonempty (Node J p κ) := by
  have : Nonempty N := IsCofiltered.nonempty
  exact ⟨⟨Classical.arbitrary N, ∅, by simp, by simp⟩⟩

private lemma nodeIsCofiltered [IsCofiltered N] : IsCofiltered (Node J p κ)
    where
  cone_objs := node_cone_objs
  cone_maps := node_cone_maps
  nonempty := node_nonempty

/-- The inclusion of `N` in the nodes, as the nodes with no instruction. -/
private def refIncl (J : GrothendieckTopology C) (p : N ⥤ C) (κ : ∀ c : CovData J p, Fin c.n) :
    N ⥤ Node J p κ
    where
  obj j := ⟨j, ∅, by simp, by simp⟩
  map {_ _} ψ := ⟨⟨ψ, by simp⟩⟩
  map_id _ := congrArg ULift.up (Subtype.ext rfl)
  map_comp _ _ := congrArg ULift.up (Subtype.ext rfl)

private lemma refIncl_full : (refIncl J p κ).Full
    where
  map_surjective {_ _} m := ⟨m.down.1, congrArg ULift.up (Subtype.ext rfl)⟩

private lemma refIncl_faithful : (refIncl J p κ).Faithful
    where
  map_injective {_ _} {_ _} h := congrArg (fun m : ULift _ => (m.down : Subtype _).1) h

/-- Every node maps to its own underlying index of `N`, forgetting its instructions; the underlying
morphism of `N` is the identity. Under `Stacks.SitePoints.UniformRefinement.refSystem` this is the
structure morphism of the node's wide fibre product. -/
private def toRefIncl (x : Node J p κ) : x ⟶ (refIncl J p κ).obj x.j :=
  nodeHom (𝟙 x.j) fun _ hi => notMem_empty_elim hi

/-- The node at which the member of a covering datum's covering prescribed by `κ` is realised: the
index of the datum's section, carrying the single instruction that prescribes the datum along the
identity. It is a node because it prescribes one datum once, and with the member `κ` prescribes. -/
private noncomputable def singletonNode (κ : ∀ c : CovData J p, Fin c.n) (c : CovData J p) :
    Node J p κ where
  j := (sk N).obj c.jj
  S := {⟨c, κ c, 𝟙 _⟩}
  consistent i hi := by
    rw [Finset.mem_singleton] at hi
    subst hi
    rfl
  inj i hi i' hi' _ := by
    rw [Finset.mem_singleton] at hi hi'
    rw [hi, hi']

/-- The single instruction of `Stacks.SitePoints.UniformRefinement.singletonNode`, as a member of
its set of instructions. -/
private noncomputable def singletonNodeInstr (κ : ∀ c : CovData J p, Fin c.n) (c : CovData J p) :
    ↥(singletonNode κ c).S :=
  ⟨⟨c, κ c, 𝟙 _⟩, Finset.mem_singleton_self _⟩

variable
  (hpb :
    ∀ {W : C} {ι : Type t} [Finite ι] {Y : ι → C} (g : ∀ k, Y k ⟶ W),
      Sieve.ofArrows Y g ∈ J W → ∀ (X : C) (h : X ⟶ W) (k : ι), HasPullback h (g k))

include hpb

/-- The morphism of wide fibre products induced by a morphism of nodes: the instructions of the
target pull back into those of the source, so the projections of the source are a family compatible
with the instructions of the target. -/
private noncomputable def refMap {x y : Node J p κ} (m : x ⟶ y) :
    (inter hpb x.j x.S).X ⟶ (inter hpb y.j y.S).X :=
  (inter hpb x.j x.S).map (inter hpb y.j y.S) m.down.1 m.down.2

private lemma refMap_π {x y : Node J p κ} (m : x ⟶ y) :
    refMap hpb m ≫ (inter hpb y.j y.S).π = (inter hpb x.j x.S).π ≫ p.map m.down.1 :=
  Inter.map_π _ _ _ _

private lemma refMap_π_assoc {x y : Node J p κ} (m : x ⟶ y) {Z : C} (f : p.obj y.j ⟶ Z) :
    refMap hpb m ≫ (inter hpb y.j y.S).π ≫ f = (inter hpb x.j x.S).π ≫ p.map m.down.1 ≫ f := by
  rw [← Category.assoc, refMap_π, Category.assoc]

private lemma refMap_y {x y : Node J p κ} (m : x ⟶ y) (i : y.S) :
    refMap hpb m ≫ (inter hpb y.j y.S).y i =
      (inter hpb x.j x.S).y ⟨pullInstr m.down.1 i, m.down.2 i i.2⟩ :=
  Inter.map_y _ _ _ _ _

/-- Functoriality of `Stacks.SitePoints.UniformRefinement.refMap`, read on the projections of the
wide fibre product. -/
private lemma refMap_y_comp {x y z : Node J p κ} (m₁ : x ⟶ y) (m₂ : y ⟶ z) (i : z.S) :
    refMap hpb (m₁ ≫ m₂) ≫ (inter hpb z.j z.S).y i =
      refMap hpb m₁ ≫ refMap hpb m₂ ≫ (inter hpb z.j z.S).y i := by
  have h₂ : pullInstr m₂.down.1 (i : Instr J p z.j) ∈ y.S := m₂.down.2 i i.2
  have h₁ : pullInstr m₁.down.1 (pullInstr m₂.down.1 (i : Instr J p z.j)) ∈ x.S := m₁.down.2 _ h₂
  have e₁ :
    refMap hpb (m₁ ≫ m₂) ≫ (inter hpb z.j z.S).y i =
      (inter hpb x.j x.S).y ⟨pullInstr m₁.down.1 (pullInstr m₂.down.1 (i : Instr J p z.j)), h₁⟩ :=
    (refMap_y hpb (m₁ ≫ m₂) i).trans
      (Inter.y_pullInstr_comp (inter hpb x.j x.S) (nodeComp_down m₁ m₂) _ h₁)
  have e₂ :
    refMap hpb m₁ ≫ refMap hpb m₂ ≫ (inter hpb z.j z.S).y i =
      (inter hpb x.j x.S).y
        ⟨pullInstr m₁.down.1 (pullInstr m₂.down.1 (i : Instr J p z.j)), h₁⟩ := by
    rw [refMap_y hpb m₂ i]
    exact refMap_y hpb m₁ ⟨pullInstr m₂.down.1 (i : Instr J p z.j), h₂⟩
  exact e₁.trans e₂.symm

/-- The refined system: the functor sending a node to its wide fibre product. -/
private noncomputable def refSystem (κ : ∀ c : CovData J p, Fin c.n) : Node J p κ ⥤ C where
  obj x := (inter hpb x.j x.S).X
  map m := refMap hpb m
  map_id x := by
    refine (inter hpb x.j x.S).hom_ext _ _ ?_ (fun i => ?_)
    · rw [refMap_π, nodeId_down]
      simp
    · simp only [refMap_y, Category.id_comp]
      exact Inter.y_pullInstr_id _ (nodeId_down x) _ _
  map_comp m₁ m₂ := by
    refine (inter hpb _ _).hom_ext _ _ ?_ (fun i => ?_)
    · simp [refMap_π, refMap_π_assoc, nodeComp_down]
    · rw [Category.assoc]
      exact refMap_y_comp hpb m₁ m₂ i

/-- The refined system restricts along the inclusion of `N` to the original system. -/
private noncomputable def refIso (κ : ∀ c : CovData J p, Fin c.n) :
    refIncl J p κ ⋙ refSystem hpb κ ≅ p :=
  NatIso.ofComponents (fun j => interEmptyIso hpb j)
    (by
      intro j j' ψ; exact (inter hpb j' ∅).lift_π _ _ _)

/-- A morphism of the refined system into an index of `N`, followed by the comparison isomorphism
with `p`, is the structure morphism of the source's wide fibre product followed by the underlying
morphism of `N`. This is `Stacks.SitePoints.UniformRefinement.refMap_π` read through
`Stacks.SitePoints.UniformRefinement.refIso`, and it is what turns the two conclusions of Stacks
00YP into statements about the wide fibre products. -/
private lemma refSystem_map_comp_refIso_hom_app {x : Node J p κ} {j : N}
    (m : x ⟶ (refIncl J p κ).obj j) :
    (refSystem hpb κ).map m ≫ (refIso hpb κ).hom.app j = (inter hpb x.j x.S).π ≫ p.map m.down.1 :=
  refMap_π hpb m

/-- The defining square of a node's wide fibre product, read through
`Stacks.SitePoints.UniformRefinement.refSystem` and `Stacks.SitePoints.UniformRefinement.refIso`:
the left-hand side is the form `Stacks.SitePoints.UniformRefinement.toBase` takes at an instruction
whose transport morphism is the identity. -/
private lemma refSystem_map_toRefIncl_comp (x : Node J p κ) {W : C} (ff : p.obj x.j ⟶ W) :
    (inter hpb x.j x.S).π ≫ p.map (𝟙 x.j) ≫ ff =
      (refSystem hpb κ).map (toRefIncl x) ≫ (refIso hpb κ).hom.app x.j ≫ ff :=
  (refMap_π_assoc hpb (toRefIncl x) ff).symm

end Node

end Stacks.SitePoints.UniformRefinement

end
