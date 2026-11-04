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
import all StacksFrontier.CategoryTheory.Sites.Point.CriterionForExistenceOfPoints.RefinedIndexCategory

/-!
# The uniform refinement (Stacks 00YP) and the sections of closed sieves

The global choice of members of the coverings, the essential smallness of the refined index
category, and Stacks 00YP
(`CategoryTheory.GrothendieckTopology.exists_refinement_forall_covering_of_ne`);
then the start of Deligne's criterion: the sections of the sheaf of closed sieves.
Split out of `StacksFrontier.CategoryTheory.Sites.Point.CriterionForExistenceOfPoints`.
-/

section

universe w w' v u t u₁ v₂ u₂
open CategoryTheory Limits Opposite

namespace Stacks.SitePoints.UniformRefinement

/-! ### The global choice of members of the coverings -/

section Good

variable {C : Type u} [Category.{v} C] {N : Type u₁} [SmallCategory N] [IsCofiltered N]
  {J : GrothendieckTopology C} {F : Cᵒᵖ ⥤ Type w} {p : N ⥤ C}
  (hpb :
    ∀ {W : C} {ι : Type t} [Finite ι] {Y : ι → C} (g : ∀ k, Y k ⟶ W),
      Sieve.ofArrows Y g ∈ J W → ∀ (X : C) (h : X ⟶ W) (k : ι), HasPullback h (g k))

attribute [local instance] nodeCategory

/-- Restriction along a morphism admitting a section — in particular along an isomorphism — is
injective on sections of a presheaf. -/
private lemma map_op_injective_of_comp_eq_id {X Y : C} (π : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ π = 𝟙 Y)
    {x y : F.obj (op Y)} (h : F.map π.op x = F.map π.op y) : x = y := by
  have key : ∀ zz : F.obj (op Y), F.map s.op (F.map π.op zz) = zz := by
    intro zz
    rw [← F.map_comp_apply, ← op_comp, hs, op_id, F.map_id]
    rfl
  exact (key x).symm.trans ((congrArg (F.map s.op) h).trans (key y))

/-- Let `{g k : Y k ⟶ W}` be a covering of the site and let `u : X ⟶ W` be a morphism along which
the fibre products `X ×_W Y k` exist. Then two sections of a separated presheaf `F` over `X'` have
the same restriction along a morphism `v : X ⟶ X'` as soon as their restrictions along the
composites
`X ×_W Y k ⟶ X ⟶ X'` agree, because the fibre products `X ×_W Y k` cover `X`.

This is the only place where the topology, and the separatedness of `F`, are used. It is the same
statement as `Stacks.SitePoints.RefinementStep.map_eq_of_forall_pullback_fst_comp_eq`, which is the
analogous step of Stacks 00YO; the two files do not import one another, so a
home for it in the library — a section on the fibre products of a covering — is what the
duplication asks for. -/
private alias map_eq_of_forall_pullback_fst_comp_eq :=
  Stacks.SitePoints.RefinementStep.map_eq_of_forall_pullback_fst_comp_eq

/-- A *partial choice* of members of the coverings: a set of pairs `⟨c, k⟩` prescribing at most one
member of the covering of each covering datum. -/
private def Functional (T : Set (Σ c : CovData J p, Fin c.n)) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, x.1 = y.1 → x = y

/-- A partial choice is *good* for the germs of `a` and `a'` when those germs stay distinct over
the wide fibre product of every finite set of instructions all of whose prescriptions it makes and
which prescribes each covering datum at most once. This is
`Stacks.SitePoints.UniformRefinement.Good` for a partial choice; a total one is the special case
where the set of pairs is the graph of a function.
-/
private def GoodOn (T : Set (Σ c : CovData J p, Fin c.n)) (j₀ : N) (a a' : F.obj (op (p.obj j₀))) :
    Prop :=
  ∀ (j : N) (S : Finset (Instr J p j)),
    (∀ i ∈ S, (⟨i.c, i.k⟩ : Σ c : CovData J p, Fin c.n) ∈ T) →
      (∀ i ∈ S, ∀ i' ∈ S, i.c = i'.c → i = i') →
      ∀ ψ : j ⟶ j₀,
        F.map ((inter hpb j S).π ≫ p.map ψ).op a ≠ F.map ((inter hpb j S).π ≫ p.map ψ).op a'

omit [IsCofiltered N] in
/-- A partial choice extends to a total one: at a covering datum it prescribes, the extension takes
its prescription — which is unique because the choice is partial — and elsewhere the first member
of the covering, which exists by `Stacks.SitePoints.UniformRefinement.CovData.pos`. -/
private lemma exists_total_extension (T : Set (Σ c : CovData J p, Fin c.n)) (hfun : Functional T) :
    ∃ κ : ∀ c : CovData J p, Fin c.n,
      ∀ (c : CovData J p) (k : Fin c.n), (⟨c, k⟩ : Σ c : CovData J p, Fin c.n) ∈ T → κ c = k := by
  classical
  have hchoice :
    ∀ c : CovData J p,
      ∃ k : Fin c.n,
        ((⟨c, k⟩ : Σ c : CovData J p, Fin c.n) ∈ T) ∨
          ∀ k' : Fin c.n, (⟨c, k'⟩ : Σ c : CovData J p, Fin c.n) ∉ T := by
    intro c
    by_cases h : ∃ k : Fin c.n, (⟨c, k⟩ : Σ c : CovData J p, Fin c.n) ∈ T
    · exact ⟨h.choose, Or.inl h.choose_spec⟩
    · push Not at h
      exact ⟨⟨0, c.pos⟩, Or.inr h⟩
  choose κ hκ0 using hchoice
  refine ⟨κ, fun c k hk => ?_⟩
  rcases hκ0 c with h | h
  · simpa using hfun _ h _ hk rfl
  · exact absurd hk (h k)

omit [IsCofiltered N] in
/-- The empty partial choice is good: the wide fibre product over no instruction at all is
`p j`. -/
private lemma goodOn_empty (j₀ : N) (a a' : F.obj (op (p.obj j₀)))
    (haa' : ∀ (j : N) (φ : j ⟶ j₀), F.map (p.map φ).op a ≠ F.map (p.map φ).op a') :
    GoodOn hpb ∅ j₀ a a' := by
  intro j S hmem _ ψ heq
  have hS : S = ∅ := Finset.eq_empty_of_forall_notMem fun i hi => absurd (hmem i hi) (by simp)
  subst hS
  refine haa' j ψ ?_
  refine
    map_op_injective_of_comp_eq_id ((inter hpb j (∅ : Finset (Instr J p j))).π)
      (interEmptyIso hpb j).inv (interEmptyIso hpb j).inv_hom_id ?_
  rw [← F.map_comp_apply, ← F.map_comp_apply, ← op_comp]
  exact heq

omit [IsCofiltered N] in
/-- The union of a chain of partial choices is a partial choice: two pairs of the union lie in a
common member of the chain. -/
private lemma functional_sUnion {ch : Set (Set (Σ c : CovData J p, Fin c.n))}
    (hcha : IsChain (· ⊆ ·) ch) (h : ∀ T ∈ ch, Functional T) : Functional (⋃₀ ch) := by
  rintro x ⟨s, hs, hxs⟩ y ⟨s', hs', hys'⟩ hxy
  obtain ⟨T, hT, hsT, hs'T⟩ := hcha.directedOn s hs s' hs'
  exact h T hT x (hsT hxs) y (hs'T hys') hxy

omit [IsCofiltered N] in
/-- **The union of a chain of good partial choices is good.** A finite set of instructions all of
whose prescriptions the union makes prescribes finitely many pairs, so all of them are made by a
single member of the chain, and that member is good at the set. -/
private lemma goodOn_sUnion {j₀ : N} {a a' : F.obj (op (p.obj j₀))}
    {ch : Set (Set (Σ c : CovData J p, Fin c.n))} (hne : ch.Nonempty) (hcha : IsChain (· ⊆ ·) ch)
    (h : ∀ T ∈ ch, GoodOn hpb T j₀ a a') : GoodOn hpb (⋃₀ ch) j₀ a a' := by
  intro j S hmem hinj ψ
  obtain ⟨T, hT, hsub⟩ :=
    DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion hne hcha.directedOn
      (S.finite_toSet.image fun i : Instr J p j => (⟨i.c, i.k⟩ : Σ c : CovData J p, Fin c.n))
      (Set.image_subset_iff.2 hmem)
  exact h T hT j S (fun i hi => hsub ⟨i, hi, rfl⟩) hinj ψ

open scoped Classical in
omit [IsCofiltered N] in
/-- **The witnesses of Deligne's step.** Let `T` be a good partial choice, maximal among the good
ones, prescribing no member of the covering of a covering datum `c₀`. Then for every member `k` of
that covering there are an index `jw` of `N`, a finite set `Sw` of instructions at `jw` prescribing
each covering datum at most once, a morphism `ph : jw ⟶ (sk N).obj c₀.jj` and a morphism
`psw : jw ⟶ j₀` such that `⟨c₀, k, ph⟩ ∈ Sw`, such that `T` prescribes every other instruction of
`Sw`, and such that the germs of `a` and `a'` agree over the wide fibre product of `Sw` along
`psw`.

Adjoining `⟨c₀, k⟩` to `T` keeps it a partial choice, `T` prescribing nothing for `c₀`; so by
maximality it is no longer good, and `Sw` is a set of instructions witnessing that. It prescribes
`c₀`, or else it would already witness the failure of goodness of `T` itself, and it prescribes it
once, and with the member `k`, prescribing each covering datum at most once. -/
private lemma exists_witness_of_maximal (j₀ : N) (a a' : F.obj (op (p.obj j₀)))
    {T : Set (Σ c : CovData J p, Fin c.n)} (hfun : Functional T) (hgood : GoodOn hpb T j₀ a a')
    (hmax :
      ∀ T' : Set (Σ c : CovData J p, Fin c.n),
        Functional T' → GoodOn hpb T' j₀ a a' → T ⊆ T' → T' ⊆ T)
    (c₀ : CovData J p) (hc : ∀ k : Fin c₀.n, (⟨c₀, k⟩ : Σ c : CovData J p, Fin c.n) ∉ T)
    (k : Fin c₀.n) :
    ∃ (jw : N) (Sw : Finset (Instr J p jw)) (ph : jw ⟶ (sk N).obj c₀.jj) (psw : jw ⟶ j₀),
      (⟨c₀, k, ph⟩ : Instr J p jw) ∈ Sw ∧
        (∀ i ∈ Sw, ∀ i' ∈ Sw, i.c = i'.c → i = i') ∧
        (∀ i ∈ Sw.erase (⟨c₀, k, ph⟩ : Instr J p jw),
          (⟨i.c, i.k⟩ : Σ c : CovData J p, Fin c.n) ∈ T) ∧
        F.map ((inter hpb jw Sw).π ≫ p.map psw).op a =
          F.map ((inter hpb jw Sw).π ≫ p.map psw).op a' := by
  classical
  -- No pair of `T` has `c₀` as its covering datum, so adjoining `⟨c₀, k⟩` keeps `T` partial.
  have hc' : ∀ y ∈ T, y.1 ≠ c₀ := by
    rintro ⟨cy, ky⟩ hy rfl
    exact hc ky hy
  have hfun' : Functional (insert (⟨c₀, k⟩ : Σ c : CovData J p, Fin c.n) T) := by
    intro x hx y hy hxy
    rcases Set.mem_insert_iff.1 hx with rfl | hx
    · rcases Set.mem_insert_iff.1 hy with rfl | hy
      · rfl
      · exact absurd hxy.symm (hc' y hy)
    · rcases Set.mem_insert_iff.1 hy with rfl | hy
      · exact absurd hxy (hc' x hx)
      · exact hfun x hx y hy hxy
  -- By maximality it is no longer good, and a witness to that is a set of instructions.
  have hbad : ¬GoodOn hpb (insert (⟨c₀, k⟩ : Σ c : CovData J p, Fin c.n) T) j₀ a a' := fun hg =>
    hc k (hmax _ hfun' hg (Set.subset_insert _ _) (Set.mem_insert _ _))
  obtain ⟨jw, Sw, hmemw, hinjw, psw, hheqw⟩ :
    ∃ (jw : N) (Sw : Finset (Instr J p jw)),
      (∀ i ∈ Sw,
          (⟨i.c, i.k⟩ : Σ c : CovData J p, Fin c.n) ∈
            insert (⟨c₀, k⟩ : Σ c : CovData J p, Fin c.n) T) ∧
        (∀ i ∈ Sw, ∀ i' ∈ Sw, i.c = i'.c → i = i') ∧
        ∃ psw : jw ⟶ j₀,
          F.map ((inter hpb jw Sw).π ≫ p.map psw).op a =
            F.map ((inter hpb jw Sw).π ≫ p.map psw).op a' :=
    by
    by_contra hno
    exact hbad fun j S hmem hinj ψ heq => hno ⟨j, S, hmem, hinj, ψ, heq⟩
  -- Each instruction of `Sw` is either one for `c₀` with the member `k`, or prescribed by `T`.
  have hcase : ∀ i ∈ Sw, (∃ ph, i = (⟨c₀, k, ph⟩ : Instr J p jw)) ∨
      (⟨i.c, i.k⟩ : Σ c : CovData J p, Fin c.n) ∈ T := by
    rintro ⟨ci, ki, φi⟩ hi
    rcases Set.mem_insert_iff.1 (hmemw _ hi) with he | he
    · simp only [Sigma.mk.injEq] at he
      obtain ⟨rfl, h2⟩ := he
      obtain rfl : ki = k := eq_of_heq h2
      exact Or.inl ⟨φi, rfl⟩
    · exact Or.inr he
  -- It prescribes `c₀`, or else it would witness the failure of goodness of `T` itself.
  obtain ⟨ph, hph⟩ : ∃ ph : jw ⟶ (sk N).obj c₀.jj, (⟨c₀, k, ph⟩ : Instr J p jw) ∈ Sw := by
    by_contra hno
    exact hgood jw Sw (fun i hi => (hcase i hi).resolve_left fun ⟨ph, h⟩ => hno ⟨ph, h ▸ hi⟩)
      hinjw psw hheqw
  -- Everything else it prescribes, `T` already prescribes.
  refine ⟨jw, Sw, ph, psw, hph, hinjw, fun i hi => ?_, hheqw⟩
  rcases hcase i (Finset.mem_of_mem_erase hi) with ⟨_, rfl⟩ | he
  · exact absurd (hinjw _ (Finset.mem_of_mem_erase hi) _ hph rfl) (Finset.ne_of_mem_erase hi)
  · exact he

/-- **A common refinement of finitely many admissible sets of instructions.** Let `T` be a partial
choice with total extension `κT`, let `S t` be a finite nonempty family of finite sets of
instructions, at indices `A t` of `N`, all of whose prescriptions `T` makes and each of which
prescribes a covering datum at most once, and let `g₁ t : A t ⟶ b₁` and `g₂ t : A t ⟶ b₂` be two
families of morphisms of `N`. Then there is a single index `z` below all the `A t` at which all the
`g₁ t` become one morphism and all the `g₂ t` become one morphism, carrying a finite set `S'` of
instructions with the same two properties into which every `S t` pulls back.

Each `S t` is the set of instructions of a node for `κT`, so, the nodes being cofiltered
(`Stacks.SitePoints.UniformRefinement.nodeIsCofiltered`),
`Stacks.SitePoints.UniformRefinement.exists_cone_forall_comp_eq` applies to them; discarding from
the instructions of the resulting node those whose prescription `T` does not make leaves `S'`, and
no pullback of an instruction of an `S t` is so discarded. -/
private lemma exists_common_refinement {T : Set (Σ c : CovData J p, Fin c.n)}
    {κT : ∀ c : CovData J p, Fin c.n}
    (hκT : ∀ (c : CovData J p) (k : Fin c.n), (⟨c, k⟩ : Σ c : CovData J p, Fin c.n) ∈ T → κT c = k)
    {ι : Type*} [Finite ι] [Nonempty ι] {A : ι → N} (S : ∀ t, Finset (Instr J p (A t)))
    (hmem : ∀ (t : ι), ∀ i ∈ S t, (⟨i.c, i.k⟩ : Σ c : CovData J p, Fin c.n) ∈ T)
    (hinj : ∀ (t : ι), ∀ i ∈ S t, ∀ i' ∈ S t, i.c = i'.c → i = i') {b₁ b₂ : N} (g₁ : ∀ t, A t ⟶ b₁)
    (g₂ : ∀ t, A t ⟶ b₂) :
    ∃ (z : N) (S' : Finset (Instr J p z)) (u : ∀ t, z ⟶ A t) (f₁ : z ⟶ b₁) (f₂ : z ⟶ b₂),
      (∀ i ∈ S', (⟨i.c, i.k⟩ : Σ c : CovData J p, Fin c.n) ∈ T) ∧
        (∀ i ∈ S', ∀ i' ∈ S', i.c = i'.c → i = i') ∧
        (∀ (t : ι), ∀ i ∈ S t, pullInstr (u t) i ∈ S') ∧
        (∀ t, u t ≫ g₁ t = f₁) ∧ (∀ t, u t ≫ g₂ t = f₂) := by
  classical
  have : IsCofiltered (Node J p κT) := nodeIsCofiltered
  obtain ⟨zz, vv, ff₁, ff₂, h₁, h₂⟩ :=
    exists_cone_forall_comp_eq
      (fun t => (⟨A t, S t, fun i hi => (hκT i.c i.k (hmem t i hi)).symm, hinj t⟩ : Node J p κT))
      (⟨b₁, ∅, fun _ hi => notMem_empty_elim hi, fun _ hi => notMem_empty_elim hi⟩ : Node J p κT)
      (⟨b₂, ∅, fun _ hi => notMem_empty_elim hi, fun _ hi => notMem_empty_elim hi⟩ : Node J p κT)
      (fun t => nodeHom (g₁ t) fun _ hi => notMem_empty_elim hi)
      (fun t => nodeHom (g₂ t) fun _ hi => notMem_empty_elim hi)
  exact
    ⟨zz.j, zz.S.filter fun i => (⟨i.c, i.k⟩ : Σ c : CovData J p, Fin c.n) ∈ T, fun t =>
      (vv t).down.1, ff₁.down.1, ff₂.down.1, fun _ hi => (Finset.mem_filter.1 hi).2,
      fun i hi i' hi' h => zz.inj i (Finset.mem_filter.1 hi).1 i' (Finset.mem_filter.1 hi').1 h,
      fun t i hi => Finset.mem_filter.2 ⟨(vv t).down.2 i hi, hmem t i hi⟩, fun t =>
      (nodeComp_down (vv t) _).symm.trans (nodeHom_down_congr (h₁ t)), fun t =>
      (nodeComp_down (vv t) _).symm.trans (nodeHom_down_congr (h₂ t))⟩

/-- **Deligne's step.** A maximal good partial choice prescribes a member of the covering of every
covering datum.

Were a covering datum `c₀` unprescribed, then each member `k` of its covering would come with a
witness to the failure of goodness of the choice extended by `⟨c₀, k⟩`
(`Stacks.SitePoints.UniformRefinement.exists_witness_of_maximal`): an index `jw k`, an admissible
set of instructions `Sw k` at it containing exactly one instruction `⟨c₀, k, phw k⟩` prescribing
`c₀`, and a morphism `psw k : jw k ⟶ j₀` over which the germs of `a` and `a'` agree. Deleting that
instruction leaves a set the partial choice prescribes, so
`Stacks.SitePoints.UniformRefinement.exists_common_refinement` puts a single index below all the
`jw k` at which all the `phw k` and all the `psw k` become one morphism `ph`, resp. `ps`, and which
carries a set `S'` that the partial choice prescribes and that still receives the pullbacks of the
`(Sw k).erase _`, so that adjoining `⟨c₀, k, ph⟩` to it gives, for each `k`, an admissible set for
the extended choice mapping to `Sw k`. The object of that set is the `k`-th member of the pullback
along `X' ⟶ c₀.W` of the covering of `c₀`, where `X'` is the object of `S'`, so the germs of `a`
and `a'` agree on a covering of `X'`, hence on `X'` because `F` is separated — contradicting the
goodness of the partial choice at `S'`. -/
private lemma exists_mem_of_maximal (hF : Presieve.IsSeparated J F) (j₀ : N)
    (a a' : F.obj (op (p.obj j₀))) {T : Set (Σ c : CovData J p, Fin c.n)} (hfun : Functional T)
    (hgood : GoodOn hpb T j₀ a a')
    (hmax :
      ∀ T' : Set (Σ c : CovData J p, Fin c.n),
        Functional T' → GoodOn hpb T' j₀ a a' → T ⊆ T' → T' ⊆ T)
    (c₀ : CovData J p) : ∃ k : Fin c₀.n, (⟨c₀, k⟩ : Σ c : CovData J p, Fin c.n) ∈ T := by
  classical
  by_contra hcon
  push Not at hcon
  -- One witness to the failure of goodness of `T ∪ {⟨c₀, k⟩}` for each member `k`.
  choose jw Sw phw psw hphw hinjw hmem0 hheqw using fun k : Fin c₀.n =>
    exists_witness_of_maximal hpb j₀ a a' hfun hgood hmax c₀ hcon k
  obtain ⟨κT, hκT⟩ := exists_total_extension T hfun
  have : Nonempty (Fin c₀.n) := ⟨⟨0, c₀.pos⟩⟩
  -- One index below all the witnesses, at which all the `phw k` and all the `psw k` agree,
  -- carrying a set `S'` of instructions prescribed by `T` receiving the pullbacks of all the
  -- witnesses.
  obtain ⟨z, S', uu, ph, ps, hS'mem, hS'inj, hS'pull, hph, hps⟩ :=
    exists_common_refinement hκT (fun k => (Sw k).erase (⟨c₀, k, phw k⟩ : Instr J p (jw k))) hmem0
      (fun k i hi i' hi' h =>
        hinjw k i (Finset.mem_of_mem_erase hi) i' (Finset.mem_of_mem_erase hi') h)
      phw psw
  -- `T` prescribes no member of the covering of `c₀`, so neither does `S'`; and adjoining
  -- `⟨c₀, k, ph⟩` to `S'` gives a set receiving all of `Sw k`.
  have hnot : ∀ k : Fin c₀.n, (⟨c₀, k, ph⟩ : Instr J p z) ∉ S' := fun k hk => hcon k (hS'mem _ hk)
  have hpull2 :
    ∀ (k : Fin c₀.n) (i : Instr J p (jw k)),
      i ∈ Sw k → pullInstr (uu k) i ∈ insert (⟨c₀, k, ph⟩ : Instr J p z) S' := by
    intro k i hi
    by_cases he : i = (⟨c₀, k, phw k⟩ : Instr J p (jw k))
    · refine Finset.mem_insert.2 (Or.inl ?_)
      rw [he]
      rw [pullInstr_mk, hph k]
    · exact Finset.mem_insert_of_mem (hS'pull k i (Finset.mem_erase.2 ⟨he, hi⟩))
  -- The members of the pullback of the covering of `c₀` to the object of `S'`, each of which maps
  -- to the object of the witness it refines.
  have hpk : ∀ k : Fin c₀.n, HasPullback ((inter hpb z S').π ≫ p.map ph ≫ c₀.f) (c₀.g k) :=
    fun k => hasPullback_covData hpb c₀ (inter hpb z S').X ((inter hpb z S').π ≫ p.map ph ≫ c₀.f) k
  choose qq hqq using fun k : Fin c₀.n => exists_hom_comp_π_eq hpb (hnot k) (uu k) (hpull2 k)
  -- The germs agree on every member of that covering, hence on the object of `S'`.
  refine hgood z S' hS'mem hS'inj ps ?_
  refine
    map_eq_of_forall_pullback_fst_comp_eq hF c₀.g c₀.covering
      ((inter hpb z S').π ≫ p.map ph ≫ c₀.f) ((inter hpb z S').π ≫ p.map ps) ?_
  intro k
  have hfac :
    pullback.fst ((inter hpb z S').π ≫ p.map ph ≫ c₀.f) (c₀.g k) ≫
        ((inter hpb z S').π ≫ p.map ps) =
      qq k ≫ ((inter hpb (jw k) (Sw k)).π ≫ p.map (psw k)) := by
    rw [← Category.assoc (qq k), hqq k, ← hps k, Functor.map_comp]
    simp
  rw [hfac, op_comp, F.map_comp_apply, F.map_comp_apply, hheqw k]

/-- A global choice `κ` of members of the coverings is *good* for the germs of `a` and `a'` when
those germs stay distinct over the object of every node, i.e. over the wide fibre product of every
finite set of instructions that is consistent with `κ` and prescribes each covering datum at most
once. -/
private def Good (κ : ∀ c : CovData J p, Fin c.n) (j₀ : N) (a a' : F.obj (op (p.obj j₀))) : Prop :=
  ∀ (x : Node J p κ) (ψ : x.j ⟶ j₀),
    F.map ((inter hpb x.j x.S).π ≫ p.map ψ).op a ≠ F.map ((inter hpb x.j x.S).π ≫ p.map ψ).op a'

/-- **The mathematical content of Stacks 00YP.** A global choice of members of the coverings exists
for which the germs of `a` and `a'` stay distinct over every node.

By Zorn's lemma on the partial choices, as described in the module docstring: the germs stay
distinct over the object of the empty set of instructions, which is `p j`, by `haa'`
(`Stacks.SitePoints.UniformRefinement.goodOn_empty`); the union of a chain of good partial choices
is good, a finite set of instructions being one for a single member of the chain; and a maximal
good partial choice is total (`Stacks.SitePoints.UniformRefinement.exists_mem_of_maximal`). -/
private lemma exists_good (hF : Presieve.IsSeparated J F) (j₀ : N) (a a' : F.obj (op (p.obj j₀)))
    (haa' : ∀ (j : N) (φ : j ⟶ j₀), F.map (p.map φ).op a ≠ F.map (p.map φ).op a') :
    ∃ κ : ∀ c : CovData J p, Fin c.n, Good hpb κ j₀ a a' := by
  classical
  obtain ⟨T, -, hTmem, hTmax⟩ :=
    zorn_subset_nonempty
      {T : Set (Σ c : CovData J p, Fin c.n) | Functional T ∧ GoodOn hpb T j₀ a a'}
      (fun ch hch hcha hne =>
        ⟨⋃₀ ch,
          ⟨functional_sUnion hcha fun _ hT => (hch hT).1,
            goodOn_sUnion hpb hne hcha fun _ hT => (hch hT).2⟩,
          fun _ hs => Set.subset_sUnion_of_mem hs⟩)
      ∅ ⟨fun x hx => absurd hx (by simp), goodOn_empty hpb j₀ a a' haa'⟩
  choose κ hκ using
    exists_mem_of_maximal hpb hF j₀ a a' hTmem.1 hTmem.2 fun _ h1 h2 hsub => hTmax ⟨h1, h2⟩ hsub
  refine ⟨κ, fun x ψ => hTmem.2 x.j x.S (fun i hi => ?_) x.inj ψ⟩
  rw [show (⟨i.c, i.k⟩ : Σ c : CovData J p, Fin c.n) = ⟨i.c, κ i.c⟩ from
      congrArg (fun kk : Fin i.c.n => (⟨i.c, kk⟩ : Σ c : CovData J p, Fin c.n))
        (x.consistent i hi)]
  exact hκ i.c

end Good

/-! ### The refined index category is essentially small -/

section Small

variable {C : Type u} [Category.{v} C] [Small.{w'} C] [LocallySmall.{w'} C] {N : Type u₁}
  [SmallCategory N] [EssentiallySmall.{w'} N] {J : GrothendieckTopology C} {p : N ⥤ C}
  {κ : ∀ c : CovData J p, Fin c.n}

attribute [local instance] nodeCategory

/-- The covering data are `w'`-small: a covering datum is objects and morphisms of `C` together
with an object of the skeleton of `N`. -/
private lemma small_covData : Small.{w'} (CovData J p) := by
  apply
    small_of_injective (f := fun c : CovData J p =>
      (⟨c.n, c.W, c.Y, c.g, c.jj, c.f⟩ :
        Σ (n : ℕ) (W : C) (Y : Fin n → C),
          (∀ k, Y k ⟶ W) × Σ jj : Skeleton N, (p.obj ((sk N).obj jj) ⟶ W)))
  intro c c' h
  obtain ⟨n, pos, W, Y, g, cov, jj, f⟩ := c
  obtain ⟨n', pos', W', Y', g', cov', jj', f'⟩ := c'
  iterate 3
    simp only [heq_eq_eq, Sigma.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
  simp only [heq_eq_eq, Prod.mk.injEq, Sigma.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

/-- An instruction is `w'`-small data: a covering datum, a member of its covering, and a morphism
of `N`. -/
private lemma small_instr (j : N) : Small.{w'} (Instr J p j) := by
  have := small_covData (J := J) (p := p)
  apply
    small_of_injective (f := fun i : Instr J p j =>
      (⟨i.c, i.k, i.φ⟩ : Σ c : CovData J p, Fin c.n × (j ⟶ (sk N).obj c.jj)))
  intro i i' h
  obtain ⟨ci, ki, φi⟩ := i
  obtain ⟨ci', ki', φi'⟩ := i'
  simp only [Sigma.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  simp only [heq_eq_eq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

private lemma small_finset_instr (j : N) : Small.{w'} (Finset (Instr J p j)) := by
  have := small_instr (J := J) (p := p) j
  exact
    small_of_injective (f := fun s : Finset (Instr J p j) => (↑s : Set (Instr J p j)))
      Finset.coe_injective

omit [Small.{w', u} C] [LocallySmall.{w', v, u} C] in
/-- Morphisms of nodes are `w'`-small: a morphism of nodes is a morphism of `N`. -/
private lemma small_nodeHom (x y : Node J p κ) : Small.{w'} (x ⟶ y) :=
  small_of_injective (f := fun m : x ⟶ y => (m.down : x.j ⟶ y.j)) fun _ _ h => nodeHom_ext _ _ h

omit [Small.{w', u} C] [LocallySmall.{w', v, u} C] in
private lemma locallySmall_node : LocallySmall.{w'} (Node J p κ)
    where
  hom_small := small_nodeHom

/-- A node whose index is presented as the image of an object of the skeleton of `N`. These are
`w'`-small, and every node is isomorphic to one of them, so they are a small model of the refined
index category. -/
private structure SkNode (J : GrothendieckTopology C) (p : N ⥤ C)
    (κ : ∀ c : CovData J p, Fin c.n) where
  /-- The object of the skeleton of `N` whose image is the index. -/
  jj : Skeleton N
  /-- The finite set of instructions imposed at the index. -/
  S : Finset (Instr J p ((sk N).obj jj))
  /-- The chosen members are the globally prescribed ones. -/
  consistent : ∀ i ∈ S, i.k = κ i.c
  /-- No covering datum is prescribed twice. -/
  inj : ∀ i ∈ S, ∀ i' ∈ S, i.c = i'.c → i = i'

/-- The node underlying an object of `Stacks.SitePoints.UniformRefinement.SkNode`. -/
private noncomputable def SkNode.toNode (x : SkNode J p κ) : Node J p κ :=
  ⟨(sk N).obj x.jj, x.S, x.consistent, x.inj⟩

private lemma small_skNode : Small.{w'} (SkNode J p κ) := by
  have : ∀ jj : Skeleton N, Small.{w'} (Finset (Instr J p ((sk N).obj jj))) := fun jj =>
    small_finset_instr _
  apply
    small_of_injective (f := fun x : SkNode J p κ =>
      (⟨x.jj, x.S⟩ : Σ jj : Skeleton N, Finset (Instr J p ((sk N).obj jj))))
  intro x y h
  obtain ⟨jjx, Sx, hx1, hx2⟩ := x
  obtain ⟨jjy, Sy, hy1, hy2⟩ := y
  simp only [Sigma.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  simp only [heq_eq_eq] at h
  subst h
  rfl

omit [Small.{w', u} C] [LocallySmall.{w', v, u} C] [EssentiallySmall.{w', u₁, u₁} N] in
/-- Every node is isomorphic to one whose index is presented as the image of an object of the
skeleton of `N`: the index is transported along `Stacks.SitePoints.UniformRefinement.skPreIso`, and
the instructions are pulled back along that isomorphism. -/
private lemma essSurj_inducedFunctor_toNode :
    (inducedFunctor (SkNode.toNode : SkNode J p κ → Node J p κ)).EssSurj
    where
  mem_essImage x := by
    classical
    have hback : ∀ i ∈ (x.pull (skPreIso x.j).hom).S, pullInstr (skPreIso x.j).inv i ∈ x.S := by
      intro i hi
      obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.1 hi
      rw [pullInstr_pullInstr_of_comp_eq_id _ _ (skPreIso x.j).inv_hom_id]
      exact hi₀
    refine
      ⟨⟨skPre x.j, (x.pull (skPreIso x.j).hom).S, (x.pull _).consistent, (x.pull _).inj⟩,
        ⟨nodeHom (skPreIso x.j).hom fun _ hi => Finset.mem_image_of_mem _ hi,
          nodeHom (skPreIso x.j).inv hback, ?_, ?_⟩⟩
    · exact nodeHom_ext _ _ (skPreIso x.j).hom_inv_id
    · exact nodeHom_ext _ _ (skPreIso x.j).inv_hom_id

/-- The refined index category is essentially `w'`-small. It is not `w'`-small: its objects involve
an arbitrary index of `N`, which is only essentially `w'`-small. The nodes whose index is presented
as the image of an object of the skeleton (`Stacks.SitePoints.UniformRefinement.SkNode`) are
`w'`-small, the morphisms of nodes are `w'`-small, and the forgetful functor is an equivalence,
because a node transports along an isomorphism of `N`. -/
private lemma essentiallySmall_node : EssentiallySmall.{w'} (Node J p κ) := by
  have := locallySmall_node (J := J) (p := p) (κ := κ)
  have : Small.{w'} (InducedCategory (Node J p κ) (SkNode.toNode (κ := κ))) :=
    small_skNode (J := J) (p := p) (κ := κ)
  have : LocallySmall.{w'} (InducedCategory (Node J p κ) (SkNode.toNode (κ := κ))) :=
    locallySmall_of_faithful (inducedFunctor _)
  have := essSurj_inducedFunctor_toNode (J := J) (p := p) (κ := κ)
  have : (inducedFunctor (SkNode.toNode : SkNode J p κ → Node J p κ)).IsEquivalence := {}
  exact
    (essentiallySmall_congr
          (inducedFunctor (SkNode.toNode : SkNode J p κ → Node J p κ)).asEquivalence).1
      inferInstance

end Small

/-! ### Passing from the covering data to arbitrary finite coverings -/

section Reindex

/-- A covering of `W` indexed by the empty type forces any two sections of a separated presheaf
over an object of `C` lying over `W` to agree: the empty sieve is then a covering sieve of `W`,
hence its pullback is one of that object, and a section is determined by its restrictions along a
covering sieve. This is what rules out the empty covering, which the covering data exclude by
`Stacks.SitePoints.UniformRefinement.CovData.pos`. -/
private lemma map_eq_of_isEmpty {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F : Cᵒᵖ ⥤ Type w} (hF : Presieve.IsSeparated J F) {W : C} {ι : Type t} (hι : IsEmpty ι)
    {Y : ι → C} (g : ∀ k, Y k ⟶ W) (hg : Sieve.ofArrows Y g ∈ J W) {X : C} (u : X ⟶ W)
    (x y : F.obj (op X)) : x = y := by
  refine (hF _ (J.pullback_stable u hg)).ext fun Z α hα => ?_
  have hα' : (Sieve.ofArrows Y g).arrows (α ≫ u) := hα
  obtain ⟨k, -, -⟩ := (Sieve.mem_ofArrows_iff Y g (α ≫ u)).1 hα'
  exact hι.elim' k

/-- Naturality of the comparison isomorphism of a refinement transports a factorisation of a
section of `u'` along a morphism of `N`: if the section `p θ ≫ ff` at `j'` is covered at the index
`i` of the refinement, then so is `ff` at `j`, at the same index and through the same member of the
covering.

This is how the conclusion of `Stacks.SitePoints.UniformRefinement.key`, whose section is
represented at an object of the skeleton of `N`, is moved to an arbitrary index of `N`. -/
private lemma comp_eq_of_comp_eq {C : Type u} [Category.{v} C] {M : Type u₂} [Category.{v₂} M]
    {N : Type u₁} [SmallCategory N] {q : M ⥤ C} {e : N ⥤ M} {p : N ⥤ C} (ε : e ⋙ q ≅ p) {j' j : N}
    (θ : j' ⟶ j) {W : C} (ff : p.obj j ⟶ W) {i : M} (ψ : i ⟶ e.obj j') {Z : C} {h : q.obj i ⟶ Z}
    {gk : Z ⟶ W} (hh : h ≫ gk = q.map ψ ≫ ε.hom.app j' ≫ p.map θ ≫ ff) :
    h ≫ gk = q.map (ψ ≫ e.map θ) ≫ ε.hom.app j ≫ ff := by
  have hnat : q.map (e.map θ) ≫ ε.hom.app j = ε.hom.app j' ≫ p.map θ := ε.hom.naturality θ
  rw [hh, Functor.map_comp, Category.assoc, ← Category.assoc (q.map (e.map θ)), hnat,
    Category.assoc]

/-- The covering datum attached to a finite covering of `W` indexed by `Fin n`, a section
`ff : p j ⟶ W` of `u'(W)`, and an equivalence reindexing the covering: the index of the section is
recorded as the object `Stacks.SitePoints.UniformRefinement.skPre j` of the skeleton of `N`, the
section being composed with `Stacks.SitePoints.UniformRefinement.skPreIso`. Reindexing changes
neither the sieve the covering generates
(`Stacks.SitePoints.UniformRefinement.sieve_ofArrows_reindex`) nor its members. -/
private noncomputable def covDataOfCovering {C : Type u} [Category.{v} C] {N : Type u₁}
    [SmallCategory N] {J : GrothendieckTopology C} {p : N ⥤ C} {W : C} {ι : Type t} {Y : ι → C}
    (g : ∀ k, Y k ⟶ W) (hg : Sieve.ofArrows Y g ∈ J W) {n : ℕ} (hn : 0 < n) (τ : Fin n ≃ ι) (j : N)
    (ff : p.obj j ⟶ W) : CovData J p
    where
  n := n
  pos := hn
  W := W
  Y := fun k => Y (τ k)
  g := fun k => g (τ k)
  covering := by
    rw [sieve_ofArrows_reindex τ g]; exact hg
  jj := skPre j
  f := p.map (skPreIso j).hom ≫ ff

end Reindex

/-! ### Stacks 00YP -/

attribute [local instance] nodeCategory

/-- The conclusion of Stacks 00YP for the covering data, i.e. for finite coverings indexed by
`Fin n` with a section represented at an index of the skeleton of `N`. -/
private lemma key {C : Type u} [Category.{v} C] [Small.{w'} C] [LocallySmall.{w'} C] {N : Type u₁}
    [SmallCategory N] [IsCofiltered N] [EssentiallySmall.{w'} N] {J : GrothendieckTopology C}
    {F : Cᵒᵖ ⥤ Type w} {p : N ⥤ C}
    (hpb :
      ∀ {W : C} {ι : Type t} [Finite ι] {Y : ι → C} (g : ∀ k, Y k ⟶ W),
        Sieve.ofArrows Y g ∈ J W → ∀ (X : C) (h : X ⟶ W) (k : ι), HasPullback h (g k))
    (hF : Presieve.IsSeparated J F) (j₀ : N) (a a' : F.obj (op (p.obj j₀)))
    (haa' : ∀ (j : N) (φ : j ⟶ j₀), F.map (p.map φ).op a ≠ F.map (p.map φ).op a') :
    ∃ (M : Type (max u₁ u v)) (_ : SmallCategory M) (_ : IsCofiltered M) (_ :
      EssentiallySmall.{w'} M) (q : M ⥤ C) (e : N ⥤ M) (_ : e.Full) (_ : e.Faithful) (ε :
      e ⋙ q ≅ p),
      (∀ (i : M) (ψ : i ⟶ e.obj j₀),
          F.map (q.map ψ ≫ ε.hom.app j₀).op a ≠ F.map (q.map ψ ≫ ε.hom.app j₀).op a') ∧
        ∀ c : CovData J p,
          ∃ (k : Fin c.n) (i : M) (ψ : i ⟶ e.obj ((sk N).obj c.jj)) (h : q.obj i ⟶ c.Y k),
            h ≫ c.g k = q.map ψ ≫ ε.hom.app ((sk N).obj c.jj) ≫ c.f := by
  obtain ⟨κ, hκ⟩ := exists_good hpb hF j₀ a a' haa'
  refine
    ⟨Node J p κ, nodeCategory J p κ, nodeIsCofiltered, essentiallySmall_node, refSystem hpb κ,
      refIncl J p κ, refIncl_full, refIncl_faithful, refIso hpb κ, ?_, ?_⟩
  · intro x m
    rw [refSystem_map_comp_refIso_hom_app]
    exact hκ x m.down.1
  · intro c
    refine
      ⟨κ c, singletonNode κ c, toRefIncl (singletonNode κ c),
        (inter hpb (singletonNode κ c).j (singletonNode κ c).S).y (singletonNodeInstr κ c), ?_⟩
    exact
      ((inter hpb (singletonNode κ c).j (singletonNode κ c).S).fac (singletonNodeInstr κ c)).trans
        (refSystem_map_toRefIncl_comp hpb (singletonNode κ c) c.f)

end Stacks.SitePoints.UniformRefinement

attribute [local instance] Stacks.SitePoints.UniformRefinement.nodeCategory

namespace CategoryTheory.GrothendieckTopology

@[expose] public section

open Stacks.SitePoints.UniformRefinement in
/-- **Stacks 00YP.** Let `(C, J)` be a site in which the members of a finite covering admit fibre
products along arbitrary morphisms to its base (`hpb`), let `F` be a separated presheaf of sets on
`C` and let `p : N ⥤ C` be a cofiltered system in `C`, with associated fibre functor
`u'(X) = colim_j Mor(p j, X)` and stalk functor `F ↦ F_{p'} = colim_j F(p j)`. Let `s ≠ s'` be two
germs in `F_{p'}`, represented by `a, a' : F(p j₀)`.

Then the system can be refined — there are a cofiltered system `q : M ⥤ C`, a fully faithful
`e : N ⥤ M` and an isomorphism `ε : e ⋙ q ≅ p` exhibiting `p` as the restriction of `q` — in such a
way that the two germs stay distinct in `F_p` and that, for every finite covering `{g k : Y k ⟶ W}`
of the site and every section `f : p j ⟶ W` of `u'(W)`, the image of `f` in `u(W)` lies in the
image of `u(Y k)` for one of the members `g k` of the covering. Moreover the refined index category
is no larger than the data it is assembled from: if `C` is `w'`-small with `w'`-small hom types and
`N` is essentially `w'`-small, then so is `M`, so the refinement can in turn be fed back into the
construction of a point of the site and the lemma iterated.

Unlike `CategoryTheory.GrothendieckTopology.exists_refinement_of_ne` (Stacks 00YO), the covering
and the section are not fixed in advance: one refinement works for all of them at once. -/
@[stacks 00YP "The main step of Deligne's criterion: a cofiltered system can be refined so as to
  keep two germs of a separated presheaf distinct while every section of `u'` becomes covered by
  every finite covering of the site.", sga "4 VI 9.2", sga "4 VI 9.4"]
public theorem exists_refinement_forall_covering_of_ne {C : Type u} [Category.{v} C] [Small.{w'} C]
    [LocallySmall.{w'} C] (J : GrothendieckTopology C) {F : Cᵒᵖ ⥤ Type w}
    (hF : Presieve.IsSeparated J F)
    (hpb :
      ∀ {W : C} {ι : Type t} [Finite ι] {Y : ι → C} (g : ∀ k, Y k ⟶ W),
        Sieve.ofArrows Y g ∈ J W → ∀ (X : C) (h : X ⟶ W) (k : ι), HasPullback h (g k))
    {N : Type u₁} [SmallCategory N] [IsCofiltered N] [EssentiallySmall.{w'} N] (p : N ⥤ C) (j₀ : N)
    (a a' : F.obj (op (p.obj j₀)))
    (haa' : ∀ (j : N) (φ : j ⟶ j₀), F.map (p.map φ).op a ≠ F.map (p.map φ).op a') :
    ∃ (M : Type (max u₁ u v)) (_ : SmallCategory M) (_ : IsCofiltered M) (_ :
      EssentiallySmall.{w'} M) (q : M ⥤ C) (e : N ⥤ M) (_ : e.Full) (_ : e.Faithful) (ε :
      e ⋙ q ≅ p),
      (∀ (i : M) (ψ : i ⟶ e.obj j₀),
          F.map (q.map ψ ≫ ε.hom.app j₀).op a ≠ F.map (q.map ψ ≫ ε.hom.app j₀).op a') ∧
        ∀ {W : C} {ι : Type t} [Finite ι] {Y : ι → C} (g : ∀ k, Y k ⟶ W),
          Sieve.ofArrows Y g ∈ J W →
            ∀ (j : N) (f : p.obj j ⟶ W),
              ∃ (k : ι) (i : M) (ψ : i ⟶ e.obj j) (h : q.obj i ⟶ Y k),
                h ≫ g k = q.map ψ ≫ ε.hom.app j ≫ f := by
  obtain ⟨M, catM, cofM, esM, q, e, eFull, eFaithful, ε, h₁, h₂⟩ := key hpb hF j₀ a a' haa'
  refine ⟨M, catM, cofM, esM, q, e, eFull, eFaithful, ε, h₁, ?_⟩
  intro W ι hfin Y g hg j f
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact
      absurd
        (map_eq_of_isEmpty hF hι g hg (p.map (IsCofiltered.minToLeft j j₀) ≫ f)
          (F.map (p.map (IsCofiltered.minToRight j j₀)).op a)
          (F.map (p.map (IsCofiltered.minToRight j j₀)).op a'))
        (haa' (IsCofiltered.min j j₀) (IsCofiltered.minToRight j j₀))
  · obtain ⟨n, ⟨τ⟩⟩ := @Finite.exists_equiv_fin ι hfin
    have hn : 0 < n :=
      Nat.pos_of_ne_zero
        (by
          rintro rfl
          exact (τ hι.some).elim0)
    obtain ⟨k, i, ψ, h, hh⟩ := h₂ (covDataOfCovering g hg hn τ.symm j f)
    exact
      ⟨τ.symm k, i, ψ ≫ e.map (skPreIso j).hom, h, comp_eq_of_comp_eq ε (skPreIso j).hom f ψ hh⟩

end

end CategoryTheory.GrothendieckTopology

end

/-!
# Deligne's criterion for the existence of enough points

Let `(C, J)` be a site. Deligne's criterion, the appendix to SGA 4, Exposé VI, asserts that if
fibre products exist in `C` and every covering of `C` admits a refinement by a *finite* covering,
then `(C, J)` has enough points: there is a small family of points of the site whose fibre functors
jointly reflect isomorphisms of sheaves of sets.

The points are the fibre functors `u(X) = colim_j Mor(V_j, X)` of the cofiltered systems `(V_j)_j`
in `C` of the section "Criterion for existence of points", constructed in Mathlib by
`CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered`. Given a sheaf `F` and two distinct
sections `s ≠ s'` of `F` over `U`, one starts from the one-object system `V_1 = U` and refines it,
keeping the two germs distinct, until every section of its own fibre functor is covered by every
finite covering of the site (the lemma Stacks 00YP, iterated along `ω`). The finite-refinement
hypothesis then upgrades "every finite covering" to "every covering sieve", which is exactly what
makes the resulting fibre functor a point, and it separates `s` from `s'`. The family of all points
so obtained is a set, because the index systems can be taken inside a fixed `w`-small set, and it
is conservative because a map of sheaves of sets which is bijective on all fibres and whose source
and target are separated by these points is an isomorphism.

## Main results

* `CategoryTheory.GrothendieckTopology.hasEnoughPoints_of_exists_finite_refinement`: Stacks 00YQ,
  Deligne's criterion.

## Implementation notes

Three departures from the source's form, all of them widenings.

* Hypothesis (1), "finite limits exist in `C`", is weakened to `HasPullbacks C`. In the source,
  finite limits are asked for twice: so that the fibre functor `u` of a system commutes with them,
  which is part of the definition of a point there, and to form the fibre products
  `V_j ×_W W_k` of the members of a finite covering along an arbitrary morphism (Stacks 00YO,
  00YP). The first is not a hypothesis in Mathlib's formulation: a point
  `CategoryTheory.GrothendieckTopology.Point` records left exactness of the fibre functor as
  cofilteredness of its category of elements, which holds for a filtered colimit of representables
  whatever limits `C` has. So only the fibre products remain, and they are pullbacks.
  `HasFiniteLimits C` implies `HasPullbacks C`, so the source's hypothesis is a special case.
* Hypothesis (2) is phrased for covering *sieves*: `h` says that every covering sieve `S` of `X`
  contains a finite family `g k : Y k ⟶ X` which is itself a covering. This is the source's
  condition on covering families, since a family and the sieve it generates have the same
  refinements, and `Sieve.ofArrows Y g ≤ S` says exactly that every `g k` lies in `S`, i.e.
  factors through a member of any family generating `S`. The index type of the refinement is taken
  in `Type`, which is no restriction: a finite family indexed by any type is a reindexing of one
  indexed by a type in `Type`, and `Sieve.ofArrows` is unchanged by reindexing.
* The conclusion is `HasEnoughPoints.{w}`, a statement about sheaves of `Type w`; the source's
  small site with `Set`-valued sheaves is the case `w = u = v`. It is stated for an arbitrary `w`
  under `Small.{w} C` and `LocallySmall.{w} C` — what makes both the fibre functors `C ⥤ Type w`
  and the set of index systems `w`-small — and `HasSheafify J (Type w)`, which is how a family of
  points is recognized as conservative (`ObjectProperty.IsConservativeFamilyOfPoints.mk'`). At
  `w = max u v` all three are instances, so nothing has to be supplied there.

Faithfulness, on the four points a reader should check against the source.

1. No hypothesis is dead: `HasPullbacks C` builds the fibre products of covering members, `h` is
   used both to apply the finite-covering lemma Stacks 00YP and to pass from finite coverings to
   arbitrary covering sieves, and the smallness hypotheses are what make the conservative family
   small, which is the content of "enough points".
2. The base is the source's: one Grothendieck topology `J` on one category `C`, the same `J` for
   the coverings refined in `h`, for the sheaves of `Type w` whose sections the points separate,
   and for the points produced; no auxiliary topology and no localization.
3. Nothing canonical is left unpinned: "has enough points" is not a bare existence statement about
   maps but Mathlib's `HasEnoughPoints.{w} J`, i.e. the existence of a `w`-small family of points
   whose fibre functors `Sheaf J (Type w) ⥤ Type w` jointly reflect isomorphisms, which is the
   source's definition of a conservative family of points (Stacks 00YJ) together with the source's
   requirement that a family be indexed by a set.
4. Not degenerate: any category `C` with pullbacks, equipped with the topology generated by the
   pretopology of finite families `CategoryTheory.Pretopology.finite C`, satisfies both hypotheses
   — a covering sieve for `Pretopology.toGrothendieck` contains by definition a finite covering
   family — and the conclusion is then a non-vacuous supply of points.

## References

* [Stacks 00YQ](https://stacks.math.columbia.edu/tag/00YQ), in the section "Criterion for existence
  of points" (Stacks 00YN), whose previous steps are Stacks 00YO and Stacks 00YP; the definition of
  a conservative family of points and of "enough points" is Stacks 00YJ.
* [SGA4], Exposé VI, appendix by Deligne, Proposition 9.0.
-/

section

universe w v u u₁ v₁ u₂ v₂
open CategoryTheory Limits
open CategoryTheory Limits Opposite
open ConcreteCategory GrothendieckTopology.Point.ofIsCofiltered

namespace Stacks.SitePoints.DeligneCriterion

@[expose] public section

variable {C : Type u} [Category.{v} C]

/-- On a `w`-small category with `w`-small hom types, the sieves on an object form a `w`-small
type: a sieve is a set of arrows with target that object. -/
private lemma small_sieve [Small.{w} C] [LocallySmall.{w} C] (X : C) : Small.{w} (Sieve X) :=
  small_of_injective (f := fun (S : Sieve X) ↦ {t : Σ Y : C, (Y ⟶ X) | S.arrows t.2}) fun _ _ hS ↦
    Sieve.ext fun Y f ↦ Set.ext_iff.1 hS ⟨Y, f⟩

/-- Colimits of shape `Nᵒᵖ` exist in `Type w` as soon as `N` is initially `w`-small; this is the
private instance under which `CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.fiber` is
defined. -/
private lemma hasColimitsOfShapeOpOfInitiallySmall (N : Type u₁) [Category.{v₁} N]
    [InitiallySmall.{w} N] : HasColimitsOfShape Nᵒᵖ (Type w) :=
  hasColimitsOfShape_of_finallySmall _ _

attribute [local instance] hasColimitsOfShapeOpOfInitiallySmall

section Sections

variable (J : GrothendieckTopology C) {X : C} (S : Sieve X)

/-- The section of the sheaf of `J`-closed sieves over `Z` given by the `J`-closure of a sieve `S`
on `X`, pulled back along a morphism `f : Z ⟶ X`. -/
private def closeSection {Z : C} (f : Z ⟶ X) : (Functor.closedSieves J).toFunctor.obj (op Z) :=
  ⟨(J.close S).pullback f, J.isClosed_pullback _ _ (J.close_isClosed S)⟩

/-- The section of the sheaf of `J`-closed sieves over `Z` given by the maximal sieve. -/
private def topSection (Z : C) : (Functor.closedSieves J).toFunctor.obj (op Z) :=
  ⟨(⊤ : Sieve Z), by
    intro Y f _; trivial⟩

private lemma map_closeSection {Z Y : C} (f : Z ⟶ X) (g : Y ⟶ Z) :
    (Functor.closedSieves J).toFunctor.map g.op (closeSection J S f) = closeSection J S (g ≫ f) :=
  Subtype.ext (Sieve.pullback_comp _).symm

private lemma map_topSection {Z Y : C} (g : Y ⟶ Z) :
    (Functor.closedSieves J).toFunctor.map g.op (topSection J Z) = topSection J Y :=
  Subtype.ext (show (⊤ : Sieve Z).pullback g = (⊤ : Sieve Y) from Sieve.pullback_top)

/-- The two distinguished sections of the sheaf of `J`-closed sieves agree over `Z` exactly when
the structural morphism belongs to the `J`-closure of `S`. -/
private lemma closeSection_eq_topSection_iff {Z : C} (f : Z ⟶ X) :
    closeSection J S f = topSection J Z ↔ (J.close S) f := by
  rw [Sieve.mem_iff_pullback_eq_top]
  exact Subtype.ext_iff

/-- **The invariant in sieve-theoretic form.** The two distinguished sections of the sheaf of
`J`-closed sieves have the same restriction along `g` exactly when `g ≫ f` lies in the `J`-closure
of `S`.

This is the form in which the hypothesis and the conclusion of Stacks 00YP are read: both speak of
the two germs at a *transition map* of the system, so both are restrictions of the two sections
rather than the sections themselves. -/
private lemma map_closeSection_eq_map_topSection_iff {Z Y : C} (f : Z ⟶ X) (g : Y ⟶ Z) :
    (Functor.closedSieves J).toFunctor.map g.op (closeSection J S f) =
        (Functor.closedSieves J).toFunctor.map g.op (topSection J Z) ↔
      (J.close S) (g ≫ f) := by
  rw [map_closeSection, map_topSection, closeSection_eq_topSection_iff]

end Sections

end

end Stacks.SitePoints.DeligneCriterion

end
