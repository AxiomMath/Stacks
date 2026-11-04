module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.SelfExtOnACollectionOfOpens

/-!
# Glueing locally given derived objects over a finite cover

Let `(X, 𝒪_X)` be a ringed space and let `(ℬ, K_U, ρ^U_V)` be a system of locally given derived
objects on it, as in Situation 0D67.  Assume that `X = U_1 ∪ … ∪ U_n` with `U_i ∈ ℬ`, that the
intersection of two members of `ℬ` is the union of the members of `ℬ` contained in it, and that
`Ext^i(K_U, K_U) = 0` for `i < 0` and `U ∈ ℬ`.  Then the system has a solution, by induction on
`n` from the case of a cover by two opens.

This file carries out that induction.  A solution over an open `U ⊆ X` is an object of `D(𝒪_U)`
identified with the prescribed object on every member of `ℬ` contained in `U`, compatibly with
the prescribed transitions; a solution in the sense of Situation 0D67 is a solution over `⊤`.
The induction step glues a solution over `U_1 ∪ … ∪ U_{n-1}` with the prescribed object on
`U_n`, and what makes it legitimate is that the covering condition on intersections passes from
the members of `ℬ` to their finite unions.

## Main definitions

* `Stacks.DerivedGlueing.SolutionOver`: a solution of the system over an open subset of `X`.
* `Stacks.DerivedGlueing.GluesAlongTwoOpens`: the case of a cover by two opens, as a hypothesis.

## Main results

* `Stacks.DerivedGlueing.selfSolutionOver`: the prescribed object on a member of `ℬ` is a
  solution over that member — the case `n = 1` of the induction.
* `Stacks.DerivedGlueing.finsetSup_eq_sSup_covered`: a finite union of members of `ℬ` is the
  union of the members of `ℬ` contained in it.
* `Stacks.DerivedGlueing.inf_finsetSup_eq`: the intersection of a member of `ℬ` with a finite
  union of members is the union of the members contained in it.
* `Stacks.DerivedGlueing.exists_solutionOver_finsetSup`: a solution over a finite union of
  members of `ℬ`, granted the two-open case.
* `Stacks.DerivedGlueing.exists_solution_of_finite_cover`: **[Stacks, Tag 0D6A]**, existence,
  granted the two-open case.
* `Stacks.DerivedGlueing.exists_solution_of_top_mem`: existence when a single member of `ℬ` is
  all of `X`.

## No unrestricted `@[stacks 0D6A]`

Tag 0D6A asserts that a solution *exists* and is *unique up to unique isomorphism*.  Both halves
rest on one missing input, the **uniqueness clause of [Stacks, Tag 0D68]**: a system whose
displayed opens cover `X` and whose intersections are covered by displayed opens has at most one
solution, up to a unique compatible isomorphism.  That clause is not carried in this
development — `Stacks.DerivedGlueing.Solution.subsingleton_shiftedHom_self` is tagged 0D68 and
proves only the other clause of that tag, the vanishing of negative self-Ext.

* **Uniqueness** in 0D6A *is* that clause, so nothing about it is stated below.  It *is* stated
  in `StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UniquenessOverACover`, as
  `Stacks.DerivedGlueing.exists_unique_solutionIso_of_finite_cover` — granted not that clause but
  the sheaf condition of [Stacks, Tag 0D66] part (2), from which this library already derives it.
* **Existence** is carried only modulo the case of a cover by two opens, which appears as the
  hypothesis `Stacks.DerivedGlueing.GluesAlongTwoOpens`.  That hypothesis is stated in the shape
  the source's induction uses it: the second open is a union of members of `ℬ`, and the covering
  condition on intersections of members is assumed.  Both restrictions are necessary rather than
  cosmetic — without the second the statement is false, and its docstring exhibits a four-point
  discrete space where it fails; without the first it is true but reachable only from the full
  [Stacks, Tag 0D6C], which is what it is used to prove.  Since the hypothesis sits in
  hypothesis position, restoring the restrictions *strengthens* every theorem below that carries
  it.  The glueing lemma [Stacks, Tag 08DG]
  *is* proved here, as `Stacks.Cohomology.GlueingComplexes.exists_glueing`, but it does not
  suffice: among its hypotheses is an isomorphism `c : A|_{U ∩ V} ≅ B|_{U ∩ V}` between the two
  objects to be glued, and in Situation 0D67 that isomorphism is the one of
  [Stacks, Tag 0D69], which the source produces from the uniqueness clause of 0D68 applied to
  the system induced on `U ∩ V`, both restrictions being solutions there.  The source's proof
  of the two-open case uses the same clause again, to produce the identification over a member
  of the collection contained in neither `U` nor `V`.
* Beyond that, 08DG is stated for open immersions of ringed spaces and derived pullback rather
  than for the restriction functors of Situation 0D67, so applying it here would also need a
  comparison of the two vocabularies, natural in the open subspace; the comparison of a single
  open is `Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso`.  That
  naturality *is* now recorded, in
  `StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestrictionNaturality`:
  `Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso_ofRestrict_comp` is the
  naturality at an open subspace of an open subspace, and
  `Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso_eq` transports it into
  the restriction-functor spelling.  So this is no longer an obstruction; what remains missing for
  the two-open case is only the uniqueness clause of 0D68, as described next.

The uniqueness clause of 0D68 is itself within sight but not within reach of the present tree:
the rule `V ↦ Hom(K|_{f⁻¹V}, L|_{f⁻¹V})` is already known to be a sheaf, by
`Stacks.Cohomology.UnboundedHigherDirectImage.isSheaf_derivedPreimageHomPresheaf`, and the
values of that presheaf are already identified with those groups of morphisms, by
`Stacks.Cohomology.UnboundedHigherDirectImage.derivedPreimageHomPresheafValueEquiv`; what is
missing is that this identification is compatible with the restriction maps of the presheaf,
without which a compatible family of local morphisms cannot be read as a family of sections and
glued.

Everything *after* that sheaf condition is carried:
`Stacks.DerivedGlueing.hasUniqueSolutionOverIso_of_hasGluingForHomsOver` derives the uniqueness
clause, in the relativized form `Stacks.DerivedGlueing.HasUniqueSolutionOverIso`, from the
glueing of morphisms alone.

What *is* carried unconditionally is the induction itself, together with the case `n = 1`:
`Stacks.DerivedGlueing.exists_solution_of_top_mem` needs no hypothesis beyond `⊤ ∈ ℬ`, and so
does its uniqueness partner
`Stacks.DerivedGlueing.exists_unique_solutionIso_of_top_mem`, so the two together are the whole
of Tag 0D6A for `n = 1`.

## References

* [Stacks Project, Tag 0D6A](https://stacks.math.columbia.edu/tag/0D6A)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D69](https://stacks.math.columbia.edu/tag/0D69)
* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.DerivedGlueing

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-! ### Solutions over an open subset -/

/-- **A solution of a system of locally given derived objects over an open subset.** An object
of `D(𝒪_U)` together with isomorphisms identifying its restrictions with the prescribed objects
on the members of the collection contained in `U`, compatibly with the prescribed transition
isomorphisms.  Taking `U = ⊤` recovers `Stacks.DerivedGlueing.Solution`. -/
structure SolutionOver (S : LocallyGiven X) (U : Opens X.carrier) where
  /-- The object over `U`. -/
  obj : OpenDerivedCategory X U
  /-- The identification of its restriction to a member contained in `U` with the prescribed
  object there. -/
  rho : ∀ (V : Opens X.carrier) (hV : V ∈ S.opens) (hVU : V ≤ U),
    (S.restriction V U hVU).obj obj ≅ S.obj V hV
  /-- Restricting the identification over `V` to a smaller member `W` and composing with the
  prescribed transition isomorphism gives the identification over `W`. -/
  compatibility : ∀ (V W : Opens X.carrier) (hWV : W ≤ V) (hV : V ∈ S.opens)
      (hW : W ∈ S.opens) (hVU : V ≤ U),
    (S.restrictionComp W V U hWV hVU).hom.app obj ≫
        (S.restriction W V hWV).map (rho V hV hVU).hom ≫ (S.rho W V hWV hV hW).hom =
      (rho W hW (hWV.trans hVU)).hom

/-- A solution over `⊤` is a solution of the system. -/
def SolutionOver.toSolution {S : LocallyGiven X} (A : SolutionOver S ⊤) : Solution S where
  obj := A.obj
  rho U hU := A.rho U hU le_top
  compatibility V U hVU hU hV := A.compatibility U V hVU hU hV le_top

/-- A solution of the system is a solution over `⊤`. -/
def Solution.toSolutionOver {S : LocallyGiven X} (A : Solution S) : SolutionOver S ⊤ where
  obj := A.obj
  rho U hU _ := A.rho U hU
  compatibility V U hUV hV hU _ := A.compatibility U V hUV hV hU

/-- **The case `n = 1`.** The prescribed object on a member `U` of the collection is a solution
over `U`: its identifications are the prescribed transition isomorphisms out of `U`, and their
compatibility is the cocycle condition. -/
def selfSolutionOver (S : LocallyGiven X) (U : Opens X.carrier) (hU : U ∈ S.opens) :
    SolutionOver S U where
  obj := S.obj U hU
  rho V hV hVU := S.rho V U hVU hU hV
  compatibility V W hWV hV hW hVU := (S.cocycle W V U hWV hVU hU hV hW).symm

/-! ### The two-open case, as a hypothesis -/

/-- **The case of a cover by two opens.** A solution over a member `U` of the collection and a
solution over an open `V` that is the union of the members of the collection contained in it
glue to a solution over `U ∪ V`, provided the intersection of two members of the collection is
the union of the members contained in it and the prescribed objects have no negative self-Ext.

This is the case `n = 2` of [Stacks, Tag 0D6A], read as the source applies it inside the
induction: there `V` is `U_1 ∪ … ∪ U_{n-1}`, which the source adjoins to the collection, so it
is a union of members and the covering condition on intersections holds for the enlarged
collection.  It appears as a hypothesis of
`Stacks.DerivedGlueing.exists_solutionOver_finsetSup` and of
`Stacks.DerivedGlueing.exists_solution_of_finite_cover` because it is not available: the
glueing lemma [Stacks, Tag 08DG] that proves it needs an isomorphism between the two objects
over the overlap, which is [Stacks, Tag 0D69] and comes from the uniqueness clause of
[Stacks, Tag 0D68], a clause this development does not carry.

Neither hypothesis is decoration.  Without the covering condition on intersections of members
the statement is **false**: take `X = {1,2,3,4}` discrete, `ℬ = {{1}, {1,2,3}, {1,3,4}}`, and
prescribe sheaves of modules in degree `0` agreeing on `{1}` whose stalk at `3` is `0` on
`{1,2,3}` and nonzero on `{1,3,4}`.  All the prescribed objects then have no negative self-Ext,
and `U = {1}`, `V = {2,3,4}` satisfy `U ∩ V = ∅ = ⋃ {W ∈ ℬ : W ⊆ ∅}` and both carry solutions —
`V` contains no member of `ℬ` at all — while no object on `X` restricts to the prescribed
objects on both `{1,2,3}` and `{1,3,4}`, their stalks at `3` being non-isomorphic.  What fails
there is that `ℬ` does not cover `{1,2,3} ∩ {1,3,4} = {1,3}`.

Without the hypothesis that `V` is a union of members the statement is still true, but no
longer provable by the source's argument: the glueing of a solution over `U` with one over `V`
produces nothing over a member of `ℬ` that meets `V` outside the part of `V` covered by members,
and the statement is then a consequence only of the full [Stacks, Tag 0D6C] applied to the union
of the members contained in `U ∪ V` — the theorem that this very hypothesis is used to prove.
Since the hypothesis occupies hypothesis position, restoring both restrictions makes every
theorem below that carries it **stronger**, not weaker. -/
def GluesAlongTwoOpens (S : LocallyGiven X) : Prop :=
  ∀ (U : Opens X.carrier), U ∈ S.opens → ∀ (V : Opens X.carrier),
    V = sSup {W | W ∈ S.opens ∧ W ≤ V} →
    U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V} →
    (∀ U' ∈ S.opens, ∀ V' ∈ S.opens, U' ⊓ V' = sSup {W | W ∈ S.opens ∧ W ≤ U' ⊓ V'}) →
    (∀ (W : Opens X.carrier) (hW : W ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj W hW) (S.obj W hW) i)) →
    SolutionOver S U → SolutionOver S V → Nonempty (SolutionOver S (U ⊔ V))

/-! ### The induction on the number of members of the cover -/

/-- **A finite union of members of the collection is the union of the members contained in
it.** One inclusion holds because each member of the family is itself a member of the
collection contained in the union, the other because every member contained in the union is. -/
theorem finsetSup_eq_sSup_covered (S : LocallyGiven X) (s : Finset (Opens X.carrier))
    (hs : ∀ U ∈ s, U ∈ S.opens) :
    s.sup id = sSup {W | W ∈ S.opens ∧ W ≤ s.sup id} :=
  le_antisymm (Finset.sup_le fun U hU => le_sSup ⟨hs U hU, Finset.le_sup (f := id) hU⟩)
    (sSup_le fun _ hW => hW.2)

/-- **The covering condition on intersections passes to finite unions.** If the intersection of
two members of the collection is the union of the members contained in it, then so is the
intersection of a member with a finite union of members. -/
theorem inf_finsetSup_eq (S : LocallyGiven X)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (V : Opens X.carrier) (hV : V ∈ S.opens) (s : Finset (Opens X.carrier))
    (hs : ∀ U ∈ s, U ∈ S.opens) :
    V ⊓ s.sup id = sSup {W | W ∈ S.opens ∧ W ≤ V ⊓ s.sup id} := by
  refine le_antisymm (fun x hx => ?_) (sSup_le fun W hW => hW.2)
  obtain ⟨hxV, hxs⟩ := hx
  rw [Finset.sup_id_eq_sSup] at hxs
  obtain ⟨U, hU, hxU⟩ := Opens.mem_sSup.mp hxs
  have hxUV : x ∈ V ⊓ U := ⟨hxV, hxU⟩
  rw [hinter V hV U (hs U hU)] at hxUV
  obtain ⟨W, hW, hxW⟩ := Opens.mem_sSup.mp hxUV
  refine Opens.mem_sSup.mpr ⟨W, ⟨hW.1, hW.2.trans (inf_le_inf_left V ?_)⟩, hxW⟩
  rw [Finset.sup_id_eq_sSup]
  exact le_sSup hU

/-- **The induction of [Stacks, Tag 0D6A].** Granted the case of a cover by two opens, a system
of locally given derived objects whose intersections are covered by members of the collection
and whose prescribed objects have no negative self-Ext admits a solution over any finite,
nonempty union of members of the collection.

The induction starts from `Stacks.DerivedGlueing.selfSolutionOver` and glues on one member at a
time; `Stacks.DerivedGlueing.inf_finsetSup_eq` supplies the hypothesis on the intersection of
the new member with the union of the previous ones, and
`Stacks.DerivedGlueing.finsetSup_eq_sSup_covered` the hypothesis that that union is a union of
members of the collection. -/
theorem exists_solutionOver_finsetSup (S : LocallyGiven X) (hglue : GluesAlongTwoOpens S)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    (s : Finset (Opens X.carrier)) (hs : s.Nonempty) (hmem : ∀ U ∈ s, U ∈ S.opens) :
    Nonempty (SolutionOver S (s.sup id)) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton U =>
    have hU : U ∈ S.opens := hmem U (Finset.mem_singleton_self U)
    rw [Finset.sup_singleton]
    exact ⟨selfSolutionOver S U hU⟩
  | cons U t hUt ht ih =>
    have hU : U ∈ S.opens := hmem U (Finset.mem_cons.mpr (Or.inl rfl))
    have hmem' : ∀ V ∈ t, V ∈ S.opens := fun V hV => hmem V (Finset.mem_cons_of_mem hV)
    obtain ⟨A⟩ := ih hmem'
    rw [Finset.sup_cons]
    exact hglue U hU (t.sup id) (finsetSup_eq_sSup_covered S t hmem')
      (inf_finsetSup_eq S hinter U hU t hmem') hinter hExt (selfSolutionOver S U hU) A

/-! ### Tag 0D6A, existence -/

/-- **Existence of a solution over a finite cover, from the two-open case.** In Situation 0D67,
assume that `X = U_1 ∪ … ∪ U_n` with `U_i` in the collection, that the intersection of two
members of the collection is the union of the members contained in it, that the prescribed
objects have no negative self-Ext, and that the system satisfies
`Stacks.DerivedGlueing.GluesAlongTwoOpens`, the case `n = 2`.  Then the system has a solution. -/
theorem exists_solution_of_finite_cover (S : LocallyGiven X) (hglue : GluesAlongTwoOpens S)
    (s : Finset (Opens X.carrier)) (hs : s.Nonempty) (hmem : ∀ U ∈ s, U ∈ S.opens)
    (hcover : s.sup id = ⊤)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i)) :
    Nonempty (Solution S) := by
  obtain ⟨A⟩ : Nonempty (SolutionOver S ⊤) :=
    hcover ▸ exists_solutionOver_finsetSup S hglue hinter hExt s hs hmem
  exact ⟨A.toSolution⟩

/-- **[Stacks, Tag 0D6A] when the cover has a single member.** If the whole of `X` belongs to
the collection, then the system has a solution: the prescribed object on `⊤` is one.

This is the case `n = 1` of the tag. -/
@[stacks 0D6A "existence when a single member of the collection is all of X"]
theorem exists_solution_of_top_mem (S : LocallyGiven X) (htop : ⊤ ∈ S.opens) :
    Nonempty (Solution S) :=
  ⟨(selfSolutionOver S ⊤ htop).toSolution⟩

end Stacks.DerivedGlueing

end
