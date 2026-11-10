module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.TwoOpenGlueingInput

/-!
# The two-open case of the glueing problem, from the uniqueness clause

Let `(X, 𝒪_X)` be a ringed space and `(ℬ, K_U, ρ^U_V)` a system of locally given derived objects
on it, as in Situation 0D67.  This file reduces the hypothesis
`Stacks.DerivedGlueing.GluesAlongTwoOpens` — the case of a cover by two opens, which the
induction of [Stacks, Tag 0D6A] rests on — to the glueing lemma [Stacks, Tag 08DG] read in the
vocabulary of Situation 0D67.

Write `P` for `U ∪ V` and `ℬ'` for the members of `ℬ` contained in `U` or in `V`.  Given a
solution `A` over the member `U` and a solution `B` over the union `V` of members, the argument
of the source is in three steps.

* The uniqueness clause of [Stacks, Tag 0D68] over `U ∩ V`, which both restrictions solve,
  produces the comparison isomorphism `c : A|_{U ∩ V} ≅ B|_{U ∩ V}` of [Stacks, Tag 0D69].
* The glueing lemma produces an object `F` over `P` whose restrictions to `U` and to `V` are `A`
  and `B`, compatibly with `c`.  That is the hypothesis
  `Stacks.DerivedGlueing.GluesObjectsAlongTwoOpens` below, which is [Stacks, Tag 08DG] stated for
  the displayed restriction functors of the system; it is not discharged here.
* The identifications of `F` over the members of `ℬ` contained in `P` come from the uniqueness
  clause **again**, applied over each such member to the subsystem carried by `ℬ'`, which covers
  `P` and every member of `ℬ` below it
  (`Stacks.DerivedGlueing.mem_eq_sSup_opensBelowPair`).

## Main definitions

* `Stacks.DerivedGlueing.transportedRho`: the identification over a member `W` of a collection,
  below an open `O` below `P`, of the restriction from `P` of an object with the prescribed
  object, read off an identification of its restriction to `O` with the object of a solution
  over `O`.
* `Stacks.DerivedGlueing.GluesObjectsAlongTwoOpens`: [Stacks, Tag 08DG] in the vocabulary of
  Situation 0D67 — the glueing of two objects along the two displayed restrictions to an
  intersection.
* `Stacks.DerivedGlueing.glueRho`: the identification over a member of `ℬ'`, obtained from the
  solution over `U` when the member lies below `U` and from the solution over `V` otherwise.
* `Stacks.DerivedGlueing.glueSolutionOverSubcollection`: the glued object, as a solution over
  `U ∪ V` for the subsystem carried by `ℬ'`.

## Main results

* `Stacks.DerivedGlueing.transportedRho_hom_factor`: the identification transported from `O`
  factors through any intermediate open `M` with `W ⊆ M ⊆ O`.  Everything below is deduced from
  this one factorization.
* `Stacks.DerivedGlueing.transportedRho_compatibility`: the transported identifications satisfy
  the compatibility of a solution.
* `Stacks.DerivedGlueing.transportedRho_eq_of_le_inf`: over a member contained in **both** `U`
  and `V` the two transported identifications agree.  This is where the compatibility of the
  glueing with `c`, and the compatibility of `c` itself, are used, and it is what makes the
  case distinction of `Stacks.DerivedGlueing.glueRho` well posed.
* `Stacks.DerivedGlueing.selfSolutionOverSubcollection_rho_isCompatibleHom`: a prescribed
  transition is a morphism of the solutions that the prescribed objects define for a subsystem;
  this is the cocycle condition.
* `Stacks.DerivedGlueing.nonempty_solutionOver_sup_of_subcollectionSolution`: a solution over
  `U ∪ V` for the subsystem is a solution for the system — the second use of the uniqueness
  clause.
* `Stacks.DerivedGlueing.nonempty_solutionOver_sup_of_glueing`: the two-open case at one pair of
  opens, from the two instances of the uniqueness clause that the argument uses and nothing
  else.
* `Stacks.DerivedGlueing.gluesAlongTwoOpens_of_gluesObjectsAlongTwoOpens`: **the reduction.**
  The two-open case holds for a system whose every subsystem satisfies the uniqueness clause of
  [Stacks, Tag 0D68] and for which the glueing lemma is available.
* `Stacks.DerivedGlueing.gluesAlongTwoOpens_of_hasGluingForHomsOver_subcollections`: the same
  with the uniqueness clause replaced by the sheaf condition of [Stacks, Tag 0D66] part (2) that
  implies it.

## Which uniqueness clause, and why it is not the one for `S`

The hypothesis carried below is the uniqueness clause of [Stacks, Tag 0D68] for **every
subsystem** of the given system,

```
∀ (𝒟 : Set (Opens X.carrier)) (h𝒟 : 𝒟 ⊆ S.opens),
  HasUniqueSolutionOverIso (S.subcollection 𝒟 h𝒟)
```

and **not** `Stacks.DerivedGlueing.HasUniqueSolutionOverIso S` alone, which the module
documentation of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.TwoOpenGlueingInput` displays as the
missing statement.  That display is wrong, and the same documentation says why four lines
earlier: the clause "is needed twice: once over `U ∩ V` … and once over each member of the
collection below `U ∪ V` … and **the second use is at the subsystem**".  It is not available for
the subsystem: a solution over an open for a subsystem carries *fewer* identifications than one
for the ambient system, so the clause for the subsystem is a strictly stronger statement, and
the glued object `F` has, before the clause is applied, no identification at all over a member
of `ℬ` lying below neither `U` nor `V`.  Applying the clause for `S` would need exactly the
identification it is being used to produce.

Nothing is lost by the change: the clause for the ambient system is the case `𝒟 = S.opens`, by
`Stacks.DerivedGlueing.LocallyGiven.subcollection_self`, so the hypothesis below implies the one
displayed there.  In the source this costs nothing at all, [Stacks, Tag 0D68] being a theorem
about an arbitrary system rather than a hypothesis attached to one.

## What is not here

`Stacks.DerivedGlueing.GluesObjectsAlongTwoOpens` is not proved.  It is
`Stacks.Cohomology.GlueingComplexes.exists_glueing`, which this development carries, transported
from open immersions of ringed spaces and derived pullback to the displayed restriction functors
of Situation 0D67; `Stacks.DerivedGlueing.openModuleRestriction_eq`,
`Stacks.DerivedGlueing.LocallyGiven.restrictionIsoOfExtension` and
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso_eq` are steps of that
transport.  Two things are missing for it and neither is below: a Cartesian square of open
immersions of ringed spaces presenting `U ∩ V` inside `U ∪ V`, and the comparison of the modules
on an open `U` of `X` with the modules on the corresponding open of the subspace `U ∪ V`, under
which the degreewise restrictions correspond.

## References

* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D69](https://stacks.math.columbia.edu/tag/0D69)
* [Stacks Project, Tag 0D6A](https://stacks.math.columbia.edu/tag/0D6A)
* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.DerivedGlueing

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-! ### A rewriting helper -/

/-- Reassociating a two-term identity so that it can be applied to the head of a longer
composite. -/
theorem comp_assoc_congr {C : Type*} [Category C] {P Q₁ Q₂ R T : C} {a : P ⟶ Q₁} {b : Q₁ ⟶ R}
    {a' : P ⟶ Q₂} {b' : Q₂ ⟶ R} (h : a ≫ b = a' ≫ b') (z : R ⟶ T) :
    a ≫ b ≫ z = a' ≫ b' ≫ z := by
  rw [← Category.assoc, h, Category.assoc]

/-! ### The subsystem on the whole collection -/

/-- **The subsystem carried by the whole collection is the system.** Every field of
`Stacks.DerivedGlueing.LocallyGiven.subcollection` is then the corresponding field of the given
system, the membership hypotheses being transported along the identity. -/
theorem LocallyGiven.subcollection_self (S : LocallyGiven X) (h : S.opens ⊆ S.opens) :
    S.subcollection S.opens h = S :=
  rfl

/-! ### Transporting an identification along an inclusion of opens -/

/-- **The identification over a member `W` of the collection obtained from a solution over an
open `O` above it.** Let `F` be an object over an open `P`, let `A` be a solution over an open
`O` below `P` and let `f` identify the restriction of `F` to `O` with the object of `A`.  Then
the restriction of `F` to a member `W` of the collection contained in `O` is identified with the
prescribed object there: restrict `f` to `W` and compose with the identification of `A`. -/
def transportedRho (S : LocallyGiven X) {O P : Opens X.carrier} (hOP : O ≤ P)
    (F : OpenDerivedCategory X P) (A : SolutionOver S O)
    (f : (S.restriction O P hOP).obj F ≅ A.obj) (W : Opens X.carrier) (hW : W ∈ S.opens)
    (hWO : W ≤ O) :
    (S.restriction W P (hWO.trans hOP)).obj F ≅ S.obj W hW :=
  (S.restrictionComp W O P hWO hOP).app F ≪≫ (S.restriction W O hWO).mapIso f ≪≫
    A.rho W hW hWO

/-- The morphism underlying `Stacks.DerivedGlueing.transportedRho` is the comparison of
restrictions, followed by the restriction of `f` to `W`, followed by the identification of `A` over
`W`. -/
theorem transportedRho_hom (S : LocallyGiven X) {O P : Opens X.carrier} (hOP : O ≤ P)
    (F : OpenDerivedCategory X P) (A : SolutionOver S O)
    (f : (S.restriction O P hOP).obj F ≅ A.obj) (W : Opens X.carrier) (hW : W ∈ S.opens)
    (hWO : W ≤ O) :
    (transportedRho S hOP F A f W hW hWO).hom =
      (S.restrictionComp W O P hWO hOP).hom.app F ≫
        (S.restriction W O hWO).map f.hom ≫ (A.rho W hW hWO).hom :=
  rfl

/-- The identification over `W` of the solution `A` restricted to `M` is the inverse comparison of
restrictions through `M`, followed by the identification of `A` over `W`. -/
theorem restrictOpen_rho_hom (S : LocallyGiven X) {O : Opens X.carrier} (A : SolutionOver S O)
    (M : Opens X.carrier) (hMO : M ≤ O) (W : Opens X.carrier) (hW : W ∈ S.opens) (hWM : W ≤ M) :
    ((A.restrictOpen M hMO).rho W hW hWM).hom =
      (S.restrictionComp W M O hWM hMO).inv.app A.obj ≫
        (A.rho W hW (hWM.trans hMO)).hom :=
  rfl

/-- **The transported identification factors through an intermediate open.** For
`W ⊆ M ⊆ O ⊆ P`, the identification over `W` read off `f` is the comparison of restriction
through `M`, then the restriction to `M` of the identification of `F|_M` with `A|_M`, then the
identification of the solution `A` restricted to `M`.

Only the associativity `Stacks.DerivedGlueing.LocallyGiven.restrictionComp_pentagon` of the
comparisons and the naturality of one of them are used. -/
theorem transportedRho_hom_factor (S : LocallyGiven X) {O P : Opens X.carrier} (hOP : O ≤ P)
    (F : OpenDerivedCategory X P) (A : SolutionOver S O)
    (f : (S.restriction O P hOP).obj F ≅ A.obj) (M W : Opens X.carrier) (hMO : M ≤ O)
    (hWM : W ≤ M) (hW : W ∈ S.opens) :
    (transportedRho S hOP F A f W hW (hWM.trans hMO)).hom =
      (S.restrictionComp W M P hWM (hMO.trans hOP)).hom.app F ≫
        (S.restriction W M hWM).map
          ((S.restrictionComp M O P hMO hOP).hom.app F ≫
            (S.restriction M O hMO).map f.hom) ≫
        ((S.restrictionComp W M O hWM hMO).inv.app A.obj ≫
          (A.rho W hW (hWM.trans hMO)).hom) := by
  have hpent := S.restrictionComp_pentagon W M O P hWM hMO hOP F
  have hnat : (S.restrictionComp W M O hWM hMO).hom.app ((S.restriction O P hOP).obj F) ≫
        (S.restriction W M hWM).map ((S.restriction M O hMO).map f.hom) =
      (S.restriction W O (hWM.trans hMO)).map f.hom ≫
        (S.restrictionComp W M O hWM hMO).hom.app A.obj :=
    ((S.restrictionComp W M O hWM hMO).hom.naturality f.hom).symm
  rw [transportedRho_hom, Functor.map_comp, Category.assoc,
    ← comp_assoc_congr hpent, comp_assoc_congr hnat, Iso.hom_inv_id_app_assoc]

/-- **The transported identifications are compatible with the prescribed transitions.** This is
the compatibility clause of a solution, for the identifications read off a single `f`; it is the
compatibility clause of the solution `A` over `O`, moved across the factorization
`Stacks.DerivedGlueing.transportedRho_hom_factor`. -/
theorem transportedRho_compatibility (S : LocallyGiven X) {O P : Opens X.carrier} (hOP : O ≤ P)
    (F : OpenDerivedCategory X P) (A : SolutionOver S O)
    (f : (S.restriction O P hOP).obj F ≅ A.obj) (V W : Opens X.carrier) (hWV : W ≤ V)
    (hV : V ∈ S.opens) (hW : W ∈ S.opens) (hVO : V ≤ O) :
    (S.restrictionComp W V P hWV (hVO.trans hOP)).hom.app F ≫
        (S.restriction W V hWV).map (transportedRho S hOP F A f V hV hVO).hom ≫
        (S.rho W V hWV hV hW).hom =
      (transportedRho S hOP F A f W hW (hWV.trans hVO)).hom := by
  have hA : (S.restrictionComp W V O hWV hVO).inv.app A.obj ≫
      (A.rho W hW (hWV.trans hVO)).hom =
      (S.restriction W V hWV).map (A.rho V hV hVO).hom ≫ (S.rho W V hWV hV hW).hom := by
    rw [← A.compatibility V W hWV hV hW hVO, Iso.inv_hom_id_app_assoc]
  rw [transportedRho_hom_factor S hOP F A f V W hVO hWV hW, hA, transportedRho_hom]
  simp only [Functor.map_comp, Category.assoc]

/-! ### The glueing lemma in the vocabulary of Situation 0D67 -/

/-- **[Stacks, Tag 08DG] in the vocabulary of Situation 0D67, as a hypothesis.** An object `A`
over an open `U`, an object `B` over an open `V` and an isomorphism `c` between their displayed
restrictions to `U ∩ V` come from an object `F` over `U ∪ V` whose displayed restrictions to `U`
and to `V` are `A` and `B`, compatibly with `c`.

The statement is carried by this development for open immersions of ringed spaces and derived
pullback, as `Stacks.Cohomology.GlueingComplexes.exists_glueing`.  Transporting it to the
displayed restriction functors `Stacks.DerivedGlueing.LocallyGiven.restriction` is a separate
obligation, which this file does not discharge; see the section *What is not here* of the module
documentation. -/
def GluesObjectsAlongTwoOpens (S : LocallyGiven X) : Prop :=
  ∀ (U V : Opens X.carrier) (A : OpenDerivedCategory X U) (B : OpenDerivedCategory X V)
    (c : (S.restriction (U ⊓ V) U inf_le_left).obj A ≅
      (S.restriction (U ⊓ V) V inf_le_right).obj B),
    ∃ (F : OpenDerivedCategory X (U ⊔ V))
      (f : (S.restriction U (U ⊔ V) le_sup_left).obj F ≅ A)
      (g : (S.restriction V (U ⊔ V) le_sup_right).obj F ≅ B),
      (S.restrictionComp (U ⊓ V) U (U ⊔ V) inf_le_left le_sup_left).hom.app F ≫
          (S.restriction (U ⊓ V) U inf_le_left).map f.hom ≫ c.hom =
        (S.restrictionComp (U ⊓ V) V (U ⊔ V) inf_le_right le_sup_right).hom.app F ≫
          (S.restriction (U ⊓ V) V inf_le_right).map g.hom

/-! ### The identification over a member below one of the two opens -/

section Glue

variable (S : LocallyGiven X) (U V : Opens X.carrier) (F : OpenDerivedCategory X (U ⊔ V))
  (A : SolutionOver S U) (B : SolutionOver S V)
  (f : (S.restriction U (U ⊔ V) le_sup_left).obj F ≅ A.obj)
  (g : (S.restriction V (U ⊔ V) le_sup_right).obj F ≅ B.obj)

/-- **Over a member contained in both opens the two transported identifications agree.** The
compatibility of the glueing with the comparison `c`, and the compatibility of `c` with the
prescribed transitions, say exactly this; the factorization
`Stacks.DerivedGlueing.transportedRho_hom_factor` through `U ∩ V` is what brings both sides into
a shape where they can be compared. -/
theorem transportedRho_eq_of_le_inf
    (c : (S.restriction (U ⊓ V) U inf_le_left).obj A.obj ≅
      (S.restriction (U ⊓ V) V inf_le_right).obj B.obj)
    (hfg : (S.restrictionComp (U ⊓ V) U (U ⊔ V) inf_le_left le_sup_left).hom.app F ≫
        (S.restriction (U ⊓ V) U inf_le_left).map f.hom ≫ c.hom =
      (S.restrictionComp (U ⊓ V) V (U ⊔ V) inf_le_right le_sup_right).hom.app F ≫
        (S.restriction (U ⊓ V) V inf_le_right).map g.hom)
    (hc : (A.restrictOpen (U ⊓ V) inf_le_left).IsCompatibleHom
      (B.restrictOpen (U ⊓ V) inf_le_right) c.hom)
    (W : Opens X.carrier) (hW : W ∈ S.opens) (hWM : W ≤ U ⊓ V) :
    transportedRho S le_sup_left F A f W hW (hWM.trans inf_le_left) =
      transportedRho S le_sup_right F B g W hW (hWM.trans inf_le_right) := by
  have hc' : (S.restriction W (U ⊓ V) hWM).map c.hom ≫
      (S.restrictionComp W (U ⊓ V) V hWM inf_le_right).inv.app B.obj ≫
        (B.rho W hW (hWM.trans inf_le_right)).hom =
      (S.restrictionComp W (U ⊓ V) U hWM inf_le_left).inv.app A.obj ≫
        (A.rho W hW (hWM.trans inf_le_left)).hom := hc W hW hWM
  have hstep : (S.restriction W (U ⊓ V) hWM).map
        ((S.restrictionComp (U ⊓ V) U (U ⊔ V) inf_le_left le_sup_left).hom.app F ≫
          (S.restriction (U ⊓ V) U inf_le_left).map f.hom) ≫
      ((S.restrictionComp W (U ⊓ V) U hWM inf_le_left).inv.app A.obj ≫
        (A.rho W hW (hWM.trans inf_le_left)).hom) =
      (S.restriction W (U ⊓ V) hWM).map
          ((S.restrictionComp (U ⊓ V) V (U ⊔ V) inf_le_right le_sup_right).hom.app F ≫
            (S.restriction (U ⊓ V) V inf_le_right).map g.hom) ≫
        ((S.restrictionComp W (U ⊓ V) V hWM inf_le_right).inv.app B.obj ≫
          (B.rho W hW (hWM.trans inf_le_right)).hom) := by
    rw [← hc', ← Category.assoc, ← Functor.map_comp, Category.assoc, hfg]
  apply Iso.ext
  rw [transportedRho_hom_factor S le_sup_left F A f (U ⊓ V) W inf_le_left hWM hW,
    transportedRho_hom_factor S le_sup_right F B g (U ⊓ V) W inf_le_right hWM hW, hstep]

/-- **The identification over a member of the collection contained in `U` or in `V`.** Read off
the solution over `U` when the member lies below `U`, and off the solution over `V` otherwise.
The choice is immaterial by `Stacks.DerivedGlueing.transportedRho_eq_of_le_inf`. -/
def glueRho (W : Opens X.carrier) (hW : W ∈ S.opens) (hWP : W ≤ U ⊔ V)
    (hor : W ≤ U ∨ W ≤ V) : (S.restriction W (U ⊔ V) hWP).obj F ≅ S.obj W hW :=
  @dite _ (W ≤ U) (Classical.propDecidable (W ≤ U))
    (fun h => transportedRho S le_sup_left F A f W hW h)
    (fun h => transportedRho S le_sup_right F B g W hW (hor.resolve_left h))

/-- For a member `W` contained in `U`, the identification `Stacks.DerivedGlueing.glueRho` is the
one transported from the solution over `U`. -/
theorem glueRho_of_le_left (W : Opens X.carrier) (hW : W ∈ S.opens) (hWP : W ≤ U ⊔ V)
    (hor : W ≤ U ∨ W ≤ V) (h : W ≤ U) :
    glueRho S U V F A B f g W hW hWP hor = transportedRho S le_sup_left F A f W hW h := by
  simp [glueRho, h]

/-- For a member `W` not contained in `U`, the identification `Stacks.DerivedGlueing.glueRho` is
the one transported from the solution over `V`. -/
theorem glueRho_of_not_le_left (W : Opens X.carrier) (hW : W ∈ S.opens) (hWP : W ≤ U ⊔ V)
    (hor : W ≤ U ∨ W ≤ V) (h : ¬ W ≤ U) :
    glueRho S U V F A B f g W hW hWP hor =
      transportedRho S le_sup_right F B g W hW (hor.resolve_left h) := by
  simp [glueRho, h]

/-- Whichever branch the case distinction takes, a member contained in `V` is identified through
the solution over `V`. -/
theorem glueRho_of_le_right
    (c : (S.restriction (U ⊓ V) U inf_le_left).obj A.obj ≅
      (S.restriction (U ⊓ V) V inf_le_right).obj B.obj)
    (hfg : (S.restrictionComp (U ⊓ V) U (U ⊔ V) inf_le_left le_sup_left).hom.app F ≫
        (S.restriction (U ⊓ V) U inf_le_left).map f.hom ≫ c.hom =
      (S.restrictionComp (U ⊓ V) V (U ⊔ V) inf_le_right le_sup_right).hom.app F ≫
        (S.restriction (U ⊓ V) V inf_le_right).map g.hom)
    (hc : (A.restrictOpen (U ⊓ V) inf_le_left).IsCompatibleHom
      (B.restrictOpen (U ⊓ V) inf_le_right) c.hom)
    (W : Opens X.carrier) (hW : W ∈ S.opens) (hWP : W ≤ U ⊔ V)
    (hor : W ≤ U ∨ W ≤ V) (h : W ≤ V) :
    glueRho S U V F A B f g W hW hWP hor = transportedRho S le_sup_right F B g W hW h := by
  by_cases hU : W ≤ U
  · rw [glueRho_of_le_left S U V F A B f g W hW hWP hor hU]
    exact transportedRho_eq_of_le_inf S U V F A B f g c hfg hc W hW (le_inf hU h)
  · rw [glueRho_of_not_le_left S U V F A B f g W hW hWP hor hU]

/-- **The glued object, as a solution over `U ∪ V` for the subsystem carried by the members of
the collection contained in `U` or in `V`.** Its identifications are
`Stacks.DerivedGlueing.glueRho`, and their compatibility is
`Stacks.DerivedGlueing.transportedRho_compatibility` on whichever of the two opens contains the
larger of the two members. -/
def glueSolutionOverSubcollection
    (c : (S.restriction (U ⊓ V) U inf_le_left).obj A.obj ≅
      (S.restriction (U ⊓ V) V inf_le_right).obj B.obj)
    (hfg : (S.restrictionComp (U ⊓ V) U (U ⊔ V) inf_le_left le_sup_left).hom.app F ≫
        (S.restriction (U ⊓ V) U inf_le_left).map f.hom ≫ c.hom =
      (S.restrictionComp (U ⊓ V) V (U ⊔ V) inf_le_right le_sup_right).hom.app F ≫
        (S.restriction (U ⊓ V) V inf_le_right).map g.hom)
    (hc : (A.restrictOpen (U ⊓ V) inf_le_left).IsCompatibleHom
      (B.restrictOpen (U ⊓ V) inf_le_right) c.hom) :
    SolutionOver (S.subcollection (opensBelowPair S U V) (opensBelowPair_subset S U V))
      (U ⊔ V) where
  obj := F
  rho W hW hWP := glueRho S U V F A B f g W hW.1 hWP hW.2
  compatibility := by
    intro V₀ W₀ hW₀V₀ hV₀ hW₀ hV₀P
    by_cases hV₀U : V₀ ≤ U
    · rw [glueRho_of_le_left S U V F A B f g V₀ hV₀.1 hV₀P hV₀.2 hV₀U,
        glueRho_of_le_left S U V F A B f g W₀ hW₀.1 (hW₀V₀.trans hV₀P) hW₀.2
          (hW₀V₀.trans hV₀U)]
      exact transportedRho_compatibility S le_sup_left F A f V₀ W₀ hW₀V₀ hV₀.1 hW₀.1 hV₀U
    · have hV₀V : V₀ ≤ V := hV₀.2.resolve_left hV₀U
      rw [glueRho_of_le_right S U V F A B f g c hfg hc V₀ hV₀.1 hV₀P hV₀.2 hV₀V,
        glueRho_of_le_right S U V F A B f g c hfg hc W₀ hW₀.1 (hW₀V₀.trans hV₀P) hW₀.2
          (hW₀V₀.trans hV₀V)]
      exact transportedRho_compatibility S le_sup_right F B g V₀ W₀ hW₀V₀ hV₀.1 hW₀.1 hV₀V

end Glue

/-! ### A prescribed transition is a morphism of solutions for a subsystem -/

/-- **The prescribed transition `ρ^V_W` is a morphism of solutions for any subsystem.** It goes
from the restriction to `W` of the solution over `V` defined by the prescribed object there to
the solution over `W` defined by the prescribed object there, and its compatibility is the
cocycle condition. -/
theorem selfSolutionOverSubcollection_rho_isCompatibleHom (S : LocallyGiven X)
    (𝒟 : Set (Opens X.carrier)) (h𝒟 : 𝒟 ⊆ S.opens) (V W : Opens X.carrier) (hWV : W ≤ V)
    (hV : V ∈ S.opens) (hW : W ∈ S.opens) :
    ((selfSolutionOverSubcollection S 𝒟 h𝒟 V hV).restrictOpen W hWV).IsCompatibleHom
      (selfSolutionOverSubcollection S 𝒟 h𝒟 W hW) (S.rho W V hWV hV hW).hom := by
  intro T hT hTW
  change (S.restriction T W hTW).map (S.rho W V hWV hV hW).hom ≫
        (S.rho T W hTW hW (h𝒟 hT)).hom =
      (S.restrictionComp T W V hTW hWV).inv.app (S.obj V hV) ≫
        (S.rho T V (hTW.trans hWV) hV (h𝒟 hT)).hom
  rw [S.cocycle T W V hTW hWV hV hW (h𝒟 hT), Iso.inv_hom_id_app_assoc]

/-! ### Assembling the solution over the union -/

/-- **A solution over `U ∪ V` for the subsystem carried by the members contained in `U` or in
`V` is a solution over `U ∪ V` for the system**, granted the uniqueness clause of
[Stacks, Tag 0D68] for that subsystem.

This is the second use of the uniqueness clause in the source's proof of the two-open case of
[Stacks, Tag 0D6A], and the only step that needs the subsystem.  Over a member `W` of the
collection contained in `U ∪ V` the restriction of the given solution and the prescribed object
are both solutions over `W` for the subsystem — the second by
`Stacks.DerivedGlueing.selfSolutionOverSubcollection`, whose membership hypothesis is taken in
the ambient collection — and `W` is a union of members of the subsystem, by
`Stacks.DerivedGlueing.mem_eq_sSup_opensBelowPair`.  So the clause produces the identification,
uniquely; its compatibility with the prescribed transitions is that same uniqueness applied to
the smaller member, both sides of the compatibility being morphisms of the same pair of
solutions by `Stacks.DerivedGlueing.restrictOpen_comparison_isCompatibleHom`,
`Stacks.DerivedGlueing.SolutionOver.IsCompatibleHom.restrictOpen` and
`Stacks.DerivedGlueing.selfSolutionOverSubcollection_rho_isCompatibleHom`. -/
theorem nonempty_solutionOver_sup_of_subcollectionSolution (S : LocallyGiven X)
    (U V : Opens X.carrier) (hU : U ∈ S.opens) (hV : V = sSup {W | W ∈ S.opens ∧ W ≤ V})
    (hinter : ∀ U' ∈ S.opens, ∀ V' ∈ S.opens,
      U' ⊓ V' = sSup {W | W ∈ S.opens ∧ W ≤ U' ⊓ V'})
    (hExt : ∀ (W : Opens X.carrier) (hW : W ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj W hW) (S.obj W hW) i))
    (huniq : HasUniqueSolutionOverIso
      (S.subcollection (opensBelowPair S U V) (opensBelowPair_subset S U V)))
    (FS : SolutionOver
      (S.subcollection (opensBelowPair S U V) (opensBelowPair_subset S U V)) (U ⊔ V)) :
    Nonempty (SolutionOver S (U ⊔ V)) := by
  have key : ∀ (W : Opens X.carrier) (hW : W ∈ S.opens) (hWP : W ≤ U ⊔ V),
      ∃! φ : (FS.restrictOpen W hWP).obj ≅
          (selfSolutionOverSubcollection S (opensBelowPair S U V)
            (opensBelowPair_subset S U V) W hW).obj,
        (FS.restrictOpen W hWP).IsCompatibleHom
          (selfSolutionOverSubcollection S (opensBelowPair S U V)
            (opensBelowPair_subset S U V) W hW) φ.hom :=
    fun W hW hWP => huniq W (mem_eq_sSup_opensBelowPair S U V hU hV hinter W hW hWP)
      (inf_eq_sSup_opensBelowPair S U V hinter)
      (fun U' hU' i hi => hExt U' (opensBelowPair_subset S U V hU') i hi)
      (FS.restrictOpen W hWP)
      (selfSolutionOverSubcollection S (opensBelowPair S U V)
        (opensBelowPair_subset S U V) W hW)
  choose rho hrho hrhouniq using key
  refine ⟨{ obj := FS.obj, rho := rho, compatibility := ?_ }⟩
  intro V₀ W₀ hW₀V₀ hV₀ hW₀ hV₀P
  have hpsi := (restrictOpen_comparison_isCompatibleHom FS hV₀P hW₀V₀).comp
    (((hrho V₀ hV₀ hV₀P).restrictOpen hW₀V₀).comp
      (selfSolutionOverSubcollection_rho_isCompatibleHom S (opensBelowPair S U V)
        (opensBelowPair_subset S U V) V₀ W₀ hW₀V₀ hV₀ hW₀))
  exact congrArg (fun e => e.hom)
    (hrhouniq W₀ hW₀ (hW₀V₀.trans hV₀P)
      ((S.restrictionComp W₀ V₀ (U ⊔ V) hW₀V₀ hV₀P).app FS.obj ≪≫
        (S.restriction W₀ V₀ hW₀V₀).mapIso (rho V₀ hV₀ hV₀P) ≪≫
        S.rho W₀ V₀ hW₀V₀ hV₀ hW₀) hpsi)

/-- **The two-open case at one pair of opens, from the two instances of the uniqueness clause
that the argument uses and the glueing lemma at that pair.**  This is the minimal interface: the
clause is used over `U ∩ V`, for the given system, to compare the two solutions there, and over
the members of the collection below `U ∪ V`, for the subsystem carried by the members below `U`
or below `V`.  Nothing else about the system is assumed. -/
theorem nonempty_solutionOver_sup_of_glueing (S : LocallyGiven X) (U V : Opens X.carrier)
    (hU : U ∈ S.opens) (hV : V = sSup {W | W ∈ S.opens ∧ W ≤ V})
    (hUV : U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hinter : ∀ U' ∈ S.opens, ∀ V' ∈ S.opens,
      U' ⊓ V' = sSup {W | W ∈ S.opens ∧ W ≤ U' ⊓ V'})
    (hExt : ∀ (W : Opens X.carrier) (hW : W ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj W hW) (S.obj W hW) i))
    (huniqS : HasUniqueSolutionOverIso S)
    (huniqSub : HasUniqueSolutionOverIso
      (S.subcollection (opensBelowPair S U V) (opensBelowPair_subset S U V)))
    (hglue : ∀ (A : OpenDerivedCategory X U) (B : OpenDerivedCategory X V)
      (c : (S.restriction (U ⊓ V) U inf_le_left).obj A ≅
        (S.restriction (U ⊓ V) V inf_le_right).obj B),
      ∃ (F : OpenDerivedCategory X (U ⊔ V))
        (f : (S.restriction U (U ⊔ V) le_sup_left).obj F ≅ A)
        (g : (S.restriction V (U ⊔ V) le_sup_right).obj F ≅ B),
        (S.restrictionComp (U ⊓ V) U (U ⊔ V) inf_le_left le_sup_left).hom.app F ≫
            (S.restriction (U ⊓ V) U inf_le_left).map f.hom ≫ c.hom =
          (S.restrictionComp (U ⊓ V) V (U ⊔ V) inf_le_right le_sup_right).hom.app F ≫
            (S.restriction (U ⊓ V) V inf_le_right).map g.hom)
    (A : SolutionOver S U) (B : SolutionOver S V) :
    Nonempty (SolutionOver S (U ⊔ V)) := by
  obtain ⟨c, hc, -⟩ := huniqS (U ⊓ V) hUV hinter hExt
    (A.restrictOpen (U ⊓ V) inf_le_left) (B.restrictOpen (U ⊓ V) inf_le_right)
  obtain ⟨F, f, g, hfg⟩ := hglue A.obj B.obj c
  exact nonempty_solutionOver_sup_of_subcollectionSolution S U V hU hV hinter hExt huniqSub
    (glueSolutionOverSubcollection S U V F A B f g c hfg hc)

/-! ### The reduction -/

/-- **The two-open case of [Stacks, Tag 0D6A], granted the uniqueness clause of
[Stacks, Tag 0D68] for every subsystem and the glueing lemma [Stacks, Tag 08DG] in the
vocabulary of Situation 0D67.**

Let `U` be a member of the collection, let `V` be a union of members, assume that the
intersection of two members is a union of members and that `U ∩ V` is one, and that the
prescribed objects have no negative self-Ext.  Then a solution over `U` and a solution over `V`
glue to a solution over `U ∪ V`.

The proof follows the source.  The uniqueness clause over `U ∩ V`, which the two restrictions
both solve, gives the comparison isomorphism of [Stacks, Tag 0D69]; the glueing lemma gives an
object `F` over `U ∪ V` restricting to the two given ones compatibly with it;
`Stacks.DerivedGlueing.glueSolutionOverSubcollection` makes `F` a solution for the subsystem
carried by the members contained in `U` or in `V`; and
`Stacks.DerivedGlueing.nonempty_solutionOver_sup_of_subcollectionSolution` turns that into a
solution for the system, using the uniqueness clause for the subsystem.

Why the hypothesis is the clause for every subsystem and not for the system alone is explained
in the module documentation. -/
theorem gluesAlongTwoOpens_of_gluesObjectsAlongTwoOpens (S : LocallyGiven X)
    (huniq : ∀ (𝒟 : Set (Opens X.carrier)) (h𝒟 : 𝒟 ⊆ S.opens),
      HasUniqueSolutionOverIso (S.subcollection 𝒟 h𝒟))
    (hglue : GluesObjectsAlongTwoOpens S) : GluesAlongTwoOpens S := fun U hU V hV hUV hinter
    hExt A B =>
  nonempty_solutionOver_sup_of_glueing S U V hU hV hUV hinter hExt
    (huniq S.opens (fun _ hW => hW))
    (huniq (opensBelowPair S U V) (opensBelowPair_subset S U V)) (hglue U V) A B

/-- **The same, from the sheaf condition of [Stacks, Tag 0D66] part (2) for every subsystem.**
The uniqueness clause of [Stacks, Tag 0D68] follows from the glueing of morphisms, by
`Stacks.DerivedGlueing.hasUniqueSolutionOverIso_of_hasGluingForHomsOver`, so this is the form of
the reduction in which the remaining uniqueness input is the sheaf condition this development
already carries in the vocabulary of a morphism of ringed spaces and a basis of the target. -/
theorem gluesAlongTwoOpens_of_hasGluingForHomsOver_subcollections (S : LocallyGiven X)
    (hhom : ∀ (𝒟 : Set (Opens X.carrier)) (h𝒟 : 𝒟 ⊆ S.opens),
      HasGluingForHomsOver (S.subcollection 𝒟 h𝒟))
    (hglue : GluesObjectsAlongTwoOpens S) : GluesAlongTwoOpens S :=
  gluesAlongTwoOpens_of_gluesObjectsAlongTwoOpens S
    (fun 𝒟 h𝒟 => hasUniqueSolutionOverIso_of_hasGluingForHomsOver _ (hhom 𝒟 h𝒟)) hglue

end Stacks.DerivedGlueing

end
