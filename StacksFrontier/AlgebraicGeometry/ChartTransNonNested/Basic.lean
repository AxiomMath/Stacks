module

public import StacksFrontier.AlgebraicGeometry.ChartTransNonNested.Glue
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# The non-nested chart comparison, from comparisons over a refinement

`Stacks.AlgebraicGeometry.SchemeModuleGlue.ChartGlueData` asks for a comparison isomorphism
`trans i j` between the sections of the two chart modules over an **arbitrary** open `V` of `X`
contained in both `U i` and `U j`, compatible with restriction and satisfying the cocycle
condition for arbitrary triples. For the charts of a relative projective spectrum the comparison
one has is quite different in shape: it comes from Tag 01NO, and Tag 01NO compares the twists on
`Proj Γ(U, A)` with those on `Proj Γ(V, A)` for a **nested** pair `U ⊆ V` of affine opens of the
base. Two affine opens of a scheme do not form a nested pair, and their intersection is not
affine, so it indexes no chart and no nested comparison applies to it.

This file is the step that bridges the two. It takes comparison isomorphisms indexed by a
*refinement* — a family `L : κ → X.Opens` which is a basis-like family of opens, with a
comparison over each member that lies below both `U i` and `U j` — and produces the three
non-nested fields of a `ChartGlueData`. Nothing is assumed about `U i ⊓ U j` beyond the two
containments; in particular it is **not** assumed affine, quasi-separated or anything else, and
the development's charts are not assumed to be indexed by a family closed under intersection.

## Main definitions

* `Stacks.AlgebraicGeometry.ChartTransNonNested.IsRefinedBy`: an open is refined by a family of
  opens when the members of the family contained in it cover it.
* `Stacks.AlgebraicGeometry.ChartTransNonNested.RefinementData`: charts, chart modules, and
  comparison isomorphisms over the members of a refinement, with the two compatibilities the
  construction needs.
* `Stacks.AlgebraicGeometry.ChartTransNonNested.RefinementData.trans`: **the non-nested
  comparison**, over an arbitrary open contained in two of the chart opens.
* `Stacks.AlgebraicGeometry.ChartTransNonNested.RefinementData.toChartGlueData`: **the
  `ChartGlueData`.** All three cocycle fields are discharged.

## Main results

* `Stacks.AlgebraicGeometry.ChartTransNonNested.RefinementData.trans_app_of_le`: over an open
  contained in a member of the refinement, the non-nested comparison is that member's comparison.
  This is the only computational handle on `trans`, and the two cocycle laws are proved through
  it.
* `Stacks.AlgebraicGeometry.ChartTransNonNested.RefinementData.trans_map` and `trans_trans`:
  compatibility with restriction, and the cocycle condition for arbitrary triples.

## What the two compatibilities are, and why neither is avoidable

`loc_comp` is the cocycle condition **over a single member of the refinement**: the comparisons
`i → j → l` compose there. For a family of comparisons obtained by identifying each chart module
with one local model over that member — which is how a nested comparison produces them — it holds
by construction, the two sides being the same composite with the model's identification cancelled
in the middle.

`loc_mono` is the compatibility along a **nested pair of refinement members**: shrinking the
member does not change the comparison. This is what makes the glueing possible at all, and it is
the one place a genuine cocycle for the nested comparisons is needed. Without it the comparisons
over two different members of the refinement need not agree on the overlap, and there is nothing
to glue; and no weaker hypothesis stated on arbitrary overlaps would do, since an overlap of two
members of a refinement is again not a member.

Given those two, the cocycle condition for arbitrary triples over an arbitrary open is *not*
further mathematical content: it is checked on a cover by members of the refinement, where all
three comparisons are the local ones, and `loc_comp` closes it. That is recorded here because the
alternative route — proving `trans_trans` by a rigidity argument, showing the composite
endomorphism to be multiplicative and to fix the homogeneous sections — is strictly more work and
is not needed once the comparisons factor through local models.

## Implementation notes

**Containment proofs are never transported, and `rw` is never used on a comparison.** The
comparison `loc k i j hi hj` takes its two containments as explicit arguments, so two instances
of it at different proofs of the same containment are distinct *terms* while being definitionally
equal by proof irrelevance. Term-mode `Eq.trans` chains therefore typecheck where `rw` cannot
even find the pattern, and every proof below that has to move between two spellings of a
containment is written that way. This is the same phenomenon recorded in
`StacksFrontier/AlgebraicGeometry/SchemeModuleGlue/Chart.lean` for `rw` and
`AlgebraicGeometry.Scheme.Modules`, in a different guise.

The refinement hypothesis is stated as a containment in a supremum over the *subtype* of indices
lying below the given open, `T ≤ ⨆ m : {m // L m ≤ T}, L m.1`, rather than as the
`TopologicalSpace.Opens.IsBasis` predicate, and it is **assumed only at the chart opens and at
the pairwise meets of the refinement's own members**, not at every open of `X`. That restriction
is not economy, it is necessary: the intended refinement for a relative projective spectrum is
the family of inverse images of the affine opens of the base, which is not a basis of the
topology of the relative Proj — an open contained in a single fibre contains the inverse image of
no nonempty open of the base — so a hypothesis quantified over every open of `X` would be
unsatisfiable there, while the two assumed instances both hold, being statements about the affine
opens of the *base* pulled back. Cofinality over an arbitrary meet is then derived
(`Stacks.AlgebraicGeometry.ChartTransNonNested.IsRefinedBy.inf`), which is what the two cocycle
laws consume; they are proved over a cover of `V` by the meets `V ⊓ L n` rather than by members
contained in `V`, for the same reason.

## References

* [Stacks Project, Tag 00AN](https://stacks.math.columbia.edu/tag/00AN)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ChartTransNonNested

/-- The module on a chart, pushed forward to the ambient scheme and read as a presheaf of
`𝒪_X`-modules. A section of this over an open `V` of `X` *is* a section of the chart module over
the preimage of `V`. -/
public abbrev pushforwardVal {X Y : Scheme.{u}} (f : Y ⟶ X) (M : Y.Modules) :
    PresheafOfModules.{u} X.ringCatSheaf.obj :=
  ((Scheme.Modules.pushforward f).obj M).val

/-! ### Cofinality of a family of opens -/

/-- **An open is refined by a family of opens** when it is covered by the members of the family
contained in it. The containment is carried by the index of the covering family, since the
comparison over a member is only available where the member lies below the open in question.

This is the relativisation of `TopologicalSpace.Opens.IsBasis` that the construction needs: the
family it is applied to — the inverse images of the affine opens of the base of a relative
projective spectrum — is emphatically **not** a basis of the topology of `X`, since a small open
of a fibre contains no inverse image of a nonempty open of the base at all. What is true of it,
and all that is used, is that it refines each chart open and each pairwise meet of its own
members. -/
public def IsRefinedBy {X : Scheme.{u}} {κ : Type u} (L : κ → X.Opens) (T : X.Opens) : Prop :=
  T ≤ ⨆ m : {m : κ // L m ≤ T}, L m.1

/-- **A family refining its own pairwise meets refines the meet of any two opens it refines.**

This is why the two hypotheses of
`Stacks.AlgebraicGeometry.ChartTransNonNested.RefinementData` suffice, even though cofinality is
not preserved by meets for a general family: a point of `T ⊓ T'` lies in a member below `T` and
in a member below `T'`, and the family refines the meet of those two, which lies below
`T ⊓ T'`. -/
public theorem IsRefinedBy.inf {X : Scheme.{u}} {κ : Type u} {L : κ → X.Opens}
    (hL : ∀ k k' : κ, IsRefinedBy L (L k ⊓ L k')) {T T' : X.Opens}
    (hT : IsRefinedBy L T) (hT' : IsRefinedBy L T') : IsRefinedBy L (T ⊓ T') := by
  rintro x ⟨hxT, hxT'⟩
  obtain ⟨m, hm⟩ := Opens.mem_iSup.mp (hT hxT)
  obtain ⟨m', hm'⟩ := Opens.mem_iSup.mp (hT' hxT')
  obtain ⟨n, hn⟩ := Opens.mem_iSup.mp (hL m.1 m'.1 ⟨hm, hm'⟩)
  exact Opens.mem_iSup.mpr ⟨⟨n.1, n.2.trans (inf_le_inf m.2 m'.2)⟩, hn⟩

/-- **The inverse images of the affine opens of the base refine every inverse image.** For a
morphism of schemes `f : X ⟶ S` and an open `T` of `S`, the family of inverse images of the
affine opens of `S` refines `f ⁻¹ᵁ T`: the affine opens of `S` are a basis of its topology, and
taking inverse images preserves both membership and containment.

This is what makes the hypotheses of
`Stacks.AlgebraicGeometry.ChartTransNonNested.RefinementData` satisfiable for the charts of a
relative projective spectrum. Those charts' opens *are* the inverse images of the affine opens of
the base (`Stacks.AlgebraicGeometry.RelativeProjTwistGlue.chart_image_top`), and the family of
such inverse images is not a basis of the topology of the relative Proj — which is why the
refinement hypothesis is assumed only where it is. -/
public theorem isRefinedBy_preimage_affineOpens {X S : Scheme.{u}} (f : X ⟶ S) (T : S.Opens) :
    IsRefinedBy (fun W : S.affineOpens => f ⁻¹ᵁ (W.1 : S.Opens)) (f ⁻¹ᵁ T) := by
  intro x hx
  obtain ⟨W, hWmem, hxW, hWT⟩ :=
    Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens (show f.base x ∈ T from hx)
  exact Opens.mem_iSup.mpr ⟨⟨⟨W, hWmem⟩, fun _ hy => hWT hy⟩, hxW⟩

/-- The same family refines the meet of any two of its own members, the meet being the inverse
image of the meet of the two affine opens. -/
public theorem isRefinedBy_inf_preimage_affineOpens {X S : Scheme.{u}} (f : X ⟶ S)
    (W W' : S.affineOpens) :
    IsRefinedBy (fun W : S.affineOpens => f ⁻¹ᵁ (W.1 : S.Opens))
      (f ⁻¹ᵁ (W.1 : S.Opens) ⊓ f ⁻¹ᵁ (W'.1 : S.Opens)) :=
  (isRefinedBy_preimage_affineOpens f ((W.1 : S.Opens) ⊓ (W'.1 : S.Opens)) :
    IsRefinedBy _ (f ⁻¹ᵁ ((W.1 : S.Opens) ⊓ (W'.1 : S.Opens))))

/-- **Chart data together with comparison isomorphisms over a refinement.**

`chart`, `hom` and `sheaf` are the chart data of a
`Stacks.AlgebraicGeometry.SchemeModuleGlue.ChartGlueData`. The rest is what replaces its three
cocycle fields: a basis-like family `L : κ → X.Opens`, and over each member of that family lying
below both `U i` and `U j` an isomorphism between the sections of the `i`-th and the `j`-th chart
module, composing over a single member and unchanged by shrinking the member. -/
public structure RefinementData (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens) where
  /-- The `i`-th chart. -/
  chart (i : ι) : Scheme.{u}
  /-- The morphism from the `i`-th chart to `X`. -/
  hom (i : ι) : chart i ⟶ X
  /-- The sheaf of modules carried by the `i`-th chart. -/
  sheaf (i : ι) : (chart i).Modules
  /-- The index type of the refinement. -/
  κ : Type u
  /-- The refinement: a family of opens of `X`. -/
  L : κ → X.Opens
  /-- Each chart open is covered by the members of the refinement contained in it. -/
  isRefinedBy_chartOpen (i : ι) : IsRefinedBy L (U i)
  /-- So is the meet of any two members of the refinement. -/
  isRefinedBy_inf (k k' : κ) : IsRefinedBy L (L k ⊓ L k')
  /-- The comparison isomorphism over a member of the refinement lying below two chart opens. -/
  loc (k : κ) (i j : ι) (hi : L k ≤ U i) (hj : L k ≤ U j) :
    TopCat.Sheaf.LocalModuleEquiv (pushforwardVal (hom i) (sheaf i))
      (pushforwardVal (hom j) (sheaf j)) (L k)
  /-- **The cocycle condition over a single member of the refinement.** -/
  loc_comp (k : κ) (i j l : ι) (hi : L k ≤ U i) (hj : L k ≤ U j) (hl : L k ≤ U l)
    (V : X.Opens) (hV : V ≤ L k) (s : (pushforwardVal (hom i) (sheaf i)).obj (op V)) :
    (loc k j l hj hl).app V hV ((loc k i j hi hj).app V hV s)
      = (loc k i l hi hl).app V hV s
  /-- **Shrinking a member of the refinement does not change the comparison.** -/
  loc_mono (k k' : κ) (i j : ι) (hkk' : L k ≤ L k') (hi : L k' ≤ U i) (hj : L k' ≤ U j)
    (V : X.Opens) (hV : V ≤ L k) (s : (pushforwardVal (hom i) (sheaf i)).obj (op V)) :
    (loc k i j (hkk'.trans hi) (hkk'.trans hj)).app V hV s
      = (loc k' i j hi hj).app V (hV.trans hkk') s

namespace RefinementData

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (G : RefinementData X U)

/-- The pushforward of the `i`-th chart module is a sheaf: it is the pushforward of a sheaf of
modules along a morphism of schemes. -/
public theorem isSheaf_pushforwardVal (i : ι) :
    CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (pushforwardVal (G.hom i) (G.sheaf i)).presheaf :=
  ((Scheme.Modules.pushforward (G.hom i)).obj (G.sheaf i)).isSheaf

/-! ### The covering family for a pair of chart opens -/

/-- The members of the refinement lying below both `U i` and `U j`. This is the index of the
covering family the comparison `trans i j` is glued over. -/
public abbrev pairIndex (i j : ι) : Type u := {m : G.κ // G.L m ≤ U i ⊓ U j}

/-- The comparison isomorphisms over the members of the refinement below both `U i` and `U j`. -/
public noncomputable def pairLoc (i j : ι) (m : G.pairIndex i j) :
    TopCat.Sheaf.LocalModuleEquiv (pushforwardVal (G.hom i) (G.sheaf i))
      (pushforwardVal (G.hom j) (G.sheaf j)) (G.L m.1) :=
  G.loc m.1 i j (m.2.trans inf_le_left) (m.2.trans inf_le_right)

/-- The refinement refines the meet of two chart opens. -/
public theorem isRefinedBy_inf_chartOpens (i j : ι) : IsRefinedBy G.L (U i ⊓ U j) :=
  (G.isRefinedBy_chartOpen i).inf G.isRefinedBy_inf (G.isRefinedBy_chartOpen j)

/-- Those members cover `U i ⊓ U j`. -/
public theorem le_iSup_pairIndex (i j : ι) :
    U i ⊓ U j ≤ ⨆ m : G.pairIndex i j, G.L m.1 :=
  G.isRefinedBy_inf_chartOpens i j

/-- **The comparisons over two members of the refinement agree on any open below both.**

This is the hypothesis the glueing engine needs, and it is where the refinement refining its own
pairwise meets is used: the meet of the two members is covered by members contained in it, so the
open is covered by its meets with those, and over such a meet both comparisons are that member's
own comparison by `loc_mono`. The target being a sheaf then promotes the agreement from the cover
to the open itself. -/
public theorem pairLoc_app_eq (i j : ι) (m m' : G.pairIndex i j) (V : X.Opens)
    (hm : V ≤ G.L m.1) (hm' : V ≤ G.L m'.1)
    (s : (pushforwardVal (G.hom i) (G.sheaf i)).obj (op V)) :
    (G.pairLoc i j m).app V hm s = (G.pairLoc i j m').app V hm' s := by
  -- over `V ⊓ L n` with `L n ≤ L m`, the restriction of the comparison for `m` is `loc n`
  have key := fun (m : G.pairIndex i j) (hm : V ≤ G.L m.1) (n : G.κ) (hn : G.L n ≤ G.L m.1) =>
    ((G.pairLoc i j m).naturality hm (inf_le_left : V ⊓ G.L n ≤ V) s).symm.trans
      (G.loc_mono n m.1 i j hn (m.2.trans inf_le_left) (m.2.trans inf_le_right)
        (V ⊓ G.L n) inf_le_right _).symm
  exact TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf (G.isSheaf_pushforwardVal j)
    (fun n : {n : G.κ // G.L n ≤ G.L m.1 ⊓ G.L m'.1} => V ⊓ G.L n.1)
    (fun _ => inf_le_left)
    (TopCat.Sheaf.le_iSup_inf_of_le ((le_inf hm hm').trans (G.isRefinedBy_inf m.1 m'.1)))
    fun n => (key m hm n.1 (n.2.trans inf_le_left)).trans
      (key m' hm' n.1 (n.2.trans inf_le_right)).symm

/-! ### The non-nested comparison -/

/-- The glued comparison, as a local isomorphism on `U i ⊓ U j`. -/
public noncomputable def transEquiv (i j : ι) :
    TopCat.Sheaf.LocalModuleEquiv (pushforwardVal (G.hom i) (G.sheaf i))
      (pushforwardVal (G.hom j) (G.sheaf j)) (U i ⊓ U j) :=
  TopCat.Sheaf.LocalModuleEquiv.glueLE (G.isSheaf_pushforwardVal i) (G.isSheaf_pushforwardVal j)
    (G.pairLoc i j) (G.pairLoc_app_eq i j) (G.le_iSup_pairIndex i j)

/-- **The non-nested chart comparison.** For an arbitrary open `V` of `X` contained in both `U i`
and `U j`, an isomorphism of `𝒪_X(V)`-modules between the sections of the two chart modules over
the respective preimages of `V`.

No affineness, separatedness or quasi-separatedness hypothesis enters: `U i ⊓ U j` is covered by
members of the refinement lying inside it, and the comparison is glued over that cover. -/
public noncomputable def trans (i j : ι) {V : X.Opens} (hi : V ≤ U i) (hj : V ≤ U j) :
    (pushforwardVal (G.hom i) (G.sheaf i)).obj (op V) ≃ₗ[X.ringCatSheaf.obj.obj (op V)]
      (pushforwardVal (G.hom j) (G.sheaf j)).obj (op V) :=
  (G.transEquiv i j).app V (le_inf hi hj)

/-- **Over an open contained in a member of the refinement, the non-nested comparison is that
member's comparison.** Every property of `trans` below is proved through this. -/
public theorem trans_app_of_le (i j : ι) {V : X.Opens} (hi : V ≤ U i) (hj : V ≤ U j)
    (k : G.κ) (hk : G.L k ≤ U i ⊓ U j) (hV : V ≤ G.L k)
    (s : (pushforwardVal (G.hom i) (G.sheaf i)).obj (op V)) :
    G.trans i j hi hj s
      = (G.loc k i j (hk.trans inf_le_left) (hk.trans inf_le_right)).app V hV s :=
  TopCat.Sheaf.LocalModuleEquiv.glueLE_app_of_le (G.isSheaf_pushforwardVal i)
    (G.isSheaf_pushforwardVal j) (G.pairLoc i j) (G.pairLoc_app_eq i j)
    (G.le_iSup_pairIndex i j) (i := ⟨k, hk⟩) (le_inf hi hj) hV s

/-- **The non-nested comparison commutes with the restriction maps.** This is `trans_map` of
`Stacks.AlgebraicGeometry.SchemeModuleGlue.ChartGlueData`, and it is the naturality of the glued
local isomorphism. -/
public theorem trans_map (i j : ι) {V W : X.Opens} (hi : V ≤ U i) (hj : V ≤ U j) (hWV : W ≤ V)
    (s : (pushforwardVal (G.hom i) (G.sheaf i)).obj (op V)) :
    G.trans i j (hWV.trans hi) (hWV.trans hj)
        ((pushforwardVal (G.hom i) (G.sheaf i)).resLE hWV s)
      = (pushforwardVal (G.hom j) (G.sheaf j)).resLE hWV (G.trans i j hi hj s) :=
  (G.transEquiv i j).naturality (le_inf hi hj) hWV s

/-- **The cocycle condition, for an arbitrary triple of charts over an arbitrary open.**

Checked on a cover of `V` by members of the refinement contained in it: over such a member all
three comparisons are the local ones by
`Stacks.AlgebraicGeometry.ChartTransNonNested.RefinementData.trans_app_of_le`, and `loc_comp`
closes it. No rigidity argument and no multiplicativity of a composite endomorphism is used. -/
public theorem trans_trans (i j l : ι) {V : X.Opens} (hi : V ≤ U i) (hj : V ≤ U j) (hl : V ≤ U l)
    (s : (pushforwardVal (G.hom i) (G.sheaf i)).obj (op V)) :
    G.trans j l hj hl (G.trans i j hi hj s) = G.trans i l hi hl s :=
  TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf (G.isSheaf_pushforwardVal l)
    (fun n : {n : G.κ // G.L n ≤ U i ⊓ U j ⊓ U l} => V ⊓ G.L n.1) (fun _ => inf_le_left)
    (TopCat.Sheaf.le_iSup_inf_of_le ((le_inf (le_inf hi hj) hl).trans
      ((G.isRefinedBy_inf_chartOpens i j).inf G.isRefinedBy_inf (G.isRefinedBy_chartOpen l))))
    fun n => by
      have hVn : V ⊓ G.L n.1 ≤ V := inf_le_left
      have hnL : V ⊓ G.L n.1 ≤ G.L n.1 := inf_le_right
      have hni : G.L n.1 ≤ U i := n.2.trans (inf_le_left.trans inf_le_left)
      have hnj : G.L n.1 ≤ U j := n.2.trans (inf_le_left.trans inf_le_right)
      have hnl : G.L n.1 ≤ U l := n.2.trans inf_le_right
      refine Eq.trans (G.trans_map j l hj hl hVn _).symm
        (Eq.trans ?_ (G.trans_map i l hi hl hVn s))
      refine Eq.trans (congrArg (G.trans j l (hVn.trans hj) (hVn.trans hl))
        (Eq.trans (G.trans_map i j hi hj hVn s).symm
          (G.trans_app_of_le i j (hVn.trans hi) (hVn.trans hj) n.1 (le_inf hni hnj) hnL _))) ?_
      refine Eq.trans (G.trans_app_of_le j l (hVn.trans hj) (hVn.trans hl) n.1
        (le_inf hnj hnl) hnL _) ?_
      refine Eq.trans (G.loc_comp n.1 i j l hni hnj hnl (V ⊓ G.L n.1) hnL _) ?_
      exact (G.trans_app_of_le i l (hVn.trans hi) (hVn.trans hl) n.1 (le_inf hni hnl) hnL _).symm

/-! ### The glueing datum -/

/-- **The glueing datum for the chart modules.** All three of
`Stacks.AlgebraicGeometry.SchemeModuleGlue.ChartGlueData`'s cocycle fields are discharged from
the comparisons over the refinement. -/
public noncomputable def toChartGlueData : SchemeModuleGlue.ChartGlueData X U where
  chart := G.chart
  hom := G.hom
  sheaf := G.sheaf
  trans := G.trans
  trans_map := G.trans_map
  trans_trans := G.trans_trans

/-- The chart of `G.toChartGlueData` at `i` is `G.chart i`. -/
@[simp]
public theorem toChartGlueData_chart (i : ι) : G.toChartGlueData.chart i = G.chart i := rfl

/-- The chart morphism of `G.toChartGlueData` at `i` is `G.hom i`. -/
@[simp]
public theorem toChartGlueData_hom (i : ι) : G.toChartGlueData.hom i = G.hom i := rfl

/-- The chart module of `G.toChartGlueData` at `i` is `G.sheaf i`. -/
@[simp]
public theorem toChartGlueData_sheaf (i : ι) : G.toChartGlueData.sheaf i = G.sheaf i := rfl

/-- The comparison map of `G.toChartGlueData` from chart `i` to chart `j` over `V` is
`G.trans i j`. -/
@[simp]
public theorem toChartGlueData_trans (i j : ι) {V : X.Opens} (hi : V ≤ U i) (hj : V ≤ U j)
    (s : (pushforwardVal (G.hom i) (G.sheaf i)).obj (op V)) :
    G.toChartGlueData.trans i j hi hj s = G.trans i j hi hj s := rfl

end RefinementData

end Stacks.AlgebraicGeometry.ChartTransNonNested

end
