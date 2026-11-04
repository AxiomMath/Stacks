module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.Syntomic
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSource.SourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Syntomic
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SyntomicCoveringBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SyntomicCoveringComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SyntomicCoverings

/-!
# Source locality for the syntomic topology transferred from schemes to algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`, and let `P` be a property of morphisms of
schemes which is étale local on the source and target (**Stacks 04QZ**). **Stacks 03MJ** turns
`P` into the property `AlgebraicGeometry.Space.HoldsOnEveryEtaleChart B S hS P` of morphisms of
algebraic spaces over `S`. **Stacks 06ER** says that if `P` is local on the source for one of
the five topologies of **Stacks 03YH** then so is the associated property of morphisms of
algebraic spaces. This module proves the **syntomic case**, and reads off from it that
syntomicity of morphisms of algebraic spaces is syntomic local on the source
(**Stacks 06F0**).

The two axioms of the syntomic topology the transfer consumes are composition and base change
for syntomic covering families, clauses (2) and (3) of **Stacks 041B**. The composition clause
is `AlgebraicGeometry.Space.isSyntomicCovering_comp`, which lives in
`StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SyntomicCoveringComposition`; the base-change
clause is `AlgebraicGeometry.Space.isSyntomicCovering_pullback`, which lives in
`StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SyntomicCoveringBaseChange` and is proved there
from base change for syntomic morphisms of algebraic spaces (**Stacks 03Z9**) together with the
joint-surjectivity criterion of **Stacks 03H4**.

The transfer itself is the argument
`AlgebraicGeometry.Space.isLocalAtSource_fpqc_of_schemes` runs for the fpqc topology and
`AlgebraicGeometry.Space.isLocalAtSource_etale_of_schemes` for the étale one. Given `f : X ⟶ Y`
and a syntomic covering `{Zᵢ ⟶ X}`, choose a surjective étale scheme atlas `V ⟶ Y`, lift it to
a surjective étale chart `T₀ ⟶ X` over a morphism `α : T₀ ⟶ V` of the site (**Stacks 02X1**),
base-change the covering along `T₀ ⟶ X`, choose a surjective étale scheme atlas `Wᵢ` of each
member of the base-changed family — an étale covering, hence a syntomic one by
**Stacks 0DFB** — and compose. The resulting family `{Wᵢ ⟶ T₀}` consists of morphisms of the
*site*, and a syntomic covering of algebraic spaces whose members and target are representable
is a syntomic covering of schemes, which is
`AlgebraicGeometry.Space.Topology.isCovering_yoneda`. With both sides of the equivalence now
expressed on schemes, source locality of `P` for the syntomic topology of schemes gives the two
implications, and **Stacks 03MJ** carries them back.

## Main results

* `AlgebraicGeometry.Space.isSyntomicCovering_pullback_snd`: the base-change clause of
  Stacks 041B in the orientation the transfer consumes.
* `AlgebraicGeometry.Space.isLocalAtSource_syntomic_of_schemes`: **Stacks 06ER**, the syntomic
  case.
* `AlgebraicGeometry.Space.syntomic_isLocalAtSource_syntomic`: **Stacks 06F0**.

## Implementation notes

`isLocalAtSource_syntomic_of_schemes` is **deliberately not tagged** `@[stacks 06ER]`, for the
reason recorded in `StacksFrontier/AlgebraicGeometry/Spaces/FpqcSourceLocalityTransfer.lean`:
Stacks 06ER asserts the transfer for all five topologies `fpqc`, `fppf`, `syntomic`, `smooth`
and `étale` at once, and this theorem is the `syntomic` instance of it only. With the fpqc,
étale and syntomic cases now in the tree, the two still missing are `fppf` and `smooth`, each
of which needs the composition and base-change lemmas for its own covering families.

Stacks 06F0 itself is a single-topology statement and is tagged: syntomicity of morphisms of
schemes is étale local on the source and target (**Stacks 04R3**,
`AlgebraicGeometry.syntomic_isEtaleLocalOnSourceAndTarget`) and local on the source for the
syntomic topology of schemes (**Stacks 036S**,
`AlgebraicGeometry.Syntomic.isLocalAtSource_syntomicPrecoverage`), which are exactly the two
hypotheses of the transfer.

The base-change clause of Stacks 041B is stated, as for the other four topologies, for the
*first* projection of the presheaf fibre product, whereas the transfer consumes the base change
of a covering family along a chart of its target as a family of *second* projections;
`isSyntomicCovering_pullback_snd` below is that orientation, proved from the cartesian square of
**Stacks 02X2** and Stacks 03H4 rather than by transporting along the symmetry of the fibre
product. It reuses `AlgebraicGeometry.Space.isSyntomic_of_isPullback`, which it imports with the
base-change clause itself.

## References

* [Stacks Project, Tag 036S](https://stacks.math.columbia.edu/tag/036S)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03Z9](https://stacks.math.columbia.edu/tag/03Z9)
* [Stacks Project, Tag 041B](https://stacks.math.columbia.edu/tag/041B)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 06ER](https://stacks.math.columbia.edu/tag/06ER)
* [Stacks Project, Tag 06F0](https://stacks.math.columbia.edu/tag/06F0)
* [Stacks Project, Tag 0DFB](https://stacks.math.columbia.edu/tag/0DFB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 041B**, the base-change clause in the orientation the source-locality transfer
consumes: the second projections of the fibre products of a syntomic covering `{Zᵢ ⟶ X}` with a
morphism `f : X' ⟶ X` form a syntomic covering of `X'`.

Each member is the base change of `gi i` along `f` in the cartesian square of Stacks 02X2, hence
syntomic by Stacks 03Z9, and joint surjectivity is Stacks 03H4: a point of `X'` and a point of
some `Zᵢ` over its image amalgamate to a point of the fibre product. -/
theorem isSyntomicCovering_pullback_snd {I : Type v} {X X' : AlgebraicSpaces B S hS}
    (Zi : I → AlgebraicSpaces B S hS) (gi : ∀ i, Zi i ⟶ X) (f : X' ⟶ X)
    (hcover : IsSyntomicCovering B S hS (fun i => (Zi i).1) (fun i => (gi i).hom)) :
    IsSyntomicCovering B S hS (fun i => pullback (gi i).hom f.hom)
      (fun i => pullback.snd (gi i).hom f.hom) := by
  have hsq (i : I) : IsPullback
      (ObjectProperty.homMk (pullback.fst (gi i).hom f.hom) :
        AlgebraicSpaces.fiberProduct B S hS (gi i) f ⟶ Zi i)
      (ObjectProperty.homMk (pullback.snd (gi i).hom f.hom)) (gi i) f :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS (gi i) f
  refine ⟨X'.property,
    fun i => isAlgebraicSpace_pullback B S hS (gi i).hom f.hom (Zi i).property X'.property
      X.property,
    fun i => isSyntomic_of_isPullback B S hS _ _ (gi i) f (hsq i) (hcover.syntomic i), ?_⟩
  refine Set.eq_univ_of_forall fun x' => ?_
  obtain ⟨i, z, hz⟩ := Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp hcover.jointly_surjective
    (pointsMap B S hS X'.1 f.hom x'))
  obtain ⟨wpt, -, hwq⟩ := exists_point_of_isPullback B S hS (hsq i) z x' hz
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_range.mpr ⟨wpt, hwq⟩⟩

/-- Base change of a syntomic covering of algebraic spaces over `S` along a chart of its target:
the fibre products form a syntomic covering of the chart, and each of them sits in a pullback
square over the chart and the corresponding member of the original family. -/
theorem isSyntomicCovering_baseChange_of_chart {I : Type v} {X : AlgebraicSpaces B S hS}
    (Zi : I → AlgebraicSpaces B S hS) (gi : ∀ i, Zi i ⟶ X)
    (hcover : Topology.IsCovering .syntomic B S hS (fun i => (Zi i).1) (fun i => (gi i).hom))
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X.1) :
    ∃ (Ai : I → AlgebraicSpaces B S hS)
      (qi : ∀ i, Ai i ⟶ representedAlgebraicSpace B S hS U)
      (projZ : ∀ i, Ai i ⟶ Zi i),
        Topology.IsCovering .syntomic B S hS (fun i => (Ai i).1) (fun i => (qi i).hom) ∧
        (∀ i, IsPullback (qi i) (projZ i)
          (ObjectProperty.homMk a : representedAlgebraicSpace B S hS U ⟶ X) (gi i)) := by
  let Uobj := representedAlgebraicSpace B S hS U
  let au : Uobj ⟶ X := ObjectProperty.homMk a
  let Ai : I → AlgebraicSpaces B S hS :=
    fun i => AlgebraicSpaces.fiberProduct B S hS (gi i) au
  refine ⟨Ai, fun i => ObjectProperty.homMk (pullback.snd (gi i).hom au.hom),
    fun i => ObjectProperty.homMk (pullback.fst (gi i).hom au.hom), ?_, ?_⟩
  · exact ⟨Uobj.property, fun i => (Ai i).property,
      isSyntomicCovering_pullback_snd B S hS Zi gi au hcover.2.2⟩
  · exact fun i => (AlgebraicSpaces.isPullback_fiberProduct B S hS (gi i) au).flip

/-- Composing a syntomic covering of algebraic spaces over `S` with a surjective étale scheme
atlas of each of its members gives a syntomic covering, indexed by the members paired with a
one-element type.

The atlases form étale coverings, which are syntomic coverings by Stacks 0DFB, so this is the
composition clause of Stacks 041B. -/
theorem etale_atlases_comp_isSyntomicCovering {I : Type v} (Z : I → AlgebraicSpaces B S hS)
    (V : AlgebraicSpaces B S hS) (g : ∀ i, Z i ⟶ V)
    (hbase : Topology.IsCovering .syntomic B S hS (fun i => (Z i).1) (fun i => (g i).hom))
    (U : I → BigFppfOver B S hS) (a : ∀ i, yoneda.obj (U i) ⟶ (Z i).1)
    (hsurj : ∀ i, (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (a i))
    (hetale : ∀ i, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (a i)) :
    Topology.IsCovering .syntomic B S hS
      (fun p : Σ _ : I, PUnit.{v + 1} => yoneda.obj (U p.1))
      (fun p => a p.1 ≫ (g p.1).hom) := by
  refine ⟨hbase.1, fun p => isAlgebraicSpace_yoneda B S hS (U p.1), ?_⟩
  exact isSyntomicCovering_comp B S hS (J := fun _ : I => PUnit.{v + 1})
    (X := V.1) (fun i => (Z i).1) (fun i => (g i).hom)
    (fun i _ => yoneda.obj (U i)) (fun i _ => a i) hbase.2.2
    (fun i => isSyntomicCovering_of_isEtaleCovering B S hS
      (isEtaleCovering_atlas B S hS (hbase.2.1 i) (hsurj i) (hetale i)))

/-! ### Stacks 06ER, the syntomic case -/

/-- Refining the base change of a syntomic covering `{Zᵢ ⟶ X}` along a chart `a : U ⟶ X` by a
surjective étale scheme atlas `Wᵢ` of each member gives a syntomic covering `{Wᵢ ⟶ U}` of
schemes, each member of which factors through the corresponding pullback square. -/
theorem exists_syntomic_scheme_refinement_of_chart {I : Type v} {X : AlgebraicSpaces B S hS}
    (Zi : I → AlgebraicSpaces B S hS) (gi : ∀ i, Zi i ⟶ X)
    (hcover : Topology.IsCovering .syntomic B S hS (fun i => (Zi i).1) (fun i => (gi i).hom))
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X.1) :
    ∃ (Ai : I → AlgebraicSpaces B S hS)
      (qi : ∀ i, Ai i ⟶ representedAlgebraicSpace B S hS U)
      (projZ : ∀ i, Ai i ⟶ Zi i) (Wi : I → BigFppfOver B S hS)
      (wi : ∀ i, yoneda.obj (Wi i) ⟶ (Ai i).1) (d : ∀ i, Wi i ⟶ U),
        (∀ i, IsPullback (qi i) (projZ i)
          (ObjectProperty.homMk a : representedAlgebraicSpace B S hS U ⟶ X) (gi i)) ∧
        (∀ i, (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf (wi i)) ∧
        (∀ i, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf (wi i)) ∧
        (∀ i, yoneda.map (d i) = wi i ≫ (qi i).hom) ∧
        Presieve.ofArrows
          (fun p : Σ _ : I, PUnit.{v + 1} => (BigFppfOver.toScheme B S hS).obj (Wi p.1))
          (fun p => (BigFppfOver.toScheme B S hS).map (d p.1)) ∈
            Scheme.precoverage (@Syntomic.{u}) ((BigFppfOver.toScheme B S hS).obj U) := by
  obtain ⟨Ai, qi, projZ, hAi, hpb⟩ :=
    isSyntomicCovering_baseChange_of_chart B S hS Zi gi hcover U a
  choose Wi wi hsurjWi hetaleWi using fun i => (Ai i).property.exists_atlas
  let d : ∀ i, Wi i ⟶ U := fun i => yoneda.preimage (wi i ≫ (qi i).hom)
  have hd (i : I) : yoneda.map (d i) = wi i ≫ (qi i).hom := by simp [d]
  have hspaceCover := etale_atlases_comp_isSyntomicCovering B S hS Ai
    (representedAlgebraicSpace B S hS U) qi hAi Wi wi hsurjWi hetaleWi
  have hspaceCoverD : Topology.IsCovering .syntomic B S hS
      (fun p : Σ _ : I, PUnit.{v + 1} => yoneda.obj (Wi p.1))
      (fun p => yoneda.map (d p.1)) := by
    simpa only [hd] using hspaceCover
  exact ⟨Ai, qi, projZ, Wi, wi, d, hpb, hsurjWi, hetaleWi, hd,
    Topology.isCovering_yoneda B S hS .syntomic (fun p : Σ _ : I, PUnit.{v + 1} => Wi p.1) U
      (fun p => d p.1) hspaceCoverD⟩

/-- If `Q` respects isomorphisms and two families of arrows into `X` generate the same presieve,
then `Q` holding after composing every member of one family with `f` implies the same for the
other family. -/
private lemma comp_of_ofArrows_eq {C : Type*} [Category C] (Q : MorphismProperty C)
    [Q.RespectsIso] {X Y : C} (f : X ⟶ Y) {ι κ : Type*} {A : ι → C} {A' : κ → C}
    (u : ∀ i, A i ⟶ X) (v : ∀ j, A' j ⟶ X)
    (h : Presieve.ofArrows A u = Presieve.ofArrows A' v) (hv : ∀ j, Q (v j ≫ f)) (i : ι) :
    Q (u i ≫ f) := by
  obtain ⟨j, hobj, hji⟩ := Presieve.ofArrows_surj v (u i) (by rw [← h]; exact ⟨i⟩)
  rw [hji, Category.assoc]
  exact MorphismProperty.RespectsIso.precomp Q (eqToHom hobj.symm) (v j ≫ f) (hv j)

/-- A member `W ⟶ A ⟶ Z` of the refinement of a base change along a chart `a` is étale, and the
chart square `W ⟶ V` over `Y` commutes, where `W ⟶ V` is `d` followed by a lift `k` of `f`. -/
private theorem etale_and_comm_of_refinement_chart {X Y Z A : AlgebraicSpaces B S hS}
    {U V W : BigFppfOver B S hS} (f : X ⟶ Y) (g : Z ⟶ X) (a : yoneda.obj U ⟶ X.1)
    (b : yoneda.obj V ⟶ Y.1) (k : U ⟶ V) (q : A ⟶ representedAlgebraicSpace B S hS U)
    (p : A ⟶ Z) (w : yoneda.obj W ⟶ A.1) (d : W ⟶ U)
    (hpb : IsPullback q p
      (ObjectProperty.homMk a : representedAlgebraicSpace B S hS U ⟶ X) g)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hw : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf w)
    (hd : yoneda.map d = w ≫ q.hom) (hcomm : yoneda.map k ≫ b = a ≫ f.hom) :
    IsEtale B S hS (w ≫ p.hom) ∧
      yoneda.map (d ≫ k) ≫ b = (w ≫ p.hom) ≫ g.hom ≫ f.hom := by
  refine ⟨isEtale_comp B S hS (chart_map_isEtale B S hS W w hw)
    (isEtale_of_isPullback B S hS q p _ g hpb (chart_map_isEtale B S hS U a ha)), ?_⟩
  have hpbw : q.hom ≫ a = p.hom ≫ g.hom := congrArg (fun k => k.hom) hpb.w
  rw [Functor.map_comp, hd]
  simp only [Category.assoc, hcomm, reassoc_of% hpbw]

/-- The forward implication of the syntomic case of Stacks 06ER: if `f` satisfies the property
of Stacks 03MJ, then so does its composite with every member of a syntomic covering. -/
theorem holdsOnEveryEtaleChart_comp_of_isSyntomicCovering (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P)
    [hlocal : P.IsLocalAtSource (Scheme.precoverage (@Syntomic.{u}))] {I : Type v}
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (Zi : I → AlgebraicSpaces B S hS)
    (gi : ∀ i, Zi i ⟶ X)
    (hcover : Topology.IsCovering .syntomic B S hS (fun i => (Zi i).1) (fun i => (gi i).hom))
    (hf : HoldsOnEveryEtaleChart B S hS P f.hom) (j : I) :
    HoldsOnEveryEtaleChart B S hS P (gi j ≫ f).hom := by
  let T := BigFppfOver.toScheme B S hS
  obtain ⟨V, b, hbSurj, hbEtale⟩ := Y.property.exists_atlas
  obtain ⟨T0, t, alpha, hα, htSurj, htEtale⟩ := exists_surjective_etale_presentation_lift B S hS
    X.property Y.property f.hom V b hbSurj hbEtale
  have hPalpha : P (T.map alpha) := hf T0 V t b alpha htEtale hbEtale hα.symm
  obtain ⟨Ai, qi, projZ, Wi, wi, d, hpb, hsurjWi, hetaleWi, hd, hcov⟩ :=
    exists_syntomic_scheme_refinement_of_chart B S hS Zi gi hcover T0 t
  obtain ⟨hcEtale, hcomm⟩ := etale_and_comm_of_refinement_chart B S hS f (gi j) t b alpha (qi j)
    (projZ j) (wi j) (d j) (hpb j) htEtale (hetaleWi j) (hd j) hα.symm
  have hcSurj := (surjective_iff_surjective_pointsMap B S hS
    (Zi j).1 (Zi j).property (Wi j) (wi j ≫ (projZ j).hom)).mpr <| isSurjective_comp B S hS
      ((surjective_iff_surjective_pointsMap B S hS (Ai j).1 (Ai j).property
        (Wi j) (wi j)).mp (hsurjWi j))
      (isSurjective_of_isPullback B S hS (hpb j)
        ((surjective_iff_surjective_pointsMap B S hS X.1 X.property T0 t).mp htSurj))
  have hPh : P (T.map (d j ≫ alpha)) := by
    have hp := hlocal.comp hcov (T.map (d j))
      (by exact ⟨(⟨j, PUnit.unit⟩ : Σ _ : I, PUnit.{v + 1})⟩) hPalpha
    simpa [Functor.map_comp] using hp
  exact (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP (Zi j).property
    Y.property ((gi j ≫ f).hom)).2 ⟨Wi j, V, wi j ≫ (projZ j).hom, b, d j ≫ alpha,
      (isEtale_iff_presheaf_of_yoneda B S hS _).1 hcEtale, hbEtale, hcSurj, hcomm, hPh⟩

/-- The backward implication of the syntomic case of Stacks 06ER: if the composite of `f` with
every member of a syntomic covering satisfies the property of Stacks 03MJ, then so does `f`. -/
theorem holdsOnEveryEtaleChart_of_comp_isSyntomicCovering (P : MorphismProperty Scheme.{u})
    [hlocal : P.IsLocalAtSource (Scheme.precoverage (@Syntomic.{u}))] {I : Type v}
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (Zi : I → AlgebraicSpaces B S hS)
    (gi : ∀ i, Zi i ⟶ X)
    (hcover : Topology.IsCovering .syntomic B S hS (fun i => (Zi i).1) (fun i => (gi i).hom))
    (hall : ∀ i, HoldsOnEveryEtaleChart B S hS P (gi i ≫ f).hom) :
    HoldsOnEveryEtaleChart B S hS P f.hom := by
  intro U V a b h ha hb hcomm
  obtain ⟨_, qi, projZ, Wi, wi, d, hpb, -, hetaleWi, hd, hcov⟩ :=
    exists_syntomic_scheme_refinement_of_chart B S hS Zi gi hcover U a
  apply hlocal.of_forall_comp hcov
  intro W' k hk
  cases hk with
  | mk p =>
    rcases p with ⟨i, ji⟩
    obtain ⟨hwzEtale, hchartComm⟩ := etale_and_comm_of_refinement_chart B S hS f (gi i) a b h
      (qi i) (projZ i) (wi i) (d i) (hpb i) ha (hetaleWi i) (hd i) hcomm
    exact hall i (Wi i) V _ b (d i ≫ h) ((isEtale_iff_presheaf_of_yoneda B S hS _).1 hwzEtale)
      hb hchartComm

/-- **Stacks 06ER**, the syntomic case. If a property `P` of morphisms of schemes is étale local
on the source and target and local on the source for the syntomic topology of schemes, then the
associated property of morphisms of algebraic spaces over `S` of Stacks 03MJ is local on the
source for the syntomic topology of algebraic spaces.

Deliberately untagged: Stacks 06ER asserts this for all five topologies of Stacks 03YH at once,
and only the syntomic case is proved here; the fpqc case is
`AlgebraicGeometry.Space.isLocalAtSource_fpqc_of_schemes` and the étale case is
`AlgebraicGeometry.Space.isLocalAtSource_etale_of_schemes`. -/
theorem isLocalAtSource_syntomic_of_schemes (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P)
    [P.IsLocalAtSource (Scheme.precoverage (@Syntomic.{u}))] :
    MorphismProperty.IsLocalAtSource
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
        HoldsOnEveryEtaleChart B S hS P f.hom)
      (Topology.precoverage.{u, v} .syntomic B S hS) := by
  let Q : MorphismProperty (AlgebraicSpaces B S hS) := fun {F G} f =>
    HoldsOnEveryEtaleChart B S hS P f.hom
  let _ : Q.RespectsIso := holdsOnEveryEtaleChart_respectsIso B S hS P
  refine MorphismProperty.IsLocalAtSource.mk_of_iff_of_zeroHypercover ?_
  intro X Y f E
  rcases E.mem₀ with ⟨I, Zi, gi, hpres, hcover⟩
  exact ⟨fun hf => comp_of_ofArrows_eq Q f E.f gi hpres
      (holdsOnEveryEtaleChart_comp_of_isSyntomicCovering B S hS P hP f Zi gi hcover hf),
    fun hall => holdsOnEveryEtaleChart_of_comp_isSyntomicCovering B S hS P f Zi gi hcover
      (comp_of_ofArrows_eq Q f gi E.f hpres.symm hall)⟩

/-! ### Stacks 06F0 -/

/-- **Stacks 06F0.** Syntomicity of a morphism of algebraic spaces over `S` is local on the
source for the syntomic topology of Stacks 03YH.

Syntomicity of morphisms of schemes is étale local on the source and target
([Stacks Project, Tag 04R3]) and local on the source for the syntomic topology of schemes
([Stacks Project, Tag 036S]), so this is the instance of
`AlgebraicGeometry.Space.isLocalAtSource_syntomic_of_schemes` at that property. -/
@[stacks 06F0]
instance syntomic_isLocalAtSource_syntomic :
    MorphismProperty.IsLocalAtSource
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsSyntomic B S hS f.hom)
      (Topology.precoverage.{u, v} .syntomic B S hS) :=
  isLocalAtSource_syntomic_of_schemes B S hS
    (@_root_.AlgebraicGeometry.Syntomic.{u} : MorphismProperty Scheme.{u})
    _root_.AlgebraicGeometry.syntomic_isEtaleLocalOnSourceAndTarget

end AlgebraicGeometry.Space

end
