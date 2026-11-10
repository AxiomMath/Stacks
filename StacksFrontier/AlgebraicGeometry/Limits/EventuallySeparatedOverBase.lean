module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.Separated
public import StacksCore.Tactic.StacksAttribute

/-!
# Separatedness over a fixed base at a finite stage of a limit

Let `S` be a quasi-separated scheme and let `X = lim X_i` be a directed inverse limit of
quasi-compact and quasi-separated schemes over `S` with affine transition morphisms. If the
structure morphism `X ⟶ S` is separated, then `X_i ⟶ S` is separated for every sufficiently
large `i`.

This is the relative form, over a fixed base, of the absolute statement
`AlgebraicGeometry.eventually_isSeparated` (Tag 086Q), which is the case `S = ⊤_ Scheme`.

## Main results

* `AlgebraicGeometry.isSeparated_of_isSeparated_source`: a morphism out of a separated scheme is
  separated, whatever its target.
* `AlgebraicGeometry.Scheme.IsSeparated.of_isSeparated`: a scheme separated over a separated
  scheme is separated.
* `AlgebraicGeometry.exists_isSeparated_app_stage`: the relative statement for a cofiltered thin
  index category in the universe of the schemes.
* `AlgebraicGeometry.eventually_isSeparated_app`: Tag 01ZH, for a directed preorder whose index
  universe is independent of the scheme universe.

## Implementation notes

The proof is the Stacks proof: cover the image of one stage by finitely many affine opens of `S`
and reduce to the absolute statement over each of them.

Concretely, for a point `x` of the stage `X_i` choose an affine open `U` of `S` around its image
and let `T = (X_i ⟶ S)⁻¹ U`. The inverse images of `T` along the transition morphisms form the
diagram `AlgebraicGeometry.opensDiagram`, indexed by `CategoryTheory.Over i`, whose limit is the
inverse image of `T` in `X` (`AlgebraicGeometry.isLimitOpensCone`). That inverse image is the
inverse image of `U` under `X ⟶ S`, hence is separated over the affine `U` and therefore is a
separated scheme; so the absolute statement applies and gives a stage at which the inverse image
of `U` is a separated scheme. Finitely many such opens suffice because `X_i` is quasi-compact,
and cofilteredness merges the finitely many stages into one.

Two general facts carry the argument across the absolute/relative divide and are recorded
separately: a morphism whose source is a separated scheme is separated, and a scheme separated
over a separated scheme is separated. The first is what turns the stagewise absolute conclusion
back into a statement about the structure morphism; the second is what produces the absolute
hypothesis of Tag 086Q from the relative one.

The opens of `S` chosen above cover only the image of the stage, not `S` itself, and `S` need not
be quasi-compact, so separatedness of the structure morphism cannot be read off from
`IsZariskiLocalAtTarget` on `S` directly. The structure morphism is therefore factored through
the quasi-compact open `V` that those finitely many opens do cover, using
`AlgebraicGeometry.IsOpenImmersion.lift`; locality at the target applies over `V`, and the open
immersion `V ⟶ S` is a monomorphism and hence separated.

## The smallness hypothesis

This is an eventual statement — it asserts that a property holds at some finite stage — so a
smallness condition on the index relative to the scheme universe is expected to be necessary, and
`AlgebraicGeometry.eventually_isSeparated_app` carries `CategoryTheory.EssentiallySmall`. That is
not a hypothesis added to the source: the source's index is a directed *set*, which has this
condition, and the absolute Tag 086Q it is proved from carries the same one.

The mechanism by which smallness can fail to be dispensable is the one in the module
documentation of `StacksDraft.AlgebraicGeometry.F3b.Limits.EventuallyAffine`: for a field `F`
that is not `u`-small, a system indexed by `(Finset F)ᵒᵖ` whose stages live over models of the
finitely generated subrings of `F` has the *empty* scheme as its limit, because global sections
assemble into a ring map out of `F`. Every morphism out of the empty scheme has every property,
while no stage need have it.

What is *not* claimed here is that that particular diagram refutes a smallness-free Tag 01ZH.
It does not: its stages are quasi-compact opens of affine schemes, hence separated, so
separatedness does hold at every stage of it. The refutation would need a diagram with the same
limit and non-separated stages — replacing the stage over each model by, say, the line with
doubled origin over it leaves the global-sections argument intact — and no such diagram has been
formalised. The smallness here is therefore carried because the source has it and because 086Q
needs it, not on the strength of a verified counterexample for this tag.

## References

* [Stacks Project, Tag 01ZH](https://stacks.math.columbia.edu/tag/01ZH)
* [Stacks Project, Tag 086Q](https://stacks.math.columbia.edu/tag/086Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

section Bridge

variable {X Y : Scheme.{u}}

/-- A morphism out of a separated scheme is separated, whatever its target. -/
lemma isSeparated_of_isSeparated_source (f : X ⟶ Y) [X.IsSeparated] : IsSeparated f :=
  inferInstance

/-- A scheme separated over a separated scheme is separated. -/
lemma Scheme.IsSeparated.of_isSeparated (f : X ⟶ Y) [IsSeparated f] [Y.IsSeparated] :
    X.IsSeparated := by
  refine ⟨?_⟩
  rw [← terminal.comp_from f]
  infer_instance

/-- The inverse image of a separated open under a separated morphism is a separated scheme. -/
private lemma isSeparated_preimage_of_isSeparated (f : X ⟶ Y) [IsSeparated f] (V : Y.Opens)
    [V.toScheme.IsSeparated] : Scheme.IsSeparated (f ⁻¹ᵁ V).toScheme :=
  Scheme.IsSeparated.of_isSeparated (f.resLE V _ le_rfl)

/-- A morphism is separated if its source is covered by the inverse images of opens of the
target that are separated schemes. -/
private lemma isSeparated_of_iSup_preimage_eq_top (f : X ⟶ Y) {ι : Type*} (U : ι → Y.Opens)
    (hU : ⨆ i, f ⁻¹ᵁ U i = ⊤) (h : ∀ i, Scheme.IsSeparated (f ⁻¹ᵁ U i).toScheme) :
    IsSeparated f := by
  set V : Y.Opens := ⨆ i, U i with hV
  have hrange : Set.range f.base ⊆ Set.range V.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro y ⟨z, rfl⟩
    have hz : z ∈ ⨆ i, f ⁻¹ᵁ U i := by
      rw [hU]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
    rw [hV]
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  have hgfac : IsOpenImmersion.lift V.ι f hrange ≫ V.ι = f := IsOpenImmersion.lift_fac _ _ _
  have : IsSeparated (IsOpenImmersion.lift V.ι f hrange) := by
    refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun i => V.ι ⁻¹ᵁ U i) ?_ fun i => ?_
    · rw [← Scheme.Hom.preimage_iSup, ← hV, Scheme.Opens.ι_preimage_self]
    · have : Scheme.IsSeparated
          (IsOpenImmersion.lift V.ι f hrange ⁻¹ᵁ V.ι ⁻¹ᵁ U i).toScheme := by
        rw [← Scheme.Hom.comp_preimage, hgfac]
        exact h i
      exact isSeparated_of_isSeparated_source _
  rw [← hgfac]
  infer_instance

end Bridge

/-- The morphism from the limit to the base does not depend on the stage at which it is
computed. -/
lemma limitHom_app_eq {K : Type*} [Category K] [IsCofilteredOrEmpty K] {S : Scheme.{u}}
    {D : K ⥤ Scheme.{u}} (c : Cone D)
    (t : D ⟶ (Functor.const K).obj S) (a b : K) :
    c.π.app a ≫ t.app a = c.π.app b ≫ t.app b := by
  have step : ∀ {p q : K} (f : p ⟶ q), c.π.app p ≫ t.app p = c.π.app q ≫ t.app q := by
    intro p q f
    rw [← c.w f, Category.assoc]
    simp
  obtain ⟨l, g, h, -⟩ := IsCofilteredOrEmpty.cone_objs a b
  exact (step g).symm.trans (step h)

section Core

variable {J : Type u} [Category.{u} J] {S : Scheme.{u}} {D : J ⥤ Scheme.{u}}

/-- If the inverse image in the limit of a quasi-compact open of a stage is a separated scheme,
then so is its inverse image at some earlier stage. -/
private lemma exists_isSeparated_preimage_stage [IsCofiltered J] [Quiver.IsThin J] (c : Cone D)
    (hc : IsLimit c) [∀ {a b : J} (f : a ⟶ b), IsAffineHom (D.map f)]
    [∀ a, QuasiSeparatedSpace (D.obj a)] {i : J} (T : (D.obj i).Opens)
    (hT : IsCompact (T : Set (D.obj i))) (hsep : Scheme.IsSeparated (c.π.app i ⁻¹ᵁ T).toScheme) :
    ∃ (a : J) (g : a ⟶ i), Scheme.IsSeparated (D.map g ⁻¹ᵁ T).toScheme := by
  have : ∀ a : Over i, CompactSpace ((opensDiagram D i T).obj a) := fun a =>
    isCompact_iff_compactSpace.mp ((D.map a.hom).isCompact_preimage hT)
  have : ∀ a : Over i, QuasiSeparatedSpace ((opensDiagram D i T).obj a) := fun a =>
    (quasiSeparatedSpace_of_quasiSeparated (D.map a.hom ⁻¹ᵁ T).ι :)
  have : Quiver.IsThin (Over i) := fun _ _ =>
    ⟨fun _ _ => Over.OverMorphism.ext (Subsingleton.elim _ _)⟩
  have : Scheme.IsSeparated (opensCone D c i T).pt := hsep
  obtain ⟨a, ha⟩ := exists_isSeparated_stage (opensDiagram D i T) (opensCone D c i T)
    (isLimitOpensCone D c hc i T)
  exact ⟨a.left, a.hom, ha⟩

/-- The relative form of Tag 086Q for a cofiltered thin index category in the universe of the
schemes: if the morphism from the limit to the base is separated, then so is the structure
morphism of some stage. -/
lemma exists_isSeparated_app_stage [IsCofiltered J] [Quiver.IsThin J] [QuasiSeparatedSpace S]
    (c : Cone D) (hc : IsLimit c)
    [∀ {a b : J} (f : a ⟶ b), IsAffineHom (D.map f)]
    [∀ a, CompactSpace (D.obj a)] [∀ a, QuasiSeparatedSpace (D.obj a)]
    (t : D ⟶ (Functor.const J).obj S) (i : J)
    (hsep : IsSeparated (c.π.app i ≫ t.app i)) :
    ∃ a : J, IsSeparated (t.app a) := by
  classical
  have hqc : QuasiCompact (t.app i) := quasiCompact_of_compactSpace (Y := S) (t.app i)
  have hpt : ∀ x : D.obj i, ∃ U : S.affineOpens, (t.app i).base x ∈ (U : S.Opens) := by
    intro x
    have hx : (t.app i).base x ∈ (⨆ V : S.affineOpens, (V : S.Opens)) := by
      rw [iSup_affineOpens_eq_top S]
      trivial
    simpa using hx
  choose U hU using hpt
  let T : D.obj i → (D.obj i).Opens := fun x => t.app i ⁻¹ᵁ (U x : S.Opens)
  have hT : ∀ x, T x = t.app i ⁻¹ᵁ (U x : S.Opens) := fun _ => rfl
  obtain ⟨s, hs⟩ := (CompactSpace.isCompact_univ (X := D.obj i)).elim_finite_subcover
    (fun x : D.obj i => (T x : Set (D.obj i))) (fun x => (T x).2)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hU x⟩)
  have key : ∀ x : D.obj i, ∃ (a : J) (g : a ⟶ i),
      Scheme.IsSeparated (D.map g ⁻¹ᵁ T x).toScheme := by
    intro x
    refine exists_isSeparated_preimage_stage c hc (T x)
      ((t.app i).isCompact_preimage (U x).2.isCompact) ?_
    have : IsAffine (U x : S.Opens).toScheme := (U x).2
    have := isSeparated_preimage_of_isSeparated (c.π.app i ≫ t.app i) (U x : S.Opens)
    rwa [Scheme.Hom.comp_preimage] at this
  choose a ga hga using key
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (insert i (s.image a))
  let q : k ⟶ i := (hk (Finset.mem_insert_self _ _)).some
  have hnat : D.map q ≫ t.app i = t.app k := by simp
  have hstage : ∀ x ∈ s, Scheme.IsSeparated (t.app k ⁻¹ᵁ (U x : S.Opens)).toScheme := by
    intro x hx
    obtain ⟨r⟩ := hk (Finset.mem_insert_of_mem (Finset.mem_image_of_mem a hx))
    have := hga x
    have hopen : t.app k ⁻¹ᵁ (U x : S.Opens) = D.map r ⁻¹ᵁ (D.map (ga x) ⁻¹ᵁ T x) := by
      have e₁ : D.map r ⁻¹ᵁ (D.map (ga x) ⁻¹ᵁ T x) = D.map q ⁻¹ᵁ T x := by
        rw [← Scheme.Hom.comp_preimage, ← D.map_comp, Subsingleton.elim (r ≫ ga x) q]
      rw [e₁, hT, ← Scheme.Hom.comp_preimage, hnat]
    rw [hopen]
    exact isSeparated_preimage_of_isSeparated (D.map r) _
  refine ⟨k, isSeparated_of_iSup_preimage_eq_top (t.app k) (fun x : s => (U x.1 : S.Opens)) ?_
    fun x => hstage x.1 x.2⟩
  refine top_unique fun z _ => ?_
  obtain ⟨x, hx, hmem⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ ((D.map q).base z)))
  have hz : z ∈ t.app k ⁻¹ᵁ (U x : S.Opens) := by
    rw [← hnat]
    exact hmem
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hz⟩

end Core

/-- **Stacks Project, Tag 01ZH.** Let `S` be a quasi-separated scheme and let `X = lim X_i` be a
directed inverse limit of quasi-compact and quasi-separated schemes over `S` with affine
transition morphisms. If `X ⟶ S` is separated, then `X_i ⟶ S` is separated for all sufficiently
large `i`. -/
@[stacks 01ZH]
theorem eventually_isSeparated_app {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    [EssentiallySmall.{u} I] (d : DescentSituation.{v, u} I) {S : Scheme.{u}}
    [QuasiSeparatedSpace S] (t : d.system ⟶ (Functor.const Iᵒᵖ).obj S)
    (hsep : IsSeparated (d.limitCone.π.app (op d.base) ≫ t.app (op d.base))) :
    ∃ i₀ : I, ∀ i : I, i₀ ≤ i → IsSeparated (t.app (op i)) := by
  classical
  have : Nonempty I := ⟨d.base⟩
  let e := equivSmallModel.{u} Iᵒᵖ
  have : IsCofiltered (SmallModel.{u} Iᵒᵖ) := IsCofiltered.of_equivalence e
  have : Quiver.IsThin (SmallModel.{u} Iᵒᵖ) := fun _ _ =>
    ⟨fun _ _ => e.inverse.map_injective (Subsingleton.elim _ _)⟩
  let D := e.inverse ⋙ d.system
  let c := d.limitCone.whisker e.inverse
  have hc : IsLimit c :=
    (Functor.Initial.isLimitWhiskerEquiv e.inverse d.limitCone).symm d.isLimit
  have : ∀ j, CompactSpace (D.obj j) := fun j => d.quasiCompact (e.inverse.obj j).unop
  have : ∀ j, QuasiSeparatedSpace (D.obj j) := fun j => d.quasiSeparated (e.inverse.obj j).unop
  have : ∀ {j k : SmallModel.{u} Iᵒᵖ} (f : j ⟶ k), IsAffineHom (D.map f) := fun f =>
    d.transition_affine (e.inverse.map f)
  let t' : D ⟶ (Functor.const (SmallModel.{u} Iᵒᵖ)).obj S :=
    { app := fun j => t.app (e.inverse.obj j)
      naturality := fun _ _ f => t.naturality (e.inverse.map f) }
  obtain ⟨j⟩ := IsCofiltered.nonempty (C := SmallModel.{u} Iᵒᵖ)
  have hsep' : IsSeparated (c.π.app j ≫ t'.app j) := by
    change IsSeparated (d.limitCone.π.app (e.inverse.obj j) ≫ t.app (e.inverse.obj j))
    rw [limitHom_app_eq d.limitCone t (e.inverse.obj j) (op d.base)]
    exact hsep
  obtain ⟨b, hb⟩ := exists_isSeparated_app_stage c hc t' j hsep'
  refine ⟨(e.inverse.obj b).unop, fun i hi => ?_⟩
  have : IsSeparated (t.app (op (e.inverse.obj b).unop)) := hb
  have : IsAffineHom (d.system.map (homOfLE hi).op) := d.transition_affine _
  have hnat :
      d.system.map (homOfLE hi).op ≫ t.app (op (e.inverse.obj b).unop) = t.app (op i) := by
    simp
  rw [← hnat]
  infer_instance

end AlgebraicGeometry

end
