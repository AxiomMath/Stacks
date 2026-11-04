module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Characterization
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms

/-!
# Testing an étale-local property on the charts of a morphism of algebraic spaces (Stacks 03MJ)

Let `S` be a scheme contained in a big fppf site `B`, and let `P` be a property of morphisms of
schemes which is étale local on the source and target in the sense of Stacks 04QZ. For a
morphism `f : F ⟶ G` of algebraic spaces over `S`, Stacks 03MJ compares the ways of asserting
`P` of `f` through charts:

* condition (1), `AlgebraicGeometry.Space.HoldsOnEveryEtaleChart`: the morphism of schemes
  underlying *every* commuting square of étale charts of `f` has `P`;
* condition (2), `AlgebraicGeometry.Space.HoldsOnSurjectiveEtaleChart`: *one* such square has
  it, with the chart of the source in addition surjective.

The two are equivalent. The implication (1) ⇒ (2) is Stacks 025Y and 02X1: the target has a
surjective étale chart, and that chart lifts through `f` to a surjective étale chart of the
source. For (2) ⇒ (1), given a second square over `h' : U' ⟶ V'`, pull the given source chart
back along the new one and the new target chart back along the given one; the resulting
`W ⟶ Z` is an étale-chart refinement of `h` on one side and a surjective étale chart of `h'`
on the other, so Stacks 04R1 carries `P` across.

Two specialisations follow, both as stated by Stacks 03MJ: when source and target are
*representable*, condition (1) says exactly that the corresponding morphism of schemes has
`P`; and when `f` is merely *representable*, condition (1) says exactly that `P` holds of
every represented base change of `f`, i.e. that the relative morphism property of the inverse
image of `P` holds.

## Main results

* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_surjectiveChart`: **Stacks 03MJ**, the
  equivalence of conditions (1) and (2).
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_representable`: **Stacks 03MJ** for a
  morphism of representable presheaves.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_relative`: **Stacks 03MJ** for a
  representable morphism.

## Implementation notes

Every use of étale locality of `P` goes through the Stacks 04R1 interface
`AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget.iff_forall_etale_diagrams` and
`...iff_exists_surjective_etale_diagram`, which are the scheme-level counterparts of the two
conditions being compared here; the proofs below are therefore purely the transfer between
charts of algebraic spaces and the squares of schemes those interfaces speak about.

`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_representable` reads the morphism of
schemes off the canonical Yoneda representations of source and target; the two representing
isomorphisms are étale charts because an isomorphism of presheaves is relatively representable
with isomorphisms as its base changes.

`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_relative` keeps the base-change stability
and fppf locality of `P` as instance hypotheses, as Stacks 03MJ states them.

## References

* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 04QZ](https://stacks.math.columbia.edu/tag/04QZ)
* [Stacks Project, Tag 04R1](https://stacks.math.columbia.edu/tag/04R1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

/-- A functor sends a commuting square to a commuting square. -/
private theorem map_comp_eq_map_comp {C D : Type*} [Category C] [Category D] (T : C ⥤ D)
    {W X Y Z : C} {f : W ⟶ X} {g : X ⟶ Z} {h : W ⟶ Y} {i : Y ⟶ Z} (e : f ≫ g = h ≫ i) :
    T.map f ≫ T.map g = T.map h ≫ T.map i := by
  simpa only [Functor.map_comp] using congrArg T.map e

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u})
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 03MJ**, the equivalence of conditions (1) and (2). A property of morphisms of
schemes which is étale local on the source and target holds on every commuting square of étale
charts of a morphism of algebraic spaces exactly when it holds on one such square whose chart
of the source is surjective. -/
@[stacks 03MJ "equivalence of conditions (1) and (2)"]
theorem holdsOnEveryEtaleChart_iff_surjectiveChart
    (hP : IsEtaleLocalOnSourceAndTarget P)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) :
    HoldsOnEveryEtaleChart B S hS P f ↔ HoldsOnSurjectiveEtaleChart B S hS P f := by
  let T := BigFppfOver.toScheme B S hS
  constructor
  · intro hall
    obtain ⟨V, b, hbSurj, hbEtale⟩ := hG.exists_atlas
    obtain ⟨U, a, α, hα, haSurj, haEtale⟩ :=
      exists_surjective_etale_presentation_lift B S hS hF hG f V b hbSurj hbEtale
    exact ⟨U, V, a, b, α, haEtale, hbEtale, haSurj, hα.symm,
      hall U V a b α haEtale hbEtale hα.symm⟩
  · rintro ⟨U, V, a, b, h, ha, hb, haSurj, hab, hPab⟩
    intro U' V' a' b' h' ha' hb' hab'
    let W := ha'.rep.pullback a
    let u : W ⟶ U' := ha'.rep.fst' a
    let u₀ : W ⟶ U := ha'.rep.snd a
    let Z := hb.rep.pullback b'
    let v : Z ⟶ V := hb.rep.fst' b'
    let v₀ : Z ⟶ V' := hb.rep.snd b'
    have hw : yoneda.map u ≫ a' = yoneda.map u₀ ≫ a := by
      simpa [u, u₀] using (ha'.rep.isPullback' a).w
    have hu₀ : AlgebraicGeometry.Etale (T.map u₀) :=
      ha'.property a (yoneda.map (ha'.rep.fst' a)) (ha'.rep.snd a) (ha'.rep.isPullback' a)
    have hu : AlgebraicGeometry.Etale (T.map u) :=
      ha.property a' (yoneda.map (ha'.rep.snd a)) (ha'.rep.fst' a) (ha'.rep.isPullback' a).flip
    have huSurj : AlgebraicGeometry.Surjective (T.map u) :=
      haSurj.property a' (yoneda.map (ha'.rep.snd a)) (ha'.rep.fst' a)
        (ha'.rep.isPullback' a).flip
    have hv₀ : AlgebraicGeometry.Etale (T.map v₀) :=
      hb.property b' (yoneda.map (hb.rep.fst' b')) (hb.rep.snd b') (hb.rep.isPullback' b')
    have hv : AlgebraicGeometry.Etale (T.map v) :=
      hb'.property b (yoneda.map (hb.rep.snd b')) (hb.rep.fst' b') (hb.rep.isPullback' b').flip
    have hcompat : yoneda.map (u₀ ≫ h) ≫ b = yoneda.map (u ≫ h') ≫ b' := by
      simp only [Functor.map_comp, Category.assoc]
      rw [hab, hab', reassoc_of% hw]
    let k : W ⟶ Z := hb.rep.lift' (u₀ ≫ h) (u ≫ h') hcompat
    have hk : k ≫ v = u₀ ≫ h := hb.rep.lift'_fst _ _ _
    have hk₀ : k ≫ v₀ = u ≫ h' := hb.rep.lift'_snd _ _ _
    have hPk : P (T.map k) :=
      (IsEtaleLocalOnSourceAndTarget.iff_forall_etale_diagrams (P := P) (T.map h) hP).mp hPab
        (T.map u₀) (T.map v) (T.map k) hu₀ hv
        (map_comp_eq_map_comp T hk)
    exact (IsEtaleLocalOnSourceAndTarget.iff_exists_surjective_etale_diagram
      (P := P) (T.map h') hP).mpr
        ⟨T.obj W, T.obj Z, T.map u, T.map v₀, T.map k, hu, hv₀, huSurj.surj,
          map_comp_eq_map_comp T hk₀, hPk⟩

/-- **Stacks 03MJ** for a morphism of representable presheaves: a property of morphisms of
schemes which is étale local on the source and target holds on every commuting square of étale
charts of the morphism exactly when it holds of the morphism of schemes read off the canonical
representations of source and target. -/
@[stacks 03MJ "representable source and target"]
theorem holdsOnEveryEtaleChart_iff_representable
    (hP : IsEtaleLocalOnSourceAndTarget P)
    [F.IsRepresentable] [G.IsRepresentable] (f : F ⟶ G) :
    HoldsOnEveryEtaleChart B S hS P f ↔
      P ((BigFppfOver.toScheme B S hS).map
        (yoneda.preimage (F.reprW.hom ≫ f ≫ G.reprW.inv))) := by
  let T := BigFppfOver.toScheme B S hS
  let Q : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T
  let f₀ := yoneda.preimage (F.reprW.hom ≫ f ≫ G.reprW.inv)
  have isoEtaleChart {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (e : X ≅ Y) : Q.presheaf e.hom := by
    refine ⟨Functor.relativelyRepresentable.of_isIso yoneda e.hom, ?_⟩
    intro A C g fst snd sq
    have : IsIso (yoneda.map snd) := sq.isIso_snd_of_isIso
    have : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map _
    exact (inferInstance : AlgebraicGeometry.Etale (T.map snd))
  have hA : Q.presheaf F.reprW.hom := isoEtaleChart F.reprW
  have hB : Q.presheaf G.reprW.hom := isoEtaleChart G.reprW
  have : Q.presheaf.RespectsIso := MorphismProperty.relative_respectsIso Q
  constructor
  · intro hall
    have hcomm : yoneda.map f₀ ≫ G.reprW.hom = F.reprW.hom ≫ f := by
      simp [f₀]
    exact hall F.reprX G.reprX F.reprW.hom G.reprW.hom f₀ hA hB hcomm
  · intro hf U V a b h ha hb hab
    let a₀ : U ⟶ F.reprX := yoneda.preimage (a ≫ F.reprW.inv)
    let b₀ : V ⟶ G.reprX := yoneda.preimage (b ≫ G.reprW.inv)
    have etale₀ {X Y A} (e : yoneda.obj Y ≅ A) (c : yoneda.obj X ⟶ A) (hc : Q.presheaf c) :
        AlgebraicGeometry.Etale (T.map (yoneda.preimage (c ≫ e.inv))) := by
      have := (Q.presheaf.cancel_right_of_respectsIso c e.inv).2 hc
      rw [← yoneda.map_preimage (c ≫ e.inv)] at this
      exact this.2 (𝟙 _) (𝟙 _) _ (IsPullback.id_horiz _)
    have hcomm₀ : a₀ ≫ f₀ = h ≫ b₀ := by
      apply yoneda.map_injective
      simp [a₀, b₀, f₀, ← hab, Category.assoc]
    exact (IsEtaleLocalOnSourceAndTarget.iff_forall_etale_diagrams (P := P)
        (T.map f₀) hP).mp hf
      (T.map a₀) (T.map b₀) (T.map h) (etale₀ F.reprW a ha) (etale₀ G.reprW b hb)
      (map_comp_eq_map_comp T hcomm₀.symm)

/-- **Stacks 03MJ** for a representable morphism of algebraic spaces: when `P` is in addition
stable under base change and local on the base for the fppf topology, the every-chart condition
is exactly the relative morphism property of the inverse image of `P`, that is, `P` holds of
every represented base change of the morphism. -/
@[stacks 03MJ "representable morphism"]
theorem holdsOnEveryEtaleChart_iff_relative
    (hP : IsEtaleLocalOnSourceAndTarget P)
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (f : F ⟶ G) (hf : yoneda.relativelyRepresentable f) :
    HoldsOnEveryEtaleChart B S hS P f ↔
      (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f := by
  let T := BigFppfOver.toScheme B S hS
  let Q := P.inverseImage T
  let E : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T
  constructor
  · intro hall
    obtain ⟨U, V, a, b, h, ha, hb, haSurj, hab, hPab⟩ :=
      (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP hF hG f).mp hall
    apply MorphismProperty.relative.of_exists (F := yoneda) (P := Q)
    intro Z g
    let X := hf.pullback g
    let x := hf.fst g
    let t := hf.snd g
    let R := hb.rep.pullback g
    let r : R ⟶ V := hb.rep.fst' g
    let z : R ⟶ Z := hb.rep.snd g
    let W := Limits.pullback h r
    let u : W ⟶ U := Limits.pullback.fst h r
    let q : W ⟶ R := Limits.pullback.snd h r
    have hzEtale : AlgebraicGeometry.Etale (T.map z) :=
      hb.property g (yoneda.map r) z (hb.rep.isPullback' g)
    have hcomp : IsPullback (yoneda.map u) (yoneda.map (q ≫ z)) (a ≫ f) g := by
      simpa only [Functor.map_comp, hab] using
        ((IsPullback.of_hasPullback h r).map yoneda).paste_vert (hb.rep.isPullback' g)
    let m : W ⟶ X := yoneda.preimage
      ((hf.isPullback g).lift (yoneda.map u ≫ a) (yoneda.map (q ≫ z)) hcomp.w)
    have hmt : m ≫ t = q ≫ z := by
      apply yoneda.map_injective
      simp [m, t, X, Functor.map_comp]
    have hpm : IsPullback (yoneda.map u) (yoneda.map m) a x := by
      simpa [m] using hcomp.of_bot' (hf.isPullback g)
    have hmEtale : AlgebraicGeometry.Etale (T.map m) := ha.property x (yoneda.map u) m hpm
    have hmSurj : AlgebraicGeometry.Surjective (T.map m) := haSurj.property x (yoneda.map u) m hpm
    have hqP : P (T.map q) := MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback h r |>.map T : IsPullback (T.map u) (T.map q) (T.map h) (T.map r))
      hPab
    exact ⟨X, x, t, hf.isPullback g,
      (IsEtaleLocalOnSourceAndTarget.iff_exists_surjective_etale_diagram (P := P) (T.map t) hP).mpr
        ⟨T.obj W, T.obj R, T.map m, T.map z, T.map q, hmEtale, hzEtale, hmSurj.surj,
          map_comp_eq_map_comp T hmt.symm, hqP⟩⟩
  · intro hrel U V a b h ha hb hab
    let R := hrel.1.pullback b
    let x := hrel.1.fst b
    let t := hrel.1.snd b
    have hx : E.presheaf x := by
      have : MorphismProperty.IsStableUnderBaseChange E.presheaf :=
        MorphismProperty.relative_isStableUnderBaseChange E
      exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (hrel.1.isPullback b).flip hb
    let s : U ⟶ R := hrel.1.lift a h hab.symm
    have hsx : yoneda.map s ≫ x = a := hrel.1.lift_fst _ _ _
    have hst : s ≫ t = h := hrel.1.lift_snd _ _ _
    have hsEtale : AlgebraicGeometry.Etale (T.map s) :=
      etale_of_etale_charts B S hS a x ha hx s hsx
    have ht : P (T.map t) := hrel.2 b x t (hrel.1.isPullback b)
    exact (IsEtaleLocalOnSourceAndTarget.iff_forall_etale_diagrams (P := P) (T.map t) hP).mp ht
      (T.map s) (𝟙 (T.obj V)) (T.map h) hsEtale (by infer_instance)
      (by simp [← T.map_comp, hst])

end AlgebraicGeometry.Space

end
