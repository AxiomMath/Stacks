module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Groupoids.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.CohenMacaulayRestriction
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.GroupoidRestriction
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.QuasiFiniteSlice
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionGroupoid
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.JacobsonPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.EquivalenceRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Slicing a flat equivalence relation to a locally quasi-finite one

Let `j : R ⟶ U ×_S U` be an equivalence relation on objects of a big fppf site over `S` whose
source and target maps are flat and locally of finite presentation.  Then `j` can be *sliced*:
there is a second equivalence relation `j' : R' ⟶ U' ×_S U'` on objects of the site whose source
and target maps are in addition locally quasi-finite, together with a morphism `g : U' ⟶ U` of
object schemes and a morphism `r : R' ⟶ R` of arrow schemes over it, such that the induced map
of fppf quotient sheaves `U'/R' ⟶ U/R` is an isomorphism.

This is Stacks 0489, Lemma 80.8.1 of the source's Bootstrap chapter, and it is the first
reduction step of the final bootstrap theorem Stacks 04S6: it replaces a flat, locally finitely
presented equivalence relation by one which is moreover locally quasi-finite, without changing
the quotient sheaf.

## Main results

* `AlgebraicGeometry.exists_slice_locallyQuasiFinite`: **Stacks 0489.**

## Implementation notes

The proof follows the source's three steps.

Step 1 shrinks `U` to the open `W ⊆ U` whose target inverse image is the maximal open on which
the source map is Cohen–Macaulay, which is Stacks 0460 and is available as
`AlgebraicGeometry.exists_open_source_cohenMacaulay_locus` and its companions; the reach map
`h : W ×_{W, U, t} R ⟶ U` of that restriction is flat and locally of finite presentation
because it is a base change of the source map along an open immersion, and surjective by
Stacks 0460 part (3).  Hence `{h}` is an fppf covering and Stacks 02VH, in the form
`AlgebraicGeometry.GroupoidScheme.isIso_restrictionQuotientMap_of_reach_cover`, makes
`W/R|_W ⟶ U/R` an isomorphism.

Step 2 is Stacks 04N0,
`AlgebraicGeometry.exists_affine_slice_locallyQuasiFinite_of_isFiniteTypePoint`, applied at
each finite type point of `W`.  Its Cohen–Macaulay hypotheses are Stacks 0460 part (5) and its
hypothesis that the stabilizer group scheme is locally quasi-finite holds because the stabilizer
of an equivalence-relation groupoid is trivial: that is `groupoid_stabilizer_isIso_of_mono`
below, which is where the relation being a *monomorphism* is used.

Step 3 takes the coproduct `U' = ∐_u U'_u` over the finite type points.  Its reach map is the
coproduct of the individual reach maps, so it keeps the three properties by Zariski locality on
the source, and it is surjective because its image is open and contains every finite type point,
hence meets every nonempty closed set.  That the coproduct is again an object of the site is the
source's set-theoretic footnote; here it is `coproduct_small_of_bounded_by_base`, which bounds
the index set by the points of `W` and each piece by the size of `W`, so the coproduct has size
below the site's cutoff because the cutoff is a strong limit.

The conclusion's isomorphism of quotient sheaves is the canonical map
`Stacks.Groupoids.quotientSheafMap` induced by the pair `(r, g)`, not merely some isomorphism.
Both `R` and `U` are objects of the site, as in the source, and so are the produced `R'` and
`U'`.  The source's displayed conclusion `s', t' : R → U` is a typo for `s', t' : R' → U'`.

## References

* [Stacks Project, Tag 0489](https://stacks.math.columbia.edu/tag/0489)
* [Stacks Project, Tag 0460](https://stacks.math.columbia.edu/tag/0460)
* [Stacks Project, Tag 04N0](https://stacks.math.columbia.edu/tag/04N0)
* [Stacks Project, Tag 02VH](https://stacks.math.columbia.edu/tag/02VH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- **Stacks 04N0** in the shape the slicing argument consumes: the affine slice together with
the three properties of its reach map `h : U' ×_{g, U, t} R ⟶ U`. -/
private theorem exists_affine_slice_reach {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.objects.left) (hu : AlgebraicGeometry.IsFiniteTypePoint u)
    [LocallyOfFinitePresentation G.source.left]
    [LocallyOfFinitePresentation G.target.left]
    (hs : ∃ hf : ∀ y : G.objects.left, IsLocallyNoetherian (G.source.left.fiber y),
      Scheme.Hom.IsCohenMacaulay G.source.left hf)
    (ht : ∃ hf : ∀ y : G.objects.left, IsLocallyNoetherian (G.target.left.fiber y),
      Scheme.Hom.IsCohenMacaulay G.target.left hf)
    [LocallyQuasiFinite (stabilizer G).hom] :
    ∃ (U' : Over S) (g : U' ⟶ G.objects) (u' : U'.left), g.left u' = u ∧
      IsAffine U'.left ∧ IsImmersion g.left ∧ LocallyOfFinitePresentation g.left ∧
      (Flat (GroupoidScheme.restrictionReachMap G g).left ∧
        LocallyOfFinitePresentation (GroupoidScheme.restrictionReachMap G g).left ∧
        LocallyQuasiFinite (GroupoidScheme.restrictionReachMap G g).left) := by
  obtain ⟨U', g, u', hgu, hrest⟩ :=
    exists_affine_slice_locallyQuasiFinite_of_isFiniteTypePoint G u hu hs ht
  exact ⟨U', g, u', hgu, hrest.1, hrest.2.1, hrest.2.2.1, hrest.2.2.2.1⟩

private theorem relation_mono {S : Scheme.{u}} {R U : Over S}
    (j : Stacks.Groupoids.PreRelation R U)
    [IsEquivalenceRelation j.target j.source] : Mono j :=
  ((Stacks.Groupoids.isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation j).mp
    inferInstance).1

private noncomputable abbrev relationGroupoid {S : Scheme.{u}} {R U : Over S}
    (j : Stacks.Groupoids.PreRelation R U) [IsEquivalenceRelation j.target j.source] :
    Stacks.Groupoids.GroupoidScheme S := by
  let e : EquivalenceRelation j.target j.source :=
    Classical.choice IsEquivalenceRelation.nonempty_equivalenceRelation
  let k : pullback j.source j.target ⟶ e.c.pt :=
    PullbackCone.IsLimit.lift e.isLimit (pullback.fst _ _) (pullback.snd _ _)
      pullback.condition
  let m : pullback j.source j.target ⟶ R := k ≫ e.t
  exact
    { objects := U
      arrows := R
      source := j.source
      target := j.target
      comp := m
      identity := e.r
      inverse := e.s
      source_identity := e.reflexivity₂
      target_identity := e.reflexivity₁
      source_inverse := e.symmetry₂
      target_inverse := e.symmetry₁
      source_comp := by simp [m, k, Category.assoc, e.transitivity₂]
      target_comp := by simp [m, k, Category.assoc, e.transitivity₁]
      left_identity := by
        intro T f w
        dsimp [m, k]
        apply e.right_cancellation <;>
          simp only [Category.assoc, e.transitivity₁, e.transitivity₂,
            PullbackCone.IsLimit.lift_fst_assoc, PullbackCone.IsLimit.lift_snd_assoc,
            pullback.lift_fst_assoc, pullback.lift_snd_assoc, e.reflexivity₁,
            Category.comp_id]
      right_identity := by
        intro T f w
        dsimp [m, k]
        apply e.right_cancellation <;>
          simp only [Category.assoc, e.transitivity₁, e.transitivity₂,
            PullbackCone.IsLimit.lift_fst_assoc, PullbackCone.IsLimit.lift_snd_assoc,
            pullback.lift_fst_assoc, pullback.lift_snd_assoc, e.reflexivity₂,
            Category.comp_id]
      left_inverse := by
        intro T f w
        dsimp [m, k]
        apply e.right_cancellation <;>
          simp only [Category.assoc, e.transitivity₁, e.transitivity₂,
            PullbackCone.IsLimit.lift_fst_assoc, PullbackCone.IsLimit.lift_snd_assoc,
            pullback.lift_fst_assoc, pullback.lift_snd_assoc, e.symmetry₁,
            e.reflexivity₁, e.reflexivity₂, Category.comp_id]
      right_inverse := by
        intro T f w
        dsimp [m, k]
        apply e.right_cancellation <;>
          simp only [Category.assoc, e.transitivity₁, e.transitivity₂,
            PullbackCone.IsLimit.lift_fst_assoc, PullbackCone.IsLimit.lift_snd_assoc,
            pullback.lift_fst_assoc, pullback.lift_snd_assoc, e.symmetry₂,
            e.reflexivity₁, e.reflexivity₂, Category.comp_id]
      assoc := by
        intro T f g h wfg wgh w₁ w₂
        dsimp [m, k] at w₁ w₂ ⊢
        apply e.right_cancellation <;>
          simp only [Category.assoc, e.transitivity₁, e.transitivity₂,
            PullbackCone.IsLimit.lift_fst_assoc, PullbackCone.IsLimit.lift_snd_assoc,
            pullback.lift_fst_assoc, pullback.lift_snd_assoc] }

private theorem relationGroupoid_relation {S : Scheme.{u}} {R U : Over S}
    (j : Stacks.Groupoids.PreRelation R U) [IsEquivalenceRelation j.target j.source] :
    groupoidPreRelation (relationGroupoid j) = j := by
  apply prod.hom_ext <;>
    simp [groupoidPreRelation, Stacks.Groupoids.PreRelation.target,
      Stacks.Groupoids.PreRelation.source, relationGroupoid]

private theorem groupoid_stabilizer_isIso_of_mono {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S)
    (hpre : Mono (groupoidPreRelation G)) :
    IsIso (stabilizer G).hom := by
  let p := stabilizer G
  have hdiag : G.identity ≫ sourceTarget G =
      𝟙 G.objects ≫ diagonal G := by
    apply (CartesianMonoidalCategory.tensorProductIsBinaryProduct
      G.objects G.objects).hom_ext
    rintro ⟨_ | _⟩ <;>
      simp [sourceTarget, diagonal,
        G.source_identity, G.target_identity]
  let e : G.objects ⟶
      pullback (sourceTarget G) (diagonal G) :=
    pullback.lift G.identity (𝟙 G.objects) hdiag
  let Q := (Over.map G.objects.hom).obj p
  let q : Q ⟶ G.objects := Over.homMk p.hom rfl
  let f : Q ⟶ G.arrows := stabilizerArrowHom G (𝟙 p)
  let g : Q ⟶ G.arrows := q ≫ G.identity
  have htarget : f ≫ G.target = g ≫ G.target := by
    calc
      f ≫ G.target = Over.homMk p.hom :=
        stabilizerArrowHom_target G (𝟙 p)
      _ = q := rfl
      _ = g ≫ G.target := by simp [g, Category.assoc, G.target_identity]
  have hsource : f ≫ G.source = g ≫ G.source := by
    calc
      f ≫ G.source = Over.homMk p.hom :=
        stabilizerArrowHom_source G (𝟙 p)
      _ = q := rfl
      _ = g ≫ G.source := by simp [g, Category.assoc, G.source_identity]
  have hrel : f ≫ groupoidPreRelation G =
      g ≫ groupoidPreRelation G := by
    apply prod.hom_ext
    · simpa [groupoidPreRelation, Stacks.Groupoids.PreRelation.target] using htarget
    · simpa [groupoidPreRelation, Stacks.Groupoids.PreRelation.source] using hsource
  have hArrow : stabilizerArrow G = p.hom ≫ G.identity.left := by
    simpa [f, g, q, Q, stabilizerArrowHom, Over.comp_left] using
      congrArg Over.Hom.left ((cancel_mono (groupoidPreRelation G)).mp hrel)
  have hesnd : e.left ≫ (pullback.snd (sourceTarget G)
      (diagonal G)).left = 𝟙 G.objects.left := by
    change (pullback.lift G.identity (𝟙 G.objects) hdiag ≫
      pullback.snd (sourceTarget G) (diagonal G)).left = _
    rw [pullback.lift_snd]
    simp
  have hefst : e.left ≫ (pullback.fst (sourceTarget G)
      (diagonal G)).left = G.identity.left := by
    change (pullback.lift G.identity (𝟙 G.objects) hdiag ≫
      pullback.fst (sourceTarget G) (diagonal G)).left = _
    rw [pullback.lift_fst]
  let α : Q ⟶ pullback (sourceTarget G) (diagonal G) :=
    Over.homMk (𝟙 p.left) (by
      simp [Q, p, stabilizer])
  have hαe : α = q ≫ e := by
    apply pullback.hom_ext
    · apply Over.OverMorphism.ext
      change (𝟙 p.left ≫ (pullback.fst (sourceTarget G)
          (diagonal G)).left) =
        (p.hom ≫ e.left) ≫ (pullback.fst (sourceTarget G)
          (diagonal G)).left
      calc
        _ = stabilizerArrow G := by
          simp [stabilizerArrow, stabilizer]
        _ = p.hom ≫ G.identity.left := hArrow
        _ = (p.hom ≫ e.left) ≫
            (pullback.fst (sourceTarget G)
              (diagonal G)).left := by
          rw [← hefst, Category.assoc]
    · apply Over.OverMorphism.ext
      change 𝟙 p.left ≫ (pullback.snd (sourceTarget G)
          (diagonal G)).left =
        (p.hom ≫ e.left) ≫ (pullback.snd (sourceTarget G)
          (diagonal G)).left
      rw [Category.assoc, hesnd, Category.comp_id]
      simp [p, stabilizer]
  have hp : p.hom ≫ e.left = 𝟙 p.left := by
    simpa [α, Q, q, p, stabilizer, Over.comp_left] using (congrArg Over.Hom.left hαe).symm
  exact ⟨⟨e.left, hp, by simpa [p, stabilizer] using hesnd⟩⟩

private theorem schemePoints_card_le_two_pow_size (X : Scheme.{u}) :
    Cardinal.mk X ≤ (2 : Cardinal.{u}) ^ X.size := by
  let F : X → Set X.affineOpens := fun x => {V | x ∈ (V : X.Opens)}
  have hF : Function.Injective F := by
    intro x y hxy
    have hinsep : Inseparable x y := (inseparable_iff_forall_isOpen).2 fun O hO => by
      suffices key : ∀ a b, F a = F b → a ∈ O → b ∈ O from
        ⟨key x y hxy, key y x hxy.symm⟩
      intro a b hab ha
      obtain ⟨_, ⟨V, hV, rfl⟩, haV, hVO⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open ha hO
      have hW : (⟨V, hV⟩ : X.affineOpens) ∈ F a := by simpa [F] using haV
      rw [hab] at hW
      exact hVO (by simpa [F] using hW)
    exact hinsep.eq
  calc
    Cardinal.mk X ≤ Cardinal.mk (Set X.affineOpens) := Cardinal.mk_le_of_injective hF
    _ = (2 : Cardinal.{u}) ^ Cardinal.mk X.affineOpens := Cardinal.mk_set
    _ ≤ (2 : Cardinal.{u}) ^ X.size := Cardinal.power_le_power_left
      two_ne_zero (Scheme.mk_affineOpens_le_size X)

private theorem coproduct_small_of_bounded_by_base (B : AlgebraicGeometry.BigFppfSite.{u})
    {X : Scheme.{u}} (hX : B.Contains X) {I : Type u}
    (f : I → X) (hf : Function.Injective f) (Y : I → Scheme.{u})
    (hY : ∀ i, (Y i).size ≤ X.size) :
    B.Contains (∐ Y) := by
  let κ := (2 : Cardinal.{u}) ^ X.size
  have hcoprod : (∐ Y).size ≤ κ :=
    AlgebraicGeometry.schemeSize_coproduct_le Y κ
      (X.aleph0_le_size.trans (Cardinal.cantor X.size).le)
      ((Cardinal.mk_le_of_injective hf).trans (schemePoints_card_le_two_pow_size X))
      (fun i => (hY i).trans (Cardinal.cantor X.size).le)
  exact hcoprod.trans_lt (B.cutoff_isStrongPrelimit hX)

private noncomputable def overPullbackLeftIsoAux {S : Scheme.{u}}
    {X Y Z : Over S} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullback f g).left ≅ pullback f.left g.left :=
  ((IsPullback.of_hasPullback f g).map (Over.forget S)).isoPullback

private theorem restriction_mono {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    [Mono (groupoidPreRelation G)] {V : Over S} {g : V ⟶ G.objects}
    (H : GroupoidScheme.Restriction G g) :
    Mono (groupoidPreRelation H.groupoid) := by
  constructor
  intro T f k h
  have ht : f ≫ H.groupoid.target = k ≫ H.groupoid.target := by
    simpa [groupoidPreRelation, Stacks.Groupoids.PreRelation.target] using
      congrArg (fun z => z ≫ prod.fst) h
  have hs : f ≫ H.groupoid.source = k ≫ H.groupoid.source := by
    simpa [groupoidPreRelation, Stacks.Groupoids.PreRelation.source] using
      congrArg (fun z => z ≫ prod.snd) h
  have hmap : f ≫ H.hom.mapArrows = k ≫ H.hom.mapArrows := by
    apply (cancel_mono (groupoidPreRelation G)).mp
    apply prod.hom_ext
    · simp only [groupoidPreRelation, Category.assoc, prod.lift_fst]
      rw [H.hom.map_target, reassoc_of% ht]
    · simp only [groupoidPreRelation, Category.assoc, prod.lift_snd]
      rw [H.hom.map_source, reassoc_of% hs]
  let F := H.hom.evaluation T
  let ff : H.groupoid.EvaluationHom (T := T) (f ≫ H.groupoid.source)
      (f ≫ H.groupoid.target) :=
    ⟨f, rfl, rfl⟩
  let kk : H.groupoid.EvaluationHom (T := T) (f ≫ H.groupoid.source)
      (f ≫ H.groupoid.target) :=
    ⟨k, hs.symm, ht.symm⟩
  have hff : F.map ff = F.map kk := Stacks.Groupoids.GroupoidScheme.EvaluationHom.ext hmap
  let hFully : F.FullyFaithful := Classical.choice (H.evaluation_fullyFaithful T)
  exact congrArg Stacks.Groupoids.GroupoidScheme.EvaluationHom.arrow (hFully.map_injective hff)

private theorem restrictedGroupoid_stabilizer_locallyQuasiFinite {S : Scheme.{u}}
    {R U U' : Over S} (j : Stacks.Groupoids.PreRelation R U)
    [IsEquivalenceRelation j.target j.source] (g : U' ⟶ U) :
    LocallyQuasiFinite
      (stabilizer
        (AlgebraicGeometry.GroupoidScheme.restrict (relationGroupoid j) g).groupoid).hom := by
  let G := relationGroupoid j
  have : Mono (groupoidPreRelation G) := by
    rw [relationGroupoid_relation j]
    exact relation_mono j
  let H := AlgebraicGeometry.GroupoidScheme.restrict G g
  have : IsIso (stabilizer H.groupoid).hom :=
    groupoid_stabilizer_isIso_of_mono H.groupoid (restriction_mono G H)
  infer_instance

/-- A morphism property respecting isomorphisms is unchanged by composing with isomorphisms. -/
private theorem property_left_comp_iso {S : Scheme.{u}} (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] {X Y X' Y' : Over S} (a : X' ⟶ X) (f : X ⟶ Y) (b : Y ⟶ Y')
    [IsIso a] [IsIso b] (hf : P f.left) : P (a ≫ f ≫ b).left := by
  have : IsIso a.left := (Over.forget S).map_isIso _
  have : IsIso b.left := (Over.forget S).map_isIso _
  simpa only [Over.comp_left, P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso] using hf

private theorem restriction_source_property_of_reach {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) {V : Over S} (g : V ⟶ G.objects)
    (H : GroupoidScheme.Restriction G g)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (hP : P (GroupoidScheme.restrictionReachMap G g).left) : P H.groupoid.source.left := by
  have sq := (IsPullback.of_hasPullback
    (pullback.snd g G.target) (pullback.fst G.source g)).paste_vert
    (IsPullback.of_hasPullback G.source g)
  have hp : P (restrictionSource G g).left :=
    P.of_isPullback (sq.map (Over.forget S)) hP
  rw [H.source_eq]
  exact property_left_comp_iso P _ _ _ hp

private theorem groupoid_inverse_isIso {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) [Mono (groupoidPreRelation G)] :
    IsIso G.inverse := by
  have hi : G.inverse ≫ G.inverse = 𝟙 G.arrows := by
    apply (cancel_mono (groupoidPreRelation G)).mp
    apply prod.hom_ext <;>
      simp [groupoidPreRelation, Category.assoc,
        G.source_inverse, G.target_inverse]
  exact ⟨⟨G.inverse, hi, hi⟩⟩

private theorem groupoid_target_property {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) [Mono (groupoidPreRelation G)]
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hs : P G.source.left) : P G.target.left := by
  have := groupoid_inverse_isIso G
  have : IsIso G.inverse.left := (Over.forget S).map_isIso G.inverse
  have he : G.inverse.left ≫ G.source.left = G.target.left :=
    congrArg Over.Hom.left G.source_inverse
  rwa [← he, P.cancel_left_of_respectsIso]

private theorem reach_property_of_coproduct {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) {I : Type u} (V : I → Over S)
    (g : ∀ i, V i ⟶ G.objects) (Z : Over S)
    (hZ : Z.left = ∐ fun i => (V i).left) (q : Z ⟶ G.objects)
    (hq : q.left = eqToHom hZ ≫ Sigma.desc (fun i => (g i).left))
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P]
    (hp : ∀ i, P (GroupoidScheme.restrictionReachMap G (g i)).left) :
    P (GroupoidScheme.restrictionReachMap G q).left := by
  have hreach {V : Over S} (k : V ⟶ G.objects) :
      (GroupoidScheme.restrictionReachMap G k).left =
        (overPullbackLeftIsoAux k G.target).hom ≫
          (pullback.snd k.left G.target.left ≫ G.source.left) := by
    have hsnd : (overPullbackLeftIsoAux k G.target).hom ≫ pullback.snd k.left G.target.left =
        (pullback.snd k G.target).left :=
      ((IsPullback.of_hasPullback k G.target).map (Over.forget S)).isoPullback_hom_snd
    rw [← Category.assoc, hsnd]
    rfl
  rw [hreach, P.cancel_left_of_respectsIso]
  have hpi (i : I) : P (pullback.snd (g i).left G.target.left ≫ G.source.left) := by
    rw [← P.cancel_left_of_respectsIso (overPullbackLeftIsoAux (g i) G.target).hom, ← hreach]
    exact hp i
  rcases Z with ⟨Z, Zhom⟩
  cases hZ
  simp only [eqToHom_refl, Category.id_comp] at hq
  rw [hq]
  let c := Scheme.IsLocallyDirected.openCover (Discrete.functor (fun i : I => (V i).left))
  apply IsZariskiLocalAtSource.of_openCover
    (c.pullback₂ (pullback.fst (Sigma.desc fun i => (g i).left) G.target.left))
  rintro ⟨i⟩
  change P (pullback.snd _ _ ≫ pullback.snd _ _ ≫ G.source.left)
  have sq := (IsPullback.of_hasPullback (Sigma.ι (fun i => (V i).left) i)
    (pullback.fst (Sigma.desc fun i => (g i).left) G.target.left)).paste_vert
    (IsPullback.of_hasPullback (Sigma.desc fun i => (g i).left) G.target.left)
  simp only [Sigma.ι_comp_desc] at sq
  have hsnd := sq.isoPullback_hom_snd
  rw [← Category.assoc]
  change P ((pullback.snd (Sigma.ι (fun i => (V i).left) i)
    (pullback.fst (Sigma.desc fun i => (g i).left) G.target.left) ≫
    pullback.snd (Sigma.desc fun i => (g i).left) G.target.left) ≫ G.source.left)
  rw [← hsnd, Category.assoc, P.cancel_left_of_respectsIso]
  exact hpi i

private theorem reach_surjective_of_finiteTypePoints {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) {V : Over S} (g : V ⟶ G.objects)
    [Flat (GroupoidScheme.restrictionReachMap G g).left]
    [LocallyOfFinitePresentation (GroupoidScheme.restrictionReachMap G g).left]
    (hg : ∀ x : G.objects.left, AlgebraicGeometry.IsFiniteTypePoint x →
      x ∈ Set.range g.left) : Surjective (GroupoidScheme.restrictionReachMap G g).left := by
  let h := GroupoidScheme.restrictionReachMap G g
  let l : V ⟶ pullback g G.target :=
    pullback.lift (𝟙 V) (g ≫ G.identity) (by simp [G.target_identity])
  have hl : l ≫ h = g := by
    simp only [l, h, GroupoidScheme.restrictionReachMap, pullback.lift_snd_assoc]
    rw [Category.assoc, G.source_identity, Category.comp_id]
  have hfinite : Scheme.finiteTypePoints G.objects.left ⊆
      Set.range h.left := by
    intro x hx
    obtain ⟨y, rfl⟩ := hg x hx
    exact ⟨l.left y, congrArg (fun k : V ⟶ G.objects => k.left y) hl⟩
  refine ⟨fun x => ?_⟩
  by_contra hx
  have hc : IsClosed (Set.range h.left)ᶜ := h.left.isOpenMap.isOpen_range.isClosed_compl
  obtain ⟨y, hy, hfin⟩ := AlgebraicGeometry.inter_finiteTypePoints_nonempty
    hc.isLocallyClosed ⟨x, hx⟩
  exact hy (hfinite hfin)

private theorem exists_site_object (B : AlgebraicGeometry.BigFppfSite.{u})
    {S : Scheme.{u}} (hS : B.Contains S) (X : Over S) (hX : B.Contains X.left) :
    ∃ Y : AlgebraicGeometry.BigFppfOver B S hS, Nonempty ((Over.post B.inclusion).obj Y ≅ X) := by
  let Y : AlgebraicGeometry.BigFppfOver B S hS :=
    Over.mk (B.inclusion.preimage (X := B.obj hX) (Y := B.obj hS) X.hom)
  refine ⟨Y, ⟨Over.isoMk (Iso.refl X.left) ?_⟩⟩
  change 𝟙 X.left ≫ X.hom =
    B.inclusion.map (B.inclusion.preimage (X := B.obj hX) (Y := B.obj hS) X.hom)
  simp only [Category.id_comp]
  exact (B.inclusion.map_preimage (X := B.obj hX) (Y := B.obj hS) X.hom).symm

private theorem singleton_mem_fppf_topology (B : AlgebraicGeometry.BigFppfSite.{u})
    {S : Scheme.{u}} (hS : B.Contains S)
    {X Y : AlgebraicGeometry.BigFppfOver B S hS} (f : X ⟶ Y)
    [Flat ((Over.post B.inclusion).map f).left]
    [LocallyOfFinitePresentation ((Over.post B.inclusion).map f).left]
    [Surjective ((Over.post B.inclusion).map f).left] :
    Sieve.generate (Presieve.singleton f) ∈ AlgebraicGeometry.BigFppfOver.topology B S hS Y := by
  have : Flat (B.inclusion.map f.left) := ‹Flat ((Over.post B.inclusion).map f).left›
  have : LocallyOfFinitePresentation (B.inclusion.map f.left) :=
    ‹LocallyOfFinitePresentation ((Over.post B.inclusion).map f).left›
  have : Surjective (B.inclusion.map f.left) :=
    ‹Surjective ((Over.post B.inclusion).map f).left›
  let E : Covering B.Schemes := ⟨Y.left, PreZeroHypercover.singleton f.left⟩
  have hE : IsFppfCovering E := by
    change (PreZeroHypercover.singleton f.left).presieve₀.map B.inclusion ∈
      Scheme.fppfPrecoverage (B.inclusion.obj Y.left)
    rw [PreZeroHypercover.presieve₀_singleton, Presieve.map_singleton]
    exact (Scheme.singleton_mem_precoverage_iff _ _).2
      ⟨Scheme.Hom.surjective _, inferInstance, inferInstance⟩
  obtain ⟨E', hE', hEquiv⟩ := B.fppf_has_representative E hE
  have hpre : E.2.presieve₀ ∈ B.precoverage Y.left := by
    rcases E' with ⟨Z, E'⟩
    obtain ⟨hY, hComb⟩ := hEquiv
    dsimp [E] at hY
    subst Z
    rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hComb]
    exact ⟨E', rfl, hE'⟩
  have hb : Sieve.generate (Presieve.singleton f.left) ∈ B.topology Y.left := by
    simpa [E, PreZeroHypercover.presieve₀_singleton] using
      Precoverage.generate_mem_toGrothendieck hpre
  rw [AlgebraicGeometry.BigFppfOver.topology, GrothendieckTopology.mem_over_iff,
    Sieve.overEquiv_generate]
  simpa only [← Sieve.arrows_generate_map_eq_functorPushforward,
    Sieve.generate_sieve, Presieve.map_singleton, Over.forget_map] using hb

private theorem restriction_quotient_isIso (B : AlgebraicGeometry.BigFppfSite.{u})
    {S : Scheme.{u}} (hS : B.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type u)]
    (G : Stacks.Groupoids.GroupoidScheme S) {V : Over S} (g : V ⟶ G.objects)
    (H : GroupoidScheme.Restriction G g)
    (hU : B.Contains G.objects.left) (hR : B.Contains G.arrows.left)
    (hV : B.Contains V.left)
    [Flat (GroupoidScheme.restrictionReachMap G g).left]
    [LocallyOfFinitePresentation (GroupoidScheme.restrictionReachMap G g).left]
    [Surjective (GroupoidScheme.restrictionReachMap G g).left] :
    IsIso (GroupoidScheme.restrictionQuotientMap
      (AlgebraicGeometry.BigFppfOver.topology B S hS) (Over.post B.inclusion) G g H) := by
  have hP : B.Contains (pullback g G.target).left := by
    change (pullback g G.target).left.size < B.cutoff
    rw [Scheme.size_congr (overPullbackLeftIsoAux g G.target)]
    exact (Scheme.size_pullback_le g.left G.target.left).trans_lt (max_lt hV hR)
  obtain ⟨X, ⟨eX⟩⟩ := exists_site_object B hS (pullback g G.target) hP
  obtain ⟨Y, ⟨eY⟩⟩ := exists_site_object B hS G.objects hU
  let F : AlgebraicGeometry.BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
  have : F.Full := inferInstanceAs (Over.post B.inclusion).Full
  let a : X ⟶ Y := F.preimage (eX.hom ≫ GroupoidScheme.restrictionReachMap G g ≫ eY.inv)
  have ha : F.map a = eX.hom ≫ GroupoidScheme.restrictionReachMap G g ≫ eY.inv :=
    F.map_preimage _
  have : IsIso eX.hom.left := (Over.forget S).map_isIso _
  have : IsIso eY.inv.left := (Over.forget S).map_isIso _
  have : Flat (F.map a).left := by
    rw [ha, Over.comp_left, Over.comp_left]
    infer_instance
  have : LocallyOfFinitePresentation (F.map a).left := by
    rw [ha, Over.comp_left, Over.comp_left]
    infer_instance
  have : Surjective (F.map a).left := by
    rw [ha, Over.comp_left, Over.comp_left]
    infer_instance
  exact AlgebraicGeometry.GroupoidScheme.isIso_restrictionQuotientMap_of_reach_cover
    _ _ inferInstance
    G g H X Y eX eY a (by
      change F.map a ≫ eY.hom = _
      rw [ha]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
    (singleton_mem_fppf_topology B hS a)

private theorem restriction_arrows_size_le {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) {V : Over S} (g : V ⟶ G.objects)
    (H : GroupoidScheme.Restriction G g) :
    H.groupoid.arrows.left.size ≤ max V.left.size G.arrows.left.size := by
  have hsize : H.groupoid.arrows.left.size =
      (restrictionArrows G g).left.size :=
    congrArg Scheme.size
      (congrArg (fun X : Over S => X.left) H.arrows_eq)
  rw [hsize]
  change (pullback (pullback.snd g G.target)
    (pullback.fst G.source g)).left.size ≤ _
  have hOuter := Scheme.size_congr
    (overPullbackLeftIsoAux (pullback.snd g G.target)
      (pullback.fst G.source g))
  have hSecond := Scheme.size_congr (overPullbackLeftIsoAux g G.target)
  have hThird := Scheme.size_congr (overPullbackLeftIsoAux G.source g)
  have hsecond := Scheme.size_pullback_le g.left G.target.left
  have hthird := Scheme.size_pullback_le G.source.left g.left
  have hfirst :
      (pullback (pullback.snd g G.target).left
        (pullback.fst G.source g).left).size ≤
      max (pullback g.left G.target.left).size
        (pullback G.source.left g.left).size := by
    rw [← hSecond, ← hThird]
    exact Scheme.size_pullback_le _ _
  calc
    _ = (pullback (pullback.snd g G.target).left
        (pullback.fst G.source g).left).size := hOuter
    _ ≤ max (pullback (g.left) G.target.left).size
        (pullback G.source.left g.left).size := hfirst
    _ ≤ max (max V.left.size G.arrows.left.size)
        (max G.arrows.left.size V.left.size) :=
      max_le (hsecond.trans (le_max_left _ _)) (hthird.trans (le_max_right _ _))
    _ = max V.left.size G.arrows.left.size := by
      simp [max_comm]

private theorem equivalenceRelation_transport {S : Scheme.{u}}
    {R U R' U' : Over S} (j : Stacks.Groupoids.PreRelation R U)
    [IsEquivalenceRelation j.target j.source] (eR : R' ≅ R) (eU : U' ≅ U) :
    let j' : Stacks.Groupoids.PreRelation R' U' := eR.hom ≫ j ≫ prod.map eU.inv eU.inv
    IsEquivalenceRelation j'.target j'.source := by
  intro j'
  have : Mono j := relation_mono j
  apply (Stacks.Groupoids.isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation j').2
  refine ⟨inferInstance, fun T => ?_⟩
  have heq (x y : T ⟶ U') : j'.Rel x y ↔ j.Rel (x ≫ eU.hom) (y ≫ eU.hom) := by
    constructor
    · rintro ⟨r, ht, hs⟩
      refine ⟨r ≫ eR.hom, ?_, ?_⟩
      · simpa [j', Stacks.Groupoids.PreRelation.target, Category.assoc] using
          congrArg (· ≫ eU.hom) ht
      · simpa [j', Stacks.Groupoids.PreRelation.source, Category.assoc] using
          congrArg (· ≫ eU.hom) hs
    · rintro ⟨r, ht, hs⟩
      refine ⟨r ≫ eR.inv, ?_, ?_⟩
      · simpa [j', Stacks.Groupoids.PreRelation.target, Category.assoc] using
          congrArg (· ≫ eU.inv) ht
      · simpa [j', Stacks.Groupoids.PreRelation.source, Category.assoc] using
          congrArg (· ≫ eU.inv) hs
  have h := (Stacks.Groupoids.isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation j).1
    inferInstance |>.2 T
  exact ⟨fun x => (heq x x).2 (h.refl _),
    fun {x y} hxy => (heq y x).2 (h.symm ((heq x y).1 hxy)),
    fun {x y z} hxy hyz => (heq x z).2 (h.trans ((heq x y).1 hxy) ((heq y z).1 hyz))⟩

private theorem quotientSheafMap_comp {S : Scheme.{u}} {C : Type*} [Category C]
    (J : GrothendieckTopology C) [HasSheafify J (Type u)] (F : C ⥤ Over S)
    {R₁ U₁ R₂ U₂ R₃ U₃ : Over S}
    (j₁ : Stacks.Groupoids.PreRelation R₁ U₁) (j₂ : Stacks.Groupoids.PreRelation R₂ U₂)
    (j₃ : Stacks.Groupoids.PreRelation R₃ U₃) (r₁ : R₁ ⟶ R₂) (f₁ : U₁ ⟶ U₂)
    (r₂ : R₂ ⟶ R₃) (f₂ : U₂ ⟶ U₃)
    (hs₁ : r₁ ≫ j₂.source = j₁.source ≫ f₁)
    (ht₁ : r₁ ≫ j₂.target = j₁.target ≫ f₁)
    (hs₂ : r₂ ≫ j₃.source = j₂.source ≫ f₂)
    (ht₂ : r₂ ≫ j₃.target = j₂.target ≫ f₂) :
    Stacks.Groupoids.quotientSheafMap J F j₁ j₂ r₁ f₁ hs₁ ht₁ ≫
      Stacks.Groupoids.quotientSheafMap J F j₂ j₃ r₂ f₂ hs₂ ht₂ =
    Stacks.Groupoids.quotientSheafMap J F j₁ j₃ (r₁ ≫ r₂) (f₁ ≫ f₂)
      (by rw [Category.assoc, hs₂, ← Category.assoc, hs₁, Category.assoc])
      (by rw [Category.assoc, ht₂, ← Category.assoc, ht₁, Category.assoc]) := by
  unfold Stacks.Groupoids.quotientSheafMap
  rw [← Functor.map_comp]
  congr 1
  apply coequalizer.hom_ext
  simp [Stacks.Groupoids.quotientPresheafMap, Stacks.Groupoids.toQuotientPresheaf,
    Functor.whiskerLeft_comp, Functor.map_comp, Category.assoc]

private theorem quotientSheafMap_id {S : Scheme.{u}} {C : Type*} [Category C]
    (J : GrothendieckTopology C) [HasSheafify J (Type u)] (F : C ⥤ Over S)
    {R U : Over S} (j : Stacks.Groupoids.PreRelation R U)
    (hs : 𝟙 R ≫ j.source = j.source ≫ 𝟙 U)
    (ht : 𝟙 R ≫ j.target = j.target ≫ 𝟙 U) :
    Stacks.Groupoids.quotientSheafMap J F j j (𝟙 R) (𝟙 U) hs ht = 𝟙 _ := by
  have he : Stacks.Groupoids.quotientPresheafMap F j j (𝟙 R) (𝟙 U) hs ht = 𝟙 _ := by
    apply coequalizer.hom_ext
    simp only [Stacks.Groupoids.quotientPresheafMap, Stacks.Groupoids.toQuotientPresheaf,
      CategoryTheory.Functor.map_id, coequalizer.π_desc]
    exact (Category.comp_id _).symm
  unfold Stacks.Groupoids.quotientSheafMap
  rw [he]
  exact (presheafToSheaf J (Type u)).map_id _

private theorem quotientSheafMap_isIso {S : Scheme.{u}} {C : Type*} [Category C]
    (J : GrothendieckTopology C) [HasSheafify J (Type u)] (F : C ⥤ Over S)
    {R U R' U' : Over S} (j : Stacks.Groupoids.PreRelation R U)
    (j' : Stacks.Groupoids.PreRelation R' U') (r : R ⟶ R') (f : U ⟶ U')
    [IsIso r] [IsIso f]
    (hs : r ≫ j'.source = j.source ≫ f)
    (ht : r ≫ j'.target = j.target ≫ f) :
    IsIso (Stacks.Groupoids.quotientSheafMap J F j j' r f hs ht) := by
  have hs' : inv r ≫ j.source = j'.source ≫ inv f := by
    rw [IsIso.eq_comp_inv, Category.assoc, ← hs, IsIso.inv_hom_id_assoc]
  have ht' : inv r ≫ j.target = j'.target ≫ inv f := by
    rw [IsIso.eq_comp_inv, Category.assoc, ← ht, IsIso.inv_hom_id_assoc]
  refine ⟨⟨Stacks.Groupoids.quotientSheafMap J F j' j (inv r) (inv f) hs' ht', ?_, ?_⟩⟩
  · rw [quotientSheafMap_comp J F j j' j r f (inv r) (inv f) hs ht hs' ht']
    simp only [IsIso.hom_inv_id]
    exact quotientSheafMap_id J F j _ _
  · rw [quotientSheafMap_comp J F j' j j' (inv r) (inv f) r f hs' ht' hs ht]
    simp only [IsIso.inv_hom_id]
    exact quotientSheafMap_id J F j' _ _

private theorem cohenMacaulay_reach_properties {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) [Flat G.source.left] [Flat G.target.left]
    [LocallyOfFinitePresentation G.source.left] [LocallyOfFinitePresentation G.target.left] :
    let W := cohenMacaulayOpen G
    let g : Over.mk (W.ι ≫ G.objects.hom) ⟶ G.objects := Over.homMk W.ι
    Flat (GroupoidScheme.restrictionReachMap G g).left ∧
    LocallyOfFinitePresentation (GroupoidScheme.restrictionReachMap G g).left ∧
    Surjective (GroupoidScheme.restrictionReachMap G g).left := by
  intro W g
  have : IsOpenImmersion (pullback.snd g G.target).left :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback g G.target).map (Over.forget S))
      (show IsOpenImmersion g.left from inferInstanceAs (IsOpenImmersion W.ι))
  refine ⟨?_, ?_, ?_⟩
  · change Flat ((pullback.snd g G.target).left ≫ G.source.left)
    infer_instance
  · change LocallyOfFinitePresentation ((pullback.snd g G.target).left ≫ G.source.left)
    infer_instance
  · -- `W ×_{g, U, t} R` and `t⁻¹(W)` are pullbacks of the same cospan, hence agree over `R`.
    have h₁ : IsPullback (pullback.fst g G.target).left (pullback.snd g G.target).left
        g.left G.target.left :=
      (IsPullback.of_hasPullback g G.target).map (Over.forget S)
    have h₂ : IsPullback (G.target.left ∣_ W) (G.target.left ⁻¹ᵁ W).ι g.left G.target.left :=
      isPullback_morphismRestrict G.target.left W
    have he : (h₁.isoIsPullback _ _ h₂).hom ≫ (G.target.left ⁻¹ᵁ W).ι =
        (pullback.snd g G.target).left := h₁.isoIsPullback_hom_snd _ _ h₂
    change Surjective ((pullback.snd g G.target).left ≫ G.source.left)
    rw [← he, Category.assoc]
    have := AlgebraicGeometry.source_from_target_surjective G
    infer_instance

private theorem quotientSheafMap_isIso_congr_target {S : Scheme.{u}}
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] (F : C ⥤ Over S)
    {R₁ U₁ R₂ U₂ : Over S} (j₁ : Stacks.Groupoids.PreRelation R₁ U₁)
    (j₂ j₃ : Stacks.Groupoids.PreRelation R₂ U₂) (h : j₂ = j₃)
    (r : R₁ ⟶ R₂) (f : U₁ ⟶ U₂)
    (hs₂ : r ≫ j₂.source = j₁.source ≫ f)
    (ht₂ : r ≫ j₂.target = j₁.target ≫ f)
    (hs₃ : r ≫ j₃.source = j₁.source ≫ f)
    (ht₃ : r ≫ j₃.target = j₁.target ≫ f) :
    IsIso (Stacks.Groupoids.quotientSheafMap J F j₁ j₂ r f hs₂ ht₂) →
    IsIso (Stacks.Groupoids.quotientSheafMap J F j₁ j₃ r f hs₃ ht₃) := by
  subst j₃
  exact id

-- Elaborating the two restrictions and their site identifications needs the larger limit.
/-- An equivalence relation on schemes over `S` with flat, locally finitely
presented source and target maps admits a slice: an equivalence relation whose
source and target maps are flat, locally of finite presentation and locally
quasi-finite, together with a morphism `g` of object schemes and a morphism `r`
of arrow schemes over it, inducing an isomorphism of fppf quotient sheaves. -/
@[stacks 0489]
public theorem exists_slice_locallyQuasiFinite
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type u)]
    {R U : AlgebraicGeometry.BigFppfOver B S hS}
    (j : Stacks.Groupoids.PreRelation (S := S) ((Over.post B.inclusion).obj R)
      ((Over.post B.inclusion).obj U))
    [IsEquivalenceRelation j.target j.source]
    [Flat j.source.left] [LocallyOfFinitePresentation j.source.left]
    [Flat j.target.left] [LocallyOfFinitePresentation j.target.left] :
    ∃ (U' R' : AlgebraicGeometry.BigFppfOver B S hS)
      (j' : Stacks.Groupoids.PreRelation (S := S) ((Over.post B.inclusion).obj R')
        ((Over.post B.inclusion).obj U'))
      (g : U' ⟶ U) (r : R' ⟶ R)
      (hs : (Over.post B.inclusion).map r ≫ j.source =
        j'.source ≫ (Over.post B.inclusion).map g)
      (ht : (Over.post B.inclusion).map r ≫ j.target =
        j'.target ≫ (Over.post B.inclusion).map g),
      IsEquivalenceRelation j'.target j'.source ∧
        Flat j'.source.left ∧ LocallyOfFinitePresentation j'.source.left ∧
        LocallyQuasiFinite j'.source.left ∧
        Flat j'.target.left ∧ LocallyOfFinitePresentation j'.target.left ∧
        LocallyQuasiFinite j'.target.left ∧
      IsIso (Stacks.Groupoids.quotientSheafMap
          (AlgebraicGeometry.BigFppfOver.topology B S hS) (Over.post B.inclusion) j' j
          ((Over.post B.inclusion).map r) ((Over.post B.inclusion).map g)
          hs ht) := by
  classical
  let G := relationGroupoid j
  have : Flat G.source.left := inferInstanceAs (Flat j.source.left)
  have : LocallyOfFinitePresentation G.source.left :=
    inferInstanceAs (LocallyOfFinitePresentation j.source.left)
  have : Flat G.target.left := inferInstanceAs (Flat j.target.left)
  have : LocallyOfFinitePresentation G.target.left :=
    inferInstanceAs (LocallyOfFinitePresentation j.target.left)
  let W := cohenMacaulayOpen G
  let U0 : Over S := Over.mk (W.ι ≫ G.objects.hom)
  let g0 : U0 ⟶ G.objects := Over.homMk W.ι (by simp [U0])
  let H := AlgebraicGeometry.GroupoidScheme.restrict G g0
  have hCMsource : ∃ hf : ∀ y : H.groupoid.objects.left,
      IsLocallyNoetherian (H.groupoid.source.left.fiber y),
      Scheme.Hom.IsCohenMacaulay H.groupoid.source.left hf := by
    simpa [H, U0, g0] using AlgebraicGeometry.restricted_source_cohenMacaulay G
  have hCMtarget : ∃ hf : ∀ y : H.groupoid.objects.left,
      IsLocallyNoetherian (H.groupoid.target.left.fiber y),
      Scheme.Hom.IsCohenMacaulay H.groupoid.target.left hf := by
    simpa [H, U0, g0] using AlgebraicGeometry.restricted_target_cohenMacaulay G
  have : LocallyOfFinitePresentation H.groupoid.source.left := by
    simpa [H, U0, g0] using AlgebraicGeometry.restricted_source_locallyOfFinitePresentation G
  have : LocallyOfFinitePresentation H.groupoid.target.left := by
    simpa [H, U0, g0] using AlgebraicGeometry.restricted_target_locallyOfFinitePresentation G
  have : LocallyQuasiFinite (stabilizer H.groupoid).hom :=
    restrictedGroupoid_stabilizer_locallyQuasiFinite j g0
  let I : Type u := {x : H.groupoid.objects.left //
    AlgebraicGeometry.IsFiniteTypePoint x}
  have hLocalSlice (i : I) :=
    exists_affine_slice_reach H.groupoid i.1 i.2 hCMsource hCMtarget
  choose Ui gi ui hui hAffine hImm hLfp hSlice using hLocalSlice
  have hUiSize (i : I) : (Ui i).left.size ≤ H.groupoid.objects.left.size := by
    have : IsImmersion (gi i).left := hImm i
    have : LocallyOfFinitePresentation (gi i).left := hLfp i
    exact Scheme.size_le_of_mono_locallyOfFinitePresentation (gi i).left
  let X : Scheme := ∐ fun i : I => (Ui i).left
  let pS : X ⟶ S := Sigma.desc fun i => (Ui i).hom
  have hGsize : G.objects.left.size < B.cutoff := by
    change ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U).size < B.cutoff
    exact U.left.property
  have hU0size : B.Contains U0.left :=
    (Scheme.size_coe_opens_le G.objects.left W).trans_lt hGsize
  have hXbase : B.Contains H.groupoid.objects.left := by
    have hsize : H.groupoid.objects.left.size = U0.left.size :=
      Scheme.size_congr ((Over.forget S).mapIso (eqToIso H.objects_eq))
    change H.groupoid.objects.left.size < B.cutoff
    rw [hsize]
    exact hU0size
  have hXsize : B.Contains X :=
    coproduct_small_of_bounded_by_base B hXbase (fun i : I => i.1)
      (fun i j hij => Subtype.ext hij) (fun i => (Ui i).left) hUiSize
  let UsiteBase : B.Schemes := B.obj hXsize
  let pS' : B.inclusion.obj UsiteBase ⟶ B.inclusion.obj (B.obj hS) := pS
  let UsiteMap : UsiteBase ⟶ B.obj hS := B.inclusion.preimage pS'
  let Usite : AlgebraicGeometry.BigFppfOver B S hS := Over.mk UsiteMap
  let F : AlgebraicGeometry.BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
  let Uall : Over S := F.obj Usite
  have hUallMap : Uall.hom = pS := by
    change (B.inclusion.preimage pS').hom = pS
    simpa [pS'] using (B.inclusion.map_preimage pS')
  let gall : Uall ⟶ H.groupoid.objects := Over.homMk
    (Sigma.desc fun i => (gi i).left) (by
      change (Sigma.desc fun i => (gi i).left) ≫ H.groupoid.objects.hom = Uall.hom
      rw [hUallMap]
      apply Sigma.hom_ext
      intro i
      simp [pS, (gi i).w])
  let gOver : Uall ⟶ G.objects := gall ≫ eqToHom H.objects_eq ≫ g0
  let H' := AlgebraicGeometry.GroupoidScheme.restrict H.groupoid gall
  have hRsize : B.Contains G.arrows.left := R.left.property
  have hHsize : B.Contains H.groupoid.arrows.left :=
    (restriction_arrows_size_le G g0 H).trans_lt (max_lt hU0size hRsize)
  have hArrowCut : B.Contains H'.groupoid.arrows.left :=
    (restriction_arrows_size_le H.groupoid gall H').trans_lt (max_lt hXsize hHsize)
  let RsiteBase : B.Schemes := B.obj hArrowCut
  let pR : H'.groupoid.arrows.left ⟶ S := H'.groupoid.arrows.hom
  let pR' : B.inclusion.obj RsiteBase ⟶ B.inclusion.obj (B.obj hS) := pR
  let RsiteMap : RsiteBase ⟶ B.obj hS := B.inclusion.preimage pR'
  let Rsite : AlgebraicGeometry.BigFppfOver B S hS := Over.mk RsiteMap
  have hRsiteMap : ((F.obj Rsite).hom) = H'.groupoid.arrows.hom := by
    change (B.inclusion.preimage pR').hom = pR
    simpa [pR'] using (B.inclusion.map_preimage pR')
  let eR : F.obj Rsite ≅ H'.groupoid.arrows :=
    Over.isoMk (Iso.refl _) hRsiteMap.symm
  have : F.Full := inferInstanceAs (Over.post B.inclusion).Full
  let g : Usite ⟶ U := F.preimage gOver
  let r : Rsite ⟶ R := F.preimage (eR.hom ≫ H'.hom.mapArrows ≫ H.hom.mapArrows)
  have : Mono (groupoidPreRelation G) := by
    rw [relationGroupoid_relation j]
    exact relation_mono j
  have : Mono (groupoidPreRelation H.groupoid) := restriction_mono G H
  have : Mono (groupoidPreRelation H'.groupoid) := restriction_mono H.groupoid H'
  let jH := groupoidPreRelation H.groupoid
  let jK := groupoidPreRelation H'.groupoid
  have : IsEquivalenceRelation jK.target jK.source :=
    (Stacks.Groupoids.isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation jK).2
      ⟨inferInstance, AlgebraicGeometry.groupoidPreRelation_isPreEquivalenceRelation _⟩
  let eU : Uall ≅ H'.groupoid.objects := eqToIso H'.objects_eq.symm
  let j' : Stacks.Groupoids.PreRelation (F.obj Rsite) Uall :=
    eR.hom ≫ jK ≫ prod.map eU.inv eU.inv
  have hj' : IsEquivalenceRelation j'.target j'.source :=
    equivalenceRelation_transport jK eR eU
  have hs' : j'.source = eR.hom ≫ H'.groupoid.source ≫ eU.inv := by
    simp [j', jK, Stacks.Groupoids.PreRelation.source, groupoidPreRelation]
  have ht' : j'.target = eR.hom ≫ H'.groupoid.target ≫ eU.inv := by
    simp [j', jK, Stacks.Groupoids.PreRelation.target, groupoidPreRelation]
  have ho : eU.hom ≫ H'.hom.mapObjects ≫ H.hom.mapObjects = gOver := by
    rw [H'.mapObjects_eq, H.mapObjects_eq]
    simp [Category.assoc, eU, gOver]
  have hs0 : (eR.hom ≫ H'.hom.mapArrows ≫ H.hom.mapArrows) ≫ G.source =
      j'.source ≫ eU.hom ≫ H'.hom.mapObjects ≫ H.hom.mapObjects := by
    simp [Category.assoc, hs', H.hom.map_source, reassoc_of% H'.hom.map_source]
  have ht0 : (eR.hom ≫ H'.hom.mapArrows ≫ H.hom.mapArrows) ≫ G.target =
      j'.target ≫ eU.hom ≫ H'.hom.mapObjects ≫ H.hom.mapObjects := by
    simp [Category.assoc, ht', H.hom.map_target, reassoc_of% H'.hom.map_target]
  have hs : F.map r ≫ j.source = j'.source ≫ F.map g := by
    rw [show F.map r = eR.hom ≫ H'.hom.mapArrows ≫ H.hom.mapArrows from F.map_preimage _,
      show F.map g = gOver from F.map_preimage _, ← ho]
    exact hs0
  have ht : F.map r ≫ j.target = j'.target ≫ F.map g := by
    rw [show F.map r = eR.hom ≫ H'.hom.mapArrows ≫ H.hom.mapArrows from F.map_preimage _,
      show F.map g = gOver from F.map_preimage _, ← ho]
    exact ht0
  let : IsZariskiLocalAtSource (@Flat : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  let : IsZariskiLocalAtSource (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  let : IsZariskiLocalAtSource (@LocallyQuasiFinite : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  have hReach (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P]
      (hp : ∀ i, P (GroupoidScheme.restrictionReachMap H.groupoid (gi i)).left) :
      P (GroupoidScheme.restrictionReachMap H.groupoid gall).left :=
    reach_property_of_coproduct H.groupoid Ui gi Uall rfl gall rfl P hp
  have hReachFlat := hReach (@Flat) fun i => (hSlice i).1
  have hReachLfp := hReach (@LocallyOfFinitePresentation) fun i => (hSlice i).2.1
  have hReachLqf := hReach (@LocallyQuasiFinite) fun i => (hSlice i).2.2
  have : Surjective (GroupoidScheme.restrictionReachMap H.groupoid gall).left :=
    reach_surjective_of_finiteTypePoints H.groupoid gall (by
      intro x hx
      let i : I := ⟨x, hx⟩
      refine ⟨(Sigma.ι (fun i => (Ui i).left) i) (ui i), ?_⟩
      change (Sigma.ι (fun i => (Ui i).left) i ≫ Sigma.desc (fun i => (gi i).left)) (ui i) = x
      rw [Sigma.ι_comp_desc]
      exact hui i)
  have hKsource (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
      (hp : P (GroupoidScheme.restrictionReachMap H.groupoid gall).left) :
      P j'.source.left := by
    have hsource := restriction_source_property_of_reach H.groupoid gall H' P hp
    rw [hs']
    exact property_left_comp_iso P _ _ _ hsource
  have hKtarget (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
      (hp : P (GroupoidScheme.restrictionReachMap H.groupoid gall).left) :
      P j'.target.left := by
    have hsource := restriction_source_property_of_reach H.groupoid gall H' P hp
    have htarget := groupoid_target_property H'.groupoid P hsource
    rw [ht']
    exact property_left_comp_iso P _ _ _ htarget
  refine ⟨Usite, Rsite, j', g, r, hs, ht, hj',
    hKsource _ hReachFlat, hKsource _ hReachLfp, hKsource _ hReachLqf,
    hKtarget _ hReachFlat, hKtarget _ hReachLfp, hKtarget _ hReachLqf, ?_⟩
  let J := AlgebraicGeometry.BigFppfOver.topology B S hS
  have hCMreach := cohenMacaulay_reach_properties G
  have : Flat (GroupoidScheme.restrictionReachMap G g0).left := hCMreach.1
  have : LocallyOfFinitePresentation (GroupoidScheme.restrictionReachMap G g0).left := hCMreach.2.1
  have : Surjective (GroupoidScheme.restrictionReachMap G g0).left := hCMreach.2.2
  have := restriction_quotient_isIso B hS G g0 H hGsize hRsize hU0size
  have := restriction_quotient_isIso B hS H.groupoid gall H' hXbase hHsize hXsize
  have hsE : eR.hom ≫ jK.source = j'.source ≫ eU.hom := by
    rw [hs']
    simp [Category.assoc, jK, groupoidPreRelation, Stacks.Groupoids.PreRelation.source]
  have htE : eR.hom ≫ jK.target = j'.target ≫ eU.hom := by
    rw [ht']
    simp [Category.assoc, jK, groupoidPreRelation, Stacks.Groupoids.PreRelation.target]
  have := quotientSheafMap_isIso J F j' jK eR.hom eU.hom hsE htE
  let qE := Stacks.Groupoids.quotientSheafMap J F j' jK eR.hom eU.hom hsE htE
  let qK := GroupoidScheme.restrictionQuotientMap J F H.groupoid gall H'
  let qH := GroupoidScheme.restrictionQuotientMap J F G g0 H
  have hIso : IsIso (qE ≫ qK ≫ qH) := inferInstance
  have hTotal : IsIso (Stacks.Groupoids.quotientSheafMap J F j'
      (groupoidPreRelation G)
      (eR.hom ≫ H'.hom.mapArrows ≫ H.hom.mapArrows)
      (eU.hom ≫ H'.hom.mapObjects ≫ H.hom.mapObjects)
      (by simpa [groupoidPreRelation, Stacks.Groupoids.PreRelation.source] using hs0)
      (by simpa [groupoidPreRelation, Stacks.Groupoids.PreRelation.target] using ht0)) := by
    simpa only [qE, qK, qH, jK, GroupoidScheme.restrictionQuotientMap,
      quotientSheafMap_comp] using hIso
  change IsIso (Stacks.Groupoids.quotientSheafMap J F j' j (F.map r) (F.map g) hs ht)
  have hTotal' := quotientSheafMap_isIso_congr_target J F j'
    (groupoidPreRelation G) j (relationGroupoid_relation j) _ _ _ _
    hs0 ht0 hTotal
  simpa only [ho,
    show F.map r = eR.hom ≫ H'.hom.mapArrows ≫ H.hom.mapArrows from F.map_preimage _,
    show F.map g = gOver from F.map_preimage _] using hTotal'

end AlgebraicGeometry

end
