module

public import StacksFrontier.AlgebraicGeometry.Spaces.SiteGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.DenseOpenAgreement

/-!
# Gluing a sheaf on the big fppf site from open subfunctors

Let `G` be a sheaf of sets on the big fppf site over `S` and let `F i` be subfunctors of `G`,
each represented by an object `Y i` of the site, such that every point `ξ ∈ G(T)` cuts out opens
`W i T ξ` of `T` with: the pullback of `ξ` along `h : T' ⟶ T` lies in `F i` exactly when `h`
lands in `W i T ξ`; and suppose these opens cover `T`. If the index type and the representing
objects are bounded by one cardinal below the cutoff of the site, then `G` is representable by
an object of the site ([Stacks, Tag 01JJ], in the form used by the proof of
[Stacks, Tag 0B9Q]).

This is the site counterpart of `Stacks.OverGluing.isRepresentable_of_openSubfunctors`, which
glues on all schemes over a base and so produces a representing scheme with no size control.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_of_openSubfunctors`.

## References

* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 0B9Q](https://stacks.math.columbia.edu/tag/0B9Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (G : Sheaf (BigFppfOver.topology B S hS) (Type u)) {ι : Type u}
  (F : ι → Subfunctor G.obj) (Y : ι → BigFppfOver B S hS)
  (R : ∀ i, (F i).toFunctor.RepresentableBy (Y i))
  (W : ∀ (i : ι) (T : BigFppfOver B S hS), G.obj.obj (op T) → T.left.obj.Opens)
  (hW : ∀ (i : ι) (T T' : BigFppfOver B S hS) (ξ : G.obj.obj (op T)) (h : T' ⟶ T),
    G.obj.map h.op ξ ∈ (F i).obj (op T') ↔
      ∀ t, (BigFppfOver.toScheme B S hS).map h t ∈ W i T ξ)

/-- The chart attached to a represented subfunctor. -/
abbrev subfunctorOpenChart (i : ι) : yoneda.obj (Y i) ⟶ G.obj := (R i).toIso.hom ≫ (F i).ι

include hW in
/-- The restriction of `x` to the open `W i T x` lies in `F i`. -/
theorem map_openSubHom_mem (i : ι) (T : BigFppfOver B S hS) (x : G.obj.obj (op T)) :
    G.obj.map (BigFppfOver.openSubHom B S hS T (W i T x)).op x ∈
      (F i).obj (op (BigFppfOver.openSubObj B S hS T (W i T x))) :=
  (hW i T _ x _).2 fun t => by
    rw [openSubHom_toScheme]
    exact (Scheme.Opens.range_ι (W i T x) ▸ (⟨t, rfl⟩ : (W i T x).ι t ∈ Set.range (W i T x).ι) :
      (W i T x).ι t ∈ ((W i T x) : Set _))

include hW in
/-- **A subfunctor cut out by opens is an open immersion**, relative to representable
presheaves. -/
theorem presheaf_subfunctorOpenChart (i : ι) :
    (openImmersionOver B S hS).presheaf (subfunctorOpenChart G F Y R i) := by
  apply MorphismProperty.relative.of_exists
  intro a ζ
  let x : G.obj.obj (op a) := yonedaEquiv ζ
  let O := W i a x
  let b := BigFppfOver.openSubObj B S hS a O
  let snd : b ⟶ a := BigFppfOver.openSubHom B S hS a O
  have hmem : G.obj.map snd.op x ∈ (F i).obj (op b) := map_openSubHom_mem G F W hW i a x
  let k : b ⟶ Y i := (R i).homEquiv.symm ⟨_, hmem⟩
  have hk : (R i).homEquiv k = ⟨_, hmem⟩ := (R i).homEquiv.apply_symm_apply _
  have hlk {Z : BigFppfOver B S hS} (l : Z ⟶ b) :
      ((R i).homEquiv (l ≫ k)).1 = G.obj.map (l ≫ snd).op x := by
    rw [(R i).homEquiv_comp, hk]
    show G.obj.map l.op (G.obj.map snd.op x) = _
    rw [← Functor.map_comp_apply, ← op_comp]
  refine ⟨b, yoneda.map k, snd, ?_, ?_⟩
  · have hmono : Mono snd := mono_openSubHom B S hS a O
    apply IsPullback.iff_app.mpr
    intro T'
    apply (Types.isPullback_iff _ _ _ _).2
    refine ⟨?_, ?_, ?_⟩
    · ext l
      show ((R i).homEquiv (l ≫ k)).1 = ζ.app T' (l ≫ snd)
      exact (hlk l).trans (map_yonedaEquiv ζ (l ≫ snd))
    · intro l l' h
      exact (cancel_mono snd).1 h.2
    · intro m e he
      change T'.unop ⟶ Y i at m
      change T'.unop ⟶ a at e
      change ((R i).homEquiv m).1 = ζ.app T' e at he
      have he' : ((R i).homEquiv m).1 = G.obj.map e.op x := he.trans (map_yonedaEquiv ζ e).symm
      have hrange : Set.range ((BigFppfOver.toScheme B S hS).map e) ⊆ (O : Set a.left.obj) := by
        rintro _ ⟨t, rfl⟩
        exact (hW i a T'.unop x e).1 (he' ▸ ((R i).homEquiv m).2) t
      let l := openSubObjLift B S hS a O e hrange
      have hl : l ≫ snd = e := openSubObjLift_comp_openSubHom B S hS a O e hrange
      refine ⟨l, ?_, hl⟩
      apply (R i).homEquiv.injective
      apply Subtype.ext
      show ((R i).homEquiv (l ≫ k)).1 = ((R i).homEquiv m).1
      rw [hlk, hl, he']
  · show _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map snd)
    rw [openSubHom_toScheme]
    infer_instance

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (G : Sheaf (BigFppfOver.topology B S hS) (Type u)) {ι : Type u}
  (F : ι → Subfunctor G.obj) (Yr : ι → BigFppfOver B S hS)
  (R : ∀ i, (F i).toFunctor.RepresentableBy (Yr i))
  (W : ∀ (i : ι) (T : BigFppfOver B S hS), G.obj.obj (op T) → T.left.obj.Opens)
  (hW : ∀ (i : ι) (T T' : BigFppfOver B S hS) (ξ : G.obj.obj (op T)) (h : T' ⟶ T),
    G.obj.map h.op ξ ∈ (F i).obj (op T') ↔
      ∀ t, (BigFppfOver.toScheme B S hS).map h t ∈ W i T ξ)
  (hcov : ∀ (T : BigFppfOver B S hS) (ξ : G.obj.obj (op T)) (t : T.left.obj),
    ∃ i, t ∈ W i T ξ)

include hW hcov in
/-- The charts of a covering family of open subfunctors are jointly locally surjective. -/
theorem isLocallySurjective_sigmaDesc_subfunctorOpenChart :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Sigma.desc (subfunctorOpenChart G F Yr R)) := by
  refine ⟨fun {T} x => ?_⟩
  refine GrothendieckTopology.superset_covering _ ?_
    (BigFppfOver.sieve_ofArrows_mem_topology_of_jointlySurjective B S hS
      (fun i => BigFppfOver.openSubObj B S hS T (W i T x)) T
      (fun i => BigFppfOver.openSubHom B S hS T (W i T x))
      (fun i => by rw [openSubHom_toScheme]; infer_instance)
      (fun t => (hcov T x t).imp fun i hi => by
        rwa [openSubHom_toScheme, Scheme.Opens.range_ι]))
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro Z g ⟨i⟩
  have hmem := map_openSubHom_mem G F W hW i T x
  refine ⟨(Sigma.ι (fun i => yoneda.obj (Yr i)) i).app _ ((R i).homEquiv.symm ⟨_, hmem⟩), ?_⟩
  have hc := congrArg (fun n => n.app (op (BigFppfOver.openSubObj B S hS T (W i T x)))
      ((R i).homEquiv.symm ⟨_, hmem⟩))
    (Sigma.ι_desc (subfunctorOpenChart G F Yr R) i)
  refine (ConcreteCategory.comp_apply _ _ _).symm.trans (hc.trans ?_)
  exact congrArg Subtype.val ((R i).homEquiv.apply_symm_apply _)

include hW in
/-- **The glued scheme lies in the site** when the index type and the representing objects are
bounded by one cardinal below the cutoff. -/
theorem contains_glued_subfunctorOpenChart (c : Cardinal.{u}) (hc : c < B.cutoff)
    (hι : #ι ≤ c) (hY : ∀ i, ((BigFppfOver.toScheme B S hS).obj (Yr i)).size ≤ c) :
    B.Contains (schemeGlueData (subfunctorOpenChart G F Yr R)
      (presheaf_subfunctorOpenChart G F Yr R W hW)).glued := by
  set D := schemeGlueData (subfunctorOpenChart G F Yr R)
    (presheaf_subfunctorOpenChart G F Yr R W hW)
  rcases isEmpty_or_nonempty D.J with hJe | hJn
  · have : IsEmpty D.glued := ⟨fun x ↦ (D.ι_jointly_surjective x).elim fun i _ ↦ hJe.elim i⟩
    have e : D.glued ≅ (∅ : Scheme.{u}) :=
      (isInitialOfIsEmpty (X := D.glued)).uniqueUpToIso emptyIsInitial
    exact lt_of_le_of_lt ((Scheme.size_congr e).trans_le Scheme.size_empty_le_aleph0)
      B.aleph0_lt_cutoff
  · have hcov' : ⨆ i, (D.ι i).opensRange = ⊤ := by
      refine top_le_iff.mp fun x _ ↦ ?_
      obtain ⟨i, y, hy⟩ := D.ι_jointly_surjective x
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, y, hy⟩
    refine lt_of_le_of_lt (Scheme.size_le_of_iSup_eq_top _ hcov') ?_
    refine max_lt (hι.trans_lt hc) (lt_of_le_of_lt (ciSup_le' fun i => ?_) hc)
    exact (Scheme.size_congr (D.ι i).isoOpensRange).symm.trans_le (hY i)

include F R W hW hcov in
/-- **Stacks Project, Tag 01JJ, for the big fppf site, with open subfunctors.** A sheaf `G` on
the big fppf site over `S` with a family of represented subfunctors `F i`, each cut out at every
point `ξ ∈ G(T)` by an open `W i T ξ` of `T`, these opens covering `T`, is representable by an
object of the site, provided the index type and the representing objects are bounded by one
cardinal below the cutoff. -/
theorem isRepresentable_of_openSubfunctors (c : Cardinal.{u}) (hc : c < B.cutoff)
    (hι : #ι ≤ c) (hY : ∀ i, ((BigFppfOver.toScheme B S hS).obj (Yr i)).size ≤ c) :
    G.obj.IsRepresentable :=
  isRepresentable_of_openCover_of_contains (subfunctorOpenChart G F Yr R)
    (presheaf_subfunctorOpenChart G F Yr R W hW)
    (contains_glued_subfunctorOpenChart G F Yr R W hW c hc hι hY)
    (isLocallySurjective_sigmaDesc_subfunctorOpenChart G F Yr R W hW hcov)

end AlgebraicGeometry.Space
