module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleSites
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimitDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StageFaithfulness
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.FiniteAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves
public import StacksCore.Tactic.StacksAttribute

/-!
# Coverings of the small étale site of a limit of schemes are refined at a finite stage

Let `X = lim X_i` be the limit of a directed inverse system of quasi-compact, quasi-separated
schemes with affine transition morphisms, inside a big étale site. Stacks 0EYL exhibits the
affine étale site of `X` as the colimit of the affine étale sites of the `X_i`; in particular
every étale covering of `X` is refined by the inverse image of a *finite* étale covering of some
stage. This file proves that assertion for the small étale site and the final object, which is
the form in which the descent of finite local constancy along a limit of schemes uses it.

## Main results

* `AlgebraicGeometry.smallEtaleStagesCoveringsRefine_of_isLimit` — **Stacks 0EYL for the small
  étale site**: the predicate `AlgebraicGeometry.SmallEtaleStagesCoveringsRefine` holds for a
  limit cone over a directed inverse system of quasi-compact, quasi-separated schemes with
  affine transition morphisms.

## The three geometric hypotheses

`AlgebraicGeometry.SmallEtaleStagesCoveringsRefine` is a predicate on a cone, not on a limit
cone, and its own context assumes nothing of the stages. As a statement about an arbitrary cone
it is false, and quasi-compactness is what fails: take `I` a one-point preorder, `Dg` the
constant diagram at an object whose underlying scheme is an infinite disjoint union of copies of
`Spec ℚ`, and `c` the cone with that vertex and identity projection — a limit cone with affine
transition morphisms. The family of the components is an étale covering of the final object, and
a finite family refining it has its members mapping into finitely many components, hence cannot
be jointly surjective. The statement proved here therefore carries the limit cone, the affine
transitions and the quasi-compactness and quasi-separatedness of the stages explicitly.

## Implementation notes

The proof is the source's. A covering of the final object of `X_étale` is first refined, through
each point of `X`, by an object of the site whose underlying scheme is affine: the point is
covered by an affine étale object because the affine subsite is dense (Tag 04HR), and the
covering pulled back to that affine object is refined by a finite affine covering of it (Tag
021E). Quasi-compactness of `X` — which follows from that of the stages, the projections of a
limit with affine transitions being affine — cuts the resulting family down to a finite one.

Each member of the finite family is affine over `X`, hence descends to an affine étale object
over a stage by Tag 0EYL for objects
(`Stacks.EtaleCohomology.affineEtaleSiteColimit_obj_descends`); directedness puts all members at
one stage. The images of the members at that stage form a constructible subset containing the
image of `X`, so by Tag 05F4 it contains the image of a later stage, and at that stage the
base-changed family is jointly surjective, hence a covering of the final object by
`AlgebraicGeometry.SmallEtale.generate_ofArrows_mem_topology_of_jointlySurjective`.

Base change along a morphism of the ambient site is a *chosen* fibre product, so an object
presented by an abstract cartesian square is only canonically isomorphic to it. Those
comparisons are made once, in `AlgebraicGeometry.smallEtaleBaseChangeIsoOfIsPullback`, which
turns a cartesian square of underlying schemes into an isomorphism of the small étale site;
everything else is assembled from it.

## References

* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks Project, Tag 04HR](https://stacks.math.columbia.edu/tag/04HR)
* [Stacks Project, Tag 021E](https://stacks.math.columbia.edu/tag/021E)
* [Stacks Project, Tag 05F4](https://stacks.math.columbia.edu/tag/05F4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Filter

universe u

namespace AlgebraicGeometry

section Site

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An arrow to the final object of the small étale site is the structure morphism of its
source, the final object having identity structure morphism. -/
private lemma smallEtale_hom_left_to_final {Z : SmallEtale B S hS}
    (h : Z ⟶ SmallEtale.final B S hS) : h.hom.left = Z.obj.hom := by
  rw [(SmallEtale.finalIsTerminal B S hS).hom_ext h (ObjectProperty.homMk (Over.homMk Z.obj.hom))]
  rfl

/-- The underlying morphism of schemes of an arrow to the final object of the small étale site
is the structure morphism of its source. -/
private lemma smallEtale_toScheme_map_to_final {Z : SmallEtale B S hS}
    (h : Z ⟶ SmallEtale.final B S hS) :
    (SmallEtale.toScheme B S hS).map h = B.inclusion.map Z.obj.hom :=
  congrArg B.inclusion.map (smallEtale_hom_left_to_final B S hS h)

/-- An arrow of the small étale site is a morphism over the base scheme. -/
private lemma smallEtale_comp_hom {Z W : SmallEtale B S hS} (q : Z ⟶ W) :
    B.inclusion.map q.hom.left ≫ B.inclusion.map W.obj.hom = B.inclusion.map Z.obj.hom := by
  rw [← B.inclusion.map_comp, Over.w q.hom]

/-- An arrow of the small étale site is a morphism over the base scheme, read on points. -/
private lemma smallEtale_apply_hom {Z W : SmallEtale B S hS} (q : Z ⟶ W)
    (v : B.inclusion.obj Z.obj.left) :
    (B.inclusion.map W.obj.hom) ((B.inclusion.map q.hom.left) v) =
      (B.inclusion.map Z.obj.hom) v := by
  rw [← smallEtale_comp_hom B S hS q, Scheme.Hom.comp_apply]

/-- The image of the structure morphism grows along arrows of the small étale site. -/
private lemma smallEtale_range_subset_of_hom {Z W : SmallEtale B S hS} (q : Z ⟶ W) :
    Set.range (B.inclusion.map Z.obj.hom) ⊆ Set.range (B.inclusion.map W.obj.hom) := by
  rintro x ⟨w, rfl⟩
  exact ⟨(B.inclusion.map q.hom.left) w, smallEtale_apply_hom B S hS q w⟩

/-- **Stacks 021E, in the small étale site.** A covering sieve of an object of the small étale
site whose underlying scheme is affine contains, through every point of that object, an arrow
whose source is affine: the covering is refined by a finite affine covering, and one of its
members hits the point. -/
private theorem exists_affine_mem_sieve_mem_range
    (U : SmallEtale B S hS) [IsAffine (B.inclusion.obj U.obj.left)]
    {R : Sieve U} (hR : R ∈ SmallEtale.topology B S hS U)
    (y : B.inclusion.obj U.obj.left) :
    ∃ (Z : SmallEtale B S hS) (q : Z ⟶ U), R q ∧
      IsAffine (B.inclusion.obj Z.obj.left) ∧
      y ∈ Set.range (B.inclusion.map q.hom.left) := by
  obtain ⟨Rp, hRp, hle⟩ :=
    Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hR
  obtain ⟨E, rfl, hE⟩ := (SmallEtale.mem_precoverage_iff B S hS).mp hRp
  have : IsAffine (B.inclusion.obj ((SmallEtale.toBigScheme B S hS).obj U)) :=
    ‹IsAffine (B.inclusion.obj U.obj.left)›
  obtain ⟨F, hF, -, hFaff, hFref, hFet⟩ :=
    B.exists_finite_affine_refinement ((SmallEtale.toBigScheme B S hS).obj U)
      (E.map (SmallEtale.toBigScheme B S hS)) hE
  have hcov : Presieve.ofArrows (fun t : F.I₀ => B.inclusion.obj (F.X t))
      (fun t => B.inclusion.map (F.f t)) ∈
      Scheme.etalePrecoverage (B.inclusion.obj ((SmallEtale.toBigScheme B S hS).obj U)) := hF.1
  have hFref' : ∀ t : F.I₀, ∃ (j : E.I₀)
      (b : F.X t ⟶ (SmallEtale.toBigScheme B S hS).obj (E.X j)),
      b ≫ (SmallEtale.toBigScheme B S hS).map (E.f j) = F.f t := hFref
  obtain ⟨t, ht⟩ := ((Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).mp hcov).1 y
  have : Etale (B.inclusion.map U.obj.hom) := U.property
  have : Etale (B.inclusion.map (F.f t)) := hFet t
  have hZet : Etale (B.inclusion.map (F.f t ≫ U.obj.hom)) := by
    rw [B.inclusion.map_comp]
    exact Etale.etale_comp _ _
  refine ⟨⟨Over.mk (F.f t ≫ U.obj.hom), hZet⟩,
    ObjectProperty.homMk (Over.homMk (F.f t) (by simp)), ?_, hFaff t, ht⟩
  obtain ⟨j, b, hb⟩ := hFref' t
  have hEw : (SmallEtale.toBigScheme B S hS).map (E.f j) ≫ U.obj.hom = (E.X j).obj.hom :=
    Over.w ((SmallEtale.inclusion B S hS).map (E.f j))
  have hw : b ≫ (E.X j).obj.hom = F.f t ≫ U.obj.hom := by
    rw [← hEw, ← Category.assoc, hb]
  have hfac : (ObjectProperty.homMk (Over.homMk (F.f t) (by simp)) :
      (⟨Over.mk (F.f t ≫ U.obj.hom), hZet⟩ : SmallEtale B S hS) ⟶ U) =
      (ObjectProperty.homMk (Over.homMk b hw) :
        (⟨Over.mk (F.f t ≫ U.obj.hom), hZet⟩ : SmallEtale B S hS) ⟶ E.X j) ≫ E.f j :=
    ObjectProperty.hom_ext _ (Over.OverMorphism.ext hb.symm)
  rw [hfac]
  exact R.downward_closed (hle _ _ (Presieve.ofArrows.mk j)) _

/-- **Stacks 04HR.** Every point of `S` lies in the image of an object of its small étale site
whose underlying scheme is affine: the small affine étale site is a dense subsite of the small
étale site, so the sieve of arrows factoring through affine objects is covering, and a covering
sieve of the small étale site is jointly surjective on points. -/
private theorem exists_affine_smallEtale_mem_range (x : S) :
    ∃ Z : SmallEtale B S hS, IsAffine (B.inclusion.obj Z.obj.left) ∧
      x ∈ Set.range (B.inclusion.map Z.obj.hom) := by
  have hden : (SmallAffineEtale.inclusion B S hS).IsDenseSubsite
      (SmallAffineEtale.topology B S hS) (SmallEtale.topology B S hS) :=
    (SmallAffineEtale.inclusion_isSpecialCocontinuous B S hS).2
  have := Functor.IsDenseSubsite.isCoverDense (SmallAffineEtale.topology B S hS)
    (SmallEtale.topology B S hS) (SmallAffineEtale.inclusion B S hS)
  have hcov := Functor.is_cover_of_isCoverDense (SmallAffineEtale.inclusion B S hS)
    (SmallEtale.topology B S hS) (SmallEtale.final B S hS)
  obtain ⟨W, q, hq, hx⟩ := SmallEtale.exists_mem_arrows_mem_range B S hS hcov x
  obtain ⟨⟨A, f₁, f₂, he⟩⟩ := hq
  have hW : (SmallEtale.toScheme B S hS).map q = B.inclusion.map W.obj.hom :=
    smallEtale_toScheme_map_to_final B S hS q
  rw [hW] at hx
  exact ⟨(SmallAffineEtale.inclusion B S hS).obj A, A.property,
    smallEtale_range_subset_of_hom B S hS f₁ hx⟩

/-- A covering of the final object of the small étale site of a quasi-compact scheme is refined
by a *finite* family of objects whose underlying schemes are affine, each mapping into a member
of the covering. -/
private theorem exists_finite_affine_refinement_smallEtale [CompactSpace S]
    {K : Type (u + 1)} (V : K → SmallEtale B S hS)
    (g : ∀ k, V k ⟶ SmallEtale.final B S hS)
    (hg : Sieve.ofArrows V g ∈ SmallEtale.topology B S hS (SmallEtale.final B S hS)) :
    ∃ (T : Type u) (_ : Finite T) (Z : T → SmallEtale B S hS),
      (∀ t, IsAffine (B.inclusion.obj (Z t).obj.left)) ∧
      (∀ t, ∃ m : K, Nonempty (Z t ⟶ V m)) ∧
      ∀ x : B.inclusion.obj (B.obj S hS),
        ∃ t, x ∈ Set.range (B.inclusion.map (Z t).obj.hom) := by
  classical
  have key : ∀ x : B.inclusion.obj (B.obj S hS), ∃ Z : SmallEtale B S hS,
      IsAffine (B.inclusion.obj Z.obj.left) ∧
      (∃ m : K, Nonempty (Z ⟶ V m)) ∧ x ∈ Set.range (B.inclusion.map Z.obj.hom) := by
    intro x
    obtain ⟨A, hAaff, y, hy⟩ := exists_affine_smallEtale_mem_range B S hS x
    have := hAaff
    let τ : A ⟶ SmallEtale.final B S hS := (SmallEtale.finalIsTerminal B S hS).from A
    have hpb : (Sieve.ofArrows V g).pullback τ ∈ SmallEtale.topology B S hS A :=
      (SmallEtale.topology B S hS).pullback_stable τ hg
    obtain ⟨Z, q, hq, hZaff, w, hw⟩ := exists_affine_mem_sieve_mem_range B S hS A hpb y
    obtain ⟨m, d, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hq
    refine ⟨Z, hZaff, ⟨m, ⟨d⟩⟩, w, ?_⟩
    rw [← smallEtale_apply_hom B S hS q w, hw, hy]
  choose Z hZaff hZmem hZx using key
  have hopen : ∀ x : B.inclusion.obj (B.obj S hS),
      IsOpen (Set.range (B.inclusion.map (Z x).obj.hom)) := by
    intro x
    have : Etale (B.inclusion.map (Z x).obj.hom) := (Z x).property
    simpa only [Set.image_univ] using
      (B.inclusion.map (Z x).obj.hom).isOpenMap Set.univ isOpen_univ
  have hcs : CompactSpace (B.inclusion.obj (B.obj S hS)) := ‹CompactSpace S›
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : B.inclusion.obj (B.obj S hS) => Set.range (B.inclusion.map (Z x).obj.hom)) hopen
    fun x _ => Set.mem_iUnion.2 ⟨x, hZx x⟩
  refine ⟨{x : B.inclusion.obj (B.obj S hS) // x ∈ s}, inferInstance, fun t => Z t.1,
    fun t => hZaff t.1, fun t => hZmem t.1, fun x => ?_⟩
  obtain ⟨y, hy, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact ⟨⟨y, hy⟩, hx⟩

end Site

section BaseChange

/-- The image of a composite of morphisms of schemes is contained in the image of the second. -/
private lemma range_comp_subset {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) :
    Set.range (a ≫ b) ⊆ Set.range b := by
  rintro z ⟨x, rfl⟩
  exact ⟨a x, (Scheme.Hom.comp_apply a b x).symm⟩

/-- A point of the base of a cartesian square of schemes over which a point of the other side
lies has a preimage in the apex of the square. -/
private lemma exists_preimage_of_isPullback_scheme {P A A' C : Scheme.{u}} {fst : P ⟶ A}
    {snd : P ⟶ A'} {f : A ⟶ C} {g : A' ⟶ C} (h : IsPullback fst snd f g) (a : A) (a' : A')
    (hcomp : f a = g a') : ∃ p : P, snd p = a' := by
  obtain ⟨q, -, hq⟩ := Scheme.Pullback.exists_preimage_pullback a a' hcomp
  exact ⟨h.isoPullback.inv q, by rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_snd, hq]⟩

variable (B : BigEtaleSite.{u})

/-- The base-change square of the small étale site, read on underlying schemes. The first
projection is presented with the base change itself as its source, so that the square's apex is
spelled the same way as the object the base-change functor produces. -/
private lemma smallEtaleBaseChange_isPullback {S T : B.Scheme} (f : T ⟶ S)
    (Y : SmallEtale B S.obj S.property) :
    IsPullback
      (show B.inclusion.obj ((smallEtaleBaseChange B f).obj Y).obj.left ⟶
          B.inclusion.obj Y.obj.left from B.inclusion.map (pullback.fst Y.obj.hom f))
      (B.inclusion.map ((smallEtaleBaseChange B f).obj Y).obj.hom)
      (B.inclusion.map Y.obj.hom) (B.inclusion.map f) :=
  (IsPullback.of_hasPullback Y.obj.hom f).map B.inclusion

/-- **An étale object presented by a cartesian square is the base change.** If the structure
morphism of an étale object `Z` over `T` is a fibre product of the structure morphism of an
étale object `Y` over `S` along `f : T ⟶ S`, then `Z` is the base change of `Y` along `f`. -/
private def smallEtaleBaseChangeIsoOfIsPullback {S T : B.Scheme} (f : T ⟶ S)
    (Y : SmallEtale B S.obj S.property) (Z : SmallEtale B T.obj T.property)
    (p : B.inclusion.obj Z.obj.left ⟶ B.inclusion.obj Y.obj.left)
    (h : IsPullback p (B.inclusion.map Z.obj.hom) (B.inclusion.map Y.obj.hom)
      (B.inclusion.map f)) :
    (smallEtaleBaseChange B f).obj Y ≅ Z := by
  let e₀ := (smallEtaleBaseChange_isPullback B f Y).isoIsPullback _ _ h
  let e₁ : ((smallEtaleBaseChange B f).obj Y).obj.left ≅ Z.obj.left := B.inclusion.preimageIso e₀
  have he₁ : B.inclusion.map e₁.hom = e₀.hom := B.inclusion.map_preimage _
  have hw : e₁.hom ≫ Z.obj.hom = ((smallEtaleBaseChange B f).obj Y).obj.hom := by
    apply B.inclusion.map_injective
    rw [B.inclusion.map_comp, he₁]
    exact (smallEtaleBaseChange_isPullback B f Y).isoIsPullback_hom_snd _ _ h
  exact (SmallEtale.inclusion B T.obj T.property).preimageIso (Over.isoMk e₁ hw)

/-- The base change of an affine étale object along an affine morphism is affine. -/
private lemma isAffine_smallEtaleBaseChange {S T : B.Scheme} (f : T ⟶ S)
    (haf : IsAffineHom (B.inclusion.map f)) (Y : SmallEtale B S.obj S.property)
    (hY : IsAffine (B.inclusion.obj Y.obj.left)) :
    IsAffine (B.inclusion.obj ((smallEtaleBaseChange B f).obj Y).obj.left) := by
  have hY' := hY
  have hfst : IsAffineHom (B.inclusion.map (pullback.fst Y.obj.hom f)) :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback Y.obj.hom f).map B.inclusion).flip haf
  have hpb : IsAffine (B.inclusion.obj (pullback Y.obj.hom f)) :=
    isAffine_of_isAffineHom (B.inclusion.map (pullback.fst Y.obj.hom f))
  exact hpb

/-- The image of a base change, composed with the morphism base changed along, lands in the
image of the original object. -/
private lemma smallEtaleBaseChange_range_subset {S T : B.Scheme} (f : T ⟶ S)
    (Y : SmallEtale B S.obj S.property) :
    Set.range (B.inclusion.map ((smallEtaleBaseChange B f).obj Y).obj.hom ≫
        B.inclusion.map f) ⊆ Set.range (B.inclusion.map Y.obj.hom) := by
  rw [← (smallEtaleBaseChange_isPullback B f Y).w]
  exact range_comp_subset _ _

end BaseChange

section Stages

variable (B : BigEtaleSite.{u}) {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

/-- Base change to the vertex of an object base changed to a later stage is base change to the
vertex from the earlier stage: the two cartesian squares paste. -/
private def smallEtaleStageTransitionBaseChangeIso {i j : I} (h : i ≤ j)
    (Y : SmallEtale B (Dg.obj (op i)).obj (Dg.obj (op i)).property) :
    (smallEtaleBaseChange B (coneStageHom B Dg c hX j)).obj
        ((smallEtaleBaseChange B (systemStageHom B Dg h)).obj Y) ≅
      (smallEtaleBaseChange B (coneStageHom B Dg c hX i)).obj Y := by
  have hpaste := (IsPullback.of_hasPullback
      ((smallEtaleBaseChange B (systemStageHom B Dg h)).obj Y).obj.hom
      (coneStageHom B Dg c hX j)).paste_horiz
    (IsPullback.of_hasPullback Y.obj.hom (systemStageHom B Dg h))
  rw [coneStageHom_comp B Dg c hX h] at hpaste
  exact (smallEtaleBaseChangeIsoOfIsPullback B (coneStageHom B Dg c hX i) Y
    ((smallEtaleBaseChange B (coneStageHom B Dg c hX j)).obj
      ((smallEtaleBaseChange B (systemStageHom B Dg h)).obj Y)) _
    (hpaste.map B.inclusion)).symm

/-- **Stacks 0EYL for objects, in the small étale site.** An object of the small affine étale
site of the vertex is the base change of an object of the small étale site of a stage, whose
underlying scheme is again affine. -/
private theorem exists_stage_smallEtale_baseChange_iso (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (ZA : SmallAffineEtale B c.pt hX) :
    ∃ (k : I) (Y : SmallEtale B (Dg.obj (op k)).obj (Dg.obj (op k)).property),
      IsAffine (B.inclusion.obj Y.obj.left) ∧
        Nonempty ((smallEtaleBaseChange B (coneStageHom B Dg c hX k)).obj Y ≅ ZA.obj) := by
  have : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom ((Dg ⋙ B.inclusion).map e) := fun e => haff e
  obtain ⟨m, Y₁, hY₁⟩ := Stacks.EtaleCohomology.affineEtaleSiteColimit_obj_descends.{u, u}
    (Dg ⋙ B.inclusion) c B (fun i => (Dg.obj i).property) hX hc ZA
  subst hY₁
  let L := Stacks.EtaleCohomology.affineEtaleSiteColimit.{u, u} (Dg ⋙ B.inclusion) c B
    (fun i => (Dg.obj i).property) hX hc
  exact ⟨(L.indexEquiv.functor.obj m).unop, ((L.levelEquiv m).functor.obj Y₁).obj,
    ((L.levelEquiv m).functor.obj Y₁).property,
    ⟨smallEtaleBaseChangeIsoOfIsPullback B _ _ _ _ (L.toLimit_isPullback m Y₁)⟩⟩

/-- A finite family of objects of the small étale site of the vertex with affine underlying
schemes is base changed from a single stage beyond a prescribed one. -/
private theorem exists_common_stage_smallEtale_baseChange_iso (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e))) (i : I)
    {T : Type u} [Finite T] (Z : T → SmallEtale B c.pt hX)
    (hZ : ∀ t, IsAffine (B.inclusion.obj (Z t).obj.left)) :
    ∃ (j : I) (_ : i ≤ j) (Y : T → SmallEtale B (Dg.obj (op j)).obj (Dg.obj (op j)).property),
      (∀ t, IsAffine (B.inclusion.obj (Y t).obj.left)) ∧
        ∀ t, Nonempty ((smallEtaleBaseChange B (coneStageHom B Dg c hX j)).obj (Y t) ≅ Z t) := by
  classical
  have : Fintype T := Fintype.ofFinite T
  choose k Y hYaff hYiso using fun t =>
    exists_stage_smallEtale_baseChange_iso B Dg c hX hc haff ⟨Z t, hZ t⟩
  obtain ⟨j, hj⟩ := Finset.exists_le (insert i (Finset.univ.image k))
  have hkj : ∀ t : T, k t ≤ j := fun t =>
    hj (k t) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem k (Finset.mem_univ t)))
  refine ⟨j, hj i (Finset.mem_insert_self _ _),
    fun t => (smallEtaleBaseChange B (systemStageHom B Dg (hkj t))).obj (Y t),
    fun t => isAffine_smallEtaleBaseChange B (systemStageHom B Dg (hkj t)) (haff _) (Y t)
      (hYaff t),
    fun t => ⟨smallEtaleStageTransitionBaseChangeIso B Dg c hX (hkj t) (Y t) ≪≫
      (hYiso t).some⟩⟩

end Stages

section Main

variable (B : BigEtaleSite.{u}) {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

/-- **Stacks 0EYL for the small étale site.** Let `X = lim X_i` be the limit of a directed
inverse system of quasi-compact, quasi-separated schemes with affine transition morphisms inside
a big étale site. Every covering of the final object of the small étale site of `X` is refined
by the inverse image of a finite covering of the final object at some stage beyond a prescribed
one.

The hypotheses are the three geometric conditions the assertion needs and which
`AlgebraicGeometry.SmallEtaleStagesCoveringsRefine`, a predicate on an arbitrary cone, does not
itself carry: the cone is limiting, the transition morphisms are affine, and the stages are
quasi-compact and quasi-separated. Quasi-compactness is not cosmetic: the conclusion demands a
finite refining family, and over a vertex which is an infinite disjoint union the covering by
the components admits none. -/
@[stacks 0EYL "coverings of the final object, for the small étale site"]
public theorem smallEtaleStagesCoveringsRefine_of_isLimit (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesCoveringsRefine B Dg c hX := by
  classical
  have : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom ((Dg ⋙ B.inclusion).map e) := fun e => haff e
  have : ∀ p : Iᵒᵖ, CompactSpace ((Dg ⋙ B.inclusion).obj p) := fun p => hqc p.unop
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit (Dg ⋙ B.inclusion) c hc
  intro i K V g hg
  obtain ⟨T, hTfin, Z, hZaff, hZref, hZsurj⟩ :=
    exists_finite_affine_refinement_smallEtale B c.pt hX V g hg
  have : Finite T := hTfin
  obtain ⟨j, hij, Y, hYaff, hYiso⟩ :=
    exists_common_stage_smallEtale_baseChange_iso B Dg c hX hc haff i Z hZaff
  have hcj : CompactSpace (B.inclusion.obj (B.obj (Dg.obj (op j)).obj
    (Dg.obj (op j)).property)) := hqc j
  have hsj : QuasiSeparatedSpace (B.inclusion.obj (B.obj (Dg.obj (op j)).obj
    (Dg.obj (op j)).property)) := hqs j
  -- the images of the family at the stage `j` form a constructible subset of `X_j`
  set E : Set (B.inclusion.obj (B.obj (Dg.obj (op j)).obj (Dg.obj (op j)).property)) :=
    ⋃ t : T, Set.range (B.inclusion.map (Y t).obj.hom) with hEdef
  have hEc : Topology.IsConstructible E := by
    rw [hEdef]
    refine Topology.IsConstructible.iUnion fun t => ?_
    have : IsAffine (B.inclusion.obj (Y t).obj.left) := hYaff t
    have : Etale (B.inclusion.map (Y t).obj.hom) := (Y t).property
    simpa only [Set.image_univ] using
      ((B.inclusion.map (Y t).obj.hom).isLocallyConstructible_image
        Topology.IsLocallyConstructible.univ).isConstructible
  -- it contains the image of the vertex
  have hlim : Set.range ⇑(c.π.app (op j)) ⊆ E := by
    rintro x ⟨w, rfl⟩
    obtain ⟨t, hw⟩ := hZsurj w
    obtain ⟨v, hv⟩ := smallEtale_range_subset_of_hom B c.pt hX (hYiso t).some.inv hw
    have hcs : B.inclusion.map (coneStageHom B Dg c hX j) = c.π.app (op j) := rfl
    rw [hEdef]
    refine Set.mem_iUnion.2 ⟨t, ?_⟩
    refine smallEtaleBaseChange_range_subset B (coneStageHom B Dg c hX j) (Y t) ⟨v, ?_⟩
    rw [Scheme.Hom.comp_apply, hv, hcs]
  -- Tag 05F4: a constructible subset containing the image of the limit contains the image of a
  -- later stage
  obtain ⟨l₀, hl₀⟩ := eventually_atTop.mp
    (eventually_range_transition_subset_of_isLocallyConstructible
      (descentSituationOfBigEtaleCone B Dg c hc haff hqc hqs j) E
      hEc.isLocallyConstructible hlim)
  obtain ⟨l, hjl, hl₀l⟩ := directed_of (· ≤ ·) j l₀
  obtain ⟨hbl, hsub⟩ := hl₀ l hl₀l
  refine ⟨l, hij.trans hbl, ULift.{u + 1} T, inferInstance,
    fun k => (smallEtaleBaseChange B (systemStageHom B Dg hbl)).obj (Y k.down),
    fun k => (SmallEtale.finalIsTerminal B (Dg.obj (op l)).obj
      (Dg.obj (op l)).property).from _, ?_, fun k => ?_⟩
  · refine SmallEtale.generate_ofArrows_mem_topology_of_jointlySurjective B _ _ _ _ fun z => ?_
    have hz := hsub ⟨z, rfl⟩
    rw [hEdef] at hz
    obtain ⟨t, v, hv⟩ := Set.mem_iUnion.mp hz
    obtain ⟨p, hp⟩ := exists_preimage_of_isPullback_scheme
      (smallEtaleBaseChange_isPullback B (systemStageHom B Dg hbl) (Y t)) v z hv
    refine ⟨ULift.up t, p, ?_⟩
    rwa [smallEtale_hom_left_to_final B (Dg.obj (op l)).obj (Dg.obj (op l)).property]
  · obtain ⟨m, hm⟩ := hZref k.down
    exact ⟨m, ⟨(smallEtaleStageTransitionBaseChangeIso B Dg c hX hbl (Y k.down)).hom ≫
      (hYiso k.down).some.hom ≫ hm.some⟩⟩

end Main

end AlgebraicGeometry

end
