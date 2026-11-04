module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.OverPullbackLeft
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.OpenSaturation
public import StacksFrontier.AlgebraicGeometry.Spaces.GroupoidQuotientRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.StandardCoverings

/-!
# Restricting an fppf equivalence relation gives an open subspace of the quotient

Let `S` be a scheme, `U` an `S`-scheme and `j = (t, s) : R ⟶ U ×_S U` an equivalence relation
whose two maps are surjective, flat and locally of finite presentation. Let `g : U' ⟶ U` be
flat and locally of finite presentation and let `j'` be the restriction of `j` along `g`. Then
the induced map of fppf quotient sheaves `U'/R' ⟶ U/R` is representable by open immersions.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.isOpenImmersion_restrictedQuotientMap` is the representable open
  immersion of quotient sheaves.

## Implementation notes

The statement is reduced to
`AlgebraicGeometry.GroupoidScheme.isOpenImmersion_restrictionQuotientMap_of_open_image`, the
corresponding statement for a groupoid scheme and an open saturation, applied to the
canonical groupoid scheme `AlgebraicGeometry.groupoidSchemeOfIsEquivalenceRelation` extending
`j`. Three things have to be supplied.

First, the saturation of `g` has open image: the saturation map is flat and locally of finite
presentation, because it is the composite of the base change of `g` along the target map with
the source map, so it is an open map and its image is an open subscheme `W`. Second, the
factorization of the saturation through `W` is surjective, flat and locally of finite
presentation — the corestriction of a flat, locally finitely presented morphism to its open
image is again one, and it is surjective because `W` is exactly the image — and a surjective,
flat, locally finitely presented morphism induces a local surjection of fppf sheaves on
functors of points, by refining the singleton covering it defines to one of the chosen
covering families of the site
(`AlgebraicGeometry.exists_isCovering_refining_fppfCovering`). Third, the quotient sheaf of the
restricted groupoid has to be identified with the quotient sheaf of the restricted relation,
which is `AlgebraicGeometry.groupoidRestrictionQuotientIso`, and the resulting map compared
with `Stacks.Groupoids.restrictQuotientSheafMap` for `j` itself, which uses that the induced
map on quotient sheaves depends only on the map on objects.

The comparison with the canonical groupoid scheme is through the `eqToHom`s of
`AlgebraicGeometry.ExtendsRelation`, so the relation `j` and the pre-relation of the groupoid
scheme are identified by an isomorphism of pre-relations rather than by an equality, and the
two restrictions are identified by transporting that isomorphism
(`AlgebraicGeometry.Space.restrictedRelationIso`).

## References

* [Stacks Project, Tag 02WU](https://stacks.math.columbia.edu/tag/02WU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Space

open Stacks.Groupoids

/-- The corestriction of a flat, locally finitely presented morphism to an open subscheme
containing exactly its image is flat, locally of finite presentation and surjective. -/
private theorem corestriction_fppf {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] (W : Y.Opens)
    (hW : Set.range f.base ⊆ Set.range W.ι.base)
    (hWsurj : Set.range W.ι.base ⊆ Set.range f.base) :
    Flat (AlgebraicGeometry.IsOpenImmersion.lift W.ι f hW) ∧
    LocallyOfFinitePresentation (AlgebraicGeometry.IsOpenImmersion.lift W.ι f hW) ∧
    Surjective (AlgebraicGeometry.IsOpenImmersion.lift W.ι f hW) := by
  let P : X.Opens := f ⁻¹ᵁ W
  have hP : P = ⊤ := by
    ext x
    refine ⟨fun _ => by simp, fun _ => ?_⟩
    show f x ∈ (W : Set Y)
    rcases hW ⟨x, rfl⟩ with ⟨y, hy⟩
    rw [← hy]
    exact y.property
  let e : X ≅ P.toScheme := X.topIso.symm ≪≫ (X.isoOfEq hP).symm
  let q : P.toScheme ⟶ W.toScheme := f.resLE W P le_rfl
  let k : X ⟶ W.toScheme := AlgebraicGeometry.IsOpenImmersion.lift W.ι f hW
  have hk : e.hom ≫ q = k := by
    apply (cancel_mono W.ι).1
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι (f := f) (U := W) (V := P) le_rfl,
      AlgebraicGeometry.IsOpenImmersion.lift_fac (f := W.ι) (g := f) hW]
    simp [e, P]
  refine ⟨?_, ?_, ?_⟩
  · show Flat k
    rw [← hk]
    infer_instance
  · show LocallyOfFinitePresentation k
    rw [← hk]
    infer_instance
  · show Surjective k
    constructor
    intro y
    rcases hWsurj ⟨y, rfl⟩ with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply W.ι.isOpenEmbedding.injective
    show (k ≫ W.ι) x = W.ι y
    rw [AlgebraicGeometry.IsOpenImmersion.lift_fac (f := W.ι) (g := f) hW]
    simpa using hx

/-- Conjugating a morphism by `eqToHom`s of two equalities of objects: the identification of its
two ends moves to either side of the equation. -/
private theorem eqToHom_comp_comm {C : Type*} [Category C] {A A' B B' : C}
    (hA : A = A') (hB : B = B') (a : A ⟶ B) (b : A' ⟶ B')
    (h : eqToHom hA.symm ≫ a ≫ eqToHom hB = b) :
    eqToHom hA.symm ≫ a = b ≫ eqToHom hB.symm ∧ eqToHom hA ≫ b = a ≫ eqToHom hB := by
  subst hA hB
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h ⊢
  exact ⟨h, h.symm⟩

/-- The source and target maps of a groupoid scheme extending a relation inherit
surjectivity, flatness and local finite presentation from the relation. -/
private theorem endpoints_fppf {S : Scheme.{u}} {R U : Over S}
    (j : PreRelation R U) (G : GroupoidScheme S) (h : ExtendsRelation j G)
    (hsurj : Surjective j.source.left) (htsurj : Surjective j.target.left)
    (hsflat : Flat j.source.left) (htflat : Flat j.target.left)
    (hslfp : LocallyOfFinitePresentation j.source.left)
    (htlfp : LocallyOfFinitePresentation j.target.left) :
    (Surjective G.source.left ∧ Flat G.source.left ∧
      LocallyOfFinitePresentation G.source.left) ∧
    (Surjective G.target.left ∧ Flat G.target.left ∧
      LocallyOfFinitePresentation G.target.left) := by
  let r : R ⟶ G.arrows := eqToHom h.arrows_eq.symm
  let f : U ⟶ G.objects := eqToHom h.objects_eq.symm
  have hrIso : IsIso r.left := inferInstanceAs (IsIso ((Over.forget S).map r))
  have hfIso : IsIso f.left := inferInstanceAs (IsIso ((Over.forget S).map f))
  have hs : r ≫ G.source = j.source ≫ f :=
    (eqToHom_comp_comm h.arrows_eq h.objects_eq _ _ h.source_eq).1
  have ht : r ≫ G.target = j.target ≫ f :=
    (eqToHom_comp_comm h.arrows_eq h.objects_eq _ _ h.target_eq).1
  have hs' : r.left ≫ G.source.left = j.source.left ≫ f.left := by
    simpa using congrArg Over.Hom.left hs
  have ht' : r.left ≫ G.target.left = j.target.left ≫ f.left := by
    simpa using congrArg Over.Hom.left ht
  have key : ∀ (a : G.arrows.left ⟶ G.objects.left) (b : R.left ⟶ U.left),
      r.left ≫ a = b ≫ f.left → Surjective b → Flat b → LocallyOfFinitePresentation b →
      Surjective a ∧ Flat a ∧ LocallyOfFinitePresentation a := by
    intro a b hab _ _ _
    have ha : a = inv r.left ≫ b ≫ f.left := by rw [← hab]; simp
    rw [ha]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  exact ⟨key _ _ hs' hsurj hsflat hslfp, key _ _ ht' htsurj htflat htlfp⟩

/-- An isomorphism of pre-relations over an isomorphism of the objects induces an isomorphism
of their restrictions along a morphism to the objects. -/
private noncomputable def restrictedRelationIso {S : Scheme.{u}}
    {R U R' U' X : Over S} (j : PreRelation R U) (j' : PreRelation R' U')
    (g : X ⟶ U) (f : U ⟶ U') (r : R ⟶ R') (rInv : R' ⟶ R) (fInv : U' ⟶ U)
    (hrel : r ≫ j' = j ≫ prod.map f f)
    (hrelInv : rInv ≫ j = j' ≫ prod.map fInv fInv)
    (hf : f ≫ fInv = 𝟙 U) (_hfInv : fInv ≫ f = 𝟙 U')
    (hr : r ≫ rInv = 𝟙 R) (hrInv : rInv ≫ r = 𝟙 R') :
    AlgebraicGeometry.PreRelation.restriction j g ≅
      AlgebraicGeometry.PreRelation.restriction j' (g ≫ f) := by
  let p := AlgebraicGeometry.PreRelation.restriction j g
  let p' := AlgebraicGeometry.PreRelation.restriction j' (g ≫ f)
  have hprod : prod.map (g ≫ f) (g ≫ f) = prod.map g g ≫ prod.map f f := by
    apply prod.hom_ext <;> simp
  have hprodInv : prod.map (g ≫ f) (g ≫ f) ≫ prod.map fInv fInv = prod.map g g := by
    apply prod.hom_ext <;> simp [Category.assoc, hf]
  let rFwd : p ⟶ p' := pullback.lift
    (pullback.fst (prod.map g g) j)
    (pullback.snd (prod.map g g) j ≫ r)
    (by rw [hprod, pullback.condition_assoc, Category.assoc, hrel])
  let rBack : p' ⟶ p := pullback.lift
    (pullback.fst (prod.map (g ≫ f) (g ≫ f)) j')
    (pullback.snd (prod.map (g ≫ f) (g ≫ f)) j' ≫ rInv)
    (by rw [← hprodInv, pullback.condition_assoc, Category.assoc, hrelInv])
  have hFwdFst : rFwd ≫ pullback.fst (prod.map (g ≫ f) (g ≫ f)) j' =
      pullback.fst (prod.map g g) j := pullback.lift_fst _ _ _
  have hBackFst : rBack ≫ pullback.fst (prod.map g g) j =
      pullback.fst (prod.map (g ≫ f) (g ≫ f)) j' := pullback.lift_fst _ _ _
  have hFwd : rFwd ≫ pullback.snd (prod.map (g ≫ f) (g ≫ f)) j' =
      pullback.snd (prod.map g g) j ≫ r := pullback.lift_snd _ _ _
  have hBack : rBack ≫ pullback.snd (prod.map g g) j =
      pullback.snd (prod.map (g ≫ f) (g ≫ f)) j' ≫ rInv := pullback.lift_snd _ _ _
  refine ⟨rFwd, rBack, ?_, ?_⟩ <;> apply pullback.hom_ext <;>
    simp [hFwd, hBack, reassoc_of% hFwd, reassoc_of% hBack, hFwdFst, hBackFst, hr, hrInv]

/-- The saturation of a flat, locally finitely presented morphism along a groupoid scheme
whose source map is flat and locally of finite presentation is again flat and locally of
finite presentation. -/
private theorem restrictionReach_fppf {S : Scheme.{u}} {U' : Over S}
    (G : GroupoidScheme S) (g : U' ⟶ G.objects)
    [Flat g.left] [LocallyOfFinitePresentation g.left]
    [Flat G.source.left] [LocallyOfFinitePresentation G.source.left] :
    Flat (GroupoidScheme.restrictionReachMap G g).left ∧
      LocallyOfFinitePresentation (GroupoidScheme.restrictionReachMap G g).left := by
  have : Flat (pullback.snd g G.target).left := by
    rw [← overPullbackLeftIso_hom_snd]
    infer_instance
  have : LocallyOfFinitePresentation (pullback.snd g G.target).left := by
    rw [← overPullbackLeftIso_hom_snd]
    infer_instance
  constructor
  · show Flat ((pullback.snd g G.target).left ≫ G.source.left)
    infer_instance
  · show LocallyOfFinitePresentation ((pullback.snd g G.target).left ≫ G.source.left)
    exact locallyOfFinitePresentation_comp _ _

/-- A surjective, flat, locally finitely presented morphism of `S`-schemes induces a local
surjection of fppf sheaves on restricted functors of points. -/
private theorem sheafified_fppf_map_locallySurjective
    {S : Scheme.{u}} (B : BigFppfSite.{u}) (hS : B.Contains S)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {X Y : Over S} (k : X ⟶ Y)
    [Flat k.left] [LocallyOfFinitePresentation k.left] [Surjective k.left] :
    Sheaf.IsLocallySurjective
      ((presheafToSheaf (BigFppfOver.topology B S hS) (Type u)).map
        ((Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft (yoneda.map k))) := by
  classical
  let C := BigFppfOver B S hS
  let J := BigFppfOver.topology B S hS
  let F : C ⥤ Over S := Over.post (X := B.obj hS) B.inclusion
  let p := F.op.whiskerLeft (yoneda.map k)
  have hp : Presheaf.IsLocallySurjective J p := by
    refine ⟨?_⟩
    intro A s
    let f : F.obj A ⟶ Y := s
    let P := pullback k f
    let q := pullback.snd k f
    have hq : Flat q.left ∧ LocallyOfFinitePresentation q.left ∧ Surjective q.left := by
      refine ⟨?_, ?_, ?_⟩ <;> rw [← overPullbackLeftIso_hom_snd] <;> infer_instance
    let E : PreZeroHypercover.{u + 1} (B.inclusion.obj A.left) :=
      PreZeroHypercover.singleton q.left
    have hE : E.presieve₀ ∈ Scheme.fppfPrecoverage (B.inclusion.obj A.left) := by
      show E.presieve₀ ∈ Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)
        (B.inclusion.obj A.left)
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨fun y => ?_, fun _ => ⟨hq.1, hq.2.1⟩⟩
      obtain ⟨x, hx⟩ := hq.2.2.surj y
      exact ⟨PUnit.unit, x, hx⟩
    obtain ⟨V, hV, ⟨ref⟩⟩ := exists_isCovering_refining_fppfCovering B A.left E hE
    have hRcov : (Sieve.overEquiv A).symm V.sieve₀ ∈ J A := by
      rw [GrothendieckTopology.mem_over_iff]
      simpa [PreZeroHypercover.sieve₀, Sieve.ofArrows] using
        (Precoverage.generate_mem_toGrothendieck
          (show V.presieve₀ ∈ B.precoverage A.left from ⟨V, rfl, hV⟩))
    have hle : (Sieve.overEquiv A).symm V.sieve₀ ≤ Presheaf.imageSieve p s := by
      rw [← ((Sieve.overEquiv A).symm).apply_symm_apply (Presheaf.imageSieve p s),
        ((Sieve.overEquiv A).symm).map_rel_iff]
      simp only [OrderIso.symm_symm]
      rw [PreZeroHypercover.sieve₀, Sieve.ofArrows, Sieve.generate_le_iff,
        Presieve.ofArrows_le_iff]
      intro i
      let W : C := Over.mk (V.f i ≫ A.hom)
      let α : W ⟶ A := Over.homMk (V.f i) (by simp [W])
      let b : (B.inclusion.obj W.left) ⟶ P.left := ref.h₀ i
      have hbp : b ≫ q.left = B.inclusion.map (V.f i) := ref.w₀ i
      have hbeta : b ≫ P.hom = (F.obj W).hom := by
        rw [← Over.w q]
        show (b ≫ q.left) ≫ (F.obj A).hom = (F.obj W).hom
        rw [hbp]
        exact (B.inclusion.map_comp _ _).symm
      let β : F.obj W ⟶ P := Over.homMk b hbeta
      have hfactor : β ≫ q = F.map α := by
        ext
        exact hbp
      let t : F.obj W ⟶ X := β ≫ pullback.fst k f
      have hlift : p.app (op W) t = (F.op ⋙ yoneda.obj Y).map α.op s := by
        show t ≫ k = F.map α ≫ f
        rw [← hfactor]
        simp [t, q, pullback.condition]
      rw [Sieve.overEquiv_iff, Presheaf.imageSieve_apply]
      exact ⟨t, hlift⟩
    exact J.superset_covering hle hRcov
  show Presheaf.IsLocallySurjective J (sheafifyMap J p)
  let PX := F.op ⋙ yoneda.obj X
  apply (Presheaf.comp_isLocallySurjective_iff J (toSheafify J PX) (sheafifyMap J p)).1
  rw [(toSheafify_naturality J p).symm]
  infer_instance

variable {S : Scheme.{u}} {R U U' : Over S}

/-- **Stacks 02WU.** Let `j` be an equivalence relation on `U` over `S` whose source and
target maps are surjective, flat and locally of finite presentation, and let `g : U' ⟶ U` be
flat and locally of finite presentation. Then the induced map of fppf quotient sheaves
`U'/R' ⟶ U/R` is representable by open immersions. -/
@[stacks 02WU]
theorem isOpenImmersion_restrictedQuotientMap
    (B : BigFppfSite.{u}) (hS : B.Contains S)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (j : PreRelation R U) (g : U' ⟶ U)
    [IsEquivalenceRelation j.target j.source]
    (hs_surj : Surjective j.source.left)
    (ht_surj : Surjective j.target.left)
    (hs_flat : Flat j.source.left)
    (ht_flat : Flat j.target.left)
    (hs_lfp : LocallyOfFinitePresentation j.source.left)
    (ht_lfp : LocallyOfFinitePresentation j.target.left)
    (hg_flat : Flat g.left)
    (hg_lfp : LocallyOfFinitePresentation g.left) :
    IsOpenImmersion B S hS
      (restrictQuotientSheafMap (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion) j g).hom := by
  classical
  let G := groupoidSchemeOfIsEquivalenceRelation j
  let hG := groupoidSchemeOfIsEquivalenceRelation_extendsRelation j
  obtain ⟨⟨_, _, _⟩, _, _, _⟩ :=
    endpoints_fppf j G hG hs_surj ht_surj hs_flat ht_flat hs_lfp ht_lfp
  let objIso : U ⟶ G.objects := eqToHom hG.objects_eq.symm
  have hobjIso : IsIso objIso.left := inferInstanceAs (IsIso ((Over.forget S).map objIso))
  let gg : U' ⟶ G.objects := g ≫ objIso
  have hggflat : Flat gg.left := by
    show Flat (g.left ≫ objIso.left)
    infer_instance
  have hgglfp : LocallyOfFinitePresentation gg.left := by
    show LocallyOfFinitePresentation (g.left ≫ objIso.left)
    infer_instance
  let q := GroupoidScheme.restrictionReachMap G gg
  obtain ⟨hqflat, hqlfp⟩ := restrictionReach_fppf G gg
  let W : G.objects.left.Opens := ⟨Set.range q.left.base, q.left.isOpenMap.isOpen_range⟩
  have hW : Set.range q.left.base ⊆ Set.range W.ι.base := by simp [W]
  have hWsurj : Set.range W.ι.base ⊆ Set.range q.left.base := by simp [W]
  let Wover : Over S := Over.mk (W.ι ≫ G.objects.hom)
  let i : Wover ⟶ G.objects := Over.homMk W.ι (by simp [Wover])
  have hi : AlgebraicGeometry.IsOpenImmersion i.left := by
    show AlgebraicGeometry.IsOpenImmersion W.ι
    infer_instance
  let kScheme := AlgebraicGeometry.IsOpenImmersion.lift W.ι q.left hW
  let k : pullback gg G.target ⟶ Wover := Over.homMk kScheme (by
    show kScheme ≫ (W.ι ≫ G.objects.hom) = (pullback gg G.target).hom
    rw [← Category.assoc,
      AlgebraicGeometry.IsOpenImmersion.lift_fac (f := W.ι) (g := q.left) hW]
    exact q.w)
  have hk : k ≫ i = q := by
    ext
    show kScheme ≫ W.ι = q.left
    exact AlgebraicGeometry.IsOpenImmersion.lift_fac (f := W.ι) (g := q.left) hW
  obtain ⟨_, _, _⟩ : Flat k.left ∧ LocallyOfFinitePresentation k.left ∧ Surjective k.left :=
    corestriction_fppf q.left W hW hWsurj
  let J := BigFppfOver.topology B S hS
  let F : BigFppfOver B S hS ⥤ Over S := Over.post (X := B.obj hS) B.inclusion
  have hlocal : Sheaf.IsLocallySurjective
      ((presheafToSheaf J (Type u)).map (F.op.whiskerLeft (yoneda.map k))) :=
    sheafified_fppf_map_locallySurjective B hS k
  have hrange : Set.range i.left.base = Set.range q.left.base := by
    show Set.range W.ι.base = Set.range q.left.base
    rw [Scheme.Opens.range_ι]
    rfl
  let jG := groupoidPreRelation G
  let r0 : R ⟶ G.arrows := eqToHom hG.arrows_eq.symm
  let r0Inv : G.arrows ⟶ R := eqToHom hG.arrows_eq
  let f0 : U ⟶ G.objects := objIso
  let f0Inv : G.objects ⟶ U := eqToHom hG.objects_eq
  have hr0 : r0 ≫ r0Inv = 𝟙 R := by simp [r0, r0Inv]
  have hr0Inv : r0Inv ≫ r0 = 𝟙 G.arrows := by simp [r0, r0Inv]
  have hf0 : f0 ≫ f0Inv = 𝟙 U := by simp [f0, f0Inv, objIso]
  have hf0Inv : f0Inv ≫ f0 = 𝟙 G.objects := by simp [f0, f0Inv, objIso]
  have h0s : r0 ≫ jG.source = j.source ≫ f0 := by
    simpa [jG, groupoidPreRelation, PreRelation.source] using
      (eqToHom_comp_comm hG.arrows_eq hG.objects_eq _ _ hG.source_eq).1
  have h0t : r0 ≫ jG.target = j.target ≫ f0 := by
    simpa [jG, groupoidPreRelation, PreRelation.target] using
      (eqToHom_comp_comm hG.arrows_eq hG.objects_eq _ _ hG.target_eq).1
  have h0sInv : r0Inv ≫ j.source = jG.source ≫ f0Inv := by
    simpa [jG, groupoidPreRelation, PreRelation.source] using
      (eqToHom_comp_comm hG.arrows_eq hG.objects_eq _ _ hG.source_eq).2
  have h0tInv : r0Inv ≫ j.target = jG.target ≫ f0Inv := by
    simpa [jG, groupoidPreRelation, PreRelation.target] using
      (eqToHom_comp_comm hG.arrows_eq hG.objects_eq _ _ hG.target_eq).2
  have h0rel : r0 ≫ jG = j ≫ prod.map f0 f0 := by
    apply prod.hom_ext
    · simpa [groupoidPreRelation, PreRelation.target] using h0t
    · simpa [groupoidPreRelation, PreRelation.source] using h0s
  have h0relInv : r0Inv ≫ j = jG ≫ prod.map f0Inv f0Inv := by
    apply prod.hom_ext
    · simpa [groupoidPreRelation, PreRelation.target] using h0tInv
    · simpa [groupoidPreRelation, PreRelation.source] using h0sInv
  let isoBase := quotientSheafMapIso J F jG j r0Inv f0Inv r0 f0
    h0sInv h0tInv h0s h0t hf0Inv hf0
  let jR := AlgebraicGeometry.PreRelation.restrict j g
  let jRG := AlgebraicGeometry.PreRelation.restrict jG gg
  let eR := restrictedRelationIso j jG g f0 r0 r0Inv f0Inv h0rel h0relInv hf0 hf0Inv hr0 hr0Inv
  have heRfst : eR.hom ≫ pullback.fst (prod.map gg gg) jG =
      pullback.fst (prod.map g g) j := by
    dsimp [eR, restrictedRelationIso]
    exact pullback.lift_fst _ _ _
  have heRfstInv : eR.inv ≫ pullback.fst (prod.map g g) j =
      pullback.fst (prod.map gg gg) jG := by
    dsimp [eR, restrictedRelationIso]
    exact pullback.lift_fst _ _ _
  have hsR : eR.hom ≫ jRG.source = jR.source ≫ 𝟙 U' := by
    simp [jRG, jR, PreRelation.restrict, PreRelation.source, reassoc_of% heRfst]
  have htR : eR.hom ≫ jRG.target = jR.target ≫ 𝟙 U' := by
    simp [jRG, jR, PreRelation.restrict, PreRelation.target, reassoc_of% heRfst]
  have hsRInv : eR.inv ≫ jR.source = jRG.source ≫ 𝟙 U' := by
    simp [jRG, jR, PreRelation.restrict, PreRelation.source, reassoc_of% heRfstInv]
  have htRInv : eR.inv ≫ jR.target = jRG.target ≫ 𝟙 U' := by
    simp [jRG, jR, PreRelation.restrict, PreRelation.target, reassoc_of% heRfstInv]
  let isoRest := quotientSheafMapIso J F jR jRG eR.hom (𝟙 U') eR.inv (𝟙 U')
    hsR htR hsRInv htRInv (by simp) (by simp)
  let qRel := restrictQuotientSheafMap J F jG gg
  let qActual := restrictQuotientSheafMap J F j g
  let H := GroupoidScheme.restrict G gg
  let qGroup := GroupoidScheme.restrictionQuotientMap J F G gg H
  let isoGroup := groupoidRestrictionQuotientIso J F G gg H
  let P := MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))
  have hGroup : P qGroup.hom :=
    GroupoidScheme.isOpenImmersion_restrictionQuotientMap_of_open_image B S hS G gg i k hk
      hrange hlocal
  have hfactor : qGroup.hom = isoGroup.hom.hom ≫ qRel.hom :=
    congrArg (fun x => x.hom) (restrictionQuotientMap_factor J F G gg H)
  have hRelFactor : qRel.hom = isoGroup.inv.hom ≫ qGroup.hom := by
    rw [hfactor, ← Category.assoc]
    simp
  have hqRel : P qRel.hom := by
    rw [hRelFactor]
    exact MorphismProperty.RespectsIso.precomp P isoGroup.inv.hom qGroup.hom hGroup
  have hfcomp : (𝟙 U' ≫ gg) ≫ f0Inv = g := by simp [gg, f0Inv, objIso]
  have hcompSheaf : isoRest.hom ≫ qRel ≫ isoBase.hom = qActual := by
    dsimp [isoRest, isoBase, quotientSheafMapIso, qRel, qActual, restrictQuotientSheafMap]
    change
      (quotientSheafMap J F jR jRG eR.hom (𝟙 U') hsR htR ≫
        quotientSheafMap J F jRG jG (pullback.snd (prod.map gg gg) jG) gg _ _) ≫
        quotientSheafMap J F jG j r0Inv f0Inv h0sInv h0tInv =
      quotientSheafMap J F jR j (pullback.snd (prod.map g g) j) g _ _
    rw [Category.assoc, quotientSheafMap_comp, quotientSheafMap_comp]
    exact quotientSheafMap_eq_of_obj_eq J F jR j
      ((eR.hom ≫ pullback.snd (prod.map gg gg) jG) ≫ r0Inv)
      (pullback.snd (prod.map g g) j)
      ((𝟙 U' ≫ gg) ≫ f0Inv) g _ _ _ _ hfcomp
  have hmap : isoRest.hom.hom ≫ qRel.hom ≫ isoBase.hom.hom = qActual.hom :=
    congrArg (fun x => x.hom) hcompSheaf
  show P qActual.hom
  rw [← hmap]
  exact MorphismProperty.RespectsIso.postcomp P isoBase.hom.hom _
    (MorphismProperty.RespectsIso.precomp P isoRest.hom.hom qRel.hom hqRel)

end AlgebraicGeometry.Space

end
