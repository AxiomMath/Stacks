module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.OverPullbackLeft
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.StandardCoverings
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible.Objects

/-!
# Flat, locally finitely presented restrictions of a relation of schemes

Restricting an equivalence relation of schemes along a flat, locally finitely presented
morphism keeps the fppf data of the relation: the source and target maps of the groupoid
extending it stay surjective, flat and locally of finite presentation, the map from the
restricted arrow scheme to the objects is flat and locally of finite presentation, and the
corestriction of a morphism to its open image is again flat, locally of finite presentation
and now surjective. On the big fppf site the functor of points of a flat, locally finitely
presented surjection is locally surjective after sheafification.

## Main results

* `AlgebraicGeometry.corestriction_flat_locallyOfFinitePresentation_surjective`: the
  corestriction of a flat, locally finitely presented morphism to an open subscheme carrying
  exactly its image.
* `AlgebraicGeometry.flat_locallyOfFinitePresentation_pullbackSnd_comp_source`: the map
  sending an arrow whose target lifts along `g` to its source is flat and locally of finite
  presentation.
* `AlgebraicGeometry.flat_locallyOfFinitePresentation_surjective_of_extendsRelation`: the
  endpoints of a groupoid extending a relation inherit the fppf properties of the relation.
* `AlgebraicGeometry.isLocallySurjective_presheafToSheaf_map_yoneda_map`: on the big fppf
  site over `S`, a flat, locally finitely presented surjection of `S`-schemes induces a
  locally surjective map of sheafified functors of points.

## Implementation notes

The slice category over `S` is handled through
`AlgebraicGeometry.overPullbackLeftIso`, the comparison of a pullback formed in the slice
with the pullback of the underlying morphisms of schemes; the forgetful functor preserves
pullbacks, so the two agree and every property of morphisms of schemes transfers.

Local surjectivity is proved on the presheaf level and then transported through
sheafification by `Stacks.WeaklyContractible.isLocallySurjective_presheafToSheaf_map`. Given a
point of the target over an object `A` of the site, its base change along the surjection is a
one-element flat, locally finitely presented covering of the underlying scheme of `A`, which
is refined by one of the site's chosen covering families
(`AlgebraicGeometry.exists_isCovering_refining_fppfCovering`); over each member of that
refinement the point lifts.

## References

* [Stacks Project, Tag 02WU](https://stacks.math.columbia.edu/tag/02WU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry

/-- A flat, locally finitely presented morphism corestricts to an open subscheme carrying
exactly its image, and the corestriction is again flat and locally of finite presentation,
and in addition surjective. -/
theorem corestriction_flat_locallyOfFinitePresentation_surjective {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] (W : Y.Opens)
    (hW : Set.range f.base ⊆ Set.range W.ι.base)
    (hWsurj : Set.range W.ι.base ⊆ Set.range f.base) :
    Flat (IsOpenImmersion.lift W.ι f hW) ∧
      LocallyOfFinitePresentation (IsOpenImmersion.lift W.ι f hW) ∧
      Surjective (IsOpenImmersion.lift W.ι f hW) := by
  let P : X.Opens := f ⁻¹ᵁ W
  have hP : P = ⊤ := by
    ext x
    refine ⟨fun _ ↦ by simp, fun _ ↦ ?_⟩
    rcases hW ⟨x, rfl⟩ with ⟨y, hy⟩
    change f x ∈ W
    rw [← hy]
    exact y.property
  let e : X ≅ P.toScheme := X.topIso.symm ≪≫ (X.isoOfEq hP).symm
  let q : P.toScheme ⟶ W.toScheme := f.resLE W P le_rfl
  let k : X ⟶ W.toScheme := IsOpenImmersion.lift W.ι f hW
  have hk : e.hom ≫ q = k := by
    apply (cancel_mono W.ι).1
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι (f := f) (U := W) (V := P) le_rfl,
      IsOpenImmersion.lift_fac (f := W.ι) (g := f) hW]
    simp [e, P]
  refine ⟨?_, ?_, ?_⟩
  · change Flat k
    rw [← hk]
    infer_instance
  · change LocallyOfFinitePresentation k
    rw [← hk]
    infer_instance
  · change Surjective k
    constructor
    intro y
    rcases hWsurj ⟨y, rfl⟩ with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply W.ι.isOpenEmbedding.injective
    change (k ≫ W.ι) x = W.ι y
    rw [IsOpenImmersion.lift_fac (f := W.ι) (g := f) hW]
    simpa using hx

/-- A morphism property stable under base change passes to the second projection of a pullback
in the slice over `S`. -/
private theorem property_left_pullback_snd {S : Scheme.{u}} (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {X Y Z : Over S} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hf : P f.left) : P (pullback.snd f g).left := by
  rw [← overPullbackLeftIso_hom_snd, P.cancel_left_of_respectsIso]
  exact P.pullback_snd _ _ hf

/-- If `g` is, up to isomorphisms on both sides, a surjective, flat and locally finitely
presented morphism `g'`, then so is `g`. -/
private theorem surjective_flat_locallyOfFinitePresentation_of_comp_eq {X Y Z W : Scheme.{u}}
    (r : X ⟶ Y) (g : Y ⟶ Z) (g' : X ⟶ W) (f : W ⟶ Z) [IsIso r] [IsIso f]
    (h : r ≫ g = g' ≫ f) [Surjective g'] [Flat g'] [LocallyOfFinitePresentation g'] :
    Surjective g ∧ Flat g ∧ LocallyOfFinitePresentation g := by
  have : Surjective (r ≫ g) := by rw [h]; infer_instance
  have : Flat (r ≫ g) := by rw [h]; infer_instance
  have : LocallyOfFinitePresentation (r ≫ g) := by rw [h]; infer_instance
  have e : g = inv r ≫ r ≫ g := by simp
  refine ⟨Surjective.of_comp (f := r) (g := g), ?_, ?_⟩ <;> rw [e] <;> infer_instance

/-- The map sending an arrow of a groupoid scheme whose target lifts along `g` to its source
is flat and locally of finite presentation as soon as `g` and the source map of the groupoid
are. -/
theorem flat_locallyOfFinitePresentation_pullbackSnd_comp_source {S : Scheme.{u}}
    {U' : Over S} (G : Stacks.Groupoids.GroupoidScheme S) (g : U' ⟶ G.objects)
    [Flat g.left] [LocallyOfFinitePresentation g.left]
    [Flat G.source.left] [LocallyOfFinitePresentation G.source.left] :
    Flat (pullback.snd g G.target ≫ G.source).left ∧
      LocallyOfFinitePresentation (pullback.snd g G.target ≫ G.source).left := by
  have : Flat (pullback.snd g G.target).left :=
    property_left_pullback_snd @Flat g G.target inferInstance
  have : LocallyOfFinitePresentation (pullback.snd g G.target).left :=
    property_left_pullback_snd @LocallyOfFinitePresentation g G.target inferInstance
  refine ⟨?_, ?_⟩
  · change Flat ((pullback.snd g G.target).left ≫ G.source.left)
    infer_instance
  · change LocallyOfFinitePresentation ((pullback.snd g G.target).left ≫ G.source.left)
    exact locallyOfFinitePresentation_comp _ _

/-- A groupoid scheme extending a pre-relation whose source and target maps are surjective,
flat and locally of finite presentation has source and target maps with the same three
properties. -/
theorem flat_locallyOfFinitePresentation_surjective_of_extendsRelation {S : Scheme.{u}}
    {R U : Over S} (j : Stacks.Groupoids.PreRelation R U)
    (G : Stacks.Groupoids.GroupoidScheme S) (h : ExtendsRelation j G)
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
  have : IsIso r.left := by
    simpa only [CategoryTheory.Over.forget_map] using
      (show IsIso ((CategoryTheory.Over.forget S).map r) from inferInstance)
  have : IsIso f.left := by
    simpa only [CategoryTheory.Over.forget_map] using
      (show IsIso ((CategoryTheory.Over.forget S).map f) from inferInstance)
  have hs : r ≫ G.source = j.source ≫ f := by
    simpa [r, f, Category.assoc] using
      congrArg (fun q : R ⟶ U ↦ q ≫ f) h.source_eq
  have ht : r ≫ G.target = j.target ≫ f := by
    simpa [r, f, Category.assoc] using
      congrArg (fun q : R ⟶ U ↦ q ≫ f) h.target_eq
  have hs' : r.left ≫ G.source.left = j.source.left ≫ f.left := by
    simpa using congrArg CategoryTheory.Over.Hom.left hs
  have ht' : r.left ≫ G.target.left = j.target.left ≫ f.left := by
    simpa using congrArg CategoryTheory.Over.Hom.left ht
  exact ⟨surjective_flat_locallyOfFinitePresentation_of_comp_eq _ _ _ _ hs',
    surjective_flat_locallyOfFinitePresentation_of_comp_eq _ _ _ _ ht'⟩

/-- A flat, locally finitely presented surjection of `S`-schemes induces a locally surjective
map of the sheafified functors of points on the big fppf site over `S`. -/
theorem isLocallySurjective_presheafToSheaf_map_yoneda_map {S : Scheme.{u}}
    (B : BigFppfSite.{u}) (hS : B.Contains S)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)] {X Y : CategoryTheory.Over S}
    (k : X ⟶ Y) [Flat k.left] [LocallyOfFinitePresentation k.left] [Surjective k.left] :
    Sheaf.IsLocallySurjective
      ((presheafToSheaf (BigFppfOver.topology B S hS) (Type u)).map
        ((CategoryTheory.Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft
          (yoneda.map k))) := by
  classical
  let C := BigFppfOver B S hS
  let J := BigFppfOver.topology B S hS
  let F : C ⥤ CategoryTheory.Over S := CategoryTheory.Over.post (X := B.obj hS) B.inclusion
  let p := F.op.whiskerLeft (yoneda.map k)
  have hp : Presheaf.IsLocallySurjective J p := by
    refine ⟨?_⟩
    intro A s
    let f : F.obj A ⟶ Y := s
    let P := pullback k f
    let q := pullback.snd k f
    have hq : Flat q.left ∧ LocallyOfFinitePresentation q.left ∧ Surjective q.left :=
      ⟨property_left_pullback_snd @Flat k f inferInstance,
        property_left_pullback_snd @LocallyOfFinitePresentation k f inferInstance,
        property_left_pullback_snd @Surjective k f inferInstance⟩
    let E : PreZeroHypercover.{u + 1} (B.inclusion.obj A.left) :=
      PreZeroHypercover.singleton q.left
    have hE : E.presieve₀ ∈ Scheme.fppfPrecoverage (B.inclusion.obj A.left) := by
      change E.presieve₀ ∈ Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)
        (B.inclusion.obj A.left)
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨?_, ?_⟩
      · intro y
        obtain ⟨x, hx⟩ := hq.2.2.surj y
        exact ⟨PUnit.unit, x, hx⟩
      · intro i
        exact ⟨hq.1, hq.2.1⟩
    obtain ⟨V, hV, href⟩ := exists_isCovering_refining_fppfCovering B A.left E hE
    rcases href with ⟨ref⟩
    have hRcov : (Sieve.overEquiv A).symm V.sieve₀ ∈ J A := by
      rw [GrothendieckTopology.mem_over_iff]
      simpa [PreZeroHypercover.sieve₀, Sieve.ofArrows] using
        (Precoverage.generate_mem_toGrothendieck
          (show V.presieve₀ ∈ B.precoverage A.left from ⟨V, rfl, hV⟩))
    have hle : (Sieve.overEquiv A).symm V.sieve₀ ≤ Presheaf.imageSieve p s := by
      rw [← ((Sieve.overEquiv A).symm).apply_symm_apply (Presheaf.imageSieve p s)]
      rw [((Sieve.overEquiv A).symm).map_rel_iff]
      simp only [OrderIso.symm_symm]
      rw [PreZeroHypercover.sieve₀, Sieve.ofArrows, Sieve.generate_le_iff,
        Presieve.ofArrows_le_iff]
      intro i
      let W : C := CategoryTheory.Over.mk (V.f i ≫ A.hom)
      let α : W ⟶ A := CategoryTheory.Over.homMk (V.f i) (by simp [W])
      let b : (B.inclusion.obj W.left) ⟶ P.left := ref.h₀ i
      have hbp : b ≫ q.left = B.inclusion.map (V.f i) := ref.w₀ i
      have hbeta : b ≫ P.hom = (F.obj W).hom := by
        rw [← CategoryTheory.Over.w q]
        change (b ≫ q.left) ≫ (F.obj A).hom = (F.obj W).hom
        rw [hbp]
        change B.inclusion.map (V.f i) ≫ B.inclusion.map A.hom =
          B.inclusion.map (V.f i ≫ A.hom)
        exact (B.inclusion.map_comp _ _).symm
      let β : F.obj W ⟶ P := CategoryTheory.Over.homMk b hbeta
      have hfactor : β ≫ q = F.map α := by
        ext
        change b ≫ q.left = B.inclusion.map (V.f i)
        exact hbp
      let t : F.obj W ⟶ X := β ≫ pullback.fst k f
      have hlift : p.app (op W) t = (F.op ⋙ yoneda.obj Y).map α.op s := by
        change t ≫ k = F.map α ≫ f
        calc
          t ≫ k = β ≫ (pullback.fst k f ≫ k) := by simp [t, Category.assoc]
          _ = β ≫ (q ≫ f) := by rw [pullback.condition]
          _ = (β ≫ q) ≫ f := by simp [Category.assoc]
          _ = F.map α ≫ f := by rw [hfactor]
      rw [Sieve.overEquiv_iff, Presheaf.imageSieve_apply]
      exact ⟨t, hlift⟩
    exact J.superset_covering hle hRcov
  have : Presheaf.IsLocallySurjective J p := hp
  exact Stacks.WeaklyContractible.isLocallySurjective_presheafToSheaf_map J p

end AlgebraicGeometry

end
