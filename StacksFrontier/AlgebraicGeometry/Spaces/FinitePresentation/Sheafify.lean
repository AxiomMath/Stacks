module

public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreserving
public import StacksFrontier.AlgebraicGeometry.Sites.LocallySurjectiveUnivLE
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.StandardCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Vtopology.CoveringExistence
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposMorphismDefs

/-!
# Limit preservation under fppf sheafification

The fppf sheaf associated to a limit-preserving presheaf of sets on the big fppf site over
a scheme is again limit preserving. Concretely, a section of the sheafification over a
cofiltered affine limit comes from a section at some finite stage, and two sections at a
stage that agree at the limit already agree at some later stage.

## Main results

* `AlgebraicGeometry.limitPreserving_of_isLocallyBijective`: an fppf sheaf receiving a
  locally bijective map from a limit-preserving presheaf of sets is limit preserving.
* `AlgebraicGeometry.limitPreserving_sheafify`: fppf sheafification preserves limit
  preservation for presheaves of sets.

## Implementation notes

The two halves of the colimit recognition are extracted as separate hypotheses on the
comparison map to the sheafification: local injectivity gives the eventual equality of
sections, and local surjectivity gives their existence at a finite stage. Both halves rest
on refining an arbitrary covering of an affine object to a finite affine one and descending
that refinement along the limit cone, which is the content of
`AlgebraicGeometry.Space.exists_covering_refining_sieve` together with the descent of
standard fppf coverings from `AlgebraicGeometry.exists_standardFppfCovering_of_isLimit`.

The universes of the tested index objects and morphisms are bounded by the scheme universe:
this expresses the ambient set-sized limits in the source, and limits in a smaller category
of schemes do not suffice for covering descent. The universe of sets is at least the object
universe of the chosen big fppf site, where sheafification is available.

## References

* [Stacks Project, Tag 049O](https://stacks.math.columbia.edu/tag/049O)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w w' z z'

namespace AlgebraicGeometry

/-- For a limit-preserving presheaf, two sections at a stage of a cofiltered system of
affines that agree at the limit already agree at some earlier stage. -/
theorem eventually_eq_of_limitPreserving
    {C : Type z} [Category C] (toScheme : C ⥤ Scheme.{u})
    (F : Cᵒᵖ ⥤ Type v)
    (hF : LimitPreserving.{u, v, w, w', z} toScheme F)
    {I : Type (max w w')} [Category.{w'} I] [IsCofiltered I]
    (D : I ⥤ C) (c : Cone D) (hc : IsLimit (toScheme.mapCone c))
    (hD : ∀ i, IsAffine (toScheme.obj (D.obj i)))
    (hC : IsAffine (toScheme.obj c.pt)) (i : I)
    (x y : F.obj (Opposite.op (D.obj i)))
    (hxy : F.map (c.π.app i).op x = F.map (c.π.app i).op y) :
    ∃ (j : I) (f : j ⟶ i), F.map (D.map f).op x = F.map (D.map f).op y := by
  obtain ⟨h⟩ := hF I D c hc hD hC
  obtain ⟨j, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' h x y).mp hxy
  exact ⟨j.unop, f.unop, hf⟩

/-- A presheaf sends the opposite of a cofiltered cone to a colimit cocone as soon as every
section at the apex comes from a stage and sections agreeing at the apex eventually agree. -/
theorem isColimit_mapCocone_of_exists_of_eventually_eq
    {C : Type z} [Category C] {I : Type w} [Category.{w'} I] [IsCofiltered I]
    (F : Cᵒᵖ ⥤ Type v) (D : I ⥤ C) (c : Cone D)
    (hsurj : ∀ x : F.obj (Opposite.op c.pt),
      ∃ (i : I) (y : F.obj (Opposite.op (D.obj i))), F.map (c.π.app i).op y = x)
    (hinj : ∀ (i : I) (x y : F.obj (Opposite.op (D.obj i))),
      F.map (c.π.app i).op x = F.map (c.π.app i).op y →
      ∃ (j : I) (f : j ⟶ i), F.map (D.map f).op x = F.map (D.map f).op y) :
    Nonempty (IsColimit (F.mapCocone c.op)) := by
  refine ⟨Types.FilteredColimit.isColimitOf' (D.op ⋙ F) (F.mapCocone c.op) ?_ ?_⟩
  · intro x
    obtain ⟨i, y, hy⟩ := hsurj x
    exact ⟨Opposite.op i, y, hy.symm⟩
  · intro i x y hxy
    obtain ⟨j, f, hf⟩ := hinj i.unop x y hxy
    exact ⟨Opposite.op j, f.op, hf⟩

/-- A finite family of morphisms to a common object in a cofiltered category admits a common
refinement: one object mapping compatibly to all of them and to the target. The name avoids
`AlgebraicGeometry.exists_common_refinement`, which is the refinement of étale
neighbourhoods of a point. -/
theorem exists_cofiltered_common_refinement
    {I : Type w} [Category.{w'} I] [IsCofiltered I]
    {K : Type z} [Finite K] (i : I) (j : K → I) (f : ∀ k, j k ⟶ i) :
    ∃ (l : I) (g : l ⟶ i) (h : ∀ k, l ⟶ j k), ∀ k, h k ≫ f k = g := by
  classical
  let := Fintype.ofFinite K
  let O : Finset I := insert i (Finset.univ.image j)
  have hi : i ∈ O := Finset.mem_insert_self _ _
  have hj (k : K) : j k ∈ O := by simp [O]
  let H : Finset (Σ' (X Y : I) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) :=
    Finset.univ.image (fun k : K ↦ ⟨j k, i, hj k, hi, f k⟩)
  exact ⟨IsCofiltered.inf O H, IsCofiltered.infTo O H hi,
    fun k ↦ IsCofiltered.infTo O H (hj k), fun k ↦
      IsCofiltered.infTo_commutes O H (hj k) hi
        (Finset.mem_image_of_mem _ (Finset.mem_univ k))⟩

/-- A finite family of elements, one in each of finitely many filtered colimits over the same
indexing category, is jointly represented at a single stage. -/
theorem jointly_surjective_of_isColimit_finite
    {I : Type w} [Category.{w'} I] [IsFiltered I]
    {K : Type z} [Finite K] (F : K → I ⥤ Type v)
    (c : ∀ k, Cocone (F k)) (hc : ∀ k, IsColimit (c k))
    (x : ∀ k, (c k).pt) :
    ∃ (i : I) (y : ∀ k, (F k).obj i), ∀ k, (c k).ι.app i (y k) = x k := by
  classical
  let := Fintype.ofFinite K
  choose i y hy using fun k ↦ Types.jointly_surjective_of_isColimit (hc k) (x k)
  obtain ⟨j, hj⟩ := IsFiltered.sup_objs_exists (Finset.univ.image i)
  let f (k : K) : i k ⟶ j := (hj (Finset.mem_image_of_mem i (Finset.mem_univ k))).some
  refine ⟨j, fun k ↦ (F k).map (f k) (y k), fun k ↦ ?_⟩
  exact (ConcreteCategory.congr_hom ((c k).w (f k)) (y k)).trans (hy k)


/-- Base change along a morphism turns a morphism of objects over its target into a cartesian
square of the two base-changed objects. -/
theorem isPullback_pullback_map
    {C : Type z} [Category.{w} C] [HasPullbacks C]
    {X Y : C} (f : X ⟶ Y) {A B : Over Y} (g : A ⟶ B) :
    IsPullback ((Over.pullback f).map g).left
      (pullback.fst A.hom f) (pullback.fst B.hom f) g.left := by
  apply IsPullback.of_right (h₁₂ := pullback.snd B.hom f) (h₂₂ := B.hom) (v₁₃ := f)
  · simpa [Over.pullback, pullback.lift_snd, Over.w g] using
      (IsPullback.of_hasPullback A.hom f).flip
  · simp [Over.pullback]
  · exact (IsPullback.of_hasPullback B.hom f).flip

/-- Base changing a cofiltered limit cone of objects over a stage along a morphism to that
stage again gives a limit cone, computed after passing to schemes. -/
@[no_expose]
noncomputable def isLimit_mapCone_pullback_overPost
    {C : Type z} [Category.{v} C] [HasPullbacks C]
    (T : C ⥤ Scheme.{u}) [PreservesLimitsOfShape WalkingCospan T]
    {I : Type w} [Category.{w'} I] [IsCofiltered I]
    (D : I ⥤ C) (c : Cone D) (hc : IsLimit (T.mapCone c))
    (i : I) {X : C} (f : X ⟶ D.obj i) :
    IsLimit (T.mapCone ((Over.forget X).mapCone
      ((Over.pullback f).mapCone (c.overPost i)))) := by
  letI : IsConnected (Over i) := IsCofiltered.isConnected (Over i)
  let E : Over i ⥤ C := Over.post D ⋙ Over.pullback f ⋙ Over.forget X
  let cb : Cone E := (Over.forget X).mapCone ((Over.pullback f).mapCone (c.overPost i))
  let α : E ⟶ Over.forget i ⋙ D :=
    { app := fun j ↦ pullback.fst (D.map j.hom) f
      naturality := by
        intro j k g
        dsimp [E, Over.pullback]
        exact pullback.lift_fst _ _ _ }
  let p : (Cone.postcompose α).obj cb ⟶ c.whisker (Over.forget i) :=
    { hom := pullback.fst (c.π.app i) f
      w := by
        intro j
        dsimp [cb, α, Over.pullback, Cone.overPost]
        exact (pullback.lift_fst _ _ _).symm }
  have hp (j : Over i) :
      IsPullback (cb.π.app j) p.hom (α.app j) (c.π.app j.left) :=
    isPullback_pullback_map f ((c.overPost i).π.app j)
  let q : (Cone.postcompose (Functor.whiskerRight α T)).obj (T.mapCone cb) ⟶
      (T.mapCone c).whisker (Over.forget i) :=
    { hom := T.map p.hom
      w := by intro j; simpa using congrArg T.map (p.w j) }
  exact isLimitOfIsPullbackOfIsConnected (Functor.whiskerRight α T)
    (T.mapCone cb) ((T.mapCone c).whisker (Over.forget i)) q
    (fun j ↦ (hp j).map T)
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) (T.mapCone c)).symm hc)

/-- A fibre product of affine objects over an affine one is affine, for a functor to schemes
that preserves pullbacks. -/
theorem isAffine_obj_pullback
    {C : Type z} [Category.{z'} C] [HasPullbacks C]
    (T : C ⥤ Scheme.{u}) [PreservesLimitsOfShape WalkingCospan T]
    {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsAffine (T.obj X)] [IsAffine (T.obj Y)] [IsAffine (T.obj Z)] :
    IsAffine (T.obj (pullback f g)) :=
  .of_isIso (PreservesPullback.iso T f g).hom

/-- A limit-preserving presheaf sends the base change of a cofiltered limit cone along an
affine morphism to a colimit cocone. -/
theorem isColimit_pullback_overPost_of_limitPreserving
    {C : Type z} [Category.{z'} C] [HasPullbacks C]
    (T : C ⥤ Scheme.{u}) [PreservesLimitsOfShape WalkingCospan T]
    (F : Cᵒᵖ ⥤ Type v)
    (hF : LimitPreserving.{u, v, w, w', z} T F)
    {I : Type (max w w')} [Category.{w'} I] [IsCofiltered I]
    (D : I ⥤ C) (c : Cone D) (hc : IsLimit (T.mapCone c))
    (hD : ∀ i, IsAffine (T.obj (D.obj i))) (hC : IsAffine (T.obj c.pt))
    (i : I) {X : C} (f : X ⟶ D.obj i) (hX : IsAffine (T.obj X)) :
    Nonempty (IsColimit (F.mapCocone
      ((Over.forget X).mapCone ((Over.pullback f).mapCone (c.overPost i))).op)) := by
  let : ∀ i, IsAffine (T.obj (D.obj i)) := hD
  let : IsAffine (T.obj c.pt) := hC
  let : IsAffine (T.obj X) := hX
  exact hF (Over i) (Over.post D ⋙ Over.pullback f ⋙ Over.forget X)
    ((Over.forget X).mapCone ((Over.pullback f).mapCone (c.overPost i)))
    (isLimit_mapCone_pullback_overPost T D c hc i f)
    (fun j ↦ isAffine_obj_pullback T (D.map j.hom) f)
    (isAffine_obj_pullback T (show c.pt ⟶ D.obj i from c.π.app i) f)

/-- For a limit-preserving presheaf, a finite family of sections over the base changes of the
limit is defined at a single common stage. -/
theorem exists_sections_pullback_of_limitPreserving
    {C : Type z} [Category.{z'} C] [HasPullbacks C]
    (T : C ⥤ Scheme.{u}) [PreservesLimitsOfShape WalkingCospan T]
    (F : Cᵒᵖ ⥤ Type v)
    (hF : LimitPreserving.{u, v, w, w', z} T F)
    {I : Type (max w w')} [Category.{w'} I] [IsCofiltered I]
    (D : I ⥤ C) (c : Cone D) (hc : IsLimit (T.mapCone c))
    (hD : ∀ i, IsAffine (T.obj (D.obj i))) (hC : IsAffine (T.obj c.pt))
    (i : I) {K : Type*} [Finite K] (X : K → C)
    (f : ∀ k, X k ⟶ D.obj i) (hX : ∀ k, IsAffine (T.obj (X k)))
    (x : ∀ k, F.obj (Opposite.op (pullback (c.π.app i) (f k)))) :
    ∃ (j : Over i) (y : ∀ k, F.obj (Opposite.op (pullback (D.map j.hom) (f k)))),
      ∀ k, F.map (((Over.pullback (f k)).map ((c.overPost i).π.app j)).left.op)
        (y k) = x k := by
  classical
  let H (k : K) := (Over.post D ⋙ Over.pullback (f k) ⋙ Over.forget (X k)).op ⋙ F
  let cc (k : K) : Cocone (H k) := F.mapCocone
    ((Over.forget (X k)).mapCone ((Over.pullback (f k)).mapCone (c.overPost i))).op
  have hcc (k : K) : Nonempty (IsColimit (cc k)) :=
    isColimit_pullback_overPost_of_limitPreserving T F hF D c hc hD hC i (f k) (hX k)
  obtain ⟨j, y, hy⟩ := jointly_surjective_of_isColimit_finite H cc
    (fun k ↦ (hcc k).some) x
  exact ⟨j.unop, y, hy⟩






/-- Every covering sieve of an affine object of a big fppf site is refined by a chosen
covering family which is a standard fppf covering. -/
private theorem exists_standardFppf_refinement_local (B : BigFppfSite.{u})
    {T : B.Schemes} [IsAffine (B.inclusion.obj T)] {R : Sieve T}
    (hR : R ∈ B.topology T) :
    ∃ Q : PreZeroHypercover T,
      B.IsCovering ⟨T, Q⟩ ∧
      IsStandardFppfCovering
        (fun i ↦ B.inclusion.obj (Q.X i)) (fun i ↦ B.inclusion.map (Q.f i)) ∧
      Q.presieve₀ ≤ R := by
  classical
  obtain ⟨E, hE, hER⟩ := AlgebraicGeometry.Space.exists_covering_refining_sieve B hR
  have hEfp : IsFppfCovering ⟨T, E⟩ :=
    B.isFppfCovering_of_isCovering hE
  let T₀ : Scheme := T.obj
  have hEfp' : (E.map B.inclusion).presieve₀ ∈ Scheme.fppfPrecoverage T₀ := by
    simpa [IsFppfCovering, Scheme.fppfPrecoverage,
      PreZeroHypercover.presieve₀_map, T₀] using hEfp
  let U : T₀.Cover Scheme.fppfPrecoverage :=
    ⟨E.map B.inclusion, hEfp'⟩
  have hUfp := (Scheme.presieve₀_mem_precoverage_iff U.toPreZeroHypercover).mp U.mem₀
  let : Scheme.JointlySurjective Scheme.fppfPrecoverage := by
    change Scheme.JointlySurjective (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation))
    infer_instance
  let : MorphismProperty.IsStableUnderComposition
      (@Flat ⊓ @LocallyOfFinitePresentation) :=
    ⟨fun f g hf hg ↦ ⟨MorphismProperty.comp_mem (@Flat) f g hf.1 hg.1,
      MorphismProperty.comp_mem (@LocallyOfFinitePresentation) f g hf.2 hg.2⟩⟩
  let : MorphismProperty.RespectsLeft
      (@Flat ⊓ @LocallyOfFinitePresentation) @IsOpenImmersion :=
    ⟨fun i _ f hf ↦ MorphismProperty.comp_mem (@Flat ⊓ @LocallyOfFinitePresentation) i f
      (by constructor <;> infer_instance) hf⟩
  let : QuasiCompactCover U.toPreZeroHypercover := by
    apply QuasiCompactCover.of_isOpenMap
    intro i
    have hf := hUfp.2 i
    let : Flat (U.f i) := hf.1
    let : LocallyOfFinitePresentation (U.f i) := hf.2
    exact Scheme.Hom.isOpenMap (U.f i)
  let : IsAffine T₀ := by
    change IsAffine (B.inclusion.obj T)
    infer_instance
  let : CompactSpace (Spec Γ(T₀, ⊤)) := inferInstance
  let : CompactSpace T₀ :=
    @Homeomorph.compactSpace _ _ _ _ (inferInstance : CompactSpace (Spec Γ(T₀, ⊤)))
      (TopCat.homeoOfIso (asIso T₀.isoSpec.inv.base))
  obtain ⟨V, φ, hVfinite, hφopen⟩ := QuasiCompactCover.exists_hom U
  let P := V.cover.toPreZeroHypercover
  let : Finite P.I₀ := hVfinite
  let hPaff : ∀ i, IsAffine (P.X i) := by
    intro i
    change IsAffine (Spec (V.X i))
    exact isAffine_Spec _
  have hPstandard : IsStandardFppfCovering P.X P.f := by
    refine ⟨hVfinite, inferInstance, hPaff, ?_, ?_, ?_⟩
    · exact fun i ↦ (V.map_prop i).1
    · intro i
      let : IsAffine (P.X i) := hPaff i
      refine ⟨(V.map_prop i).2, ?_, ?_⟩ <;> infer_instance
    · exact Set.eq_univ_iff_forall.mpr fun x ↦
        Set.mem_iUnion.mpr (((Scheme.presieve₀_mem_precoverage_iff P).mp V.cover.mem₀).1 x)
  obtain ⟨W, hW, hWP⟩ :=
    exists_isCovering_tautologicallyEquivalent_standardFppfCovering
      B T P V.cover.mem₀ hPstandard
  rcases hWP with ⟨⟨α, hα⟩, ⟨β, hβ⟩⟩
  let α' : P.I₀ → W.I₀ := fun i ↦ α i
  let β' : W.I₀ → P.I₀ := fun i ↦ β i
  have hα' (i : P.I₀) :
      ∃ e : P.X i ≅ B.inclusion.obj (W.X (α' i)),
        e.hom ≫ B.inclusion.map (W.f (α' i)) = P.f i := by
    simpa [α', PreZeroHypercover.map] using hα i
  have hβ' (i : W.I₀) :
      ∃ e : B.inclusion.obj (W.X i) ≅ P.X (β' i),
        e.hom ≫ P.f (β' i) = B.inclusion.map (W.f i) := by
    simpa [β', PreZeroHypercover.map] using hβ i
  let I := Set.range α'
  let : Finite I := Finite.of_surjective (fun i : P.I₀ ↦ (⟨α' i, ⟨i, rfl⟩⟩ : I))
    fun i ↦ ⟨i.2.choose, Subtype.ext i.2.choose_spec⟩
  let Q : PreZeroHypercover T :=
    { I₀ := I
      X := fun i ↦ W.X i.1
      f := fun i ↦ W.f i.1 }
  have hQaff : ∀ i, IsAffine (B.inclusion.obj (Q.X i)) := by
    intro i
    obtain ⟨e, _⟩ := hβ' i.1
    let : IsAffine (P.X (β' i.1)) := hPaff _
    exact .of_isIso e.hom
  have hWprops := (Scheme.presieve₀_mem_precoverage_iff
      (W.map B.inclusion)).mp (by
        simpa [IsFppfCovering, Scheme.fppfPrecoverage,
          PreZeroHypercover.presieve₀_map] using B.isFppfCovering_of_isCovering hW)
  have hQstandard : IsStandardFppfCovering
      (fun i ↦ B.inclusion.obj (Q.X i)) (fun i ↦ B.inclusion.map (Q.f i)) := by
    refine IsStandardFppfCovering.mk inferInstance inferInstance hQaff ?_ ?_ ?_
    · exact fun i ↦ (hWprops.2 i.1).1
    · intro i
      let : IsAffine (B.inclusion.obj (Q.X i)) := hQaff i
      refine ⟨(hWprops.2 i.1).2, ?_, ?_⟩ <;> infer_instance
    · apply Set.eq_univ_iff_forall.mpr
      intro x
      obtain ⟨i, y, hy⟩ :=
        ((Scheme.presieve₀_mem_precoverage_iff P).mp V.cover.mem₀).1 x
      obtain ⟨e, he⟩ := hα' i
      let j : I := ⟨α' i, ⟨i, rfl⟩⟩
      refine Set.mem_iUnion.mpr ⟨j, Set.mem_range.mpr ⟨e.hom y, ?_⟩⟩
      change (B.inclusion.map (W.f j.1)) (e.hom y) = x
      rw [← Scheme.Hom.comp_apply, he]
      exact hy
  have hQfp : IsFppfCovering ⟨T, Q⟩ := by
    simpa [IsFppfCovering, Scheme.fppfPrecoverage,
      PreZeroHypercover.presieve₀_map] using
      (Scheme.presieve₀_mem_precoverage_iff (Q.map B.inclusion)).2
        ⟨fun x ↦ Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp hQstandard.jointly_surjective x),
          fun i ↦ ⟨hQstandard.flat i, (hQstandard.finite_presentation i).1⟩⟩
  have hQcard : Cardinal.mk Q.I₀ ≤ B.coveringBound :=
    (Cardinal.mk_le_of_injective (f := fun i : Q.I₀ => (i.1 : W.I₀))
      Subtype.val_injective).trans hW.2
  have hQcover : B.IsCovering ⟨T, Q⟩ := ⟨hQfp, hQcard⟩
  have hQle : Q.presieve₀ ≤ R := by
    rw [Presieve.ofArrows_le_iff]
    intro i
    obtain ⟨e, he⟩ := hβ' i.1
    let k := β' i.1
    let gB : Q.X i ⟶ E.X (φ.s₀ k) :=
      B.inclusion.preimage (e.hom ≫ φ.h₀ k)
    have hmapg : B.inclusion.map gB = e.hom ≫ φ.h₀ k := B.inclusion.map_preimage _
    have hφ' : φ.h₀ k ≫ B.inclusion.map (E.f (φ.s₀ k)) = P.f k := φ.w₀ k
    have hEq : gB ≫ E.f (φ.s₀ k) = Q.f i := B.inclusion.map_injective (by
      rw [Functor.map_comp, hmapg]
      exact (Category.assoc _ _ _).trans ((congrArg (e.hom ≫ ·) hφ').trans he))
    rw [← hEq]
    exact R.downward_closed (hER _ _ ⟨φ.s₀ k⟩) gB
  exact ⟨Q, hQcover, hQstandard, hQle⟩


/-- Every covering of an affine object of the big fppf site over `S` is refined by a chosen
standard fppf covering of its underlying scheme. -/
private theorem exists_standard_refinement_over
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj X)]
    (U : (BigFppfOver.topology B S hS).Cover X) :
    ∃ (V : PreZeroHypercover.{u + 1} X.left),
      B.IsCovering ⟨X.left, V⟩ ∧
      IsStandardFppfCovering
        (fun i => B.inclusion.obj (V.X i))
        (fun i => B.inclusion.map (V.f i)) ∧
    ∀ i : V.I₀,
        U (Over.homMk (V.f i) : Over.mk (V.f i ≫ X.hom) ⟶ X) := by
  let : IsAffine (B.inclusion.obj X.left) := by
    change IsAffine ((BigFppfOver.toScheme B S hS).obj X)
    infer_instance
  have hU : (Sieve.overEquiv X) U.1 ∈ B.topology X.left :=
    (CategoryTheory.GrothendieckTopology.mem_over_iff _ U.1).mp U.2
  obtain ⟨V, hV, hVstd, hVU⟩ :=
    exists_standardFppf_refinement_local B hU
  exact ⟨V, hV, hVstd, fun i ↦ (Sieve.overEquiv_iff U.1 (V.f i)).mp (hVU _ _ ⟨i⟩)⟩



/-- A covering of the limit of a cofiltered system of affine objects is refined by the base
change of a standard fppf covering defined at one of the stages. -/
private theorem exists_descended_standard_refinement_over
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type w} [Category.{w'} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ BigFppfOver B S hS)
    (c : Cone D)
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (hDi : ∀ i, IsAffine
      ((BigFppfOver.toScheme B S hS).obj (D.obj i)))
    (hC : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt))
    (U : (BigFppfOver.topology B S hS).Cover c.pt) :
    ∃ (Q : PreZeroHypercover.{u + 1} c.pt.left)
      (i : I) (Uᵢ : Q.I₀ → Scheme.{u}) (fᵢ : ∀ j, Uᵢ j ⟶
        (BigFppfOver.toScheme B S hS).obj (D.obj i)),
      IsStandardFppfCovering Uᵢ fᵢ ∧
      B.IsCovering ⟨c.pt.left, Q⟩ ∧
      (∀ j : Q.I₀,
        Nonempty ((Over.pullback
          ((BigFppfOver.toScheme B S hS).map (c.π.app i))).obj
            (Over.mk (fᵢ j)) ≅
          Over.mk (B.inclusion.map (Q.f j)))) ∧
      (∀ j : Q.I₀,
        U (Over.homMk (Q.f j) :
          Over.mk (Q.f j ≫ c.pt.hom) ⟶ c.pt)) := by
  obtain ⟨Q, hQ, hQstd, hQU⟩ := exists_standard_refinement_over B S hS c.pt U
  let : IsAffine ((BigFppfOver.toScheme B S hS).mapCone c).pt := hC
  let : ∀ i, IsAffine
      ((BigFppfOver.toScheme B S hS).obj (D.obj i)) := hDi
  let : Finite Q.I₀ := hQstd.finite_index
  let : ∀ i, IsAffine
      ((D ⋙ BigFppfOver.toScheme B S hS).obj i) := fun i => hDi i
  let e : I ≌ SmallModel.{u} I := equivSmallModel I
  let : IsCofiltered (SmallModel.{u} I) := IsCofiltered.of_equivalence e
  let Ds := e.inverse ⋙ D ⋙ BigFppfOver.toScheme B S hS
  let cs := ((BigFppfOver.toScheme B S hS).mapCone c).whisker e.inverse
  have hcs : IsLimit cs := hc.whiskerEquivalence e.symm
  let : IsAffine cs.pt := hC
  let : ∀ i, IsAffine (Ds.obj i) := fun i ↦ hDi (e.inverse.obj i)
  obtain ⟨i, Uᵢ, fᵢ, hUᵢ, hiso⟩ :=
    exists_standardFppfCovering_of_isLimit
      Ds cs hcs (fun j ↦ B.inclusion.obj (Q.X j))
      (fun j ↦ B.inclusion.map (Q.f j)) hQstd
  exact ⟨Q, e.inverse.obj i, Uᵢ, fᵢ, hUᵢ, hQ, hiso, hQU⟩


/-- A family in the big fppf category over `S` whose underlying family is a chosen covering
generates a covering sieve for the localized topology. -/
private theorem covering_sieve_over
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : BigFppfOver B S hS} (E : PreZeroHypercover.{u + 1} X)
    (hE : B.IsCovering ⟨X.left, E.map (Over.forget (B.obj hS))⟩) :
    E.sieve₀ ∈ BigFppfOver.topology B S hS X := by
  rw [BigFppfOver.topology, GrothendieckTopology.mem_over_iff,
    Sieve.overEquiv_ofArrows]
  exact Precoverage.generate_mem_toGrothendieck
    ⟨E.map (Over.forget (B.obj hS)), rfl, hE⟩

/-- Every covering of an affine object of the big fppf site over `S` is refined by a finite
family with affine sources. -/
private theorem finite_cover_refinement
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : BigFppfOver B S hS)
    (hX : IsAffine ((BigFppfOver.toScheme B S hS).obj X))
    (R : (BigFppfOver.topology B S hS).Cover X) :
    ∃ E : PreZeroHypercover.{u + 1} X, Finite E.I₀ ∧
      (∀ k, IsAffine ((BigFppfOver.toScheme B S hS).obj (E.X k))) ∧
      E.sieve₀ ∈ BigFppfOver.topology B S hS X ∧ ∀ k, R (E.f k) := by
  let := hX
  obtain ⟨Q, hQ, hstd, hQR⟩ := exists_standard_refinement_over B S hS X R
  let E : PreZeroHypercover X :=
    ⟨Q.I₀, fun k ↦ Over.mk (Q.f k ≫ X.hom), fun k ↦ Over.homMk (Q.f k)⟩
  exact ⟨E, hstd.finite_index, hstd.affine_source, covering_sieve_over B S hS E hQ, hQR⟩

/-- Every covering of the limit of a cofiltered system of affine objects is refined, after
base change along the limit cone, by a finite affine family defined at one of the stages. -/
private theorem finite_cover_descends
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type w} [Category.{w'} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ BigFppfOver B S hS) (c : Cone D)
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (hD : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj i)))
    (hC : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt))
    (R : (BigFppfOver.topology B S hS).Cover c.pt) :
    ∃ (i : I) (E : PreZeroHypercover.{u + 1} (D.obj i)), Finite E.I₀ ∧
      (∀ k, IsAffine ((BigFppfOver.toScheme B S hS).obj (E.X k))) ∧
      E.sieve₀ ∈ BigFppfOver.topology B S hS (D.obj i) ∧
      ∀ k, R (pullback.fst (c.π.app i) (E.f k)) := by
  classical
  let T := BigFppfOver.toScheme B S hS
  obtain ⟨Q, i, U, f, hstd, hQ, he, hQR⟩ :=
    exists_descended_standard_refinement_over B S hS D c hc hD hC R
  have hU (k : Q.I₀) : B.Contains (U k) := by
    let : LocallyOfFinitePresentation (f k) := (hstd.finite_presentation k).1
    let : QuasiCompact (f k) := (hstd.finite_presentation k).2.1
    exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (f k) (D.obj i).left.property
  let fB (k : Q.I₀) : B.obj (hU k) ⟶ (D.obj i).left := B.inclusion.preimage (f k)
  have hfB (k) : B.inclusion.map (fB k) = f k := B.inclusion.map_preimage _
  let E : PreZeroHypercover (D.obj i) :=
    ⟨Q.I₀, fun k ↦ Over.mk (fB k ≫ (D.obj i).hom), fun k ↦ Over.homMk (fB k)⟩
  have hE : B.IsCovering ⟨(D.obj i).left, E.map (Over.forget (B.obj hS))⟩ := by
    refine ⟨?_, hQ.2⟩
    change (E.map (Over.forget (B.obj hS))).presieve₀ ∈
      Scheme.fppfPrecoverage.comap B.inclusion (D.obj i).left
    rw [Precoverage.mem_comap_iff, ← PreZeroHypercover.presieve₀_map]
    apply (Scheme.presieve₀_mem_precoverage_iff _).2
    change (∀ x, ∃ k y, B.inclusion.map (fB k) y = x) ∧
      ∀ k, Flat (B.inclusion.map (fB k)) ∧ LocallyOfFinitePresentation (B.inclusion.map (fB k))
    simp only [hfB]
    exact ⟨fun x ↦ Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp hstd.jointly_surjective x),
      fun k ↦ ⟨hstd.flat k, (hstd.finite_presentation k).1⟩⟩
  refine ⟨i, E, hstd.finite_index, hstd.affine_source,
    covering_sieve_over B S hS E hE, ?_⟩
  intro k
  let e := (he k).some
  let p := pullback.fst (c.π.app i) (E.f k)
  let r : pullback (T.map (E.f k)) (T.map (c.π.app i)) ⟶
      pullback (f k) (T.map (c.π.app i)) :=
    pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _)
      (by simpa [T, E] using hfB k) (by simp)
  have hr : r ≫ pullback.snd (f k) (T.map (c.π.app i)) =
      pullback.snd (T.map (E.f k)) (T.map (c.π.app i)) :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  let g : T.obj (pullback (c.π.app i) (E.f k)) ⟶ B.inclusion.obj (Q.X k) :=
    (PreservesPullback.iso T (c.π.app i) (E.f k)).hom ≫
      (pullbackSymmetry _ _).hom ≫ r ≫ e.hom.left
  have hg : g ≫ B.inclusion.map (Q.f k) = T.map p := by
    have hew : e.hom.left ≫ B.inclusion.map (Q.f k) =
        pullback.snd (f k) (T.map (c.π.app i)) := Over.w e.hom
    simp only [g, Category.assoc, hew, hr, pullbackSymmetry_hom_comp_snd]
    exact pullbackComparison_comp_fst T _ _
  let gB : (pullback (c.π.app i) (E.f k)).left ⟶ Q.X k := B.inclusion.preimage g
  have hgB : gB ≫ Q.f k = p.left := B.inclusion.map_injective (by
    rw [B.inclusion.map_comp, show B.inclusion.map gB = g from B.inclusion.map_preimage _]
    exact hg)
  let a : pullback (c.π.app i) (E.f k) ⟶ Over.mk (Q.f k ≫ c.pt.hom) :=
    Over.homMk gB (by
      change gB ≫ (Q.f k ≫ c.pt.hom) = _
      rw [← Category.assoc, hgB]
      exact Over.w p)
  have ha : a ≫ (Over.homMk (Q.f k) : Over.mk (Q.f k ≫ c.pt.hom) ⟶ c.pt) = p :=
    Over.OverMorphism.ext hgB
  simpa only [ha] using R.1.downward_closed (hQR k) a

/-- The base change of a family generating a covering sieve again generates one. -/
theorem pullback_cover_mem
    {C : Type z} [Category.{z'} C] [HasPullbacks C]
    (J : GrothendieckTopology C) {X Y : C} (E : PreZeroHypercover X)
    (hE : E.sieve₀ ∈ J X) (f : Y ⟶ X) : (E.pullback₁ f).sieve₀ ∈ J Y := by
  apply J.superset_covering _ (J.pullback_stable f hE)
  rintro Z g ⟨W, a, _, ⟨k⟩, ha⟩
  refine ⟨_, pullback.lift g a ha.symm, _, ⟨k⟩, ?_⟩
  exact pullback.lift_fst _ _ _

/-- Two sections of a sheaf that agree on every member of a covering family are equal. -/
theorem sheaf_eq_of_cover
    {C : Type z} [Category.{z'} C] (J : GrothendieckTopology C)
    (G : Cᵒᵖ ⥤ Type v) (hG : Presieve.IsSheaf J G)
    {X : C} (E : PreZeroHypercover X) (hE : E.sieve₀ ∈ J X)
    {x y : G.obj (Opposite.op X)}
    (hxy : ∀ k, G.map (E.f k).op x = G.map (E.f k).op y) : x = y :=
  ((Presieve.isSheafFor_iff_generate _).mpr (hG _ hE)).isSeparatedFor.ext fun _ _ ⟨k⟩ ↦ hxy k

/-- The property of a transformation that, for every cofiltered system of affine objects, two
sections at a stage whose images agree at the limit have images agreeing at a later stage. -/
abbrev ImagesEventuallyEqual
    {C : Type z} [Category.{z'} C] (T : C ⥤ Scheme.{u})
    {F G : Cᵒᵖ ⥤ Type v} (η : F ⟶ G) : Prop :=
  ∀ (I : Type (max w w')) [Category.{w'} I] [IsCofiltered I]
    (D : I ⥤ C) (c : Cone D), IsLimit (T.mapCone c) →
    (∀ i, IsAffine (T.obj (D.obj i))) → IsAffine (T.obj c.pt) →
    ∀ (i : I) (x y : F.obj (Opposite.op (D.obj i))),
      G.map (c.π.app i).op (η.app _ x) = G.map (c.π.app i).op (η.app _ y) →
      ∃ (j : I) (f : j ⟶ i), G.map (D.map f).op (η.app _ x) =
        G.map (D.map f).op (η.app _ y)

/-- The property of a site that every covering of the limit of a cofiltered system of affine
objects is refined by the base change of a finite affine family from a stage. -/
abbrev AffineCoversDescend
    {C : Type z} [Category.{z'} C] [HasPullbacks C]
    (T : C ⥤ Scheme.{u}) (J : GrothendieckTopology C) : Prop :=
  ∀ (I : Type (max w w')) [Category.{w'} I] [IsCofiltered I]
    (D : I ⥤ C) (c : Cone D), IsLimit (T.mapCone c) →
    (∀ i, IsAffine (T.obj (D.obj i))) → IsAffine (T.obj c.pt) →
    ∀ R : J.Cover c.pt, ∃ (i : I) (E : PreZeroHypercover.{z} (D.obj i)),
      Finite E.I₀ ∧ (∀ k, IsAffine (T.obj (E.X k))) ∧ E.sieve₀ ∈ J (D.obj i) ∧
      ∀ k, R (pullback.fst (c.π.app i) (E.f k))

/-- Equality of two base-changed sections along `g'` passes to the base change along any `g`
factoring through `g'`. -/
private theorem pullback_snd_eq_of_factor
    {C : Type z} [Category.{z'} C] [HasPullbacks C]
    (G : Cᵒᵖ ⥤ Type v) {A B B' X : C} (f : X ⟶ A) (g : B ⟶ A) (g' : B' ⟶ A) (a : B ⟶ B')
    (hag : a ≫ g' = g) {x y : G.obj (Opposite.op X)}
    (h : G.map (pullback.snd g' f).op x = G.map (pullback.snd g' f).op y) :
    G.map (pullback.snd g f).op x = G.map (pullback.snd g f).op y := by
  subst hag
  have := congrArg (G.map (pullback.map (a ≫ g') f g' f a (𝟙 _) (𝟙 _) (by simp) (by simp)).op) h
  simpa only [← Functor.map_comp_apply, ← op_comp, pullback.lift_snd, Category.comp_id] using this

/-- Eventual equality of images passes to the base change of the system along an affine
morphism to a stage. -/
theorem images_eventually_equal_pullback
    {C : Type z} [Category.{z'} C] [HasPullbacks C]
    (T : C ⥤ Scheme.{u}) [PreservesLimitsOfShape WalkingCospan T]
    {F G : Cᵒᵖ ⥤ Type v} (η : F ⟶ G)
    (hη : ImagesEventuallyEqual.{u, v, w, w'} T η)
    {I : Type (max w w')} [Category.{w'} I] [IsCofiltered I]
    (D : I ⥤ C) (c : Cone D) (hc : IsLimit (T.mapCone c))
    (hD : ∀ i, IsAffine (T.obj (D.obj i))) (hC : IsAffine (T.obj c.pt))
    (i : I) {X : C} (f : X ⟶ D.obj i) (hX : IsAffine (T.obj X))
    (x y : F.obj (Opposite.op X))
    (hxy : G.map (pullback.snd (c.π.app i) f).op (η.app _ x) =
      G.map (pullback.snd (c.π.app i) f).op (η.app _ y)) :
    ∃ j : Over i, G.map (pullback.snd (D.map j.hom) f).op (η.app _ x) =
      G.map (pullback.snd (D.map j.hom) f).op (η.app _ y) := by
  let : ∀ i, IsAffine (T.obj (D.obj i)) := hD
  let : IsAffine (T.obj c.pt) := hC
  let : IsAffine (T.obj X) := hX
  let E := Over.post D ⋙ Over.pullback f ⋙ Over.forget X
  let cb := (Over.forget X).mapCone ((Over.pullback f).mapCone (c.overPost i))
  let j₀ : Over i := Over.mk (𝟙 i)
  let a := pullback.snd (D.map j₀.hom) f
  obtain ⟨j, e, he⟩ := hη (Over i) E cb
    (isLimit_mapCone_pullback_overPost T D c hc i f)
    (fun j ↦ isAffine_obj_pullback T (D.map j.hom) f)
    (isAffine_obj_pullback T (show c.pt ⟶ D.obj i from c.π.app i) f) j₀
    (F.map a.op x) (F.map a.op y) (by
      let b : pullback (c.π.app i) f ⟶ pullback (D.map j₀.hom) f :=
        ((Over.pullback f).map ((c.overPost i).π.app j₀)).left
      change G.map b.op (η.app _ (F.map a.op x)) = G.map b.op (η.app _ (F.map a.op y))
      rw [η.naturality_apply a.op, η.naturality_apply a.op]
      simp only [← Functor.map_comp_apply, ← op_comp]
      have hh : b ≫ a = pullback.snd (c.π.app i) f := pullback.lift_snd _ _ _
      rwa [hh])
  refine ⟨j, ?_⟩
  let b : pullback (D.map j.hom) f ⟶ pullback (D.map j₀.hom) f :=
    ((Over.pullback f).map ((Over.post D).map e)).left
  change G.map b.op (η.app _ (F.map a.op x)) = G.map b.op (η.app _ (F.map a.op y)) at he
  rw [η.naturality_apply a.op, η.naturality_apply a.op] at he
  simp only [← Functor.map_comp_apply, ← op_comp] at he
  have hh : b ≫ a = pullback.snd (D.map j.hom) f := pullback.lift_snd _ _ _
  rwa [hh] at he

/-- For a limit-preserving presheaf, two sections over the base change of a stage that agree
over the base change of the limit agree over the base change of a later stage. -/
theorem eventually_eq_pullback_sections
    {C : Type z} [Category.{z'} C] [HasPullbacks C]
    (T : C ⥤ Scheme.{u}) [PreservesLimitsOfShape WalkingCospan T]
    (F : Cᵒᵖ ⥤ Type v)
    (hF : LimitPreserving.{u, v, w, w', z} T F)
    {I : Type (max w w')} [Category.{w'} I] [IsCofiltered I]
    (D : I ⥤ C) (c : Cone D) (hc : IsLimit (T.mapCone c))
    (hD : ∀ i, IsAffine (T.obj (D.obj i))) (hC : IsAffine (T.obj c.pt))
    (i : I) {X : C} (f : X ⟶ D.obj i) (hX : IsAffine (T.obj X))
    (x y : F.obj (Opposite.op X))
    (hxy : F.map (pullback.snd (c.π.app i) f).op x =
      F.map (pullback.snd (c.π.app i) f).op y) :
    ∃ j : Over i, F.map (pullback.snd (D.map j.hom) f).op x =
      F.map (pullback.snd (D.map j.hom) f).op y :=
  images_eventually_equal_pullback T (𝟙 F)
    (fun _ _ _ D c hc hD hC i x y hxy ↦
      eventually_eq_of_limitPreserving T F hF D c hc hD hC i x y hxy)
    D c hc hD hC i f hX x y hxy

/-- A locally injective transformation from a limit-preserving presheaf into a sheaf has
eventually equal images, by descending the equalizer covering to a stage. -/
theorem images_eventually_equal_of_locally_injective
    {C : Type z} [Category.{z'} C] [HasPullbacks C]
    (T : C ⥤ Scheme.{u}) [PreservesLimitsOfShape WalkingCospan T]
    (J : GrothendieckTopology C)
    (hdesc : AffineCoversDescend.{u, w, w'} T J)
    {F G : Cᵒᵖ ⥤ Type v} (η : F ⟶ G)
    [Presheaf.IsLocallyInjective J η] (hG : Presieve.IsSheaf J G)
    (hF : LimitPreserving.{u, v, w, w', z} T F) :
    ImagesEventuallyEqual.{u, v, w, w'} T η := by
  classical
  intro I _ _ D c hc hD hC i x y hxy
  have heq : η.app _ (F.map (c.π.app i).op x) = η.app _ (F.map (c.π.app i).op y) := by
    simpa only [← NatTrans.naturality_apply] using hxy
  let R : J.Cover c.pt := ⟨_, Presheaf.equalizerSieve_mem J η _ _ heq⟩
  obtain ⟨j, E, hfin, haff, hE, hER⟩ := hdesc (Over i) (Over.forget i ⋙ D)
    (c.whisker (Over.forget i))
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) (T.mapCone c)).symm hc)
    (fun j ↦ hD j.left) hC R
  let := hfin
  have hk (k : E.I₀) : ∃ l : Over j.left,
      F.map (pullback.snd (D.map l.hom) (E.f k)).op
        (F.map (E.f k).op (F.map (D.map j.hom).op x)) =
      F.map (pullback.snd (D.map l.hom) (E.f k)).op
        (F.map (E.f k).op (F.map (D.map j.hom).op y)) := by
    apply eventually_eq_pullback_sections T F hF D c hc hD hC j.left (E.f k) (haff k)
    change F.map (pullback.snd (c.π.app j.left) (E.f k)).op _ = _
    have hr : F.map (pullback.fst (c.π.app j.left) (E.f k)).op
        (F.map (c.π.app i).op x) = F.map (pullback.fst (c.π.app j.left) (E.f k)).op
        (F.map (c.π.app i).op y) := hER k
    have hh : pullback.snd (c.π.app j.left) (E.f k) ≫ E.f k ≫ D.map j.hom =
        pullback.fst (c.π.app j.left) (E.f k) ≫ c.π.app i := by
      rw [← Category.assoc, ← pullback.condition, Category.assoc, c.w j.hom]
    simpa only [← Functor.map_comp_apply, ← op_comp, Category.assoc, hh] using hr
  choose l hl using hk
  obtain ⟨m, g, a, ha⟩ := exists_cofiltered_common_refinement j.left (fun k ↦ (l k).left)
    (fun k ↦ (l k).hom)
  refine ⟨m, g ≫ j.hom, ?_⟩
  apply sheaf_eq_of_cover J G hG (E.pullback₁ (D.map g)) (pullback_cover_mem J E hE _)
  intro k
  change E.I₀ at k
  have h'' := congrArg (η.app _) (pullback_snd_eq_of_factor F (E.f k) (D.map g)
    (D.map (l k).hom) (D.map (a k)) (by rw [← D.map_comp, ha k]) (hl k))
  change G.map (pullback.fst (D.map g) (E.f k)).op
    (G.map (D.map (g ≫ j.hom)).op (η.app _ x)) =
    G.map (pullback.fst (D.map g) (E.f k)).op
      (G.map (D.map (g ≫ j.hom)).op (η.app _ y))
  have hh : pullback.snd (D.map g) (E.f k) ≫ E.f k ≫ D.map j.hom =
      pullback.fst (D.map g) (E.f k) ≫ D.map (g ≫ j.hom) := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc, D.map_comp]
  simpa only [NatTrans.naturality_apply, ← Functor.map_comp_apply,
    ← op_comp, Category.assoc, hh] using h''

/-- The property of a site that every covering of an affine object is refined by a finite
family with affine sources. -/
abbrev FiniteAffineRefinements
    {C : Type z} [Category.{z'} C]
    (T : C ⥤ Scheme.{u}) (J : GrothendieckTopology C) : Prop :=
  ∀ (X : C), IsAffine (T.obj X) → ∀ R : J.Cover X,
    ∃ E : PreZeroHypercover.{z} X, Finite E.I₀ ∧
      (∀ k, IsAffine (T.obj (E.X k))) ∧ E.sieve₀ ∈ J X ∧ ∀ k, R (E.f k)

/-- Eventual equality of images for finitely many base changes at once, obtained by taking a
common refinement of the stages. -/
theorem images_eventually_equal_pullback_finite
    {C : Type z} [Category.{z'} C] [HasPullbacks C]
    (T : C ⥤ Scheme.{u}) [PreservesLimitsOfShape WalkingCospan T]
    {F G : Cᵒᵖ ⥤ Type v} (η : F ⟶ G)
    (hη : ImagesEventuallyEqual.{u, v, w, w'} T η)
    {I : Type (max w w')} [Category.{w'} I] [IsCofiltered I]
    (D : I ⥤ C) (c : Cone D) (hc : IsLimit (T.mapCone c))
    (hD : ∀ i, IsAffine (T.obj (D.obj i))) (hC : IsAffine (T.obj c.pt))
    (i : I) {K : Type*} [Finite K] (X : K → C)
    (f : ∀ k, X k ⟶ D.obj i) (hX : ∀ k, IsAffine (T.obj (X k)))
    (x y : ∀ k, F.obj (Opposite.op (X k)))
    (hxy : ∀ k, G.map (pullback.snd (c.π.app i) (f k)).op (η.app _ (x k)) =
      G.map (pullback.snd (c.π.app i) (f k)).op (η.app _ (y k))) :
    ∃ j : Over i, ∀ k, G.map (pullback.snd (D.map j.hom) (f k)).op (η.app _ (x k)) =
      G.map (pullback.snd (D.map j.hom) (f k)).op (η.app _ (y k)) := by
  classical
  choose j hj using fun k ↦ images_eventually_equal_pullback T η hη
    D c hc hD hC i (f k) (hX k) (x k) (y k) (hxy k)
  obtain ⟨m, g, a, ha⟩ := exists_cofiltered_common_refinement i (fun k ↦ (j k).left)
    (fun k ↦ (j k).hom)
  refine ⟨Over.mk g, fun k ↦ ?_⟩
  exact pullback_snd_eq_of_factor G (f k) (D.map g) (D.map (j k).hom) (D.map (a k))
    (by rw [← D.map_comp, ha k]) (hj k)

/-- If a transformation into a sheaf is locally surjective and has eventually equal images,
then the sheaf itself has eventually equal sections. -/
theorem images_eventually_equal_of_locally_surjective
    {C : Type z} [Category.{z'} C] [HasPullbacks C]
    (T : C ⥤ Scheme.{u}) [PreservesLimitsOfShape WalkingCospan T]
    (J : GrothendieckTopology C) (hfin : FiniteAffineRefinements T J)
    {F G : Cᵒᵖ ⥤ Type v} (η : F ⟶ G)
    [Presheaf.IsLocallySurjective J η] (hG : Presieve.IsSheaf J G)
    (hη : ImagesEventuallyEqual.{u, v, w, w'} T η) :
    ImagesEventuallyEqual.{u, v, w, w'} T (𝟙 G) := by
  intro I _ _ D c hc hD hC i x y hxy
  change G.map (c.π.app i).op x = G.map (c.π.app i).op y at hxy
  let R : J.Cover (D.obj i) := ⟨Presheaf.imageSieve η x ⊓ Presheaf.imageSieve η y,
    J.intersection_covering (Presheaf.imageSieve_mem J η x)
      (Presheaf.imageSieve_mem J η y)⟩
  obtain ⟨E, hEfin, hEaff, hE, hER⟩ := hfin (D.obj i) (hD i) R
  let := hEfin
  choose a ha using fun k ↦ (hER k).1
  choose b hb using fun k ↦ (hER k).2
  obtain ⟨j, hj⟩ := images_eventually_equal_pullback_finite T η hη
    D c hc hD hC i E.X E.f hEaff a b (fun k ↦ by
      rw [ha k, hb k]
      simpa only [← Functor.map_comp_apply, ← op_comp, ← pullback.condition]
        using congrArg (G.map (pullback.fst (c.π.app i) (E.f k)).op) hxy)
  refine ⟨j.left, j.hom, ?_⟩
  change G.map (D.map j.hom).op x = G.map (D.map j.hom).op y
  apply sheaf_eq_of_cover J G hG (E.pullback₁ (D.map j.hom)) (pullback_cover_mem J E hE _)
  intro k
  change E.I₀ at k
  change G.map (pullback.fst (D.map j.hom) (E.f k)).op
    (G.map (D.map j.hom).op x) = G.map (pullback.fst (D.map j.hom) (E.f k)).op
    (G.map (D.map j.hom).op y)
  have h := hj k
  rw [ha k, hb k] at h
  simpa only [← Functor.map_comp_apply, ← op_comp, ← pullback.condition,
    PreZeroHypercover.pullback₁_f] using h

/-- Agreement of two sections on the corners of a cartesian square transfers to the canonical
fibre product. -/
theorem pullback_restriction_eq_of_isPullback
    {C : Type z} [Category.{z'} C] [HasPullbacks C]
    (G : Cᵒᵖ ⥤ Type v) {A B X Y : C}
    {a : A ⟶ X} {b : A ⟶ B} {f : X ⟶ Y} {g : B ⟶ Y}
    (h : IsPullback a b f g) (x : G.obj (Opposite.op X)) (y : G.obj (Opposite.op B))
    (hxy : G.map a.op x = G.map b.op y) :
    G.map (pullback.fst f g).op x = G.map (pullback.snd f g).op y := by
  apply ((isIso_iff_bijective (G.map h.isoPullback.hom.op)).mp inferInstance).1
  simpa only [← Functor.map_comp_apply, ← op_comp,
    h.isoPullback_hom_fst, h.isoPullback_hom_snd] using hxy

/-- Agreement of two sections on a fibre product restricts along any commuting pair of
morphisms into the two factors. -/
theorem restrict_eq_of_pullback_eq
    {C : Type z} [Category.{z'} C] [HasPullbacks C]
    (G : Cᵒᵖ ⥤ Type v) {A X Y Z : C} {f : A ⟶ Y} {g : X ⟶ Y}
    {x : G.obj (Opposite.op A)} {y : G.obj (Opposite.op X)}
    (h : G.map (pullback.fst f g).op x = G.map (pullback.snd f g).op y)
    (p : Z ⟶ A) (q : Z ⟶ X) (hpq : p ≫ f = q ≫ g) :
    G.map p.op x = G.map q.op y := by
  have hh := congrArg (G.map (pullback.lift p q hpq).op) h
  simpa only [← Functor.map_comp_apply, ← op_comp, pullback.lift_fst, pullback.lift_snd] using hh

/-- A family of sections each agreeing with a fixed section on a base change is compatible on
the overlaps of the family, after base change along the fixed morphism. -/
theorem overlap_eq_of_pullback_amalgamation
    {C : Type z} [Category.{z'} C] [HasPullbacks C]
    (G : Cᵒᵖ ⥤ Type v) {A X : C} (f : A ⟶ X) (E : PreZeroHypercover X)
    (x : G.obj (Opposite.op A)) (y : ∀ k, G.obj (Opposite.op (E.X k)))
    (h : ∀ k, G.map (pullback.fst f (E.f k)).op x =
      G.map (pullback.snd f (E.f k)).op (y k)) (k l : E.I₀) :
    G.map (pullback.snd f (pullback.fst (E.f k) (E.f l) ≫ E.f k)).op
        (G.map (pullback.fst (E.f k) (E.f l)).op (y k)) =
      G.map (pullback.snd f (pullback.fst (E.f k) (E.f l) ≫ E.f k)).op
        (G.map (pullback.snd (E.f k) (E.f l)).op (y l)) := by
  let p := pullback.fst f (pullback.fst (E.f k) (E.f l) ≫ E.f k)
  let q := pullback.snd f (pullback.fst (E.f k) (E.f l) ≫ E.f k)
  have hk := restrict_eq_of_pullback_eq G (h k) p
    (q ≫ pullback.fst (E.f k) (E.f l)) (by
      dsimp [p, q]
      rw [Category.assoc]
      exact pullback.condition)
  have hl := restrict_eq_of_pullback_eq G (h l) p
    (q ≫ pullback.snd (E.f k) (E.f l)) (by
      dsimp [p, q]
      rw [Category.assoc, ← pullback.condition]
      exact pullback.condition)
  simpa only [op_comp, G.map_comp_apply] using hk.symm.trans hl

/-- Compatibility on overlaps makes the base-changed family a pullback-compatible family for
the base-changed covering. -/
theorem pullback_family_compatible
    {C : Type z} [Category.{z'} C] [HasPullbacks C]
    (G : Cᵒᵖ ⥤ Type v) {A X : C} (f : A ⟶ X) (E : PreZeroHypercover X)
    (y : ∀ k, G.obj (Opposite.op (E.X k)))
    (h : ∀ k l,
      G.map (pullback.snd f (pullback.fst (E.f k) (E.f l) ≫ E.f k)).op
          (G.map (pullback.fst (E.f k) (E.f l)).op (y k)) =
        G.map (pullback.snd f (pullback.fst (E.f k) (E.f l) ≫ E.f k)).op
          (G.map (pullback.snd (E.f k) (E.f l)).op (y l))) :
    Presieve.Arrows.PullbackCompatible G (E.pullback₁ f).f
      (fun k ↦ G.map (pullback.snd f (E.f k)).op (y k)) := by
  intro k l
  change E.I₀ at k l
  let a := pullback.fst (pullback.fst f (E.f k)) (pullback.fst f (E.f l))
  let b := pullback.snd (pullback.fst f (E.f k)) (pullback.fst f (E.f l))
  have hab : (a ≫ pullback.snd f (E.f k)) ≫ E.f k =
      (b ≫ pullback.snd f (E.f l)) ≫ E.f l := by
    rw [Category.assoc, Category.assoc, ← pullback.condition, ← pullback.condition,
      ← Category.assoc, ← Category.assoc]
    exact congrArg (fun t ↦ t ≫ f) (pullback.condition)
  let q := pullback.lift (a ≫ pullback.snd f (E.f k)) (b ≫ pullback.snd f (E.f l)) hab
  let p := a ≫ pullback.fst f (E.f k)
  have hpq : p ≫ f = q ≫ (pullback.fst (E.f k) (E.f l) ≫ E.f k) := by
    dsimp [p, q]
    rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, pullback.condition]
  have hh := congrArg (G.map (pullback.lift p q hpq).op) (h k l)
  change G.map a.op (G.map (pullback.snd f (E.f k)).op (y k)) =
    G.map b.op (G.map (pullback.snd f (E.f l)).op (y l))
  simpa only [← Functor.map_comp_apply, ← op_comp, pullback.lift_snd_assoc,
    q, pullback.lift_fst, pullback.lift_snd] using hh

/-- Every section of the sheaf over the limit of a cofiltered system of affine objects is the
restriction of a section at one of the stages. -/
theorem exists_sheaf_section_at_stage
    {C : Type z} [Category.{z'} C] [HasPullbacks C]
    (T : C ⥤ Scheme.{u}) [PreservesLimitsOfShape WalkingCospan T]
    (J : GrothendieckTopology C) (hdesc : AffineCoversDescend.{u, w, w'} T J)
    {F G : Cᵒᵖ ⥤ Type v} (η : F ⟶ G) [Presheaf.IsLocallySurjective J η]
    (hG : Presieve.IsSheaf J G)
    (hF : LimitPreserving.{u, v, w, w', z} T F)
    (hinj : ImagesEventuallyEqual.{u, v, w, w'} T (𝟙 G))
    {I : Type (max w w')} [Category.{w'} I] [IsCofiltered I]
    (D : I ⥤ C) (c : Cone D) (hc : IsLimit (T.mapCone c))
    (hD : ∀ i, IsAffine (T.obj (D.obj i))) (hC : IsAffine (T.obj c.pt))
    (x : G.obj (Opposite.op c.pt)) :
    ∃ (i : I) (y : G.obj (Opposite.op (D.obj i))), G.map (c.π.app i).op y = x := by
  classical
  let : ∀ i, IsAffine (T.obj (D.obj i)) := hD
  let : IsAffine (T.obj c.pt) := hC
  let R : J.Cover c.pt := ⟨Presheaf.imageSieve η x, Presheaf.imageSieve_mem J η x⟩
  obtain ⟨i, E, hEfin, hEaff, hE, hER⟩ := hdesc I D c hc hD hC R
  let := hEfin
  choose a ha using hER
  obtain ⟨j, y, hy⟩ := exists_sections_pullback_of_limitPreserving
    T F hF D c hc hD hC i E.X E.f hEaff a
  let Ej := E.pullback₁ (D.map j.hom)
  let : Finite Ej.I₀ := hEfin
  have hEj : Ej.sieve₀ ∈ J (D.obj j.left) := pullback_cover_mem J E hE _
  have hEjaff (k : Ej.I₀) : IsAffine (T.obj (Ej.X k)) := by
    let := hEaff k
    exact isAffine_obj_pullback T (D.map j.hom) (E.f k)
  let z (k : Ej.I₀) : G.obj (Opposite.op (Ej.X k)) := η.app _ (y k)
  have hz (k : Ej.I₀) : G.map (pullback.fst (c.π.app j.left) (Ej.f k)).op x =
      G.map (pullback.snd (c.π.app j.left) (Ej.f k)).op (z k) := by
    change E.I₀ at k
    let b : pullback (c.π.app i) (E.f k) ⟶ pullback (D.map j.hom) (E.f k) :=
      ((Over.pullback (E.f k)).map ((c.overPost i).π.app j)).left
    have hh : G.map (pullback.fst (c.π.app i) (E.f k)).op x =
        G.map b.op (η.app _ (y k)) :=
      (ha k).symm.trans ((congrArg (η.app _) (hy k).symm).trans
        (η.naturality_apply b.op (y k)))
    exact pullback_restriction_eq_of_isPullback G
      (isPullback_pullback_map (E.f k) ((c.overPost i).π.app j)).flip x (z k) hh
  let O (kl : Ej.I₀ × Ej.I₀) := pullback (Ej.f kl.1) (Ej.f kl.2)
  let fO (kl : Ej.I₀ × Ej.I₀) : O kl ⟶ D.obj j.left :=
    pullback.fst (Ej.f kl.1) (Ej.f kl.2) ≫ Ej.f kl.1
  let xO (kl : Ej.I₀ × Ej.I₀) : G.obj (Opposite.op (O kl)) :=
    G.map (pullback.fst (Ej.f kl.1) (Ej.f kl.2)).op (z kl.1)
  let yO (kl : Ej.I₀ × Ej.I₀) : G.obj (Opposite.op (O kl)) :=
    G.map (pullback.snd (Ej.f kl.1) (Ej.f kl.2)).op (z kl.2)
  have hO (kl) : IsAffine (T.obj (O kl)) := by
    let := hEjaff kl.1
    let := hEjaff kl.2
    exact isAffine_obj_pullback T (Ej.f kl.1) (Ej.f kl.2)
  obtain ⟨m, hm⟩ := images_eventually_equal_pullback_finite T (𝟙 G) hinj
    D c hc hD hC j.left O fO hO xO yO (fun kl ↦
      overlap_eq_of_pullback_amalgamation G (c.π.app j.left) Ej x z hz kl.1 kl.2)
  let Em := Ej.pullback₁ (D.map m.hom)
  let t (k : Em.I₀) : G.obj (Opposite.op (Em.X k)) :=
    G.map (pullback.snd (D.map m.hom) (Ej.f k)).op (z k)
  have ht : Presieve.Arrows.PullbackCompatible G Em.f t :=
    pullback_family_compatible G (D.map m.hom) Ej z (fun k l ↦ hm (k, l))
  have hEm : Em.sieve₀ ∈ J (D.obj m.left) := pullback_cover_mem J Ej hEj _
  obtain ⟨s, hs, _⟩ := (Presieve.isSheafFor_arrows_iff_pullbacks G Em.f).mp
    ((Presieve.isSheafFor_iff_generate _).mpr (hG _ hEm)) t ht
  refine ⟨m.left, s, ?_⟩
  apply sheaf_eq_of_cover J G hG (Ej.pullback₁ (c.π.app j.left))
    (pullback_cover_mem J Ej hEj _)
  intro k
  change Ej.I₀ at k
  let b : pullback (c.π.app j.left) (Ej.f k) ⟶ pullback (D.map m.hom) (Ej.f k) :=
    ((Over.pullback (Ej.f k)).map ((c.overPost j.left).π.app m)).left
  have hb : b ≫ pullback.fst (D.map m.hom) (Ej.f k) =
      pullback.fst (c.π.app j.left) (Ej.f k) ≫ c.π.app m.left :=
    (isPullback_pullback_map (Ej.f k) ((c.overPost j.left).π.app m)).w
  have hb' : b ≫ pullback.snd (D.map m.hom) (Ej.f k) =
      pullback.snd (c.π.app j.left) (Ej.f k) := pullback.lift_snd _ _ _
  change G.map (pullback.fst (c.π.app j.left) (Ej.f k)).op
    (G.map (c.π.app m.left).op s) = G.map (pullback.fst (c.π.app j.left) (Ej.f k)).op x
  have hs' : G.map (pullback.fst (D.map m.hom) (Ej.f k)).op s =
      G.map (pullback.snd (D.map m.hom) (Ej.f k)).op (z k) := hs k
  rw [← G.map_comp_apply, ← op_comp, ← hb, op_comp, G.map_comp_apply, hs']
  change G.map b.op (G.map (pullback.snd (D.map m.hom) (Ej.f k)).op (z k)) = _
  rw [← G.map_comp_apply, ← op_comp, hb']
  exact (hz k).symm

/-- **Coverings of a cofiltered affine limit descend in the big fppf site.** Every covering of
the limit of a cofiltered system of affine objects of the big fppf site over `S`, indexed in a
universe below that of the schemes, is refined by the base change of a finite family of affine
objects which covers a stage of the system. -/
public theorem affineCoversDescend_bigFppfOver [UnivLE.{max w w', u}]
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    AffineCoversDescend.{u, w, w'} (BigFppfOver.toScheme B S hS)
      (BigFppfOver.topology B S hS) :=
  have : UnivLE.{w', u} := UnivLE.trans.{w', max w w', u}
  fun _ _ _ D c hc hD hC R ↦ finite_cover_descends B S hS D c hc hD hC R

/-- **Coverings of an affine object of the big fppf site have finite affine refinements.** -/
public theorem finiteAffineRefinements_bigFppfOver
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    FiniteAffineRefinements (BigFppfOver.toScheme B S hS) (BigFppfOver.topology B S hS) :=
  finite_cover_refinement B S hS

/-- An fppf sheaf receiving a locally bijective map from a limit-preserving presheaf is
limit preserving. Local injectivity makes sections that agree at the limit agree at a later
stage, and local surjectivity puts every section of the sheaf at a finite stage. -/
@[stacks 049O "locally bijective comparison"]
public theorem limitPreserving_of_isLocallyBijective [UnivLE.{max w w', u}]
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v} (η : F ⟶ G)
    [Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) η]
    [Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS) η]
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    (hF : LimitPreserving.{u, v, w, w', u + 1} (BigFppfOver.toScheme B S hS) F) :
    LimitPreserving.{u, v, w, w', u + 1} (BigFppfOver.toScheme B S hS) G := by
  let T := BigFppfOver.toScheme B S hS
  let J := BigFppfOver.topology B S hS
  have hdesc : AffineCoversDescend.{u, w, w'} T J := affineCoversDescend_bigFppfOver B S hS
  have hfin : FiniteAffineRefinements T J := finiteAffineRefinements_bigFppfOver B S hS
  have hGt : Presieve.IsSheaf J G := (isSheaf_iff_isSheaf_of_type J G).mp hG
  have hη : ImagesEventuallyEqual.{u, v, w, w'} T η :=
    images_eventually_equal_of_locally_injective T J hdesc η hGt hF
  have hinj : ImagesEventuallyEqual.{u, v, w, w'} T (𝟙 G) :=
    images_eventually_equal_of_locally_surjective T J hfin η hGt hη
  intro I _ _ D c hc hD hC
  exact isColimit_mapCocone_of_exists_of_eventually_eq G D c
    (exists_sheaf_section_at_stage T J hdesc η hGt hF hinj D c hc hD hC)
    (hinj I D c hc hD hC)

/-- Fppf sheafification of a limit-preserving presheaf is limit preserving. -/
@[stacks 049O]
public theorem limitPreserving_sheafify [UnivLE.{max w w', u}]
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max (u + 1) v))
    (hF : LimitPreserving.{u, max (u + 1) v, w, w', u + 1}
      (BigFppfOver.toScheme B S hS) F) :
    LimitPreserving.{u, max (u + 1) v, w, w', u + 1}
      (BigFppfOver.toScheme B S hS)
      ((BigFppfOver.topology B S hS).sheafify F) :=
  let J := BigFppfOver.topology B S hS
  have : Presheaf.IsLocallySurjective J (J.toSheafify F) := isLocallySurjective_toSheafify J F
  have : Presheaf.IsLocallyInjective J (J.toSheafify F) := isLocallyInjective_toSheafify J F
  limitPreserving_of_isLocallyBijective.{u, max (u + 1) v, w, w'} B S hS (J.toSheafify F)
    (J.sheafify_isSheaf F) hF

end AlgebraicGeometry
