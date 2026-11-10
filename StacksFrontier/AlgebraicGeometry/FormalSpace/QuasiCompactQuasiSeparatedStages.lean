module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Factorization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.QuasiFiniteRepresentableULift
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.ThickeningStage
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SchemeImageSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.AlgebraicQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.InvariantImageRelation
public import StacksFrontier.CategoryTheory.EquivalenceRelation.Transfer

/-!
# Stages of a quasi-compact quasi-separated formal algebraic space

Let `S` be a scheme contained in a big fppf site `B`, let `X` be a quasi-compact and
quasi-separated formal algebraic space over `S`, and let `c : Y ⟶ X` be a chart, representable
by objects of the site and étale, by an affine formal algebraic space `Y` presented as a
directed colimit `colim Y_i` of affine schemes along thickenings. For each index `i` there is an
affine closed subscheme `Z ⊆ Y` containing `Y_i` which is invariant for the étale equivalence
relation `Y ×_X Y`, and the restriction of that relation to `Z` is an étale equivalence
relation. These invariant stages form a monotone system indexed by the same directed set.

## Main definitions

* `AlgebraicGeometry.FormalSpace.uliftYonedaHom`: a morphism of fppf sheaves out of a
  sheafified representable, read as a morphism of presheaves out of the universe-lifted Yoneda
  presheaf.
* `AlgebraicGeometry.FormalSpace.stageObj` and `AlgebraicGeometry.FormalSpace.stageMap'`: a
  stage of a presentation of an affine formal algebraic space and its map to the presented sheaf.
* `AlgebraicGeometry.FormalSpace.overlapObj`: the object of the site representing `Y_i ×_X Y`.
* `AlgebraicGeometry.FormalSpace.overlapTransition`: the transition morphism between two
  overlaps.

## Main results

* `AlgebraicGeometry.FormalSpace.compactSpace_overlapObj`: for a quasi-separated `X` the overlap
  `Y_i ×_X Y` is a quasi-compact scheme of the site.
* `AlgebraicGeometry.FormalSpace.exists_factor_stageMap`: a morphism to the presented sheaf from
  the sheaf represented by a quasi-compact object of the site factors through one stage.
* `AlgebraicGeometry.FormalSpace.exists_invariantStage`: the invariant affine closed subscheme
  cut out by a stage, with its restricted relation as a kernel pair.
* `AlgebraicGeometry.FormalSpace.isEtaleEquivalenceRelation_of_isKernelPair`: such a kernel pair
  is an étale equivalence relation over `S`.
* `AlgebraicGeometry.FormalSpace.exists_invariantStageSystem`: the monotone system of invariant
  stages.
* `AlgebraicGeometry.FormalSpace.relative_etaleOnSite_of_isRepresentableEtale` and
  `AlgebraicGeometry.FormalSpace.relative_surjectiveOnSite_of_isLocallySurjective`: a
  representable étale chart is étale, and a representable surjection of fppf sheaves is
  surjective, after every represented base change.

## References

* [Stacks Project, Tag 02WS](https://stacks.math.columbia.edu/tag/02WS)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 0AI9](https://stacks.math.columbia.edu/tag/0AI9)
* [Stacks Project, Tag 0AJ5](https://stacks.math.columbia.edu/tag/0AJ5)
* [Stacks Project, Tag 0AJE](https://stacks.math.columbia.edu/tag/0AJE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Reading a sheaf morphism out of a sheafified representable as a presheaf morphism -/

/-- A morphism of fppf sheaves whose source is a sheafified representable, read as a morphism
of presheaves out of the universe-lifted Yoneda presheaf. -/
noncomputable def uliftYonedaHom {T : BigFppfOver B S hS} {Z : FppfSheaf B S hS}
    (h : (fppfYoneda B S hS).obj T ⟶ Z) :
    (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).obj T ⟶ Z.obj :=
  ((fppfYonedaCompSheafToPresheaf' B S hS).app T).inv ≫ h.hom

/-- A morphism of presheaves out of the universe-lifted Yoneda presheaf of an object of the
site into the presheaf of an fppf sheaf, read as a morphism of fppf sheaves. This inverts
`AlgebraicGeometry.FormalSpace.uliftYonedaHom`. -/
noncomputable def sheafHomOfUliftYonedaHom {T : BigFppfOver B S hS} {Z : FppfSheaf B S hS}
    (h : (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).obj T ⟶ Z.obj) :
    (fppfYoneda B S hS).obj T ⟶ Z :=
  ⟨((fppfYonedaCompSheafToPresheaf' B S hS).app T).hom ≫ h⟩

/-- `AlgebraicGeometry.FormalSpace.uliftYonedaHom` inverts
`AlgebraicGeometry.FormalSpace.sheafHomOfUliftYonedaHom`. -/
@[simp]
theorem uliftYonedaHom_sheafHomOfUliftYonedaHom {T : BigFppfOver B S hS} {Z : FppfSheaf B S hS}
    (h : (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).obj T ⟶ Z.obj) :
    uliftYonedaHom B S hS (sheafHomOfUliftYonedaHom B S hS h) = h := by
  change ((fppfYonedaCompSheafToPresheaf' B S hS).app T).inv ≫
    ((fppfYonedaCompSheafToPresheaf' B S hS).app T).hom ≫ h = h
  rw [Iso.inv_hom_id_assoc]

/-- The identification of the two readings of a morphism out of a sheafified representable is
injective. -/
theorem uliftYonedaHom_injective {T : BigFppfOver B S hS} {Z : FppfSheaf B S hS} :
    Function.Injective (uliftYonedaHom B S hS (T := T) (Z := Z)) := by
  intro h h' hh
  exact Sheaf.hom_ext ((cancel_epi ((fppfYonedaCompSheafToPresheaf' B S hS).app T).inv).1 hh)

/-- Reading a morphism out of a sheafified representable as a morphism of universe-lifted
presheaves does not change its effect on sections, once the sections are transported along the
comparison isomorphism of the two sources. -/
theorem uliftYonedaHom_app {T : BigFppfOver B S hS} {Z : FppfSheaf B S hS}
    (h : (fppfYoneda B S hS).obj T ⟶ Z) (V : BigFppfOver B S hS)
    (w : ((fppfYoneda B S hS).obj T).obj.obj (Opposite.op V)) :
    (uliftYonedaHom B S hS h).app (Opposite.op V)
        (((fppfYonedaCompSheafToPresheaf' B S hS).app T).hom.app (Opposite.op V) w) =
      h.hom.app (Opposite.op V) w := by
  simp only [uliftYonedaHom, NatTrans.comp_app, ConcreteCategory.comp_apply,
    Iso.hom_inv_id_app_apply]

/-- Reading a morphism out of a sheafified representable as a presheaf morphism commutes with
postcomposition by a morphism of sheaves. -/
theorem uliftYonedaHom_comp {T : BigFppfOver B S hS} {Z Z' : FppfSheaf B S hS}
    (h : (fppfYoneda B S hS).obj T ⟶ Z) (k : Z ⟶ Z') :
    uliftYonedaHom B S hS (h ≫ k) = uliftYonedaHom B S hS h ≫ k.hom :=
  (Category.assoc _ _ _).symm

/-- Naturality of the identification: precomposing a sheaf morphism with a morphism of
sheafified representables precomposes the underlying presheaf morphism with the corresponding
morphism of universe-lifted representables. -/
theorem uliftYonedaHom_naturality {T T' : BigFppfOver B S hS} (g : T ⟶ T') :
    (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).map g ≫
        ((fppfYonedaCompSheafToPresheaf' B S hS).app T').inv =
      ((fppfYonedaCompSheafToPresheaf' B S hS).app T).inv ≫ ((fppfYoneda B S hS).map g).hom :=
  (fppfYonedaCompSheafToPresheaf' B S hS).inv.naturality g

/-- Precomposing a sheaf morphism with a morphism of sheafified representables precomposes its
presheaf reading with the corresponding morphism of universe-lifted representables. -/
theorem uliftYonedaHom_map_comp {T T' : BigFppfOver B S hS} {Z : FppfSheaf B S hS}
    (g : T ⟶ T') (h : (fppfYoneda B S hS).obj T' ⟶ Z) :
    uliftYonedaHom B S hS ((fppfYoneda B S hS).map g ≫ h) =
      (uliftYoneda.{u + 1}).map g ≫ uliftYonedaHom B S hS h := by
  change ((fppfYonedaCompSheafToPresheaf' B S hS).app T).inv ≫
      ((fppfYoneda B S hS).map g).hom ≫ h.hom = _
  rw [← Category.assoc, ← uliftYonedaHom_naturality B S hS g, Category.assoc]
  rfl

/-- The underlying square of presheaves of a cartesian square of fppf sheaves whose top row is
a morphism of sheafified representables, read along the universe-lifted Yoneda embedding. -/
theorem isPullback_uliftYonedaHom {T T' : BigFppfOver B S hS} {Z Z' : FppfSheaf B S hS}
    {fst : (fppfYoneda B S hS).obj T ⟶ Z} {snd : T ⟶ T'} {f : Z ⟶ Z'}
    {g : (fppfYoneda B S hS).obj T' ⟶ Z'}
    (h : IsPullback fst ((fppfYoneda B S hS).map snd) f g) :
    IsPullback (uliftYonedaHom B S hS fst) ((uliftYoneda.{u + 1}).map snd) f.hom
      (uliftYonedaHom B S hS g) := by
  have hp := h.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
  refine hp.of_iso' ((fppfYonedaCompSheafToPresheaf' B S hS).app T).symm
    (Iso.refl _) ((fppfYonedaCompSheafToPresheaf' B S hS).app T').symm (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).symm
  · exact (uliftYonedaHom_naturality B S hS snd).symm
  · simp
  · exact (Category.comp_id _).symm

/-! ### The scheme-theoretic image of a quasi-compact morphism of the site -/

/-- The scheme-theoretic image of a morphism of the big fppf site of `S` with affine target is
affine. -/
theorem isAffine_schemeImageObj {W T : BigFppfOver B S hS} (a : W ⟶ T)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (Space.schemeImageObj B S hS a)) := by
  have _ := hT
  exact (IsClosedImmersion.isAffine_surjective_of_isAffine
    (((BigFppfOver.toScheme B S hS).map a).imageι)).1

/-- A morphism of the big fppf site of `S` out of a quasi-compact object dominates its
scheme-theoretic image scheme-theoretically, when the target is affine. -/
theorem isSchemeTheoreticallyDominant_toSchemeImageObj {W T : BigFppfOver B S hS} (a : W ⟶ T)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hW : CompactSpace ((BigFppfOver.toScheme B S hS).obj W)) :
    IsSchemeTheoreticallyDominant
      ((BigFppfOver.toScheme B S hS).map (Space.toSchemeImageObj B S hS a)) := by
  have _ := hW
  exact Space.isSchemeTheoreticallyDominant_of_factor_schemeImage B S hS a
    (Space.schemeImageObjι B S hS a) (Space.toSchemeImageObj B S hS a) (Iso.refl _)
    (by rw [Space.schemeImageObjι_toScheme]; exact (Category.id_comp _).symm)
    (Space.toSchemeImageObj_comp_schemeImageObjι B S hS a) hT inferInstance

/-! ### A kernel pair of presheaves with étale projection is an étale equivalence relation -/

/-- If `t, r : R ⟶ Z` are morphisms of the big fppf site of `S` whose images under the
universe-lifted Yoneda embedding form a kernel pair of a morphism of presheaves out of `Z`, and
one of the two projections is étale, then the pair is an étale equivalence relation on `Z` over
`S` in the sense of Stacks 02WS. -/
@[sga "3 IV 3.4.3" "special case"]
theorem isEtaleEquivalenceRelation_of_isKernelPair {Z R : BigFppfOver B S hS} (t r : R ⟶ Z)
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    {g : (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).obj Z ⟶ W}
    (hker : IsPullback ((uliftYoneda.{u + 1}).map t) ((uliftYoneda.{u + 1}).map r) g g)
    (hret : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map r)) :
    Stacks.Groupoids.IsEtaleEquivalenceRelation (Space.relation B S hS r t) := by
  classical
  let H := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)
  let ff : H.FullyFaithful := ULiftYoneda.fullyFaithful (BigFppfOver B S hS)
  let _ : H.Full := ff.full
  let _ : H.Faithful := ff.faithful
  let _ : HasPullbacks (BigFppfOver B S hS) := inferInstance
  have hkp : IsKernelPair g (H.map t) (H.map r) := hker
  have hpre : IsEquivalenceRelation (H.map t) (H.map r) :=
    EquivalenceRelation.isEquivalenceRelation
      (IsKernelPair.equivalenceRelation g (H.map t) (H.map r)
        (pullback.isLimit (H.map r) (H.map t)) hkp)
  obtain ⟨esite⟩ := (isEquivalenceRelation_of_map H t r hpre).nonempty_equivalenceRelation
  have hsymm : esite.s ≫ esite.s = 𝟙 R := by
    refine esite.right_cancellation _ _ ?_ ?_
    · rw [Category.assoc, esite.symmetry₁, esite.symmetry₂, Category.id_comp]
    · rw [Category.assoc, esite.symmetry₂, esite.symmetry₁, Category.id_comp]
  have _ : IsIso esite.s := ⟨esite.s, hsymm, hsymm⟩
  have htet : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map t) := by
    have _ : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map r) := hret
    have hmap := (BigFppfOver.toScheme B S hS).map_comp esite.s r
    rw [esite.symmetry₂] at hmap
    rw [hmap]
    infer_instance
  exact Space.isEtaleEquivalenceRelation_of_embedding B S hS r t H (Iso.refl _)
    (by simpa using hpre) htet hret

/-! ### Represented base changes of a representable étale chart -/

/-- A chart of fppf sheaves which is representable by objects of the site and étale is étale after
every represented base change. -/
theorem relative_etaleOnSite_of_isRepresentableEtale {X Y : FppfSheaf B S hS} (c : Y ⟶ X)
    (hc : (fppfYoneda B S hS).relativelyRepresentable c)
    (hce : IsRepresentableEtale B S hS c) :
    (Space.etaleOnSite B S hS).relative (uliftYoneda.{u + 1}) c.hom := by
  obtain ⟨hrep, het⟩ := hce
  refine ⟨(relativelyRepresentable_sheafifiedYoneda_iff_uliftYoneda B S hS c).mp hc, ?_⟩
  intro T R g fst snd hpb
  refine (Space.isEtaleULift_uliftYoneda_map_iff B S hS snd).mp ?_
  refine isEtaleULift_of_iso_source B S hS
    (hpb.flip.isoIsPullback _ _ (IsPullback.of_hasPullback g c.hom)) ?_ (het T g)
  exact hpb.flip.isoIsPullback_hom_fst _ _ _

/-- A representable chart which is a surjection of fppf sheaves is surjective after every
represented base change. -/
theorem relative_surjectiveOnSite_of_isLocallySurjective {X Y : FppfSheaf B S hS} (c : Y ⟶ X)
    (hc : (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).relativelyRepresentable c.hom)
    (hcs : Sheaf.IsLocallySurjective c) :
    (Space.surjectiveOnSite B S hS).relative (uliftYoneda.{u + 1}) c.hom := by
  refine ⟨hc, ?_⟩
  intro T R g fst snd hpb
  have _ : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) c.hom := hcs
  refine ⟨fun x => ?_⟩
  obtain ⟨V, h, ⟨t, ht⟩, hx⟩ := BigFppfOver.exists_mem_range_of_mem_topology B S hS
    (Presheaf.imageSieve_mem (BigFppfOver.topology B S hS) c.hom
      (uliftYonedaEquiv.{u + 1} g)) x
  let ff : (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).FullyFaithful :=
    ULiftYoneda.fullyFaithful _
  have hcomm : uliftYonedaEquiv.{u + 1}.symm t ≫ c.hom =
      (uliftYoneda.{u + 1}).map h ≫ g := by
    rw [uliftYonedaEquiv_symm_comp, ht, uliftYonedaEquiv_symm_map]
    simp
  let k : V ⟶ R := ff.preimage (hpb.lift (uliftYonedaEquiv.{u + 1}.symm t)
    ((uliftYoneda.{u + 1}).map h) hcomm)
  have hk : k ≫ snd = h := by
    apply ff.map_injective
    rw [Functor.map_comp, ff.map_preimage]
    exact hpb.lift_snd _ _ _
  obtain ⟨y, hy⟩ := hx
  refine ⟨(BigFppfOver.toScheme B S hS).map k y, ?_⟩
  have hcomp : (BigFppfOver.toScheme B S hS).map k ≫ (BigFppfOver.toScheme B S hS).map snd =
      (BigFppfOver.toScheme B S hS).map h := by
    rw [← Functor.map_comp, hk]
  exact (congrArg (fun m : (BigFppfOver.toScheme B S hS).obj V ⟶
    (BigFppfOver.toScheme B S hS).obj T => m y) hcomp).trans hy

section Stages

variable {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : I ⥤ BigAffineFppf B S hS)
  (hD : ∀ ⦃i j : I⦄ (g : i ⟶ j),
    Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D.map g)))
  {Y X : FppfSheaf B S hS}
  (e : Y ≅ colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙ fppfYoneda B S hS))

/-- The object of the site underlying the `i`-th stage of a presentation. -/
abbrev stageObj (i : I) : BigFppfOver B S hS :=
  (BigAffineFppf.inclusion B S hS).obj (D.obj i)

/-- The `i`-th stage of a presentation, mapping to the presented sheaf. -/
noncomputable def stageMap' (i : I) :
    (fppfYoneda B S hS).obj (stageObj B S hS D i) ⟶ Y :=
  colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙ fppfYoneda B S hS) i ≫ e.inv

include hD in
/-- Each stage map of a presentation is relatively representable. -/
theorem relativelyRepresentable_stageMap (i : I) :
    (fppfYoneda B S hS).relativelyRepresentable (stageMap' B S hS D e i) :=
  relativelyRepresentable_colimitι B S hS D hD Y e.symm i

include hD in
/-- Each stage map of a presentation is a thickening after every represented base change. -/
theorem isThickening_stageMap (i : I) :
    (MorphismProperty.relative (fppfYoneda B S hS)
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)))
      (stageMap' B S hS D e i) :=
  isThickening_colimitι B S hS D hD Y e.symm i

/-- The transition morphism of the site between two stages of a presentation. -/
abbrev stageTransition {i j : I} (g : i ⟶ j) : stageObj B S hS D i ⟶ stageObj B S hS D j :=
  (BigAffineFppf.inclusion B S hS).map (D.map g)

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- An earlier stage map of a presentation is the later one precomposed with the transition
morphism. -/
@[reassoc]
theorem stageMap_eq_stageTransition_comp {i j : I} (g : i ⟶ j) :
    (fppfYoneda B S hS).map (stageTransition B S hS D g) ≫ stageMap' B S hS D e j =
      stageMap' B S hS D e i := by
  rw [stageMap', stageMap', ← Category.assoc]
  congr 1
  exact colimit.w (D ⋙ BigAffineFppf.inclusion B S hS ⋙ fppfYoneda B S hS) g

include hD in
/-- A stage map of a presentation, read as a morphism of universe-lifted presheaves, is a
representable thickening. -/
theorem relative_isThickening_uliftYonedaHom_stageMap (i : I) :
    (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1})
      (uliftYonedaHom B S hS (stageMap' B S hS D e i)) :=
  MorphismProperty.RespectsIso.precomp _
    ((fppfYonedaCompSheafToPresheaf' B S hS).app (stageObj B S hS D i)).inv
    (stageMap' B S hS D e i).hom
    ((relative_fppfYoneda_iff_uliftYoneda' B S hS _ (stageMap' B S hS D e i)).mp
      (isThickening_stageMap B S hS D hD e i))

include hD in
/-- The inclusion into the atlas of a closed subscheme of a stage is a representable closed
immersion. -/
theorem relative_isClosedImmersion_stageSub {j : I} {Z : BigFppfOver B S hS}
    (zq : Z ⟶ stageObj B S hS D j)
    (hzq : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map zq)) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1})
      ((uliftYoneda.{u + 1}).map zq ≫ uliftYonedaHom B S hS (stageMap' B S hS D e j)) := by
  have _ : MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  refine MorphismProperty.IsStableUnderComposition.comp_mem _ _
    (MorphismProperty.relative_map hzq) ?_
  have hle : (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) ≤
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) :=
    fun _ _ k hk ↦ hk.1
  exact MorphismProperty.relative_monotone hle _
    (relative_isThickening_uliftYonedaHom_stageMap B S hS D hD e j)

variable (c : Y ⟶ X) (hc : (fppfYoneda B S hS).relativelyRepresentable c)

/-- The object of the site representing the fibre product `Y_i ×_X Y` of the `i`-th stage of a
presentation of `Y` with `Y` itself, over `X`. -/
noncomputable def overlapObj (i : I) : BigFppfOver B S hS :=
  hc.pullback (stageMap' B S hS D e i ≫ c)

/-- The projection `Y_i ×_X Y ⟶ Y`. -/
noncomputable def overlapToSheaf (i : I) :
    (fppfYoneda B S hS).obj (overlapObj B S hS D e c hc i) ⟶ Y :=
  hc.fst (stageMap' B S hS D e i ≫ c)

/-- The projection `Y_i ×_X Y ⟶ Y_i`. -/
noncomputable def overlapToStage (i : I) :
    overlapObj B S hS D e c hc i ⟶ stageObj B S hS D i :=
  hc.snd (stageMap' B S hS D e i ≫ c)

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The square exhibiting `AlgebraicGeometry.FormalSpace.overlapObj` as the fibre product
`Y_i ×_X Y` is cartesian. -/
theorem isPullback_overlap (i : I) :
    IsPullback (overlapToSheaf B S hS D e c hc i)
      ((fppfYoneda B S hS).map (overlapToStage B S hS D e c hc i)) c
      (stageMap' B S hS D e i ≫ c) :=
  hc.isPullback (stageMap' B S hS D e i ≫ c)

/-- The transition morphism between the overlaps of two stages of a presentation with the whole
atlas, over the atlas. -/
noncomputable def overlapTransition {i j : I} (g : i ⟶ j) :
    overlapObj B S hS D e c hc i ⟶ overlapObj B S hS D e c hc j :=
  (fppfYoneda B S hS).preimage
    ((isPullback_overlap B S hS D e c hc j).lift
      (overlapToSheaf B S hS D e c hc i)
      ((fppfYoneda B S hS).map
        (overlapToStage B S hS D e c hc i ≫ stageTransition B S hS D g))
      (by
        rw [Functor.map_comp, Category.assoc,
          stageMap_eq_stageTransition_comp_assoc B S hS D e g]
        exact (isPullback_overlap B S hS D e c hc i).w))

/-- The scheme underlying an affine object of the site is affine. -/
private theorem isAffine_toScheme_inclusion_obj (A : BigAffineFppf B S hS) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj A)) := by
  change IsAffine ((BigAffineFppf.toScheme B S hS).obj A)
  infer_instance

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The transition morphism between two overlaps commutes with their projections to `Y`. -/
theorem overlapTransition_comp_overlapToSheaf {i j : I} (g : i ⟶ j) :
    (fppfYoneda B S hS).map (overlapTransition B S hS D e c hc g) ≫
        overlapToSheaf B S hS D e c hc j =
      overlapToSheaf B S hS D e c hc i := by
  rw [overlapTransition, Functor.map_preimage]
  exact (isPullback_overlap B S hS D e c hc j).lift_fst _ _ _

include hD in
/-- For a quasi-separated `X`, the fibre product `Y_i ×_X Y` of the `i`-th stage of a
presentation of the atlas `Y` with `Y` itself has quasi-compact underlying scheme. -/
theorem compactSpace_overlapObj (hqs : IsQuasiSeparated B S hS X) (i : I) :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj (overlapObj B S hS D e c hc i)) := by
  classical
  let F := fppfYoneda B S hS
  let G := BigFppfOver.toScheme B S hS
  obtain ⟨V, sndV, fstV, hsq1⟩ := relativelyRepresentable_stageMap B S hS D hD e i
    (overlapToSheaf B S hS D e c hc i)
  have hthick : Stacks.Thickenings.IsThickening (G.map sndV) :=
    (isThickening_stageMap B S hS D hD e i).property
      (overlapToSheaf B S hS D e c hc i) fstV sndV hsq1
  have hsq : IsPullback fstV
      (F.map (sndV ≫ overlapToStage B S hS D e c hc i))
      (stageMap' B S hS D e i ≫ c) (stageMap' B S hS D e i ≫ c) := by
    simpa only [F.map_comp] using hsq1.paste_vert (isPullback_overlap B S hS D e c hc i)
  have hVcompact : CompactSpace (G.obj V) := by
    have haff := isAffine_toScheme_inclusion_obj B S hS (D.obj i)
    refine hqs (stageObj B S hS D i) (stageObj B S hS D i) V
      (stageMap' B S hS D e i ≫ c) (stageMap' B S hS D e i ≫ c)
      (F.preimage fstV) (sndV ≫ overlapToStage B S hS D e c hc i) haff haff ?_
    rwa [F.map_preimage]
  have _ := hVcompact
  exact hthick.2.compactSpace (G.map sndV).base.hom.continuous_toFun

include hD in
/-- A morphism to the presented sheaf from a sheaf represented by a quasi-compact object of the
site factors through one stage of the presentation. -/
theorem exists_factor_stageMap {T : BigFppfOver B S hS}
    (hT : CompactSpace ((BigFppfOver.toScheme B S hS).obj T))
    (g : (fppfYoneda B S hS).obj T ⟶ Y) :
    ∃ (j : I) (a : T ⟶ stageObj B S hS D j),
      (fppfYoneda B S hS).map a ≫ stageMap' B S hS D e j = g := by
  classical
  let J := BigFppfOver.topology B S hS
  let F := fppfYoneda B S hS
  let _ := hT
  have hUqc : J.IsQuasiCompactObject T :=
    isQuasiCompactObject_over_of_compact_scheme B S hS T
  obtain ⟨j, h, hh⟩ := compact_map_factors_through_filtered_colimit
    (D ⋙ BigAffineFppf.inclusion B S hS ⋙ F)
    (fun _ _ t ↦ stageTransition_mono_sheafifiedYoneda' B S hS D hD t) T hUqc (g ≫ e.hom)
  refine ⟨j, F.preimage h, ?_⟩
  rw [F.map_preimage, stageMap']
  apply (cancel_mono e.hom).1
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hh

include hD hc in
/-- Let `X` be quasi-separated and let `c : Y ⟶ X` be a representable étale morphism from an affine
formal algebraic space presented as `colim Y_i`. For each `i` there is a later stage `Y_j`, an
affine closed subscheme `Z ⊆ Y_j` containing `Y_i`, and an object `R` of the site which is a
kernel pair of the composite `Z ⟶ Y ⟶ X` with étale projections — the restriction to `Z` of the
étale equivalence relation `Y ×_X Y`. -/
theorem exists_invariantStage (hqs : IsQuasiSeparated B S hS X)
    (hcet : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) c.hom)
    (i : I) :
    ∃ (j : I) (Z R : BigFppfOver B S hS) (zq : Z ⟶ stageObj B S hS D j)
      (si : stageObj B S hS D i ⟶ Z) (t r : R ⟶ Z)
      (l : overlapObj B S hS D e c hc i ⟶ Z),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z) ∧
      AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map zq) ∧
      (uliftYoneda.{u + 1}).map si ≫
          ((uliftYoneda.{u + 1}).map zq ≫ uliftYonedaHom B S hS (stageMap' B S hS D e j)) =
        uliftYonedaHom B S hS (stageMap' B S hS D e i) ∧
      IsPullback ((uliftYoneda.{u + 1}).map t) ((uliftYoneda.{u + 1}).map r)
        (((uliftYoneda.{u + 1}).map zq ≫
          uliftYonedaHom B S hS (stageMap' B S hS D e j)) ≫ c.hom)
        (((uliftYoneda.{u + 1}).map zq ≫
          uliftYonedaHom B S hS (stageMap' B S hS D e j)) ≫ c.hom) ∧
      AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map r) ∧
      IsPullback ((uliftYoneda.{u + 1}).map t ≫
          ((uliftYoneda.{u + 1}).map zq ≫ uliftYonedaHom B S hS (stageMap' B S hS D e j)))
        ((uliftYoneda.{u + 1}).map r) c.hom
        (((uliftYoneda.{u + 1}).map zq ≫
          uliftYonedaHom B S hS (stageMap' B S hS D e j)) ≫ c.hom) ∧
      (uliftYoneda.{u + 1}).map l ≫
          ((uliftYoneda.{u + 1}).map zq ≫ uliftYonedaHom B S hS (stageMap' B S hS D e j)) =
        uliftYonedaHom B S hS (overlapToSheaf B S hS D e c hc i) ∧
      IsSchemeTheoreticallyDominant ((BigFppfOver.toScheme B S hS).map l) := by
  classical
  let F := fppfYoneda B S hS
  let G := BigFppfOver.toScheme B S hS
  let H := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)
  let ff : H.FullyFaithful := ULiftYoneda.fullyFaithful (BigFppfOver B S hS)
  let _ : H.Full := ff.full
  let _ : H.Faithful := ff.faithful
  have hWcompact : CompactSpace (G.obj (overlapObj B S hS D e c hc i)) :=
    compactSpace_overlapObj B S hS D hD e c hc hqs i
  let _ := hWcompact
  obtain ⟨j, a, ha⟩ := exists_factor_stageMap B S hS D hD e hWcompact
    (overlapToSheaf B S hS D e c hc i)
  have haffj := isAffine_toScheme_inclusion_obj B S hS (D.obj j)
  set Z := Space.schemeImageObj B S hS a with hZdef
  have haffZ : IsAffine (G.obj Z) := isAffine_schemeImageObj B S hS a haffj
  let zq : Z ⟶ stageObj B S hS D j := Space.schemeImageObjι B S hS a
  let l : overlapObj B S hS D e c hc i ⟶ Z := Space.toSchemeImageObj B S hS a
  have hlzq : l ≫ zq = a := Space.toSchemeImageObj_comp_schemeImageObjι B S hS a
  set s := uliftYonedaHom B S hS (stageMap' B S hS D e i) with hsdef
  set p := uliftYonedaHom B S hS (overlapToSheaf B S hS D e c hc i) with hpdef
  have hp : IsPullback p (H.map (overlapToStage B S hS D e c hc i)) c.hom (s ≫ c.hom) := by
    have := isPullback_uliftYonedaHom B S hS (isPullback_overlap B S hS D e c hc i)
    rwa [uliftYonedaHom_comp] at this
  set z := H.map zq ≫ uliftYonedaHom B S hS (stageMap' B S hS D e j) with hzdef
  have hap : H.map a ≫ uliftYonedaHom B S hS (stageMap' B S hS D e j) = p := by
    rw [← uliftYonedaHom_map_comp, ha]
  have hlz : H.map l ≫ z = p := by
    rw [hzdef, ← Category.assoc, ← H.map_comp, hlzq, hap]
  have hclosed : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) G).relative H z :=
    relative_isClosedImmersion_stageSub B S hS D hD e zq
      (Space.isClosedImmersion_schemeImageObjι B S hS a)
  have hdom : IsSchemeTheoreticallyDominant (G.map l) :=
    isSchemeTheoreticallyDominant_toSchemeImageObj B S hS a haffj hWcompact
  have hlqc : QuasiCompact (G.map l) := inferInstance
  obtain ⟨R, t, r, hrel, hker, hret⟩ :=
    Space.exists_invariantImage_relation B S hS c.hom hcet s p
      (overlapToStage B S hS D e c hc i) hp z hclosed l hdom hlqc hlz
  have hsec : H.map (ff.preimage (hp.lift s (𝟙 _) (by simp)) ≫ l) ≫ z = s := by
    rw [H.map_comp, Category.assoc, hlz, ff.map_preimage]
    exact hp.lift_fst _ _ _
  exact ⟨j, Z, R, zq, ff.preimage (hp.lift s (𝟙 _) (by simp)) ≫ l, t, r, l,
    haffZ, Space.isClosedImmersion_schemeImageObjι B S hS a, hsec, hker, hret, hrel, hlz, hdom⟩

include hD hc in
/-- Let `X` be quasi-separated and let `c : Y ⟶ X` be a chart which is representable by objects of
the site and étale, with `Y` an affine formal algebraic space presented as `colim Y_i`. Then
there is a family `(Z_i)` of objects of the site, indexed by the same directed set, together with
inclusions `Z_i ⊆ Y` such that

* each `Z_i ⟶ Y` is a representable thickening;
* each stage `Y_i` of the presentation factors through `Z_i`;
* the family is monotone: `Z_i ⊆ Z_j` for `i ≤ j`, compatibly with the inclusions into `Y`;
* each `Z_i` is invariant for the étale equivalence relation of `c`, in the sense that the
  fibre product `Y ×_X Z_i` is an object of the site whose projection to `Y` factors
  through `Z_i`. -/
theorem exists_invariantStageSystem (hqs : IsQuasiSeparated B S hS X)
    (hcet : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) c.hom) :
    ∃ (Z : I → BigFppfOver B S hS) (z : ∀ i, (fppfYoneda B S hS).obj (Z i) ⟶ Y),
      (∀ i, Space.IsRepresentableThickeningULift.{u + 1} B S hS
        (uliftYonedaHom B S hS (z i))) ∧
      (∀ i, ∃ si : stageObj B S hS D i ⟶ Z i,
        (fppfYoneda B S hS).map si ≫ z i = stageMap' B S hS D e i) ∧
      (∀ ⦃i j : I⦄, (i ⟶ j) → ∃ w : Z i ⟶ Z j,
        (fppfYoneda B S hS).map w ≫ z j = z i) ∧
      (∀ i, ∃ (R : BigFppfOver B S hS) (t r : R ⟶ Z i),
        IsPullback ((uliftYoneda.{u + 1}).map t ≫ uliftYonedaHom B S hS (z i))
          ((uliftYoneda.{u + 1}).map r) c.hom
          (uliftYonedaHom B S hS (z i) ≫ c.hom)) := by
  classical
  choose jj ZZ RR zq ss tt rr ll _haff hci hsec _hker _hret hrel hlz hdom using
    fun i : I ↦ exists_invariantStage B S hS D hD e c hc hqs hcet i
  have hz (i : I) : uliftYonedaHom B S hS
      ((fppfYoneda B S hS).map (zq i) ≫ stageMap' B S hS D e (jj i)) =
      (uliftYoneda.{u + 1}).map (zq i) ≫
        uliftYonedaHom B S hS (stageMap' B S hS D e (jj i)) :=
    uliftYonedaHom_map_comp B S hS (zq i) (stageMap' B S hS D e (jj i))
  refine ⟨ZZ, fun i ↦ (fppfYoneda B S hS).map (zq i) ≫ stageMap' B S hS D e (jj i),
    fun i ↦ ?_, fun i ↦ ⟨ss i, ?_⟩, fun i j g ↦ ?_,
    fun i ↦ ⟨RR i, tt i, rr i, ?_⟩⟩
  · rw [hz i]
    exact Space.relative_isThickening_of_factor B S hS
      (uliftYonedaHom B S hS (stageMap' B S hS D e i))
      (relative_isThickening_uliftYonedaHom_stageMap B S hS D hD e i) _
      (relative_isClosedImmersion_stageSub B S hS D hD e (zq i) (hci i)) (ss i) (hsec i)
  · refine uliftYonedaHom_injective B S hS ?_
    rw [uliftYonedaHom_map_comp B S hS, hz i]
    exact hsec i
  · have hab : (uliftYoneda.{u + 1}).map (ll i) ≫
        ((uliftYoneda.{u + 1}).map (zq i) ≫
          uliftYonedaHom B S hS (stageMap' B S hS D e (jj i))) =
        (uliftYoneda.{u + 1}).map (overlapTransition B S hS D e c hc g ≫ ll j) ≫
        ((uliftYoneda.{u + 1}).map (zq j) ≫
          uliftYonedaHom B S hS (stageMap' B S hS D e (jj j))) := by
      rw [hlz i, Functor.map_comp, Category.assoc, hlz j,
        ← uliftYonedaHom_map_comp B S hS,
        overlapTransition_comp_overlapToSheaf B S hS D e c hc g]
    obtain ⟨w, hw⟩ := Space.exists_factor_of_isSchemeTheoreticallyDominant B S hS
      ((uliftYoneda.{u + 1}).map (zq j) ≫
        uliftYonedaHom B S hS (stageMap' B S hS D e (jj j)))
      (relative_isClosedImmersion_stageSub B S hS D hD e (zq j) (hci j))
      (ll i) (hdom i)
      ((uliftYoneda.{u + 1}).map (zq i) ≫
        uliftYonedaHom B S hS (stageMap' B S hS D e (jj i)))
      (overlapTransition B S hS D e c hc g ≫ ll j) hab
    refine ⟨w, uliftYonedaHom_injective B S hS ?_⟩
    rwa [uliftYonedaHom_map_comp B S hS, hz j, hz i]
  · rw [hz i]
    exact hrel i

end Stages

end AlgebraicGeometry.FormalSpace

end
