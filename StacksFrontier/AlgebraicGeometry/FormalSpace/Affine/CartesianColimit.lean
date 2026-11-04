module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Connected
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered
public import Mathlib.CategoryTheory.ShrinkYoneda
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Factorization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.MorphismOfAffines
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.RepresentableAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SetTheoreticSmall
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationSizeBounds
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelativeSizeBound
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Precoverage
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical

/-!
# Colimits of cartesian systems of affine stages are representable and affine

Let `S` be a scheme contained in a big fppf site `B`, let `(Y_i)` and `(X_i)` be directed systems
of affine objects of the site, indexed by the same directed set, the first one with thickening
transition morphisms, and let `X_i ⟶ Y_i` be a morphism of systems whose naturality squares are
cartesian. If `Y = colim Y_i` is an affine formal algebraic space and the sizes of the `X_i` are
bounded below the cutoff, then the induced morphism `colim X_i ⟶ Y` is representable by schemes
and every represented base change of it is affine. This is the representability half of
Stacks 0AL1 without the finite type condition: an inverse system of algebras `(B_i)` over the
stages of `Y` with `B_j = B_i ⊗ O(Y_j)` gives a representable affine morphism to `Y`.

The stage squares `X_i = Y_i ×_Y colim X_j` are cartesian because a filtered colimit of sheaves of
sets is exact and the transition squares are cartesian. A point of `Y` out of an affine object
factors through a stage (Stacks 0AIA), so the base change along it is a fibre product of affine
objects of the site; over an arbitrary object these charts glue by relative Tag 03JH under a
uniform size bound, which the bound on the stages supplies.

## Main results

* `AlgebraicGeometry.FormalSpace.CartesianColimit.isPullback_stage`: the stage squares are
  cartesian.
* `AlgebraicGeometry.FormalSpace.CartesianColimit.relative_of_affineBaseChanges`:
  representability with a Zariski-local property from the affine points of the target, under a
  size bound on the charts or a regular cutoff.
* `AlgebraicGeometry.FormalSpace.CartesianColimit.relative_isAffineHom_colimMap`: the colimit
  morphism is representable and affine.

## Implementation notes

The auxiliary statements about filtered colimits, smallness of sections and the glueing over an
open covering of a test object are shared with
`StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.FiniteTypeClassification`, whose finite type
glueing is the special case of `relative_of_affineBaseChanges` in which finite type bounds the
size of each chart by that of the test object.

## References

* [Stacks Project, Tag 0AL1](https://stacks.math.columbia.edu/tag/0AL1)
* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.FormalSpace.CartesianColimit

/-- The transition morphisms out of a fixed stage, as a morphism from the constant diagram on
the category under that stage. -/
def underTransition {J : Type w} [Category J] {C : Type u} [Category.{v} C]
    (F : J ⥤ C) (i : J) :
    (Functor.const (Under i)).obj (F.obj i) ⟶ Under.forget i ⋙ F where
  app j := F.map j.hom
  naturality j k f := by
    change 𝟙 _ ≫ F.map k.hom = F.map j.hom ≫ F.map f.right
    rw [Category.id_comp, ← F.map_comp, Under.w f]

/-- The colimit of a constant diagram over a connected category is its value. -/
noncomputable def constantColimitIso
    (J : Type w) [Category J] [IsConnected J]
    {C : Type u} [Category.{v} C] (X : C)
    [HasColimit ((Functor.const J).obj X)] :
    colimit ((Functor.const J).obj X) ≅ X :=
  (colimit.isColimit _).coconePointUniqueUpToIso (isColimitConstCocone J X)

/-- The coprojections of a constant diagram compose with `constantColimitIso` to the identity. -/
@[reassoc] theorem constantColimitIso_ι
    (J : Type w) [Category J] [IsConnected J]
    {C : Type u} [Category.{v} C] (X : C)
    [HasColimit ((Functor.const J).obj X)] (j : J) :
    colimit.ι ((Functor.const J).obj X) j ≫ (constantColimitIso J X).hom = 𝟙 X :=
  colimit.comp_coconePointUniqueUpToIso_hom (isColimitConstCocone J X) j

/-- An equifibered morphism of diagrams over a category in which colimits under each object are
exact has cartesian squares from each stage to the colimit. -/
theorem equifibered_colimit_isPullback
    {J : Type w} [Category J] {C : Type u} [Category.{v} C]
    [HasPullbacks C] [HasColimitsOfShape J C]
    {F G : J ⥤ C} (α : F ⟶ G) (hα : α.Equifibered)
    (i : J) [(Under.forget i).Final] [IsConnected (Under i)]
    [HasColimitsOfShape (Under i) C] [HasExactColimitsOfShape (Under i) C] :
    IsPullback (colimit.ι F i) (α.app i) (colim.map α) (colimit.ι G i) := by
  let β := Functor.whiskerLeft (Under.forget i) α
  let γ := (Functor.const (Under i)).map (α.app i)
  have hp : IsPullback (underTransition F i) γ β (underTransition G i) :=
    IsPullback.of_forall_isPullback_app (fun j => hα j.hom)
  have hq := hp.map (colim : (Under i ⥤ C) ⥤ C)
  apply hq.of_iso (constantColimitIso (Under i) (F.obj i))
    (Functor.Final.colimitIso (Under.forget i) F)
    (constantColimitIso (Under i) (G.obj i))
    (Functor.Final.colimitIso (Under.forget i) G)
  · refine colimit.hom_ext fun j => ?_
    simp only [colimit.ι_map_assoc, underTransition,
      Functor.Final.colimitIso_hom, colimit.ι_pre,
      constantColimitIso_ι_assoc]
    exact (colimit.w F j.hom).trans (Category.id_comp _).symm
  · refine colimit.hom_ext fun j => ?_
    simp only [colimit.ι_map_assoc, γ,
      Functor.const_map_app, constantColimitIso_ι, constantColimitIso_ι_assoc]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · refine colimit.hom_ext fun j => ?_
    simp only [colimit.ι_map_assoc, β,
      Functor.whiskerLeft_app, Functor.Final.colimitIso_hom, colimit.ι_pre,
      colimit.ι_pre_assoc, colimit.ι_map]
  · refine colimit.hom_ext fun j => ?_
    simp only [colimit.ι_map_assoc, underTransition,
      Functor.Final.colimitIso_hom, colimit.ι_pre,
      constantColimitIso_ι_assoc]
    exact (colimit.w G j.hom).trans (Category.id_comp _).symm


/-- The sheafified Yoneda embedding of the big fppf site, read in presheaves, is the
universe-lifted Yoneda embedding. -/
noncomputable def sheafifiedYonedaToUliftPresheafIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS) ⋙
      sheafToPresheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1)) ≅
        uliftYoneda.{u + 1} := by
  let J := AlgebraicGeometry.BigFppfOver.topology B S hS
  letI : J.Subcanonical := by
    apply GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj
    intro T
    exact (isSheaf_iff_isSheaf_of_type _ _).mp
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T).isSheaf
  let Gl := presheafToSheaf J (Type (u + 1))
  let Gr := sheafToPresheaf J (Type (u + 1))
  let adj : Gl ⊣ Gr := sheafificationAdjunction J (Type (u + 1))
  letI : IsIso adj.counit := inferInstance
  let e : Sheaf.sheafifiedYoneda J ≅ GrothendieckTopology.uliftYoneda.{u + 1} J :=
    (Functor.isoWhiskerRight
      (GrothendieckTopology.uliftYonedaCompSheafToPresheaf.{u + 1} J).symm Gl) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (asIso adj.counit) ≪≫ Functor.rightUnitor _
  exact (Functor.isoWhiskerRight e Gr) ≪≫
    GrothendieckTopology.uliftYonedaCompSheafToPresheaf.{u + 1} J

/-- The big fppf site over `S` is essentially small. -/
theorem essentiallySmall_bigFppfOver
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    EssentiallySmall.{u} (AlgebraicGeometry.BigFppfOver B S hS) := by
  let : ObjectProperty.EssentiallySmall.{u} (_root_.AlgebraicGeometry.schemeSizeBelow B.cutoff) :=
    essentiallySmall_schemeSizeBelow B.cutoff B.aleph0_lt_cutoff.le
  let : EssentiallySmall.{u} B.Schemes := inferInstance
  show EssentiallySmall.{u} (CostructuredArrow (𝟭 B.Schemes) (B.obj hS))
  infer_instance


/-- A sheaf receiving a locally surjective morphism from a pointwise small presheaf on an
essentially small site is pointwise small. -/
alias small_sections_of_locallySurjective :=
  AlgebraicGeometry.FormalSpace.small_sections_of_locallySurjective


/-- A pointwise `u`-small functor to `Type (u + 1)` is the universe lift of its shrinking. -/
noncomputable def shrinkUliftIso
    {C : Type*} [Category C] (F : C ⥤ Type (u + 1))
    [FunctorToTypes.Small.{u} F] :
    FunctorToTypes.shrink.{u} F ⋙ uliftFunctor.{u + 1, u} ≅ F :=
  NatIso.ofComponents
    (fun T ↦ (Equiv.ulift.trans (equivShrink.{u} (F.obj T)).symm).toIso)
    (by
      intro T T' g
      ext x
      change (equivShrink.{u} _).symm
        ((equivShrink.{u} _) (F.map g ((equivShrink.{u} _).symm x.down))) = _
      exact (equivShrink.{u} _).symm_apply_apply _)


/-- If every base change of `f` along a morphism out of `G.obj V` is represented, and the
morphisms `G.obj V ⟶ X` form a small type, so do the morphisms `G.obj V ⟶ Y`. -/
theorem small_hom_of_represented_fibers
    {C D : Type*} [Category C] [Category D] [LocallySmall.{u} C]
    (G : C ⥤ D) [G.Full] [G.Faithful] {X Y : D} (f : Y ⟶ X)
    (V : C) [Small.{u} (G.obj V ⟶ X)]
    (hf : ∀ ξ : G.obj V ⟶ X, ∃ (W : C) (p : G.obj W ⟶ Y) (q : W ⟶ V),
      IsPullback p (G.map q) f ξ) : Small.{u} (G.obj V ⟶ Y) := by
  classical
  let Ξ := Shrink.{u} (G.obj V ⟶ X)
  let ξ : Ξ → (G.obj V ⟶ X) := (equivShrink.{u} _).symm
  choose W p q hp using fun t => hf (ξ t)
  let (t : Ξ) : Small.{u} (G.obj V ⟶ G.obj (W t)) :=
    small_of_surjective G.map_surjective
  let d : (Σ t : Ξ, G.obj V ⟶ G.obj (W t)) → (G.obj V ⟶ Y) :=
    fun z => z.2 ≫ p z.1
  apply small_of_surjective (f := d)
  intro a
  let t : Ξ := (equivShrink.{u} _) (a ≫ f)
  have ht : a ≫ f = 𝟙 (G.obj V) ≫ ξ t := by simp [ξ, t]
  exact ⟨⟨t, (hp t).lift a (𝟙 _) ht⟩, (hp t).lift_fst _ _ _⟩

/-- A sheaf satisfying the set-theoretic condition of Stacks 0AIS is pointwise small. -/
theorem small_of_setTheoreticCondition
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1)))
    (hX : _root_.AlgebraicGeometry.SatisfiesSetTheoreticCondition B S hS X) :
    FunctorToTypes.Small.{u} X.obj := by
  obtain ⟨U, R, hU, hR, ⟨eU⟩, heR, a, ha, g, hg⟩ := hX
  let := essentiallySmall_bigFppfOver B S hS
  let : FunctorToTypes.Small.{u} hU.obj := fun T => by
    have : Small.{u} (((uliftYoneda.{u + 1}).obj U).obj T) :=
      inferInstanceAs (Small.{u} (ULift.{u + 1} (T.unop ⟶ U)))
    exact small_of_injective (CategoryTheory.injective_of_mono (eU.hom.app T))
  let : Sheaf.IsLocallySurjective a := (Sheaf.isLocallySurjective_iff_epi a).mpr ha
  intro T
  exact small_sections_of_locallySurjective _ X.property a.hom T.unop

/-- A jointly surjective family of open immersions generates a covering sieve of the big fppf
site over `S`. -/
theorem openCover_mem_topology
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T : AlgebraicGeometry.BigFppfOver B S hS} {I : Type u}
    (V : I → AlgebraicGeometry.BigFppfOver B S hS) (f : ∀ i, V i ⟶ T)
    (hf : ∀ i, IsOpenImmersion ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (f i)))
    (hcov : ∀ t : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T,
      ∃ i, t ∈ Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (f i))) :
    Sieve.ofArrows V f ∈ AlgebraicGeometry.BigFppfOver.topology B S hS T := by
  show Sieve.ofArrows V f ∈ B.topology.over (B.obj hS) T
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  apply Precoverage.generate_mem_toGrothendieck
  rw [bigFppfPrecoverage_eq_comap, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
  apply (Scheme.ofArrows_mem_precoverage_iff _).mpr
  refine ⟨hcov, ?_⟩
  intro i
  have : IsOpenImmersion (B.inclusion.map (f i).left) := hf i
  exact ⟨inferInstance, inferInstance⟩

/-- A sheaf on the big fppf site over `S` whose sections over the affine objects are small is
pointwise small. -/
theorem small_sections_of_affine
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1)))
    (hF : ∀ U : AlgebraicGeometry.BigFppfOver B S hS,
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U) →
        Small.{u} (F.obj.obj (Opposite.op U))) : FunctorToTypes.Small.{u} F.obj := by
  classical
  intro T
  choose V a ha harange hV using fun U =>
    BigFppfOver.exists_affineOpen_restrict B S hS T.unop U
  have hcover := openCover_mem_topology B S hS V a ha (by
    intro y
    have hy : y ∈
        (⊤ : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T.unop).Opens) := trivial
    rw [← iSup_affineOpens_eq_top] at hy
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    refine ⟨U, ?_⟩
    rw [harange U]
    exact hU)
  let (i : ((BigFppfOver.toScheme B S hS).obj T.unop).affineOpens) :
      Small.{u} (F.obj.obj (Opposite.op (V i))) := hF (V i) (hV i)
  let restriction : F.obj.obj T → ∀ i, Shrink.{u} (F.obj.obj (Opposite.op (V i))) :=
    fun x i => (equivShrink.{u} _) (F.obj.map (a i).op x)
  apply small_of_injective (f := restriction)
  intro x y h
  apply F.property.isSeparated _ _ hcover x y
  rintro Z g ⟨W, b, c, ⟨i⟩, rfl⟩
  have hi : F.obj.map (a i).op x = F.obj.map (a i).op y :=
    (equivShrink.{u} _).injective (congrFun h i)
  simp only [op_comp, F.obj.map_comp, types_comp_apply, hi]


/-- A fibre product of pointwise small sheaves is pointwise small. -/
theorem small_sheaf_pullback
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {F G H : Sheaf J (Type (u + 1))} (f : F ⟶ H) (g : G ⟶ H)
    [FunctorToTypes.Small.{u} F.obj] [FunctorToTypes.Small.{u} G.obj] :
    FunctorToTypes.Small.{u} (pullback f g).obj := by
  intro T
  let π : (pullback f g).obj.obj T → F.obj.obj T × G.obj.obj T :=
    fun x => ((pullback.fst f g).hom.app T x, (pullback.snd f g).hom.app T x)
  apply small_of_injective (f := π)
  intro x y h
  have hp := ((IsPullback.of_hasPullback f g).map (sheafToPresheaf J (Type (u + 1)))).map
    ((evaluation Cᵒᵖ (Type (u + 1))).obj T)
  exact Types.ext_of_isPullback hp (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- A representable sheaf on the big fppf site over `S` is pointwise small. -/
theorem small_sheafifiedYoneda
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS) :
    FunctorToTypes.Small.{u}
      ((Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)).obj U).obj := by
  intro T
  let e := (sheafifiedYonedaToUliftPresheafIso B S hS).app U
  have : Small.{u} (((uliftYoneda.{u + 1}).obj U).obj T) :=
    inferInstanceAs (Small.{u} (ULift.{u + 1} (T.unop ⟶ U)))
  exact small_of_injective (CategoryTheory.injective_of_mono (e.hom.app T))


/-- The common proof of `relative_of_affineBaseChanges` and `relative_of_affineBaseChanges'`. -/
private theorem relative_of_affineBaseChanges_aux
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] (hzl : IsZariskiLocalAtTarget P)
    {X Y : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    (f : Y ⟶ X) [FunctorToTypes.Small.{u} Y.obj] {κ : Cardinal.{u}}
    (hκ : κ < B.cutoff ∨ B.cutoff.IsRegular)
    (hf : ∀ U : AlgebraicGeometry.BigFppfOver B S hS,
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U) →
      ∀ ξ : (Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)).obj U ⟶ X,
      ∃ (V : AlgebraicGeometry.BigFppfOver B S hS)
        (p : (Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)).obj V ⟶ Y)
        (q : V ⟶ U), IsPullback p
          ((Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)).map q) f ξ ∧
        P ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q) ∧
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V).size ≤
          max κ ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U).size) :
    (MorphismProperty.inverseImage P
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)) f := by
  classical
  let J := AlgebraicGeometry.BigFppfOver.topology B S hS
  let G := Sheaf.sheafifiedYoneda J
  let K := sheafToPresheaf J (Type (u + 1))
  let L := (Functor.whiskeringRight (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ
    (Type u) (Type (u + 1))).obj uliftFunctor.{u + 1, u}
  let e := sheafifiedYonedaToUliftPresheafIso B S hS
  have hisoPT : MorphismProperty.RespectsIso (MorphismProperty.inverseImage P
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine MorphismProperty.relative.of_exists fun U ξ => ?_
  let Z := pullback ξ f
  have : FunctorToTypes.Small.{u} (G.obj U).obj := small_sheafifiedYoneda B S hS U
  have : FunctorToTypes.Small.{u} Z.obj := small_sheaf_pullback J ξ f
  let A := FunctorToTypes.shrink.{u} Z.obj
  let eZ : L.obj A ≅ Z.obj := shrinkUliftIso Z.obj
  have hA : Presheaf.IsSheaf J A :=
    Presheaf.isSheaf_of_isSheaf_comp J A uliftFunctor
      ((Presheaf.isSheaf_of_iso_iff eZ).mpr Z.property)
  let π : A ⟶ yoneda.obj U := L.preimage
    (eZ.hom ≫ (pullback.fst ξ f).hom ≫ (e.app U).hom)
  have hπ : L.map π = eZ.hom ≫ (pullback.fst ξ f).hom ≫ (e.app U).hom :=
    L.map_preimage _
  choose V a ha harange hV using fun O =>
    BigFppfOver.exists_affineOpen_restrict B S hS U O
  choose W b q hq hqa hqt using fun O => hf (V O) (hV O) (G.map (a O) ≫ ξ)
  let k (O) : G.obj (W O) ⟶ Z :=
    pullback.lift (G.map (q O) ≫ G.map (a O)) (b O) (by
      simpa only [Category.assoc] using (hq O).w.symm)
  have hk (O) : IsPullback (k O) (G.map (q O)) (pullback.fst ξ f) (G.map (a O)) := by
    apply IsPullback.of_right (p := by exact pullback.lift_fst _ _ _)
      (t := (IsPullback.of_hasPullback ξ f).flip)
    simpa only [k, pullback.lift_snd] using hq O
  let k' (O) : yoneda.obj (W O) ⟶ A := L.preimage
    ((e.app (W O)).inv ≫ (k O).hom ≫ eZ.inv)
  have hk' (O) : IsPullback (k' O) (yoneda.map (q O)) π (yoneda.map (a O)) := by
    apply IsPullback.of_map_of_faithful L
    apply ((hk O).map K).of_iso (e.app (W O)) eZ.symm
      (e.app (V O)) (e.app U)
    · dsimp only [k']
      rw [L.map_preimage]
      exact (Iso.hom_inv_id_assoc (e.app (W O)) ((k O).hom ≫ eZ.inv)).symm
    · exact e.hom.naturality (q O)
    · rw [hπ]
      simp [K]
      rfl
    · exact e.hom.naturality (a O)
  have hcov : ∀ y : (BigFppfOver.toScheme B S hS).obj U,
      ∃ O, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (a O)) := by
    intro y
    have hy : y ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj U).Opens) := trivial
    rw [← iSup_affineOpens_eq_top] at hy
    obtain ⟨O, hO⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    exact ⟨O, by rw [harange]; exact hO⟩
  have hsize (O) : ((BigFppfOver.toScheme B S hS).obj (W O)).size ≤
      max κ ((BigFppfOver.toScheme B S hS).obj U).size := by
    let T := BigFppfOver.toScheme B S hS
    have : IsOpenImmersion (T.map (a O)) := ha O
    exact (hqt O).trans (max_le_max le_rfl (Scheme.size_le_of_isOpenImmersion (T.map (a O))))
  have hcontains : ∀ (Z : Scheme.{u})
      (k : ∀ O, (BigFppfOver.toScheme B S hS).obj (W O) ⟶ Z),
      (∀ O, _root_.AlgebraicGeometry.IsOpenImmersion (k O)) →
      (∀ z : Z, ∃ O, z ∈ Set.range (k O)) → B.Contains Z := by
    rcases hκ with hκ | hreg
    · have : Nonempty ((BigFppfOver.toScheme B S hS).obj U).affineOpens :=
        ⟨⟨⊥, isAffineOpen_bot _⟩⟩
      intro Z k hk hkcov
      have := hk
      exact B.contains_of_openCover_of_size_le
        (μ := max κ ((BigFppfOver.toScheme B S hS).obj U).size)
        (max_lt hκ U.left.property)
        ((Scheme.mk_affineOpens_le_size _).trans (le_max_right _ _)) k hkcov hsize
    · exact fun Z k hk hkcov =>
        B.contains_of_openCover_affineOpens_of_isRegular S hS hreg U Z k hk hkcov
  obtain ⟨R, eR, r, hr, hrP⟩ :=
    AlgebraicGeometry.Space.exists_representing_over_of_openCover
      B S hS (Q := P) hzl hA π ha hcov hk'
      (fun O => hqa O) hcontains
  let eR' : (G.obj R).obj ≅ Z.obj :=
    e.app R ≪≫ (L.mapIso eR).symm ≪≫ eZ
  let E : G.obj R ≅ Z := (Functor.FullyFaithful.ofFullyFaithful K).preimageIso eR'
  have hEr : E.hom ≫ pullback.fst ξ f = G.map r := by
    apply K.map_injective
    rw [K.map_comp]
    show K.map ((Functor.FullyFaithful.ofFullyFaithful K).preimage eR'.hom) ≫ _ = _
    rw [(Functor.FullyFaithful.ofFullyFaithful K).map_preimage]
    show eR'.hom ≫ (pullback.fst ξ f).hom = (G.map r).hom
    apply (cancel_mono (e.app U).hom).mp
    have hh : L.map eR.inv ≫ L.map π = (uliftYoneda.{u + 1}).map r := by
      rw [← L.map_comp, hr]
      rfl
    rw [hπ] at hh
    show ((e.app R).hom ≫ L.map eR.inv ≫ eZ.hom) ≫
      (pullback.fst ξ f).hom ≫ (e.app U).hom = _
    ext T x
    have hx := congrArg (fun η => η.app T ((e.app R).hom.app T x)) hh
    have hn := congrArg (fun η => η.app T x) (e.hom.naturality r)
    exact hx.trans hn.symm
  refine ⟨R, E.hom ≫ pullback.snd ξ f, r, ?_, hrP⟩
  apply (IsPullback.of_hasPullback ξ f).flip.of_iso E.symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
    exact (Iso.inv_hom_id_assoc E _).symm
  · dsimp only [Iso.refl_hom, Iso.symm_hom]
    rw [Category.comp_id]
    exact ((Iso.inv_comp_eq E).mpr hEr.symm).symm
  · simp
  · simp only [Sheaf.sheafifiedYoneda_obj, Iso.refl_hom]
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- **Representability from the affine points of the target, under a size bound.** Let `P` be a
property of morphisms of schemes which is local at the target for the Zariski topology. A
morphism of fppf sheaves of `Type (u + 1)` with pointwise `u`-small source is representable with
represented base changes in `P` as soon as its base change along every point out of an *affine*
object `U` of the site is represented by an object `V` over `U` with `V ⟶ U` in `P` and
`size V ≤ max κ (size U)`, for one cardinal `κ` below the cutoff: the charts over the affine opens
of an arbitrary test object glue, by relative Tag 03JH under a uniform size bound. -/
theorem relative_of_affineBaseChanges
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] (hzl : IsZariskiLocalAtTarget P)
    {X Y : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    (f : Y ⟶ X) [FunctorToTypes.Small.{u} Y.obj] {κ : Cardinal.{u}} (hκ : κ < B.cutoff)
    (hf : ∀ U : AlgebraicGeometry.BigFppfOver B S hS,
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U) →
      ∀ ξ : (Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)).obj U ⟶ X,
      ∃ (V : AlgebraicGeometry.BigFppfOver B S hS)
        (p : (Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)).obj V ⟶ Y)
        (q : V ⟶ U), IsPullback p
          ((Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)).map q) f ξ ∧
        P ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q) ∧
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V).size ≤
          max κ ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U).size) :
    (MorphismProperty.inverseImage P
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)) f := by
  exact relative_of_affineBaseChanges_aux B S hS P hzl f (Or.inl hκ) hf

/-- **Representability from the affine points of the target, under a size bound on the charts or
a regular cutoff.** Let `P` be a property of morphisms of schemes which is local at the target
for the Zariski topology. A morphism of fppf sheaves of `Type (u + 1)` with pointwise `u`-small
source is representable with represented base changes in `P` as soon as its base change along
every point out of an *affine* object `U` of the site is represented by an object `V` over `U`
with `V ⟶ U` in `P` and `size V ≤ max κ (size U)`: the charts over the affine opens of an
arbitrary test object glue, by relative Tag 03JH.

The cardinal `κ` is asked to be below the cutoff *or* the cutoff to be regular, and the second
alternative makes the size clause vacuous at `κ = B.cutoff`. Either way the glued object lies in
the site: by `AlgebraicGeometry.BigFppfSite.contains_of_openCover_of_size_le` in the first case,
one cardinal bounding both the charts and the affine opens indexing them, and by
`AlgebraicGeometry.BigFppfSite.contains_of_openCover_affineOpens_of_isRegular` in the second,
which asks nothing of the charts beyond lying in the site. Only the second alternative is
available when the charts are of unbounded size, and nothing weaker than regularity will do
there: closure of the site under the coproducts of families indexed below the cutoff is
*equivalent* to regularity of the cutoff, by
`AlgebraicGeometry.BigFppfSite.isRegular_cutoff_iff_contains_sigma`. -/
theorem relative_of_affineBaseChanges'
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] (hzl : IsZariskiLocalAtTarget P)
    {X Y : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    (f : Y ⟶ X) [FunctorToTypes.Small.{u} Y.obj] {κ : Cardinal.{u}}
    (hκ : κ < B.cutoff ∨ B.cutoff.IsRegular)
    (hf : ∀ U : AlgebraicGeometry.BigFppfOver B S hS,
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U) →
      ∀ ξ : (Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)).obj U ⟶ X,
      ∃ (V : AlgebraicGeometry.BigFppfOver B S hS)
        (p : (Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)).obj V ⟶ Y)
        (q : V ⟶ U), IsPullback p
          ((Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)).map q) f ξ ∧
        P ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q) ∧
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V).size ≤
          max κ ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U).size) :
    (MorphismProperty.inverseImage P
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)) f := by
  exact relative_of_affineBaseChanges_aux B S hS P hzl f hκ hf


/-! ### Rings -/

/-- A commutative square of rings with surjective top and bottom maps, whose bottom kernel is
generated by the image of the top kernel, is a pushout. -/
theorem isPushout_of_surjective_of_ker_eq
    {R S T U : CommRingCat.{u}} (f : R ⟶ S) (g : R ⟶ T)
    (a : S ⟶ U) (b : T ⟶ U) (hw : f ≫ a = g ≫ b)
    (hf : Function.Surjective f.hom) (hb : Function.Surjective b.hom)
    (hker : RingHom.ker b.hom = (RingHom.ker f.hom).map g.hom) :
    IsPushout f g a b := by
  apply IsPushout.mk' hw
  · intro V p q _ h
    apply CommRingCat.hom_ext
    ext x
    obtain ⟨y, rfl⟩ := hb x
    exact congrArg (fun k : T ⟶ V => k.hom y) h
  · intro V p q h
    have hk : RingHom.ker b.hom ≤ RingHom.ker q.hom := by
      rw [hker, Ideal.map_le_iff_le_comap]
      intro x hx
      show q.hom (g.hom x) = 0
      have he := congrArg (fun k : R ⟶ V => k.hom x) h
      change p.hom (f.hom x) = q.hom (g.hom x) at he
      rw [RingHom.mem_ker.mp hx, map_zero] at he
      exact he.symm
    let l : U ⟶ V := CommRingCat.ofHom (b.hom.liftOfSurjective hb ⟨q.hom, hk⟩)
    have hl : b ≫ l = q := CommRingCat.hom_ext (RingHom.liftOfSurjective_comp _ _ _)
    refine ⟨l, ?_, hl⟩
    apply CommRingCat.hom_ext
    ext x
    obtain ⟨y, rfl⟩ := hf x
    have he : f ≫ a ≫ l = f ≫ p := by
      rw [← Category.assoc, hw, Category.assoc, hl, h]
    exact congrArg (fun k : R ⟶ V => k.hom y) he

/-- A surjection of rings with nil kernel induces a thickening of spectra. -/
theorem specMap_isThickening_of_nilKernel
    {R T : Type u} [CommRing R] [CommRing T]
    (f : R →+* T) (hf : Function.Surjective f)
    (hnil : ∀ x, x ∈ RingHom.ker f → IsNilpotent x) :
    Stacks.Thickenings.IsThickening (Scheme.Spec.map (CommRingCat.ofHom f).op) := by
  refine ⟨AlgebraicGeometry.IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom f) hf, ?_⟩
  show Function.Surjective (PrimeSpectrum.comap f)
  rw [← Set.range_eq_univ, range_comap_of_surjective _ f hf]
  apply Set.eq_univ_iff_forall.2
  intro p
  rw [PrimeSpectrum.mem_zeroLocus]
  intro x hx
  obtain ⟨n, hn⟩ := hnil x hx
  exact Ideal.IsPrime.mem_of_pow_mem inferInstance n (by simp [hn])

/-! ### The colimit of a cartesian system -/

section Cartesian

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (DX DY : I ⥤ AlgebraicGeometry.BigAffineFppf B S hS) (φ : DX ⟶ DY)

/-- The morphism of diagrams of represented sheaves induced by a morphism of systems. -/
abbrev sheafMap :
    DX ⋙ AlgebraicGeometry.BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS) ⟶
      DY ⋙ AlgebraicGeometry.BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS) :=
  Functor.whiskerRight φ (AlgebraicGeometry.BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS))

variable {B S hS DX DY φ}

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- Cartesian naturality squares in schemes give an equifibered morphism of diagrams of
represented sheaves. -/
theorem sheafMap_equifibered
    (hcart : ∀ ⦃i j : I⦄ (g : i ⟶ j),
      IsPullback ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map (φ.app i))
        ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map (DX.map g))
        ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map (DY.map g))
        ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map (φ.app j))) :
    (sheafMap B S hS DX DY φ).Equifibered := by
  have hincl : (Functor.whiskerRight φ
      (AlgebraicGeometry.BigAffineFppf.inclusion B S hS)).Equifibered := by
    intro i j g
    let T := AlgebraicGeometry.BigFppfOver.toScheme B S hS
    have : T.Faithful := by dsimp [T, AlgebraicGeometry.BigFppfOver.toScheme]; infer_instance
    have : ReflectsLimitsOfShape WalkingCospan T := by
      dsimp [T, AlgebraicGeometry.BigFppfOver.toScheme, AlgebraicGeometry.BigFppfOver.forget]
      infer_instance
    apply IsPullback.of_map_of_faithful T
    exact (hcart g).flip
  have : PreservesLimitsOfShape WalkingCospan
      (Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)) := by
    dsimp [Sheaf.sheafifiedYoneda]
    infer_instance
  exact hincl.whiskerRight
    (Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS))

/-- **The stage squares are cartesian**: `X_i` is the base change of `colim X_j ⟶ colim Y_j` along
the stage `Y_i ⟶ colim Y_j`. -/
theorem isPullback_stage
    (hcart : ∀ ⦃i j : I⦄ (g : i ⟶ j),
      IsPullback ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map (φ.app i))
        ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map (DX.map g))
        ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map (DY.map g))
        ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map (φ.app j)))
    (i : I) :
    IsPullback
      (colimit.ι (DX ⋙ AlgebraicGeometry.BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)) i)
      ((sheafMap B S hS DX DY φ).app i) (colim.map (sheafMap B S hS DX DY φ))
      (colimit.ι (DY ⋙ AlgebraicGeometry.BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)) i) := by
  have : IsConnected (Under i) := IsFiltered.isConnected _
  exact equifibered_colimit_isPullback (sheafMap B S hS DX DY φ) (sheafMap_equifibered hcart) i

/-- **The colimit of a cartesian system of affine stages over an affine formal algebraic space
is representable, with affine represented base changes.** -/
theorem relative_isAffineHom_colimMap
    (hDY : ∀ ⦃i j : I⦄ (g : i ⟶ j), Stacks.Thickenings.IsThickening
      ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map (DY.map g)))
    (hcart : ∀ ⦃i j : I⦄ (g : i ⟶ j),
      IsPullback ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map (φ.app i))
        ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map (DX.map g))
        ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map (DY.map g))
        ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map (φ.app j)))
    (Y : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1)))
    (hY : _root_.AlgebraicGeometry.IsAffineFormalAlgebraicSpace B S hS Y)
    (eY : Y ≅ colimit (DY ⋙ AlgebraicGeometry.BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)))
    {κ : Cardinal.{u}} (hκ : κ < B.cutoff)
    (hsize : ∀ i, ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).obj (DX.obj i)).size ≤ κ) :
    (MorphismProperty.inverseImage (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS))
      (colim.map (sheafMap B S hS DX DY φ) ≫ eY.inv) := by
  classical
  let J := AlgebraicGeometry.BigFppfOver.topology B S hS
  let G := Sheaf.sheafifiedYoneda J
  let T := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let FX := DX ⋙ AlgebraicGeometry.BigAffineFppf.inclusion B S hS ⋙ G
  let FY := DY ⋙ AlgebraicGeometry.BigAffineFppf.inclusion B S hS ⋙ G
  let f := colim.map (sheafMap B S hS DX DY φ) ≫ eY.inv
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let _ : G.Full := Sheaf.sheafifiedYoneda_full J
  let _ : G.Faithful := Sheaf.sheafifiedYoneda_faithful J
  have : PreservesLimitsOfShape WalkingCospan G := by
    dsimp [G, Sheaf.sheafifiedYoneda]
    infer_instance
  have : PreservesLimitsOfShape WalkingCospan T := by
    dsimp [T, AlgebraicGeometry.BigFppfOver.toScheme]
    infer_instance
  -- the stage squares, over `Y`
  have hstage (i : I) : IsPullback (colimit.ι FX i) ((sheafMap B S hS DX DY φ).app i) f
      (colimit.ι FY i ≫ eY.inv) :=
    (isPullback_stage hcart i).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eY.symm
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      (Category.id_comp _).symm rfl
  -- the base change along a point out of an affine object
  have hbase : ∀ U : AlgebraicGeometry.BigFppfOver B S hS,
      IsAffine (T.obj U) → ∀ ξ : G.obj U ⟶ Y,
      ∃ (V : AlgebraicGeometry.BigFppfOver B S hS) (p : G.obj V ⟶ colimit FX) (q : V ⟶ U),
        IsPullback p (G.map q) f ξ ∧ IsAffineHom (T.map q) ∧
        (T.obj V).size ≤ max κ (T.obj U).size := by
    intro U hU ξ
    have hqc := AlgebraicGeometry.Space.isQuasiCompact_yoneda_of_compact B S hS U
      (by let := hU; infer_instance)
    obtain ⟨i, g, hg⟩ := AlgebraicGeometry.exists_factor_through_thickening' B S hS I DY
      (fun _ _ g ↦ (hDY g).1) Y eY (yoneda.obj U) hqc ξ
    let g' : G.obj U ⟶ G.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj (DY.obj i)) :=
      g
    let u := G.preimage g'
    let a := (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (φ.app i)
    have hp := ((IsPullback.of_hasPullback a u).map G).paste_horiz (hstage i)
    have hq := (IsPullback.of_hasPullback a u).map T
    have ha : IsAffineHom (T.map a) := by
      have : IsAffine (T.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj (DY.obj i))) :=
        AlgebraicGeometry.BigAffineFppf.isAffine_toScheme_obj B S hS (DY.obj i)
      have : IsAffine (T.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj (DX.obj i))) :=
        AlgebraicGeometry.BigAffineFppf.isAffine_toScheme_obj B S hS (DX.obj i)
      infer_instance
    refine ⟨pullback a u, G.map (pullback.fst a u) ≫ colimit.ι FX i, pullback.snd a u, ?_, ?_, ?_⟩
    · have hξ : ξ = G.map u ≫ colimit.ι FY i ≫ eY.inv := by
        rw [show G.map u = g' from G.map_preimage g']
        exact hg.symm
      rw [hξ]
      exact hp
    · exact MorphismProperty.of_isPullback hq ha
    · refine (AlgebraicGeometry.Space.size_pullback_le B S hS a u).trans
        (max_le_max (hsize i) le_rfl)
  -- smallness of the source
  have hsmall : FunctorToTypes.Small.{u} (colimit FX).obj := by
    let := small_of_setTheoreticCondition B S hS Y hY.1
    apply small_sections_of_affine B S hS
    intro U hU
    have : Small.{u} (G.obj U ⟶ Y) :=
      small_of_injective (Sheaf.sectionEquiv J (X := U) (F := Y)).injective
    have : Small.{u} (G.obj U ⟶ colimit FX) := small_hom_of_represented_fibers.{u} G f U
      (fun ξ => by
        obtain ⟨V, p, q, hp, _⟩ := hbase U hU ξ
        exact ⟨V, p, q, hp⟩)
    exact small_of_surjective (Sheaf.sectionEquiv J (X := U)).surjective
  have : FunctorToTypes.Small.{u} (colim.obj FX).obj := hsmall
  have hisoA : MorphismProperty.RespectsIso (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact relative_of_affineBaseChanges' B S hS (@IsAffineHom.{u})
    (@HasAffineProperty.instIsZariskiLocalAtTarget _ _ instHasAffinePropertyIsAffineHomIsAffine)
    f (Or.inl hκ) hbase

end Cartesian

end AlgebraicGeometry.FormalSpace.CartesianColimit

end
