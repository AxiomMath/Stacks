module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.SheafFromSubsheaves
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.MorphismRepresentableBySpaces.Criterion
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalOverTerminal
public import StacksFrontier.AlgebraicGeometry.Stacks.EssentiallySmallSite
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LimitPreservingOnObjects
public import StacksFrontier.CategoryTheory.FiberedCategory.PairIsoClassPresheaf
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.StackOverMap
public import StacksFrontier.CategoryTheory.Sites.Localization.StacksOverSlice
public import StacksFrontier.CategoryTheory.Sites.Stack.FiberedInSets
public import StacksFrontier.CategoryTheory.Sites.Stack.SetoidTwoFibreProduct
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.ReverseEffective
public import StacksFrontier.CategoryTheory.TwoFibreProductOverReindex
public import StacksFrontier.CategoryTheory.TwoFibreProductOverRestrict
public import StacksFrontier.RingTheory.Algebra.DirectLimit.FinitePresentation
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableBySpace.Characterization
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
import all StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.MorphismRepresentableBySpaces.Criterion
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.LimitPreservingOnObjectsCriteria.FinitePresentationLimits
import all StacksFrontier.AlgebraicGeometry.Stacks.Criteria.LimitPreservingOnObjectsCriteria.FinitePresentationLimits


/-!
# A limit-preserving criterion for representability by algebraic spaces

Let `S` be a scheme contained in a big fppf site and let `κ` be the size of a scheme `T` of that
site. A 1-morphism `f : 𝒳 ⟶ 𝒴` of categories fibred in groupoids over the big fppf site of `S`
is representable by algebraic spaces as soon as the structure morphism of `𝒴` is limit preserving
on objects, the 2-fibre product `(Sch/V)_{fppf} ×_{y, 𝒴} 𝒳` is representable by an algebraic
space of size at most `κ` for every affine `V` locally of finite presentation over `S` and every
`y ∈ Ob(𝒴_V)`, and `𝒳` and `𝒴` are stacks for the Zariski topology.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_limitPreservingOnObjects`:
  **Stacks 07WH**.

## Implementation notes

The source's hypothesis that the fibre product over `V` is representable by an algebraic space of
size at most `κ = size(T)` is rendered as the existence of an algebraic space `F` over `V`
equivalent, over the big fppf site of `V`, to the first projection of the 2-fibre product,
together with an object `A` of that site of size at most `size(T)` and a surjective étale map
`yoneda.obj A ⟶ F`. That is the definition of `size(X) ≤ κ` quoted in the source: a scheme of
size at most `κ` with a surjective étale morphism to `X`.

The proof follows the source. Case I, an affine `V` mapping into an affine open of `S`, writes
`V` as a cofiltered limit of affine schemes of finite presentation over that open
(Stacks 00QN), descends the point `y` to a finite stage by limit preservation on objects, and
restricts the algebraic space found there. Case II glues: the Zariski-stack hypotheses make the
2-fibre product a stack in setoids over the Zariski topology of `V`, Case I makes each member of
an affine open cover of `V` representable, and the sheaf of isomorphism classes is then glued by
Stacks 02WR. The set-theoretic side condition of that gluing is met because the cover can be
chosen of cardinality at most `size(V)` and each chart has size at most `max (size T) (size V)`,
so Stacks 000R puts the coproduct of the charts in the site.

The Zariski topology enters only through the stack hypotheses and the open covers; the fppf
topology is the one in which the glued object is a sheaf.

## References

* [Stacks Project, Tag 07WH](https://stacks.math.columbia.edu/tag/07WH)
-/


@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

-- `Functor.Fiber`, `Functor.Fiber.fiberInclusion` and the slice functor attached to a choice of
-- pullbacks are plain `def`s, so an object of a fibre and its chosen pullbacks are only
-- recognised as such after unfolding them.
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor
  CategoryTheory.TwoFibreProductOver.fst
  CategoryTheory.MorphismProperty.inverseImage

open CategoryTheory.Limits in
private lemma exists_bounded_atlas_relocalizeRestrict
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S') (g : B.obj hS ⟶ B.obj hS')
    (F : (AlgebraicGeometry.BigFppfOver B S' hS')ᵒᵖ ⥤ Type u)
    (κ : Cardinal.{u})
    (A : AlgebraicGeometry.BigFppfOver B S' hS') (a : yoneda.obj A ⟶ F)
    (hA : A.left.1.size ≤ κ)
    (hs : (MorphismProperty.inverseImage (@Surjective.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S' hS')).presheaf a)
    (he : (MorphismProperty.inverseImage (@Etale.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S' hS')).presheaf a) :
    ∃ (A' : AlgebraicGeometry.BigFppfOver B S hS)
      (a' : yoneda.obj A' ⟶ (OverShriek.relocalizeRestrict g).obj F),
      A'.left.1.size ≤ max κ S.size ∧
      (MorphismProperty.inverseImage (@Surjective.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a' ∧
      (MorphismProperty.inverseImage (@Etale.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a' := by
  let A' := (Over.pullback g).obj A
  let a' := (OverShriek.restrictYonedaIso g A).hom ≫
    (OverShriek.relocalizeRestrict g).map a
  have hEtale : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hP (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
      (h : (MorphismProperty.inverseImage P
        (AlgebraicGeometry.BigFppfOver.toScheme B S' hS')).presheaf a) :
      (MorphismProperty.inverseImage P
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a' := by
    have : (MorphismProperty.inverseImage P
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).RespectsIso :=
      MorphismProperty.RespectsIso.inverseImage _ _
    have : (MorphismProperty.presheaf (MorphismProperty.inverseImage P
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS))).RespectsIso :=
      (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _).respectsIso
    exact MorphismProperty.RespectsIso.precomp _ _ _
      (OverShriek.relative_relocalizeRestrict_map g (fun s hs => hs) h)
  refine ⟨A', a', ?_, hP _ hs, hP _ he⟩
  have sq := (IsPullback.of_hasPullback A.hom g).map B.inclusion
  have hsize := Scheme.size_congr sq.isoPullback
  change (B.inclusion.obj (pullback A.hom g)).size ≤ max κ S.size
  rw [hsize]
  exact (Scheme.size_pullback_le _ _).trans (max_le_max hA le_rfl)

private lemma exists_algebraicSpace_fibre_of_affineFactorization
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (AlgebraicGeometry.BigFppfOver B S hS))
    (f : 𝒳 ⟶ 𝒴)
    (hlimit : AlgebraicGeometry.BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B S hS 𝒴
      (AlgebraicGeometry.Stack.terminalCFG B S hS)
      (Bicategory.InducedBicategory.mkHom (AlgebraicGeometry.Stack.toTerminalCFG B S hS 𝒴)))
    (hlocal : ∀ (U : AlgebraicGeometry.BigFppfOver B S hS),
      IsAffine U.left.1 →
      LocallyOfFinitePresentation (B.inclusion.map U.hom) →
      let 𝒰 := AlgebraicGeometry.BigFppfOver B U.left.1 U.left.2
      let p𝒰 : 𝒰 ⥤ AlgebraicGeometry.BigFppfOver B S hS := Over.map U.hom
      ∀ (y : 𝒰 ⥤ 𝒴.val.obj) (_hy : y ⋙ 𝒴.val.p = p𝒰),
        ∃ F : 𝒰ᵒᵖ ⥤ Type u,
          AlgebraicGeometry.IsAlgebraicSpace B U.left.1 U.left.2 F ∧
          Nonempty (StacksRepresentableCFG.EquivalenceOver
            (TwoFibreProductOver.fst p𝒰 𝒳.val.p 𝒴.val.p y
              (CatFiberedInGroupoids.homFunctor f))
            (presheafOfCategories (F ⋙ typeToCat)).p) ∧
          ∃ (A : 𝒰) (a : yoneda.obj A ⟶ F),
            A.left.1.size ≤ T.left.1.size ∧
            (MorphismProperty.presheaf
              (MorphismProperty.inverseImage
                (@Surjective.{u} : MorphismProperty Scheme.{u})
                (AlgebraicGeometry.BigFppfOver.toScheme B U.left.1 U.left.2))) a ∧
            (MorphismProperty.presheaf
              (MorphismProperty.inverseImage
                (@Etale.{u} : MorphismProperty Scheme.{u})
                (AlgebraicGeometry.BigFppfOver.toScheme B U.left.1 U.left.2))) a)
    (U : AlgebraicGeometry.BigFppfOver B S hS) [IsAffine U.left.1]
    (R : CommRingCat.{u}) (hR : B.Contains (Spec R))
    (r : Spec R ⟶ S) [LocallyOfFinitePresentation r]
    (q : U.left.1 ⟶ Spec R) (hq : q ≫ r = B.inclusion.map U.hom)
    (y : AlgebraicGeometry.BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (hy : y ⋙ 𝒴.val.p = Over.map U.hom) :
    ∃ F : (AlgebraicGeometry.BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u,
      AlgebraicGeometry.IsAlgebraicSpace B U.left.1 U.left.2 F ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) ∧
      ∃ (A : AlgebraicGeometry.BigFppfOver B U.left.1 U.left.2) (a : yoneda.obj A ⟶ F),
        A.left.1.size ≤ max T.left.1.size U.left.1.size ∧
        (MorphismProperty.inverseImage (@Surjective.{u})
          (AlgebraicGeometry.BigFppfOver.toScheme B U.left.1 U.left.2)).presheaf a ∧
        (MorphismProperty.inverseImage (@Etale.{u})
          (AlgebraicGeometry.BigFppfOver.toScheme B U.left.1 U.left.2)).presheaf a := by
  let 𝒰 := AlgebraicGeometry.BigFppfOver B U.left.1 U.left.2
  let p𝒰 : 𝒰 ⥤ AlgebraicGeometry.BigFppfOver B S hS := Over.map U.hom
  let x : 𝒴.val.p.Fiber U :=
    ⟨y.obj (Over.mk (𝟙 U.left)), by
      refine (Functor.congr_obj hy (Over.mk (𝟙 U.left))).trans ?_
      change Over.mk (𝟙 U.left ≫ U.hom) = U
      rw [Category.id_comp]
      cases U
      rfl⟩
  obtain ⟨V, hVaff, hVfp, g, x', φ, hφ⟩ :=
    exists_finitePresentation_stage_of_isAffine B S hS 𝒴 hlimit U
      R hR r q hq x
  have : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let y' := V.iteratedSliceBackward ⋙ 𝒴.val.p.chosenPullbacks.sliceFunctor x'
  have hy' : y' ⋙ 𝒴.val.p = Over.map V.hom := by
    dsimp only [y']
    rw [Functor.assoc, Functor.ChoiceOfPullbacks.sliceFunctor_comp]
    exact Over.iteratedSliceBackward_forget V
  obtain ⟨F, hF, hrepr, hbound⟩ := hlocal V hVaff hVfp y' hy'
  obtain ⟨eY, heY⟩ :=
    exists_iso_iteratedSliceFunctor_of_cartesian
      𝒴.val.p 𝒴.isFiberedInGroupoids 𝒴.val.p.chosenPullbacks
      g x' y hy φ hφ
  let f₀ := CatFiberedInGroupoids.homFunctor f
  let y'' := Over.map g.left ⋙ y'
  let α : y ≅ y'' :=
    eY ≪≫ Functor.isoWhiskerRight (iteratedSliceBackward_mapIso g)
      (𝒴.val.p.chosenPullbacks.sliceFunctor x') ≪≫
        Functor.associator (Over.map g.left) V.iteratedSliceBackward
          (𝒴.val.p.chosenPullbacks.sliceFunctor x')
  have hα (W : 𝒰) : 𝒴.val.p.IsHomLift (𝟙 (p𝒰.obj W)) (α.hom.app W) := by
    let cY := 𝒴.val.p.chosenPullbacks
    have h₁ := heY W
    have hdom : ((U.iteratedSliceBackward ⋙ Over.map g).obj W).left =
        p𝒰.obj W := by cases W; rfl
    have h₁' : 𝒴.val.p.IsHomLift (𝟙 (p𝒰.obj W)) (eY.hom.app W) := by
      rwa [hdom] at h₁
    have hcod : (Over.forget V).obj
        ((Over.map g.left ⋙ V.iteratedSliceBackward).obj W) = p𝒰.obj W := by
      change Over.mk ((W.hom ≫ g.left) ≫ V.hom) = p𝒰.obj W
      simp only [Category.assoc, g.w]
      cases W
      rfl
    have hbase : (Over.forget V).IsHomLift (𝟙 (p𝒰.obj W))
        ((iteratedSliceBackward_mapIso g).hom.app W) := by
      refine IsHomLift.of_fac' (Over.forget V) (𝟙 (p𝒰.obj W))
        ((iteratedSliceBackward_mapIso g).hom.app W) hdom hcod ?_
      apply Over.OverMorphism.ext
      simp only [Over.forget, Functor.comp_obj, Comma.fst_obj, Over.map_obj_left,
        iteratedSliceBackward_mapIso, Over.isoMk, Category.id_comp, eqToHom_trans,
        Over.eqToHom_left]
      change 𝟙 W.left = eqToHom (rfl : W.left = W.left)
      rfl
    have h₂' := Functor.isHomLift_map_of_comp_eq (cY.sliceFunctor_comp x')
      (𝟙 (p𝒰.obj W)) ((iteratedSliceBackward_mapIso g).hom.app W)
    change 𝒴.val.p.IsHomLift (𝟙 (p𝒰.obj W))
      (eY.hom.app W ≫ (cY.sliceFunctor x').map
        ((iteratedSliceBackward_mapIso g).hom.app W) ≫ 𝟙 _)
    rw [Category.comp_id]
    exact IsHomLift.comp_of_lift_id 𝒴.val.p (p𝒰.obj W) _ _
  obtain ⟨eR⟩ := PresheafOfCategories.nonempty_equivalenceOver_relocalizeRestrict
    (a := V.hom) (m := g.left) (F := F) y' f₀ hy'
    (CatFiberedInGroupoids.homFunctor_comp_p f)
    𝒳.isFiberedInGroupoids 𝒴.isFiberedInGroupoids hrepr.some
  rw [g.w] at eR
  refine ⟨(OverShriek.relocalizeRestrict g.left).obj F,
    AlgebraicGeometry.isAlgebraicSpace_relocalizeRestrict B U.left.1 V.left.1 U.left.2 V.left.2
      g.left F hF,
    ⟨(TwoFibreProductOver.reindexEquivalenceOver (G := f₀) α hα).trans eR⟩, ?_⟩
  obtain ⟨A, a, hA, hs, he⟩ := hbound
  exact exists_bounded_atlas_relocalizeRestrict B U.left.1 V.left.1 U.left.2 V.left.2
    g.left F T.left.1.size A a hA hs he


private lemma exists_affine_open_cover_factorization {X S : Scheme.{u}} (f : X ⟶ S) :
    ∃ (I : Type u) (U : I → X.affineOpens) (V : I → S.affineOpens),
      Cardinal.mk I ≤ X.size ∧ (⨆ i, (U i).1) = ⊤ ∧
      ∀ i, (U i).1 ≤ f ⁻¹ᵁ (V i).1 := by
  classical
  let I := {U : X.affineOpens // ∃ V : S.affineOpens, U.1 ≤ f ⁻¹ᵁ V.1}
  refine ⟨I, fun i => i.1, fun i => i.2.choose,
    (Cardinal.mk_subtype_le _).trans X.mk_affineOpens_le_size, ?_,
    fun i => i.2.choose_spec⟩
  apply top_unique
  intro x _
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := S) (x := f x) (U := ⊤) (by trivial)
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := f ⁻¹ᵁ V) hxV
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, ⟨⟨V, hV⟩, hUV⟩⟩, hxU⟩


private lemma zariskiTopology_le_fppf (B : AlgebraicGeometry.BigFppfSite.{u}) :
    AlgebraicGeometry.BigFppfSite.zariskiTopology B ≤ B.topology := by
  apply Precoverage.toGrothendieck_mono
  rintro X R ⟨E, rfl, hE, -⟩
  exact ⟨E, rfl, hE⟩

private lemma open_cover_mem_zariski (B : AlgebraicGeometry.BigFppfSite.{u})
    {X : B.Schemes} {I : Type u} (Y : I → B.Schemes) (f : ∀ i, Y i ⟶ X)
    (hopen : ∀ i, IsOpenImmersion (B.inclusion.map (f i)))
    (hsurj : ∀ x : X.1, ∃ i y, (B.inclusion.map (f i)) y = x) :
    Sieve.ofArrows Y f ∈ AlgebraicGeometry.BigFppfSite.zariskiTopology B X := by
  let E₀ : PreZeroHypercover.{u} X := ⟨I, Y, f⟩
  let E : Covering.{u + 1, u, u + 1} B.Schemes :=
    ⟨X, E₀.reindex Equiv.ulift.{u + 1, u}⟩
  have hz : AlgebraicGeometry.IsZariskiCovering E := by
    change (E.2.map B.inclusion).presieve₀ ∈ Scheme.zariskiPrecoverage _
    rw [Scheme.ofArrows_mem_precoverage_iff (P := @IsOpenImmersion)]
    refine ⟨?_, fun i => hopen i.down⟩
    intro x
    obtain ⟨i, y, hy⟩ := hsurj x
    exact ⟨ULift.up i, y, hy⟩
  obtain ⟨⟨X', E'⟩, hE', hX', hComb⟩ :=
    AlgebraicGeometry.BigFppfSite.zariskiCovering_has_representative B E hz
  dsimp only at hX'
  subst X'
  have hpre : E.2.presieve₀ ∈ AlgebraicGeometry.BigFppfSite.zariskiPrecoverage B E.1 := by
    rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hComb]
    exact ⟨E', rfl, hE'⟩
  simpa only [E, PreZeroHypercover.presieve₀_reindex] using
    Precoverage.generate_mem_toGrothendieck hpre

private lemma exists_affine_site_cover (B : AlgebraicGeometry.BigFppfSite.{u})
    {S X : B.Schemes} (g : X ⟶ S) :
    ∃ (I : Type u) (V : I → B.Schemes) (j : ∀ i, V i ⟶ X),
      Cardinal.mk I ≤ X.1.size ∧
      Sieve.ofArrows V j ∈ AlgebraicGeometry.BigFppfSite.zariskiTopology B X ∧
      (∀ i, IsOpenImmersion (B.inclusion.map (j i))) ∧
      ∀ i, IsAffine (V i).1 ∧ ∃ (R : CommRingCat.{u}),
        B.Contains (Spec R) ∧ ∃ (r : Spec R ⟶ S.1),
          LocallyOfFinitePresentation r ∧ ∃ (q : (V i).1 ⟶ Spec R),
            q ≫ r = B.inclusion.map (j i ≫ g) := by
  classical
  obtain ⟨I, O, P, hI, hcover, hOP⟩ :=
    exists_affine_open_cover_factorization (B.inclusion.map g)
  let V : I → B.Schemes := fun i =>
    B.obj (Scheme.size_lt_of_isOpenImmersion (O i).1.ι X.2)
  let j : ∀ i, V i ⟶ X := fun i => ObjectProperty.homMk (O i).1.ι
  refine ⟨I, V, j, hI, ?_, fun i => by
    change IsOpenImmersion (O i).1.ι
    infer_instance, ?_⟩
  · apply open_cover_mem_zariski B V j (fun i => by
      change IsOpenImmersion (O i).1.ι
      infer_instance)
    intro x
    have hx : x ∈ ⨆ i, (O i).1 := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨i, ⟨x, hi⟩, rfl⟩
  · intro i
    have hopen : IsOpenImmersion (P i).2.fromSpec :=
      AlgebraicGeometry.IsAffineOpen.isOpenImmersion_fromSpec (P i).2
    refine ⟨(O i).2, S.1.presheaf.obj (.op (P i).1),
      Scheme.size_lt_of_isOpenImmersion (P i).2.fromSpec S.2,
      (P i).2.fromSpec, inferInstance,
      (B.inclusion.map g).resLE (P i).1 (O i).1 (hOP i) ≫ (P i).2.isoSpec.hom, ?_⟩
    exact (resLE_isoSpec_hom_fromSpec (B.inclusion.map g) (P i) (O i).1 (hOP i)).trans
      (B.inclusion.map_comp (j i) g).symm

open CategoryTheory.Limits in
private theorem fst_isStack_overMap
    {C : Type (u + 1)} [Category.{u} C] [HasPullbacks C]
    {A Y : Type (u + 1)} [Category.{u} A] [Category.{u} Y]
    {U S : C} (g : U ⟶ S) (pA : A ⥤ Over S) (pY : Y ⥤ Over S)
    (G : Over U ⥤ Y) (F : A ⥤ Y)
    (J : GrothendieckTopology C) [J.Subcanonical]
    (hA : pA.IsStackInGroupoids.{u + 1} (J.over S))
    (hY : pY.IsStackInGroupoids.{u + 1} (J.over S))
    (hG : G ⋙ pY = Over.map g) (hF : F ⋙ pY = pA) :
    (TwoFibreProductOver.fst (Over.map g) pA pY G F).IsStack (J.over U) := by
  have hyo (X : C) : Presheaf.IsSheaf J (yoneda.obj X) :=
    (isSheaf_iff_isSheaf_of_type J _).mpr
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)
  have hpT : (Over.map g).IsStack (J.over S) :=
    Over.isStack_of_comp_forget.{u, u, u+1, u+1} (Over.map g) (hyo S) (by
      rw [Over.mapForget_eq]
      exact (Over.isStack_forget_iff_isSheaf (U := U) J).mpr
        (hyo U))
  have hgT : (Over.map g).IsFiberedInGroupoids :=
    Functor.IsFiberedInGroupoids.of_comp_over S (Over.forget U) (Over.map g)
      (Over.mapForget_eq g) (Functor.IsFiberedInGroupoids.over_forget U)
  let := hA.isFiberedInGroupoids.isFibered
  let := hY.isFiberedInGroupoids.isFibered
  have hs := TwoFibreProductOver.isStack_isFiberedInGroupoids_structureFunctor
    hpT (Functor.isStack_of_isStackInGroupoids hA)
    (Functor.isStack_of_isStackInGroupoids hY)
    hgT hA.isFiberedInGroupoids hY.isFiberedInGroupoids hG hF
  have hsG : (TwoFibreProductOver.fst (Over.map g) pA pY G F).IsStackInGroupoids.{u+1} (J.over U) :=
    Functor.isStackInGroupoids_of_comp_overMap _ g J (by
      rw [TwoFibreProductOver.fst_comp_eq]
      exact hs.1.isStackInGroupoids hs.2)
  let := hsG.isFiberedInGroupoids.isFibered
  exact Functor.isStack_of_isStackInGroupoids hsG

section RelocalizeCover

open CategoryTheory.Limits CategoryTheory.OverShriek Opposite


private def toTerminalYoneda {C : Type (u + 1)} [Category.{u} C] {U : C}
    (F : (Over U)ᵒᵖ ⥤ Type u) : F ⟶ yoneda.obj (Over.mk (𝟙 U)) where
  app W := ↾fun _ => Over.homMk W.unop.hom (by simp)
  naturality W W' k := by
    ext x
    exact Over.OverMorphism.ext k.unop.w.symm

private lemma isPullback_relocalizeCounit
    {C : Type (u + 1)} [Category.{u} C] {V U : C} (g : V ⟶ U)
    (F : (Over U)ᵒᵖ ⥤ Type u) :
    IsPullback (relocalizeOfRestricted g (𝟙 ((relocalizeRestrict g).obj F)))
      (relocalizeToYoneda g ((relocalizeRestrict g).obj F)) (toTerminalYoneda F)
      (yoneda.map (Over.homMk g (by simp) : Over.mk g ⟶ Over.mk (𝟙 U))) := by
  apply IsPullback.of_forall_isPullback_app
  intro W
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext x
    apply Over.OverMorphism.ext
    exact x.2.symm
  · rintro ⟨⟨ψ, s⟩, hs⟩ ⟨⟨ψ', s'⟩, hs'⟩ ⟨h₁, h₂⟩
    have hψ : ψ = ψ' := congrArg Over.Hom.left h₂
    subst ψ'
    have hs₀ : ψ ≫ g = W.unop.hom := hs
    let e : W.unop ≅ Over.mk (ψ ≫ g) := Over.isoMk (Iso.refl _) (by simpa using hs₀)
    have he : Function.Injective (F.map e.hom.op) :=
      (ConcreteCategory.bijective_of_isIso (F.map e.hom.op)).injective
    have hss : s = s' := he h₁
    subst s'
    rfl
  · intro x b _
    let e : W.unop ≅ Over.mk (b.left ≫ g) :=
      Over.isoMk (Iso.refl _) (by simpa using b.w)
    refine ⟨relocalizeMk g ((relocalizeRestrict g).obj F) b.left
      (F.map e.inv.op x) b.w, ?_, ?_⟩
    · change F.map e.hom.op (F.map e.inv.op x) = x
      rw [← F.map_comp_apply, ← op_comp, e.hom_inv_id, op_id, F.map_id]
      rfl
    · exact Over.OverMorphism.ext rfl

private lemma relocalizeCounit_open
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (V : AlgebraicGeometry.BigFppfOver B S hS)
    (hV : IsOpenImmersion (B.inclusion.map V.hom))
    (F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    (MorphismProperty.inverseImage (@IsOpenImmersion.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf
      (relocalizeOfRestricted V.hom (𝟙 ((relocalizeRestrict V.hom).obj F))) := by
  let P := MorphismProperty.inverseImage (@IsOpenImmersion.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : PreservesLimitsOfShape WalkingCospan
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS))
  have : P.IsStableUnderBaseChange :=
    MorphismProperty.inverseImage_isStableUnderBaseChange _ _
  have hmap : P.presheaf
      (yoneda.map (Over.homMk V.hom (by simp) : Over.mk V.hom ⟶ Over.mk (𝟙 (B.obj hS)))) :=
    MorphismProperty.relative_map hV
  have : P.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange P
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_relocalizeCounit V.hom F).flip hmap

private lemma locally_factors_relocalizeCounit
    {C : Type (u + 1)} [Category.{u} C] {S : C} (J : GrothendieckTopology C)
    {I : Type u} (V : I → C) (j : ∀ i, V i ⟶ S)
    (hcover : Sieve.ofArrows V j ∈ J S) (F : (Over S)ᵒᵖ ⥤ Type u)
    (W : Over S) (x : F.obj (op W)) :
    ∃ R : Sieve W, R ∈ J.over S W ∧ ∀ ⦃W'⦄ (g : W' ⟶ W), R g →
      ∃ (i : I) (z : ((relocalizePresheafFunctor (j i)).obj
          ((relocalizeRestrict (j i)).obj F)).obj (op W')),
        (relocalizeOfRestricted (j i) (𝟙 ((relocalizeRestrict (j i)).obj F))).app (op W') z =
          F.map g.op x := by
  let R₀ := (Sieve.ofArrows V j).pullback W.hom
  let R := (Sieve.overEquiv W).symm R₀
  refine ⟨R, J.overEquiv_symm_mem_over W R₀ (J.pullback_stable W.hom hcover), ?_⟩
  intro W' g hg
  change (Sieve.ofArrows V j) (g.left ≫ W.hom) at hg
  obtain ⟨_, b, _, ⟨i⟩, hb⟩ := hg
  let b' : W' ⟶ Over.mk (j i) := Over.homMk b (hb.trans g.w)
  let t : yoneda.obj W' ⟶ F := yoneda.map g ≫ yonedaEquiv.symm x
  have hcomm : t ≫ toTerminalYoneda F =
      yoneda.map b' ≫ yoneda.map (Over.homMk (j i) (by simp) :
        Over.mk (j i) ⟶ Over.mk (𝟙 S)) := by
    ext W'' ξ
    exact Over.OverMorphism.ext (Over.w (ξ ≫ b')).symm
  let z := (isPullback_relocalizeCounit (j i) F).lift t (yoneda.map b') hcomm
  refine ⟨i, yonedaEquiv z, ?_⟩
  have hz := congrArg yonedaEquiv
    ((isPullback_relocalizeCounit (j i) F).lift_fst t (yoneda.map b') hcomm)
  dsimp only [t] at hz
  rwa [← yonedaEquiv_naturality, Equiv.apply_symm_apply] at hz

private lemma isAlgebraicSpace_of_open_family
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf ((AlgebraicGeometry.BigFppfSite.zariskiTopology B).over (B.obj hS)) F)
    {I : Type u} (G : I → (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hG : ∀ i, AlgebraicGeometry.IsAlgebraicSpace B S hS (G i))
    (k : ∀ i, G i ⟶ F)
    (hk : ∀ i, (MorphismProperty.inverseImage (@IsOpenImmersion.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf (k i))
    (hcover : ∀ (W : AlgebraicGeometry.BigFppfOver B S hS) (x : F.obj (op W)),
      ∃ R : Sieve W, R ∈ AlgebraicGeometry.BigFppfOver.topology B S hS W ∧
        ∀ ⦃W'⦄ (g : W' ⟶ W), R g → ∃ (i : I) (z : (G i).obj (op W')),
          (k i).app (op W') z = F.map g.op x)
    (A : I → AlgebraicGeometry.BigFppfOver B S hS) (a : ∀ i, yoneda.obj (A i) ⟶ G i)
    (hs : ∀ i, (MorphismProperty.inverseImage (@Surjective.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf (a i))
    (he : ∀ i, (MorphismProperty.inverseImage (@Etale.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf (a i))
    (A₀ : AlgebraicGeometry.BigFppfOver B S hS) (j : ∀ i, A i ⟶ A₀)
    (hA₀ : IsColimit (Cofan.mk A₀ j)) :
    AlgebraicGeometry.IsAlgebraicSpace B S hS F := by
  classical
  let J := AlgebraicGeometry.BigFppfOver.topology B S hS
  let P := MorphismProperty.inverseImage (@IsOpenImmersion.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  have hmono (i : I) : Mono (k i) := by
    apply MorphismProperty.presheaf_monomorphisms_le_monomorphisms
    apply MorphismProperty.relative_monotone (P := P) _ _ (hk i)
    intro X Y f hf
    have : IsOpenImmersion ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f) := hf
    exact (AlgebraicGeometry.BigFppfOver.toScheme B S hS).mono_of_mono_map (inferInstance : Mono _)
  let H : I → Subfunctor F := fun i => Subfunctor.range (k i)
  let e (i : I) : G i ≅ (H i).toFunctor := asIso (Subfunctor.toRange (k i))
  have hH (i : I) : AlgebraicGeometry.IsAlgebraicSpace B S hS (H i).toFunctor :=
    isAlgebraicSpace_of_iso B S hS (e i).symm (hG i)
  have hrep (i : I) : AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces B S hS (H i).ι := by
    have hrel : yoneda.relativelyRepresentable (H i).ι :=
      (MorphismProperty.cancel_left_of_respectsIso _ (e i).hom _).mp (hk i).rep
    intro W ξ
    exact isAlgebraicSpace_of_iso B S hS
      ((hrel.isPullback ξ).flip.isoIsPullback _ _ (IsPullback.of_hasPullback ξ (H i).ι)).symm
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (hrel.pullback ξ))
  have hcovH : Presheaf.IsLocallySurjective J (iSup H).ι := by
    constructor
    intro W x
    obtain ⟨R, hR, hl⟩ := hcover W x
    apply J.superset_covering _ hR
    intro W' g hg
    obtain ⟨i, z, hz⟩ := hl g hg
    refine ⟨⟨F.map g.op x, ?_⟩, rfl⟩
    exact (le_iSup H i) _ ⟨z, hz⟩
  have hF' := AlgebraicGeometry.Space.isSheaf_of_locallySurjective_representable_subfunctors
    B S hS F hF I H (fun i => (hH i).isSheaf) hrep hcovH
  let GS : I → Sheaf J (Type u) := fun i => ⟨G i, (hG i).isSheaf⟩
  let FS : Sheaf J (Type u) := ⟨F, hF'⟩
  let : EssentiallySmall.{u} (AlgebraicGeometry.BigFppfOver B S hS) :=
    AlgebraicGeometry.Stack.essentiallySmall_bigFppfOver B S hS
  let : HasSheafify J (Type u) := hasSheafifyEssentiallySmallSite.{_, _, _, _, u} J (Type u)
  let : HasColimitsOfShape (Discrete I) (Sheaf J (Type u)) :=
    Sheaf.instHasColimitsOfShape
  let C : Sheaf J (Type u) := ∐ GS
  let ι : ∀ i, GS i ⟶ C := Sigma.ι GS
  let kS : C ⟶ FS := Sigma.desc (f := GS) (fun i => ⟨k i⟩)
  have hkS (i : I) : (ι i).hom ≫ kS.hom = k i :=
    congrArg (fun φ : GS i ⟶ FS => φ.hom)
      (Sigma.ι_desc (f := GS) (fun i => (⟨k i⟩ : GS i ⟶ FS)) i)
  have hsurj : Presheaf.IsLocallySurjective J kS.hom := by
    constructor
    intro W x
    obtain ⟨R, hR, hl⟩ := hcover W x
    apply J.superset_covering _ hR
    intro W' g hg
    obtain ⟨i, z, hz⟩ := hl g hg
    exact ⟨(ι i).hom.app (op W') z, (congrArg (fun t => t.app (op W') z) (hkS i)).trans hz⟩
  have hC := AlgebraicGeometry.isAlgebraicSpace_coproduct B S hS G hG C ι
    (coproductIsCoproduct GS) A a hs he A₀ j hA₀
  exact AlgebraicGeometry.isAlgebraicSpace_of_open_cover B S hS F hF' I GS hG C ι
    (coproductIsCoproduct GS) kS.hom (fun i => by rw [hkS]; exact hk i) hsurj hC

end RelocalizeCover

open CategoryTheory.Limits in
/-- **Stacks 07WH.** Let `S` be a scheme of a big fppf site, let `T` be an object of the big fppf
site of `S` and put `κ = size T`. A 1-morphism `f : 𝒳 ⟶ 𝒴` of categories fibred in groupoids over
the big fppf site of `S` is representable by algebraic spaces as soon as

* the structure morphism `𝒴 ⟶ (Sch/S)_{fppf}` is limit preserving on objects,
* for every affine `V` locally of finite presentation over `S` and every point `y` of `𝒴` over
  `V`, the 2-fibre product `(Sch/V)_{fppf} ×_{y, 𝒴} 𝒳` is representable by an algebraic space
  carrying a surjective étale atlas by a scheme of size at most `κ`, and
* `𝒳` and `𝒴` are stacks in groupoids for the big Zariski topology over `S`.

The bound by the size of a single object of the site is the source's set-theoretic hypothesis; it
is what makes the coproduct of the charts of an open cover again an object of the site. -/
@[stacks 07WH]
public theorem isRepresentableByAlgebraicSpaces_of_limitPreservingOnObjects
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (AlgebraicGeometry.BigFppfOver B S hS))
    (f : 𝒳 ⟶ 𝒴)
    (hlimit : AlgebraicGeometry.BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B S hS 𝒴
      (AlgebraicGeometry.Stack.terminalCFG B S hS)
      (Bicategory.InducedBicategory.mkHom (AlgebraicGeometry.Stack.toTerminalCFG B S hS 𝒴)))
    (hlocal : ∀ (U : AlgebraicGeometry.BigFppfOver B S hS),
      IsAffine U.left.1 →
      LocallyOfFinitePresentation (B.inclusion.map U.hom) →
      let 𝒰 := AlgebraicGeometry.BigFppfOver B U.left.1 U.left.2
      let p𝒰 : 𝒰 ⥤ AlgebraicGeometry.BigFppfOver B S hS := Over.map U.hom
      ∀ (y : 𝒰 ⥤ 𝒴.val.obj) (_hy : y ⋙ 𝒴.val.p = p𝒰),
        ∃ F : 𝒰ᵒᵖ ⥤ Type u,
          AlgebraicGeometry.IsAlgebraicSpace B U.left.1 U.left.2 F ∧
          Nonempty (StacksRepresentableCFG.EquivalenceOver
            (TwoFibreProductOver.fst p𝒰 𝒳.val.p 𝒴.val.p y
              (CatFiberedInGroupoids.homFunctor f))
            (presheafOfCategories (F ⋙ typeToCat)).p) ∧
          ∃ (A : 𝒰) (a : yoneda.obj A ⟶ F),
            A.left.1.size ≤ T.left.1.size ∧
            (MorphismProperty.presheaf
              (MorphismProperty.inverseImage
                (@Surjective.{u} : MorphismProperty Scheme.{u})
                (AlgebraicGeometry.BigFppfOver.toScheme B U.left.1 U.left.2))) a ∧
            (MorphismProperty.presheaf
              (MorphismProperty.inverseImage
                (@Etale.{u} : MorphismProperty Scheme.{u})
                (AlgebraicGeometry.BigFppfOver.toScheme B U.left.1 U.left.2))) a)
    (h𝒳 : 𝒳.val.p.IsStackInGroupoids.{u + 1}
      ((AlgebraicGeometry.BigFppfSite.zariskiTopology B).over (B.obj hS)))
    (h𝒴 : 𝒴.val.p.IsStackInGroupoids.{u + 1}
      ((AlgebraicGeometry.BigFppfSite.zariskiTopology B).over (B.obj hS))) :
    AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom := by
  classical
  intro U
  dsimp only [AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpaces]
  intro y hy
  let 𝒰 := AlgebraicGeometry.BigFppfOver B U.left.1 U.left.2
  let f₀ := CatFiberedInGroupoids.homFunctor f
  let p := TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y f₀
  let J := (AlgebraicGeometry.BigFppfSite.zariskiTopology B).over U.left
  have hp : p.IsFiberedInGroupoids := fst_isFiberedInGroupoids_overMap
    U.hom 𝒳.val.p 𝒴.val.p y f₀ 𝒳.isFiberedInGroupoids 𝒴.isFiberedInGroupoids
    hy (CatFiberedInGroupoids.homFunctor_comp_p f)
  let := hp.isFibered
  have : B.topology.Subcanonical :=
    AlgebraicGeometry.BigFppfSite.subcanonical_topology B
  have : (AlgebraicGeometry.BigFppfSite.zariskiTopology B).Subcanonical :=
    GrothendieckTopology.Subcanonical.of_le (zariskiTopology_le_fppf B)
  have hstack : p.IsStack J := fst_isStack_overMap U.hom 𝒳.val.p 𝒴.val.p y f₀
    (AlgebraicGeometry.BigFppfSite.zariskiTopology B) h𝒳 h𝒴 hy
    (CatFiberedInGroupoids.homFunctor_comp_p f)
  let Rep (W : 𝒰) : Prop :=
    ∃ F : (AlgebraicGeometry.BigFppfOver B W.left.1 W.left.2)ᵒᵖ ⥤ Type u,
      AlgebraicGeometry.IsAlgebraicSpace B W.left.1 W.left.2 F ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map (W.hom ≫ U.hom)) 𝒳.val.p 𝒴.val.p
          (Over.map W.hom ⋙ y) f₀) (presheafOfCategories (F ⋙ typeToCat)).p) ∧
      ∃ (A : AlgebraicGeometry.BigFppfOver B W.left.1 W.left.2) (a : yoneda.obj A ⟶ F),
        A.left.1.size ≤ max T.left.1.size W.left.1.size ∧
        (MorphismProperty.inverseImage (@Surjective.{u})
          (AlgebraicGeometry.BigFppfOver.toScheme B W.left.1 W.left.2)).presheaf a ∧
        (MorphismProperty.inverseImage (@Etale.{u})
          (AlgebraicGeometry.BigFppfOver.toScheme B W.left.1 W.left.2)).presheaf a
  have hcover (W : 𝒰) :
      ∃ (I : Type u) (V : I → 𝒰) (j : ∀ i, V i ⟶ W),
        Cardinal.mk I ≤ W.left.1.size ∧ Sieve.ofArrows V j ∈ J W ∧
        (∀ i, IsOpenImmersion (B.inclusion.map (j i).left)) ∧ ∀ i, Rep (V i) := by
    obtain ⟨I, V, j, hI, hcov, hopen, hV⟩ :=
      exists_affine_site_cover B (W.hom ≫ U.hom)
    let V' : I → 𝒰 := fun i => Over.mk (j i ≫ W.hom)
    let j' : ∀ i, V' i ⟶ W := fun i => Over.homMk (j i) rfl
    refine ⟨I, V', j', hI, ?_, hopen, ?_⟩
    · rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
      exact hcov
    · intro i
      obtain ⟨haff, R, hR, r, hr, q, hq⟩ := hV i
      have : IsAffine (Over.mk ((j i ≫ W.hom) ≫ U.hom)).left.1 := haff
      exact exists_algebraicSpace_fibre_of_affineFactorization B S hS T 𝒳 𝒴 f
        hlimit hlocal (Over.mk ((j i ≫ W.hom) ≫ U.hom)) R hR r q
        (by
          change q ≫ r = B.inclusion.map ((j i ≫ W.hom) ≫ U.hom)
          simpa only [Category.assoc] using hq) (Over.map (j i ≫ W.hom) ⋙ y)
        (by rw [Functor.assoc, hy, ← Over.mapComp_eq]; rfl)
  have hthin : p.IsFiberedInSetoids := by
    apply isFiberedInSetoids_of_thin_cover p hp J hstack
    intro W
    obtain ⟨I, V, j, _, hc, _, hV⟩ := hcover W
    refine ⟨I, V, j, hc, fun i => ?_⟩
    obtain ⟨F, _, ⟨e⟩, _⟩ := hV i
    have ht := fst_fiber_isThin_of_represented_restriction
      (V i).hom U.hom 𝒳.val.p 𝒴.val.p y f₀ F e
    have he : Over.mk (V i).hom = V i := by cases V i; rfl
    rwa [he] at ht
  have hsheaf : Presheaf.IsSheaf J p.isoClassPresheaf :=
    isSheaf_isoClassPresheaf p J hstack
  have hsmall : FunctorToTypes.Small.{u} p.isoClassPresheaf := by
    intro W
    obtain ⟨I, V, j, _, hc, _, hV⟩ := hcover W.unop
    have hVi (i : I) : Small.{u} (p.isoClassPresheaf.obj (.op (V i))) := by
      obtain ⟨F, _, ⟨e⟩, _⟩ := hV i
      have hs := small_fst_isoClass_of_represented_restriction
        (V i).hom U.hom 𝒳.val.p 𝒴.val.p y f₀ hp F e
      have he : Over.mk (V i).hom = V i := by cases V i; rfl
      rwa [he] at hs
    exact small_obj_of_isSheaf_cover J p.isoClassPresheaf hsheaf V j hc
  let Z := FunctorToTypes.shrink.{u} p.isoClassPresheaf
  let eZ (W : 𝒰ᵒᵖ) : p.isoClassPresheaf.obj W ≃ Z.obj W := equivShrink _
  have heZ {W W' : 𝒰ᵒᵖ} (g : W ⟶ W') (x : p.isoClassPresheaf.obj W) :
      eZ W' (p.isoClassPresheaf.map g x) = Z.map g (eZ W x) := by
    simp [Z, eZ, FunctorToTypes.shrink]
  let 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} 𝒰 :=
    ⟨BasedCategory.ofFunctor p, hp⟩
  apply (AlgebraicGeometry.isRepresentableByAlgebraicSpace_iff B U.left.1 U.left.2 𝒵).mpr
  refine ⟨hthin, Z, ?_, eZ, fun _ _ g x => heZ g x⟩
  have hZsheaf : Presheaf.IsSheaf J Z := by
    rw [isSheaf_iff_isSheaf_of_type] at hsheaf ⊢
    exact Presieve.isSheaf_of_nat_equiv (fun {_} => eZ _) (fun {_ _} g x => heZ g.op x) hsheaf
  obtain ⟨I, V, j, hI, hcov, hopen, hV⟩ := hcover (Over.mk (𝟙 U.left))
  have hji (i : I) : (j i).left = (V i).hom := by
    have h := (j i).w
    change (j i).left ≫ 𝟙 U.left = (V i).hom at h
    exact (Category.comp_id (j i).left).symm.trans h
  have hVo (i : I) : IsOpenImmersion (B.inclusion.map (V i).hom) := by
    simpa only [hji] using hopen i
  choose F hF ee hAt using hV
  let e (i : I) : F i ≅ (OverShriek.relocalizeRestrict (V i).hom).obj Z :=
    representedRestrictionIso (V i).hom U.hom 𝒳.val.p 𝒴.val.p y f₀ hp (F i)
      (ee i).some Z eZ (fun _ _ g x => heZ g x)
  have hrest (i : I) : AlgebraicGeometry.IsAlgebraicSpace B (V i).left.1 (V i).left.2
      ((OverShriek.relocalizeRestrict (V i).hom).obj Z) :=
    isAlgebraicSpace_of_iso B (V i).left.1 (V i).left.2 (e i).symm (hF i)
  let H (i : I) := (OverShriek.relocalizePresheafFunctor (V i).hom).obj
    ((OverShriek.relocalizeRestrict (V i).hom).obj Z)
  let k (i : I) : H i ⟶ Z :=
    OverShriek.relocalizeOfRestricted (V i).hom (𝟙 _)
  have hH (i : I) : AlgebraicGeometry.IsAlgebraicSpace B U.left.1 U.left.2 (H i) :=
    AlgebraicGeometry.isAlgebraicSpace_viewOver B (V i).left.1 U.left.1 (V i).left.2 U.left.2
      (V i).hom _ (hrest i)
  have hk (i : I) : (MorphismProperty.inverseImage (@IsOpenImmersion.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B U.left.1 U.left.2)).presheaf (k i) :=
    relocalizeCounit_open B U.left.1 U.left.2 (V i) (hVo i) Z
  have hraw : Sieve.ofArrows (fun i => (V i).left) (fun i => (V i).hom) ∈ B.topology U.left := by
    apply zariskiTopology_le_fppf B
    have hc := (GrothendieckTopology.mem_over_iff _ _).mp hcov
    rw [Sieve.overEquiv_ofArrows] at hc
    change Sieve.ofArrows (fun i => (V i).left) (fun i => (j i).left) ∈
      AlgebraicGeometry.BigFppfSite.zariskiTopology B U.left at hc
    simpa only [hji] using hc
  choose A a hA hs he using hAt
  let A' (i : I) : 𝒰 := (Over.map (V i).hom).obj (A i)
  let a' (i : I) : yoneda.obj (A' i) ⟶ H i :=
    ((OverShriek.relocalizeYonedaIso (V i).hom).app (A i)).inv ≫
      (OverShriek.relocalizePresheafFunctor (V i).hom).map (a i ≫ (e i).hom)
  have hEtale : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hP (P : MorphismProperty Scheme.{u}) [P.RespectsIso] (i : I)
      (h : (MorphismProperty.inverseImage P
        (AlgebraicGeometry.BigFppfOver.toScheme B (V i).left.1 (V i).left.2)).presheaf (a i)) :
      (MorphismProperty.inverseImage P
        (AlgebraicGeometry.BigFppfOver.toScheme B U.left.1 U.left.2)).presheaf (a' i) := by
    have : (MorphismProperty.inverseImage P
        (AlgebraicGeometry.BigFppfOver.toScheme B U.left.1 U.left.2)).RespectsIso :=
      MorphismProperty.RespectsIso.inverseImage _ _
    have : (MorphismProperty.presheaf (MorphismProperty.inverseImage P
        (AlgebraicGeometry.BigFppfOver.toScheme B U.left.1 U.left.2))).RespectsIso :=
      (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _).respectsIso
    have : (MorphismProperty.presheaf (MorphismProperty.inverseImage P
        (AlgebraicGeometry.BigFppfOver.toScheme B (V i).left.1 (V i).left.2))).RespectsIso :=
      (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _).respectsIso
    have h₀ : (MorphismProperty.inverseImage P
        (AlgebraicGeometry.BigFppfOver.toScheme B (V i).left.1 (V i).left.2)).presheaf
        (a i ≫ (e i).hom) :=
      MorphismProperty.RespectsIso.postcomp _ _ _ h
    exact MorphismProperty.RespectsIso.precomp _ _ _
      (OverShriek.presheaf_map_relocalize _ (fun s hs => hs) h₀)
  let μ := max T.left.1.size U.left.1.size
  have hμ : μ < B.cutoff := max_lt T.left.2 U.left.2
  have hμinf : Cardinal.aleph0 ≤ μ :=
    (Scheme.aleph0_le_size T.left.1).trans (le_max_left _ _)
  have hIμ : Cardinal.mk I ≤ μ := hI.trans (le_max_right _ _)
  have hsize (i : I) :
      ((AlgebraicGeometry.BigFppfOver.toScheme B U.left.1 U.left.2).obj (A' i)).size ≤ μ := by
    have := hVo i
    exact (hA i).trans (max_le_max le_rfl
      (Scheme.size_le_of_mono_locallyOfFinitePresentation (B.inclusion.map (V i).hom)))
  have hsum : B.Contains (∐ fun i =>
      (AlgebraicGeometry.BigFppfOver.toScheme B U.left.1 U.left.2).obj (A' i)) :=
    (AlgebraicGeometry.schemeSize_coproduct_le _ μ hμinf hIμ hsize).trans_lt hμ
  let A₀ := AlgebraicGeometry.BigFppfOver.sigmaOver B U.left.1 U.left.2 A' hsum
  let j₀ := AlgebraicGeometry.BigFppfOver.sigmaOverInj B U.left.1 U.left.2 A' hsum
  have hA₀ : Limits.IsColimit (Limits.Cofan.mk A₀ j₀) := by
    apply Limits.isColimitOfReflects (AlgebraicGeometry.BigFppfOver.toScheme B U.left.1 U.left.2)
    exact (Limits.isColimitMapCoconeCofanMkEquiv
      (AlgebraicGeometry.BigFppfOver.toScheme B U.left.1 U.left.2) A' j₀).symm
      (AlgebraicGeometry.BigFppfOver.isColimit_toScheme_sigmaOver
        B U.left.1 U.left.2 A' hsum)
  apply isAlgebraicSpace_of_open_family B U.left.1 U.left.2 Z hZsheaf H hH k hk
    (fun W x => locally_factors_relocalizeCounit B.topology
      (fun i => (V i).left) (fun i => (V i).hom) hraw Z W x)
    A' a' (fun i => hP _ i (hs i)) (fun i => hP _ i (he i)) A₀ j₀ hA₀

end AlgebraicGeometry.Stack

end
