module

public import Mathlib.CategoryTheory.Adhesive.Basic
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.RegularEpi
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupIsomorphismOffCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductCountable
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductInclusion
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductSummand
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSource.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.MorphismsToAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EquivalenceRelationGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.CoveringMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Unconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints
import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedTfae
import StacksFrontier.AlgebraicGeometry.Stacks.SmoothMonomorphismOpenImmersion

/-!
# Constructing elementary distinguished squares

Let `V` and `U` be algebraic spaces over a scheme `S`, let `V'` be an open subspace of `V` and
let `f' : V' ⟶ U` be a separated étale morphism. Glueing `V` to `U` along `f'` produces an
algebraic space `W` which is the pushout of `V ← V' → U`, and `(U ⊂ W, V ⟶ W)` is an
elementary distinguished square.

## Main results

* `AlgebraicGeometry.Space.exists_pushout_isElementaryDistinguishedSquare`: **Stacks 0DVJ**.

## Implementation notes

**The quotient by an étale equivalence relation is Stacks 04S6, part (1).** The source glues
`W` as the quotient of an étale equivalence relation on `U ⨿ V`, an algebraic space by
[Stacks, Tag 04S6]. That is
`AlgebraicGeometry.Space.bootstrap04S6QuotientSheaf` (condition (1)), applied to the pre-relation
of a groupoid in algebraic spaces whose source and target are flat and locally of finite
presentation. The unconditional
`AlgebraicGeometry.Space.isAlgebraicSpace_quotient_unconditional` — [Stacks, Tag 02WW] — is the
étale case for a relation on an *object of the site*, so it does not apply to the relation on
`U ⨿ V` built here.

The construction follows the source. The relation
`R = U ⨿ V' ⨿ V' ⨿ V ⨿ (V' ×_U V' ∖ Δ)` on `U ⨿ V` of the source is replaced by the kernel
pair of the map `U ⨿ V ⟶ W` out of the sheaf pushout `W` of `V' ⟶ V` along `f' : V' ⟶ U`:
sheaves of sets on the big fppf site form an adhesive category, so that pushout is also a
pullback with `U ⟶ W` a monomorphism, and extensivity decomposes its kernel pair into exactly
the five pieces of the source. Separatedness of `f'` is what makes the fifth piece — the
complement of the diagonal in `V' ×_U V'` — an open subspace, hence an algebraic space. The
quotient of `U ⨿ V` by that relation is `W` again, which is how 04S6 gives `W` its
algebraic-space structure; `U ⟶ W` is then étale and a monomorphism, hence an open immersion
by `AlgebraicGeometry.Space.isOpenImmersion_of_isEtale_of_mono` (the open immersion clause of
[Stacks, Tag 05W5]), and the complement of its image meets `U` nowhere, so adhesiveness makes
`V ⟶ W` an isomorphism over it.

## References

* [Stacks Project, Tag 0DVJ](https://stacks.math.columbia.edu/tag/0DVJ)
* [Stacks Project, Tag 0DVI](https://stacks.math.columbia.edu/tag/0DVI)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 05W5](https://stacks.math.columbia.edu/tag/05W5)
* [Stacks Project, Tag 08GM](https://stacks.math.columbia.edu/tag/08GM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Coproducts in an adhesive extensive category -/

section Generic

variable {C : Type u} [Category.{v} C]

/-- In an extensive category the square identifying `A ⨿ D` as the base change of `V ⨿ D`
along a monomorphism `i : A ⟶ V`, where `D` maps to `V` through `i`. -/
private theorem isPullback_coprod_of_mono [HasPullbacks C] [FinitaryExtensive C]
    {A V D : C} (i : A ⟶ V) [Mono i] (a : D ⟶ A) :
    IsPullback (coprod.desc (𝟙 A) a) (coprod.map i (𝟙 D))
      i (coprod.desc (𝟙 V) (a ≫ i)) := by
  let X := pairFunction V D
  let P := pairFunction A D
  let cV : Cofan X := BinaryCofan.mk (coprod.inl : V ⟶ V ⨿ D) coprod.inr
  let cA : Cofan P := BinaryCofan.mk (coprod.inl : A ⟶ A ⨿ D) coprod.inr
  let fs : ∀ j, X j ⟶ V := fun j => WalkingPair.casesOn j (𝟙 V) (a ≫ i)
  let q₁ : ∀ j, P j ⟶ A := fun j => WalkingPair.casesOn j (𝟙 A) a
  let q₂ : ∀ j, P j ⟶ X j := fun j => WalkingPair.casesOn j i (𝟙 D)
  have hiV : IsColimit cV := coprodIsCoprod V D
  have hiA : IsColimit cA := coprodIsCoprod A D
  have hP : ∀ j, IsPullback (q₁ j) (q₂ j) i (fs j) := by
    rintro (_ | _)
    · exact IsPullback.id_horiz i
    · refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
        (show a ≫ i = (𝟙 D) ≫ (a ≫ i) by rw [Category.id_comp])
        (fun s => s.snd) ?_ (fun s => Category.comp_id _) ?_)
      · intro s
        apply (cancel_mono i).mp
        rw [Category.assoc]
        exact s.condition.symm
      · intro s m _ hm
        simpa using hm
  have hu : ∀ j, cV.inj j ≫ coprod.desc (𝟙 V) (a ≫ i) = fs j := by
    rintro (_ | _)
    exacts [coprod.inl_desc (𝟙 V) (a ≫ i), coprod.inr_desc (𝟙 V) (a ≫ i)]
  have h := IsUniversalColimit.isPullback_of_isColimit_left
    (FinitaryExtensive.vanKampen _ hiV).isUniversal
    fs (coprod.desc (𝟙 V) (a ≫ i)) i q₁ q₂ hP hiA hu
  have he₁ : Cofan.IsColimit.desc hiA q₁ = coprod.desc (𝟙 A) a :=
    Cofan.IsColimit.hom_ext hiA _ _ fun j => by
      cases j
      · exact (Cofan.IsColimit.fac hiA q₁ WalkingPair.left).trans
          (coprod.inl_desc (𝟙 A) a).symm
      · exact (Cofan.IsColimit.fac hiA q₁ WalkingPair.right).trans
          (coprod.inr_desc (𝟙 A) a).symm
  have he₂ : Cofan.IsColimit.desc hiA (fun j => q₂ j ≫ cV.inj j) = coprod.map i (𝟙 D) :=
    Cofan.IsColimit.hom_ext hiA _ _ fun j => by
      cases j
      · exact (Cofan.IsColimit.fac hiA (fun j => q₂ j ≫ cV.inj j) WalkingPair.left).trans
          (coprod.inl_map i (𝟙 D)).symm
      · exact (Cofan.IsColimit.fac hiA (fun j => q₂ j ≫ cV.inj j) WalkingPair.right).trans
          (coprod.inr_map i (𝟙 D)).symm
  rwa [he₁, he₂] at h

attribute [local simp] coprod.inl_desc coprod.inr_desc

/-- Collapsing the summand `D` of `A ⨿ D` onto `A` and then pushing along `i : A ⟶ V` is the
same as pushing `A ⨿ D` into `V ⨿ D` and then collapsing. -/
private theorem isPushout_coprod_map_desc [HasBinaryCoproducts C]
    {A V D : C} (i : A ⟶ V) (a : D ⟶ A) :
    IsPushout (coprod.map i (𝟙 D)) (coprod.desc (𝟙 A) a)
      (coprod.desc (𝟙 V) (a ≫ i)) i := by
  have hw : coprod.map i (𝟙 D) ≫ coprod.desc (𝟙 V) (a ≫ i) =
      coprod.desc (𝟙 A) a ≫ i := by
    apply coprod.hom_ext <;> simp
  refine ⟨⟨hw⟩, ⟨PushoutCocone.IsColimit.mk _
    (fun s => coprod.inl ≫ s.inl) ?_ ?_ ?_⟩⟩
  · intro s
    apply coprod.hom_ext
    · simp
    · have hA := congrArg (fun k => (coprod.inl : A ⟶ A ⨿ D) ≫ k) s.condition
      have hD := congrArg (fun k => (coprod.inr : D ⟶ A ⨿ D) ≫ k) s.condition
      simp only [coprod.inl_map_assoc, coprod.inl_desc_assoc,
        Category.id_comp] at hA
      simp only [coprod.inr_map_assoc, coprod.inr_desc_assoc,
        Category.id_comp] at hD
      simpa [Category.assoc, hA] using hD.symm
  · intro s
    simpa using congrArg (fun k => (coprod.inl : A ⟶ A ⨿ D) ≫ k) s.condition
  · intro s m hm _
    simpa using congrArg (fun k => (coprod.inl : V ⟶ V ⨿ D) ≫ k) hm

/-- In an adhesive extensive category, a kernel pair of the shape `A ⨿ D ⇉ A` transported
along a pushout square with monomorphic left leg stays a kernel pair. -/
private theorem isPullback_coprod_kernelPair [HasPullbacks C] [FinitaryExtensive C]
    [Adhesive C] {A U V W D : C} (i : A ⟶ V) [Mono i] (g : A ⟶ U)
    (f : V ⟶ W) (j : U ⟶ W) (a b : D ⟶ A)
    (h : IsPushout i g f j)
    (hP : IsPullback (coprod.desc (𝟙 A) a) (coprod.desc (𝟙 A) b) g g) :
    IsPullback (coprod.desc (𝟙 V) (a ≫ i))
      (coprod.desc (𝟙 V) (b ≫ i)) f f := by
  have hw : coprod.desc (𝟙 V) (b ≫ i) ≫ f =
      coprod.desc (𝟙 V) (a ≫ i) ≫ f := by
    have hab := congrArg (fun k => (coprod.inr : D ⟶ A ⨿ D) ≫ k) hP.w
    simp only [coprod.inr_desc_assoc] at hab
    apply coprod.hom_ext
    · simp
    · simpa [Category.assoc, h.w] using congrArg (fun k => k ≫ j) hab.symm
  have htop := isPushout_coprod_map_desc i b
  exact (((Adhesive.van_kampen h)
    (coprod.map i (𝟙 D)) (coprod.desc (𝟙 A) b)
    (coprod.desc (𝟙 V) (b ≫ i)) i
    (coprod.desc (𝟙 A) a) (coprod.desc (𝟙 V) (a ≫ i)) g f
    (isPullback_coprod_of_mono i a).flip hP.flip
    ⟨hw⟩ h.toCommSq htop.toCommSq).mp htop).1.flip

/-- A pushout of a monomorphism in an adhesive category is also a pullback, with monomorphic
opposite leg. -/
private theorem exists_pushout_of_mono [Adhesive C] [HasPushouts C]
    {A U V : C} (i : A ⟶ V) (g : A ⟶ U) [Mono i] :
    ∃ (W : C) (f : V ⟶ W) (j : U ⟶ W), IsPushout i g f j ∧ IsPullback i g f j ∧ Mono j :=
  ⟨pushout i g, pushout.inl i g, pushout.inr i g, IsPushout.of_hasPushout i g,
    Adhesive.isPullback_of_isPushout_of_mono_left (IsPushout.of_hasPushout i g),
    Adhesive.mono_of_isPushout_of_mono_left (IsPushout.of_hasPushout i g)⟩

/-- An equivalence relation structure transported from a kernel pair in a category into which
the ambient category embeds fully faithfully. -/
private def equivalenceRelation_of_isKernelPair_map {D : Type*} [Category D]
    (F : C ⥤ D) [F.Full] [F.Faithful]
    {R X : C} (s t : R ⟶ X) [HasPullback t s]
    {Y : D} (q : F.obj X ⟶ Y)
    (h : IsKernelPair q (F.map s) (F.map t)) : EquivalenceRelation s t := by
  have hw : F.map (pullback.fst t s ≫ s) ≫ q =
      F.map (pullback.snd t s ≫ t) ≫ q := by
    simp only [Functor.map_comp, Category.assoc]
    rw [h.w, ← Category.assoc, ← F.map_comp, pullback.condition,
      F.map_comp, Category.assoc, ← h.w]
  refine
    { right_cancellation := ?_
      r := F.preimage (h.lift (𝟙 _) (𝟙 _) (by simp))
      s := F.preimage (h.lift (F.map t) (F.map s) h.w.symm)
      c := pullback.cone t s
      isLimit := pullback.isLimit t s
      t := F.preimage (h.lift (F.map (pullback.fst t s ≫ s))
        (F.map (pullback.snd t s ≫ t)) hw)
      reflexivity₁ := ?_
      reflexivity₂ := ?_
      symmetry₁ := ?_
      symmetry₂ := ?_
      transitivity₁ := ?_
      transitivity₂ := ?_ }
  · intro Z a b ha hb
    apply F.map_injective
    exact h.hom_ext (by simp only [← F.map_comp, ha])
      (by simp only [← F.map_comp, hb])
  all_goals
    apply F.map_injective
    simp only [Functor.map_comp, Functor.map_preimage,
      IsKernelPair.lift_fst, IsKernelPair.lift_snd, pullback.cone,
      PullbackCone.fst_limit_cone, PullbackCone.snd_limit_cone]
  all_goals exact (F.map_id X).symm

/-- In an adhesive category with strict initial objects, the base change of a pushout along a
map whose other leg has initial base change is an isomorphism. -/
private theorem isIso_pullback_of_initial_other_leg [Adhesive C] [HasPullbacks C]
    [HasStrictInitialObjects C] {A U V W Z P T : C}
    (i : A ⟶ V) [Mono i] (g : A ⟶ U) (f : V ⟶ W) (j : U ⟶ W)
    (h : IsPushout i g f j) (z : Z ⟶ W)
    (p : P ⟶ Z) (a : P ⟶ V) (r : T ⟶ Z) (b : T ⟶ U)
    (hp : IsPullback p a z f) (hr : IsPullback r b z j) (hT : IsInitial T) :
    IsIso p := by
  obtain ⟨A', i', g', a', _, _, htop⟩ :=
    ((IsPushout.isVanKampen_iff'.mp (Adhesive.van_kampen h)) p r a b z
      hp.toCommSq hr.toCommSq).mp ⟨hp, hr⟩
  exact htop.isIso_inl_of_isIso (hT.isIso_to g')

end Generic

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Elementary facts about morphisms of algebraic spaces -/

/-- An open immersion is an isomorphism onto its range. -/
private def isoRange_of_isOpenImmersion
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hf : IsOpenImmersion B S hS f) :
    {e : F ≅ (Subfunctor.range f).toFunctor // e.hom ≫ (Subfunctor.range f).ι = f} := by
  have : Mono f := mono_of_isOpenImmersion B S hS f hf
  exact ⟨asIso (Subfunctor.toRange f), Subfunctor.toRange_ι f⟩

/-- The open subspace complementary to the image of a closed immersion of algebraic spaces. -/
private def openComplementSubspace
    {Z X : AlgebraicSpaces B S hS} (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom) :
    {U : Subfunctor X.obj // IsOpenSubspace B S hS U} := by
  have hle : (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) ≤
      (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}) := by
    intro A C f hf
    let _ : _root_.AlgebraicGeometry.IsClosedImmersion f := hf
    infer_instance
  have himm : IsImmersion B S hS i.hom :=
    (MorphismProperty.relative_monotone
      (MorphismProperty.monotone_inverseImage (BigFppfOver.toScheme B S hS) hle)) _ hi
  have hc : IsClosed (Set.range (pointsMap B S hS Z.obj i.hom)) :=
    (isClosedImmersion_iff_isClosed_range_pointsMap B S hS X.property i.hom himm).mp hi
  exact (openSubspacesOrderIso B S hS X.obj X.property).symm ⟨_, hc.isOpen_compl⟩

/-- The points of the open complement of a closed immersion are the complement of its
points. -/
private theorem pointsMap_openComplement
    {Z X : AlgebraicSpaces B S hS} (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom) :
    Set.range (pointsMap B S hS (openComplementSubspace B S hS i hi).1.toFunctor
        (openComplementSubspace B S hS i hi).1.ι) =
      (Set.range (pointsMap B S hS Z.obj i.hom))ᶜ := by
  rw [← openSubspacesOrderIso_apply B S hS X.obj X.property (openComplementSubspace B S hS i hi)]
  simp only [openComplementSubspace, OrderIso.apply_symm_apply]

/-- The complement of the diagonal of a separated morphism of algebraic spaces, as an
algebraic space open in the fibre square. -/
private def offDiagonalAlgebraicSpace
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hfsep : IsSeparated B S hS f.hom) :
    Σ D : AlgebraicSpaces B S hS,
      { d : D ⟶ AlgebraicSpaces.fiberProduct B S hS f f //
        IsOpenImmersion B S hS d.hom ∧
          Set.range (pointsMap B S hS D.obj d.hom) =
            (Set.range (pointsMap B S hS X.obj (pullback.diagonal f.hom)))ᶜ } := by
  let P := AlgebraicSpaces.fiberProduct B S hS f f
  let d : X ⟶ P := ObjectProperty.homMk (pullback.diagonal f.hom)
  have hd : IsClosedImmersion B S hS d.hom := hfsep
  let O := openComplementSubspace B S hS d hd
  let D : AlgebraicSpaces B S hS := ⟨O.1.toFunctor, O.2.1⟩
  exact ⟨D, ObjectProperty.homMk O.1.ι, O.2.2, pointsMap_openComplement B S hS d hd⟩

/-- A morphism of algebraic spaces out of one with no points is unique. -/
private theorem hom_ext_of_isEmpty_points
    {X Y : AlgebraicSpaces B S hS} (hX : IsEmpty (points B S hS X.obj)) (f g : X ⟶ Y) :
    f = g := by
  let A : Empty → AlgebraicSpaces B S hS := Empty.elim
  let i : ∀ a, A a ⟶ X := fun a => a.elim
  have hc : IsEtaleCovering B S hS (fun a => (A a).obj) (fun a => (i a).hom) := by
    refine ⟨X.property, (fun a => a.elim), (fun a => a.elim), ?_⟩
    ext x
    exact (hX.false x).elim
  have hcov := isFpqcCovering_of_isEtaleCovering B S hS _ _ hc
  obtain ⟨d, _, hd⟩ := existsUnique_desc_of_fpqcCovering B S hS i hcov Y
    (fun a => a.elim) (fun a => a.elim)
  exact (hd f (fun a => a.elim)).trans (hd g (fun a => a.elim)).symm

/-- A finite coproduct of algebraic spaces over `S`, together with its universal property both
in the algebraic spaces and in the sheaves of sets. -/
private def finiteCoproductAlgebraicSpaces
    {I : Type v} [Finite I] (F : I → AlgebraicSpaces B S hS) :
    Σ W : AlgebraicSpaces B S hS,
      Σ ι : ∀ b, F b ⟶ W, IsColimit (Cofan.mk W ι) ×
        IsColimit (Cofan.mk ((algebraicSpacesToSheaf B S hS).obj W)
          (fun b => (algebraicSpacesToSheaf B S hS).map (ι b))) := by
  classical
  let J := BigFppfOver.topology B S hS
  let Fsh : I → Sheaf J (Type u) := fun b => ⟨(F b).1, (F b).2.isSheaf⟩
  let D := Discrete.functor Fsh
  let E := colimit.cocone (D ⋙ sheafToPresheaf J (Type u))
  let G := Sheaf.sheafifyCocone E
  have hG : IsColimit G := Sheaf.isColimitSheafifyCocone E (colimit.isColimit _)
  let A : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u := fun b => (F b).1
  have hA : ∀ b, IsAlgebraicSpace B S hS (A b) := fun b => (F b).2
  have hAlg := isAlgebraicSpace_finiteCoproduct B S hS A hA G.pt
    (fun b => G.ι.app (Discrete.mk b)) hG
  let W : AlgebraicSpaces B S hS := ⟨G.pt.obj, hAlg⟩
  let ι (b : I) : F b ⟶ W := ObjectProperty.homMk (G.ι.app (Discrete.mk b)).hom
  refine ⟨W, ι, ?_, hG⟩
  refine Cofan.IsColimit.mk (Cofan.mk W ι) (fun s => ?_) ?_ ?_
  · let Z : Sheaf J (Type u) := ⟨s.pt.1, s.pt.2.isSheaf⟩
    let f : D ⟶ (Functor.const (Discrete I)).obj Z :=
      Discrete.natTrans (fun b => ⟨(s.ι.app b).hom⟩)
    exact ObjectProperty.homMk ((hG.desc (Cocone.mk Z f)).hom)
  · intro s b
    let Z : Sheaf J (Type u) := ⟨s.pt.1, s.pt.2.isSheaf⟩
    let f : D ⟶ (Functor.const (Discrete I)).obj Z :=
      Discrete.natTrans (fun j => ⟨(s.ι.app j).hom⟩)
    exact ObjectProperty.hom_ext _
      (congrArg (fun g => g.hom) (hG.fac (Cocone.mk Z f) (Discrete.mk b)))
  · intro s m hm
    let Z : Sheaf J (Type u) := ⟨s.pt.1, s.pt.2.isSheaf⟩
    let f : D ⟶ (Functor.const (Discrete I)).obj Z :=
      Discrete.natTrans (fun j => ⟨(s.ι.app j).hom⟩)
    let c : Cocone D := Cocone.mk Z f
    let m' : G.pt ⟶ Z := ⟨m.hom⟩
    have huniq : m' = hG.desc c := by
      apply hG.hom_ext
      intro b
      have hb : G.ι.app b ≫ m' = f.app b := by
        apply Sheaf.hom_ext
        exact congrArg (fun g => g.hom) (hm b.as)
      exact hb.trans (hG.fac c b).symm
    exact ObjectProperty.hom_ext _ (congrArg (fun g => g.hom) huniq)

/-- A family of monomorphisms of algebraic spaces which is an étale covering with pairwise
disjoint images exhibits the target as their coproduct. -/
private def isColimit_of_disjoint_etaleCovering
    {I : Type v} {X : I → AlgebraicSpaces B S hS} {Y : AlgebraicSpaces B S hS}
    (f : ∀ i, X i ⟶ Y) (hm : ∀ i, Mono (f i).hom)
    (hc : IsEtaleCovering B S hS (fun i => (X i).obj) (fun i => (f i).hom))
    (hd : Pairwise fun i j => Disjoint
      (Set.range (pointsMap B S hS (X i).obj (f i).hom))
      (Set.range (pointsMap B S hS (X j).obj (f j).hom))) :
    IsColimit (Cofan.mk Y f) := by
  classical
  have hcov := isFpqcCovering_of_isEtaleCovering B S hS _ _ hc
  have hdesc (s : Cofan X) : ∃! k : Y ⟶ s.pt, ∀ i, f i ≫ k = s.inj i := by
    apply existsUnique_desc_of_fpqcCovering B S hS f hcov s.pt s.inj
    intro i j
    by_cases hij : i = j
    · subst j
      apply ObjectProperty.hom_ext
      have hmi : Mono (f i).hom := hm i
      have hp : pullback.fst (f i).hom (f i).hom = pullback.snd (f i).hom (f i).hom :=
        (cancel_mono (f i).hom).mp pullback.condition
      change pullback.fst (f i).hom (f i).hom ≫ _ = pullback.snd (f i).hom (f i).hom ≫ _
      rw [hp]
    · apply hom_ext_of_isEmpty_points B S hS
      refine ⟨fun x => ?_⟩
      have hp := congrArg (fun k => pointsMap B S hS (pullback (f i).hom (f j).hom) k x)
          (pullback.condition (f := (f i).hom) (g := (f j).hom))
      have e₁ := pointsMap_comp_apply B S hS (pullback.fst (f i).hom (f j).hom) (f i).hom x
      have e₂ := pointsMap_comp_apply B S hS (pullback.snd (f i).hom (f j).hom) (f j).hom x
      exact Set.disjoint_left.mp (hd hij) ⟨_, rfl⟩ ⟨_, e₂.symm.trans (hp.symm.trans e₁)⟩
  exact Cofan.IsColimit.mk _ (fun s => (hdesc s).choose)
    (fun s i => (hdesc s).choose_spec.1 i)
    (fun s m hm => (hdesc s).choose_spec.2 m hm)

/-- A finite coproduct of algebraic spaces is a coproduct of the underlying sheaves. -/
private def isColimit_sheaf_of_isColimit_finite
    {I : Type v} [Finite I] {X : I → AlgebraicSpaces B S hS} {Y : AlgebraicSpaces B S hS}
    (f : ∀ i, X i ⟶ Y) (hf : IsColimit (Cofan.mk Y f)) :
    IsColimit (Cofan.mk ((algebraicSpacesToSheaf B S hS).obj Y)
      (fun i => (algebraicSpacesToSheaf B S hS).map (f i))) := by
  let E := algebraicSpacesToSheaf B S hS
  obtain ⟨C, ι, hC, hCsh⟩ := finiteCoproductAlgebraicSpaces B S hS X
  let e := hC.coconePointUniqueUpToIso hf
  refine hCsh.ofIsoColimit (Cocone.ext (E.mapIso e) ?_)
  intro i
  change E.map (ι i.as) ≫ E.map e.hom = E.map (f i.as)
  rw [← E.map_comp]
  exact congrArg E.map (hC.comp_coconePointUniqueUpToIso_hom hf i)

/-- A sheaf which is a finite coproduct of algebraic spaces is an algebraic space. -/
private theorem isAlgebraicSpace_binaryCoproduct
    {F G H : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (hF : IsAlgebraicSpace B S hS F.obj) (hG : IsAlgebraicSpace B S hS G.obj)
    (i : F ⟶ H) (j : G ⟶ H) (h : IsColimit (BinaryCofan.mk i j)) :
    IsAlgebraicSpace B S hS H.obj :=
  isAlgebraicSpace_finiteCoproduct B S hS (fun k => (pairFunction F G k).obj)
    (fun k => WalkingPair.casesOn k hF hG) H
    (fun k => (BinaryCofan.mk i j).ι.app ⟨k⟩) h

/-- The relative diagonal of an étale morphism and the complement of its image cover the fibre
square: the two pieces are disjoint open subspaces whose points exhaust it. -/
private def isColimit_diagonal_openComplement
    {A U D : AlgebraicSpaces B S hS} (g : A ⟶ U) (hg : IsEtale B S hS g.hom)
    (d : D ⟶ AlgebraicSpaces.fiberProduct B S hS g g)
    (hd : IsOpenImmersion B S hS d.hom)
    (hpoints : Set.range (pointsMap B S hS D.obj d.hom) =
      (Set.range (pointsMap B S hS A.obj (pullback.diagonal g.hom)))ᶜ) :
    IsColimit (BinaryCofan.mk
      ((algebraicSpacesToSheaf B S hS).map
        (ObjectProperty.homMk (pullback.diagonal g.hom) :
          A ⟶ AlgebraicSpaces.fiberProduct B S hS g g))
      ((algebraicSpacesToSheaf B S hS).map d)) := by
  let P := AlgebraicSpaces.fiberProduct B S hS g g
  let δ : A ⟶ P := ObjectProperty.homMk (pullback.diagonal g.hom)
  have hδ : IsOpenImmersion B S hS δ.hom :=
    isOpenImmersion_diagonal_of_isUnramified B S hS A.property U.property g.hom
      (isUnramified_of_isEtale B S hS hg)
  let X := pairFunction A D
  let f : ∀ i, X i ⟶ P := fun i => WalkingPair.casesOn i δ d
  have hm : ∀ i, Mono (f i).hom := by
    rintro (_ | _)
    exacts [mono_of_isOpenImmersion B S hS _ hδ, mono_of_isOpenImmersion B S hS _ hd]
  have hc : IsEtaleCovering B S hS (fun i => (X i).obj) (fun i => (f i).hom) := by
    refine ⟨P.property, (fun i => (X i).property), ?_, ?_⟩
    · rintro (_ | _)
      exacts [isEtale_of_isOpenImmersion B S hS hδ, isEtale_of_isOpenImmersion B S hS hd]
    · refine Set.eq_univ_of_forall fun x => ?_
      classical
      by_cases hx : x ∈ Set.range (pointsMap B S hS A.obj δ.hom)
      · exact Set.mem_iUnion.mpr ⟨WalkingPair.left, hx⟩
      · exact Set.mem_iUnion.mpr ⟨WalkingPair.right, hpoints.symm ▸ hx⟩
  have hdisj : Pairwise fun i j => Disjoint
      (Set.range (pointsMap B S hS (X i).obj (f i).hom))
      (Set.range (pointsMap B S hS (X j).obj (f j).hom)) := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · change Disjoint _ (Set.range (pointsMap B S hS D.obj d.hom))
      rw [hpoints]
      exact disjoint_compl_right
    · change Disjoint (Set.range (pointsMap B S hS D.obj d.hom)) _
      rw [hpoints]
      exact disjoint_compl_left
    · exact (hij rfl).elim
  let h := isColimit_sheaf_of_isColimit_finite B S hS f
    (isColimit_of_disjoint_etaleCovering B S hS f hm hc hdisj)
  let E := algebraicSpacesToSheaf B S hS
  let c (T : Sheaf (BigFppfOver.topology B S hS) (Type u))
      (a : E.obj A ⟶ T) (b : E.obj D ⟶ T) : Cofan (fun i => E.obj (X i)) :=
    Cofan.mk T (fun i => WalkingPair.casesOn i a b)
  refine BinaryCofan.IsColimit.mk _ (fun a b => h.desc (c _ a b))
    (fun a b => h.fac (c _ a b) ⟨WalkingPair.left⟩)
    (fun a b => h.fac (c _ a b) ⟨WalkingPair.right⟩) fun a b m hm₁ hm₂ => ?_
  refine h.uniq (c _ a b) m ?_
  rintro ⟨_ | _⟩
  exacts [hm₁, hm₂]

/-! ### The kernel pair of the glueing map -/

/-- The kernel pair of the map out of a sheaf pushout along the `V` side: the five pieces of
the source's relation, assembled as `V ⨿ (V' ×_U V' ∖ Δ) ⇉ V`. -/
private theorem isPullback_sheafPushout_offDiagonal
    {A U V D : AlgebraicSpaces B S hS} (i : A ⟶ V) [Mono i.hom] (g : A ⟶ U)
    (hg : IsEtale B S hS g.hom)
    (d : D ⟶ AlgebraicSpaces.fiberProduct B S hS g g)
    (hd : IsOpenImmersion B S hS d.hom)
    (hpoints : Set.range (pointsMap B S hS D.obj d.hom) =
      (Set.range (pointsMap B S hS A.obj (pullback.diagonal g.hom)))ᶜ)
    {W : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (f : (algebraicSpacesToSheaf B S hS).obj V ⟶ W)
    (j : (algebraicSpacesToSheaf B S hS).obj U ⟶ W)
    (h : IsPushout ((algebraicSpacesToSheaf B S hS).map i)
      ((algebraicSpacesToSheaf B S hS).map g) f j) :
    IsPullback
      (coprod.desc (𝟙 _) (⟨d.hom ≫ pullback.fst g.hom g.hom ≫ i.hom⟩ :
        (algebraicSpacesToSheaf B S hS).obj D ⟶ (algebraicSpacesToSheaf B S hS).obj V))
      (coprod.desc (𝟙 _) (⟨d.hom ≫ pullback.snd g.hom g.hom ≫ i.hom⟩ :
        (algebraicSpacesToSheaf B S hS).obj D ⟶ (algebraicSpacesToSheaf B S hS).obj V))
      f f := by
  let E := algebraicSpacesToSheaf B S hS
  let P := AlgebraicSpaces.fiberProduct B S hS g g
  let p₁ : P ⟶ A := ObjectProperty.homMk (pullback.fst g.hom g.hom)
  let p₂ : P ⟶ A := ObjectProperty.homMk (pullback.snd g.hom g.hom)
  let δ : A ⟶ P := ObjectProperty.homMk (pullback.diagonal g.hom)
  have hP : IsPullback (E.map p₁) (E.map p₂) (E.map g) (E.map g) :=
    IsPullback.of_map_of_faithful
      (sheafToPresheaf (BigFppfOver.topology B S hS) (Type u))
      (IsPullback.of_hasPullback g.hom g.hom)
  let hc := isColimit_diagonal_openComplement B S hS g hg d hd hpoints
  let e : E.obj A ⨿ E.obj D ≅ E.obj P :=
    (coprodIsCoprod (E.obj A) (E.obj D)).coconePointUniqueUpToIso hc
  have he₁ : coprod.inl ≫ e.hom = E.map δ :=
    (coprodIsCoprod (E.obj A) (E.obj D)).comp_coconePointUniqueUpToIso_hom hc
      ⟨WalkingPair.left⟩
  have he₂ : coprod.inr ≫ e.hom = E.map d :=
    (coprodIsCoprod (E.obj A) (E.obj D)).comp_coconePointUniqueUpToIso_hom hc
      ⟨WalkingPair.right⟩
  have hδ₁ : δ ≫ p₁ = 𝟙 A :=
    ObjectProperty.hom_ext _ (pullback.diagonal_fst g.hom)
  have hδ₂ : δ ≫ p₂ = 𝟙 A :=
    ObjectProperty.hom_ext _ (pullback.diagonal_snd g.hom)
  have hP' : IsPullback
      (coprod.desc (𝟙 _) (E.map (d ≫ p₁)))
      (coprod.desc (𝟙 _) (E.map (d ≫ p₂))) (E.map g) (E.map g) := by
    refine hP.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.comp_id]
      refine coprod.hom_ext ?_ ?_
      · rw [← Category.assoc, he₁, coprod.inl_desc, ← E.map_comp, hδ₁, E.map_id]
      · rw [← Category.assoc, he₂, coprod.inr_desc, ← E.map_comp]
    · rw [Iso.refl_hom, Category.comp_id]
      refine coprod.hom_ext ?_ ?_
      · rw [← Category.assoc, he₁, coprod.inl_desc, ← E.map_comp, hδ₂, E.map_id]
      · rw [← Category.assoc, he₂, coprod.inr_desc, ← E.map_comp]
    · rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id]
    · rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id]
  have hmono : Mono (E.map i) := Functor.mono_of_mono_map
    (sheafToPresheaf (BigFppfOver.topology B S hS) (Type u))
    (show Mono i.hom from inferInstance)
  exact isPullback_coprod_kernelPair (E.map i) (E.map g) f j
    (E.map (d ≫ p₁)) (E.map (d ≫ p₂)) h hP'

/-! ### Étaleness of a map out of a coproduct -/

/-- A morphism out of a coproduct of open subspaces is étale as soon as each restriction is. -/
private theorem isEtale_of_open_coproduct {I : Type u}
    {A : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {X Y : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (hA : ∀ i, IsAlgebraicSpace B S hS (A i).obj)
    (hX : IsAlgebraicSpace B S hS X.obj) (hY : IsAlgebraicSpace B S hS Y.obj)
    (ι : ∀ i, A i ⟶ X) (hc : IsColimit (Cofan.mk X ι))
    (hι : ∀ i, IsOpenImmersion B S hS (ι i).hom)
    (f : X ⟶ Y) (hf : ∀ i, IsEtale B S hS ((ι i).hom ≫ f.hom)) :
    IsEtale B S hS f.hom := by
  let J := BigFppfOver.topology B S hS
  let O : I → Subfunctor X.obj := fun i => Subfunctor.range (ι i).hom
  have ho : ∀ i, IsOpenSubspace B S hS (O i) := fun i =>
    AlgebraicGeometry.Space.isOpenSubspace_range_of_isAlgebraicSpace B S hS (hA i) (ι i).hom (hι i)
  have hloc := coproduct_locallySurjective J A ι hc
  let k : (∐ fun i => (A i).obj) ⟶ (∐ fun i => (O i).toFunctor) :=
    Sigma.desc fun i => Subfunctor.toRange (ι i).hom ≫ Sigma.ι (fun i => (O i).toFunctor) i
  have hfac : k ≫ Sigma.desc (fun i => (O i).ι) = Sigma.desc (fun i => (ι i).hom) := by
    apply Sigma.hom_ext
    intro i
    simp [k, O, Subfunctor.toRange_ι]
  have hcov : IsZariskiCover B S hS I O :=
    ⟨ho, Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfac⟩
  have hp := (isZariskiCover_iff_iUnion_points B S hS X.obj hX I O ho).mp hcov
  have hrange : ∀ i, Set.range (pointsMap B S hS (A i).obj (ι i).hom) =
      Set.range (pointsMap B S hS (O i).toFunctor (O i).ι) := by
    intro i
    have hmono : Mono (ι i).hom := mono_of_isOpenImmersion B S hS _ (hι i)
    have hcomp : ∀ y, pointsMap B S hS (O i).toFunctor (O i).ι
        (pointsMap B S hS (A i).obj (Subfunctor.toRange (ι i).hom) y) =
        pointsMap B S hS (A i).obj (ι i).hom y := by
      intro y
      rw [← pointsMap_comp_apply, Subfunctor.toRange_ι]
    refine Set.Subset.antisymm ?_ ?_
    · rintro x ⟨y, rfl⟩
      exact ⟨_, hcomp y⟩
    · rintro x ⟨z, rfl⟩
      obtain ⟨y, rfl⟩ := pointsMap_surjective_of_isIso B S hS (Subfunctor.toRange (ι i).hom) z
      exact ⟨y, (hcomp y).symm⟩
  have hcovE : IsEtaleCovering B S hS (fun i => (A i).obj) (fun i => (ι i).hom) := by
    refine ⟨hX, hA, fun i => isEtale_of_isOpenImmersion B S hS (hι i), ?_⟩
    simpa only [hrange] using hp
  let Xs : AlgebraicSpaces B S hS := ⟨X.obj, hX⟩
  let Ys : AlgebraicSpaces B S hS := ⟨Y.obj, hY⟩
  let As : I → AlgebraicSpaces B S hS := fun i => ⟨(A i).obj, hA i⟩
  let ιs : ∀ i, As i ⟶ Xs := fun i => ObjectProperty.homMk (ι i).hom
  let Q : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun ⦃_ _ : AlgebraicSpaces B S hS⦄ k => IsEtale B S hS k.hom
  let _ : Q.IsLocalAtSource (Topology.precoverage.{u, u} .etale B S hS) :=
    isEtale_isLocalAtSource_etale.{u, u} B S hS
  have hR : Presieve.ofArrows As ιs ∈ Topology.precoverage.{u, u} .etale B S hS Xs :=
    ⟨I, As, ιs, rfl, hX, hA, hcovE⟩
  change Q (ObjectProperty.homMk f.hom : Xs ⟶ Ys)
  refine MorphismProperty.IsLocalAtSource.of_forall_comp (P := Q) hR ?_
  rintro T g ⟨i⟩
  exact hf i

/-- A morphism out of a finite coproduct of algebraic spaces is étale as soon as each
restriction is. -/
private theorem isEtale_of_finite_coproduct {I : Type v} [Finite I]
    {A : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {X Y : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (hA : ∀ i, IsAlgebraicSpace B S hS (A i).obj)
    (hX : IsAlgebraicSpace B S hS X.obj) (hY : IsAlgebraicSpace B S hS Y.obj)
    (ι : ∀ i, A i ⟶ X) (hc : IsColimit (Cofan.mk X ι))
    (f : X ⟶ Y) (hf : ∀ i, IsEtale B S hS ((ι i).hom ≫ f.hom)) :
    IsEtale B S hS f.hom := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  let K : Type u := ULift.{u} (Fin (Fintype.card I))
  let e : K ≃ I := Equiv.ulift.trans (Fintype.equivFin I).symm
  have hc' : IsColimit (Cofan.mk X (fun k => ι (e k))) :=
    (Cofan.isColimitEquivOfEquiv e (Cofan.mk X ι)).toFun hc
  exact isEtale_of_open_coproduct B S hS (fun k => hA (e k)) hX hY
    (fun k => ι (e k)) hc'
    (fun k => coproductIncl_isOpenImmersion B S hS A X ι hc (e k))
    f (fun k => hf (e k))

/-- A morphism out of a binary coproduct of algebraic spaces is étale as soon as both
restrictions are. -/
private theorem isEtale_binaryCoproduct_desc
    {A D X Y : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (hA : IsAlgebraicSpace B S hS A.obj) (hD : IsAlgebraicSpace B S hS D.obj)
    (hX : IsAlgebraicSpace B S hS X.obj) (hY : IsAlgebraicSpace B S hS Y.obj)
    (i : A ⟶ X) (j : D ⟶ X) (hc : IsColimit (BinaryCofan.mk i j)) (f : X ⟶ Y)
    (hi : IsEtale B S hS (i.hom ≫ f.hom)) (hj : IsEtale B S hS (j.hom ≫ f.hom)) :
    IsEtale B S hS f.hom :=
  isEtale_of_finite_coproduct B S hS (A := pairFunction A D)
    (fun k => WalkingPair.casesOn k hA hD) hX hY
    (fun k => (BinaryCofan.mk i j).ι.app ⟨k⟩) hc f
    (fun k => WalkingPair.casesOn k hi hj)

/-- Étaleness is stable under base change, read in the sheaves of sets. -/
private theorem isEtale_sheafPullback
    {A X Y Z : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (hA : IsAlgebraicSpace B S hS A.obj) (hX : IsAlgebraicSpace B S hS X.obj)
    (hY : IsAlgebraicSpace B S hS Y.obj) (hZ : IsAlgebraicSpace B S hS Z.obj)
    (a : A ⟶ X) (b : A ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : IsPullback a b f g) (hf : IsEtale B S hS f.hom) :
    IsEtale B S hS b.hom :=
  isEtale_of_isPullback B S hS
    (X' := ⟨A.obj, hA⟩) (X := ⟨X.obj, hX⟩) (Z := ⟨Y.obj, hY⟩) (Y := ⟨Z.obj, hZ⟩)
    (ObjectProperty.homMk a.hom) (ObjectProperty.homMk b.hom)
    (ObjectProperty.homMk f.hom) (ObjectProperty.homMk g.hom)
    (IsPullback.of_map_of_faithful (algebraicSpacesToSheaf B S hS) h) hf

/-! ### The quotient of an étale equivalence relation of algebraic spaces -/

/-- By Stacks 04S6 part (1), the quotient sheaf of an étale equivalence relation of algebraic
spaces over `S` is an algebraic space, and the quotient map is flat and locally of finite
presentation. -/
private theorem isAlgebraicSpace_quotient_of_etale
    {base R X : AlgebraicSpaces B S hS} {qR : R ⟶ base} {qX : X ⟶ base}
    (r : PreRelation (Over.mk qR.hom) (Over.mk qX.hom))
    [hr : IsEquivalenceRelation r.target r.source]
    (hs : IsEtale B S hS r.source.left) (ht : IsEtale B S hS r.target.left) :
    IsAlgebraicSpace B S hS (quotientSheaf r).obj ∧
      IsFlat B S hS (toQuotientSheaf r) ∧
      IsLocallyOfFinitePresentation B S hS (toQuotientSheaf r) := by
  let G : GroupoidInAlgebraicSpaces B S hS base := groupoidOfIsEquivalenceRelation r
  have heq : groupoidPreRelation G = r := by
    refine prod.hom_ext ?_ ?_ <;>
      simp only [groupoidPreRelation, prod.lift_fst, prod.lift_snd] <;>
      exact Over.OverMorphism.ext rfl
  have hrel : IsEquivalenceRelation (groupoidPreRelation G).target
      (groupoidPreRelation G).source := heq.symm ▸ hr
  have hsG : IsFlat B S hS G.source.hom := isFlat_of_isEtale B S hS hs
  have htG : IsFlat B S hS G.target.hom := isFlat_of_isEtale B S hS ht
  have hsL : IsLocallyOfFinitePresentation B S hS G.source.hom :=
    isLocallyOfFinitePresentation_of_isEtale B S hS hs
  have htL : IsLocallyOfFinitePresentation B S hS G.target.hom :=
    isLocallyOfFinitePresentation_of_isEtale B S hS ht
  have hq : IsAlgebraicSpace B S hS (quotientSheaf (groupoidPreRelation G)).obj :=
    Space.bootstrap04S6QuotientSheaf B S hS (groupoidPreRelation G) G.arrows.property
      G.objects.property hrel
      (by rwa [Stack.groupoidPreRelation_target_left])
      (by rwa [Stack.groupoidPreRelation_target_left])
      (by rwa [Stack.groupoidPreRelation_source_left])
      (by rwa [Stack.groupoidPreRelation_source_left])
  exact ⟨heq ▸ hq, heq ▸ isFlat_toQuotientSheaf G hrel hq htG,
    heq ▸ isLocallyOfFinitePresentation_toQuotientSheaf G hrel hq htL⟩

/-- The quotient sheaf of a pre-relation is the coequalizer of its two legs. -/
private def quotientSheafIsColimit
    {base R X : AlgebraicSpaces B S hS} {qR : R ⟶ base} {qX : X ⟶ base}
    (r : PreRelation (Over.mk qR.hom) (Over.mk qX.hom)) :
    IsColimit (Cofork.ofπ
      (f := (algebraicSpacesToSheaf B S hS).map (ObjectProperty.homMk r.target.left : R ⟶ X))
      (g := (algebraicSpacesToSheaf B S hS).map (ObjectProperty.homMk r.source.left : R ⟶ X))
      (⟨toQuotientSheaf r⟩ : (algebraicSpacesToSheaf B S hS).obj X ⟶ quotientSheaf r)
      (by apply Sheaf.hom_ext; exact target_toQuotientSheaf_eq_source r)) := by
  refine Cofork.IsColimit.mk _
    (fun c => quotientSheafDesc r c.pt c.π.hom (congrArg (fun k => k.hom) c.condition)) ?_ ?_
  · intro c
    apply Sheaf.hom_ext
    exact toQuotientSheaf_quotientSheafDesc r _ _ _
  · intro c m hm
    exact quotientSheafDesc_unique r _ _ _ m (congrArg (fun k => k.hom) hm)

/-! ### Descending a property along the quotient map -/

/-- A property of morphisms of algebraic spaces local at the target for the fpqc topology
descends along a surjective, flat, locally finitely presented base change. -/
private theorem property_of_fppf_pullback
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtTarget (Topology.precoverage.{u, 0} .fpqc B S hS)]
    {A X Z Y : AlgebraicSpaces B S hS}
    (a : A ⟶ X) (b : A ⟶ Z) (f : X ⟶ Y) (q : Z ⟶ Y)
    (h : IsPullback a b f q) (hq : IsSurjective B S hS q.hom)
    (hqf : IsFlat B S hS q.hom)
    (hql : IsLocallyOfFinitePresentation B S hS q.hom)
    (hb : P b) : P f := by
  have hcov : IsFppfCovering B S hS (fun _ : PUnit.{1} => Z.obj) (fun _ => q.hom) := by
    refine ⟨Y.property, fun _ => Z.property, fun _ => hqf, fun _ => hql, ?_⟩
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨y, hy⟩ := hq x
    exact Set.mem_iUnion.mpr ⟨PUnit.unit, y, hy⟩
  have hfpqc := isFpqcCovering_of_isFppfCovering B S hS _ _ hcov
  let R := Presieve.ofArrows (fun _ : PUnit.{1} => Z) (fun _ => q)
  have hR : R ∈ Topology.precoverage.{u, 0} .fpqc B S hS Y :=
    ⟨PUnit.{1}, (fun _ => Z), (fun _ => q), rfl, Y.property, (fun _ => Z.property), hfpqc⟩
  apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd (P := P) hR
  rintro T g _ ⟨i⟩
  let e := (IsPullback.of_hasPullback f q).isoIsPullback _ _ h
  have he : e.hom ≫ b = pullback.snd f q :=
    (IsPullback.of_hasPullback f q).isoIsPullback_hom_snd _ _ h
  rw [← he]
  exact (P.cancel_left_of_respectsIso e.hom b).mpr hb

/-- Postcomposing with an isomorphism preserves a property of morphisms of algebraic spaces
which is local at the target for the fpqc topology. -/
private theorem property_postcomp_iso
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtTarget (Topology.precoverage.{u, 0} .fpqc B S hS)]
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (e : Y ≅ Z) (hf : P f) :
    P (f ≫ e.hom) :=
  MorphismProperty.RespectsIso.postcomp P e.hom f hf

/-- An algebraic space with no points is an initial object among the sheaves of sets. -/
private def isInitial_sheaf_of_isEmpty_points
    (X : AlgebraicSpaces B S hS) (hX : IsEmpty (points B S hS X.obj)) :
    IsInitial ((algebraicSpacesToSheaf B S hS).obj X) := by
  let A : Empty → AlgebraicSpaces B S hS := Empty.elim
  let i : ∀ a, A a ⟶ X := fun a => a.elim
  have hc : IsEtaleCovering B S hS (fun a => (A a).obj) (fun a => (i a).hom) := by
    refine ⟨X.property, (fun a => a.elim), (fun a => a.elim), ?_⟩
    ext x
    exact (hX.false x).elim
  have hcov := isFpqcCovering_of_isEtaleCovering B S hS _ _ hc
  have hdesc (Y : AlgebraicSpaces B S hS) : ∃! f : X ⟶ Y, True := by
    obtain ⟨d, _, hd⟩ := existsUnique_desc_of_fpqcCovering B S hS i hcov Y
      (fun a => a.elim) (fun a => a.elim)
    exact ⟨d, trivial, fun f _ => hd f (fun a => a.elim)⟩
  let hInit : IsInitial X := IsInitial.ofUniqueHom
    (fun Y => (hdesc Y).choose) (fun Y f => (hdesc Y).choose_spec.2 f trivial)
  let hCol : IsColimit (Cofan.mk X i) := (isColimitEquivIsInitialOfIsEmpty _ _).symm hInit
  exact (isColimitEquivIsInitialOfIsEmpty _ _).toFun
    (isColimit_sheaf_of_isColimit_finite B S hS i hCol)

/-- A pushout square of sheaves of sets between algebraic spaces is a pushout square of
algebraic spaces. -/
private theorem isPushout_of_isPushout_sheaf
    {A U V W : AlgebraicSpaces B S hS} (i : A ⟶ V) (g : A ⟶ U) (f : V ⟶ W) (j : U ⟶ W)
    (h : IsPushout ((algebraicSpacesToSheaf B S hS).map i)
      ((algebraicSpacesToSheaf B S hS).map g)
      ((algebraicSpacesToSheaf B S hS).map f)
      ((algebraicSpacesToSheaf B S hS).map j)) :
    IsPushout i g f j :=
  IsPushout.of_map_of_faithful (algebraicSpacesToSheaf B S hS) h

/-- The base object of the site, as an algebraic space over `S` which is terminal both among
the algebraic spaces and among the presheaves. -/
private def terminalAlgebraicSpace :
    Σ T : AlgebraicSpaces B S hS, IsTerminal T × IsTerminal T.obj := by
  let T : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))
  have hT : IsTerminal T := Over.mkIdTerminal
  let hTp := hT.isTerminalObj yoneda T
  let A : AlgebraicSpaces B S hS := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩
  refine ⟨A, IsTerminal.ofUniqueHom (fun X => ObjectProperty.homMk (hTp.from X.obj)) ?_, hTp⟩
  exact fun X f => ObjectProperty.hom_ext _ (hTp.hom_ext _ _)


/-- The sheaf pushout of `V' ⟶ V` along a separated étale `f' : V' ⟶ U` is an algebraic space
which is also a pullback, and both maps out of `V` and `U` into it are étale. -/
private theorem exists_sheafPushout_isAlgebraicSpace
    (U V : AlgebraicSpaces B S hS) (V' : Subfunctor V.obj)
    (hV' : IsOpenSubspace B S hS V') (f' : V'.toFunctor ⟶ U.obj)
    (hf' : IsEtale B S hS f') (hf'sep : IsSeparated B S hS f') :
    ∃ (Q : Sheaf (BigFppfOver.topology B S hS) (Type u))
      (fQ : (algebraicSpacesToSheaf B S hS).obj V ⟶ Q)
      (jQ : (algebraicSpacesToSheaf B S hS).obj U ⟶ Q),
      IsPushout ((algebraicSpacesToSheaf B S hS).map
          (ObjectProperty.homMk V'.ι :
            (⟨V'.toFunctor, hV'.1⟩ : AlgebraicSpaces B S hS) ⟶ V))
        ((algebraicSpacesToSheaf B S hS).map
          (ObjectProperty.homMk f' :
            (⟨V'.toFunctor, hV'.1⟩ : AlgebraicSpaces B S hS) ⟶ U)) fQ jQ ∧
      IsPullback ((algebraicSpacesToSheaf B S hS).map
          (ObjectProperty.homMk V'.ι :
            (⟨V'.toFunctor, hV'.1⟩ : AlgebraicSpaces B S hS) ⟶ V))
        ((algebraicSpacesToSheaf B S hS).map
          (ObjectProperty.homMk f' :
            (⟨V'.toFunctor, hV'.1⟩ : AlgebraicSpaces B S hS) ⟶ U)) fQ jQ ∧
      Mono jQ ∧ IsAlgebraicSpace B S hS Q.obj ∧ IsEtale B S hS fQ.hom ∧
        IsEtale B S hS jQ.hom := by
  classical
  let J := BigFppfOver.topology B S hS
  let E := algebraicSpacesToSheaf B S hS
  let V₀ : AlgebraicSpaces B S hS := ⟨V'.toFunctor, hV'.1⟩
  let f₀ : V₀ ⟶ U := ObjectProperty.homMk f'
  obtain ⟨D, d, hdOpen, hdPoints⟩ := offDiagonalAlgebraicSpace B S hS f₀ hf'sep
  let i₀ : V₀ ⟶ V := ObjectProperty.homMk V'.ι
  have hi₀ : Mono i₀.hom := inferInstanceAs (Mono V'.ι)
  let ish : E.obj V₀ ⟶ E.obj V := E.map i₀
  have hishMono : Mono ish := Functor.mono_of_mono_map (sheafToPresheaf J (Type u))
    (show Mono V'.ι from inferInstance)
  obtain ⟨Q, fQ, jQ, hQ, hQpb, hjQ⟩ := exists_pushout_of_mono ish (E.map f₀)
  let p₁ : AlgebraicSpaces.fiberProduct B S hS f₀ f₀ ⟶ V₀ :=
    ObjectProperty.homMk (pullback.fst f' f')
  let p₂ : AlgebraicSpaces.fiberProduct B S hS f₀ f₀ ⟶ V₀ :=
    ObjectProperty.homMk (pullback.snd f' f')
  let VV := E.obj V ⨿ E.obj D
  have hVV : IsAlgebraicSpace B S hS VV.obj :=
    isAlgebraicSpace_binaryCoproduct B S hS V.property D.property
      coprod.inl coprod.inr (coprodIsCoprod _ _)
  let v₁ : VV ⟶ E.obj V := coprod.desc (𝟙 _) (E.map (d ≫ p₁ ≫ i₀))
  let v₂ : VV ⟶ E.obj V := coprod.desc (𝟙 _) (E.map (d ≫ p₂ ≫ i₀))
  have hvv : IsPullback v₁ v₂ fQ fQ :=
    isPullback_sheafPushout_offDiagonal B S hS i₀ f₀ hf' d hdOpen hdPoints fQ jQ hQ
  let X := E.obj U ⨿ E.obj V
  have hX : IsAlgebraicSpace B S hS X.obj :=
    isAlgebraicSpace_binaryCoproduct B S hS U.property V.property
      coprod.inl coprod.inr (coprodIsCoprod _ _)
  let q : X ⟶ Q := coprod.desc jQ fQ
  let XParts := pairFunction (E.obj U) (E.obj V)
  let mapsQ : ∀ k, XParts k ⟶ Q := fun k => WalkingPair.casesOn k jQ fQ
  let RParts : WalkingPair × WalkingPair → Sheaf J (Type u) := fun k =>
    match k with
    | (.left, .left) => E.obj U
    | (.left, .right) => E.obj V₀
    | (.right, .left) => E.obj V₀
    | (.right, .right) => VV
  let r₁ : ∀ a b, RParts (a, b) ⟶ XParts a := fun a b =>
    match a, b with
    | .left, .left => 𝟙 _
    | .left, .right => E.map f₀
    | .right, .left => ish
    | .right, .right => v₁
  let r₂ : ∀ a b, RParts (a, b) ⟶ XParts b := fun a b =>
    match a, b with
    | .left, .left => 𝟙 _
    | .left, .right => ish
    | .right, .left => E.map f₀
    | .right, .right => v₂
  have hr : ∀ a b, IsPullback (r₁ a b) (r₂ a b) (mapsQ a) (mapsQ b) := by
    intro a b
    cases a <;> cases b
    · exact IsKernelPair.id_of_mono jQ
    · exact hQpb.flip
    · exact hQpb
    · exact hvv
  let R : Sheaf J (Type u) := ∐ RParts
  have hRParts : ∀ k, IsAlgebraicSpace B S hS (RParts k).obj := by
    rintro ⟨a, b⟩
    cases a <;> cases b
    exacts [U.property, V₀.property, V₀.property, hVV]
  have hR : IsAlgebraicSpace B S hS R.obj :=
    isAlgebraicSpace_finiteCoproduct B S hS (fun k => (RParts k).obj) hRParts
      R (Sigma.ι RParts) (coproductIsCoproduct RParts)
  let xs : ∀ a, XParts a ⟶ X := fun a => WalkingPair.casesOn a coprod.inl coprod.inr
  let s : R ⟶ X := Sigma.desc (fun k => r₁ k.1 k.2 ≫ xs k.1)
  let t : R ⟶ X := Sigma.desc (fun k => r₂ k.1 k.2 ≫ xs k.2)
  have hXc : IsColimit (Cofan.mk X xs) := by
    refine (coprodIsCoprod (E.obj U) (E.obj V)).ofIsoColimit (Cocone.ext (Iso.refl _) ?_)
    rintro ⟨a⟩
    cases a <;> simp [xs, Cofan.mk] <;> rfl
  let hpbs : ∀ a : WalkingPair, HasPullback (mapsQ a) q :=
    fun a => HasLimitsOfShape.has_limit (cospan (mapsQ a) q)
  have hkernel : IsPullback s t q q :=
    @IsUniversalColimit.isPullback_prod_of_isColimit
      (Sheaf J (Type u)) _ WalkingPair WalkingPair Q XParts (Cofan.mk X xs)
      (FinitaryExtensive.isVanKampen_finiteCoproducts hXc).isUniversal
      XParts (Cofan.mk X xs)
      (FinitaryExtensive.isVanKampen_finiteCoproducts hXc).isUniversal
      mapsQ mapsQ q q hpbs inferInstance RParts r₁ r₂
      hr (Cofan.mk R (Sigma.ι RParts)) (coproductIsCoproduct RParts)
      (by
        rintro (_ | _)
        exacts [coprod.inl_desc jQ fQ, coprod.inr_desc jQ fQ])
      (by
        rintro (_ | _)
        exacts [coprod.inl_desc jQ fQ, coprod.inr_desc jQ fQ])
  obtain ⟨base, hbase, hbaseP⟩ := terminalAlgebraicSpace B S hS
  let Xsp : AlgebraicSpaces B S hS := ⟨X.obj, hX⟩
  let Rsp : AlgebraicSpaces B S hS := ⟨R.obj, hR⟩
  let qX : Xsp ⟶ base := hbase.from Xsp
  let qR : Rsp ⟶ base := hbase.from Rsp
  let sb : Over.mk qR.hom ⟶ Over.mk qX.hom :=
    Over.homMk s.hom (congrArg (fun m : Rsp ⟶ base => m.hom) (hbase.hom_ext _ _))
  let tb : Over.mk qR.hom ⟶ Over.mk qX.hom :=
    Over.homMk t.hom (congrArg (fun m : Rsp ⟶ base => m.hom) (hbase.hom_ext _ _))
  let _ : (Over.forget base.obj).Full :=
    (Over.equivalenceOfIsTerminal hbaseP).fullyFaithfulFunctor.full
  let rel : PreRelation (Over.mk qR.hom) (Over.mk qX.hom) := prod.lift sb tb
  have htr : rel.target = sb := prod.lift_fst _ _
  have hsr : rel.source = tb := prod.lift_snd _ _
  have hkernelP : IsKernelPair q.hom ((Over.forget base.obj).map sb)
      ((Over.forget base.obj).map tb) := hkernel.map (sheafToPresheaf J (Type u))
  have hrel : IsEquivalenceRelation rel.target rel.source := by
    rw [htr, hsr]
    exact (equivalenceRelation_of_isKernelPair_map (Over.forget base.obj) sb tb q.hom
      hkernelP).isEquivalenceRelation
  have hetid (A : Sheaf J (Type u)) : IsEtale B S hS (𝟙 A.obj) := by
    intro T φ hφ
    simpa using hφ
  have hi : IsEtale B S hS ish.hom := isEtale_of_isOpenImmersion B S hS hV'.2
  have hp : IsPullback (E.map p₁) (E.map p₂) (E.map f₀) (E.map f₀) :=
    IsPullback.of_map_of_faithful (sheafToPresheaf J (Type u))
      (IsPullback.of_hasPullback f' f')
  have hp₁ : IsEtale B S hS (E.map p₁).hom :=
    isEtale_sheafPullback B S hS (isAlgebraicSpace_pullback B S hS f' f' V₀.property
      V₀.property U.property) V₀.property V₀.property U.property _ _ _ _ hp.flip hf'
  have hp₂ : IsEtale B S hS (E.map p₂).hom :=
    isEtale_sheafPullback B S hS (isAlgebraicSpace_pullback B S hS f' f' V₀.property
      V₀.property U.property) V₀.property V₀.property U.property _ _ _ _ hp hf'
  have hd : IsEtale B S hS (E.map d).hom := isEtale_of_isOpenImmersion B S hS hdOpen
  have hv (p : AlgebraicSpaces.fiberProduct B S hS f₀ f₀ ⟶ V₀)
      (hp : IsEtale B S hS (E.map p).hom) :
      IsEtale B S hS (coprod.desc (𝟙 _) (E.map (d ≫ p ≫ i₀)) : VV ⟶ E.obj V).hom := by
    refine isEtale_binaryCoproduct_desc B S hS V.property D.property hVV V.property
      coprod.inl coprod.inr (coprodIsCoprod _ _) _ ?_ ?_
    · change IsEtale B S hS (coprod.inl ≫ coprod.desc (𝟙 _) (E.map (d ≫ p ≫ i₀))).hom
      rw [coprod.inl_desc]
      exact hetid (E.obj V)
    · change IsEtale B S hS (coprod.inr ≫ coprod.desc (𝟙 _) (E.map (d ≫ p ≫ i₀))).hom
      rw [coprod.inr_desc]
      exact isEtale_comp B S hS hd (isEtale_comp B S hS hp hi)
  have hv₁ : IsEtale B S hS v₁.hom := hv p₁ hp₁
  have hv₂ : IsEtale B S hS v₂.hom := hv p₂ hp₂
  have hxs : ∀ a, IsEtale B S hS (xs a).hom := fun a =>
    isEtale_of_isOpenImmersion B S hS
      (coproductIncl_isOpenImmersion B S hS XParts X xs hXc a)
  have hsEt : IsEtale B S hS s.hom := by
    refine isEtale_of_finite_coproduct B S hS hRParts hR hX
      (Sigma.ι RParts) (coproductIsCoproduct RParts) s ?_
    rintro ⟨a, b⟩
    have hr₁ : IsEtale B S hS (r₁ a b).hom := by
      cases a <;> cases b
      exacts [hetid (E.obj U), hf', hi, hv₁]
    change IsEtale B S hS ((Sigma.ι RParts (a, b) ≫ s).hom)
    simp only [s, Sigma.ι_desc]
    exact isEtale_comp B S hS hr₁ (hxs a)
  have htEt : IsEtale B S hS t.hom := by
    refine isEtale_of_finite_coproduct B S hS hRParts hR hX
      (Sigma.ι RParts) (coproductIsCoproduct RParts) t ?_
    rintro ⟨a, b⟩
    have hr₂ : IsEtale B S hS (r₂ a b).hom := by
      cases a <;> cases b
      exacts [hetid (E.obj U), hi, hf', hv₂]
    change IsEtale B S hS ((Sigma.ι RParts (a, b) ≫ t).hom)
    simp only [t, Sigma.ι_desc]
    exact isEtale_comp B S hS hr₂ (hxs b)
  have hquotRes := isAlgebraicSpace_quotient_of_etale B S hS rel
    (show IsEtale B S hS rel.source.left by rwa [hsr])
    (show IsEtale B S hS rel.target.left by rwa [htr])
  have hqepi : Epi q := by
    constructor
    intro Y a b hab
    apply hQ.hom_ext
    · simpa [q, coprod.inr_desc] using
        congrArg (fun k => (coprod.inr : E.obj V ⟶ X) ≫ k) hab
    · simpa [q, coprod.inl_desc] using
        congrArg (fun k => (coprod.inl : E.obj U ⟶ X) ≫ k) hab
  have hkr : IsKernelPair q (E.map (ObjectProperty.homMk rel.target.left : Rsp ⟶ Xsp))
      (E.map (ObjectProperty.homMk rel.source.left : Rsp ⟶ Xsp)) := by
    rw [htr, hsr]
    exact hkernel
  let hc := hkr.toCoequalizer (regularEpiOfEpi q)
  let hquotc := quotientSheafIsColimit B S hS rel
  let eqQ : quotientSheaf rel ≅ Q := hquotc.coconePointUniqueUpToIso hc
  have heqQ : (⟨toQuotientSheaf rel⟩ : E.obj Xsp ⟶ _) ≫ eqQ.hom = q :=
    hquotc.comp_coconePointUniqueUpToIso_hom hc WalkingParallelPair.one
  have hQalg : IsAlgebraicSpace B S hS Q.obj :=
    isAlgebraicSpace_of_iso B S hS ((sheafToPresheaf J (Type u)).mapIso eqQ) hquotRes.1
  let W : AlgebraicSpaces B S hS := ⟨Q.obj, hQalg⟩
  let Wquot : AlgebraicSpaces B S hS := ⟨(quotientSheaf rel).obj, hquotRes.1⟩
  let eqW : Wquot ≅ W := ObjectProperty.isoMk _ ((sheafToPresheaf J (Type u)).mapIso eqQ)
  let qW : Xsp ⟶ W := ObjectProperty.homMk q.hom
  let qquot : Xsp ⟶ Wquot := ObjectProperty.homMk (toQuotientSheaf rel)
  have hqq : qquot ≫ eqW.hom = qW := ObjectProperty.hom_ext _ (congrArg (fun k => k.hom) heqQ)
  have hqflat : IsFlat B S hS q.hom := by
    have h := @property_postcomp_iso B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) => IsFlat B S hS k.hom)
      (isFlat_isLocalAtTarget_fpqc.{u, 0} B S hS) _ _ _ qquot eqW hquotRes.2.1
    rwa [hqq] at h
  have hqlfp : IsLocallyOfFinitePresentation B S hS q.hom := by
    have h := @property_postcomp_iso B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) =>
        IsLocallyOfFinitePresentation B S hS k.hom)
      (isLocallyOfFinitePresentation_isLocalAtTarget_fpqc.{u, 0} B S hS) _ _ _
      qquot eqW hquotRes.2.2
    rwa [hqq] at h
  have hqsurj : IsSurjective B S hS q.hom := by
    have hquotSurj := isSurjective_toQuotientSheaf rel
    have heSurj : Function.Surjective
        (pointsMap B S hS (quotientSheaf rel).obj eqQ.hom.hom) := by
      intro x
      refine ⟨pointsMap B S hS Q.obj eqQ.inv.hom x, ?_⟩
      rw [← pointsMap_comp_apply]
      have h := congrArg (fun k => k.hom) eqQ.inv_hom_id
      change eqQ.inv.hom ≫ eqQ.hom.hom = 𝟙 _ at h
      rw [h]
      exact Quot.inductionOn x (fun _ => rfl)
    have hcomp := heSurj.comp hquotSurj
    intro x
    obtain ⟨y, hy⟩ := hcomp x
    refine ⟨y, ?_⟩
    dsimp only [Function.comp_apply] at hy
    rw [← pointsMap_comp_apply] at hy
    have he0 := congrArg (fun k => k.hom) heqQ
    have he : toQuotientSheaf rel ≫ eqQ.hom.hom = q.hom := he0
    rwa [he] at hy
  have hqEt : IsEtale B S hS q.hom :=
    @property_of_fppf_pullback B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) => IsEtale B S hS k.hom)
      (isEtale_isLocalAtTarget_fpqc.{u, 0} B S hS) Rsp Xsp Xsp W
      (ObjectProperty.homMk s.hom) (ObjectProperty.homMk t.hom) qW qW
      (IsPullback.of_map_of_faithful E hkernel) hqsurj hqflat hqlfp htEt
  have hfQEt : IsEtale B S hS fQ.hom := by
    have hh := isEtale_comp B S hS (hxs WalkingPair.right) hqEt
    have he : (xs WalkingPair.right).hom ≫ q.hom = fQ.hom :=
      congrArg (fun k => k.hom) (coprod.inr_desc jQ fQ)
    rwa [he] at hh
  have hjQEt : IsEtale B S hS jQ.hom := by
    have hh := isEtale_comp B S hS (hxs WalkingPair.left) hqEt
    have he : (xs WalkingPair.left).hom ≫ q.hom = jQ.hom :=
      congrArg (fun k => k.hom) (coprod.inl_desc jQ fQ)
    rwa [he] at hh
  exact ⟨Q, fQ, jQ, hQ, hQpb, hjQ, hQalg, hfQEt, hjQEt⟩

/-! ### Stacks 0DVJ -/

/-- **Stacks 0DVJ.** Let `V` and `U` be algebraic spaces over `S`, let `V'` be an open
subspace of `V` and let `f' : V' ⟶ U` be a separated étale morphism. Then there is an algebraic
space `W` over `S` together with an open subspace of `W` isomorphic to `U` and a morphism
`V ⟶ W` forming an elementary distinguished square, and the resulting square is a pushout of
`V ← V' → U` in the category of algebraic spaces over `S`. -/
@[stacks 0DVJ]
theorem exists_pushout_isElementaryDistinguishedSquare
    (U V : AlgebraicSpaces B S hS) (V' : Subfunctor V.obj)
    (hV' : IsOpenSubspace B S hS V') (f' : V'.toFunctor ⟶ U.obj)
    (hf' : IsEtale B S hS f') (hf'sep : IsSeparated B S hS f') :
    ∃ (W : AlgebraicSpaces B S hS) (Uw : Subfunctor W.obj) (e : U.obj ≅ Uw.toFunctor)
      (f : V ⟶ W),
      IsElementaryDistinguishedSquare B S hS W.property Uw f.hom ∧
        IsPushout
          (ObjectProperty.homMk V'.ι :
            (⟨V'.toFunctor, hV'.1⟩ : AlgebraicSpaces B S hS) ⟶ V)
          (ObjectProperty.homMk f' :
            (⟨V'.toFunctor, hV'.1⟩ : AlgebraicSpaces B S hS) ⟶ U)
          f (ObjectProperty.homMk (e.hom ≫ Uw.ι) : U ⟶ W) := by
  classical
  let J := BigFppfOver.topology B S hS
  let E := algebraicSpacesToSheaf B S hS
  let V₀ : AlgebraicSpaces B S hS := ⟨V'.toFunctor, hV'.1⟩
  let f₀ : V₀ ⟶ U := ObjectProperty.homMk f'
  let i₀ : V₀ ⟶ V := ObjectProperty.homMk V'.ι
  let ish : E.obj V₀ ⟶ E.obj V := E.map i₀
  have hishMono : Mono ish := Functor.mono_of_mono_map (sheafToPresheaf J (Type u))
    (show Mono V'.ι from inferInstance)
  obtain ⟨Q, fQ, jQ, hQ, hQpb, hjQ, hQalg, hfQEt, hjQEt⟩ :=
    exists_sheafPushout_isAlgebraicSpace B S hS U V V' hV' f' hf' hf'sep
  let W : AlgebraicSpaces B S hS := ⟨Q.obj, hQalg⟩
  have hjQmonoHom : Mono jQ.hom :=
    Functor.map_mono (sheafToPresheaf J (Type u)) jQ
  have hjOpen : IsOpenImmersion B S hS jQ.hom :=
    isOpenImmersion_of_isEtale_of_mono B S hS jQ.hom U.property hQalg hjQEt hjQmonoHom
  let Uw := Subfunctor.range jQ.hom
  have hUw : IsOpenSubspace B S hS Uw :=
    AlgebraicGeometry.Space.isOpenSubspace_range_of_isAlgebraicSpace B S hS U.property jQ.hom hjOpen
  obtain ⟨e, hej⟩ := isoRange_of_isOpenImmersion B S hS jQ.hom hjOpen
  have hClosed : IsClosed (Set.range (pointsMap B S hS Uw.toFunctor Uw.ι))ᶜ := by
    have hO : IsOpen (Set.range (pointsMap B S hS Uw.toFunctor Uw.ι)) := by
      rw [← openSubspacesOrderIso_apply B S hS W.obj W.property ⟨Uw, hUw⟩]
      exact (openSubspacesOrderIso B S hS W.obj W.property ⟨Uw, hUw⟩).isOpen
    exact hO.isClosed_compl
  let Zc : Subfunctor W.obj := reducedClosedSubspace B S hS W.obj W.property
    (Set.range (pointsMap B S hS Uw.toFunctor Uw.ι))ᶜ hClosed
  have hZcClosed : IsClosedSubspace B S hS Zc :=
    isClosedSubspace_reducedClosedSubspace B S hS W.obj W.property _ hClosed
  let Zsp : AlgebraicSpaces B S hS :=
    ⟨Zc.toFunctor, isAlgebraicSpace_reducedClosedSubspace B S hS W.obj W.property _ hClosed⟩
  have hUz := isClosedSubspace_preimage B S hS jQ.hom Zc hQalg U.property hZcClosed
  have hVz := isClosedSubspace_preimage B S hS fQ.hom Zc hQalg V.property hZcClosed
  let Uz : AlgebraicSpaces B S hS := ⟨(Zc.preimage jQ.hom).toFunctor, hUz.1⟩
  let Vz : AlgebraicSpaces B S hS := ⟨(Zc.preimage fQ.hom).toFunctor, hVz.1⟩
  have hempty : IsEmpty (points B S hS Uz.obj) := by
    apply isEmpty_points_preimage_of_disjoint_range B S hS jQ.hom Zc
    rw [range_pointsMap_ι_reducedClosedSubspace B S hS W.obj W.property _ hClosed]
    apply Set.disjoint_left.mpr
    rintro x ⟨a, rfl⟩ hx
    apply hx
    refine ⟨pointsMap B S hS U.obj e.hom a, ?_⟩
    have hc := pointsMap_comp_apply B S hS e.hom Uw.ι a
    rw [hej] at hc
    exact hc.symm
  let pz : E.obj Vz ⟶ E.obj Zsp := ⟨Zc.fromPreimage fQ.hom⟩
  let vz : E.obj Vz ⟶ E.obj V := ⟨(Zc.preimage fQ.hom).ι⟩
  let uz : E.obj Uz ⟶ E.obj U := ⟨(Zc.preimage jQ.hom).ι⟩
  let rz : E.obj Uz ⟶ E.obj Zsp := ⟨Zc.fromPreimage jQ.hom⟩
  let z : E.obj Zsp ⟶ Q := ⟨Zc.ι⟩
  have hpz : IsPullback pz vz z fQ :=
    IsPullback.of_map_of_faithful (sheafToPresheaf J (Type u))
      (CategoryTheory.Subfunctor.isPullback_preimage fQ.hom Zc)
  have hrz : IsPullback rz uz z jQ :=
    IsPullback.of_map_of_faithful (sheafToPresheaf J (Type u))
      (CategoryTheory.Subfunctor.isPullback_preimage jQ.hom Zc)
  let _ : IsIso pz := isIso_pullback_of_initial_other_leg ish (E.map f₀) fQ jQ hQ
    z pz vz rz uz hpz hrz (isInitial_sheaf_of_isEmpty_points B S hS Uz hempty)
  have hIso : IsIso (Zc.fromPreimage fQ.hom) :=
    inferInstanceAs (IsIso ((sheafToPresheaf J (Type u)).map pz))
  refine ⟨W, Uw, e, ObjectProperty.homMk fQ.hom, ?_, ?_⟩
  · exact ⟨V.property, hUw, hfQEt, hClosed, hIso⟩
  · have hpo := isPushout_of_isPushout_sheaf B S hS i₀ f₀
      (ObjectProperty.homMk fQ.hom : V ⟶ W) (ObjectProperty.homMk jQ.hom : U ⟶ W) hQ
    have hUU : (ObjectProperty.homMk (e.hom ≫ Uw.ι) : U ⟶ W) =
        (ObjectProperty.homMk jQ.hom : U ⟶ W) := ObjectProperty.hom_ext _ hej
    rwa [hUU]

/-! ### Every pushout of an open subspace along a separated étale morphism is cartesian -/

/-- **The pushout of Stacks 0DVJ is cartesian.** Let `V'` be an open subspace of an algebraic
space `V` and let `f' : V' ⟶ U` be a separated étale morphism. In every pushout square
`V ⟶ W ⟵ U` of `V ← V' → U` in the category of algebraic spaces over `S`, the subspace `V'` is
the fibre product `V ×_W U`: the square is a pullback square of presheaves.

The pushout of `V' ⟶ V` along `f'` in the category of sheaves is an algebraic space (this is
how Stacks 0DVJ is proved), so it is the pushout among algebraic spaces and is isomorphic to `W`.
Sheaves of sets form an adhesive category and `V' ⟶ V` is a monomorphism, so that sheaf pushout
square is also a pullback square. -/
theorem isPullback_of_isPushout_of_isEtale_of_isSeparated
    {U V P : AlgebraicSpaces B S hS} (V' : Subfunctor V.obj)
    (hV' : IsOpenSubspace B S hS V') (f' : V'.toFunctor ⟶ U.obj)
    (hf' : IsEtale B S hS f') (hf'sep : IsSeparated B S hS f') {fV : V ⟶ P} {fU : U ⟶ P}
    (hP : IsPushout
      (ObjectProperty.homMk V'.ι : (⟨V'.toFunctor, hV'.1⟩ : AlgebraicSpaces B S hS) ⟶ V)
      (ObjectProperty.homMk f' : (⟨V'.toFunctor, hV'.1⟩ : AlgebraicSpaces B S hS) ⟶ U)
      fV fU) :
    IsPullback V'.ι f' fV.hom fU.hom := by
  classical
  let J := BigFppfOver.topology B S hS
  let E := algebraicSpacesToSheaf B S hS
  let V₀ : AlgebraicSpaces B S hS := ⟨V'.toFunctor, hV'.1⟩
  let f₀ : V₀ ⟶ U := ObjectProperty.homMk f'
  let i₀ : V₀ ⟶ V := ObjectProperty.homMk V'.ι
  obtain ⟨Q, fQ, jQ, hQ, hQpb, -, hQalg, -, -⟩ :=
    exists_sheafPushout_isAlgebraicSpace B S hS U V V' hV' f' hf' hf'sep
  let W : AlgebraicSpaces B S hS := ⟨Q.obj, hQalg⟩
  have hpo := isPushout_of_isPushout_sheaf B S hS i₀ f₀
    (ObjectProperty.homMk fQ.hom : V ⟶ W) (ObjectProperty.homMk jQ.hom : U ⟶ W) hQ
  let φ : P ≅ W := hP.isoIsPushout _ _ hpo
  have hφV : fV ≫ φ.hom = (ObjectProperty.homMk fQ.hom : V ⟶ W) :=
    hP.inl_isoIsPushout_hom _ _ hpo
  have hφU : fU ≫ φ.hom = (ObjectProperty.homMk jQ.hom : U ⟶ W) :=
    hP.inr_isoIsPushout_hom _ _ hpo
  have hQpb' : IsPullback V'.ι f' fQ.hom jQ.hom := hQpb.map (sheafToPresheaf J (Type u))
  refine hQpb'.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((ObjectProperty.ι _).mapIso φ.symm) (by simp) (by simp) ?_ ?_
  · exact (congrArg (fun k : V ⟶ P => k.hom) (φ.comp_inv_eq.2 hφV.symm)).trans
      (Category.id_comp _).symm
  · exact (congrArg (fun k : U ⟶ P => k.hom) (φ.comp_inv_eq.2 hφU.symm)).trans
      (Category.id_comp _).symm

end AlgebraicGeometry.Space

end
