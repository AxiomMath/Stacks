module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Elements
public import Mathlib.CategoryTheory.Limits.Sifted
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.PreservesLimits
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.Preserves
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallBaseChange
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallProjection
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallToBigTopos
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.ClopenRefinement
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible
public import StacksCore.Tactic.StacksAttribute

/-!
# Sections of a small pro-étale inverse image at a weakly contractible object

Let `f : T ⟶ S` be a morphism in a chosen big pro-étale site and let `F` be a sheaf of sets on
the small pro-étale site of `S`. For an affine weakly contractible object `W` of the small
pro-étale site of `T`, the sections of `f_{small}^{-1} F` over `W` are the colimit of the
sections of `F` over the pro-étale objects of `S` receiving a map from `W` over `S`.

## Main definitions

* `AlgebraicGeometry.ProEtale.ProetaleComparison.smallInverseImageColimitMap`: the canonical
  map from that colimit to the sections of the inverse-image sheaf over `W`.

## Main results

* `AlgebraicGeometry.ProEtale.ProetaleComparison.bijective_smallInverseImageColimitMap`: the
  canonical map is a bijection at an affine weakly contractible object.

## References

* [Stacks Project, Tag 0F64](https://stacks.math.columbia.edu/tag/0F64)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.ProEtale.ProetaleComparison

variable (B : BigProetaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S)

private lemma lan_preservesFiniteProducts
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    [HasFiniteCoproducts C] (G : C ⥤ D) (F : Cᵒᵖ ⥤ Type (max u v))
    [PreservesFiniteProducts F] : PreservesFiniteProducts (G.op.lan.obj F) := by
  let : G.op.lan.IsLeftAdjoint := (G.op.lanAdjunction (Type (max u v))).isLeftAdjoint
  have : HasFiniteProducts F.Elements := ⟨fun _ ↦ inferInstance⟩
  have : Nonempty F.Elementsᵒᵖ := ⟨op (⊤_ F.Elements)⟩
  have : IsSifted F.Elementsᵒᵖ := inferInstance
  let E := AsSmall.{max u v} F.Elementsᵒᵖ
  let e : E ≌ F.Elementsᵒᵖ := AsSmall.equiv.symm
  have : IsSifted E := IsSifted.isSifted_of_equiv e
  constructor
  intro n
  let P := ObjectProperty.preservesLimitsOfShape (C := Type (max u v))
    (J := Dᵒᵖ) (Discrete (Fin n))
  have : P.IsClosedUnderColimitsOfShape E := inferInstance
  have : P.IsClosedUnderColimitsOfShape F.Elementsᵒᵖ :=
    ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence e
  apply P.prop_of_isColimit
    (isColimitOfPreserves G.op.lan (Presheaf.colimitOfRepresentable.{max u v} F))
  intro j
  change PreservesLimitsOfShape (Discrete (Fin n))
    (G.op.lan.obj (uliftYoneda.{max u v}.obj j.unop.1.unop))
  have : PreservesLimitsOfShape (Discrete (Fin n))
      (uliftYoneda.{max u v}.obj (G.obj j.unop.1.unop)) := by
    dsimp [uliftYoneda]
    infer_instance
  let e : uliftYoneda.{max u v}.obj (G.obj j.unop.1.unop) ≅
      G.op.lan.obj (uliftYoneda.{max u v}.obj j.unop.1.unop) :=
    (Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{max u v} G).app j.unop.1.unop
  exact preservesLimitsOfShape_of_natIso e

private lemma finite_coproduct_size (B : BigProetaleSite.{u})
    {ι : Type} [Finite ι] (X : ι → Scheme.{u}) (hX : ∀ i, B.Contains (X i)) :
    B.Contains (∐ X) := by
  change (∐ X).size < B.cutoff
  rw [← Scheme.size_congr (Sigma.reindex (Equiv.ulift : ULift.{u} ι ≃ ι) X)]
  exact Scheme.size_sigmaObj_lt B.aleph0_lt_cutoff B.aleph0_lt_cutoff_cof
    Cardinal.mk_le_aleph0 _ (fun i ↦ hX i.down)

private def smallCoproductCofan (B : BigProetaleSite.{u}) (T : B.Scheme)
    {ι : Type} [Finite ι] (X : ι → SmallProetale B T.obj T.property) : Cofan X := by
  let Y := fun i ↦ (SmallProetale.toScheme B T.obj T.property).obj (X i)
  let Z : B.Scheme := ⟨∐ Y, finite_coproduct_size B Y (fun i ↦ (X i).obj.left.property)⟩
  let g : Z ⟶ T := ObjectProperty.homMk (Limits.Sigma.desc (fun i ↦ B.inclusion.map (X i).obj.hom))
  have hg : WeaklyEtale (B.inclusion.map g) := by
    change WeaklyEtale (Limits.Sigma.desc (fun i ↦ B.inclusion.map (X i).obj.hom))
    exact IsZariskiLocalAtSource.sigmaDesc (fun i ↦ (X i).property)
  let W : SmallProetale B T.obj T.property := ⟨Over.mk g, hg⟩
  refine Cofan.mk W (fun i ↦ ObjectProperty.homMk (Over.homMk
    (ObjectProperty.homMk (Sigma.ι Y i)) ?_))
  apply B.inclusion.map_injective
  change Sigma.ι Y i ≫ Limits.Sigma.desc _ = _
  simp

private def smallCoproductCofanIsColimit (B : BigProetaleSite.{u}) (T : B.Scheme)
    {ι : Type} [Finite ι] (X : ι → SmallProetale B T.obj T.property) :
    IsColimit (smallCoproductCofan B T X) := by
  let H := SmallProetale.toScheme B T.obj T.property
  refine Cofan.IsColimit.mk _ (fun s ↦ ObjectProperty.homMk (Over.homMk
    (ObjectProperty.homMk (Limits.Sigma.desc (fun i ↦ H.map (s.inj i)))) ?_)) ?_ ?_
  · apply B.inclusion.map_injective
    change Limits.Sigma.desc _ ≫ B.inclusion.map s.pt.obj.hom = Limits.Sigma.desc _
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    change B.inclusion.map (s.inj i).hom.left ≫ B.inclusion.map s.pt.obj.hom = _
    rw [← Functor.map_comp, Over.w]
  · intro s i
    apply H.map_injective
    change Sigma.ι _ i ≫ Limits.Sigma.desc _ = _
    simp
  · intro s m hm
    apply H.map_injective
    apply Sigma.hom_ext
    intro i
    have hi := congrArg H.map (hm i)
    change Sigma.ι _ i ≫ H.map m = H.map (s.inj i) at hi
    change Sigma.ι (fun i ↦ H.obj (X i)) i ≫ H.map m =
      Sigma.ι (fun i ↦ H.obj (X i)) i ≫ Limits.Sigma.desc (fun i ↦ H.map (s.inj i))
    simpa only [Sigma.ι_comp_desc] using hi

private lemma small_open_cover (B : BigProetaleSite.{u}) (T : B.Scheme)
    {ι : Type} {W : SmallProetale B T.obj T.property}
    (X : ι → SmallProetale B T.obj T.property) (a : ∀ i, X i ⟶ W)
    (ho : ∀ i, IsOpenImmersion ((SmallProetale.toScheme B T.obj T.property).map (a i)))
    (hc : ∀ x : (SmallProetale.toScheme B T.obj T.property).obj W,
      ∃ i, x ∈ Set.range ((SmallProetale.toScheme B T.obj T.property).map (a i))) :
    Sieve.ofArrows X a ∈ SmallProetale.topology B T.obj T.property W := by
  let I := SmallProetale.inclusion B T.obj T.property
  let Q := BigProetaleOver.forget B T.obj T.property
  let H := I ⋙ Q
  let J := SmallProetale.topology B T.obj T.property
  let K := BigProetaleOver.topology B T.obj T.property
  let V := smallProetaleToBigProetaleFunctor B T T (𝟙 T)
  have e : V = I := by
    dsimp [V, smallProetaleToBigProetaleFunctor]
    rw [Over.mapId_eq]
    rfl
  have : I.IsCocontinuous J K := e ▸
    smallProetaleToBigProetaleFunctor_isCocontinuous B T T (𝟙 T)
  have : H.IsCocontinuous J B.topology := isCocontinuous_comp I Q J K
  have hbig : Sieve.ofArrows (fun i ↦ H.obj (X i)) (fun i ↦ H.map (a i)) ∈
      B.topology (H.obj W) := by
    apply Precoverage.generate_mem_toGrothendieck
    rw [B.precoverage_eq_comap, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    have : MorphismProperty.ContainsIdentities @WeaklyEtale := ⟨fun _ ↦ by infer_instance⟩
    apply (Scheme.zariskiPrecoverage_le_propQCPrecoverage (P := @WeaklyEtale))
    exact (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨hc, ho⟩
  apply J.superset_covering _ (H.cover_lift J B.topology hbig)
  intro A g hg
  change (Sieve.ofArrows (fun i ↦ H.obj (X i)) (fun i ↦ H.map (a i))) (H.map g) at hg
  rcases hg with ⟨Z, b, c, ⟨i⟩, hbc⟩
  let b' : A ⟶ X i := ObjectProperty.homMk (Over.homMk b (by
    calc
      b ≫ (X i).obj.hom = b ≫ (a i).hom.left ≫ W.obj.hom := by rw [Over.w]
      _ = g.hom.left ≫ W.obj.hom := by rw [← Category.assoc]; exact congrArg (· ≫ W.obj.hom) hbc
      _ = A.obj.hom := g.hom.w))
  have heq : b' ≫ a i = g := H.map_injective hbc
  rw [← heq]
  exact (Sieve.ofArrows X a).downward_closed (Sieve.ofArrows_mk X a i) b'

private lemma small_sheaf_bijective_restriction (B : BigProetaleSite.{u})
    (T : B.Scheme) (F : Sheaf (SmallProetale.topology B T.obj T.property) (Type (u + 1)))
    {ι : Type} {W : SmallProetale B T.obj T.property}
    (X : ι → SmallProetale B T.obj T.property) (a : ∀ i, X i ⟶ W)
    (ho : ∀ i, IsOpenImmersion ((SmallProetale.toScheme B T.obj T.property).map (a i)))
    (hc : ∀ x : (SmallProetale.toScheme B T.obj T.property).obj W,
      ∃ i, x ∈ Set.range ((SmallProetale.toScheme B T.obj T.property).map (a i)))
    (hd : Pairwise fun i j ↦ Disjoint
      (Set.range ((SmallProetale.toScheme B T.obj T.property).map (a i)))
      (Set.range ((SmallProetale.toScheme B T.obj T.property).map (a j)))) :
    Function.Bijective (fun t : F.obj.obj (op W) ↦ fun i ↦ F.obj.map (a i).op t) := by
  let H := SmallProetale.toScheme B T.obj T.property
  have hcov := small_open_cover B T X a ho hc
  have hsh : Presieve.IsSheafFor F.obj (Presieve.ofArrows X a) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact F.property.isSheafFor _ hcov
  rw [Function.bijective_iff_existsUnique]
  intro t
  have hcompat : Presieve.Arrows.Compatible F.obj a t := by
    intro i j Z gi gj heq
    by_cases hij : i = j
    · subst j
      have : Mono (a i) := H.mono_of_mono_map (ho i).mono
      rw [(cancel_mono (a i)).1 heq]
    · have : IsEmpty (H.obj Z) := ⟨fun z ↦ by
        have he : H.map (a i) (H.map gi z) = H.map (a j) (H.map gj z) :=
          congrArg (fun q ↦ H.map q z) heq
        exact Set.disjoint_left.1 (hd hij) ⟨H.map gi z, rfl⟩ ⟨H.map gj z, he.symm⟩⟩
      have hbot : (⊥ : Sieve Z) ∈ SmallProetale.topology B T.obj T.property Z := by
        have h := small_open_cover B T (W := Z) (fun i : Empty ↦ i.elim)
          (fun i ↦ i.elim) (fun i ↦ i.elim) (fun z ↦ isEmptyElim z)
        have he : Sieve.ofArrows (fun i : Empty ↦ (i.elim : SmallProetale B T.obj T.property))
            (fun i ↦ (i.elim : i.elim ⟶ Z)) = ⊥ :=
          le_bot_iff.mp fun _ _ ⟨_, _, _, ⟨i⟩, _⟩ ↦ i.elim
        rwa [he] at h
      let : Unique (F.obj.obj (op Z)) :=
        Types.isTerminalEquivUnique _ (Sheaf.isTerminalOfBotCover F Z hbot)
      exact Subsingleton.elim _ _
  rw [Presieve.isSheafFor_arrows_iff] at hsh
  obtain ⟨s, hs, hu⟩ := hsh t hcompat
  exact ⟨s, funext hs, fun y hy ↦ hu y (fun i ↦ congrFun hy i)⟩

private lemma small_hasFiniteCoproducts (B : BigProetaleSite.{u}) (T : B.Scheme) :
    HasFiniteCoproducts (SmallProetale B T.obj T.property) := by
  constructor
  intro n
  refine ⟨fun F ↦ ?_⟩
  let : HasColimit (Discrete.functor (F.obj ∘ Discrete.mk)) :=
    ⟨⟨_, smallCoproductCofanIsColimit B T (F.obj ∘ Discrete.mk)⟩⟩
  exact hasColimit_of_iso Discrete.natIsoFunctor

private def isLimitFanOfBijective {ι : Type} (X : ι → Type (u + 1))
    (W : Type (u + 1)) (a : ∀ i, W ⟶ X i)
    (ha : Function.Bijective (fun w ↦ fun i ↦ a i w)) :
    IsLimit (Fan.mk W a) := by
  apply Nonempty.some
  rw [Types.isLimit_iff]
  intro s hs
  rw [Function.bijective_iff_existsUnique] at ha
  obtain ⟨w, hw, hu⟩ := ha (fun i ↦ s ⟨i⟩)
  exact ⟨w, fun j ↦ congrFun hw j.as, fun y hy ↦ hu y (funext fun i ↦ hy ⟨i⟩)⟩

private lemma small_sheaf_preservesFiniteProducts (B : BigProetaleSite.{u})
    (T : B.Scheme) (F : Sheaf (SmallProetale.topology B T.obj T.property) (Type (u + 1))) :
    PreservesFiniteProducts F.obj := by
  let H := SmallProetale.toScheme B T.obj T.property
  have hpres {ι : Type} [Finite ι] (X : ι → SmallProetale B T.obj T.property) :
      PreservesLimit (Discrete.functor (fun i ↦ op (X i))) F.obj := by
    let c := smallCoproductCofan B T X
    have hc := smallCoproductCofanIsColimit B T X
    have hb : Function.Bijective
        (fun t : F.obj.obj (op c.pt) ↦ fun i ↦ F.obj.map (c.inj i).op t) := by
      apply small_sheaf_bijective_restriction B T F X c.inj
      · intro i
        change IsOpenImmersion (Sigma.ι (fun i ↦ H.obj (X i)) i)
        infer_instance
      · intro x
        let U := sigmaOpenCover (fun i ↦ H.obj (X i))
        exact ⟨U.idx x, U.covers x⟩
      · intro i j hij
        exact TopologicalSpace.Opens.coe_disjoint.mpr
          (disjoint_opensRange_sigmaι (fun i ↦ H.obj (X i)) i j hij)
    apply preservesLimit_of_preserves_limit_cone (Cofan.IsColimit.op hc)
    refine (Fan.isLimitMapConeEquiv F.obj _ c.op).symm ?_
    exact isLimitFanOfBijective _ _ _ hb
  constructor
  intro n
  constructor
  intro K
  let X := fun i : Fin n ↦ (K.obj ⟨i⟩).unop
  have : PreservesLimit (Discrete.functor (fun i ↦ op (X i))) F.obj := hpres X
  exact preservesLimit_of_iso_diagram F.obj (Discrete.natIsoFunctor (F := K)).symm

private def small_isColimit_of_disjoint_cover (B : BigProetaleSite.{u})
    (T : B.Scheme) {ι : Type} {W : SmallProetale B T.obj T.property}
    (X : ι → SmallProetale B T.obj T.property) (a : ∀ i, X i ⟶ W)
    (ho : ∀ i, IsOpenImmersion ((SmallProetale.toScheme B T.obj T.property).map (a i)))
    (hc : ∀ x : (SmallProetale.toScheme B T.obj T.property).obj W,
      ∃ i, x ∈ Set.range ((SmallProetale.toScheme B T.obj T.property).map (a i)))
    (hd : Pairwise fun i j ↦ Disjoint
      (Set.range ((SmallProetale.toScheme B T.obj T.property).map (a i)))
      (Set.range ((SmallProetale.toScheme B T.obj T.property).map (a j)))) :
    IsColimit (Cofan.mk W a) := by
  let H := SmallProetale.toScheme B T.obj T.property
  have : ∀ i, IsOpenImmersion (H.map (a i)) := ho
  have hcov : ⨆ i, (H.map (a i)).opensRange = ⊤ := by
    apply SetLike.coe_injective
    ext x
    simpa only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion,
      TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true, Scheme.Hom.coe_opensRange] using hc x
  have hdisj : Pairwise fun i j ↦ Disjoint (H.map (a i)).opensRange (H.map (a j)).opensRange :=
    fun _ _ hij ↦ TopologicalSpace.Opens.coe_disjoint.mp (hd hij)
  exact isColimitOfReflects H ((Cofan.isColimitMapCoconeEquiv H X (Cofan.mk W a)).symm
    (nonempty_isColimit_cofanMk_of (fun i ↦ H.map (a i)) hcov hdisj).some)

private lemma bijective_restriction_of_preservesProduct
    {C : Type (u + 1)} [Category.{u} C] (P : Cᵒᵖ ⥤ Type (u + 1))
    {ι : Type} {X : ι → C} (c : Cofan X) (hc : IsColimit c)
    [PreservesLimit (Discrete.functor (fun i ↦ op (X i))) P] :
    Function.Bijective (fun x : P.obj (op c.pt) ↦ fun i ↦ P.map (c.inj i).op x) := by
  let h := (Fan.isLimitMapConeEquiv P _ c.op)
    (isLimitOfPreserves P (Cofan.IsColimit.op hc))
  have hh := (Types.isLimit_iff _).mp ⟨h⟩
  rw [Function.bijective_iff_existsUnique]
  intro s
  have hs : (fun i : Discrete ι ↦ s i.as) ∈
      (Discrete.functor (fun i ↦ P.obj (op (X i)))).sections := by
    intro i j f
    obtain rfl := IsDiscrete.eq_of_hom f
    simp [Subsingleton.elim f (𝟙 i)]
  obtain ⟨x, hx, hu⟩ := hh (fun i : Discrete ι ↦ s i.as) hs
  exact ⟨x, funext fun i ↦ hx ⟨i⟩, fun y hy ↦ hu y (fun i ↦ congrFun hy i.as)⟩

private lemma weaklyContractible_of_smallProetale
    (W : SmallProetale B T.obj T.property)
    (hW : (SmallProetale.topology B T.obj T.property).IsWeaklyContractible W) :
    B.topology.IsWeaklyContractible
      ((BigProetaleOver.forget B T.obj T.property).obj
        ((SmallProetale.inclusion B T.obj T.property).obj W)) := by
  let C := SmallProetale B T.obj T.property
  let D := BigProetaleOver B T.obj T.property
  let J := SmallProetale.topology B T.obj T.property
  let K := BigProetaleOver.topology B T.obj T.property
  let I := SmallProetale.inclusion B T.obj T.property
  let Q := BigProetaleOver.forget B T.obj T.property
  let H := I ⋙ Q
  let V := smallProetaleToBigProetaleFunctor B
    (⟨T.obj, T.property⟩ : B.Scheme) (⟨T.obj, T.property⟩ : B.Scheme)
    (𝟙 (⟨T.obj, T.property⟩ : B.Scheme))
  have e : V = I := by
    dsimp [V, smallProetaleToBigProetaleFunctor]
    rw [Over.mapId_eq]
    rfl
  let : I.IsContinuous J K := (smallProetaleInclusion_isMorphismOfSites
    B T.obj T.property).toIsContinuous
  let : I.IsCocontinuous J K := e ▸ smallProetaleToBigProetaleFunctor_isCocontinuous
    B (⟨T.obj, T.property⟩ : B.Scheme) (⟨T.obj, T.property⟩ : B.Scheme)
    (𝟙 (⟨T.obj, T.property⟩ : B.Scheme))
  let : Q.IsContinuous K B.topology := inferInstance
  let : Q.IsCocontinuous K B.topology := inferInstance
  let : H.IsContinuous J B.topology := Functor.isContinuous_comp I Q J K B.topology
  let : H.IsCocontinuous J B.topology := isCocontinuous_comp I Q J K
  intro F G φ hφ s
  let F' := H.sheafPushforwardContinuous (Type u) J B.topology |>.obj F
  let G' := H.sheafPushforwardContinuous (Type u) J B.topology |>.obj G
  let φ' := (H.sheafPushforwardContinuous (Type u) J B.topology).map φ
  have hφ' : Sheaf.IsLocallySurjective φ' := by
    let : Presheaf.IsLocallySurjective B.topology φ.hom := hφ
    let : Presheaf.IsLocallySurjective J (H.op.whiskerLeft φ.hom) :=
      Presheaf.isLocallySurjective_whisker J B.topology H φ.hom
    change Presheaf.IsLocallySurjective J (H.op.whiskerLeft φ.hom)
    infer_instance
  obtain ⟨x, hx⟩ := hW F' G' φ' hφ' s
  refine ⟨x, ?_⟩
  change (φ.hom.app (op (H.obj W))) x = s at hx
  exact hx

private lemma clopenRefinements_of_smallProetale
    (W : SmallProetale B T.obj T.property)
    [IsAffine ((SmallProetale.toScheme B T.obj T.property).obj W)]
    (hW : (SmallProetale.topology B T.obj T.property).IsWeaklyContractible W) :
    ∀ (R : Sieve ((BigProetaleOver.forget B T.obj T.property).obj
      ((SmallProetale.inclusion B T.obj T.property).obj W))),
      R ∈ B.topology _ →
        ∃ (n : ℕ) (U : Fin n → B.Scheme) (g : (i : Fin n) → U i ⟶
          (BigProetaleOver.forget B T.obj T.property).obj
            ((SmallProetale.inclusion B T.obj T.property).obj W)),
          ProetaleWContractible.IsClopenDecompositionCover
            (fun i => (U i).obj) (fun i => B.inclusion.map (g i)) ∧
          ∀ i, R.arrows (g i) := by
  let V := (BigProetaleOver.forget B T.obj T.property).obj
    ((SmallProetale.inclusion B T.obj T.property).obj W)
  let : IsAffine V.obj := by
    change IsAffine ((SmallProetale.toScheme B T.obj T.property).obj W)
    infer_instance
  intro R hR
  exact exists_clopenRefinement_of_isWContractible B V
    (B.isWContractible_of_isWeaklyContractible V
      (weaklyContractible_of_smallProetale B T W hW)) R hR

private lemma smallSite_cover_has_clopen_refinement
    (W : SmallProetale B T.obj T.property)
    [IsAffine ((SmallProetale.toScheme B T.obj T.property).obj W)]
    (hW : (SmallProetale.topology B T.obj T.property).IsWeaklyContractible W)
    {R : Sieve W} (hR : R ∈ SmallProetale.topology B T.obj T.property W) :
    ∃ (n : ℕ) (U : Fin n → SmallProetale B T.obj T.property)
      (a : ∀ i, U i ⟶ W),
      ProetaleWContractible.IsClopenDecompositionCover
        (fun i => (SmallProetale.toScheme B T.obj T.property).obj (U i))
        (fun i => (SmallProetale.toScheme B T.obj T.property).map (a i)) ∧
      ∀ i, R.arrows (a i) := by
  classical
  let C := SmallProetale B T.obj T.property
  let D := BigProetaleOver B T.obj T.property
  let J := SmallProetale.topology B T.obj T.property
  let K := BigProetaleOver.topology B T.obj T.property
  let I := SmallProetale.inclusion B T.obj T.property
  let Q := BigProetaleOver.forget B T.obj T.property
  let H := I ⋙ Q
  let : I.IsContinuous J K := (smallProetaleInclusion_isMorphismOfSites
    B T.obj T.property).toIsContinuous
  let : Q.IsContinuous K B.topology := inferInstance
  let : H.IsContinuous J B.topology := Functor.isContinuous_comp I Q J K B.topology
  have hpush : R.functorPushforward H ∈ B.topology (H.obj W) :=
    (CoverPreserving.of_isContinuous H J B.topology).cover_preserve hR
  obtain ⟨n, U, g, hdec, hg⟩ :=
    clopenRefinements_of_smallProetale B T W hW (R.functorPushforward H) hpush
  let O : ∀ i, D := fun i => Over.mk (g i ≫ (I.obj W).hom)
  have hO : ∀ i, WeaklyEtale (B.inclusion.map (O i).hom) := by
    intro i
    have hopen : IsOpenImmersion (B.inclusion.map (g i)) := hdec.openImmersion i
    have hg : WeaklyEtale (B.inclusion.map (g i)) := by
      let : IsOpenImmersion (B.inclusion.map (g i)) := hopen
      infer_instance
    have hWEt : WeaklyEtale (B.inclusion.map (I.obj W).hom) := W.property
    change WeaklyEtale (B.inclusion.map (g i ≫ (I.obj W).hom))
    simpa using (show WeaklyEtale (B.inclusion.map (g i) ≫
      B.inclusion.map (I.obj W).hom) from inferInstance)
  let U' : Fin n → C := fun i => ⟨O i, hO i⟩
  let a : ∀ i, U' i ⟶ W := fun i =>
    ObjectProperty.homMk (Over.homMk (g i) (by rfl))
  have hmap : ∀ i, H.map (a i) = g i := by intro i; rfl
  refine ⟨n, U', a, hdec, ?_⟩
  · intro i
    have hi : (R.functorPushforward H).arrows (H.map (a i)) := by
      simpa [hmap] using hg i
    rcases hi with ⟨Y, b, c, hb, hbc⟩
    have heq' : g i = c ≫ H.map b := by
      simpa [hmap] using hbc
    have hOver : c ≫ (I.obj Y).hom = (O i).hom := by
      calc
        c ≫ (I.obj Y).hom = c ≫ (b.hom.left ≫ (I.obj W).hom) := by
          change c ≫ Y.obj.hom = c ≫ b.hom.left ≫ W.obj.hom
          rw [b.hom.w]
        _ = (c ≫ H.map b) ≫ (I.obj W).hom := by
          simp [H, I, Q, Category.assoc]
        _ = (g i) ≫ (I.obj W).hom := by rw [heq']
        _ = (O i).hom := rfl
    let c' : U' i ⟶ Y := ObjectProperty.homMk <|
      Over.homMk c hOver
    have heq'' : c' ≫ b = a i := by
      apply H.map_injective
      simp only [Functor.map_comp, hmap]
      simpa [c', H, I, Q] using heq'.symm
    rw [← heq'']
    exact R.downward_closed hb c'

private lemma bijective_toSheafify_small_of_affine_weaklyContractible
    (P : (SmallProetale B T.obj T.property)ᵒᵖ ⥤ Type (u + 1))
    [PreservesFiniteProducts P]
    (W : SmallProetale B T.obj T.property)
    [IsAffine ((SmallProetale.toScheme B T.obj T.property).obj W)]
    (hW : (SmallProetale.topology B T.obj T.property).IsWeaklyContractible W) :
    Function.Bijective ((toSheafify (SmallProetale.topology B T.obj T.property) P).app
      (op W)) := by
  let J := SmallProetale.topology B T.obj T.property
  let H := SmallProetale.toScheme B T.obj T.property
  let Q := (presheafToSheaf J (Type (u + 1))).obj P
  let η := toSheafify J P
  have : PreservesFiniteProducts Q.obj := small_sheaf_preservesFiniteProducts B T Q
  have href (R : Sieve W) (hR : R ∈ J W) :
      ∃ (n : ℕ) (X : Fin n → SmallProetale B T.obj T.property) (a : ∀ i, X i ⟶ W),
        Nonempty (IsColimit (Cofan.mk W a)) ∧ ∀ i, R.arrows (a i) := by
    obtain ⟨n, X, a, hdec, ha⟩ := smallSite_cover_has_clopen_refinement B T W hW hR
    have hcov : ∀ x : H.obj W, ∃ i, x ∈ Set.range (H.map (a i)) := by
      intro x
      have hx : x ∈ ⋃ i, Set.range (H.map (a i)).base := by
        rw [hdec.cover]
        trivial
      simpa only [Set.mem_iUnion] using hx
    exact ⟨n, X, a, ⟨small_isColimit_of_disjoint_cover B T X a
      hdec.openImmersion hcov hdec.disjoint⟩, ha⟩
  constructor
  · intro x y hxy
    obtain ⟨n, X, a, ⟨hc⟩, ha⟩ := href _ (Presheaf.equalizerSieve_mem J η x y hxy)
    exact (bijective_restriction_of_preservesProduct P (Cofan.mk W a) hc).1
      (funext ha)
  · intro s
    obtain ⟨n, X, a, ⟨hc⟩, ha⟩ := href _ (Presheaf.imageSieve_mem J η s)
    have hlift : ∀ i, ∃ t : P.obj (op (X i)),
        η.app (op (X i)) t = Q.obj.map (a i).op s := ha
    choose t ht using hlift
    obtain ⟨x, hx⟩ := (bijective_restriction_of_preservesProduct P
      (Cofan.mk W a) hc).2 t
    refine ⟨x, (bijective_restriction_of_preservesProduct Q.obj (Cofan.mk W a) hc).1 ?_⟩
    funext i
    change Q.obj.map (a i).op (η.app (op W) x) = Q.obj.map (a i).op s
    rw [← ht i, ← congrFun hx i]
    exact (η.naturality_apply (a i).op x).symm

/-- The canonical comparison from `colim_{W ⟶ f^*V} F(V)`, the colimit over the morphisms from
`W` to a pro-étale object of `S` over `S`, to the sections of `f_{small}^{-1} F` over `W`. -/
@[stacks 0F64 "the colimit and the canonical map to the inverse-image sections"]
public noncomputable def smallInverseImageColimitMap
    (F : Sheaf (SmallProetale.topology B S.obj S.property) (Type (u + 1)))
    (W : SmallProetale B T.obj T.property) :
    colimit (CostructuredArrow.proj
      (smallProetaleBaseChange B T S f).op (op W) ⋙ F.obj) →
      ((smallProetaleMorphism B T S f).inverseImage.obj F).obj.obj (op W) :=
  (Functor.leftKanExtensionObjIsoColimit
    (smallProetaleBaseChange B T S f).op F.obj (op W)).inv ≫
    (toSheafify (SmallProetale.topology B T.obj T.property)
      ((smallProetaleBaseChange B T S f).op.lan.obj F.obj)).app (op W) ≫
    (((Functor.sheafPullbackConstruction.sheafPullbackIso
      (smallProetaleBaseChange B T S f)
      (Type (u + 1)) (SmallProetale.topology B S.obj S.property)
      (SmallProetale.topology B T.obj T.property)).symm ≪≫
      (Adjunction.leftAdjointUniq
        ((smallProetaleMorphism B T S f).adj)
        ((smallProetaleBaseChange B T S f).sheafAdjunctionContinuous
          (Type (u + 1))
          (SmallProetale.topology B S.obj S.property)
          (SmallProetale.topology B T.obj T.property))).symm).hom.app F).hom.app (op W)

/-- For an affine weakly contractible object `W` of the small pro-étale site
of `T`, the sections of `f_{small}^{-1} F` over `W` are the colimit of the sections of `F` over
the pro-étale objects of `S` receiving a map from `W` over `S`. -/
@[stacks 0F64 "the canonical map is a bijection at an affine weakly contractible object"]
public theorem bijective_smallInverseImageColimitMap
    (F : Sheaf (SmallProetale.topology B S.obj S.property) (Type (u + 1)))
    (W : SmallProetale B T.obj T.property)
    [IsAffine ((SmallProetale.toScheme B T.obj T.property).obj W)]
    (hW : (SmallProetale.topology B T.obj T.property).IsWeaklyContractible W) :
    Function.Bijective (smallInverseImageColimitMap B T S f F W) := by
  let G := smallProetaleBaseChange B T S f
  have : HasFiniteCoproducts (SmallProetale B S.obj S.property) :=
    small_hasFiniteCoproducts B S
  have : PreservesFiniteProducts F.obj := small_sheaf_preservesFiniteProducts B S F
  have : PreservesFiniteProducts (G.op.lan.obj F.obj) :=
    lan_preservesFiniteProducts G F.obj
  have hη := bijective_toSheafify_small_of_affine_weaklyContractible B T
    (G.op.lan.obj F.obj) W hW
  have : IsIso ((toSheafify (SmallProetale.topology B T.obj T.property)
      (G.op.lan.obj F.obj)).app (op W)) := (isIso_iff_bijective _).2 hη
  unfold smallInverseImageColimitMap
  apply (isIso_iff_bijective _).1
  refine IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' this ?_)
  let e :=
    (Functor.sheafPullbackConstruction.sheafPullbackIso G (Type (u + 1))
      (SmallProetale.topology B S.obj S.property)
      (SmallProetale.topology B T.obj T.property)).symm ≪≫
    (Adjunction.leftAdjointUniq (smallProetaleMorphism B T S f).adj
      (G.sheafAdjunctionContinuous (Type (u + 1))
        (SmallProetale.topology B S.obj S.property)
        (SmallProetale.topology B T.obj T.property))).symm
  change IsIso ((((sheafToPresheaf (SmallProetale.topology B T.obj T.property)
    (Type (u + 1))).mapIso (e.app F)).app (op W)).hom)
  infer_instance

end AlgebraicGeometry.ProEtale.ProetaleComparison

end
