module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Order.Filter.AtTopBot.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.FiniteTypeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion

/-!
# Isomorphisms onto a directed limit of algebraic spaces

Let `X = lim Xᵢ` be a directed inverse limit of quasi-compact algebraic spaces over a base
algebraic space, with closed-immersion transition morphisms and stages locally of finite type
over the base.  An isomorphism `Y ⟶ X` whose source is locally of finite presentation over the
base is already an isomorphism onto `Xᵢ` for all sufficiently large `i`.

## Main results

* `AlgebraicGeometry.Space.eventually_isIso_comp_limitπ`: an isomorphism `Y ⟶ lim Xᵢ` with `Y`
  locally of finite presentation over the base is an isomorphism onto `Xᵢ` for all large `i`.

## References

* [Stacks Project, Tag 0828](https://stacks.math.columbia.edu/tag/0828)
* [Stacks Project, Tag 081B](https://stacks.math.columbia.edu/tag/081B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Filter Opposite

universe u v w

namespace AlgebraicGeometry

/-! ### Limits of systems of closed subschemes -/

/-- A connected system of closed immersions into a fixed scheme has a limit, which is a closed
subscheme of that scheme cut out by the supremum of their ideal sheaves. -/
private lemma exists_isLimit_of_isClosedImmersion {J : Type v} [Category.{w} J] [IsConnected J]
    {U : Scheme.{u}} (D : J ⥤ Scheme.{u}) (t : D ⟶ (Functor.const J).obj U)
    (ht : ∀ j, IsClosedImmersion (t.app j)) :
    ∃ (c : Cone D) (r : c.pt ⟶ U),
      Nonempty (IsLimit c) ∧ IsClosedImmersion r ∧
      (∀ j, c.π.app j ≫ t.app j = r) ∧ r.ker = ⨆ j, (t.app j).ker := by
  classical
  let K : U.IdealSheafData := ⨆ j, (t.app j).ker
  let r := K.subschemeι
  have hker : r.ker = K := Scheme.IdealSheafData.ker_subschemeι K
  have hle' (j : J) : (t.app j).ker ≤ r.ker := by
    rw [hker]
    exact @le_iSup U.IdealSheafData J _ (fun j : J => (t.app j).ker) j
  let p (j : J) : K.subscheme ⟶ D.obj j :=
    @IsClosedImmersion.lift _ _ _ (t.app j) r (ht j) (hle' j)
  have hp (j : J) : p j ≫ t.app j = r := by
    dsimp [p]; apply IsClosedImmersion.lift_fac
  let c : Cone D :=
    { pt := K.subscheme
      π :=
        { app := p
          naturality := by
            intro i j f
            dsimp
            simp only [Category.id_comp]
            have := ht j
            apply (cancel_mono (t.app j)).1
            rw [Category.assoc, t.naturality f]
            simpa using (hp j).trans (hp i).symm } }
  refine ⟨c, r, ⟨?_⟩, inferInstance, hp, hker⟩
  let j₀ : J := Classical.arbitrary J
  let base (s : Cone D) := s.π.app j₀ ≫ t.app j₀
  have hb (s : Cone D) (j : J) : s.π.app j ≫ t.app j = base s :=
    nat_trans_from_is_connected (s.π ≫ t) j j₀
  have hle (s : Cone D) : r.ker ≤ (base s).ker := by
    rw [hker]
    refine iSup_le fun j => ?_
    rw [← hb s j]
    exact Scheme.Hom.le_ker_comp _ _
  refine { lift := fun s => IsClosedImmersion.lift r (base s) (hle s), fac := ?_, uniq := ?_ }
  · intro s j
    have := ht j
    apply (cancel_mono (t.app j)).1
    show (IsClosedImmersion.lift r (base s) (hle s) ≫ p j) ≫ t.app j = _
    rw [Category.assoc, hp, IsClosedImmersion.lift_fac, hb]
  · intro s m hm
    apply (cancel_mono r).1
    rw [IsClosedImmersion.lift_fac, ← hp j₀, ← Category.assoc,
      show m ≫ p j₀ = s.π.app j₀ from hm j₀]

/-- The ideal of global sections cut out by a closed immersion of finite presentation into an
affine scheme is finitely generated. -/
private lemma fg_ker_ideal_top_of_locallyOfFinitePresentation {X U : Scheme.{u}} [IsAffine U]
    (r : X ⟶ U) [IsClosedImmersion r] [LocallyOfFinitePresentation r] :
    (r.ker.ideal ⟨⊤, isAffineOpen_top U⟩).FG := by
  have : IsAffine X := (IsClosedImmersion.isAffine_surjective_of_isAffine r).1
  have hs := (IsClosedImmersion.isAffine_surjective_of_isAffine r).2
  let f := r.appTop.hom
  let _ : Algebra (↑(U.presheaf.obj (op ⊤))) (↑(X.presheaf.obj (op ⊤))) := f.toAlgebra
  have : Algebra.FinitePresentation (↑(U.presheaf.obj (op ⊤))) (↑(X.presheaf.obj (op ⊤))) :=
    r.finitePresentation_appTop
  let g : (↑(U.presheaf.obj (op ⊤))) →ₐ[(↑(U.presheaf.obj (op ⊤)))]
      (↑(X.presheaf.obj (op ⊤))) := { __ := f, commutes' := fun _ => rfl }
  have hf := Algebra.FinitePresentation.ker_fG_of_surjective g hs
  rw [Scheme.ker_of_isAffine]
  simpa [Scheme.IdealSheafData.ofIdealTop_ideal, g, f] using hf

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A connected system of closed subobjects of an object of the site has a limit in the site,
which is a closed subobject cut out by the supremum of their ideal sheaves. -/
private lemma exists_isLimit_site_of_isClosedImmersion {J : Type v} [Category.{w} J]
    [IsConnected J] {U : BigFppfOver B S hS} (D : J ⥤ BigFppfOver B S hS)
    (t : D ⟶ (Functor.const J).obj U)
    (ht : ∀ j, _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (t.app j))) :
    ∃ (c : Cone D) (r : c.pt ⟶ U),
      Nonempty (IsLimit c) ∧
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map r) ∧
      (∀ j, c.π.app j ≫ t.app j = r) ∧
      ((BigFppfOver.toScheme B S hS).map r).ker =
        ⨆ j, ((BigFppfOver.toScheme B S hS).map (t.app j)).ker := by
  classical
  let F := BigFppfOver.toScheme B S hS
  let ts : D ⋙ F ⟶ (Functor.const J).obj (F.obj U) :=
    { app := fun j => F.map (t.app j)
      naturality := by
        intro i j f
        show F.map (D.map f) ≫ F.map (t.app j) = F.map (t.app i) ≫ 𝟙 _
        rw [← F.map_comp, Category.comp_id]
        exact congrArg F.map ((t.naturality f).trans (Category.comp_id _)) }
  obtain ⟨cs, r, ⟨hc⟩, hr, hw, hk⟩ := exists_isLimit_of_isClosedImmersion (D ⋙ F) ts ht
  have := hr
  let V : BigFppfOver B S hS :=
    Over.mk
      (ObjectProperty.homMk (X := ⟨cs.pt, Scheme.size_lt_of_isClosedImmersion r U.left.property⟩)
        (r ≫ U.hom.hom))
  let p (j : J) : V ⟶ D.obj j := Over.homMk (ObjectProperty.homMk (cs.π.app j)) (by
    apply ObjectProperty.hom_ext
    show cs.π.app j ≫ (D.obj j).hom.hom = r ≫ U.hom.hom
    rw [← hw j, Category.assoc]
    exact (congrArg (fun z => cs.π.app j ≫ z.hom) (Over.w (t.app j))).symm)
  let c : Cone D :=
    { pt := V
      π := { app := p, naturality := fun _ _ f => F.map_injective (cs.π.naturality f) } }
  let r' : V ⟶ U := Over.homMk (ObjectProperty.homMk r) (by rfl)
  have hc' : IsLimit (F.mapCone c) := hc
  exact ⟨c, r', ⟨isLimitOfReflects F hc'⟩, hr, fun j => F.map_injective (hw j), hk⟩

/-- A system of closed immersions into a represented presheaf is, up to natural isomorphism,
the Yoneda image of a system in the site. -/
private lemma exists_siteDiagram_of_isClosedImmersion {J : Type v} [Category.{w} J]
    (U : BigFppfOver B S hS) (E : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (t : E ⟶ (Functor.const J).obj (yoneda.obj U))
    (ht : ∀ j, IsClosedImmersion B S hS (t.app j)) :
    ∃ (D : J ⥤ BigFppfOver B S hS) (e : D ⋙ yoneda ≅ E) (r : D ⟶ (Functor.const J).obj U),
      (∀ j, _root_.AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B S hS).map (r.app j))) ∧
      ∀ j, e.hom.app j ≫ t.app j = yoneda.map (r.app j) := by
  classical
  have hE (j : J) : yoneda.essImage (E.obj j) := by
    obtain ⟨V, v, a, hpb⟩ := (ht j).1 (𝟙 _)
    have : IsIso a := hpb.isIso_fst_of_isIso
    exact ⟨V, ⟨asIso a⟩⟩
  let D := Functor.essImage.liftFunctor E yoneda hE
  let e : D ⋙ yoneda ≅ E := Functor.essImage.liftFunctorCompIso E yoneda hE
  let r : D ⟶ (Functor.const J).obj U :=
    { app := fun j => yoneda.preimage (e.hom.app j ≫ t.app j)
      naturality := by
        intro i j f
        apply yoneda.map_injective
        simp only [Functor.map_comp, Functor.map_preimage]
        show yoneda.map (D.map f) ≫ (e.hom.app j ≫ t.app j) =
          (e.hom.app i ≫ t.app i) ≫ yoneda.map (𝟙 U)
        rw [yoneda.map_id]
        refine Eq.trans ?_ (Category.comp_id (e.hom.app i ≫ t.app i)).symm
        calc
          _ = (yoneda.map (D.map f) ≫ e.hom.app j) ≫ t.app j := (Category.assoc _ _ _).symm
          _ = (e.hom.app i ≫ E.map f) ≫ t.app j :=
            congrArg (fun z => z ≫ t.app j) (e.hom.naturality f)
          _ = e.hom.app i ≫ (E.map f ≫ t.app j) := Category.assoc _ _ _
          _ = e.hom.app i ≫ t.app i :=
            congrArg (fun z => e.hom.app i ≫ z)
              ((t.naturality f).trans (Category.comp_id _)) }
  have hr (j : J) : e.hom.app j ≫ t.app j = yoneda.map (r.app j) :=
    (yoneda.map_preimage _).symm
  refine ⟨D, e, r, fun j => ?_, hr⟩
  refine (ht j).2 (𝟙 _) (e.hom.app j) (r.app j) (IsPullback.of_horiz_isIso ?_)
  exact ⟨by rw [Category.comp_id]; exact hr j⟩

/-- Over an affine object of the site, a projection from the limit of a cofiltered system of
closed subobjects is an isomorphism at some stage, provided the limit is locally of finite
presentation over that object. -/
private lemma exists_isIso_π_app_of_locallyOfFinitePresentation {J : Type v} [Category.{w} J]
    [IsCofiltered J] {U : BigFppfOver B S hS} (D : J ⥤ BigFppfOver B S hS)
    (t : D ⟶ (Functor.const J).obj U)
    (ht : ∀ j, _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (t.app j)))
    (c : Cone D) (r : c.pt ⟶ U)
    (hr : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map r))
    (hw : ∀ j, c.π.app j ≫ t.app j = r)
    (hk : ((BigFppfOver.toScheme B S hS).map r).ker =
      ⨆ j, ((BigFppfOver.toScheme B S hS).map (t.app j)).ker)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map r)) :
    ∃ j, IsIso (c.π.app j) := by
  classical
  let F := BigFppfOver.toScheme B S hS
  have := hU
  have := hr
  have := hfp
  let topU : (F.obj U).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  let K : J → Ideal (↑((F.obj U).presheaf.obj (op ⊤))) :=
    fun j => (F.map (t.app j)).ker.ideal topU
  have hle {i j : J} (f : i ⟶ j) : K j ≤ K i := by
    have he : F.map (D.map f) ≫ F.map (t.app j) = F.map (t.app i) := by
      rw [← F.map_comp]
      exact congrArg F.map ((t.naturality f).trans (Category.comp_id _))
    have hl := Scheme.Hom.le_ker_comp (F.map (D.map f)) (F.map (t.app j))
    rw [he] at hl
    exact hl topU
  have hdir : Directed (· ≤ ·) K := fun i j =>
    ⟨IsCofiltered.min i j, hle (IsCofiltered.minToLeft i j), hle (IsCofiltered.minToRight i j)⟩
  have htop : (F.map r).ker.ideal topU = ⨆ j, K j := by
    rw [hk, Scheme.IdealSheafData.ideal_iSup]
    exact iSup_apply
  have hfg : (⨆ j, K j).FG := htop ▸ fg_ker_ideal_top_of_locallyOfFinitePresentation (F.map r)
  have : Nonempty J := IsCofiltered.nonempty
  obtain ⟨-, ⟨j, rfl⟩, hj⟩ := (Submodule.fg_iff_compact _).mp hfg
    (Set.range K) (⨆ j, K j) (Set.range_nonempty K) hdir.directedOn_range
    (isLUB_iSup (f := K)) le_rfl
  have hj : K j = ⨆ k, K k := le_antisymm (le_iSup K j) hj
  have heq : (F.map r).ker = (F.map (t.app j)).ker :=
    Scheme.IdealSheafData.ext_of_isAffine (htop.trans hj.symm)
  have := ht j
  have : IsIso (F.map (c.π.app j)) :=
    _root_.AlgebraicGeometry.IsClosedImmersion.isIso_of_ker_eq (F.map r) (F.map (t.app j)) _
      (by rw [← F.map_comp, hw]) heq
  exact ⟨j, isIso_of_reflects_iso (c.π.app j) F⟩

/-! ### Auxiliary categorical and sheaf-theoretic facts -/

/-- If every transition in a cofiltered inverse system is monic, so is each projection from
its limit. -/
private lemma mono_limitπ_of_mono_map {J : Type v} [Category.{w} J] [IsCofiltered J]
    {C : Type*} [Category C] (D : J ⥤ C) (c : Cone D) (hc : IsLimit c)
    (hmono : ∀ ⦃i j : J⦄ (f : i ⟶ j), Mono (D.map f)) (i : J) : Mono (c.π.app i) := by
  constructor
  intro T a b hab
  refine hc.hom_ext fun j => ?_
  have := hmono (IsCofiltered.minToLeft i j)
  have hk : a ≫ c.π.app (IsCofiltered.min i j) = b ≫ c.π.app (IsCofiltered.min i j) := by
    apply (cancel_mono (D.map (IsCofiltered.minToLeft i j))).1
    simpa only [Category.assoc, c.w] using hab
  simpa only [← c.w (IsCofiltered.minToRight i j), Category.assoc] using
    congrArg (fun z => z ≫ D.map (IsCofiltered.minToRight i j)) hk

/-- A locally surjective monomorphism of sheaves of types is an isomorphism. -/
private lemma isIso_of_mono_of_isLocallySurjective {C : Type v} [Category.{w} C]
    (J : GrothendieckTopology C) {F G : Cᵒᵖ ⥤ Type u} (hF : Presheaf.IsSheaf J F)
    (hG : Presheaf.IsSheaf J G) (f : F ⟶ G) (hmono : Mono f)
    (hloc : Presheaf.IsLocallySurjective J f) : IsIso f := by
  let g : (⟨F, hF⟩ : Sheaf J (Type u)) ⟶ ⟨G, hG⟩ := ObjectProperty.homMk f
  have hi : Sheaf.IsLocallyInjective g :=
    Presheaf.isLocallyInjective_of_injective J f
      (fun X => (mono_iff_injective _).mp ((NatTrans.mono_iff_mono_app f).1 hmono X))
  have : IsIso g := (Sheaf.isLocallyBijective_iff_isIso g).1 ⟨hi, hloc⟩
  exact (sheafToPresheaf J (Type u)).map_isIso g

/-! ### Transferring atlas properties along base change -/

/-- An étale morphism of algebraic spaces from a represented presheaf has étale represented
base changes. -/
private lemma presheafEtale_of_isEtale (U : BigFppfOver B S hS)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q : yoneda.obj U ⟶ X) (hq : IsEtale B S hS q) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q := by
  let E := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have hid : E.presheaf (𝟙 (yoneda.obj U)) := by
    refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, ?_⟩
    intro A W g fst snd hpb
    have : IsIso (yoneda.map snd) := hpb.isIso_snd_of_isIso
    have : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map snd
    show Etale ((BigFppfOver.toScheme B S hS).map snd)
    infer_instance
  exact hq U (𝟙 _) hid

/-- A represented pullback of a surjective étale chart is again surjective and étale. -/
private lemma presheafSurjective_and_presheafEtale_of_isPullback
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : X ⟶ Y)
    (U V : BigFppfOver B S hS) (q₀ : yoneda.obj U ⟶ Y) (qᵢ : yoneda.obj V ⟶ X) (v : V ⟶ U)
    (hpb : IsPullback qᵢ (yoneda.map v) p q₀)
    (hSurjective₀ : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q₀)
    (hEtale₀ : IsEtale B S hS q₀) :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf qᵢ ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf qᵢ := by
  have hEtale₀' := presheafEtale_of_isEtale B S hS U q₀ hEtale₀
  have : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip hSurjective₀,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip hEtale₀'⟩

/-- If the base change of a morphism along a surjective étale chart of its target is an
isomorphism, the morphism is locally surjective for the topology of the site. -/
private lemma isLocallySurjective_of_isIso_pullback
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : F ⟶ G)
    (U V : BigFppfOver B S hS) (q : yoneda.obj U ⟶ G) (a : yoneda.obj V ⟶ F) (r : V ⟶ U)
    (hsq : a ≫ p = yoneda.map r ≫ q)
    (hSurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hEtale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hr : IsIso (yoneda.map r)) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) p := by
  classical
  let J := BigFppfOver.topology B S hS
  let hrep := hSurj.1
  refine ⟨?_⟩
  intro T x
  let g : yoneda.obj T ⟶ G := yonedaEquiv.symm x
  let sourcePr := hrep.fst g
  let targetPr := hrep.snd g
  have hpbq : IsPullback sourcePr (yoneda.map targetPr) q g := hrep.isPullback g
  let q₀ := (BigFppfOver.forget B S hS).map targetPr
  have hsurj : Surjective ((BigFppfOver.toScheme B S hS).map targetPr) :=
    hSurj.2 g sourcePr targetPr hpbq
  have hetale : Etale ((BigFppfOver.toScheme B S hS).map targetPr) :=
    hEtale.2 g sourcePr targetPr hpbq
  have hbase : Sieve.generate (Presieve.singleton q₀) ∈
      B.topology ((BigFppfOver.forget B S hS).obj T) :=
    singleton_mem_bigFppf_topology B q₀ hsurj hetale
  let S₀ : Sieve T := (Sieve.overEquiv T).symm (Sieve.generate (Presieve.singleton q₀))
  have hcover : S₀ ∈ J T := B.topology.overEquiv_symm_mem_over T _ hbase
  refine J.superset_covering ?_ hcover
  intro W k hk
  have hk₀ : Sieve.generate (Presieve.singleton q₀) k.left := by simpa [S₀] using hk
  obtain ⟨W', b₀, c₀, hc₀, hfac₀⟩ := hk₀
  cases hc₀
  let b : W ⟶ hrep.pullback g := Over.homMk b₀ (by
    calc
      b₀ ≫ (hrep.pullback g).hom = b₀ ≫ targetPr.left ≫ T.hom := by rw [← Over.w targetPr]
      _ = (b₀ ≫ q₀) ≫ T.hom := by rw [← Category.assoc]; rfl
      _ = k.left ≫ T.hom := by rw [hfac₀]
      _ = W.hom := Over.w k)
  have hb : b ≫ targetPr = k := Over.OverMorphism.ext hfac₀
  let α : hrep.pullback g ⟶ U := yoneda.preimage sourcePr
  have : IsIso r := Yoneda.fullyFaithful.isIso_of_isIso_map r
  let ℓ : yoneda.obj W ⟶ F := yoneda.map (b ≫ α ≫ inv r) ≫ a
  have hℓ : ℓ ≫ p = yoneda.map k ≫ g := by
    dsimp [ℓ]
    calc
      (yoneda.map (b ≫ α ≫ inv r) ≫ a) ≫ p =
          yoneda.map (b ≫ α ≫ inv r) ≫ (a ≫ p) := by simp [Category.assoc]
      _ = yoneda.map (b ≫ α ≫ inv r) ≫ yoneda.map r ≫ q := by rw [hsq]
      _ = yoneda.map (b ≫ α) ≫ q := by simp [Functor.map_comp, Category.assoc]
      _ = yoneda.map b ≫ yoneda.map α ≫ q := by simp [Functor.map_comp, Category.assoc]
      _ = yoneda.map b ≫ sourcePr ≫ q := by simp [α]
      _ = yoneda.map b ≫ yoneda.map targetPr ≫ g := by rw [hpbq.w]
      _ = yoneda.map (b ≫ targetPr) ≫ g := by simp [Functor.map_comp]
      _ = yoneda.map k ≫ g := by rw [hb]
  refine ⟨yonedaEquiv ℓ, ?_⟩
  show p.app (op W) (yonedaEquiv ℓ) = G.map k.op x
  rw [← yonedaEquiv_comp, hℓ]
  have hg : yonedaEquiv g = x := by simp [g]
  rw [← hg, yonedaEquiv_naturality]

/-- Local finite presentation is unchanged by precomposing with an isomorphism. -/
private lemma isLocallyOfFinitePresentation_of_isIso_precomp
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : Y ⟶ X) [IsIso e] (g : X ⟶ Z)
    (h : IsLocallyOfFinitePresentation B S hS (e ≫ g)) :
    IsLocallyOfFinitePresentation B S hS g := by
  intro U V a b φ ha hb hφ
  let E := (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf
  have : E.RespectsIso := inferInstance
  refine h U V (a ≫ inv e) b φ (MorphismProperty.RespectsIso.postcomp E (inv e) a ha) hb ?_
  simpa only [Category.assoc, IsIso.inv_hom_id_assoc] using hφ

set_option synthInstance.maxHeartbeats 400000 in
/-- Limits of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance hasLimits_presheaf :
    HasLimitsOfSize.{0, 0} ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance hasPullbacks_presheaf : HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  inferInstance

private instance (priority := high) hasPullback_presheaf
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### The eventual isomorphism -/

/-- **An isomorphism onto a directed limit is eventually an isomorphism onto the stages.**  Let
`X = lim Xᵢ` be a directed limit of algebraic spaces over an algebraic space `Bspace` and let
`f : Y ⟶ X` be an isomorphism.  If the stages `Xᵢ` are quasi-compact and locally of finite type
over `Bspace`, the transition morphisms are closed immersions, and `Y` is locally of finite
presentation over `Bspace`, then `Y ⟶ Xᵢ` is an isomorphism for all sufficiently large `i`. -/
@[stacks 0828 "part (3): isomorphism", sga "3 XI 3.11" "more general"]
theorem eventually_isIso_comp_limitπ
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (contains : B.Contains S)
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (Bspace : (BigFppfOver B S contains)ᵒᵖ ⥤ Type u)
    (algebraicBase : IsAlgebraicSpace B S contains Bspace)
    (D : Iᵒᵖ ⥤ (BigFppfOver B S contains)ᵒᵖ ⥤ Type u)
    (algebraicStage : ∀ i, IsAlgebraicSpace B S contains (D.obj (op i)))
    (t : D ⟶ (Functor.const Iᵒᵖ).obj Bspace)
    (c : Cone D) (isLimit : IsLimit c) (s : c.pt ⟶ Bspace)
    (commutes : c.π ≫ t = (Functor.const Iᵒᵖ).map s)
    (Y : (BigFppfOver B S contains)ᵒᵖ ⥤ Type u) (algebraic : IsAlgebraicSpace B S contains Y)
    (f : Y ⟶ c.pt) (iso : IsIso f)
    (quasiCompactStage : ∀ i, IsQuasiCompactSpace B S contains (D.obj (op i)))
    (finiteType : ∀ i, IsLocallyOfFiniteType B S contains (t.app (op i)))
    (closed : ∀ ⦃i j : I⦄ (h : i ≤ j), IsClosedImmersion B S contains (D.map (homOfLE h).op))
    (finitePresentation : IsLocallyOfFinitePresentation B S contains (f ≫ s)) :
    ∀ᶠ i in atTop, IsIso (f ≫ c.π.app (op i)) := by
  have := iso
  have hC : IsAlgebraicSpace B S contains c.pt :=
    AlgebraicGeometry.isAlgebraicSpace_of_iso B S contains (asIso f).symm algebraic
  have hProjection : ∀ᶠ i in atTop, IsIso (c.π.app (op i)) := by
    classical
    have hs := isLocallyOfFinitePresentation_of_isIso_precomp B S contains f s finitePresentation
    have hProjFP (i : I) : IsLocallyOfFinitePresentation B S contains (c.π.app (op i)) := by
      refine isLocallyOfFinitePresentation_of_comp B S contains hC (algebraicStage i) algebraicBase
        (c.π.app (op i)) (t.app (op i)) ?_ (finiteType i)
      have hi : c.π.app (op i) ≫ t.app (op i) = s := by
        simpa only [NatTrans.comp_app, Functor.const_map_app] using
          congrArg (fun η => η.app (op i)) commutes
      rwa [hi]
    let i₀ : I := Classical.choice ‹Nonempty I›
    obtain ⟨U₀, q₀, hAffine₀, hSurjective₀, hEtale₀⟩ :=
      (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S contains
        (D.obj (op i₀)) (algebraicStage i₀)).mp (quasiCompactStage i₀)
    have hTransitionMono : ∀ ⦃i j : Iᵒᵖ⦄ (g : i ⟶ j), Mono (D.map g) := by
      intro i j g
      have h : j.unop ≤ i.unop := leOfHom g.unop
      rw [show g = (homOfLE h).op from Subsingleton.elim _ _]
      exact mono_of_isClosedImmersion B S contains _ (closed h)
    have hProjectionMono (i : I) : Mono (c.π.app (op i)) :=
      mono_limitπ_of_mono_map D c isLimit hTransitionMono (op i)
    let P := Over.post (X := op i₀) D ⋙ Over.pullback q₀
    let E := P ⋙ Over.forget (yoneda.obj U₀)
    let pc : Cone E := (Over.forget (yoneda.obj U₀)).mapCone
      ((Over.pullback q₀).mapCone (c.overPost (op i₀)))
    have : IsConnected (Over (op i₀)) := IsCofiltered.isConnected _
    have hpc : IsLimit pc :=
      isLimitOfPreserves (Over.forget (yoneda.obj U₀))
        (isLimitOfPreserves (Over.pullback q₀) (isLimit.overPost (op i₀)))
    let τ : E ⟶ (Functor.const (Over (op i₀))).obj (yoneda.obj U₀) :=
      { app := fun j => (P.obj j).hom
        naturality := fun _ _ g => (Over.w (P.map g)).trans (Category.comp_id _).symm }
    have hτ (j : Over (op i₀)) : IsClosedImmersion B S contains (τ.app j) := by
      have : (MorphismProperty.inverseImage
          (@_root_.AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S contains)).presheaf.IsStableUnderBaseChange :=
        MorphismProperty.relative_isStableUnderBaseChange _
      refine MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback (D.map j.hom) q₀) ?_
      rw [show j.hom = (homOfLE (leOfHom j.hom.unop)).op from Subsingleton.elim _ _]
      exact closed _
    obtain ⟨G, e, r, hr, he⟩ := exists_siteDiagram_of_isClosedImmersion B S contains U₀ E τ hτ
    obtain ⟨lc, v₀, ⟨hlc⟩, hv₀, hw, hk⟩ :=
      exists_isLimit_site_of_isClosedImmersion B S contains G r hr
    let lc' : Cone E := (Cone.postcompose e.hom).obj (yoneda.mapCone lc)
    have hlc' : IsLimit lc' :=
      (IsLimit.postcomposeHomEquiv e _).symm (isLimitOfPreserves yoneda hlc)
    let a : yoneda.obj lc.pt ≅ pc.pt := hlc'.conePointUniqueUpToIso hpc
    have ha (j : Over (op i₀)) :
        a.hom ≫ pc.π.app j = yoneda.map (lc.π.app j) ≫ e.hom.app j :=
      hlc'.conePointUniqueUpToIso_hom_comp hpc j
    have hpcv (j : Over (op i₀)) :
        pc.π.app j ≫ τ.app j = pullback.snd (c.π.app (op i₀)) q₀ :=
      Over.w (((Over.pullback q₀).mapCone (c.overPost (op i₀))).π.app j)
    have hav : a.hom ≫ pullback.snd (c.π.app (op i₀)) q₀ = yoneda.map v₀ := by
      rw [← hpcv (Over.mk (𝟙 (op i₀))), ← Category.assoc, ha, Category.assoc, he,
        ← yoneda.map_comp, hw]
    let alim : yoneda.obj lc.pt ⟶ c.pt := a.hom ≫ pullback.fst (c.π.app (op i₀)) q₀
    have hpbLim : IsPullback alim (yoneda.map v₀) (c.π.app (op i₀)) q₀ := by
      apply IsPullback.of_iso_pullback _ a rfl hav
      refine ⟨?_⟩
      rw [← hav]
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun z => a.hom ≫ z) pullback.condition).trans (Category.assoc _ _ _).symm)
    have hfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S contains).map v₀) :=
      hProjFP i₀ lc.pt U₀ alim q₀ v₀
        (presheafSurjective_and_presheafEtale_of_isPullback B S contains (c.π.app (op i₀)) U₀ lc.pt
          q₀ alim v₀ hpbLim hSurjective₀ hEtale₀).2
        (presheafEtale_of_isEtale B S contains U₀ q₀ hEtale₀) hpbLim.w.symm
    obtain ⟨j, hj⟩ := exists_isIso_π_app_of_locallyOfFinitePresentation B S contains G r hr lc v₀
      hv₀ hw hk hAffine₀ hfp
    let qj : yoneda.obj (G.obj j) ⟶ D.obj j.left :=
      e.hom.app j ≫ pullback.fst (D.map j.hom) q₀
    have hpbj : IsPullback qj (yoneda.map (r.app j)) (D.map j.hom) q₀ := by
      apply IsPullback.of_iso_pullback _ (e.app j) rfl (he j)
      refine ⟨?_⟩
      rw [← he j]
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun z => e.hom.app j ≫ z) pullback.condition).trans
          (Category.assoc _ _ _).symm)
    have hsq : alim ≫ c.π.app j.left = yoneda.map (lc.π.app j) ≫ qj := by
      have hpcfst : pc.π.app j ≫ pullback.fst (D.map j.hom) q₀ =
          pullback.fst (c.π.app (op i₀)) q₀ ≫ c.π.app j.left := pullback.lift_fst _ _ _
      calc
        _ = a.hom ≫ (pullback.fst (c.π.app (op i₀)) q₀ ≫ c.π.app j.left) :=
          Category.assoc _ _ _
        _ = a.hom ≫ (pc.π.app j ≫ pullback.fst (D.map j.hom) q₀) :=
          congrArg (fun z => a.hom ≫ z) hpcfst.symm
        _ = (a.hom ≫ pc.π.app j) ≫ pullback.fst (D.map j.hom) q₀ :=
          (Category.assoc _ _ _).symm
        _ = (yoneda.map (lc.π.app j) ≫ e.hom.app j) ≫ pullback.fst (D.map j.hom) q₀ :=
          congrArg (fun z => z ≫ pullback.fst (D.map j.hom) q₀) (ha j)
        _ = _ := Category.assoc _ _ _
    obtain ⟨hsj, hej⟩ := presheafSurjective_and_presheafEtale_of_isPullback B S contains
      (D.map j.hom) U₀ (G.obj j) q₀ qj (r.app j) hpbj hSurjective₀ hEtale₀
    have : IsIso (lc.π.app j) := hj
    have hjIso : IsIso (c.π.app j.left) :=
      isIso_of_mono_of_isLocallySurjective (BigFppfOver.topology B S contains) hC.isSheaf
        (algebraicStage j.left.unop).isSheaf (c.π.app j.left) (hProjectionMono j.left.unop)
        (isLocallySurjective_of_isIso_pullback B S contains (c.π.app j.left) (G.obj j) lc.pt qj alim
          (lc.π.app j) hsq hsj hej inferInstance)
    refine Filter.eventually_atTop.mpr ⟨j.left.unop, fun k hjk => ?_⟩
    have : Mono (D.map (homOfLE hjk).op) := hTransitionMono _
    have := hjIso
    refine ⟨⟨D.map (homOfLE hjk).op ≫ inv (c.π.app j.left), ?_, ?_⟩⟩
    · rw [← Category.assoc,
        show c.π.app (op k) ≫ D.map (homOfLE hjk).op = c.π.app j.left from c.w _,
        IsIso.hom_inv_id]
    · apply (cancel_mono (D.map (homOfLE hjk).op)).1
      simp only [Category.assoc, Category.id_comp]
      rw [show c.π.app (op k) ≫ D.map (homOfLE hjk).op = c.π.app j.left from c.w _]
      simp
  filter_upwards [hProjection] with i hi
  have := hi
  infer_instance

end Space

end AlgebraicGeometry

end
