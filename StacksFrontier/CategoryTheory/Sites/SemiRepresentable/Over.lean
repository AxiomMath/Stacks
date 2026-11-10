module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Sheaves
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-!
# Semi-representable objects over an object of a site

Let `(C, J)` be a site and `X` an object of `C`. A semi-representable object of `C` *over* `X` is
a formal coproduct `K = {U i / X}` of objects of `C / X`; the Stacks Project writes
`SR(C, X)`. Its localization site `C / K` is the disjoint union of the slice sites `C / U i` with
the componentwise topology — the same site as for the underlying semi-representable object of
`C`, since the structural maps to `X` play no role in it.

What the structural maps give is a canonical functor `C / K ⥤ C / X`, which on the component
indexed by `i` is relocalization along `U i ⟶ X`. This file constructs that functor, proves it
continuous, cocontinuous and in possession of property P of Stacks 09W7, and does the same for
the relocalization functor attached to a morphism of `SR(C, X)`, which in addition induces a
morphism of topoi.

The proofs reduce everything to the corresponding statements for a semi-representable object of
`C` itself: the functor `C / K ⥤ C / X` factors as the componentwise relocalization functor into
the disjoint union of copies of `C / X`, followed by the functor collapsing those copies, and
each factor is continuous and cocontinuous.

## Main definitions

* `CategoryTheory.SemiRepresentable.componentwiseLocalizationFunctor`: the functor
  `C / K ⥤ C / X`.
* `CategoryTheory.SemiRepresentable.componentwiseLocalizationSitesOver`: a morphism of
  `SR(C, X)`, read as a morphism of semi-representable objects of `C`.
* `CategoryTheory.SemiRepresentable.componentwiseRelocalizationMorphismOfTopoi`: the morphism of
  topoi induced by componentwise relocalization.

## Main results

* `CategoryTheory.SemiRepresentable.componentwiseLocalizationFunctorCompIso`: on the component
  indexed by `i`, the functor `C / K ⥤ C / X` is `Over.map (K.obj i).hom`.
* `CategoryTheory.SemiRepresentable.componentwiseLocalization_isContinuous`,
  `CategoryTheory.SemiRepresentable.componentwiseLocalization_isCocontinuous`,
  `CategoryTheory.SemiRepresentable.componentwiseLocalization_hasCoverPullbacks`.
* `CategoryTheory.SemiRepresentable.componentwiseRelocalization_isContinuous`,
  `CategoryTheory.SemiRepresentable.componentwiseRelocalization_isCocontinuous`,
  `CategoryTheory.SemiRepresentable.componentwiseRelocalization_hasCoverPullbacks`.

## Implementation notes

The site `C / K` is `ComponentOver` of the formal coproduct `⟨K.I, fun i => (K.obj i).left⟩` of
the *domains* of the components of `K`, with `componentwiseTopology`; it is the disjoint union of
`Over (K.obj i).left`, not a disjoint union of slices taken inside `Over X`. Accordingly the
component functor is `Over.map (K.obj i).hom`.

`componentwiseRelocalizationMorphismOfTopoi` is bundled with the equation identifying its inverse
image, after forgetting that its values are sheaves, with restriction along the componentwise
relocalization functor. That records which functor induces the morphism, and keeps a choice of
continuity proof out of the public interface.

Property P for the localization functor is spelled out, with an independent universe for the
index types of covering families, exactly as the source's lemma is used; property P for the
relocalization functor is `CategoryTheory.Functor.HasCoverPullbacks`, whose covering-family index
universe is pinned.

## References

* [Stacks Project, Tag 0D89](https://stacks.math.columbia.edu/tag/0D89)
* [Stacks Project, Tag 0D85](https://stacks.math.columbia.edu/tag/0D85)
* [Stacks Project, Tag 09W7](https://stacks.math.columbia.edu/tag/09W7)
-/

@[expose] public section

universe w' w v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SemiRepresentable

variable {C : Type u} [Category.{v} C]

/-! ### The localization functor to `C / X` -/

/-- The localization functor from the componentwise site `C / K` of a semi-representable object
`K` over `X` to `C / X`. On the component indexed by `i` it is relocalization along
`K.obj i : U i ⟶ X`. -/
@[stacks 0D89 "localization"]
def componentwiseLocalizationFunctor {X : C} (K : FormalCoproduct.{w} (Over X)) :
    ComponentOver (⟨K.I, fun i => (K.obj i).left⟩ : FormalCoproduct.{w} C) ⥤ Over X :=
  CategoryTheory.Sigma.desc fun i => Over.map (K.obj i).hom

/-- On each component, the functor `C / K ⥤ C / X` is canonically the relocalization functor
associated to the structural map `U i ⟶ X`. -/
@[stacks 0D89 "localization"]
def componentwiseLocalizationFunctorCompIso {X : C} (K : FormalCoproduct.{w} (Over X))
    (i : K.I) :
    CategoryTheory.Sigma.incl (C := fun i : K.I => Over (K.obj i).left) i ⋙
      componentwiseLocalizationFunctor K ≅ Over.map (K.obj i).hom :=
  CategoryTheory.Sigma.inclDesc _ i

/-! ### Continuity, cocontinuity and property P of the localization functor -/

variable (J : GrothendieckTopology C) (X : C)

/-- The semi-representable object of `C` with the same index type as `K` and all components
equal to `X`. -/
private abbrev localizationTarget (X : C) (K : FormalCoproduct.{w} (Over X)) :
    FormalCoproduct.{w} C := ⟨K.I, fun _ => X⟩

/-- The morphism of semi-representable objects of `C` whose relocalization functor is the
componentwise part of `componentwiseLocalizationFunctor`. -/
private abbrev localizationSites (J : GrothendieckTopology C) (X : C)
    (K : FormalCoproduct.{w} (Over X)) : LocalizationSites.{w} C J :=
  ⟨⟨K.I, fun i => (K.obj i).left⟩, localizationTarget X K,
    ⟨id, fun i => (K.obj i).hom⟩⟩

/-- The functor collapsing the disjoint union of copies of `C / X` onto `C / X`. -/
private def localizationTargetForget (X : C) (K : FormalCoproduct.{w} (Over X)) :
    ComponentOver (localizationTarget X K) ⥤ Over X :=
  CategoryTheory.Sigma.desc fun _ => 𝟭 (Over X)

/-- The inclusion of the `i`-th copy of `C / X`. -/
private abbrev localizationTargetIncl (X : C) (K : FormalCoproduct.{w} (Over X))
    (i : K.I) : Over X ⥤ ComponentOver (localizationTarget X K) :=
  CategoryTheory.Sigma.incl
    (C := fun i : (localizationTarget X K).I => Over ((localizationTarget X K).obj i)) i

/-- The underlying arrow of a morphism of a disjoint union whose two endpoints carry the same
index. -/
private def sigmaHomUnderlying {I : Type w} {D : I → Type u}
    [∀ i, Category.{v} (D i)] {i : I} {A B : D i} :
    CategoryTheory.Sigma.SigmaHom ⟨i, A⟩ ⟨i, B⟩ → (A ⟶ B)
  | .mk f => f

/-- The functor `C / K ⥤ C / X` factors as componentwise relocalization into the disjoint union
of copies of `C / X`, followed by the collapsing functor. -/
private lemma localizationFunctor_eq (J : GrothendieckTopology C) (X : C)
    (K : FormalCoproduct.{w} (Over X)) :
    componentwiseLocalizationFunctor K =
      (localizationSites J X K).relocalizationFunctor ⋙ localizationTargetForget X K := by
  refine CategoryTheory.Functor.hext (h_obj := ?_) (h_map := ?_)
  · intro U
    rcases U with ⟨i, U⟩
    rfl
  · intro U V f
    rcases U with ⟨i, U⟩
    cases f with
    | mk f =>
      change (Over.map (K.obj i).hom).map f ≍
        (𝟭 (Over X)).map ((Over.map (K.obj i).hom).map f)
      simp

/-- The collapsing functor is cocontinuous. -/
private lemma localizationTargetForget_isCocontinuous (J : GrothendieckTopology C)
    (X : C) (K : FormalCoproduct.{w} (Over X)) :
    (localizationTargetForget X K).IsCocontinuous
      (componentwiseTopology J (localizationTarget X K)) (J.over X) := by
  refine ⟨?_⟩
  intro U R hR
  rcases U with ⟨i, U⟩
  change R.functorPullback (localizationTargetForget X K) ∈
    componentwiseTopology J (localizationTarget X K) ⟨i, U⟩
  rw [mem_componentwiseTopology_iff]
  have hpull : (R.functorPullback (localizationTargetForget X K)).functorPullback
      (localizationTargetIncl X K i) = R := by
    ext Y f
    simp [Sieve.functorPullback, Presieve.functorPullback,
      localizationTargetIncl, localizationTargetForget, localizationTarget]
    rfl
  rwa [hpull]

/-- The collapsing functor is continuous. -/
private lemma localizationTargetForget_isContinuous (J : GrothendieckTopology C)
      (X : C) (K : FormalCoproduct.{w} (Over X)) :
    (localizationTargetForget X K).IsContinuous
      (componentwiseTopology J (localizationTarget X K)) (J.over X) := by
  refine ⟨fun G => ?_⟩
  apply isSheaf_componentwise J ((localizationTargetForget X K).op ⋙ G.obj)
  intro i
  let incl := localizationTargetIncl X K i
  change Presieve.IsSheaf (J.over X)
    (incl.op ⋙ (localizationTargetForget X K).op ⋙ G.obj)
  have hG : Presieve.IsSheaf (J.over X) G.obj :=
    (isSheaf_iff_isSheaf_of_type (J.over X) G.obj).mp G.property
  let hcomp : incl ⋙ localizationTargetForget X K ≅ 𝟭 (Over X) :=
    CategoryTheory.Sigma.inclDesc (fun _ => 𝟭 (Over X)) i
  let eop : incl.op ⋙ (localizationTargetForget X K).op ≅ 𝟭 ((Over X)ᵒᵖ) := by
    simpa using (Functor.opComp incl (localizationTargetForget X K)).symm ≪≫
      (NatIso.op hcomp).symm ≪≫ Functor.opId (Over X)
  exact Presieve.isSheaf_iso (J := J.over X) (Functor.isoWhiskerRight eop G.obj) hG

variable (K : FormalCoproduct.{w} (Over X))

/-- **Stacks 0D89.** The componentwise localization functor to `C / X` is continuous. -/
@[stacks 0D89 "localization_property"]
instance componentwiseLocalization_isContinuous :
    (componentwiseLocalizationFunctor K).IsContinuous
      (componentwiseTopology J
        (⟨K.I, fun i => (K.obj i).left⟩ : FormalCoproduct.{w} C))
  (J.over X) := by
  let S := localizationSites J X K
  rw [localizationFunctor_eq J X K]
  have : S.relocalizationFunctor.IsContinuous S.sourceTopology S.targetTopology :=
    LocalizationSites.relocalizationFunctor_isContinuous S
  have : (localizationTargetForget X K).IsContinuous S.targetTopology (J.over X) :=
    localizationTargetForget_isContinuous J X K
  exact Functor.isContinuous_comp S.relocalizationFunctor
    (localizationTargetForget X K) S.sourceTopology S.targetTopology (J.over X)

/-- **Stacks 0D89.** The componentwise localization functor to `C / X` is cocontinuous. -/
@[stacks 0D89 "localization_property"]
instance componentwiseLocalization_isCocontinuous :
    (componentwiseLocalizationFunctor K).IsCocontinuous
      (componentwiseTopology J
        (⟨K.I, fun i => (K.obj i).left⟩ : FormalCoproduct.{w} C))
  (J.over X) := by
  let S := localizationSites J X K
  rw [localizationFunctor_eq J X K]
  have : S.relocalizationFunctor.IsCocontinuous S.sourceTopology S.targetTopology :=
    LocalizationSites.relocalizationFunctor_isCocontinuous S
  have : (localizationTargetForget X K).IsCocontinuous S.targetTopology (J.over X) :=
    localizationTargetForget_isCocontinuous J X K
  exact isCocontinuous_comp S.relocalizationFunctor
    (localizationTargetForget X K) S.sourceTopology S.targetTopology

/-- **Stacks 0D89.** The componentwise localization functor to `C / X` has property P:
pullbacks of covering families along maps out of its image are representable and cover. -/
@[stacks 0D89 "localization_property"]
lemma componentwiseLocalization_hasCoverPullbacks
    [(J.over X).toCoverage.HasPullbacks] :
    ∀ (𝒱 : Covering.{max u v, v, w'} (Over X)),
      𝒱.2.presieve₀ ∈ (J.over X).toCoverage 𝒱.1 →
      ∀ (U : ComponentOver
        (⟨K.I, fun i => (K.obj i).left⟩ : FormalCoproduct.{w} C))
        (g : (componentwiseLocalizationFunctor K).obj U ⟶ 𝒱.1),
        ∃ (P : 𝒱.2.I₀ → ComponentOver
            (⟨K.I, fun i => (K.obj i).left⟩ : FormalCoproduct.{w} C))
          (p₁ : ∀ i, P i ⟶ U)
          (p₂ : ∀ i, (componentwiseLocalizationFunctor K).obj (P i) ⟶ 𝒱.2.X i),
          (∀ i,
            (componentwiseLocalizationFunctor K).map (p₁ i) ≫ g =
              p₂ i ≫ 𝒱.2.f i ∧
              ∀ (T : ComponentOver
                  (⟨K.I, fun i => (K.obj i).left⟩ : FormalCoproduct.{w} C))
                (a : T ⟶ U)
                (b : (componentwiseLocalizationFunctor K).obj T ⟶ 𝒱.2.X i),
                (componentwiseLocalizationFunctor K).map a ≫ g = b ≫ 𝒱.2.f i →
                  ∃! l : T ⟶ P i,
                    (l ≫ p₁ i = a ∧
                      (componentwiseLocalizationFunctor K).map l ≫ p₂ i = b)) ∧
            (PreZeroHypercover.mk 𝒱.2.I₀ P p₁).presieve₀ ∈
              (componentwiseTopology J
                (⟨K.I, fun i => (K.obj i).left⟩ : FormalCoproduct.{w} C)).toCoverage U :=
  by
  classical
  let F := componentwiseLocalizationFunctor K
  intro 𝒱 h𝒱 U g
  rcases U with ⟨i, U⟩
  let W : Over X := (Over.map (K.obj i).hom).obj U
  let g' : W ⟶ 𝒱.1 := g
  have hPullbacks : (Sieve.generate 𝒱.2.presieve₀).arrows.HasPullbacks g' :=
    Precoverage.hasPullbacks_of_mem _ (by
      rwa [GrothendieckTopology.mem_toCoverage_iff, Sieve.generate_sieve])
  have hpb (a : 𝒱.2.I₀) : HasPullback (𝒱.2.f a) g' :=
    hPullbacks.hasPullback (Sieve.le_generate 𝒱.2.presieve₀ _ _ (𝒱.2.presieve₀_f a))
  let Q (a : 𝒱.2.I₀) : Over X := pullback (𝒱.2.f a) g'
  let q₁ (a : 𝒱.2.I₀) : Q a ⟶ W := pullback.snd (𝒱.2.f a) g'
  let q₂ (a : 𝒱.2.I₀) : Q a ⟶ 𝒱.2.X a := pullback.fst (𝒱.2.f a) g'
  have hpulltop : (Sieve.generate 𝒱.2.presieve₀).pullback g' ∈ J.over X W :=
    (J.over X).pullback_stable g' ((GrothendieckTopology.mem_toCoverage_iff (J.over X)).mp h𝒱)
  have hpull_le : (Sieve.generate 𝒱.2.presieve₀).pullback g' ≤
      Sieve.generate (Presieve.ofArrows Q q₁) := by
    intro T f hf
    rw [Sieve.generate] at hf ⊢
    obtain ⟨Z, h, k, ⟨a⟩, hfac⟩ := hf
    exact ⟨Q a, pullback.lift h f (by simp [← hfac]), q₁ a, ⟨a⟩, pullback.lift_snd h f _⟩
  let P (a : 𝒱.2.I₀) : Over (K.obj i).left := Over.mk ((q₁ a).left ≫ U.hom)
  let p₁comp (a : 𝒱.2.I₀) : P a ⟶ U := Over.homMk (q₁ a).left rfl
  let p₁ (a : 𝒱.2.I₀) :
      (⟨i, P a⟩ : ComponentOver
        (⟨K.I, fun i => (K.obj i).left⟩ : FormalCoproduct.{w} C)) ⟶ ⟨i, U⟩ :=
    CategoryTheory.Sigma.SigmaHom.mk (p₁comp a)
  let p₂ (a : 𝒱.2.I₀) : F.obj ⟨i, P a⟩ ⟶ 𝒱.2.X a :=
    Over.homMk (q₂ a).left
      ((Over.w (q₂ a)).trans ((Over.w (q₁ a)).symm.trans (Category.assoc _ _ _).symm))
  have hsquare (a : 𝒱.2.I₀) : F.map (p₁ a) ≫ g = p₂ a ≫ 𝒱.2.f a := Over.OverMorphism.ext
    (congrArg CommaMorphism.left (pullback.condition (f := 𝒱.2.f a) (g := g')).symm :)
  refine ⟨fun a => ⟨i, P a⟩, p₁, p₂, fun a => ⟨hsquare a, ?_⟩, ?_⟩
  · rintro ⟨_, T⟩ ⟨aT⟩ bT h
    have key : ∀ {A B : C} (h : A ⟶ B) {U T : Over A} {Z V : Over B}
        (f : Z ⟶ V) (g : (Over.map h).obj U ⟶ V) [HasPullback f g]
        (a : T ⟶ U) (b : (Over.map h).obj T ⟶ Z), (Over.map h).map a ≫ g = b ≫ f →
        ∃! l : T ⟶ Over.mk ((pullback.snd f g).left ≫ U.hom),
          l.left ≫ (pullback.snd f g).left = a.left ∧
            l.left ≫ (pullback.fst f g).left = b.left := by
      intro A B h U T Z V f g _ a b hab
      let lQ := pullback.lift b ((Over.map h).map a) hab.symm
      have h₁ : lQ.left ≫ (pullback.snd f g).left = a.left :=
        (congrArg CommaMorphism.left (pullback.lift_snd b ((Over.map h).map a) hab.symm) :)
      have h₂ : lQ.left ≫ (pullback.fst f g).left = b.left :=
        (congrArg CommaMorphism.left (pullback.lift_fst b ((Over.map h).map a) hab.symm) :)
      refine ⟨Over.homMk lQ.left (by simp [← Category.assoc, h₁]), ⟨h₁, h₂⟩, ?_⟩
      rintro l ⟨hl₁, hl₂⟩
      have hw : l.left ≫ (pullback f g).hom = ((Over.map h).obj T).hom := by
        rw [← Over.w (pullback.snd f g)]
        simpa using congrArg (· ≫ h) (Over.w l)
      have hl : (Over.homMk l.left hw : (Over.map h).obj T ⟶ pullback f g) = lQ := pullback.hom_ext
        (Over.OverMorphism.ext (by simp [hl₂, h₂])) (Over.OverMorphism.ext (by simp [hl₁, h₁]))
      ext
      exact (congrArg CommaMorphism.left hl :)
    obtain ⟨l, ⟨hl₁, hl₂⟩, hl⟩ := key (K.obj i).hom (𝒱.2.f a) g' aT bT h
    refine ⟨CategoryTheory.Sigma.SigmaHom.mk l, ⟨by
      simp only [p₁]; exact congrArg CategoryTheory.Sigma.SigmaHom.mk (Over.OverMorphism.ext hl₁),
        Over.OverMorphism.ext hl₂⟩, ?_⟩
    rintro ⟨l'⟩ ⟨hl'₁, hl'₂⟩
    have h₁ : l' ≫ p₁comp a = aT := (congrArg sigmaHomUnderlying hl'₁ :)
    exact congrArg CategoryTheory.Sigma.SigmaHom.mk
      (hl l' ⟨(congrArg CommaMorphism.left h₁ :), (congrArg CommaMorphism.left hl'₂ :)⟩)
  · have hq : Sieve.generate (Presieve.ofArrows Q q₁) ∈
        J.over X ((Over.map (K.obj i).hom).obj U) :=
      (J.over X).superset_covering hpull_le hpulltop
    have hcov : Sieve.generate (Presieve.ofArrows
        (fun a => (⟨i, Over.mk ((q₁ a).left ≫ U.hom)⟩ : ComponentOver
          (⟨K.I, fun i => (K.obj i).left⟩ : FormalCoproduct.{w} C)))
        fun a => CategoryTheory.Sigma.SigmaHom.mk (Over.homMk (q₁ a).left rfl)) ∈
        componentwiseTopology J (⟨K.I, fun i => (K.obj i).left⟩ : FormalCoproduct.{w} C)
          ⟨i, U⟩ := by
      rw [mem_componentwiseTopology_iff]
      have hQ : Sieve.generate (Presieve.ofArrows (fun a => (Q a).left) fun a => (q₁ a).left) ∈
          J U.left := by
        have h := (GrothendieckTopology.mem_over_iff J _).1 hq
        rwa [Sieve.overEquiv_ofArrows] at h
      have hP : Sieve.generate (Presieve.ofArrows (fun a => Over.mk ((q₁ a).left ≫ U.hom))
          fun a => (Over.homMk (q₁ a).left rfl : Over.mk ((q₁ a).left ≫ U.hom) ⟶ U)) ∈
          J.over (K.obj i).left U := by
        refine (GrothendieckTopology.mem_over_iff J _).2 ?_
        rw [Sieve.overEquiv_ofArrows]
        simpa using hQ
      refine (J.over (K.obj i).left).superset_covering ?_ hP
      rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
      exact fun a => Sieve.le_generate _ _ _ ⟨a⟩
    exact hcov

/-! ### Relocalization along a morphism of `SR(C, X)` -/

/-- A morphism of semi-representable objects over `X`, read as a morphism of semi-representable
objects of `C`: the structural maps to `X` are forgotten, while the component objects and
component maps are retained. -/
def componentwiseLocalizationSitesOver {K L : FormalCoproduct.{w} (Over X)}
    (f : K ⟶ L) : LocalizationSites.{w} C J where
  K := ⟨K.I, fun i ↦ (K.obj i).left⟩
  L := ⟨L.I, fun i ↦ (L.obj i).left⟩
  f := ⟨f.f, fun i ↦ (f.φ i).left⟩

/-- **Stacks 0D89.** The morphism of topoi from `Sh(C / K)` to `Sh(C / L)` induced by
componentwise relocalization along a morphism `K ⟶ L` of `SR(C, X)`, together with the
identification of its inverse image with restriction along the componentwise functor. -/
@[stacks 0D89 "relocalization"]
noncomputable def componentwiseRelocalizationMorphismOfTopoi
    {K L : FormalCoproduct.{w} (Over X)} (f : K ⟶ L) :
    let S := componentwiseLocalizationSitesOver J X f
    { g : MorphismOfTopoi
        (Sheaf S.sourceTopology (Type (max w v u)))
        (Sheaf S.targetTopology (Type (max w v u))) //
      g.inverseImage ⋙ sheafToPresheaf S.sourceTopology (Type (max w v u)) =
        sheafToPresheaf S.targetTopology (Type (max w v u)) ⋙
          (CategoryTheory.Functor.whiskeringLeft _ _ _).obj S.relocalizationFunctor.op } := by
  let S := componentwiseLocalizationSitesOver J X f
  let R := S.relocalizationFunctor
  let A := Type (max w v u)
  exact ⟨{
    pushforward := R.sheafPushforwardCocontinuous A S.sourceTopology S.targetTopology
    inverseImage := R.sheafPushforwardContinuous A S.sourceTopology S.targetTopology
    adj := R.sheafAdjunctionCocontinuous A S.sourceTopology S.targetTopology
    preservesFiniteLimits := inferInstance
  }, rfl⟩

/-- **Stacks 0D89.** The componentwise relocalization functor is continuous. -/
@[stacks 0D89 "relocalization_property"]
instance componentwiseRelocalization_isContinuous
    {K L : FormalCoproduct.{w} (Over X)} (f : K ⟶ L) :
    let S := componentwiseLocalizationSitesOver J X f
    S.relocalizationFunctor.IsContinuous S.sourceTopology S.targetTopology :=
  LocalizationSites.relocalizationFunctor_isContinuous _

/-- **Stacks 0D89.** The componentwise relocalization functor is cocontinuous. -/
@[stacks 0D89 "relocalization_property"]
instance componentwiseRelocalization_isCocontinuous
    {K L : FormalCoproduct.{w} (Over X)} (f : K ⟶ L) :
    let S := componentwiseLocalizationSitesOver J X f
    S.relocalizationFunctor.IsCocontinuous S.sourceTopology S.targetTopology :=
  LocalizationSites.relocalizationFunctor_isCocontinuous _

/-- **Stacks 0D89.** The componentwise relocalization functor has property P: pullbacks of
covering families along maps out of its image are representable and covering. -/
@[stacks 0D89 "relocalization_property"]
lemma componentwiseRelocalization_hasCoverPullbacks
    {K L : FormalCoproduct.{w} (Over X)} (f : K ⟶ L)
    [J.toCoverage.HasPullbacks] :
    let S := componentwiseLocalizationSitesOver J X f
    S.relocalizationFunctor.HasCoverPullbacks
      (fun 𝒰 ↦ 𝒰.2.presieve₀ ∈ S.sourceTopology.toCoverage 𝒰.1)
      (fun 𝒱 ↦ 𝒱.2.presieve₀ ∈ S.targetTopology.toCoverage 𝒱.1) :=
  LocalizationSites.relocalizationFunctor_hasCoverPullbacks _

end CategoryTheory.SemiRepresentable

end

add_to_stacks 0D89 "site" CategoryTheory.SemiRepresentable.ComponentOver
add_to_stacks 0D89 "site" CategoryTheory.SemiRepresentable.componentwiseTopology
add_to_stacks 0D89 "product"
  CategoryTheory.SemiRepresentable.formalCoproductSliceSheavesEquivalence
