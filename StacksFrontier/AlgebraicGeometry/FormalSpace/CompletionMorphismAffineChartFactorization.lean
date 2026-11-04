module

public import StacksFrontier.AlgebraicGeometry.Etale.LiftAcrossClosedImmersion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceThickening
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleChartLiftAlongThickening
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ModificationCompletionDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.StandardCoveringSieves

/-!
# Factoring a morphism out of a completion through an affine étale chart

Let `X` and `W` be presheaves on the big fppf site of `S`, with `W` an algebraic space, let
`T ⊆ |X|` be closed and let `ŵ : X_{/T} ⟶ W` be a morphism out of the completion of `X` along
`T`. Let `p : V ⟶ X` be a morphism from a locally Noetherian site object. This file shows that
every point of `V` over `T` has an affine Noetherian étale neighbourhood `r : P ⟶ V`, mapping
into an affine open `O` of `S`, on which the restriction of `ŵ` to `P_{/T}` factors through an
étale chart `π : W₀ ⟶ W` of `W` with `W₀` affine and mapping into `O`.

## Main results

* `AlgebraicGeometry.Space.hasImageIn_yoneda_iff_range_subset`: a morphism of site objects has
  point-set image in the inverse image of a set of points exactly when its underlying morphism
  of schemes maps into the corresponding set of scheme points.
* `AlgebraicGeometry.Space.exists_completionSubfunctor_lift_of_isClosedImmersion`: a morphism
  out of the completion of a site object `P` lifts along an étale `π : W₀ ⟶ W` once it lifts on
  a closed subscheme of `P` containing every section with image in the closed subset.
* `AlgebraicGeometry.Space.exists_affine_chart_completion_factorization`: every point of `V`
  over `T` has an affine Noetherian étale neighbourhood on which the restriction of `ŵ` factors
  through an affine étale chart of `W`.

## References

* [Stacks Project, Tag 057R](https://stacks.math.columbia.edu/tag/057R)
* [Stacks Project, Tag 0BTY](https://stacks.math.columbia.edu/tag/0BTY)
* [Stacks Project, Tag 0GI3](https://stacks.math.columbia.edu/tag/0GI3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- A morphism `h₀ : Zo ⟶ V` of site objects has point-set image in the inverse image under
`q : V ⟶ G` of a set `T'` of points exactly when the underlying morphism of schemes maps into the
set of scheme points of `V` corresponding to `q⁻¹ T'`. -/
theorem hasImageIn_yoneda_iff_range_subset {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {V Zo : BigFppfOver B S hS} (q : yoneda.obj V ⟶ G) (T' : Set (points B S hS G))
    (h₀ : Zo ⟶ V) :
    HasImageIn B S hS (yoneda.obj V) (pointsMap B S hS _ q ⁻¹' T') Zo h₀ ↔
      Set.range ((BigFppfOver.toScheme B S hS).map h₀).base ⊆
        pointsToScheme B S hS V '' (pointsMap B S hS _ q ⁻¹' T') := by
  rw [hasImageIn_yoneda_iff]
  constructor
  · rintro h _ ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := surjective_pointsToScheme B S hS Zo x
    refine ⟨pointsMap B S hS _ (yoneda.map h₀) z, ?_,
      pointsToScheme_pointsMap_yoneda B S hS h₀ z⟩
    simpa only [pointsMap_comp, Function.comp_apply, Set.mem_preimage] using h z
  · intro h z
    obtain ⟨w, hw, he⟩ := h ⟨pointsToScheme B S hS Zo z, rfl⟩
    rw [← pointsToScheme_pointsMap_yoneda] at he
    rw [pointsMap_comp, Function.comp_apply, ← injective_pointsToScheme B S hS V he]
    exact hw

/-- The underlying scheme morphism of a morphism of the big fppf category over `S` is compatible
with the structure morphisms. -/
private theorem toScheme_map_comp_inclusion_map_hom {A A' : BigFppfOver B S hS} (f : A ⟶ A') :
    (BigFppfOver.toScheme B S hS).map f ≫ B.inclusion.map A'.hom = B.inclusion.map A.hom :=
  (B.inclusion.map_comp f.left A'.hom).symm.trans (congrArg B.inclusion.map (Over.w f))

/-- Let `π : W₀ ⟶ W` be étale after every representable base change, let `q : P ⟶ X` and let
`ŵ : X_{/T} ⟶ W`. Let `k : E ⟶ P` be a closed immersion through which every section of `P` with
image in `q⁻¹ T` maps set-theoretically, and let `l : E ⟶ W₀` be a morphism over `S` lifting the
value of `ŵ` on every section of `P` factoring through `E`. Then the restriction of `ŵ` to
`P_{/q⁻¹T}` factors through `π`. -/
theorem exists_completionSubfunctor_lift_of_isClosedImmersion
    {X W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {P W₀ : BigFppfOver B S hS}
    (π : yoneda.obj W₀ ⟶ W)
    (hπ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf π)
    (q : yoneda.obj P ⟶ X) (T : Set (points B S hS X))
    (ŵ : (completionSubfunctor B S hS X T).toFunctor ⟶ W ⋙ uliftFunctor.{u + 1})
    {E : Scheme.{u}} (k : E ⟶ (BigFppfOver.toScheme B S hS).obj P)
    [AlgebraicGeometry.IsClosedImmersion k]
    (l : E ⟶ (BigFppfOver.toScheme B S hS).obj W₀)
    (hlS : l ≫ B.inclusion.map W₀.hom = k ≫ B.inclusion.map P.hom)
    (hk : ∀ (Zo : BigFppfOver B S hS) (y : Zo ⟶ P),
      HasImageIn B S hS (yoneda.obj P) (pointsMap B S hS _ q ⁻¹' T) Zo y →
      Set.range ((BigFppfOver.toScheme B S hS).map y).base ⊆ Set.range k.base)
    (hl : ∀ (Zo : BigFppfOver B S hS)
      (s : (completionSubfunctor B S hS (yoneda.obj P)
        (pointsMap B S hS _ q ⁻¹' T)).toFunctor.obj (op Zo))
      (l' : Zo ⟶ W₀) (m : (BigFppfOver.toScheme B S hS).obj Zo ⟶ E),
      m ≫ k = (BigFppfOver.toScheme B S hS).map s.1.down →
      (BigFppfOver.toScheme B S hS).map l' = m ≫ l →
      π.app (op Zo) l' = ((completionMap B S hS q T ≫ ŵ).app (op Zo) s).down) :
    ∃ ŵ₀ : (completionSubfunctor B S hS (yoneda.obj P)
        (pointsMap B S hS _ q ⁻¹' T)).toFunctor ⟶ yoneda.obj W₀ ⋙ uliftFunctor.{u + 1},
      ŵ₀ ≫ Functor.whiskerRight π uliftFunctor.{u + 1} = completionMap B S hS q T ≫ ŵ := by
  classical
  let Tf := BigFppfOver.toScheme B S hS
  have hover := @toScheme_map_comp_inclusion_map_hom B S hS
  let C := completionSubfunctor B S hS (yoneda.obj P) (pointsMap B S hS _ q ⁻¹' T)
  let ŵP := completionMap B S hS q T ≫ ŵ
  let Good : ∀ Zo : BigFppfOver B S hS, C.toFunctor.obj (op Zo) → (Zo ⟶ W₀) → Prop :=
    fun Zo s l₁ => yoneda.map l₁ ≫ π = yonedaEquiv.symm (ŵP.app (op Zo) s).down ∧
      ∀ (Z₁ : BigFppfOver B S hS) (t : Z₁ ⟶ Zo) (m : Tf.obj Z₁ ⟶ E),
        m ≫ k = Tf.map (t ≫ s.1.down) → Tf.map (t ≫ l₁) = m ≫ l
  have key : ∀ (Zo : BigFppfOver B S hS) (s : C.toFunctor.obj (op Zo)),
      ∃ l₁, Good Zo s l₁ ∧ ∀ l₂, Good Zo s l₂ → l₂ = l₁ := by
    intro Zo s
    let y : Zo ⟶ P := s.1.down
    let j := pullback.fst (Tf.map y) k
    have hsurj : Function.Surjective j.base := fun x => by
      show x ∈ Set.range (pullback.fst (Tf.map y) k)
      rw [Scheme.Pullback.range_fst]
      exact hk Zo y s.2 ⟨x, rfl⟩
    let Zo₀ : BigFppfOver B S hS := BigFppfOver.mk B S hS (B.contains_of_mono j Zo.left.2)
      (j ≫ B.inclusion.map Zo.hom)
    let j₀ : Zo₀ ⟶ Zo := Over.homMk (ObjectProperty.homMk j)
      (by apply ObjectProperty.hom_ext; rfl)
    have hj₀ : Tf.map j₀ = j := rfl
    have : AlgebraicGeometry.IsClosedImmersion (Tf.map j₀) :=
      (inferInstance : AlgebraicGeometry.IsClosedImmersion j)
    have : AlgebraicGeometry.UniversalHomeomorphism (Tf.map j₀) :=
      Stacks.Etale.universalHomeomorphism_of_isClosedImmersion_of_surjective _ hsurj
    obtain ⟨l₀, hl₀⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS (X := Zo₀) (Y := W₀)
      (pullback.snd (Tf.map y) k ≫ l) (by
        show (pullback.snd (Tf.map y) k ≫ l) ≫ B.inclusion.map W₀.hom =
          j ≫ B.inclusion.map Zo.hom
        rw [Category.assoc, hlS, ← Category.assoc, ← pullback.condition, Category.assoc,
          hover y])
    have hc : yoneda.map l₀ ≫ π = yoneda.map j₀ ≫ yonedaEquiv.symm (ŵP.app (op Zo) s).down := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_symm_naturality_left,
        Equiv.apply_symm_apply,
        hl Zo₀ (C.toFunctor.map j₀.op s) l₀ (pullback.snd (Tf.map y) k) ?_ hl₀,
        NatTrans.naturality_apply]
      · rfl
      · show pullback.snd (Tf.map y) k ≫ k = Tf.map (j₀ ≫ y)
        rw [Functor.map_comp, hj₀]
        exact pullback.condition.symm
    obtain ⟨l₁, ⟨hl₁π, hl₁j⟩, hl₁u⟩ :=
      existsUnique_lift_of_universalHomeomorphism B S hS π hπ j₀ _ l₀ hc
    refine ⟨l₁, ⟨hl₁π, ?_⟩, ?_⟩
    · intro Z₁ t m hm
      have hcond : Tf.map t ≫ Tf.map y = m ≫ k := by rw [hm, Functor.map_comp]
      obtain ⟨κ, hκ⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS (X := Z₁) (Y := Zo₀)
        (pullback.lift (Tf.map t) m hcond) (by
          show pullback.lift (Tf.map t) m hcond ≫ j ≫ B.inclusion.map Zo.hom = _
          rw [pullback.lift_fst_assoc]
          exact hover t)
      have hκj : κ ≫ j₀ = t := Tf.map_injective (by
        rw [Functor.map_comp, hκ, hj₀]
        exact pullback.lift_fst _ _ _)
      rw [← hκj, Category.assoc, hl₁j, Functor.map_comp, hl₀, hκ]
      exact pullback.lift_snd_assoc (Tf.map t) m hcond l
    · rintro l₂ ⟨hl₂π, hl₂⟩
      refine hl₁u l₂ ⟨hl₂π, Tf.map_injective ?_⟩
      rw [hl₂ Zo₀ j₀ (pullback.snd (Tf.map y) k) ?_, hl₀]
      show pullback.snd (Tf.map y) k ≫ k = Tf.map j₀ ≫ Tf.map y
      rw [hj₀]
      exact pullback.condition.symm
  choose L hL hLu using key
  refine ⟨{ app := fun Zo => ↾fun s => ULift.up (L Zo.unop s)
            naturality := ?_ }, ?_⟩
  · intro Zo Zo' f
    ext s
    apply ULift.ext
    show L Zo'.unop (C.toFunctor.map f s) = f.unop ≫ L Zo.unop s
    symm
    apply hLu
    refine ⟨?_, ?_⟩
    · rw [Functor.map_comp, Category.assoc, (hL _ s).1, yonedaEquiv_symm_naturality_left]
      congr 2
      exact (congrArg ULift.down (NatTrans.naturality_apply ŵP f s)).symm
    · intro Z₁ t m hm
      rw [← Category.assoc]
      exact (hL _ s).2 Z₁ (t ≫ f.unop) m (by rw [hm, Category.assoc]; rfl)
  · ext Zo s
    apply ULift.ext
    show π.app Zo (L Zo.unop s) = (ŵP.app Zo s).down
    have h := congrArg yonedaEquiv (hL Zo.unop s).1
    rwa [yonedaEquiv_comp, yonedaEquiv_yoneda_map, Equiv.apply_symm_apply] at h

/-- Let `W` be an algebraic space, `T ⊆ |X|` closed, `ŵ : X_{/T} ⟶ W`, and `p : V ⟶ X` a morphism
from a locally Noetherian site object. Every point `v` of `V` mapping into `T` lies in the image of
an étale morphism `r : P ⟶ V` with `P` affine and Noetherian, mapping into an affine open `O` of
`S`, such that the restriction of `ŵ` to `P_{/T}` factors as `ŵ₀ ≫ π` through a morphism
`π : W₀ ⟶ W` from an affine site object `W₀` mapping into `O`. -/
theorem exists_affine_chart_completion_factorization
    {X W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    {T : Set (points B S hS X)} (hT : IsClosed T)
    (ŵ : (completionSubfunctor B S hS X T).toFunctor ⟶ W ⋙ uliftFunctor.{u + 1})
    {Va : BigFppfOver B S hS} [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj Va)]
    (p : yoneda.obj Va ⟶ X) (v : points B S hS (yoneda.obj Va))
    (hv : pointsMap B S hS _ p v ∈ T) :
    ∃ (P : BigFppfOver B S hS) (r : P ⟶ Va), Etale ((BigFppfOver.toScheme B S hS).map r) ∧
      pointsToScheme B S hS Va v ∈ Set.range ((BigFppfOver.toScheme B S hS).map r).base ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj P) ∧
      IsNoetherian ((BigFppfOver.toScheme B S hS).obj P) ∧
      ∃ (W₀ : BigFppfOver B S hS) (O : S.Opens), IsAffineOpen O ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj W₀) ∧
        Set.range (B.inclusion.map P.hom).base ⊆ (O : Set S) ∧
        Set.range (B.inclusion.map W₀.hom).base ⊆ (O : Set S) ∧
        ∃ (π : yoneda.obj W₀ ⟶ W)
          (ŵ₀ : (completionSubfunctor B S hS (yoneda.obj P)
            (pointsMap B S hS _ (yoneda.map r ≫ p) ⁻¹' T)).toFunctor ⟶
              yoneda.obj W₀ ⋙ uliftFunctor.{u + 1}),
          ŵ₀ ≫ Functor.whiskerRight π uliftFunctor.{u + 1} =
            completionMap B S hS (yoneda.map r ≫ p) T ≫ ŵ := by
  classical
  let Tf := BigFppfOver.toScheme B S hS
  have hover := @toScheme_map_comp_inclusion_map_hom B S hS
  let TV : Set (Tf.obj Va) := pointsToScheme B S hS Va '' (pointsMap B S hS _ p ⁻¹' T)
  have hTV : IsClosed TV := (isClosed_pointTopology_yoneda_iff_isClosed_image B S hS Va _).1
    (hT.preimage (continuous_pointsMap B S hS p))
  let x₀ : Tf.obj Va := pointsToScheme B S hS Va v
  have hx₀ : x₀ ∈ TV := ⟨v, hv, rfl⟩
  let sV : Tf.obj Va ⟶ S := B.inclusion.map Va.hom
  obtain ⟨O, hO, hsO, -⟩ := exists_isAffineOpen_mem_and_subset (x := sV.base x₀)
    (U := ⊤) trivial
  obtain ⟨V₀, hV₀, hx₀V₀, hV₀O⟩ := exists_isAffineOpen_mem_and_subset (x := x₀)
    (U := sV ⁻¹ᵁ O) hsO
  have : IsAffine V₀ := hV₀
  have hV₀C : B.Contains V₀ := B.contains_of_mono V₀.ι Va.left.2
  let Ws : Set V₀ := V₀.ι.base ⁻¹' TV
  have hWs : IsClosed Ws := hTV.preimage V₀.ι.continuous
  let i : (Scheme.IdealSheafData.vanishingIdeal
      (⟨Ws, hWs⟩ : TopologicalSpace.Closeds V₀)).subscheme ⟶ V₀ :=
    (Scheme.IdealSheafData.vanishingIdeal (⟨Ws, hWs⟩ : TopologicalSpace.Closeds V₀)).subschemeι
  have hirange : Set.range i.base = Ws := by
    show Set.range (Scheme.IdealSheafData.vanishingIdeal
      (⟨Ws, hWs⟩ : TopologicalSpace.Closeds V₀)).subschemeι.base = Ws
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have : AlgebraicGeometry.IsClosedImmersion i := by
    show AlgebraicGeometry.IsClosedImmersion (Scheme.IdealSheafData.vanishingIdeal
      (⟨Ws, hWs⟩ : TopologicalSpace.Closeds V₀)).subschemeι
    infer_instance
  have : IsAffine (Scheme.IdealSheafData.vanishingIdeal
      (⟨Ws, hWs⟩ : TopologicalSpace.Closeds V₀)).subscheme := isAffine_of_isAffineHom i
  have hZC : B.Contains (Scheme.IdealSheafData.vanishingIdeal
      (⟨Ws, hWs⟩ : TopologicalSpace.Closeds V₀)).subscheme :=
    B.contains_of_mono (i ≫ V₀.ι) Va.left.2
  let Zs : BigFppfOver B S hS := BigFppfOver.mk B S hS hZC ((i ≫ V₀.ι) ≫ sV)
  let zV : Zs ⟶ Va := Over.homMk (ObjectProperty.homMk (i ≫ V₀.ι))
    (by apply ObjectProperty.hom_ext; rfl)
  have hzV : Tf.map zV = i ≫ V₀.ι := rfl
  have hzVimg : HasImageIn B S hS (yoneda.obj Va) (pointsMap B S hS _ p ⁻¹' T) Zs zV := by
    rw [hasImageIn_yoneda_iff_range_subset]
    rintro _ ⟨z, rfl⟩
    exact (hirange.subset ⟨z, rfl⟩ : i.base z ∈ Ws)
  let ŵV := completionMap B S hS p T ≫ ŵ
  let sZ : (completionSubfunctor B S hS (yoneda.obj Va)
      (pointsMap B S hS _ p ⁻¹' T)).toFunctor.obj (op Zs) := ⟨ULift.up zV, hzVimg⟩
  let a : yoneda.obj Zs ⟶ W := yonedaEquiv.symm (ŵV.app (op Zs) sZ).down
  obtain ⟨Wa, σ, hσs, hσe⟩ := hW.exists_atlas
  have hrep := hσe.rep
  let Pa := hrep.pullback a
  let snd : Pa ⟶ Zs := hrep.snd a
  obtain ⟨fst, hfst⟩ := yoneda.map_surjective (hrep.fst a)
  have hw : yoneda.map fst ≫ σ = yoneda.map snd ≫ a := by rw [hfst]; exact hrep.w a
  have hsndet : Etale (Tf.map snd) := hσe.property_snd a
  have hsndsurj : Surjective (Tf.map snd) := hσs.property_snd a
  have hx₀' : (⟨x₀, hx₀V₀⟩ : V₀) ∈ Ws := hx₀
  obtain ⟨z₀, hz₀⟩ : (⟨x₀, hx₀V₀⟩ : V₀) ∈ Set.range i.base := hirange.superset hx₀'
  obtain ⟨pa, hpa⟩ := hsndsurj.surj z₀
  let sW : Tf.obj Wa ⟶ S := B.inclusion.map Wa.hom
  have hw₀O : sW.base ((Tf.map fst).base pa) ∈ O := by
    show (Tf.map fst ≫ sW).base pa ∈ O
    rw [hover fst, ← hover snd]
    show sV.base (V₀.ι.base (i.base ((Tf.map snd).base pa))) ∈ O
    rw [hpa, hz₀]
    exact hsO
  obtain ⟨W₀', hW₀', hw₀W₀, hW₀O⟩ := exists_isAffineOpen_mem_and_subset
    (x := (Tf.map fst).base pa) (U := sW ⁻¹ᵁ O) hw₀O
  have : IsAffine W₀' := hW₀'
  have hW₀C : B.Contains W₀' := B.contains_of_mono W₀'.ι Wa.left.2
  let W₀ : BigFppfOver B S hS := BigFppfOver.mk B S hS hW₀C (W₀'.ι ≫ sW)
  let ιW : W₀ ⟶ Wa := Over.homMk (ObjectProperty.homMk W₀'.ι)
    (by apply ObjectProperty.hom_ext; rfl)
  let π : yoneda.obj W₀ ⟶ W := yoneda.map ιW ≫ σ
  have hπ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf π := by
    have h1 := presheaf_yoneda_map B S hS (@AlgebraicGeometry.Etale.{u}) ιW
      (by change Etale W₀'.ι; infer_instance)
    exact MorphismProperty.comp_mem _ _ _ h1 hσe
  obtain ⟨P₁, hP₁, hpaP₁, hP₁W⟩ := exists_isAffineOpen_mem_and_subset
    (x := pa) (U := Tf.map fst ⁻¹ᵁ W₀') hw₀W₀
  have : IsAffine P₁ := hP₁
  let sndZ : Tf.obj Pa ⟶ (Scheme.IdealSheafData.vanishingIdeal
      (⟨Ws, hWs⟩ : TopologicalSpace.Closeds V₀)).subscheme := Tf.map snd
  have : Etale sndZ := hsndet
  let ρ : (P₁ : Scheme.{u}) ⟶ (Scheme.IdealSheafData.vanishingIdeal
      (⟨Ws, hWs⟩ : TopologicalSpace.Closeds V₀)).subscheme := P₁.ι ≫ sndZ
  have : Etale ρ := by change Etale (P₁.ι ≫ sndZ); infer_instance
  obtain ⟨X₁, g, hX₁aff, hget, e, he⟩ := Stacks.Etale.exists_etale_lift_of_isClosedImmersion i ρ
  have hρ : e.inv ≫ P₁.ι ≫ sndZ = pullback.fst i g := e.inv_comp_eq.2 he.symm
  have hX₁C : B.Contains X₁ := size_lt_cutoff_of_isAffine_of_locallyOfFiniteType .fppf B g hV₀C
  let P : BigFppfOver B S hS := BigFppfOver.mk B S hS hX₁C ((g ≫ V₀.ι) ≫ sV)
  let r : P ⟶ Va := Over.homMk (ObjectProperty.homMk (g ≫ V₀.ι))
    (by apply ObjectProperty.hom_ext; rfl)
  have hr : Tf.map r = g ≫ V₀.ι := rfl
  have hstruct : pullback.fst i g ≫ (i ≫ V₀.ι) ≫ sV = pullback.snd i g ≫ (g ≫ V₀.ι) ≫ sV := by
    simp only [Category.assoc, pullback.condition_assoc]
  have hsndS : sndZ ≫ (i ≫ V₀.ι) ≫ sV = B.inclusion.map Pa.hom := hover snd
  have hfstS : Tf.map fst ≫ sW = B.inclusion.map Pa.hom := hover fst
  have hres : (Tf.map fst).resLE W₀' P₁ hP₁W ≫ W₀'.ι = P₁.ι ≫ Tf.map fst :=
    Scheme.Hom.resLE_comp_ι _ _
  let l : pullback i g ⟶ (W₀' : Scheme.{u}) := e.inv ≫ (Tf.map fst).resLE W₀' P₁ hP₁W
  have hlS' : l ≫ W₀'.ι ≫ sW = pullback.snd i g ≫ (g ≫ V₀.ι) ≫ sV := by
    rw [Category.assoc, reassoc_of% hres, hfstS, ← hsndS, reassoc_of% hρ, hstruct]
  have himg : ∀ (Zo : BigFppfOver B S hS) (y : Zo ⟶ P),
      HasImageIn B S hS (yoneda.obj P) (pointsMap B S hS _ (yoneda.map r ≫ p) ⁻¹' T) Zo y →
      HasImageIn B S hS (yoneda.obj Va) (pointsMap B S hS _ p ⁻¹' T) Zo (y ≫ r) := by
    intro Zo y hy
    rw [hasImageIn_yoneda_iff] at hy ⊢
    intro z
    rw [Functor.map_comp, Category.assoc]
    exact hy z
  have hk : ∀ (Zo : BigFppfOver B S hS) (y : Zo ⟶ P),
      HasImageIn B S hS (yoneda.obj P) (pointsMap B S hS _ (yoneda.map r ≫ p) ⁻¹' T) Zo y →
      Set.range ((BigFppfOver.toScheme B S hS).map y).base ⊆ Set.range (pullback.snd i g).base := by
    intro Zo y hy
    have hy' := (hasImageIn_yoneda_iff_range_subset B S hS p T (y ≫ r)).1 (himg Zo y hy)
    rintro _ ⟨x, rfl⟩
    show (Tf.map y).base x ∈ Set.range (pullback.snd i g)
    rw [Scheme.Pullback.range_snd]
    show g.base ((Tf.map y).base x) ∈ Set.range i.base
    rw [hirange]
    exact hy' ⟨x, rfl⟩
  have hŵeq : ∀ (Zo : BigFppfOver B S hS)
      (s₁ : (completionSubfunctor B S hS (yoneda.obj P)
        (pointsMap B S hS _ (yoneda.map r ≫ p) ⁻¹' T)).toFunctor.obj (op Zo))
      (s₂ : (completionSubfunctor B S hS (yoneda.obj Va)
        (pointsMap B S hS _ p ⁻¹' T)).toFunctor.obj (op Zo)),
      s₁.1.down ≫ r = s₂.1.down →
      (completionMap B S hS (yoneda.map r ≫ p) T ≫ ŵ).app (op Zo) s₁ = ŵV.app (op Zo) s₂ := by
    rintro Zo s₁ ⟨⟨y₂⟩, hy₂⟩ h
    change s₁.1.down ≫ r = y₂ at h
    subst h
    rfl
  have hl : ∀ (Zo : BigFppfOver B S hS)
      (s : (completionSubfunctor B S hS (yoneda.obj P)
        (pointsMap B S hS _ (yoneda.map r ≫ p) ⁻¹' T)).toFunctor.obj (op Zo))
      (l' : Zo ⟶ W₀) (m : (BigFppfOver.toScheme B S hS).obj Zo ⟶ pullback i g),
      m ≫ pullback.snd i g = (BigFppfOver.toScheme B S hS).map s.1.down →
      (BigFppfOver.toScheme B S hS).map l' = m ≫ l →
      π.app (op Zo) l' =
        ((completionMap B S hS (yoneda.map r ≫ p) T ≫ ŵ).app (op Zo) s).down := by
    intro Zo s l' m hm hl'
    let yS : Tf.obj Zo ⟶ X₁ := Tf.map s.1.down
    have hm' : m ≫ pullback.snd i g = yS := hm
    have hsS : yS ≫ (g ≫ V₀.ι) ≫ sV = B.inclusion.map Zo.hom := hover s.1.down
    have hnS : (m ≫ e.inv ≫ P₁.ι) ≫ sndZ ≫ (i ≫ V₀.ι) ≫ sV = B.inclusion.map Zo.hom := by
      rw [Category.assoc, Category.assoc, reassoc_of% hρ, hstruct, ← Category.assoc, hm', hsS]
    obtain ⟨n, hn⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS (X := Zo) (Y := Pa)
      (m ≫ e.inv ≫ P₁.ι)
      ((congrArg (fun φ => (m ≫ e.inv ≫ P₁.ι) ≫ φ) hsndS).symm.trans hnS)
    have hfst' : l' ≫ ιW = n ≫ fst := Tf.map_injective (by
      calc Tf.map (l' ≫ ιW) = (m ≫ e.inv ≫ (Tf.map fst).resLE W₀' P₁ hP₁W) ≫ W₀'.ι :=
            (Tf.map_comp l' ιW).trans (congrArg (· ≫ Tf.map ιW) hl')
        _ = (m ≫ e.inv ≫ P₁.ι) ≫ Tf.map fst := by simp only [Category.assoc, hres]
        _ = Tf.map (n ≫ fst) := ((Tf.map_comp n fst).trans (congrArg (· ≫ Tf.map fst) hn)).symm)
    have hsnd' : (n ≫ snd) ≫ zV = s.1.down ≫ r := Tf.map_injective (by
      calc Tf.map ((n ≫ snd) ≫ zV) = ((m ≫ e.inv ≫ P₁.ι) ≫ sndZ) ≫ (i ≫ V₀.ι) :=
            (Tf.map_comp _ _).trans ((congrArg (· ≫ Tf.map zV) (Tf.map_comp n snd)).trans
              (congrArg (fun φ => (φ ≫ Tf.map snd) ≫ Tf.map zV) hn))
        _ = (m ≫ pullback.snd i g) ≫ (g ≫ V₀.ι) := by
          simp only [Category.assoc]
          rw [reassoc_of% hρ, pullback.condition_assoc]
        _ = Tf.map (s.1.down ≫ r) :=
            ((Tf.map_comp _ _).trans (congrArg (· ≫ Tf.map r) hm.symm)).symm)
    calc π.app (op Zo) l' = σ.app (op Zo) (n ≫ fst) := by rw [← hfst']; rfl
      _ = a.app (op Zo) (n ≫ snd) := congrArg (fun φ => φ.app (op Zo) n) hw
      _ = (ŵV.app (op Zo) ((completionSubfunctor B S hS (yoneda.obj Va)
            (pointsMap B S hS _ p ⁻¹' T)).toFunctor.map (n ≫ snd).op sZ)).down := by
          rw [NatTrans.naturality_apply]
          rfl
      _ = _ := (congrArg ULift.down (hŵeq Zo s _ hsnd'.symm)).symm
  let k : pullback i g ⟶ (BigFppfOver.toScheme B S hS).obj P := pullback.snd i g
  have : AlgebraicGeometry.IsClosedImmersion k :=
    (inferInstance : AlgebraicGeometry.IsClosedImmersion (pullback.snd i g))
  obtain ⟨ŵ₀, hŵ₀⟩ := exists_completionSubfunctor_lift_of_isClosedImmersion B S hS π hπ
    (yoneda.map r ≫ p) T ŵ k l hlS' hk hl
  refine ⟨P, r, (inferInstance : Etale (g ≫ V₀.ι)),
    ⟨(pullback.snd i g).base (e.hom.base ⟨pa, hpaP₁⟩), ?_⟩, hX₁aff, ?_, W₀, O, hO, hW₀', ?_, ?_,
    π, ŵ₀, hŵ₀⟩
  · have hkey : e.hom ≫ pullback.snd i g ≫ (g ≫ V₀.ι) = (P₁.ι ≫ sndZ) ≫ i ≫ V₀.ι := by
      rw [← pullback.condition_assoc, reassoc_of% he]
    calc (Tf.map r).base ((pullback.snd i g).base (e.hom.base ⟨pa, hpaP₁⟩))
        = (e.hom ≫ pullback.snd i g ≫ (g ≫ V₀.ι)).base ⟨pa, hpaP₁⟩ := rfl
      _ = ((P₁.ι ≫ sndZ) ≫ i ≫ V₀.ι).base ⟨pa, hpaP₁⟩ := by rw [hkey]
      _ = V₀.ι.base (i.base (sndZ.base pa)) := rfl
      _ = x₀ := by
        have hpa' : sndZ.base pa = z₀ := hpa
        rw [hpa', hz₀]
        rfl
  · have : IsLocallyNoetherian X₁ := LocallyOfFiniteType.isLocallyNoetherian g
    show IsNoetherian X₁
    exact { }
  · rintro _ ⟨x, rfl⟩
    exact hV₀O (g.base x).2
  · rintro _ ⟨x, rfl⟩
    exact hW₀O x.2

end Space

end AlgebraicGeometry

end
