module

public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.AlgebraicGeometry.Sites.Representability
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.WalkingPair
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductInclusion
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SiteQuasiCompact

/-!
# The diagonal of an affine formal algebraic space (Stacks 0AI8)

Let `X` be the colimit, among the fppf sheaves over a scheme `S` in a big fppf site `B`, of a
nonempty directed diagram of affine schemes over `S` whose transition morphisms are thickenings.
**Stacks 0AI8** says that the diagonal `X ⟶ X ⨯ X` is representable by schemes and that each of
its base changes along a represented sheaf is a closed immersion of schemes — the relative
morphism property `AlgebraicGeometry.FormalSpace.IsClosedImmersionInto` applied to `diag X`.

The Stacks proof is the following chain, and it is the chain run here. Testing the diagonal against
a representable sheaf amounts to testing a *pair* of morphisms `f, g : U ⟶ X` out of a single
object of the site, and the base change of the diagonal along `prod.lift f g` is their equalizer.
Over an affine `U` such a morphism factors through one stage of the presentation, because an affine
object of the site is quasi-compact and the transition morphisms are monomorphisms (a thickening is
a closed immersion, hence a monomorphism, and `Sheaf.sheafifiedYoneda` preserves monomorphisms of
the site), so the colimit of sections over `U` is the colimit of the sections of the stages; a pair
of morphisms then factors through a *common* stage by directedness. At that stage the equalizer is
the base change of the diagonal of an affine scheme over `S`, which is a closed immersion since an
affine scheme is separated, and the stage inclusion into `X` is a monomorphism, so the equalizer
over `X` agrees with the equalizer over the stage. A general object of the site is covered by its
affine opens; the resulting closed subschemes are glued with
`AlgebraicGeometry.Scheme.Cover.RelativeGluingData` over the directed affine cover of `U`, and a
morphism of schemes that is a closed immersion over each member of an open cover of its target is a
closed immersion.

## Main results

* `AlgebraicGeometry.FormalSpace.diagonal_isClosedImmersion`: **Stacks 0AI8**.
* `AlgebraicGeometry.FormalSpace.stageTransition_mono_sheafifiedYoneda`: a transition morphism
  of the presentation is a monomorphism of sheaves.
* `AlgebraicGeometry.FormalSpace.pair_maps_factor_through_common_stage_for_two_affines`: two
  scheme-valued points of the colimit taken at affine objects of the site factor through one
  common stage of the presentation.

## Implementation notes

The presentation enters as an explicit diagram together with an isomorphism of its colimit with
`X`, rather than through `AlgebraicGeometry.FormalSpace.IsAffineFormalAlgebraicSpace`: the
set-theoretic condition of Stacks 0AIS is not used, and Stacks 0AIS is in turn deduced from this
result, so stating the hypothesis as affineness of the formal algebraic space would be circular.

The private helpers of this file duplicate, at file scope, a block of helpers that
`StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealPresentation` also declares privately
(`Space.exists_covering_refining_sieve` and the two `isQuasiCompactObject_…_of_compact_scheme`).
They are private there, hence not importable; promoting them is a refactor of that file rather
than part of this result.

Subcanonicity of the two topologies is *not* reproved:
`AlgebraicGeometry.BigFppfSite.subcanonical_topology` and
`AlgebraicGeometry.bigFppfOver_subcanonical` are in the library and are used directly.

## References

* [Stacks Project, Tag 0AI8](https://stacks.math.columbia.edu/tag/0AI8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u v w w₁ w₂


private theorem relatively_glued_closedImmersion
    {S : Scheme.{u}} (𝒰 : Scheme.OpenCover S)
    [Category 𝒰.I₀] [𝒰.LocallyDirected]
    (d : Scheme.Cover.RelativeGluingData 𝒰)
    [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]
    (h : ∀ i, IsClosedImmersion (d.natTrans.app i)) :
    IsClosedImmersion d.toBase := by
  apply IsZariskiLocalAtTarget.of_openCover 𝒰
  intro i
  have hp := d.isPullback_natTrans_ι_toBase i
  let e := hp.isoPullback ≪≫ pullbackSymmetry (𝒰.f i) d.toBase
  have hArrow : Arrow.mk (pullback.snd d.toBase (𝒰.f i)) ≅
      Arrow.mk (d.natTrans.app i) := by
    refine Arrow.isoMk e.symm (Iso.refl _) ?_
    refine Eq.trans ?_ (Category.comp_id (pullback.snd d.toBase (𝒰.f i))).symm
    exact (congrArg ((pullbackSymmetry (𝒰.f i) d.toBase).inv ≫ ·)
      hp.isoPullback_inv_fst).trans (pullbackSymmetry_inv_comp_fst _ _)
  exact (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion hArrow).2 (h i)

private theorem affine_source_diagonal_isClosedImmersion {T S : Scheme.{u}}
    (f : T ⟶ S) [IsAffine T] :
    IsClosedImmersion (pullback.diagonal f) := by
  let : T.IsSeparated := inferInstance
  let : IsSeparated f := inferInstance
  infer_instance

private theorem stageTransition_mono_sheafifiedYoneda
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type (u + 1)} [Preorder I]
    (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening
        ((BigAffineFppf.toScheme B S hS).map (D.map f)))
    {i j : I} (f : i ⟶ j) :
    Mono ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
      ((BigAffineFppf.inclusion B S hS).map (D.map f))) := by
  let J := BigFppfOver.topology B S hS
  let q := BigFppfOver.toScheme B S hS
  let g := (BigAffineFppf.inclusion B S hS).map (D.map f)
  have hm : Mono (q.map g) := by
    have : IsClosedImmersion (q.map g) := (hD f).1
    infer_instance
  exact Sheaf.mono_sheafifiedYoneda_map_of_mono_underlying J q g hm

/-- A transition morphism of a presentation of an affine formal algebraic space becomes a
monomorphism of sheaves: a thickening is a closed immersion, hence a monomorphism of schemes,
and the structure functor of the big fppf site of `S` is faithful. -/
alias stageTransition_mono_sheafifiedYoneda' := stageTransition_mono_sheafifiedYoneda

private theorem map_factors_through_stage_of_affine
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening
        ((BigAffineFppf.toScheme B S hS).map (D.map f)))
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (e : colimit
      (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda
          (BigFppfOver.topology B S hS)) ≅ X)
    (U : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (g : (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).obj U ⟶ X) :
    ∃ i : I, ∃ g' : (Sheaf.sheafifiedYoneda
        (BigFppfOver.topology B S hS)).obj U ⟶
        (Sheaf.sheafifiedYoneda
          (BigFppfOver.topology B S hS)).obj
          ((BigAffineFppf.inclusion B S hS).obj (D.obj i)),
      g' ≫ colimit.ι
        (D ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda
            (BigFppfOver.topology B S hS)) i ≫ e.hom = g := by
  classical
  let J := BigFppfOver.topology B S hS
  let F := D ⋙ BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda J
  have htrans : ∀ i j (f : i ⟶ j), Mono (F.map f) :=
    fun _ _ f => stageTransition_mono_sheafifiedYoneda B S hS D hD f
  let G := (sheafSections J (Type (u + 1))).obj (op U)
  let α : (Sheaf.sheafifiedYoneda J).obj U ⟶ colimit F := g ≫ e.inv
  have hUqc : J.IsQuasiCompactObject U :=
    AlgebraicGeometry.FormalSpace.isQuasiCompactObject_over_of_compact_scheme B S hS U
  have hbij : Function.Bijective (colimit.post F G) :=
    (Sheaf.injective_and_bijective_colimit_post_sheafSections J F U).2.2.1 hUqc htrans
  let s := (Sheaf.sectionEquiv J) α
  obtain ⟨z, hz⟩ := hbij.2 s
  let Fsec := F ⋙ G
  obtain ⟨i, x, hx⟩ := Concrete.isColimit_exists_rep Fsec (colimit.isColimit Fsec) z
  let g' : (Sheaf.sheafifiedYoneda J).obj U ⟶ F.obj i :=
    (Sheaf.sectionEquiv J).symm x
  have hpost (x : (F.obj i).obj.obj (op U)) :
      colimit.post F G (colimit.ι Fsec i x) = (colimit.ι F i).hom.app (op U) x :=
    ConcreteCategory.congr_hom (colimit.ι_post F G i) x
  have hgi : g' ≫ colimit.ι F i = α := by
    apply (Sheaf.sectionEquiv J).injective
    calc
      (Sheaf.sectionEquiv J) (g' ≫ colimit.ι F i) = (colimit.ι F i).hom.app (op U) x := by
        rw [Sheaf.sectionEquiv_comp]
        change (colimit.ι F i).hom.app (op U)
          ((Sheaf.sectionEquiv J) ((Sheaf.sectionEquiv J).symm x)) = _
        exact congrArg ((colimit.ι F i).hom.app (op U))
          ((Sheaf.sectionEquiv J).apply_symm_apply x)
      _ = colimit.post F G (colimit.ι Fsec i x) := (hpost x).symm
      _ = colimit.post F G z := congrArg (colimit.post F G) hx
      _ = s := hz
      _ = (Sheaf.sectionEquiv J) α := rfl
  refine ⟨i, g', ?_⟩
  rw [← Category.assoc, hgi]
  change (g ≫ e.inv) ≫ e.hom = g
  rw [Category.assoc, e.inv_hom_id, Category.comp_id]

private theorem pair_maps_factor_through_common_stage_for_two_affines
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening
        ((BigAffineFppf.toScheme B S hS).map (D.map f)))
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (e : colimit
      (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda
          (BigFppfOver.topology B S hS)) ≅ X)
    (U V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (f : (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).obj U ⟶ X)
    (g : (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).obj V ⟶ X) :
    ∃ i : I, ∃ f' : (Sheaf.sheafifiedYoneda
        (BigFppfOver.topology B S hS)).obj U ⟶
        (Sheaf.sheafifiedYoneda
          (BigFppfOver.topology B S hS)).obj
          ((BigAffineFppf.inclusion B S hS).obj (D.obj i)),
      ∃ g' : (Sheaf.sheafifiedYoneda
        (BigFppfOver.topology B S hS)).obj V ⟶
        (Sheaf.sheafifiedYoneda
          (BigFppfOver.topology B S hS)).obj
          ((BigAffineFppf.inclusion B S hS).obj (D.obj i)),
      f' ≫ colimit.ι
        (D ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda
            (BigFppfOver.topology B S hS)) i ≫ e.hom = f ∧
      g' ≫ colimit.ι
        (D ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda
            (BigFppfOver.topology B S hS)) i ≫ e.hom = g := by
  obtain ⟨i, f', hf⟩ := map_factors_through_stage_of_affine B S hS D hD X e U f
  obtain ⟨j, g', hg⟩ := map_factors_through_stage_of_affine B S hS D hD X e V g
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  let K := D ⋙ BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let α := (BigAffineFppf.inclusion B S hS).map
    (D.map (homOfLE hik))
  let β := (BigAffineFppf.inclusion B S hS).map
    (D.map (homOfLE hjk))
  have hι₁ : (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).map α ≫ colimit.ι K k =
      colimit.ι K i :=
    colimit.w K (homOfLE hik)
  have hι₂ : (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).map β ≫ colimit.ι K k =
      colimit.ι K j :=
    colimit.w K (homOfLE hjk)
  refine ⟨k, f' ≫ (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).map α,
    g' ≫ (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).map β, ?_, ?_⟩
  · exact (congrArg (fun t => f' ≫ t ≫ e.hom) hι₁).trans hf
  · exact (congrArg (fun t => g' ≫ t ≫ e.hom) hι₂).trans hg

/-- Two scheme-valued points of a nonempty directed colimit of representable sheaves, taken at
affine objects `U` and `V` of the site and with the transition morphisms of the diagram
thickenings, factor through one common stage: an affine object of the site is quasi-compact, so
each point factors through some stage, and directedness takes the two stages to a common one. -/
alias pair_maps_factor_through_common_stage_for_two_affines' :=
  pair_maps_factor_through_common_stage_for_two_affines

/-- A map into `T` composed with the diagonal is a pair map exactly when it equals both
components. -/
private theorem comp_diag_eq_comp_prod_lift_iff
    {C : Type u} [Category.{v} C] [HasBinaryProducts C]
    {P T U : C} {x : P ⟶ T} {y : P ⟶ U} {a b : U ⟶ T} :
    x ≫ Limits.diag T = y ≫ Limits.prod.lift a b ↔ x = y ≫ a ∧ x = y ≫ b := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ?_⟩
  · simpa using congrArg (fun k => k ≫ Limits.prod.fst) h
  · simpa using congrArg (fun k => k ≫ Limits.prod.snd) h
  · obtain ⟨rfl, h⟩ := h
    apply Limits.prod.hom_ext <;> simp [h]

private theorem postcompose_diagonal_mono
    {C : Type u} [Category.{v} C] [HasBinaryProducts C]
    {P T X U : C} (fst : P ⟶ T) (snd : P ⟶ U)
    (a b : U ⟶ T)
    (hp : IsPullback fst snd (Limits.diag T) (Limits.prod.lift a b))
    (m : T ⟶ X) [Mono m] :
    IsPullback (fst ≫ m) snd (Limits.diag X)
      (Limits.prod.lift (a ≫ m) (b ≫ m)) := by
  obtain ⟨h₁, h₂⟩ := comp_diag_eq_comp_prod_lift_iff.1 hp.w
  have w : (fst ≫ m) ≫ Limits.diag X =
      snd ≫ Limits.prod.lift (a ≫ m) (b ≫ m) :=
    comp_diag_eq_comp_prod_lift_iff.2 ⟨by simp [h₁], by simp [h₂]⟩
  have hs (s : PullbackCone (Limits.diag X) (Limits.prod.lift (a ≫ m) (b ≫ m))) :
      s.fst = s.snd ≫ a ≫ m ∧ s.fst = s.snd ≫ b ≫ m :=
    comp_diag_eq_comp_prod_lift_iff.1 s.condition
  have compat (s : PullbackCone (Limits.diag X)
      (Limits.prod.lift (a ≫ m) (b ≫ m))) : s.snd ≫ a = s.snd ≫ b :=
    (cancel_mono m).1 (by simpa using (hs s).1.symm.trans (hs s).2)
  have stageCompat (s : PullbackCone (Limits.diag X)
      (Limits.prod.lift (a ≫ m) (b ≫ m))) :
      (s.snd ≫ a) ≫ Limits.diag T = s.snd ≫ Limits.prod.lift a b :=
    comp_diag_eq_comp_prod_lift_iff.2 ⟨rfl, compat s⟩
  let lift (s : PullbackCone (Limits.diag X)
      (Limits.prod.lift (a ≫ m) (b ≫ m))) :=
    hp.lift (s.snd ≫ a) s.snd (stageCompat s)
  have hfac (s : PullbackCone (Limits.diag X) (Limits.prod.lift (a ≫ m) (b ≫ m))) :
      lift s ≫ fst ≫ m = s.fst := by
    rw [(hs s).1]
    simp [lift]
  have hlim : IsLimit (PullbackCone.mk (fst ≫ m) snd w) :=
    PullbackCone.IsLimit.mk w lift hfac (fun s => by simp [lift])
      (fun s l hl₁ hl₂ => hp.hom_ext
        ((cancel_mono m).1 (by simp only [Category.assoc, hl₁, hfac]))
        (by rw [hl₂]; simp [lift]))
  exact IsPullback.of_isLimit hlim

private theorem affine_test_pair_has_closed_equalizer
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening
        ((BigAffineFppf.toScheme B S hS).map (D.map f)))
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (e : colimit
      (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) ≅ X)
    (U : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (f g : (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).obj U ⟶ X) :
    ∃ V : BigFppfOver B S hS, ∃ p : V ⟶ U,
      IsClosedImmersion
        ((BigFppfOver.toScheme B S hS).map p) ∧
      ∃ a : (Sheaf.sheafifiedYoneda
        (BigFppfOver.topology B S hS)).obj V ⟶ X,
        IsPullback a
          ((Sheaf.sheafifiedYoneda
            (BigFppfOver.topology B S hS)).map p)
          (Limits.diag X) (Limits.prod.lift f g) := by
  classical
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  let q := BigFppfOver.toScheme B S hS
  let K := D ⋙ BigAffineFppf.inclusion B S hS ⋙ F
  have htrans : ∀ i j (t : i ⟶ j), Mono (K.map t) :=
    fun _ _ t => stageTransition_mono_sheafifiedYoneda B S hS D hD t
  obtain ⟨i, f', g', hf', hg'⟩ :=
    pair_maps_factor_through_common_stage_for_two_affines B S hS D hD X e U U f g
  let T := (BigAffineFppf.inclusion B S hS).obj (D.obj i)
  let : Mono (colimit.ι K i) := Sheaf.mono_colimit_ι_of_mono_transition K htrans i
  let m : F.obj T ⟶ X := colimit.ι K i ≫ e.hom
  have : Mono m := by dsimp [m]; infer_instance
  let : HasPullbacks (BigFppfOver B S hS) := inferInstance
  let : HasBinaryProducts (BigFppfOver B S hS) :=
    Over.ConstructProducts.over_binaryProduct_of_pullback
  let : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let eH : J.uliftYoneda.{u + 1} ≅ F :=
    (Functor.isoWhiskerLeft J.uliftYoneda
      (sheafificationNatIso.{u, u + 1, u + 1, u + 2} J (Type (u + 1)))) ≪≫
      Functor.isoWhiskerRight J.uliftYonedaCompSheafToPresheaf
        (presheafToSheaf J (Type (u + 1)))
  have : PreservesLimitsOfShape WalkingCospan F := preservesLimitsOfShape_of_natIso eH
  have : PreservesLimitsOfShape (Discrete WalkingPair) F := preservesLimitsOfShape_of_natIso eH
  let : F.Full := Sheaf.sheafifiedYoneda_full J
  let α : U ⟶ T := F.preimage f'
  let β : U ⟶ T := F.preimage g'
  have hα : F.map α = f' := F.map_preimage f'
  have hβ : F.map β = g' := F.map_preimage g'
  let d : T ⟶ T ⨯ T := Limits.diag T
  let pairMap : U ⟶ T ⨯ T := Limits.prod.lift α β
  let V := Limits.pullback d pairMap
  let p : V ⟶ U := Limits.pullback.snd d pairMap
  have hp : IsPullback (F.map (Limits.pullback.fst d pairMap))
      (F.map (Limits.pullback.snd d pairMap)) (Limits.diag (F.obj T))
      (Limits.prod.lift (F.map α) (F.map β)) :=
    ((IsPullback.of_hasPullback d pairMap).map F).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (PreservesLimitPair.iso F T T) (by simp) (by simp)
      (by apply Limits.prod.hom_ext <;> simp [d, ← Functor.map_comp])
      (by apply Limits.prod.hom_ext <;> simp [pairMap, ← Functor.map_comp])
  have hαX : F.map α ≫ m = f := by
    rw [hα]
    exact hf'
  have hβX : F.map β ≫ m = g := by
    rw [hβ]
    exact hg'
  have hpX' : IsPullback
      (F.map (Limits.pullback.fst d pairMap) ≫ m)
      (F.map (Limits.pullback.snd d pairMap)) (Limits.diag X)
      (Limits.prod.lift f g) := by
    simpa [hαX, hβX] using postcompose_diagonal_mono _ _ _ _ hp m
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := by
    change IsAffine ((BigAffineFppf.toScheme B S hS).obj (D.obj i))
    infer_instance
  have hd : IsClosedImmersion (q.map d) := by
    let τ := terminal.from T
    have hdiagOver : d = pullback.diagonal τ ≫ (prodIsoPullback T T).inv := by
      apply Limits.prod.hom_ext <;> simp [d, τ]
    have hq := Functor.map_isPullback q (pullback.diagonal_isKernelPair τ)
    have hArrow : Arrow.mk (q.map (pullback.diagonal τ)) ≅
        Arrow.mk (pullback.diagonal (q.map τ)) := by
      refine Arrow.isoMk (Iso.refl _) hq.isoPullback ?_
      apply pullback.hom_ext <;> simp [← Functor.map_comp]
    have : IsClosedImmersion (q.map (pullback.diagonal τ)) :=
      (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion hArrow).2
        (affine_source_diagonal_isClosedImmersion (q.map τ))
    have : IsIso (q.map (prodIsoPullback T T).inv) := Functor.map_isIso q _
    rw [hdiagOver, q.map_comp]
    infer_instance
  have hclosed : IsClosedImmersion (q.map p) := by
    have hpbq : IsPullback (q.map (Limits.pullback.fst d pairMap))
        (q.map (Limits.pullback.snd d pairMap)) (q.map d) (q.map pairMap) :=
      (IsPullback.of_hasPullback d pairMap).map q
    dsimp [p, V]
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hpbq hd
  exact ⟨V, p, hclosed,
    F.map (Limits.pullback.fst d pairMap) ≫ m, hpX'⟩

private theorem open_family_mem_topology
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U : BigFppfOver B S hS} {ι : Type (u + 1)}
    {V : ι → BigFppfOver B S hS} (f : ∀ i, V i ⟶ U)
    (ho : ∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (f i)))
    (hs : ∀ x : (BigFppfOver.toScheme B S hS).obj U,
      ∃ i y, ((BigFppfOver.toScheme B S hS).map (f i)) y = x) :
    Sieve.ofArrows V f ∈ BigFppfOver.topology B S hS U := by
  let E : PreZeroHypercover U.left := ⟨ι, fun i => (V i).left, fun i => (f i).left⟩
  have hE : IsFppfCovering ⟨U.left, E⟩ := by
    have hfppf : (E.map B.inclusion).presieve₀ ∈ Scheme.fppfPrecoverage _ := by
      apply (Scheme.presieve₀_mem_precoverage_iff _).2
      refine ⟨hs, ?_⟩
      intro i
      have : IsOpenImmersion ((E.map B.inclusion).f i) := ho i
      exact ⟨inferInstance, inferInstance⟩
    simpa [IsFppfCovering, Scheme.fppfPrecoverage,
      PreZeroHypercover.presieve₀_map] using hfppf
  obtain ⟨⟨T, E'⟩, hE', heq⟩ := B.fppf_has_representative ⟨U.left, E⟩ hE
  obtain ⟨hT, heq⟩ := heq
  dsimp at hT
  subst T
  have hpre : E.presieve₀ = E'.presieve₀ :=
    PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent heq
  have hmem : E.sieve₀ ∈ B.topology U.left := by
    change Sieve.generate E.presieve₀ ∈ _
    rw [hpre]
    exact Precoverage.generate_mem_toGrothendieck (show E'.presieve₀ ∈ B.precoverage _
      from ⟨E', rfl, hE'⟩)
  rw [BigFppfOver.topology, GrothendieckTopology.mem_over_iff,
    Sieve.overEquiv_ofArrows]
  exact hmem

private theorem sheafifiedYoneda_hom_ext_open_family
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U : BigFppfOver B S hS} {ι : Type u}
    {V : ι → BigFppfOver B S hS} (f : ∀ i, V i ⟶ U)
    (ho : ∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (f i)))
    (hs : ∀ x : (BigFppfOver.toScheme B S hS).obj U,
      ∃ i y, ((BigFppfOver.toScheme B S hS).map (f i)) y = x)
    {Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    {a b : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ Y}
    (h : ∀ i, (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
      (f i) ≫ a = (Sheaf.sheafifiedYoneda
        (BigFppfOver.topology B S hS)).map (f i) ≫ b) : a = b := by
  let J := BigFppfOver.topology B S hS
  apply (Sheaf.sectionEquiv J).injective
  let x : PUnit.{u + 2} ⟶ Y.obj.obj (op U) := ↾fun _ => Sheaf.sectionEquiv J a
  let y : PUnit.{u + 2} ⟶ Y.obj.obj (op U) := ↾fun _ => Sheaf.sectionEquiv J b
  have hxy : x = y := Y.property.hom_ext_ofArrows (fun i : ULift.{u + 1} ι => f i.down)
    (open_family_mem_topology B S hS (fun i : ULift.{u + 1} ι => f i.down) (fun i => ho i.down)
      (fun x => by
        obtain ⟨i, z, hz⟩ := hs x
        exact ⟨⟨i⟩, z, hz⟩)) (fun i => by
      ext z
      change Y.obj.map (f i.down).op (Sheaf.sectionEquiv J a) =
        Y.obj.map (f i.down).op (Sheaf.sectionEquiv J b)
      rw [← Sheaf.sectionEquiv_map_comp, ← Sheaf.sectionEquiv_map_comp, h i.down])
  exact ConcreteCategory.congr_hom hxy PUnit.unit

private theorem sheaf_hom_ext_yoneda
    {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    {X Y : Sheaf J (Type (max v w))} {f g : X ⟶ Y}
    (h : ∀ (T : C) (a : (Sheaf.sheafifiedYoneda J).obj T ⟶ X), a ≫ f = a ≫ g) :
    f = g := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.hom_ext
  intro x
  have hx := congrArg (Sheaf.sectionEquiv J)
    (h T.unop ((Sheaf.sectionEquiv J).symm x))
  simpa only [Sheaf.sectionEquiv_comp, Equiv.apply_symm_apply] using hx

@[implicit_reducible]
private def openOver (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (U : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk (O.ι ≫ B.inclusion.map U.hom) :
    B.obj (Scheme.size_lt_of_isOpenImmersion O.ι U.left.property) ⟶ B.obj hS)

@[implicit_reducible]
private def openOverι (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (U : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    openOver B S hS U O ⟶ U :=
  Over.homMk (ObjectProperty.homMk O.ι)

@[implicit_reducible]
private noncomputable def affineOpenDiagram (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (U : BigFppfOver B S hS) :
    ((BigFppfOver.toScheme B S hS).obj U).affineOpens ⥤
      BigFppfOver B S hS where
  obj i := openOver B S hS U i.1
  map {i j} t := Over.homMk (ObjectProperty.homMk
    (((BigFppfOver.toScheme B S hS).obj U).homOfLE (leOfHom t)))
    (by ext : 1; simp [openOver, Scheme.homOfLE])
  map_id i := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    change ((BigFppfOver.toScheme B S hS).obj U).homOfLE (le_refl i.1) = 𝟙 _
    apply (cancel_mono i.1.ι).1
    simp [Scheme.homOfLE]
  map_comp {i j k} f g := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    change ((BigFppfOver.toScheme B S hS).obj U).homOfLE (leOfHom (f ≫ g)) =
      ((BigFppfOver.toScheme B S hS).obj U).homOfLE (leOfHom f) ≫
      ((BigFppfOver.toScheme B S hS).obj U).homOfLE (leOfHom g)
    apply (cancel_mono k.1.ι).1
    simp [Scheme.homOfLE]

private theorem affineOpenDiagram_map_ι
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    {i j : ((BigFppfOver.toScheme B S hS).obj U).affineOpens} (t : i ⟶ j) :
    (affineOpenDiagram B S hS U).map t ≫ openOverι B S hS U j.1 =
      openOverι B S hS U i.1 := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  change ((BigFppfOver.toScheme B S hS).obj U).homOfLE (leOfHom t) ≫ j.1.ι = i.1.ι
  simp [Scheme.homOfLE]

private theorem exists_closed_gluing
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    (E : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (y : E ⟶ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U)
    (V : ((BigFppfOver.toScheme B S hS).obj U).affineOpens →
      BigFppfOver B S hS)
    (p : ∀ i, V i ⟶ (affineOpenDiagram B S hS U).obj i)
    (a : ∀ i, (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).obj (V i) ⟶ E)
    (hc : ∀ i, IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (p i)))
    (hp : ∀ i, IsPullback (a i)
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (p i)) y
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        (openOverι B S hS U i.1))) :
    ∃ (W : BigFppfOver B S hS) (f : W ⟶ U),
      IsClosedImmersion ((BigFppfOver.toScheme B S hS).map f) ∧
      ∃ c : ∀ i, V i ⟶ W,
        (∀ i, c i ≫ f = p i ≫ openOverι B S hS U i.1) ∧
        (∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (c i))) ∧
        (∀ x : (BigFppfOver.toScheme B S hS).obj W,
          ∃ i z, ((BigFppfOver.toScheme B S hS).map (c i)) z = x) := by
  classical
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  let q := BigFppfOver.toScheme B S hS
  let A := affineOpenDiagram B S hS U
  let ui := fun i : (q.obj U).affineOpens => openOverι B S hS U i.1
  let : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let : F.Full := Sheaf.sheafifiedYoneda_full J
  let : F.Faithful := Sheaf.sheafifiedYoneda_faithful J
  have : ∀ i, Mono (p i) := fun i => by
    have := hc i
    exact Functor.mono_of_mono_map q inferInstance
  have hui {i j} (t : i ⟶ j) : A.map t ≫ ui j = ui i :=
    affineOpenDiagram_map_ι B S hS U t
  have compat {i j} (t : i ⟶ j) :
      a i ≫ y = (F.map (p i) ≫ F.map (A.map t)) ≫ F.map (ui j) := by
    rw [(hp i).w, Category.assoc, ← F.map_comp (A.map t) (ui j), hui]
  let r {i j} (t : i ⟶ j) : V i ⟶ V j :=
    F.preimage ((hp j).lift (a i) (F.map (p i) ≫ F.map (A.map t)) (compat t))
  have hr {i j} (t : i ⟶ j) :
      F.map (r t) = (hp j).lift (a i) (F.map (p i) ≫ F.map (A.map t)) (compat t) :=
    F.map_preimage _
  have hrp {i j} (t : i ⟶ j) : r t ≫ p j = p i ≫ A.map t := by
    apply F.map_injective
    rw [F.map_comp, hr, (hp j).lift_snd, F.map_comp]
  have hra {i j} (t : i ⟶ j) : F.map (r t) ≫ a j = a i := by
    rw [hr, (hp j).lift_fst]
  let G : (q.obj U).affineOpens ⥤ BigFppfOver B S hS := {
    obj := V
    map := r
    map_id := fun i => by
      apply (cancel_mono (p i)).1
      rw [hrp, A.map_id, Category.id_comp, Category.comp_id]
    map_comp := fun t t' => by
      apply (cancel_mono (p _)).1
      rw [hrp, Category.assoc, hrp, ← Category.assoc, hrp, Category.assoc, A.map_comp] }
  have hpb {i j} (t : i ⟶ j) : IsPullback (r t) (p i) (p j) (A.map t) := by
    apply IsPullback.of_map_of_faithful F
    apply IsPullback.of_right (h₁₂ := a j) (h₂₂ := F.map (ui j))
    · simpa only [hra, ← F.map_comp, hui] using hp i
    · rw [← F.map_comp, hrp, F.map_comp]
    · exact hp j
  let 𝒰 := (q.obj U).directedAffineCover
  let d : Scheme.Cover.RelativeGluingData 𝒰 := {
    functor := G ⋙ q
    natTrans := {
      app i := q.map (p i)
      naturality := fun i j t => by
        change q.map (r t) ≫ q.map (p j) = q.map (p i) ≫ q.map (A.map t)
        simp only [← q.map_comp]
        exact congrArg q.map (hrp t) }
    equifibered := fun i j t => (hpb t).map q }
  let : Small.{u} 𝒰.I₀ := inferInstanceAs (Small.{u} (q.obj U).affineOpens)
  let : Quiver.IsThin 𝒰.I₀ := inferInstance
  let : ∀ {i j : 𝒰.I₀} (t : i ⟶ j), IsOpenImmersion (d.functor.map t) :=
    fun {i j} t => MorphismProperty.of_isPullback (d.equifibered t).flip (by infer_instance)
  let : (d.functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.isLocallyDirected_of_equifibered_of_injective d.natTrans d.equifibered
      (by intro i j t; exact (d.functor.map t).injective)
  have : IsClosedImmersion d.toBase := relatively_glued_closedImmersion 𝒰 d hc
  let W₀ : B.Schemes := B.obj (Scheme.size_lt_of_isClosedImmersion d.toBase U.left.property)
  let f₀ : W₀ ⟶ U.left := ObjectProperty.homMk d.toBase
  let W : BigFppfOver B S hS := Over.mk (f₀ ≫ U.hom)
  let f : W ⟶ U := Over.homMk f₀
  let c (i : (q.obj U).affineOpens) : V i ⟶ W :=
    Over.homMk (ObjectProperty.homMk (colimit.ι d.functor i)) (by
      apply B.inclusion.map_injective
      change colimit.ι d.functor i ≫ (d.toBase ≫ B.inclusion.map U.hom) =
        B.inclusion.map (V i).hom
      refine (Category.assoc _ _ _).symm.trans
        ((congrArg (fun t => t ≫ B.inclusion.map U.hom) (d.ι_toBase i)).trans
          ((Category.assoc _ _ _).trans ?_))
      change q.map (p i) ≫ q.map (ui i) ≫ B.inclusion.map U.hom = _
      change B.inclusion.map (p i).left ≫ B.inclusion.map (ui i).left ≫
        B.inclusion.map U.hom = _
      rw [← B.inclusion.map_comp (ui i).left U.hom, (ui i).w,
        ← B.inclusion.map_comp]
      exact congrArg B.inclusion.map (p i).w)
  exact ⟨W, f, inferInstanceAs (IsClosedImmersion d.toBase), c,
    fun i => q.map_injective (d.ι_toBase i),
    fun i => (Scheme.IsLocallyDirected.openCover d.functor).map_prop i,
    fun x => Scheme.IsLocallyDirected.ι_jointly_surjective d.functor x⟩

/-- The diagonal of an affine formal algebraic space is representable and a
closed immersion. -/
@[stacks 0AI8]
public theorem diagonal_isClosedImmersion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening
        ((BigAffineFppf.toScheme B S hS).map (D.map f)))
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (e : colimit
      (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda
          (BigFppfOver.topology B S hS)) ≅ X) :
    (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) (diag X) := by
  classical
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  let q := BigFppfOver.toScheme B S hS
  let : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let : F.Full := Sheaf.sheafifiedYoneda_full J
  let : F.Faithful := Sheaf.sheafifiedYoneda_faithful J
  let : (MorphismProperty.inverseImage (@IsClosedImmersion.{u}) q).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage (@IsClosedImmersion.{u}) q
  apply MorphismProperty.relative.of_exists
  intro U b
  let A := affineOpenDiagram B S hS U
  let ui := fun i : (q.obj U).affineOpens => openOverι B S hS U i.1
  let f := b ≫ Limits.prod.fst
  let g := b ≫ Limits.prod.snd
  have hlocal (i : (q.obj U).affineOpens) := by
    let : IsAffine (q.obj (A.obj i)) := i.property
    exact affine_test_pair_has_closed_equalizer B S hS D hD X e (A.obj i)
      (F.map (ui i) ≫ f) (F.map (ui i) ≫ g)
  choose V p hc a hp using hlocal
  let E := pullback (diag X) b
  let y : E ⟶ F.obj U := pullback.snd (diag X) b
  have : Mono y := inferInstanceAs (Mono (pullback.snd (diag X) b))
  have hp' (i) : IsPullback (a i) (F.map (p i)) (diag X) (F.map (ui i) ≫ b) := by
    convert hp i using 1
    apply Limits.prod.hom_ext <;> simp only [f, g, Category.assoc, prod.lift_fst,
      prod.lift_snd]
  let l (i) : F.obj (V i) ⟶ E :=
    pullback.lift (a i) (F.map (p i) ≫ F.map (ui i)) (by
      simpa only [Category.assoc] using (hp' i).w)
  have hl (i) : IsPullback (l i) (F.map (p i)) y (F.map (ui i)) := by
    apply IsPullback.of_right (h₁₂ := pullback.fst (diag X) b) (h₂₂ := b)
    · simpa only [l, pullback.lift_fst] using hp' i
    · exact pullback.lift_snd _ _ _
    · exact IsPullback.of_hasPullback (diag X) b
  obtain ⟨W, j, hj, c, hcf, hco, hcs⟩ :=
    exists_closed_gluing B S hS U E y V p l hc hl
  have heq : F.map j ≫ f = F.map j ≫ g := by
    apply sheafifiedYoneda_hom_ext_open_family B S hS c hco hcs
    intro i
    change F.map (c i) ≫ (F.map j ≫ f) = F.map (c i) ≫ (F.map j ≫ g)
    have hcmap : F.map (c i) ≫ F.map j = F.map (p i) ≫ F.map (ui i) := by
      rw [← F.map_comp, hcf, F.map_comp]
    conv_lhs => rw [← Category.assoc, hcmap]
    conv_rhs => rw [← Category.assoc, hcmap]
    obtain ⟨h₁, h₂⟩ := comp_diag_eq_comp_prod_lift_iff.1 (hp i).w
    simpa only [Category.assoc] using h₁.symm.trans h₂
  let m : F.obj W ⟶ E := pullback.lift (F.map j ≫ f) (F.map j) (by
    apply Limits.prod.hom_ext
    · rw [prod.comp_diag, prod.lift_fst]
      change F.map j ≫ (b ≫ Limits.prod.fst) = (F.map j ≫ b) ≫ Limits.prod.fst
      exact (Category.assoc _ _ _).symm
    · rw [prod.comp_diag, prod.lift_snd]
      change F.map j ≫ f = (F.map j ≫ b) ≫ Limits.prod.snd
      rw [heq]
      exact (Category.assoc _ _ _).symm)
  have hm : m ≫ y = F.map j := pullback.lift_snd _ _ _
  have : Mono (F.map j) := by
    have := hj
    exact Sheaf.mono_sheafifiedYoneda_map_of_mono_underlying J q j inferInstance
  have : Mono m := mono_of_mono_fac hm
  have hcm (i) : F.map (c i) ≫ m = l i := by
    apply (cancel_mono y).1
    rw [Category.assoc, hm, ← F.map_comp, hcf, F.map_comp]; exact (hl i).w.symm
  have : Epi m := by
    constructor
    intro Z z₁ z₂ hz
    apply sheaf_hom_ext_yoneda
    intro T s
    let t : T ⟶ U := F.preimage (s ≫ y)
    have ht : F.map t = s ≫ y := F.map_preimage _
    let Q (i : (q.obj U).affineOpens) := pullback t (ui i)
    let t₁ (i) : Q i ⟶ T := pullback.fst t (ui i)
    let t₂ (i) : Q i ⟶ A.obj i := pullback.snd t (ui i)
    have hQ (i) : IsPullback (q.map (t₁ i)) (q.map (t₂ i))
        (q.map t) (q.map (ui i)) := (IsPullback.of_hasPullback t (ui i)).map q
    have ho (i) : IsOpenImmersion (q.map (t₁ i)) := by
      apply MorphismProperty.IsStableUnderBaseChange.of_isPullback (hQ i).flip
      exact inferInstanceAs (IsOpenImmersion i.1.ι)
    have hs (x : q.obj T) : ∃ i z, q.map (t₁ i) z = x := by
      obtain ⟨i, z, h⟩ := (q.obj U).directedAffineCover.exists_eq (q.map t x)
      obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback (hQ i) x z h.symm
      exact ⟨i, w, hw⟩
    apply sheafifiedYoneda_hom_ext_open_family B S hS t₁ ho hs
    intro i
    have hw : (F.map (t₁ i) ≫ s) ≫ y = F.map (t₂ i) ≫ F.map (ui i) := by
      rw [Category.assoc, ← ht, ← F.map_comp, pullback.condition, F.map_comp]
    let k : F.obj (Q i) ⟶ F.obj (V i) :=
      (hl i).lift (F.map (t₁ i) ≫ s) (F.map (t₂ i)) hw
    have hk : k ≫ l i = F.map (t₁ i) ≫ s := (hl i).lift_fst _ _ _
    have hkm : (k ≫ F.map (c i)) ≫ m = F.map (t₁ i) ≫ s := by
      rw [Category.assoc, hcm, hk]
    calc
      F.map (t₁ i) ≫ (s ≫ z₁) = (k ≫ F.map (c i)) ≫ (m ≫ z₁) := by
        simp only [← Category.assoc, hkm]
      _ = (k ≫ F.map (c i)) ≫ (m ≫ z₂) := by rw [hz]
      _ = F.map (t₁ i) ≫ (s ≫ z₂) := by
        simp only [← Category.assoc, hkm]
  have : IsIso m := isIso_of_mono_of_epi m
  refine ⟨W, F.map j ≫ f, j, ?_, hj⟩
  apply IsPullback.of_iso (IsPullback.of_hasPullback (diag X) b)
    (asIso m).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · change pullback.fst (diag X) b ≫ 𝟙 X = inv m ≫ (F.map j ≫ f)
    have hm₁ : m ≫ pullback.fst (diag X) b = F.map j ≫ f := pullback.lift_fst _ _ _
    rw [Category.comp_id, ← hm₁, IsIso.inv_hom_id_assoc]
  · change y ≫ 𝟙 _ = inv m ≫ F.map j
    rw [Category.comp_id, ← hm, IsIso.inv_hom_id_assoc]
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm

end AlgebraicGeometry.FormalSpace

end
