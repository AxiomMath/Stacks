module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FppfApplication.FiniteDomination
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverReductions
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasiAffineClosedInFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesForget
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Refining an integral scheme cover along a surjective étale morphism

Let `X` be a quasi-compact and quasi-separated algebraic space over `S` and let `p : U ⟶ X` be a
surjective étale morphism from an algebraic space.  Given a surjective integral morphism onto `X`
from a scheme, Stacks 0CP0 refines it to one which, Zariski locally on its source, factors
through `p`; likewise for a surjective finite morphism of finite presentation.  These are the
implications from clause (1) to clause (2) of Stacks 09YB and of Stacks 09YC.

## Main results

* `AlgebraicGeometry.Space.exists_etale_chart_over`: the fibre product `U ×_X h_Y` has an étale
  chart which is a surjective étale morphism of schemes onto `Y`.
* `AlgebraicGeometry.Space.compactSpace_and_quasiSeparatedSpace_of_isIntegralHom`: the source
  of an integral morphism onto a quasi-compact quasi-separated algebraic space is a
  quasi-compact quasi-separated scheme.
* `AlgebraicGeometry.Space.exists_finite_surjective_refinement_over`: the finite refinement of a
  scheme cover along `p`, by Stacks 0CP0.
* `AlgebraicGeometry.Space.exists_integralSurjectiveSchemeCover_refining_of_clause_one` and
  `AlgebraicGeometry.Space.exists_finiteSurjectiveSchemeCover_refining_of_clause_one`: clause (2)
  of Stacks 09YB and of Stacks 09YC from clause (1).

## References

* [Stacks Project, Tag 0CP0](https://stacks.math.columbia.edu/tag/0CP0)
* [Stacks Project, Tag 09YB](https://stacks.math.columbia.edu/tag/09YB)
* [Stacks Project, Tag 09YC](https://stacks.math.columbia.edu/tag/09YC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- If a morphism of the site is sent to a base-change stable affine morphism property `P` of
schemes, every base change of it along a map from an affine object is represented by an affine
object whose projection satisfies `P`. -/
private theorem exists_affine_pullback_of_property {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange]
    (hP : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), P f → _root_.AlgebraicGeometry.IsAffineHom f)
    {M N : BigFppfOver B S hS} (m : M ⟶ N) (hm : P ((BigFppfOver.toScheme B S hS).map m))
    (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (gg : yoneda.obj T ⟶ yoneda.obj N) :
    ∃ (V : BigFppfOver B S hS) (q : V ⟶ T) (a : yoneda.obj V ⟶ yoneda.obj M),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧ P ((BigFppfOver.toScheme B S hS).map q) ∧
      IsPullback a (yoneda.map q) (yoneda.map m) gg := by
  have _ : (MorphismProperty.inverseImage P
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    ⟨fun h hf => MorphismProperty.of_isPullback (P := P) (h.map _) hf⟩
  have h := MorphismProperty.relative_map (F := yoneda) (P := MorphismProperty.inverseImage P
    (BigFppfOver.toScheme B S hS)) hm
  obtain ⟨V, q, a, hpb⟩ := h.rep gg
  have := hP _ (h.property gg a q hpb)
  exact ⟨V, q, a, isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map q),
    h.property gg a q hpb, hpb⟩

/-- A morphism of the site which is integral as a morphism of schemes induces an integral
morphism of algebraic spaces. -/
private theorem isIntegralHom_yoneda_map' {M N : BigFppfOver B S hS} (m : M ⟶ N)
    (hm : _root_.AlgebraicGeometry.IsIntegralHom ((BigFppfOver.toScheme B S hS).map m)) :
    IsIntegralHom B S hS (yoneda.map m) := fun T _ gg => by
  obtain ⟨V, q, a, hV, hq, hpb⟩ := exists_affine_pullback_of_property B S hS
    (P := @_root_.AlgebraicGeometry.IsIntegralHom.{u}) (fun f _ => inferInstance) m hm T gg
  exact ⟨V, q, a, hpb, hV, hq⟩

/-- A morphism of the site which is surjective as a morphism of schemes induces a surjective
morphism of algebraic spaces. -/
private theorem isSurjective_yoneda_map' {M N : BigFppfOver B S hS} (m : M ⟶ N)
    (hm : Surjective ((BigFppfOver.toScheme B S hS).map m)) :
    IsSurjective B S hS (yoneda.map m) := by
  set Qf := BigFppfOver.toScheme B S hS with hQf
  have _ : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) Qf).IsStableUnderBaseChange :=
    ⟨fun h hf => MorphismProperty.of_isPullback (P := @Surjective.{u}) (h.map Qf) hf⟩
  exact (presheafSurjective_iff_isSurjective_yoneda B S hS _
    (isAlgebraicSpace_yoneda B S hS N) M (yoneda.map m)).mp
    (MorphismProperty.relative_map hm)

/-- Precomposing a surjective morphism of algebraic spaces with a morphism of the site which is
surjective as a morphism of schemes gives a surjective morphism. -/
private theorem isSurjective_yoneda_map_comp {Z Y : BigFppfOver B S hS}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (r : Z ⟶ Y) {f : yoneda.obj Y ⟶ X}
    (hf : IsSurjective B S hS f) (hr : Surjective ((BigFppfOver.toScheme B S hS).map r)) :
    IsSurjective B S hS (yoneda.map r ≫ f) := by
  change Function.Surjective (pointsMap B S hS (yoneda.obj Z) (yoneda.map r ≫ f))
  rw [pointsMap_comp B S hS (yoneda.obj Z) (yoneda.map r) f]
  exact hf.comp (isSurjective_yoneda_map' B S hS r hr)

/-- A morphism of the site which is finite as a morphism of schemes induces a finite morphism
of algebraic spaces. -/
private theorem isFinite_yoneda_map' {M N : BigFppfOver B S hS} (m : M ⟶ N)
    (hm : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map m)) :
    IsFinite B S hS (yoneda.map m) := fun T _ gg => by
  obtain ⟨V, q, a, hV, hq, hpb⟩ := exists_affine_pullback_of_property B S hS
    (P := @_root_.AlgebraicGeometry.IsFinite.{u}) (fun f _ => inferInstance) m hm T gg
  exact ⟨V, q, a, hV, hq, hpb⟩

/-- An étale chart of the fibre product `U ×_X h_Y`, read as a surjective étale morphism of
schemes onto `Y` together with a morphism to `U` over `X`. -/
theorem exists_etale_chart_over
    {X U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hU : IsAlgebraicSpace B S hS U)
    (Y : BigFppfOver B S hS) (z : yoneda.obj Y ⟶ X)
    (p : U ⟶ X) (hp : IsSurjective B S hS p) (he : IsEtale B S hS p) :
    ∃ (W : BigFppfOver B S hS) (q : W ⟶ Y) (a : yoneda.obj W ⟶ U),
      Surjective ((BigFppfOver.toScheme B S hS).map q) ∧
      Etale ((BigFppfOver.toScheme B S hS).map q) ∧
      yoneda.map q ≫ z = a ≫ p := by
  let X' : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let U' : AlgebraicSpaces B S hS := ⟨U, hU⟩
  let Y' : AlgebraicSpaces B S hS := ⟨yoneda.obj Y, isAlgebraicSpace_yoneda B S hS Y⟩
  let p' : U' ⟶ X' := ObjectProperty.homMk p
  let z' : Y' ⟶ X' := ObjectProperty.homMk z
  let P := AlgebraicSpaces.fiberProduct B S hS p' z'
  have hs := AlgebraicSpaces.isPullback_fiberProduct B S hS p' z'
  have het := isEtale_of_isPullback B S hS _ _ _ _ hs he
  have hsur := isSurjective_of_isPullback B S hS hs hp
  set ρ : P.obj ⟶ U :=
    (ObjectProperty.homMk (pullback.fst p'.hom z'.hom) : P ⟶ U').hom with hρ
  set π : P.obj ⟶ yoneda.obj Y :=
    (ObjectProperty.homMk (pullback.snd p'.hom z'.hom) : P ⟶ Y').hom with hπ
  have hcond : ρ ≫ p = π ≫ z := congrArg (fun t : P ⟶ X' => t.hom) hs.w
  obtain ⟨W, w, hwSur, hwEt⟩ := P.property.exists_atlas
  let q : W ⟶ Y := yoneda.preimage (w ≫ π)
  have hq : yoneda.map q = w ≫ π := yoneda.map_preimage _
  refine ⟨W, q, w ≫ ρ, ?_, ?_, ?_⟩
  · have hwSur' := (presheafSurjective_iff_isSurjective_yoneda B S hS
      P.obj P.property W w).mp hwSur
    have hqSur : IsSurjective B S hS (yoneda.map q) := by
      rw [hq]
      show Function.Surjective (pointsMap B S hS (yoneda.obj W) (w ≫ π))
      rw [pointsMap_comp B S hS (yoneda.obj W) w π]
      exact hsur.comp hwSur'
    have hr := (presheafSurjective_iff_isSurjective_yoneda B S hS
      _ Y'.property W (yoneda.map q)).mpr hqSur
    exact MorphismProperty.of_relative_map (F := yoneda)
      (P := MorphismProperty.inverseImage _ (BigFppfOver.toScheme B S hS)) hr
  · have hr : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map q) := by
      rw [hq]
      exact het W w hwEt
    exact MorphismProperty.of_relative_map (F := yoneda)
      (P := MorphismProperty.inverseImage _ (BigFppfOver.toScheme B S hS)) hr
  · rw [hq, Category.assoc, ← hcond, Category.assoc]

/-- An integral morphism from a represented presheaf onto a quasi-compact quasi-separated
algebraic space has quasi-compact and quasi-separated underlying scheme. -/
theorem compactSpace_and_quasiSeparatedSpace_of_isIntegralHom
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (Y : BigFppfOver B S hS)
    (f : yoneda.obj Y ⟶ X) (hX : IsAlgebraicSpace B S hS X)
    (hXqc : IsQuasiCompactSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (hf : IsIntegralHom B S hS f) :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj Y) ∧
      QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj Y) := by
  refine ⟨compactSpace_of_isIntegralHom B S hS Y f hX hXqc hf, ?_⟩
  let := pointTopology B S hS (yoneda.obj Y)
  have hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal (yoneda.obj Y) :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ
      (isAlgebraicSpace_yoneda B S hS Y) hXqs
      (isQuasiSeparated_of_isSeparated B S hS
        (isSeparated_of_isIntegralHom B S hS f (isAlgebraicSpace_yoneda B S hS Y) hX hf))
  have := quasiSeparatedSpace_points_of_isAbsolutelyQuasiSeparated B S hS (yoneda.obj Y)
    (isAlgebraicSpace_yoneda B S hS Y) hYqs
  exact (schemePointsHomeomorph B S hS Y).symm.isOpenEmbedding.quasiSeparatedSpace

/-- **The finite refinement of a scheme cover along a surjective étale morphism, by
Stacks 0CP0.** Let `X` be an algebraic space over `S`, let `p : U ⟶ X` be a surjective étale
morphism from an algebraic space, and let `f : h_Y ⟶ X` be any morphism from the presheaf
represented by an object `Y` of the site whose underlying scheme is quasi-compact and
quasi-separated. Then there are an object `Z` of the site and a morphism `r : Z ⟶ Y` which is
finite, surjective and of finite presentation as a morphism of schemes, such that `r ≫ f`
factors through `p` on a representable open neighbourhood of every point of `h_Z`.

This is the whole of the refinement argument: the fibre product `U ×_X h_Y` has a surjective
étale chart `W ⟶ Y` by `AlgebraicGeometry.Space.exists_etale_chart_over`, so `{W ⟶ Y}` is a
one-member fppf covering of the quasi-compact quasi-separated scheme `Y`, and Stacks 0CP0
dominates it by a finite surjective morphism of finite presentation carrying an open covering
each member of which maps to `Y` through `W`, hence to `X` through `U`. -/
theorem exists_finite_surjective_refinement_over
    {X U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hU : IsAlgebraicSpace B S hS U)
    (Y : BigFppfOver B S hS) (f : yoneda.obj Y ⟶ X)
    (hYc : CompactSpace ((BigFppfOver.toScheme B S hS).obj Y))
    (hYqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj Y))
    (p : U ⟶ X) (hpsurj : IsSurjective B S hS p) (hpet : IsEtale B S hS p) :
    ∃ (Z : BigFppfOver B S hS) (r : Z ⟶ Y),
      _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map r) ∧
      Surjective ((BigFppfOver.toScheme B S hS).map r) ∧
      FinitePresentation ((BigFppfOver.toScheme B S hS).map r) ∧
      ∀ y : points B S hS (yoneda.obj Z), ∃ W : Subfunctor (yoneda.obj Z),
        IsOpenSubspace B S hS W ∧ W.toFunctor.IsRepresentable ∧
        y ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) ∧
        ∃ a : W.toFunctor ⟶ U, W.ι ≫ (yoneda.map r ≫ f) = a ≫ p := by
  classical
  obtain ⟨W, q, a, hqsur, hqet, hqa⟩ := exists_etale_chart_over B S hS hX hU Y f p hpsurj hpet
  set Q := BigFppfOver.toScheme B S hS with hQ
  have hqsur' : Surjective (Q.map q) := hqsur
  have hqet' : Etale (Q.map q) := hqet
  have hc : Presieve.ofArrows (fun _ : PUnit.{u + 1} => Q.obj W) (fun _ => Q.map q)
      ∈ Scheme.fppfPrecoverage (Q.obj Y) := by
    rw [Presieve.ofArrows_pUnit]
    exact (Q.map q).singleton_mem_fppfPrecoverage
  obtain ⟨S', g, hgfin, hgsurj, hgfp, J, V, hVtop, hVfac⟩ :=
    exists_finite_surjective_openCover_factorization_of_mem_fppfPrecoverage
      (fun _ : PUnit.{u + 1} => Q.obj W) (fun _ => Q.map q) hc
  have hgfin' : _root_.AlgebraicGeometry.IsFinite g := hgfin
  have hS' : B.Contains S' :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact g Y.left.property
  set r₀ : B.obj hS' ⟶ Y.left := B.inclusion.preimage g with hr₀
  set Z : BigFppfOver B S hS := Over.mk (r₀ ≫ Y.hom) with hZdef
  set r' : Z ⟶ Y := Over.homMk r₀ with hr'def
  have hr' : Q.map r' = g := B.inclusion.map_preimage _
  refine ⟨Z, r', by rw [hr']; exact hgfin, by rw [hr']; exact hgsurj,
    by rw [hr']; exact hgfp, ?_⟩
  · have hVc : ∀ c, B.Contains ((V c : S'.Opens) : Scheme.{u}) := fun c =>
      Scheme.size_lt_of_isOpenImmersion (V c).ι hS'
    have hfacc : ∀ c, ∃ t : ((V c : S'.Opens) : Scheme.{u}) ⟶ Q.obj W,
        (V c).ι ≫ g = t ≫ Q.map q := by
      intro c
      obtain ⟨_, t, ht⟩ := hVfac c
      exact ⟨t, ht⟩
    choose t ht using hfacc
    set Vobj : J → BigFppfOver B S hS := fun c =>
      Over.mk ((B.inclusion.preimage (V c).ι : B.obj (hVc c) ⟶ B.obj hS') ≫ Z.hom) with hVobj
    set jj : ∀ c, Vobj c ⟶ Z := fun c => Over.homMk (B.inclusion.preimage (V c).ι) with hjj
    have hjmap : ∀ c, Q.map (jj c) = (V c).ι := fun c => B.inclusion.map_preimage _
    have hbb : ∀ c, ∃ b : Vobj c ⟶ W, b ≫ q = jj c ≫ r' := by
      intro c
      have hb₀ : (B.inclusion.preimage (t c) : (Vobj c).left ⟶ W.left) ≫ q.left =
          (B.inclusion.preimage (V c).ι : B.obj (hVc c) ⟶ B.obj hS') ≫ r₀ := by
        apply B.inclusion.map_injective
        rw [B.inclusion.map_comp, B.inclusion.map_comp, B.inclusion.map_preimage,
          B.inclusion.map_preimage, B.inclusion.map_preimage]
        exact (ht c).symm
      refine ⟨Over.homMk (B.inclusion.preimage (t c)) ?_, ?_⟩
      · show (B.inclusion.preimage (t c) : (Vobj c).left ⟶ W.left) ≫ W.hom = (Vobj c).hom
        rw [← q.w]
        show _ = (B.inclusion.preimage (V c).ι : B.obj (hVc c) ⟶ B.obj hS') ≫ r₀ ≫ Y.hom
        rw [← Category.assoc, hb₀, Category.assoc]
      · exact Over.OverMorphism.ext hb₀
    choose b hb using hbb
    intro y
    refine exists_isOpenSubspace_isRepresentable_factoring_of_openCover B S hS p Z
      (yoneda.map r' ≫ f) Vobj jj (fun c => ?_) (fun z => ?_) (fun c => ?_) y
    · rw [hjmap c]
      infer_instance
    · have hz : z ∈ (⨆ c, V c : S'.Opens) := by rw [hVtop]; trivial
      obtain ⟨c, hzc⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
      refine ⟨c, ?_⟩
      rw [hjmap c]
      exact ⟨⟨z, hzc⟩, rfl⟩
    · refine ⟨yoneda.map (b c) ≫ a, ?_⟩
      calc yoneda.map (jj c) ≫ yoneda.map r' ≫ f
          = yoneda.map (jj c ≫ r') ≫ f := by rw [Functor.map_comp, Category.assoc]
        _ = yoneda.map (b c ≫ q) ≫ f := by rw [hb c]
        _ = (yoneda.map (b c) ≫ a) ≫ p := by
            rw [Functor.map_comp, Category.assoc, hqa, Category.assoc]

/-- **Clause (2) of Stacks 09YB from clause (1), by Stacks 0CP0.** If a quasi-compact
quasi-separated algebraic space `X` over `S` admits *some* surjective integral morphism from a
scheme, then for every surjective étale `p : U ⟶ X` it admits one which, Zariski locally on its
source, factors through `p`.

The cover of clause (1) is quasi-compact and quasi-separated as a scheme, so the finite
refinement of `AlgebraicGeometry.Space.exists_finite_surjective_refinement_over` applies to it;
the refined cover is finite over it, hence integral over `X`, and surjective. -/
theorem exists_integralSurjectiveSchemeCover_refining_of_clause_one
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {X U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hU : IsAlgebraicSpace B S hS U)
    (hXqc : IsQuasiCompactSpace B S hS X) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (p : U ⟶ X) (hpsurj : IsSurjective B S hS p) (hpet : IsEtale B S hS p)
    (h1 : ExistsIntegralSurjectiveSchemeCover B S hS X) :
    ∃ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ X),
      IsSurjective B S hS g ∧ IsIntegralHom B S hS g ∧
      ∀ y : points B S hS (yoneda.obj Z), ∃ W : Subfunctor (yoneda.obj Z),
        IsOpenSubspace B S hS W ∧ W.toFunctor.IsRepresentable ∧
        y ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) ∧
        ∃ a : W.toFunctor ⟶ U, W.ι ≫ g = a ≫ p := by
  obtain ⟨Y, f, hfsurj, hfint⟩ := h1
  obtain ⟨hYc, hYqs⟩ :=
    compactSpace_and_quasiSeparatedSpace_of_isIntegralHom B S hS hZ Y f hX hXqc hXqs hfint
  obtain ⟨Z, r, hrfin, hrsurj, -, hloc⟩ :=
    exists_finite_surjective_refinement_over B S hS hX hU Y f hYc hYqs p hpsurj hpet
  refine ⟨Z, yoneda.map r ≫ f, ?_, ?_, hloc⟩
  · exact isSurjective_yoneda_map_comp B S hS r hfsurj hrsurj
  · refine isIntegralHom_comp B S hS ?_ hfint
    exact isIntegralHom_yoneda_map' B S hS r (by have := hrfin; infer_instance)

/-- **Clause (2) of Stacks 09YC from clause (1), by Stacks 0CP0.** If a quasi-compact
quasi-separated algebraic space `X` over `S` admits *some* surjective finite morphism of finite
presentation from a scheme, then for every surjective étale `p : U ⟶ X` it admits one which,
Zariski locally on its source, factors through `p`.

This is `AlgebraicGeometry.Space.exists_integralSurjectiveSchemeCover_refining_of_clause_one`
with finiteness and finite presentation carried through the composition instead of
integrality. -/
theorem exists_finiteSurjectiveSchemeCover_refining_of_clause_one
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {X U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hU : IsAlgebraicSpace B S hS U)
    (hXqc : IsQuasiCompactSpace B S hS X) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (p : U ⟶ X) (hpsurj : IsSurjective B S hS p) (hpet : IsEtale B S hS p)
    (h1 : ∃ (Y : BigFppfOver B S hS) (f : yoneda.obj Y ⟶ X),
      IsSurjective B S hS f ∧ IsFinite B S hS f ∧ IsFinitePresentation B S hS f) :
    ∃ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ X),
      IsSurjective B S hS g ∧ IsFinite B S hS g ∧ IsFinitePresentation B S hS g ∧
      ∀ y : points B S hS (yoneda.obj Z), ∃ W : Subfunctor (yoneda.obj Z),
        IsOpenSubspace B S hS W ∧ W.toFunctor.IsRepresentable ∧
        y ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) ∧
        ∃ a : W.toFunctor ⟶ U, W.ι ≫ g = a ≫ p := by
  obtain ⟨Y, f, hfsurj, hffin, hffp⟩ := h1
  obtain ⟨hYc, hYqs⟩ :=
    compactSpace_and_quasiSeparatedSpace_of_isIntegralHom B S hS hZ Y f hX hXqc hXqs
      hffin.isIntegralHom
  obtain ⟨Z, r, hrfin, hrsurj, hrfp, hloc⟩ :=
    exists_finite_surjective_refinement_over B S hS hX hU Y f hYc hYqs p hpsurj hpet
  refine ⟨Z, yoneda.map r ≫ f, ?_, ?_, ?_, hloc⟩
  · exact isSurjective_yoneda_map_comp B S hS r hfsurj hrsurj
  · exact isFinite_comp B S hS (isFinite_yoneda_map' B S hS r hrfin) hffin
  · exact isFinitePresentation_comp B S hS (isAlgebraicSpace_yoneda B S hS Z)
      (isAlgebraicSpace_yoneda B S hS Y) hX _ _
      (isFinitePresentation_yoneda_map B S hS r hrfp) hffp

end AlgebraicGeometry.Space

end
