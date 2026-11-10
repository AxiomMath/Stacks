module

public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.Cohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.HigherDirectImages
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CohomologyPresheafLocallyZero
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CohomologyViaSectionComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.AbelianSheavesOnALocalizedSite
import StacksCore.Tactic.StacksAttribute

/-!
# Descent of a cohomology class along a single covering morphism

In the situation of Stacks 0EZ3 let `f : X ⟶ Y` be a morphism of the distinguished class `P`
which by itself is a covering for the finer topology, and let `F` be an abelian sheaf of the
weak Serre class `𝒜'_Y` on the coarser site localized at `Y`. A cohomology class of positive
degree on `X` whose two restrictions to `X ×_Y X` agree need not come from a class on `Y`, but
it does die after base changing `X` along a suitable covering of `Y` for the *coarser*
topology.

The argument is the source's. The class `θ` determines a global section `θ̄` of the higher
direct image `𝒢' = R^{n+1} f_{τ',*}(F|_X)`, and the assertion is that `θ̄` is zero. The sheaf
`𝒢'` lies in `𝒜'_Y`, because `F|_X` lies in `𝒜'_X` and `P` is stable under higher direct
images; hence `𝒢'` satisfies the sheaf condition for the *finer* topology. As `{X ⟶ Y}` is a
fine covering, restriction `𝒢'(Y) ⟶ 𝒢'(X)` is therefore injective, and the equalizer
hypothesis says exactly that the restriction of `θ̄` to `X` vanishes — by trivial base change
along the Cartesian square of the two projections of `X ×_Y X`.

## Main results

* `Stacks.ComparingTopologies.exists_coarseCovering_restrict_eq_zero_of_equalizer`: an
  equalizing class of degree `n + 1` becomes zero after base change by a covering for the
  coarser topology.

## Implementation notes

Cohomology over an object of a site is `Stacks.sheafCohomology`, the right derived functors of
sections, and `Stacks.sheafCohomologyRestriction` is the restriction map between two of them.

Fibre products are expressed by an object of the slice category together with `IsPullback`,
rather than by a global `HasPullbacks` instance: the comparison situation only supplies the
pullbacks needed to base change a covering, and a `Presieve`'s membership in a precoverage is
the way covering families are given. Equalizer membership is the equality of the two
restriction maps.

The higher direct image is computed through the presheaf `V ↦ H^{n+1}(I^•(V))` of the sections
of an injective resolution `I` of `F`: its sheafification for the coarser localized topology is
`R^{n+1} f_{τ',*}` of the restriction of `F`, which is
`pullbackHomologySheafIso`, and it is locally zero in positive degree by Stacks 01FW. Working
with that presheaf rather than with the derived functor directly is what makes "θ̄ restricts to
zero on a covering" a statement about sections of a presheaf, which is how the sheaf condition
for the finer topology is used.

## References

* [Stacks Project, Tag 0EZD](https://stacks.math.columbia.edu/tag/0EZD)
* [Stacks Project, Tag 01FW](https://stacks.math.columbia.edu/tag/01FW)
* [Stacks Project, Tag 0EZ0](https://stacks.math.columbia.edu/tag/0EZ0)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory Opposite

namespace Stacks.ComparingTopologies

open Stacks.Cohomology.Locality Stacks.Cohomology.Localization

variable {C : Type u} [Category.{v} C]

/-- The image of an injective resolution under an exact functor which preserves injective
objects is an injective resolution of the image. -/
private def mapInjectiveResolution {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] (G : A ⥤ B) [G.Additive] [G.PreservesInjectiveObjects]
    [G.PreservesHomology] {F : A} (I : InjectiveResolution F) :
    InjectiveResolution (G.obj F) where
  cocomplex := (G.mapHomologicalComplex _).obj I.cocomplex
  injective n := G.injective_obj _
  ι := (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℕ) 0).inv.app F ≫
    (G.mapHomologicalComplex _).map I.ι

/-- **Stacks 0EZ0, degreewise.** The higher direct image of the restriction of `F` along `f` is
the sheafification of the presheaf of cohomology classes on the base changes along `f`. -/
private def pullbackHomologySheafIso (J : GrothendieckTopology C) {X Y : C} (f : X ⟶ Y)
    [Limits.HasPullbacksAlong f] (F : Sheaf (J.over Y) Ab.{max u v}) (I : InjectiveResolution F)
    (n : ℕ) :
    (presheafToSheaf (J.over Y) Ab.{max u v}).obj
        ((Over.pullback f ⋙ Over.map f).op ⋙ (sectionComplex F I).homology n) ≅
      ((overPushforward J f).rightDerived n).obj ((overPullback J f).obj F) := by
  let R := overPullback J f
  let P := overPushforward J f
  let L := sheafToPresheaf (J.over Y) Ab.{max u v}
  let T := (Functor.whiskeringLeft _ _ Ab.{max u v}).obj (Over.pullback f ⋙ Over.map f).op
  let A := presheafToSheaf (J.over Y) Ab.{max u v}
  have : (Over.pullback f).IsContinuous (J.over Y) (J.over X) :=
    (Over.mapPullbackAdj f).isContinuous_of_isCocontinuous _ _
  let P' := (Over.pullback f).sheafPushforwardContinuous Ab.{max u v} (J.over Y) (J.over X)
  let eP : P' ≅ P := Adjunction.rightAdjointUniq
    ((Over.mapPullbackAdj f).sheafPushforwardContinuous (E := Ab.{max u v}) (J.over X) (J.over Y))
    ((Over.map f).sheafAdjunctionCocontinuous Ab.{max u v} (J.over X) (J.over Y))
  have eM : L ⋙ T ⋙ A ≅ R ⋙ P :=
    (Functor.associator R P' (L ⋙ A)).symm ≪≫
      Functor.isoWhiskerLeft (R ⋙ P') (sheafificationNatIso (J.over Y) Ab.{max u v}).symm ≪≫
      Functor.rightUnitor (R ⋙ P') ≪≫ Functor.isoWhiskerLeft R eP
  let adjCo : R ⊣ P := (Over.map f).sheafAdjunctionCocontinuous Ab.{max u v} (J.over X) (J.over Y)
  let adjCt : (Over.map f).sheafPullback Ab.{max u v} (J.over X) (J.over Y) ⊣ R :=
    (Over.map f).sheafAdjunctionContinuous Ab.{max u v} (J.over X) (J.over Y)
  have := adjCo.isLeftAdjoint
  have := adjCt.isRightAdjoint
  let _ : Limits.PreservesFiniteColimits R :=
    (adjCo.leftAdjoint_preservesColimits.{u, u}).preservesFiniteColimits
  let _ : Limits.PreservesFiniteLimits R :=
    (adjCt.rightAdjoint_preservesLimits.{u, u}).preservesFiniteLimits
  let I' := mapInjectiveResolution R I
  let K := sectionComplex F I
  have eH : A.obj (T.obj (K.homology n)) ≅
      ((P.mapHomologicalComplex _).obj I'.cocomplex).homology n :=
    ((K.sc n).mapHomologyIso (T ⋙ A)).symm ≪≫
      (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).mapIso
        ((NatIso.mapHomologicalComplex eM (ComplexShape.up ℕ)).app I.cocomplex)
  exact eH ≪≫ (I'.isoRightDerivedObj P n).symm

/-- A section of a sheaf which restricts to zero along a morphism generating a covering sieve is
zero. -/
private lemma section_eq_zero_of_singleton {D : Type u} [Category.{v} D]
    (J : GrothendieckTopology D) (G : Dᵒᵖ ⥤ Ab.{max u v}) (hG : Presheaf.IsSheaf J G) {U V : D}
    (f : U ⟶ V) (hf : Sieve.generate (Presieve.singleton f) ∈ J V) (x : G.obj (op V))
    (hx : G.map f.op x = 0) : x = 0 := by
  apply section_eq_zero_of_cover J G hG ⟨_, hf⟩ x
  rintro ⟨W, _, Z, g, _, ⟨⟩, rfl⟩
  simpa using congrArg (fun y => G.map g.op y) hx

/-- A locally zero section of a presheaf stays zero in the sheafification of its restriction
along a comonad-like endofunctor, after transport by the natural map to the identity. -/
private lemma sheafify_section_eq_zero_of_locally_zero {D : Type u} [Category.{v} D]
    (J : GrothendieckTopology D) (B : D ⥤ D) (ε : B ⟶ 𝟭 D) (H : Dᵒᵖ ⥤ Ab.{max u v}) {U : D}
    (x : H.obj (op U)) (hx : ∃ R : J.Cover U, ∀ g : R.Arrow, H.map g.f.op x = 0) :
    (toSheafify J (B.op ⋙ H)).app (op U) (H.map (ε.app U).op x) = 0 := by
  obtain ⟨R, hR⟩ := hx
  let η := toSheafify J (B.op ⋙ H)
  apply section_eq_zero_of_cover J _ ((presheafToSheaf J Ab.{max u v}).obj (B.op ⋙ H)).property R
  intro g
  have hn := NatTrans.naturality_apply η g.f.op (H.map (ε.app U).op x)
  change _ = 0
  rw [← hn]
  have he : H.map (B.map g.f).op (H.map (ε.app U).op x) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← H.map_comp, ← op_comp, ε.naturality g.f, op_comp,
      H.map_comp, ConcreteCategory.comp_apply]
    simp [hR g]
  simpa using congrArg (fun z => η.app (op g.Y) z) he

/-- The second projection from the base change of `f` along an object of the slice category. -/
private def baseChangeProjection {X Y : C} (f : X ⟶ Y) [Limits.HasPullbacksAlong f]
    (V : Over Y) : (Over.pullback f ⋙ Over.map f).obj V ⟶ Over.mk f :=
  Over.homMk (Limits.pullback.snd V.hom f) rfl

/-- The projections from the base changes of `f` are natural in the slice object. -/
private lemma baseChangeProjection_naturality {X Y : C} (f : X ⟶ Y)
    [Limits.HasPullbacksAlong f] {U V : Over Y} (g : U ⟶ V) :
    (Over.pullback f ⋙ Over.map f).map g ≫ baseChangeProjection f V =
      baseChangeProjection f U := by
  ext
  dsimp [baseChangeProjection]
  exact Limits.pullback.lift_snd _ _ _

/-- **Stacks 0EZD.** Let `f : X ⟶ Y` be a morphism of the distinguished class which by itself
is a covering for the finer topology, and let `F` be a sheaf of the weak Serre class `𝒜'_Y` on
the coarser site localized at `Y`. If a cohomology class of degree `n + 1` over `X` has equal
restrictions along the two projections from `X ×_Y X`, then there is a covering of `Y` for the
coarser topology such that the class restricts to zero over every base change `Yᵢ ×_Y X`. -/
@[stacks 0EZD]
theorem exists_coarseCovering_restrict_eq_zero_of_equalizer (S : CohomologyComparison C)
    {X Y : C} (f : X ⟶ Y) (hf : S.morphismProperty f)
    (hcover : Presieve.singleton f ∈ S.fineCoverage Y)
    (F : Sheaf (S.coarseCoverage.toGrothendieck.over Y) Ab.{max u v}) (hF : S.weakSerre Y F) (n : ℕ)
    (P : Over Y) (p₁ p₂ : P ⟶ Over.mk f) (hP : IsPullback p₁.left p₂.left f f)
    (θ : Stacks.sheafCohomology (S.coarseCoverage.toGrothendieck.over Y) F (Over.mk f) (n + 1))
    (hθ : Stacks.sheafCohomologyRestriction (S.coarseCoverage.toGrothendieck.over Y) p₁
        (n + 1) F θ =
      Stacks.sheafCohomologyRestriction (S.coarseCoverage.toGrothendieck.over Y) p₂
        (n + 1) F θ) :
    ∃ R : Presieve Y, R ∈ S.coarseCoverage Y ∧
      ∀ ⦃Z : C⦄ (g : Z ⟶ Y), R g →
        ∃ (Q : Over Y) (a : Q ⟶ Over.mk f) (b : Q ⟶ Over.mk g),
          IsPullback a.left b.left f g ∧
            Stacks.sheafCohomologyRestriction (S.coarseCoverage.toGrothendieck.over Y) a
              (n + 1) F θ = 0 := by
  let J := S.coarseCoverage.toGrothendieck
  let T : Over Y := Over.mk (𝟙 Y)
  let U : Over Y := Over.mk f
  let t : U ⟶ T := Over.homMk f (by simp [T, U])
  have : Limits.HasPullbacksAlong f := fun {Z} g => by
    obtain ⟨_, _, _, h, _⟩ := S.morphismProperty_baseChange f hf g
    exact h.flip.hasPullback
  let B := Over.pullback f ⋙ Over.map f
  let ε : B ⟶ 𝟭 (Over Y) := (Over.mapPullbackAdj f).counit
  let I := injectiveResolution F
  let H := (sectionComplex F I).homology (n + 1)
  let K := B.op ⋙ H
  let η := toSheafify (J.over Y) K
  let x := (sectionHomologyIso (J.over Y) F I (n + 1) U).hom θ
  let s : K.obj (op T) := H.map (baseChangeProjection f T).op x
  have hH : H.map p₁.op x = H.map p₂.op x := by
    rw [← sectionHomologyIso_restrict, ← sectionHomologyIso_restrict, hθ]
  have hpair : H.map (baseChangeProjection f U).op x = H.map (ε.app U).op x := by
    let l : B.obj U ⟶ P := Over.homMk
      (hP.lift (Limits.pullback.snd f f) (Limits.pullback.fst f f)
        Limits.pullback.condition.symm)
      (by rw [← Over.w p₁, ← Category.assoc, hP.lift_fst]; rfl)
    have hl₁ : l ≫ p₁ = baseChangeProjection f U := by
      ext
      exact hP.lift_fst _ _ _
    have hl₂ : l ≫ p₂ = ε.app U := by
      ext
      simpa only [l, ε, Over.comp_left, Over.homMk_left, Over.mapPullbackAdj_counit_app, U,
        Over.mk_hom] using
        hP.lift_snd (Limits.pullback.snd f f) (Limits.pullback.fst f f)
          Limits.pullback.condition.symm
    have hl := congrArg (fun y => H.map l.op y) hH
    simpa only [← ConcreteCategory.comp_apply, ← H.map_comp, ← op_comp, hl₁, hl₂] using hl
  have hs₀ : η.app (op U) (K.map t.op s) = 0 := by
    have he : K.map t.op s = H.map (ε.app U).op x := by
      change H.map (B.map t).op (H.map (baseChangeProjection f T).op x) = _
      rw [← ConcreteCategory.comp_apply, ← H.map_comp, ← op_comp,
        baseChangeProjection_naturality]
      exact hpair
    rw [he]
    exact sheafify_section_eq_zero_of_locally_zero (J.over Y) B ε H x
      (injectiveResolution_homology_presheaf_locally_zero F I (n + 1) (Nat.succ_pos _) U x)
  have hG : Presheaf.IsSheaf (S.fineCoverage.toGrothendieck.over Y)
      (sheafify (J.over Y) K) :=
    (Presheaf.isSheaf_of_iso_iff ((sheafToPresheaf (J.over Y) Ab.{max u v}).mapIso
      (pullbackHomologySheafIso J f F I (n + 1)))).mpr
      (S.weakSerre_isSheaf_fine Y _ (S.weakSerre_rightDerived_relocalizationPushforward f hf _
        (S.weakSerre_relocalizationInverseImage f F hF) (n + 1)))
  have hcov : Sieve.generate (Presieve.singleton t) ∈
      (S.fineCoverage.toGrothendieck.over Y) T := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate]
    apply S.fineCoverage.toGrothendieck.superset_covering _
      (S.fineCoverage.generate_mem_toGrothendieck hcover)
    apply Sieve.generate_mono
    intro Z g hg
    cases hg
    exact ⟨U, t, 𝟙 X, ⟨⟩, by simp [t]⟩
  have hs : η.app (op T) s = 0 := by
    apply section_eq_zero_of_singleton _ _ hG t hcov
    rwa [← NatTrans.naturality_apply η t.op s]
  let E := Presheaf.equalizerSieve s 0
  have hE : E ∈ (J.over Y) T :=
    Presheaf.IsLocallyInjective.equalizerSieve_mem (φ := η) s 0 (by simpa using hs)
  have hEY : Sieve.overEquiv T E ∈ J Y := hE
  obtain ⟨R, hR, hRE⟩ :=
    S.coarseCoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hEY
  refine ⟨R, hR, ?_⟩
  intro Z g hg
  let V : Over Y := Over.mk g
  let v : V ⟶ T := Over.homMk g (by simp [T, V])
  have hv : E v := by
    rw [← (Sieve.overEquiv T).symm_apply_apply E]
    exact hRE _ g hg
  have hv₀ : K.map v.op s = 0 := by simpa [E] using hv
  have hx₀ : H.map (baseChangeProjection f V).op x = 0 := by
    change H.map (B.map v).op (H.map (baseChangeProjection f T).op x) = 0 at hv₀
    simpa only [B, ← ConcreteCategory.comp_apply, ← H.map_comp, ← op_comp,
      baseChangeProjection_naturality] using hv₀
  refine ⟨B.obj V, baseChangeProjection f V, ε.app V, ?_, ?_⟩
  · simpa only [ε, Over.mapPullbackAdj_counit_app, baseChangeProjection, Over.homMk_left, V,
      Over.mk_hom] using (IsPullback.of_hasPullback g f).flip
  · apply (sectionHomologyIso (J.over Y) F I (n + 1)
      (B.obj V)).addCommGroupIsoToAddEquiv.injective
    change (sectionHomologyIso (J.over Y) F I (n + 1) (B.obj V)).hom
        (Stacks.sheafCohomologyRestriction (J.over Y) (baseChangeProjection f V) (n + 1) F θ) =
      (sectionHomologyIso (J.over Y) F I (n + 1) (B.obj V)).hom 0
    rw [map_zero, sectionHomologyIso_restrict]
    exact hx₀

end Stacks.ComparingTopologies
