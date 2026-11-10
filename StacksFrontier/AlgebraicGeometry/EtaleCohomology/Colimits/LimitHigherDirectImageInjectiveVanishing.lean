module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.InjectiveSystemVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.AbelianHigherDirectImageSheafification
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.HigherDirectImageLocalVanishing

/-!
# Higher direct images along a limit vanish on colimits of injective systems

Let `I` be a directed set, let `g_i : X_i ⟶ S_i` be an inverse system of quasi-compact and
quasi-separated morphisms of schemes over `I` with affine transition morphisms on both sides, and
let `g : X ⟶ S` be its limit. Let `(𝒢_i, φ_{i'i})` be a system of injective abelian sheaves on
the small étale sites of the `X_i` and `𝒢 = colim f_i⁻¹𝒢_i` on the small étale site of `X`. Then
`R^p g_* 𝒢 = 0` for `p > 0`. This is the step of the first proof of [Stacks, Tag 0EYM] that
deals with a system of injective sheaves.

The higher direct image `R^p g_* 𝒢` is the sheafification of the presheaf
`U ↦ H^p(U ×_S X, 𝒢)` ([Stacks, Tag 072W]), so it suffices that every object `U` of the small
étale site of `S` is covered by objects `U'` with `H^p(U' ×_S X, 𝒢) = 0`. Take `U'` affine and
mapping into an affine open `W` of a stage `S_{i₀}`. Then `U'` descends to an object `U_j`
étale over a later stage `S_j` with quasi-compact and quasi-separated underlying scheme, and
`U' ×_S X = V₀ ×_{X_j} X` for `V₀ = U_j ×_{S_j} X_j`, which has quasi-compact and
quasi-separated underlying scheme because `g_j` is quasi-compact and quasi-separated. Over such
an object the higher cohomology of `𝒢` vanishes,
`Stacks.EtaleCohomology.EtaleSheafSystem.isZero_rightDerived_sheafSections_of_injective`.

## Main results

Both in the namespace `Stacks.EtaleCohomology.LimitHigherDirectImage`:

* `exists_smallEtaleBaseChange_mem_qcqsOverStageObjects`: every point of an object of the small
  étale site of `S` lies in the image of an object `U'` whose base change `U' ×_S X` lies over the
  base change of a quasi-compact and quasi-separated object of a stage `X_j`.
* `isZero_rightDerived_limitMorphism_of_injective`: `R^{q+1} g_* 𝒢 = 0` for a colimit `𝒢` of a
  system of injective sheaves.

## References

* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.LimitHigherDirectImage

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}}
  (γ : DX ⟶ DS) [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)] [∀ i, QuasiCompact (γ.app i)]
  [∀ i, QuasiSeparated (γ.app i)] {cX : Cone DX} {cS : Cone DS} (hcX : IsLimit cX)
  (hcS : IsLimit cS)

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition

include hcX in
omit [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)] in
/-- **The base change to `X` of an object of the small étale site of `S` descended to a stage.**
Let `U'` be an object of the small étale site of `S` which is the base change of an object
`U_j ⟶ S_j` of a stage with quasi-compact and quasi-separated underlying scheme. Then
`U' ×_S X` is the base change of `U_j ×_{S_j} X_j`, an object of the small étale site of `X_j`
with quasi-compact and quasi-separated underlying scheme; in particular it belongs to
`Stacks.EtaleCohomology.qcqsOverStageObjects`. -/
theorem smallEtaleBaseChange_mem_qcqsOverStageObjects_of_isPullback {U' : cS.pt.Etale} {j : Iᵒᵖ}
    {Y : Scheme.{u}} {p : Y ⟶ DS.obj j} [Etale p] [CompactSpace Y] [QuasiSeparatedSpace Y]
    {θ : U'.left ⟶ Y} (hθ : IsPullback θ U'.hom p (cS.π.app j)) :
    (smallEtaleBaseChange (limitMorphism γ cX cS hcS)).obj U' ∈ qcqsOverStageObjects cX := by
  let g := limitMorphism γ cX cS hcS
  let V₀ : (DX.obj j).Etale := (smallEtaleBaseChange (γ.app j)).obj (Scheme.Etale.mk p)
  have : CompactSpace V₀.left :=
    compactSpace_smallEtaleBaseChange_obj (γ.app j) (Scheme.Etale.mk p) ‹CompactSpace Y›
  have : QuasiSeparatedSpace V₀.left :=
    quasiSeparatedSpace_smallEtaleBaseChange_obj (γ.app j) (Scheme.Etale.mk p)
      ‹QuasiSeparatedSpace Y›
  let P := (smallEtaleBaseChange g).obj U'
  have hw : (pullback.fst U'.hom g ≫ θ) ≫ p = (pullback.snd U'.hom g ≫ cX.π.app j) ≫ γ.app j := by
    rw [Category.assoc, hθ.w, ← Category.assoc, pullback.condition, Category.assoc,
      limitMorphism_comp_π, Category.assoc]
  let r : P.left ⟶ V₀.left := pullback.lift _ _ hw
  -- the square presenting `U' ×_S X` as the base change of `V₀`
  have h₁ := (IsPullback.of_hasPullback U'.hom g).paste_horiz hθ
  rw [limitMorphism_comp_π] at h₁
  have e₁ : r ≫ pullback.fst p (γ.app j) = pullback.fst U'.hom g ≫ θ := pullback.lift_fst _ _ _
  have e₂ : r ≫ pullback.snd p (γ.app j) = pullback.snd U'.hom g ≫ cX.π.app j :=
    pullback.lift_snd _ _ _
  have h₂ : IsPullback (r ≫ pullback.fst p (γ.app j)) (pullback.snd U'.hom g) p
      (cX.π.app j ≫ γ.app j) := by
    rwa [e₁]
  have hP : IsPullback r (pullback.snd U'.hom g) (pullback.snd p (γ.app j)) (cX.π.app j) :=
    IsPullback.of_right h₂ e₂ (IsPullback.of_hasPullback p (γ.app j))
  let Q := (smallEtaleBaseChange (cX.π.app j)).obj V₀
  have hV : Q ∈ qcqsEtaleObjects cX.pt := mem_qcqsEtaleObjects_smallEtaleBaseChange_obj cX hcX V₀
  have : CompactSpace Q.left := hV.1
  have : QuasiSeparatedSpace Q.left := hV.2
  let e : P.left ≅ Q.left := hP.isoPullback
  refine ⟨⟨e.inv.homeomorph.compactSpace,
    (quasiSeparatedSpace_congr e.hom.homeomorph).mpr inferInstance⟩,
    j, V₀, ⟨inferInstance, inferInstance⟩, ⟨smallEtaleBaseChangeHomMk (cX.π.app j) r e₂⟩⟩

include hcX in
/-- **Objects of the small étale site of `S` whose base change to `X` lies over a quasi-compact
quasi-separated object of a stage cover.** Every point of an object `U` of the small étale site
of `S` lies in the image of a morphism `U' ⟶ U` such that `U' ×_S X` belongs to
`Stacks.EtaleCohomology.qcqsOverStageObjects`. The object `U'` is an affine open of `U` which
descends to a stage (`AlgebraicGeometry.exists_isAffineOpen_isPullback_etale_of_isLimit`), and
`smallEtaleBaseChange_mem_qcqsOverStageObjects_of_isPullback` applies. -/
theorem exists_smallEtaleBaseChange_mem_qcqsOverStageObjects (U : cS.pt.Etale) (x : U.left) :
    ∃ (U' : cS.pt.Etale) (f : U' ⟶ U), x ∈ Set.range f.left ∧
      (smallEtaleBaseChange (limitMorphism γ cX cS hcS)).obj U' ∈ qcqsOverStageObjects cX := by
  have : Etale U.hom := U.prop
  obtain ⟨U'', -, hxU'', j, Y, p, θ, hp, hYc, hYs, hθ⟩ :=
    exists_isAffineOpen_isPullback_etale_of_isLimit DS cS hcS U.hom x
  have : Etale p := hp
  let U' : cS.pt.Etale := Scheme.Etale.mk (U''.ι ≫ U.hom)
  let f : U' ⟶ U := MorphismProperty.Over.homMk U''.ι rfl trivial
  refine ⟨U', f, ?_, smallEtaleBaseChange_mem_qcqsOverStageObjects_of_isPullback γ hcX hcS hθ⟩
  change x ∈ Set.range U''.ι
  rwa [Scheme.Opens.range_ι]

include hcX in
/-- **The higher direct images along the limit vanish on the colimit of a system of injective
sheaves** (the step of the first proof of [Stacks, Tag 0EYM] for a system of injective sheaves).
Let `g_i : X_i ⟶ S_i` be quasi-compact and quasi-separated with affine transition morphisms, `g`
the limit morphism, and `𝒢 = colim f_i⁻¹𝒢_i` with every `𝒢_i` injective. Then
`R^{q+1} g_* 𝒢 = 0`. -/
theorem isZero_rightDerived_limitMorphism_of_injective (G : EtaleSheafSystem DX Ab.{u + 1})
    [∀ i, Injective (G.obj i)] {𝓖 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1}}
    (ιG : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (G.obj i) ⟶ 𝓖)
    (hιG : IsPullbackCocone cX G ιG) (hG : IsPullbackColimitPresentation cX 𝓖 G ιG) (q : ℕ) :
    IsZero
      (((smallEtalePushforwardAb (limitMorphism γ cX cS hcS)).rightDerived (q + 1)).obj 𝓖) := by
  let u := smallEtaleBaseChange (limitMorphism γ cX cS hcS)
  let P := ((Stacks.Cohomology.SheafifiedHigherDirectImage.pushforwardCohomologyPresheaf
    (K := smallEtaleTopology cX.pt) Ab.{u + 1} u).rightDerived (q + 1)).obj 𝓖
  refine IsZero.of_iso ?_ ((Stacks.Cohomology.SheafifiedHigherDirectImage.rightDerivedPushforwardIso
    (J := smallEtaleTopology cS.pt) (K := smallEtaleTopology cX.pt) Ab.{u + 1} u (q + 1)).app 𝓖)
  refine Stacks.Cohomology.SheafifiedHigherDirectImage.isZero_presheafToSheaf_of_locallyZero
    (smallEtaleTopology cS.pt) P fun U x ↦ ?_
  have hzero : ∀ U' : cS.pt.Etale, u.obj U' ∈ qcqsOverStageObjects cX →
      IsZero (P.obj (op U')) := fun U' hU' ↦
    IsZero.of_iso (EtaleSheafSystem.isZero_rightDerived_sheafSections_of_injective hcX G ιG hιG hG
      hU' q)
      ((Stacks.Cohomology.SheafifiedHigherDirectImage.pushforwardCohomologyPresheafEvaluationIso
        (K := smallEtaleTopology cX.pt) Ab.{u + 1} u (q + 1) U').app 𝓖).symm
  choose U' f hx hU' using exists_smallEtaleBaseChange_mem_qcqsOverStageObjects γ hcX hcS U
  refine (smallEtaleTopology cS.pt).superset_covering ?_
    ((Scheme.ofArrows_mem_smallEtaleTopology_iff f).2
      (Set.eq_univ_of_forall fun y ↦ Set.mem_iUnion.2 ⟨y, hx y⟩))
  refine (Sieve.generate_le_iff _ _).2 ?_
  rintro V g ⟨y⟩
  have := AddCommGrpCat.isZero_iff_subsingleton.mp (hzero (U' y) (hU' y))
  exact Subsingleton.elim _ _

end Stacks.EtaleCohomology.LimitHigherDirectImage
