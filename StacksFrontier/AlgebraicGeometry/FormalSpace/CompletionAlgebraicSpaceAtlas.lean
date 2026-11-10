module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAffineStageAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionDiagonal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFormalAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# The completion of an algebraic space along a closed subset

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an algebraic space over `S` and
let `T ⊆ |X|` be a closed subset. **Stacks 0AIZ** says that the completion `X_{/T}` is a formal
algebraic space, and **Stacks 0AQ1 (2)** that it is locally Noetherian when `X` is. The atlas
argument for both is `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_completionSheaf` and
`AlgebraicGeometry.FormalSpace.isLocallyNoetherian_completionSheaf`, which take the affine étale
charts of `X`, their closed point sets, the stage atlases of the affine case and the
set-theoretic condition of Stacks 0AIS as inputs. This file proves all of those inputs, so the
two statements hold under the source's hypotheses alone.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_affine_etale_charts`: an algebraic space has an étale
  covering by affine schemes of the site, of uniformly bounded size, which is jointly surjective
  after the sheafified universe lift (Properties of Spaces, Lemma 03FR / 0BGL).
* `AlgebraicGeometry.FormalSpace.exists_isClosed_preimage_eq_supportedPoints`: on such a chart
  the inverse image of `T` is the set of points supported in a closed subset of the chart.
* `AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_completionSheaf`: the
  set-theoretic condition of Stacks 0AIS holds for `X_{/T}`.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_completionSheaf_of_isClosed`:
  **Stacks 0AIZ**.
* `AlgebraicGeometry.FormalSpace.isLocallyNoetherian_completionSheaf_of_isLocallyNoetherian`:
  **Stacks 0AQ1 (2)**.
* `AlgebraicGeometry.FormalSpace.isLocallyNoetherian_of_isLocallyOfFiniteType`: an algebraic
  space locally of finite type over a locally Noetherian one is locally Noetherian.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpaceCompletionSheaf` and
  `AlgebraicGeometry.FormalSpace.isLocallyNoetherianCompletionSheaf`: the two completion
  hypotheses `IsFormalAlgebraicSpaceCompletionSheaf` and `IsLocallyNoetherianCompletionSheaf`
  of the arrow of Stacks 0AR5 (`AlgebraicGeometry.FormalSpace.completionOfFiniteTypeModification`
  and `AlgebraicGeometry.FormalSpace.completionFiniteTypeModificationFunctor`) hold, the second
  for an algebraic space `X`. The third hypothesis of those, the reduction of Stacks 0AR2 to the
  affine case, is not addressed here.

## Implementation notes

*The charts.* The field `exists_atlas` of `AlgebraicGeometry.IsAlgebraicSpace` gives a
surjective étale `h_{U₀} ⟶ X` with `U₀` an object of the site; the charts are `Spec Γ(U₀, W)`
over the affine opens `W` of `U₀`, mapped to `X` through `U₀`. Their joint surjectivity after
the sheafified universe lift is the composite of three local surjections: the universe-lifted
Yoneda images of a Zariski covering
(`GrothendieckTopology.ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map`),
the universe lift of `h_{U₀} ⟶ X` (`AlgebraicGeometry.isLocallySurjective_of_surjective_etale`)
and the sheafification map.

*The set-theoretic condition.* The source does not discuss it, and it is not a formal
consequence of the atlas, whose index is not countable. What makes it hold is a uniform size
bound. Each chart completion is the colimit of the quotient stages `Spec (A_k ⧸ J)`, whose
coproduct is an object `V_k` of the site of size at most `max ℵ₀ (2 ^ #A_k)`; the number of
charts and every `#A_k` are bounded by the size of `U₀`, so the `V_k` are bounded by `2 ^ size U₀`,
which is below the cutoff since the cutoff is a strong prelimit, and their coproduct `W` is again
an object of the site (`AlgebraicGeometry.BigFppfOver.exists_isColimitUliftYoneda_of_size_le`).
`h_W ⟶ X_{/T}` is surjective because each `h_{V_k}` surjects onto its chart completion and the
chart completions cover `X_{/T}`. For the relation, `X_{/T} ⟶ X` is a monomorphism, so the
kernel pair of `h_W ⟶ X_{/T}` is that of `h_W ⟶ X`, which is represented by an object of the
site because the diagonal of `X` is representable. No cofinality bound on the cutoff is used.

## References

* [Stacks Project, Tag 0AIZ](https://stacks.math.columbia.edu/tag/0AIZ)
* [Stacks Project, Tag 0AQ1](https://stacks.math.columbia.edu/tag/0AQ1)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AIY](https://stacks.math.columbia.edu/tag/0AIY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Raising the universe of the values of presheaves of types preserves local surjectivity:
the image sieve of a lifted section is the image sieve of the section. -/
private theorem isLocallySurjective_whiskerRight_uliftFunctor
    {C : Type*} [Category* C] (J : GrothendieckTopology C) {F G : Cᵒᵖ ⥤ Type u} (f : F ⟶ G)
    [Presheaf.IsLocallySurjective J f] :
    Presheaf.IsLocallySurjective J (Functor.whiskerRight f uliftFunctor.{u + 1}) where
  imageSieve_mem {U} s := by
    obtain ⟨s⟩ := s
    refine J.superset_covering ?_ (Presheaf.imageSieve_mem J f (U := op U) s)
    rintro V g ⟨t, ht⟩
    exact ⟨ULift.up t, congrArg ULift.up ht⟩

/-- The sheafified universe lifts of the composites of a covering family `ι i : C i ⟶ U₀` of
the site with a locally surjective morphism `p : h_{U₀} ⟶ X` are jointly surjective. -/
private theorem isLocallySurjective_sigmaDesc_sheafifiedULiftMap
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U₀ : BigFppfOver B S hS} (p : yoneda.obj U₀ ⟶ X)
    (hp : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) p)
    {K : Type (u + 1)} {C : K → BigFppfOver B S hS} (ι : ∀ i, C i ⟶ U₀)
    (hsieve : Sieve.ofArrows C ι ∈ BigFppfOver.topology B S hS U₀) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
      Sheaf.instHasColimitsOfSize;
    Sheaf.IsLocallySurjective
      (Sigma.desc fun i ↦ Space.sheafifiedULiftMap B S hS (yoneda.map (ι i) ≫ p)) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have h₀' : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Sigma.desc fun i ↦ uliftYoneda.{u + 1}.map (ι i)) :=
    (GrothendieckTopology.ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map _ ι).1
      hsieve
  have h₀ : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Sigma.desc fun i ↦ Functor.whiskerRight (yoneda.map (ι i)) uliftFunctor.{u + 1}) := h₀'
  have h₁ : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Functor.whiskerRight p uliftFunctor.{u + 1}) :=
    isLocallySurjective_whiskerRight_uliftFunctor _ p
  let G : K → FppfSheaf B S hS := fun i ↦ Space.sheafifiedULift B S hS (yoneda.obj (C i))
  let d : (∐ fun i ↦ yoneda.obj (C i) ⋙ uliftFunctor.{u + 1}) ⟶ (∐ G).obj :=
    Sigma.desc fun i ↦ (BigFppfOver.topology B S hS).toSheafify
      (yoneda.obj (C i) ⋙ uliftFunctor.{u + 1}) ≫ (Sigma.ι G i).hom
  have hfac : d ≫ (Sigma.desc fun i ↦
        Space.sheafifiedULiftMap B S hS (yoneda.map (ι i) ≫ p)).hom =
      (Sigma.desc fun i ↦ Functor.whiskerRight (yoneda.map (ι i)) uliftFunctor.{u + 1}) ≫
        Functor.whiskerRight p uliftFunctor.{u + 1} ≫
          (BigFppfOver.topology B S hS).toSheafify (X ⋙ uliftFunctor.{u + 1}) := by
    refine Sigma.hom_ext _ _ fun i ↦ ?_
    let JJ := BigFppfOver.topology B S hS
    have hG : (Sigma.ι G i).hom ≫ (Sigma.desc fun i ↦
          Space.sheafifiedULiftMap B S hS (yoneda.map (ι i) ≫ p)).hom =
        (Space.sheafifiedULiftMap B S hS (yoneda.map (ι i) ≫ p)).hom := by
      rw [← ObjectProperty.FullSubcategory.comp_hom, Sigma.ι_comp_desc]
    have hL : Sigma.ι (fun i ↦ yoneda.obj (C i) ⋙ uliftFunctor.{u + 1}) i ≫ d =
        JJ.toSheafify (yoneda.obj (C i) ⋙ uliftFunctor.{u + 1}) ≫ (Sigma.ι G i).hom :=
      Sigma.ι_comp_desc _ i
    have hR : Sigma.ι (fun i ↦ yoneda.obj (C i) ⋙ uliftFunctor.{u + 1}) i ≫
        (Sigma.desc fun i ↦ Functor.whiskerRight (yoneda.map (ι i)) uliftFunctor.{u + 1}) =
          Functor.whiskerRight (yoneda.map (ι i)) uliftFunctor.{u + 1} :=
      Sigma.ι_comp_desc _ i
    have e₁ : Sigma.ι (fun i ↦ yoneda.obj (C i) ⋙ uliftFunctor.{u + 1}) i ≫ d ≫
          (Sigma.desc fun i ↦ Space.sheafifiedULiftMap B S hS (yoneda.map (ι i) ≫ p)).hom =
        (JJ.toSheafify (yoneda.obj (C i) ⋙ uliftFunctor.{u + 1}) ≫ (Sigma.ι G i).hom) ≫
          (Sigma.desc fun i ↦ Space.sheafifiedULiftMap B S hS (yoneda.map (ι i) ≫ p)).hom :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hL)
    have e₂ : (JJ.toSheafify (yoneda.obj (C i) ⋙ uliftFunctor.{u + 1}) ≫ (Sigma.ι G i).hom) ≫
          (Sigma.desc fun i ↦ Space.sheafifiedULiftMap B S hS (yoneda.map (ι i) ≫ p)).hom =
        JJ.toSheafify (yoneda.obj (C i) ⋙ uliftFunctor.{u + 1}) ≫
          (Space.sheafifiedULiftMap B S hS (yoneda.map (ι i) ≫ p)).hom :=
      (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hG)
    have e₃ : JJ.toSheafify (yoneda.obj (C i) ⋙ uliftFunctor.{u + 1}) ≫
          (Space.sheafifiedULiftMap B S hS (yoneda.map (ι i) ≫ p)).hom =
        Functor.whiskerRight (yoneda.map (ι i) ≫ p) uliftFunctor.{u + 1} ≫
          JJ.toSheafify (X ⋙ uliftFunctor.{u + 1}) :=
      (GrothendieckTopology.toSheafify_naturality JJ _).symm
    have e₄ : Functor.whiskerRight (yoneda.map (ι i) ≫ p) uliftFunctor.{u + 1} ≫
          JJ.toSheafify (X ⋙ uliftFunctor.{u + 1}) =
        Sigma.ι (fun i ↦ yoneda.obj (C i) ⋙ uliftFunctor.{u + 1}) i ≫
          (Sigma.desc fun i ↦ Functor.whiskerRight (yoneda.map (ι i)) uliftFunctor.{u + 1}) ≫
            Functor.whiskerRight p uliftFunctor.{u + 1} ≫
              JJ.toSheafify (X ⋙ uliftFunctor.{u + 1}) :=
      ((congrArg (· ≫ _) (Functor.whiskerRight_comp _ _ _)).trans (Category.assoc _ _ _)).trans
        ((congrArg (· ≫ _) hR.symm).trans (Category.assoc _ _ _))
    exact e₁.trans (e₂.trans (e₃.trans e₄))
  have h₂ : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      ((BigFppfOver.topology B S hS).toSheafify (X ⋙ uliftFunctor.{u + 1})) :=
    Presheaf.isLocallySurjective_toSheafify _ _
  have h₁₂ := @Presheaf.isLocallySurjective_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂
  have h₀₁₂ := @Presheaf.isLocallySurjective_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₀ h₁₂
  exact @Presheaf.isLocallySurjective_of_isLocallySurjective_fac _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hfac h₀₁₂

/-- **An algebraic space has an affine étale atlas, read in the value universe of the formal
algebraic spaces.** For an algebraic space `X` over `S` there are an object `U₀` of the site and
affine schemes `Spec A_k` of the site, indexed by a type of cardinality at most the size of
`U₀` and each of size at most that of `U₀`, with étale morphisms `a_k : Spec A_k ⟶ X` whose
sheafified universe lifts are jointly surjective.

The charts are the spectra of the rings of sections over the affine opens of the scheme of an
étale atlas `U₀ ⟶ X`, which is what the field `exists_atlas` of an algebraic space provides;
this is the source's appeal to Properties of Spaces, Lemma 03FR / 0BGL. -/
theorem exists_affine_etale_charts {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) :
    ∃ (U₀ : BigFppfOver B S hS) (K : Type u) (A : K → Type u) (_ : ∀ k, CommRing (A k))
      (hA : ∀ k, B.Contains (Spec (.of (A k)))) (str : ∀ k, Spec (.of (A k)) ⟶ S)
      (a : ∀ k, yoneda.obj (affineOver B S hS (hA k) (str k)) ⟶ X),
      #K ≤ ((BigFppfOver.toScheme B S hS).obj U₀).size ∧
      (∀ k, (Spec (.of (A k))).size ≤ ((BigFppfOver.toScheme B S hS).obj U₀).size) ∧
      (∀ k, Space.IsEtale B S hS (a k)) ∧
      (letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
          Sheaf.instHasColimitsOfSize;
        Sheaf.IsLocallySurjective
          (Sigma.desc fun (i : ULift.{u + 1} K) ↦
            Space.sheafifiedULiftMap B S hS (a i.down))) := by
  classical
  obtain ⟨U₀, p, hps, hpe⟩ := hX.exists_atlas
  let Y := (BigFppfOver.toScheme B S hS).obj U₀
  let K := Y.affineOpens
  let A : K → Type u := fun W ↦ Γ(Y, W.1)
  have hopen : ∀ W : K, IsOpenImmersion (W.2.fromSpec : Spec (.of (A W)) ⟶ Y) := fun W ↦
    IsAffineOpen.isOpenImmersion_fromSpec W.2
  have hA : ∀ W : K, B.Contains (Spec (.of (A W))) := fun W ↦
    Scheme.size_lt_of_isOpenImmersion (W.2.fromSpec : Spec (.of (A W)) ⟶ Y) U₀.left.property
  let str : ∀ W : K, Spec (.of (A W)) ⟶ S := fun W ↦ W.2.fromSpec ≫ B.inclusion.map U₀.hom
  let ι : ∀ W : K, affineOver B S hS (hA W) (str W) ⟶ U₀ := fun W ↦
    Over.homMk (ObjectProperty.homMk W.2.fromSpec) rfl
  have hιmap : ∀ W, (BigFppfOver.toScheme B S hS).map (ι W) = W.2.fromSpec := fun W ↦ rfl
  let a : ∀ W : K, yoneda.obj (affineOver B S hS (hA W) (str W)) ⟶ X := fun W ↦
    yoneda.map (ι W) ≫ p
  have hιet : ∀ W, Space.IsEtale B S hS (yoneda.map (ι W)) := fun W ↦
    (Space.isEtale_iff_presheaf_of_yoneda B S hS _).2
      ((Space.presheaf_yoneda_map_etale_iff B S hS (ι W)).2 (by
        have := hopen W
        exact (inferInstance : Etale (W.2.fromSpec : Spec (.of (A W)) ⟶ Y))))
  have hpet : Space.IsEtale B S hS p := (Space.isEtale_iff_presheaf_of_yoneda B S hS p).2 hpe
  refine ⟨U₀, K, A, inferInstance, hA, str, a, Y.mk_affineOpens_le_size, fun W ↦ ?_,
    fun W ↦ Space.isEtale_comp B S hS (hιet W) hpet, ?_⟩
  · exact (Scheme.size_congr W.2.isoSpec).symm.trans_le (Y.size_coe_opens_le W.1)
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let J := BigFppfOver.topology B S hS
  let C : ULift.{u + 1} K → BigFppfOver B S hS := fun i ↦
    affineOver B S hS (hA i.down) (str i.down)
  have hcovx : ∀ x : (BigFppfOver.toScheme B S hS).obj U₀,
      ∃ i : ULift.{u + 1} K, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (ι i.down)) := by
    intro x
    obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := x) (U := ⊤)
      trivial
    refine ⟨ULift.up ⟨W, hW⟩, ?_⟩
    rw [hιmap]
    exact (Set.ext_iff.mp hW.range_fromSpec x).mpr hxW
  have hopen' : ∀ i : ULift.{u + 1} K,
      IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (ι i.down)) := fun i ↦ hopen i.down
  have hsieve : Sieve.ofArrows C (fun i ↦ ι i.down) ∈ J U₀ :=
    BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS (T := U₀) (X := C)
      (fun i ↦ ι i.down) hopen' hcovx
  have hpls : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) p :=
    isLocallySurjective_of_surjective_etale B S hS p hps hpe
  exact isLocallySurjective_sigmaDesc_sheafifiedULiftMap (K := ULift.{u + 1} K) (C := C) p hpls
    (fun i ↦ ι i.down) hsieve


/-! ### The set-theoretic condition -/

/-- **The set-theoretic condition of Stacks 0AIS for a subsheaf of an algebraic space.** Let
`Z` be an fppf sheaf over `S` with a monomorphism into the universe lift of an algebraic space
`X`, and let `h_V ⟶ Z` be a surjection from the sheaf represented by an object `V` of the site.
Then `Z` satisfies the set-theoretic condition: the kernel pair of `h_V ⟶ Z` is the kernel pair
of `h_V ⟶ X`, `Z ⟶ X` being a monomorphism, and that is represented by an object `R` of the
site because the diagonal of `X` is representable. -/
theorem satisfiesSetTheoreticCondition_of_isAlgebraicSpace_of_mono_of_epi
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X) {Z : FppfSheaf B S hS}
    (m : Z ⟶ Space.sheafifiedULift B S hS X) [Mono m] (V : BigFppfOver B S hS)
    (q : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj V ⟶ Z) [Epi q] :
    SatisfiesSetTheoreticCondition B S hS Z := by
  classical
  let J := BigFppfOver.topology B S hS
  let _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have hF : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (X ⋙ uliftFunctor.{u + 1}) :=
    (Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS X).2 hX
  let eX : X ⋙ uliftFunctor.{u + 1} ≅ (Space.sheafifiedULift B S hS X).obj :=
    J.isoSheafify hF.isSheaf
  let eV : (J.uliftYoneda.{u + 1}.obj V).obj ≅ uliftYoneda.{u + 1}.obj V :=
    J.uliftYonedaCompSheafToPresheaf.app V
  let h : uliftYoneda.{u + 1}.obj V ⟶ X ⋙ uliftFunctor.{u + 1} :=
    eV.inv ≫ (q ≫ m).hom ≫ eX.inv
  obtain ⟨R, snd, fst, hpb⟩ := hF.diagonal_representable.of_diag h h
  have hsq : IsPullback ((pullback.fst (q ≫ m) (q ≫ m)).hom ≫ eV.hom)
      ((pullback.snd (q ≫ m) (q ≫ m)).hom ≫ eV.hom) h h :=
    ((IsPullback.of_hasPullback (q ≫ m) (q ≫ m)).map (sheafToPresheaf J (Type (u + 1)))).of_iso
      (Iso.refl _) eV eV eX.symm (by simp) (by simp) (by simp [h]) (by simp [h])
  let k : pullback q q ⟶ pullback (q ≫ m) (q ≫ m) :=
    pullback.lift (pullback.fst q q) (pullback.snd q q) (by
      rw [← Category.assoc, pullback.condition, Category.assoc])
  let g : pullback (q ≫ m) (q ≫ m) ⟶ pullback q q :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by
      rw [← cancel_mono m, Category.assoc, Category.assoc]
      exact pullback.condition)
  have hkg : k ≫ g = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]
  have : IsSplitEpi g := ⟨⟨k, hkg⟩⟩
  exact ⟨V, R, J.uliftYoneda.{u + 1}.obj V, pullback (q ≫ m) (q ≫ m), ⟨eV⟩,
    ⟨hsq.isoIsPullback _ _ hpb⟩, q, inferInstance, g, IsSplitEpi.epi g⟩

/-- The completions of the members of a jointly surjective family of morphisms into `X` along
the inverse images of a set `T` of points are jointly surjective onto `X_{/T}`: the completion
squares of Stacks 0APV exhibit them as the base changes of the family along `X_{/T} ⟶ X`. -/
theorem epi_sigmaDesc_completionSheafMap {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) {Ix : Type (u + 1)}
    {Y : Ix → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : ∀ i, Y i ⟶ X)
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize;
      Sheaf.IsLocallySurjective (Sigma.desc fun i ↦ Space.sheafifiedULiftMap B S hS (a i))) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize;
    Epi (Sigma.desc fun i ↦ Space.completionSheafMap B S hS (a i) T) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  set φ := Space.completionSheafInclusion B S hS X T with hφ
  set ψ := fun i ↦ Space.sheafifiedULiftMap B S hS (a i) with hψ
  have hbase : Sheaf.IsLocallySurjective (Sigma.desc fun i ↦ pullback.snd (ψ i) φ) :=
    Sheaf.isLocallySurjective_sigmaDesc_pullback_snd φ ψ hcov
  let e : ∀ i, Space.completionSheaf B S hS (Y i) (Space.pointsMap B S hS _ (a i) ⁻¹' T) ≅
      pullback (ψ i) φ := fun i ↦
    (Space.isPullback_completionSheafMap B S hS (a i) T).isoPullback
  let t : (∐ fun i ↦ Space.completionSheaf B S hS (Y i)
        (Space.pointsMap B S hS _ (a i) ⁻¹' T)) ⟶ (∐ fun i ↦ pullback (ψ i) φ) :=
    Sigma.desc fun i ↦ (e i).hom ≫ Sigma.ι (fun j ↦ pullback (ψ j) φ) i
  have hts : IsSplitEpi t :=
    ⟨⟨Sigma.desc fun i ↦ (e i).inv ≫ Sigma.ι
        (fun j ↦ Space.completionSheaf B S hS (Y j)
          (Space.pointsMap B S hS _ (a j) ⁻¹' T)) i, by
      apply Sigma.hom_ext
      intro i
      simp [t]⟩⟩
  have hfac : (Sigma.desc fun i ↦ Space.completionSheafMap B S hS (a i) T) =
      t ≫ Sigma.desc fun i ↦ pullback.snd (ψ i) φ := by
    apply Sigma.hom_ext
    intro i
    simp only [t, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, Category.assoc]
    exact ((Space.isPullback_completionSheafMap B S hS (a i) T).isoPullback_hom_snd).symm
  rw [hfac]
  exact epi_comp' (IsSplitEpi.epi t) ((Sheaf.isLocallySurjective_iff_epi _).mp hbase)

attribute [local instance] Space.pointTopology in
/-- The inverse image of a closed set of points under a morphism from a represented presheaf is
the set of points supported in a closed subset of the representing scheme. -/
theorem exists_isClosed_preimage_eq_supportedPoints {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : Set (Space.points B S hS X)} (hT : IsClosed T) {U : BigFppfOver B S hS}
    (a : yoneda.obj U ⟶ X) :
    ∃ T' : Set ((BigFppfOver.toScheme B S hS).obj U), IsClosed T' ∧
      Space.pointsMap B S hS _ a ⁻¹' T = supportedPoints B S hS U T' := by
  let e := Space.schemePointsHomeomorph B S hS U
  refine ⟨e '' (Space.pointsMap B S hS _ a ⁻¹' T),
    e.isClosed_image.2 (hT.preimage (Space.continuous_pointsMap B S hS a)), ?_⟩
  ext x
  exact (e.injective.mem_set_image (a := x)).symm

/-- A map out of a coproduct `∐ P k` is an epimorphism when it restricts to `q k ≫ g k` on each
summand, with `q k` epimorphisms and the `g k` jointly epimorphic. -/
private theorem epi_cofanIsColimitDesc_comp {K : Type u} {P Zk : K → FppfSheaf B S hS}
    {Z : FppfSheaf B S hS} {c : Cofan P} (hc : IsColimit c) (q : ∀ k, P k ⟶ Zk k)
    [∀ k, Epi (q k)] (g : ∀ k, Zk k ⟶ Z)
    (hg : ∀ {Z' : FppfSheaf B S hS} (g₁ g₂ : Z ⟶ Z'), (∀ k, g k ≫ g₁ = g k ≫ g₂) → g₁ = g₂) :
    Epi (Cofan.IsColimit.desc hc fun k ↦ q k ≫ g k) := by
  refine ⟨fun {Z'} g₁ g₂ h ↦ hg _ _ fun k ↦ ?_⟩
  rw [← cancel_epi (q k)]
  have h' := congrArg (c.inj k ≫ ·) h
  simpa only [← Category.assoc, Cofan.IsColimit.fac] using h'

attribute [local instance] sheaf_hasColimits in
/-- **A surjection onto the completion of an affine scheme from one object of the site.** The
coproduct of the quotient stages `Spec (A ⧸ J)`, over the ideals with zero locus `V(I)`, is an
object `V` of the site of size at most `max ℵ₀ (2 ^ #A)`, and its representable sheaf surjects
onto the completion along `V(I)`, which is the colimit of the stages. -/
theorem exists_epi_uliftYoneda_zeroLocusCompletion {A : Type u} [CommRing A]
    (hA : B.Contains (Spec (.of A))) (f : Spec (.of A) ⟶ S) (I : Ideal A) :
    ∃ (V : BigFppfOver B S hS),
      ((BigFppfOver.toScheme B S hS).obj V).size ≤ max ℵ₀ (2 ^ #A) ∧
      ∃ q : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj V ⟶
        zeroLocusCompletion B S hS hA f I, Epi q := by
  classical
  let J := BigFppfOver.topology B S hS
  let Xs : SupportIdeal I → BigFppfOver B S hS := fun K ↦
    (BigAffineFppf.inclusion B S hS).obj (supportStage B S hS hA f I K)
  have hAc : #A < B.cutoff := by
    have h : (Spec (.of A)).size < B.cutoff := hA
    rw [Scheme.size_Spec] at h
    exact (le_max_right _ _).trans_lt h
  set μ : Cardinal.{u} := max ℵ₀ (2 ^ #A) with hμdef
  have hμ : μ < B.cutoff := max_lt B.aleph0_lt_cutoff (B.cutoff_isStrongPrelimit hAc)
  have hι : #(SupportIdeal I) ≤ μ :=
    calc #(SupportIdeal I) ≤ #(Ideal A) := mk_subtype_le _
      _ ≤ #(Set A) := mk_le_of_injective (f := fun K : Ideal A => (K : Set A))
          SetLike.coe_injective
      _ = 2 ^ #A := mk_set
      _ ≤ μ := le_max_right _ _
  have hX : ∀ K, ((BigFppfOver.toScheme B S hS).obj (Xs K)).size ≤ μ := by
    intro K
    change (Spec (.of (A ⧸ K.1))).size ≤ μ
    rw [Scheme.size_Spec]
    exact max_le (le_max_left _ _)
      (mk_quotient_le.trans ((Cardinal.cantor _).le.trans (le_max_right _ _)))
  obtain ⟨V, j, -, -, ⟨hj⟩, -, ⟨hV⟩⟩ :=
    BigFppfOver.exists_isColimitUliftYoneda_of_size_le B S hS Xs hμ hι hX
  have hVsize : ((BigFppfOver.toScheme B S hS).obj V).size ≤ μ :=
    (Scheme.size_congr ((coproductIsCoproduct _).coconePointUniqueUpToIso hj)).symm.trans_le
      ((schemeSize_coproduct_le _ (max μ ℵ₀) (le_max_right _ _)
        (hι.trans (le_max_left _ _)) fun K ↦ (hX K).trans (le_max_left _ _)).trans
          (max_le le_rfl (le_max_left _ _)))
  let eH : J.uliftYoneda.{u + 1} ≅ Sheaf.sheafifiedYoneda J :=
    (Sheaf.sheafifiedYonedaIsoUliftYoneda' J).symm
  have := isIso_supportComparison B S hS hA f I
  refine ⟨V, hVsize, _, epi_cofanIsColimitDesc_comp hV (fun K ↦ eH.hom.app (Xs K))
    (fun K ↦ colimit.ι (supportSheafDiagram B S hS hA f I) (ULift.up K) ≫
      supportComparison B S hS hA f I) fun g₁ g₂ hk ↦ ?_⟩
  rw [← cancel_epi (supportComparison B S hS hA f I)]
  exact colimit.hom_ext fun jj ↦ by
    rw [← Category.assoc, ← Category.assoc]
    exact hk (OrderDual.ofDual jj.down)

/-- **Gluing surjections from objects of the site.** Let `q_k : h_{V_k} ⟶ Z_k` be surjections
from the representable sheaves of objects of the site and `g_k : Z_k ⟶ Z` jointly surjective,
with the index and the `V_k` bounded by one cardinal below the cutoff. Then some object `W` of
the site has its representable sheaf surjecting onto `Z`, namely the coproduct of the `V_k`. -/
theorem exists_epi_uliftYoneda_of_jointly_epi {K : Type u} (V : K → BigFppfOver B S hS)
    {ν : Cardinal.{u}} (hν : ν < B.cutoff) (hK : #K ≤ ν)
    (hV : ∀ k, ((BigFppfOver.toScheme B S hS).obj (V k)).size ≤ ν)
    {Zk : K → FppfSheaf B S hS} {Z : FppfSheaf B S hS}
    (q : ∀ k, (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj (V k) ⟶ Zk k)
    [∀ k, Epi (q k)] (g : ∀ k, Zk k ⟶ Z)
    (hg : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize;
      Epi (Sigma.desc fun i : ULift.{u + 1} K ↦ g i.down)) :
    ∃ (W : BigFppfOver B S hS)
      (p : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj W ⟶ Z), Epi p := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨W, j, -, -, -, -, ⟨hW⟩⟩ :=
    BigFppfOver.exists_isColimitUliftYoneda_of_size_le B S hS V hν hK hV
  refine ⟨W, _, epi_cofanIsColimitDesc_comp hW q g fun g₁ g₂ hk ↦ ?_⟩
  exact (cancel_epi (Sigma.desc fun i : ULift.{u + 1} K ↦ g i.down)).mp
    (Sigma.hom_ext _ _ fun i ↦ by simpa using hk i.down)

/-- **The set-theoretic condition of Stacks 0AIS for the completion of an algebraic space along a
closed subset.** Let `X` be an algebraic space over `S` and `T ⊆ |X|` closed. Then `X_{/T}`
satisfies the set-theoretic condition.

The surjection from a representable sheaf is assembled from the stage atlases of the affine
charts: for an étale atlas `U₀ ⟶ X` and the affine opens `Spec A_k` of `U₀`, the quotient spectra
`Spec (A_k ⧸ J)`, over the ideals `J` cutting out the inverse image of `T`, glue to one object
`V_k` of the site surjecting onto the chart completion
(`AlgebraicGeometry.FormalSpace.exists_epi_uliftYoneda_zeroLocusCompletion`); the `V_k` are
uniformly bounded by `2 ^ size U₀`, so they glue in turn to one object `W` of the site
(`AlgebraicGeometry.FormalSpace.exists_epi_uliftYoneda_of_jointly_epi`), the chart completions
covering `X_{/T}` (`AlgebraicGeometry.FormalSpace.epi_sigmaDesc_completionSheafMap`). The
relation is then supplied by
`satisfiesSetTheoreticCondition_of_isAlgebraicSpace_of_mono_of_epi`. -/
theorem satisfiesSetTheoreticCondition_completionSheaf {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (T : Set (Space.points B S hS X))
    (hT : @IsClosed _ (Space.pointTopology B S hS X) T) :
    SatisfiesSetTheoreticCondition B S hS (Space.completionSheaf B S hS X T) := by
  classical
  obtain ⟨U₀, K, A, _, hA, str, a, hK, hAsize, -, hcov⟩ := exists_affine_etale_charts hX
  choose Ti hTi hTpts using fun k ↦ exists_isClosed_preimage_eq_supportedPoints hT (a k)
  have hP : ∀ k, Space.pointsMap B S hS _ (a k) ⁻¹' T =
      zeroLocusPoints B S hS (hA k) (str k) (PrimeSpectrum.vanishingIdeal (Ti k)) := fun k ↦
    (hTpts k).trans ((congrArg (supportedPoints B S hS (affineOver B S hS (hA k) (str k)))
      ((hTi k).closure_eq.symm.trans
        (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure (Ti k)).symm)).trans
      (supportedPoints_zeroLocus B S hS (hA k) (str k) _))
  choose V hVsize q hq using fun k ↦ exists_epi_uliftYoneda_zeroLocusCompletion (hA k) (str k)
    (PrimeSpectrum.vanishingIdeal (Ti k))
  set μ : Cardinal.{u} := ((BigFppfOver.toScheme B S hS).obj U₀).size with hμ
  have hμ0 : ℵ₀ ≤ μ := Scheme.aleph0_le_size _
  have hμν : μ ≤ 2 ^ μ := (Cardinal.cantor μ).le
  have hAk : ∀ k, #(A k) ≤ μ := fun k ↦ by
    have h := hAsize k
    rw [Scheme.size_Spec] at h
    exact (le_max_right _ _).trans h
  have hVν : ∀ k, ((BigFppfOver.toScheme B S hS).obj (V k)).size ≤ 2 ^ μ := fun k ↦
    (hVsize k).trans (max_le (hμ0.trans hμν)
      (Cardinal.power_le_power_left two_ne_zero (hAk k)))
  let ψ : ∀ k, zeroLocusCompletion B S hS (hA k) (str k) (PrimeSpectrum.vanishingIdeal (Ti k)) ⟶
      Space.completionSheaf B S hS X T := fun k ↦
    eqToHom (congrArg (Space.completionSheaf B S hS _) (hP k).symm) ≫
      Space.completionSheafMap B S hS (a k) T
  have hψ : let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize;
      Epi (Sigma.desc fun i : ULift.{u + 1} K ↦ ψ i.down) := by
    let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    have hatlas := epi_sigmaDesc_completionSheafMap T (fun i : ULift.{u + 1} K ↦ a i.down) hcov
    have hfac : (Sigma.desc fun i : ULift.{u + 1} K ↦ ψ i.down) =
        (Limits.Sigma.map fun i : ULift.{u + 1} K ↦
          eqToHom (congrArg (Space.completionSheaf B S hS _) (hP i.down).symm)) ≫
        Sigma.desc fun i : ULift.{u + 1} K ↦ Space.completionSheafMap B S hS (a i.down) T := by
      apply Sigma.hom_ext
      intro i
      simp [ψ]
    rw [hfac]
    infer_instance
  obtain ⟨W, p, hp⟩ := exists_epi_uliftYoneda_of_jointly_epi V
    (B.cutoff_isStrongPrelimit U₀.left.property) (hK.trans hμν) hVν q ψ hψ
  have := Space.mono_completionSheafInclusion B S hS X T
  exact satisfiesSetTheoreticCondition_of_isAlgebraicSpace_of_mono_of_epi hX
    (Space.completionSheafInclusion B S hS X T) W p

/-! ### Stacks 0AIZ and Stacks 0AQ1 (2) -/

/-- **Stacks 0AIZ.** Let `S` be a scheme, let `X` be an algebraic space over `S` and let
`T ⊆ |X|` be a closed subset. The completion `X_{/T}` of `X` along `T` — the fppf sheaf attached
to the functor sending `U` to the morphisms `f : U ⟶ X` with `f(|U|) ⊆ T` — is a formal
algebraic space over `S`.

The affine étale charts of `X` are those of
`AlgebraicGeometry.FormalSpace.exists_affine_etale_charts`, the inverse image of `T` on each is
the set of points supported in a closed subset
(`AlgebraicGeometry.FormalSpace.exists_isClosed_preimage_eq_supportedPoints`), the stage atlas
of each chart completion is `AlgebraicGeometry.FormalSpace.hasStageAtlas`, and the set-theoretic
condition is `AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_completionSheaf`;
with these the atlas argument of
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_completionSheaf` applies. -/
@[stacks 0AIZ]
theorem isFormalAlgebraicSpace_completionSheaf_of_isClosed
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X)) (hT : @IsClosed _ (Space.pointTopology B S hS X) T) :
    IsFormalAlgebraicSpace B S hS (Space.completionSheaf B S hS X T) := by
  obtain ⟨U₀, K, A, _, hA, str, a, -, -, het, hcov⟩ := exists_affine_etale_charts hX
  choose Ti hTi hTpts using fun k ↦ exists_isClosed_preimage_eq_supportedPoints hT (a k)
  exact isFormalAlgebraicSpace_completionSheaf hX T (Ix := ULift.{u + 1} K)
    (A := fun i ↦ A i.down) (fun i ↦ hA i.down) (fun i ↦ str i.down) (fun i ↦ a i.down)
    (fun i ↦ exists_hasPropertyULift_sheafifiedULiftMap_of_isEtale B S hS
      (isAlgebraicSpace_yoneda B S hS _) hX (a i.down) (het i.down))
    hcov (fun i ↦ Ti i.down) (fun i ↦ hTi i.down) (fun i ↦ hTpts i.down)
    (fun i ↦ hasStageAtlas B S hS (hA i.down) (str i.down) _)
    (satisfiesSetTheoreticCondition_completionSheaf hX T hT)

/-- **Stacks 0AQ1, part (2).** Let `S` be a scheme, let `X` be a locally Noetherian algebraic
space over `S` and let `T ⊆ |X|` be a closed subset. The completion `X_{/T}` of `X` along `T` is
locally Noetherian.

The affine étale charts `Spec A_k ⟶ X` of
`AlgebraicGeometry.FormalSpace.exists_affine_etale_charts` are étale over the locally Noetherian
`X`, so each `Spec A_k` is locally Noetherian and each `A_k` is a Noetherian ring; the
set-theoretic condition is
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_completionSheaf`. With these the
atlas argument of `AlgebraicGeometry.FormalSpace.isLocallyNoetherian_completionSheaf`
applies. -/
@[stacks 0AQ1 "part (2)"]
theorem isLocallyNoetherian_completionSheaf_of_isLocallyNoetherian
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXN : Space.IsLocallyNoetherian B S hS X)
    (T : Set (Space.points B S hS X)) (hT : @IsClosed _ (Space.pointTopology B S hS X) T) :
    IsLocallyNoetherian B S hS (Space.completionSheaf B S hS X T) := by
  obtain ⟨U₀, K, A, _, hA, str, a, -, -, het, hcov⟩ := exists_affine_etale_charts hX
  have hNoeth : ∀ k, IsNoetherianRing (A k) := fun k ↦ by
    have hloc : _root_.AlgebraicGeometry.IsLocallyNoetherian (Spec (.of (A k))) :=
      hXN (affineOver B S hS (hA k) (str k)) (a k) (het k)
    have : _root_.AlgebraicGeometry.IsNoetherian (Spec (.of (A k))) := ⟨⟩
    exact isNoetherian_Spec.mp this
  exact isLocallyNoetherian_completionSheaf hX T hT (Ix := ULift.{u + 1} K)
    (A := fun i ↦ A i.down) (fun i ↦ hNoeth i.down) (fun i ↦ hA i.down) (fun i ↦ str i.down)
    (fun i ↦ a i.down)
    (fun i ↦ exists_hasPropertyULift_sheafifiedULiftMap_of_isEtale B S hS
      (isAlgebraicSpace_yoneda B S hS _) hX (a i.down) (het i.down))
    hcov (satisfiesSetTheoreticCondition_completionSheaf hX T hT)

/-! ### The two completion hypotheses of Stacks 0AR5 -/

/-- An algebraic space locally of finite type over a locally Noetherian algebraic space is locally
Noetherian, in the sense of `AlgebraicGeometry.Space.IsLocallyNoetherian`: every scheme étale over
it is locally Noetherian.

The base change `P = U_Z ×_X U_X` of étale scheme atlases of `Z` and `X` is surjective étale over
`Z` and locally of finite type over the locally Noetherian `U_X`, hence locally Noetherian
(`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`); local Noetherianity being étale
local, it then holds on every scheme étale over `Z` (Stacks 03E8,
`AlgebraicGeometry.Space.exists_atlas_iff_forall_etale`). -/
theorem isLocallyNoetherian_of_isLocallyOfFiniteType
    {Z X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z)
    (hX : IsAlgebraicSpace B S hS X) (h : Z ⟶ X) (hh : Space.IsLocallyOfFiniteType B S hS h)
    (hXN : Space.IsLocallyNoetherian B S hS X) : Space.IsLocallyNoetherian B S hS Z := by
  obtain ⟨UZ, a, has, hae⟩ := hZ.exists_atlas
  obtain ⟨UX, b, hbs, hbe⟩ := hX.exists_atlas
  let hrep := hbs.1
  let g : yoneda.obj UZ ⟶ X := a ≫ h
  let P := hrep.pullback g
  let q := hrep.snd g
  let fst := hrep.fst g
  have hpb := hrep.isPullback g
  have hqs : Surjective ((BigFppfOver.toScheme B S hS).map q) := hbs.2 g fst q hpb
  have hqe : Etale ((BigFppfOver.toScheme B S hS).map q) := hbe.2 g fst q hpb
  let r : P ⟶ UX := yoneda.preimage fst
  have hmulS := Space.isMultiplicative_presheaf_surjective B S hS
  have hmulE := Space.isMultiplicative_presheaf_etale B S hS
  have hfs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map q ≫ a) :=
    MorphismProperty.comp_mem _ _ _
      ((Space.presheaf_yoneda_map_iff B S hS inferInstance q).2 hqs) has
  have hfe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map q ≫ a) :=
    MorphismProperty.comp_mem _ _ _ ((Space.presheaf_yoneda_map_etale_iff B S hS q).2 hqe) hae
  have hUX : _root_.AlgebraicGeometry.IsLocallyNoetherian
      ((BigFppfOver.toScheme B S hS).obj UX) :=
    hXN UX b ((Space.isEtale_iff_presheaf_of_yoneda B S hS b).2 hbe)
  have hr : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map r) := by
    refine hh P UX (yoneda.map q ≫ a) b r hfe hbe ?_
    rw [Functor.map_preimage, Category.assoc]
    exact hpb.w
  have hP : _root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj P) :=
    LocallyOfFiniteType.isLocallyNoetherian ((BigFppfOver.toScheme B S hS).map r)
  have hall := (Space.exists_atlas_iff_forall_etale B S hS Z
    (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian T) hZ).mp
    ⟨P, yoneda.map q ≫ a, hfs, hfe, hP⟩
  exact fun W w hw ↦ hall W w ((Space.isEtale_iff_presheaf_of_yoneda B S hS w).1 hw)

attribute [local instance] Space.pointTopology in
/-- The first completion hypothesis of Stacks 0AR5,
`AlgebraicGeometry.FormalSpace.IsFormalAlgebraicSpaceCompletionSheaf`, holds for every presheaf
`X` and set of points `T`: it is Stacks 0AIZ for the algebraic spaces over `X`, the inverse
image of a closed set of points being closed. -/
theorem isFormalAlgebraicSpaceCompletionSheaf (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (T : Set (Space.points B S hS X)) : IsFormalAlgebraicSpaceCompletionSheaf B S hS X T :=
  fun hT _ h hZ ↦ isFormalAlgebraicSpace_completionSheaf_of_isClosed hZ _
    (hT.preimage (Space.continuous_pointsMap B S hS h))

attribute [local instance] Space.pointTopology in
/-- The second completion hypothesis of Stacks 0AR5,
`AlgebraicGeometry.FormalSpace.IsLocallyNoetherianCompletionSheaf`, holds for every algebraic
space `X` and set of points `T`: an algebraic space locally of finite type over the locally
Noetherian `X` is locally Noetherian
(`AlgebraicGeometry.FormalSpace.isLocallyNoetherian_of_isLocallyOfFiniteType`), so its completion
along the closed inverse image of `T` is locally Noetherian by Stacks 0AQ1 (2). -/
theorem isLocallyNoetherianCompletionSheaf {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (T : Set (Space.points B S hS X)) :
    IsLocallyNoetherianCompletionSheaf B S hS X T :=
  fun hT hXN _ h hZ hh ↦ isLocallyNoetherian_completionSheaf_of_isLocallyNoetherian hZ
    (isLocallyNoetherian_of_isLocallyOfFiniteType hZ hX h hh hXN) _
    (hT.preimage (Space.continuous_pointsMap B S hS h))

end AlgebraicGeometry.FormalSpace

end
