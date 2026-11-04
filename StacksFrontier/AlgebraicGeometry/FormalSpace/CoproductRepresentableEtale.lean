module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactSpaceCriteriaRefined
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproductSpaceRefined
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedCoproductSummand
public import StacksFrontier.CategoryTheory.Sites.InfinitaryExtensive

/-!
# A morphism out of a finite coproduct of fppf sheaves is representable étale summand by summand

Let `S` be a scheme contained in a big fppf site `B` and let `g i : Z i ⟶ W` be finitely many
morphisms of fppf sheaves over `S`, each representable by algebraic spaces and étale. This file
proves that the induced morphism `∐ Z ⟶ W` is again representable by algebraic spaces and
étale, which is the assertion
`AlgebraicGeometry.FormalSpace.CoproductsRepresentableEtale` consumed by the implication
(2) ⇒ (3) of **Stacks 0AJ9**. Nothing is assumed of the summands beyond the sheaf condition:
they need not be affine formal, or formal, algebraic spaces.

Everything rests on one decomposition. A base change of `∐ Z ⟶ W` along a scheme-valued point
`ξ : h_T ⟶ W` is the coproduct, in sheaves, of the base changes of the `g i`
(`AlgebraicGeometry.FormalSpace.exists_cofan_pullback_sigmaDesc`), because coproducts of
sheaves of sets are universal colimits. The summands of that coproduct are algebraic spaces by
hypothesis, so:

* the base change itself is an algebraic space, by **Stacks 02WQ** in the value universe
  `Type (u + 1)` where formal algebraic spaces live
  (`AlgebraicGeometry.Space.isAlgebraicSpaceULift_coproduct`), the atlases of the summands
  having a coproduct inside the site because the index type is finite;
* its summand inclusions are representable by open immersions, by **Stacks 0F15** in that
  value universe (`AlgebraicGeometry.Space.relative_isOpenImmersion_coproductIncl`). An étale
  chart `h_U ⟶ T ×_W ∐ Z` is therefore cut into clopen pieces, one for each summand, each
  étale over `T` by the hypothesis on that summand; and étaleness is local on the source.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_cofan_pullback_sigmaDesc`: the base change of
  `∐ Z ⟶ W` along a scheme-valued point of `W`, decomposed as the coproduct of the base
  changes of the summands.
* `AlgebraicGeometry.FormalSpace.isRepresentableByAlgebraicSpacesULift_sigmaDesc` and
  `AlgebraicGeometry.FormalSpace.isEtaleULift_pullback_fst_sigmaDesc`: the two halves,
  representability by algebraic spaces and étaleness.
* `AlgebraicGeometry.FormalSpace.coproductsRepresentableEtale`: the assertion
  `AlgebraicGeometry.FormalSpace.CoproductsRepresentableEtale`.

## Implementation notes

The decomposition is formed in the category of fppf sheaves, where the coproduct lives and
where universality of coproducts is available, and is carried over to presheaves — which is
where `AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpacesULift` and
`AlgebraicGeometry.Space.IsEtaleULift` are stated — by
`AlgebraicGeometry.isPullback_sheaf_of_hom'` and `AlgebraicGeometry.isPullback_hom_of_sheaf'`.
The scheme-valued point is read as a morphism out of
`CategoryTheory.GrothendieckTopology.uliftYoneda`, whose underlying presheaf is the
universe-lifted Yoneda presheaf on the nose, so no comparison isomorphism intervenes.

The clopen decomposition of the étale chart is *not* the `Type u`-only machinery of
`StacksFrontier/AlgebraicGeometry/Spaces/FiniteCoproductSpace.lean`: the sheaves here take values
in `Type (u + 1)`. It is the universality of coproducts of sheaves of sets at an arbitrary
value universe (`CategoryTheory.Sheaf.nonempty_isColimit_cofanMk_of_isPullback`) together with
Stacks 0F15 in that universe, which is available for a coproduct of *algebraic spaces* because
those have pointwise `u`-small sections.

No `@[stacks]` registration is made: see
`AlgebraicGeometry.FormalSpace.coproductsRepresentableEtale`.

## References

* [Stacks Project, Tag 0AJ9](https://stacks.math.columbia.edu/tag/0AJ9)
* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 0F15](https://stacks.math.columbia.edu/tag/0F15)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The base change of a morphism out of a finite coproduct of fppf sheaves along a
scheme-valued point of its target, decomposed summand by summand. -/
theorem exists_cofan_pullback_sigmaDesc {I : Type (u + 1)} [Finite I]
    (Z : I → FppfSheaf B S hS) (W : FppfSheaf B S hS) (g : ∀ i, Z i ⟶ W)
    (T : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj T ⟶ W.obj) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    letI : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
    ∃ (A : FppfSheaf B S hS) (Ai : I → FppfSheaf B S hS) (ιA : ∀ i, Ai i ⟶ A)
      (qA : A.obj ⟶ (uliftYoneda.{u + 1}).obj T)
      (rA : A ⟶ ∐ Z)
      (rAi : ∀ i, Ai i ⟶ Z i),
      Nonempty (IsColimit (Cofan.mk A ιA)) ∧
        IsPullback qA rA.hom ξ (Sigma.desc g).hom ∧
        ∀ i, IsPullback ((ιA i).hom ≫ qA) (rAi i).hom ξ (g i).hom := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let J := BigFppfOver.topology B S hS
  let Tsh := J.uliftYoneda.{u + 1}.obj T
  let ξ' : Tsh ⟶ W := ⟨ξ⟩
  let u : (∐ Z) ⟶ W := Sigma.desc g
  have hApb : IsPullback (pullback.fst u ξ') (pullback.snd u ξ') u ξ' :=
    IsPullback.of_hasPullback u ξ'
  let t := pullback.fst u ξ'
  refine ⟨pullback u ξ', fun i ↦ pullback (Sigma.ι Z i) t,
    fun i ↦ pullback.snd (Sigma.ι Z i) t, (pullback.snd u ξ').hom, pullback.fst u ξ',
    fun i ↦ pullback.fst (Sigma.ι Z i) t,
    ⟨Sheaf.isColimitCofanMkPullback J (Sigma.ι Z) (coproductIsCoproduct Z) t⟩,
    isPullback_hom_of_sheaf' hApb.flip, fun i ↦ ?_⟩
  have hp : IsPullback (pullback.snd (Sigma.ι Z i) t ≫ pullback.snd u ξ')
      (pullback.fst (Sigma.ι Z i) t) ξ' (Sigma.ι Z i ≫ u) :=
    (IsPullback.of_hasPullback (Sigma.ι Z i) t).flip.paste_horiz hApb.flip
  rw [Sigma.ι_desc] at hp
  exact isPullback_hom_of_sheaf' hp

/-- The summands of a base change of `∐ Z ⟶ W` are algebraic spaces if the `g i` are
representable by algebraic spaces. -/
private theorem isAlgebraicSpaceULift_of_isPullback {I : Type (u + 1)}
    {Z : I → FppfSheaf B S hS} {W : FppfSheaf B S hS} {g : ∀ i, Z i ⟶ W}
    (hrep : ∀ i, Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (g i).hom)
    {Ai : I → FppfSheaf B S hS} {rAi : ∀ i, Ai i ⟶ Z i} {T : BigFppfOver B S hS}
    {ξ : (uliftYoneda.{u + 1}).obj T ⟶ W.obj}
    {qi : ∀ i, (Ai i).obj ⟶ (uliftYoneda.{u + 1}).obj T}
    (hpb : ∀ i, IsPullback (qi i) (rAi i).hom ξ (g i).hom) (i : I) :
    Space.IsAlgebraicSpaceULift.{u + 1} B S hS (Ai i).obj :=
  Space.isAlgebraicSpaceULift_of_iso B S hS (hpb i).isoPullback.symm (hrep i T ξ)

/-- A morphism out of a coproduct of finitely many fppf sheaves is representable by algebraic
spaces as soon as its restriction to every summand is. -/
theorem isRepresentableByAlgebraicSpacesULift_sigmaDesc {I : Type (u + 1)} [Finite I]
    (Z : I → FppfSheaf B S hS) (W : FppfSheaf B S hS) (g : ∀ i, Z i ⟶ W)
    (hrep : ∀ i, Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (g i).hom) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (Sigma.desc g).hom := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let : Small.{u} I := Countable.toSmall.{u} I
  show Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (Sigma.desc g).hom
  intro T ξ
  obtain ⟨A, Ai, ιA, qA, rA, rAi, ⟨hA⟩, hpbA, hpbAi⟩ :=
    exists_cofan_pullback_sigmaDesc B S hS Z W g T ξ
  have hAi := isAlgebraicSpaceULift_of_isPullback B S hS hrep hpbAi
  choose U c hcs hce using fun i ↦ (hAi i).exists_atlas
  exact Space.isAlgebraicSpaceULift_of_iso B S hS hpbA.isoPullback
    (Space.isAlgebraicSpaceULift_coproduct.{u + 1} B S hS hAi ιA hA U c hcs hce
      (BigFppfOver.isColimit_sigmaCofan B S hS U))

/-- A morphism out of a coproduct of finitely many fppf sheaves is étale after every
represented base change as soon as its restriction to every summand is. -/
theorem isEtaleULift_pullback_fst_sigmaDesc {I : Type (u + 1)} [Finite I]
    (Z : I → FppfSheaf B S hS) (W : FppfSheaf B S hS) (g : ∀ i, Z i ⟶ W)
    (hrep : ∀ i, Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (g i).hom)
    (het : ∀ (i : I) (T : BigFppfOver B S hS) (ζ : (uliftYoneda.{u + 1}).obj T ⟶ W.obj),
      Space.IsEtaleULift.{u + 1} B S hS (pullback.fst ζ (g i).hom))
    (T : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj T ⟶ W.obj) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    Space.IsEtaleULift.{u + 1} B S hS (pullback.fst ξ (Sigma.desc g).hom) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let : Small.{u} I := Countable.toSmall.{u} I
  let : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  show Space.IsEtaleULift.{u + 1} B S hS (pullback.fst ξ (Sigma.desc g).hom)
  let J := BigFppfOver.topology B S hS
  let PP := (MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1})
  let : PP.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  obtain ⟨A, Ai, ιA, qA, rA, rAi, ⟨hA⟩, hpbA, hpbAi⟩ :=
    exists_cofan_pullback_sigmaDesc B S hS Z W g T ξ
  have hAi := isAlgebraicSpaceULift_of_isPullback B S hS hrep hpbAi
  have hoi : ∀ i, (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) (ιA i).hom := fun i ↦
    Space.relative_isOpenImmersion_coproductIncl.{u + 1} B S hS hAi ιA hA i
  have key : Space.IsEtaleULift.{u + 1} B S hS qA := by
    intro U₀ φ hφ
    -- the clopen pieces of `U₀` cut out by the summands
    let D : I → BigFppfOver B S hS := fun i ↦ (hoi i).rep.pullback φ
    let α : ∀ i, D i ⟶ U₀ := fun i ↦ (hoi i).rep.snd φ
    have hsq : ∀ i, IsPullback ((hoi i).rep.fst φ) ((uliftYoneda.{u + 1}).map (α i))
        (ιA i).hom φ := fun i ↦ (hoi i).rep.isPullback φ
    -- they exhibit the representable sheaf of `U₀` as the coproduct of theirs
    obtain ⟨hcU⟩ : Nonempty (IsColimit (Cofan.mk (J.uliftYoneda.{u + 1}.obj U₀)
        fun i ↦ J.uliftYoneda.{u + 1}.map (α i))) :=
      Sheaf.nonempty_isColimit_cofanMk_of_isPullback J ιA hA
        (⟨φ⟩ : J.uliftYoneda.{u + 1}.obj U₀ ⟶ A)
        (fun i ↦ J.uliftYoneda.{u + 1}.map (α i))
        (fun i ↦ (⟨(hoi i).rep.fst φ⟩ : J.uliftYoneda.{u + 1}.obj (D i) ⟶ Ai i))
        fun i ↦ isPullback_sheaf_of_hom' (hsq i).flip
    -- hence identify their coproduct inside the site with `U₀`
    let σ : BigFppfOver.sigmaObj B S hS D ⟶ U₀ :=
      Cofan.IsColimit.desc (BigFppfOver.isColimit_sigmaCofan B S hS D) α
    have hσ : ∀ i, BigFppfOver.sigmaIncl B S hS D i ≫ σ = α i := fun i ↦
      Cofan.IsColimit.fac (BigFppfOver.isColimit_sigmaCofan B S hS D) α i
    have hmap : J.uliftYoneda.{u + 1}.map σ =
        ((BigFppfOver.isColimitUliftYonedaSigmaCofan B S hS D).coconePointUniqueUpToIso
          hcU).hom := by
      refine Cofan.IsColimit.hom_ext
        (BigFppfOver.isColimitUliftYonedaSigmaCofan B S hS D) _ _ fun i ↦ ?_
      simp only [Cofan.inj]
      rw [IsColimit.comp_coconePointUniqueUpToIso_hom]
      simp only [Cofan.mk_ι_app]
      rw [← Functor.map_comp, hσ]
    have : IsIso (J.uliftYoneda.{u + 1}.map σ) := by rw [hmap]; infer_instance
    have : IsIso σ :=
      Functor.FullyFaithful.isIso_of_isIso_map J.fullyFaithfulUliftYoneda.{u + 1} σ
    -- each piece is étale over `T`, by the hypothesis on the corresponding summand
    obtain ⟨ψ, hψ⟩ :=
      (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).map_surjective (φ ≫ qA)
    have hpiece : ∀ i, AlgebraicGeometry.Etale
        ((BigFppfOver.toScheme B S hS).map (α i ≫ ψ)) := by
      intro i
      have hβ : PP ((hoi i).rep.fst φ) :=
        MorphismProperty.IsStableUnderBaseChange.of_isPullback (hsq i).flip hφ
      have hβ' : PP ((hoi i).rep.fst φ ≫ (hpbAi i).isoPullback.hom) :=
        MorphismProperty.RespectsIso.postcomp PP (hpbAi i).isoPullback.hom _ hβ
      have hcomp := het i T ξ (D i) ((hoi i).rep.fst φ ≫ (hpbAi i).isoPullback.hom) hβ'
      rw [Category.assoc, (hpbAi i).isoPullback_hom_fst, ← Category.assoc, (hsq i).w,
        Category.assoc, ← hψ, ← Functor.map_comp] at hcomp
      exact (Space.relative_etale_uliftYoneda_map_iff B S hS (α i ≫ ψ)).mp hcomp
    -- étaleness is local on the source, and the pieces cover
    have htot : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (σ ≫ ψ)) := by
      refine etale_toScheme_of_sigmaIncl B S hS D (σ ≫ ψ) fun i ↦ ?_
      rw [← Category.assoc, hσ]
      exact hpiece i
    rw [Functor.map_comp] at htot
    rw [← hψ]
    refine (Space.relative_etale_uliftYoneda_map_iff B S hS ψ).mpr ?_
    exact (MorphismProperty.cancel_left_of_respectsIso
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      ((BigFppfOver.toScheme B S hS).map σ) ((BigFppfOver.toScheme B S hS).map ψ)).mp htot
  have h1 : Space.IsEtaleULift.{u + 1} B S hS
      (hpbA.isoPullback.hom ≫ pullback.fst ξ (Sigma.desc g).hom) := by
    rw [hpbA.isoPullback_hom_fst]
    exact key
  have h2 := isEtaleULift_precomp_iso B S hS hpbA.isoPullback.symm _ h1
  rwa [Iso.symm_hom, Iso.inv_hom_id_assoc] at h2

/-- **A morphism out of a coproduct of finitely many fppf sheaves over `S` is representable by
algebraic spaces and étale as soon as its restriction to every summand is**: the assertion
`AlgebraicGeometry.FormalSpace.CoproductsRepresentableEtale`, which the implication
(2) ⇒ (3) of **Stacks 0AJ9** consumes.

Representability is
`AlgebraicGeometry.FormalSpace.isRepresentableByAlgebraicSpacesULift_sigmaDesc` and étaleness
is `AlgebraicGeometry.FormalSpace.isEtaleULift_pullback_fst_sigmaDesc`.

This carries no `@[stacks]` registration. The Stacks project invokes it inside the proof of
Stacks 0AJ9 as the bare assertion that the morphism from the coproduct of the members of a
finite atlas is representable by algebraic spaces, étale and surjective, with no tag of its
own; the tagged statement is Stacks 0AJ9 itself. -/
theorem coproductsRepresentableEtale : CoproductsRepresentableEtale B S hS := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  intro I Z W g hfinite hg
  let : Finite I := hfinite
  have hrep : ∀ i, Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (g i).hom :=
    fun i ↦ (hg i).choose
  have het : ∀ (i : I) (T : BigFppfOver B S hS)
      (ζ : (uliftYoneda.{u + 1}).obj T ⟶ W.obj),
      Space.IsEtaleULift.{u + 1} B S hS (pullback.fst ζ (g i).hom) :=
    fun i T ζ ↦ (hg i).choose_spec T ζ
  exact ⟨isRepresentableByAlgebraicSpacesULift_sigmaDesc B S hS Z W g hrep,
    fun T ξ ↦ isEtaleULift_pullback_fst_sigmaDesc B S hS Z W g hrep het T ξ⟩

end AlgebraicGeometry.FormalSpace

end
