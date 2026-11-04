module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.DescendedScheme
public import StacksFrontier.AlgebraicGeometry.Etale.FpqcDescentApplication.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperFiniteCase
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite étale schemes over a henselian pair, and open and closed immersions by descent

Let `(A, I)` be a henselian pair and let `f : X ⟶ Spec A` be finite, with closed fibre `Y ⟶ X`.
Two schemes finite étale over `X` and an isomorphism of their restrictions to `Y` over `Y` are
joined by exactly one morphism over `X` restricting to that isomorphism, and it is an isomorphism.

Universal injectivity descends along a surjective base change. Since an étale morphism is an open
immersion exactly when it is universally injective (Tag 02LC), a morphism of étale schemes over a
base is an open and closed immersion as soon as its base change along a surjective closed morphism
is an open immersion with closed image.

For a descent datum relative to `f : X ⟶ S` with scheme `V`, a morphism `ρ : V ⟶ U` that restricts
on each member of a cover of `V` by invariant opens to the projection of a scheme descending the
restricted datum, followed by a morphism to `U`, equalises the two legs of the gluing isomorphism;
together with a cartesian square this makes `U` a descended scheme of the datum.

## Main definitions

* `AlgebraicGeometry.DescentDatum.descendedOfIsOpenCover`: the descended scheme given by a cover
  of `V` by invariant opens and a cartesian square.

## Main results

* `Stacks.Etale.exists_isIso_of_isFinite_of_henselianPair`: over a henselian pair, a scheme finite
  étale over a finite `X` is determined, together with the identification, by its closed fibre.
* `Stacks.Etale.universallyInjective_of_surjective_baseChange`: universal injectivity descends
  along a surjective base change.
* `Stacks.Etale.isOpenImmersion_isClosedImmersion_of_surjective_baseChange`: a morphism of étale
  schemes over a base whose base change along a surjective closed morphism is an open immersion
  with closed image is an open and closed immersion.
* `AlgebraicGeometry.DescentDatum.proj_invariant_of_isOpenCover`: a morphism out of `V` which is a
  descended projection on each member of a cover of `V` by invariant opens equalises the two legs
  of the gluing isomorphism.

## References

* [Stacks Project, Tag 02LC](https://stacks.math.columbia.edu/tag/02LC)
* [Stacks Project, Tag 09ZS](https://stacks.math.columbia.edu/tag/09ZS)
* [Stacks Project, Tag 0GS2](https://stacks.math.columbia.edu/tag/0GS2)
* [Stacks Project, Tag 0BTN](https://stacks.math.columbia.edu/tag/0BTN)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public noncomputable section

universe u

namespace Stacks.Etale

open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits

/-- **Over a henselian pair, a finite étale scheme is determined, together with the
identification, by its closed fibre.** Let `(A, I)` be a henselian pair, let `f : X ⟶ Spec A` be
finite, and let `y : Y ⟶ X` be the closed fibre of `f`, named by a cartesian square over
`Spec (A ⧸ I) ⟶ Spec A`. Given two schemes `P` and `Q` finite étale over `X` and an isomorphism
`ψ` of their restrictions to `Y` over `Y`, there is exactly one morphism `φ : P ⟶ Q` over `X`
whose restriction to `Y` is `ψ`, and it is an isomorphism. -/
theorem exists_isIso_of_isFinite_of_henselianPair
    {A : Type u} [CommRing A] {I : Ideal A} (hI : HenselianPair A I)
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsFinite f]
    (y : Y ⟶ X) (yq : Y ⟶ Spec (.of (A ⧸ I)))
    (hY : IsPullback y yq f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
    {P Q : Scheme.{u}} (p : P ⟶ X) (q : Q ⟶ X)
    [IsFinite p] [Etale p] [IsFinite q] [Etale q]
    (ψ : pullback p y ⟶ pullback q y) [IsIso ψ]
    (hψ : ψ ≫ pullback.snd q y = pullback.snd p y) :
    ∃ φ : P ⟶ Q, IsIso φ ∧ φ ≫ q = p ∧
      pullback.fst p y ≫ φ = ψ ≫ pullback.fst q y ∧
      ∀ φ' : P ⟶ Q, φ' ≫ q = p →
        pullback.fst p y ≫ φ' = ψ ≫ pullback.fst q y → φ' = φ := by
  have : (finiteEtaleBaseChange y).IsEquivalence := by
    rw [← hY.isoPullback_hom_fst]
    exact isEquivalence_finiteEtaleBaseChange_isIso_comp _ _
      (isEquivalence_finiteEtaleBaseChange_of_isFinite_of_henselianPair A I hI f)
  let F : (finiteEtaleBaseChange y).FullyFaithful := .ofFullyFaithful _
  let Pobj : FiniteEtaleOver X := MorphismProperty.Over.mk ⊤ p ⟨inferInstance, inferInstance⟩
  let Qobj : FiniteEtaleOver X := MorphismProperty.Over.mk ⊤ q ⟨inferInstance, inferInstance⟩
  let e : pullback p y ≅ pullback q y := asIso ψ
  let Ψ : (finiteEtaleBaseChange y).obj Pobj ≅ (finiteEtaleBaseChange y).obj Qobj :=
    MorphismProperty.Over.isoMk e hψ
  have key : ∀ Φ : Pobj ⟶ Qobj, pullback.fst p y ≫ Φ.left =
      ((finiteEtaleBaseChange y).map Φ).left ≫ pullback.fst q y :=
    fun Φ ↦ (finiteEtaleBaseChange_map_left_fst y Φ).symm
  have hmap : ((finiteEtaleBaseChange y).map (F.preimageIso Ψ).hom).left = ψ :=
    congrArg (fun k ↦ k.left) (F.map_preimage Ψ.hom)
  refine ⟨(F.preimageIso Ψ).hom.left, ?_, MorphismProperty.Over.w _, ?_, ?_⟩
  · show IsIso ((MorphismProperty.Over.forget (finiteEtale : MorphismProperty Scheme.{u}) ⊤ X ⋙
      CategoryTheory.Over.forget X).map (F.preimageIso Ψ).hom)
    infer_instance
  · exact (key (F.preimageIso Ψ).hom).trans
      (congrArg (fun k : pullback p y ⟶ pullback q y ↦ k ≫ pullback.fst q y) hmap)
  · intro φ' hφ' hcompat
    let Φ' : Pobj ⟶ Qobj := MorphismProperty.Over.homMk φ' hφ'
    have hΦ' : (finiteEtaleBaseChange y).map Φ' =
        (finiteEtaleBaseChange y).map (F.preimageIso Ψ).hom :=
      finiteEtaleOver_hom_ext y
        (((key Φ').symm.trans hcompat).trans
          (congrArg (fun k : pullback p y ⟶ pullback q y ↦ k ≫ pullback.fst q y) hmap).symm)
    exact congrArg (fun k ↦ k.left) (F.map_injective hΦ')

/-! ### The open and closed immersion produced by full faithfulness -/

/-- A morphism whose base change along a surjective morphism is injective on points is itself
injective on points. -/
@[sga "1 VIII 3.2"]
private theorem injective_of_injective_pullback_snd {A B C : Scheme.{u}} (g : A ⟶ B) (c : C ⟶ B)
    [Surjective c] (h : Function.Injective (pullback.snd g c)) : Function.Injective g := by
  intro a₁ a₂ hga
  obtain ⟨w, hw⟩ := Surjective.surj (f := c) (g a₁)
  obtain ⟨z₁, hz₁a, hz₁w⟩ := Scheme.Pullback.exists_preimage_pullback a₁ w hw.symm
  obtain ⟨z₂, hz₂a, hz₂w⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := g) (g := c) a₂ w (by rw [← hga]; exact hw.symm)
  have hz : z₁ = z₂ := h (by rw [hz₁w, hz₂w])
  rw [← hz₁a, ← hz₂a, hz]

/-- **Universal injectivity descends along a surjective base change.** If the square
`IsPullback a φ' φ b` is cartesian, `b` is surjective and `φ'` is universally injective, then `φ`
is universally injective. -/
@[ega "IV 2.6.1"]
theorem universallyInjective_of_surjective_baseChange {P Q P' Q' : Scheme.{u}} {φ : P ⟶ Q}
    {φ' : P' ⟶ Q'} {a : P' ⟶ P} {b : Q' ⟶ Q} [Surjective b] [UniversallyInjective φ']
    (h : IsPullback a φ' φ b) : UniversallyInjective φ := by
  constructor
  intro P'' Q'' i₁ i₂ φ'' hsq
  have hc : Surjective (pullback.fst i₂ b) :=
    MorphismProperty.of_isPullback (P := @Surjective) (IsPullback.of_hasPullback i₂ b).flip ‹_›
  have hpaste : IsPullback (pullback.fst φ'' (pullback.fst i₂ b) ≫ i₁)
      (pullback.snd φ'' (pullback.fst i₂ b)) φ (pullback.snd i₂ b ≫ b) := by
    have hp := (IsPullback.of_hasPullback φ'' (pullback.fst i₂ b)).paste_horiz hsq.flip
    rwa [pullback.condition (f := i₂) (g := b)] at hp
  exact injective_of_injective_pullback_snd φ'' (pullback.fst i₂ b)
    (UniversallyInjective.universally_injective (f := φ') _ _ _
      (IsPullback.of_right' hpaste h).flip)

/-- Let `P` and `Q` be étale over `S` and let `φ : P ⟶ Q` be a morphism over `S` whose base
change `φ'` along a surjective morphism `b` with closed underlying map is an open immersion with
closed image. Then `φ` is an open and closed immersion. -/
theorem isOpenImmersion_isClosedImmersion_of_surjective_baseChange {S P Q P' Q' : Scheme.{u}}
    {p : P ⟶ S} {q : Q ⟶ S} [Etale p] [Etale q] (φ : P ⟶ Q) (hφ : φ ≫ q = p)
    {φ' : P' ⟶ Q'} {a : P' ⟶ P} {b : Q' ⟶ Q} [Surjective b] [IsOpenImmersion φ']
    (hb : IsClosedMap b) (hcl : IsClosed (Set.range φ')) (h : IsPullback a φ' φ b) :
    IsOpenImmersion φ ∧ IsClosedImmersion φ := by
  have hcomp : Etale (φ ≫ q) := by rw [hφ]; infer_instance
  have hetale : Etale φ :=
    MorphismProperty.of_postcomp @Etale (W' := @Etale) φ q inferInstance hcomp
  have hui : UniversallyInjective φ := universallyInjective_of_surjective_baseChange h
  have _ : Surjective a := MorphismProperty.of_isPullback (P := @Surjective) h.flip ‹_›
  have hrange : Set.range φ = b '' Set.range φ' := by
    rw [← range_eq_range_of_surjective (a ≫ φ) φ a rfl, h.w, Scheme.Hom.comp_base,
      TopCat.coe_comp, Set.range_comp]
  have hopen : IsOpenImmersion φ := isOpenImmersion_of_etale_universallyInjective φ
  exact ⟨hopen, IsClosedImmersion.of_isPreimmersion φ (hrange ▸ hb _ hcl)⟩

end Stacks.Etale

/-! ### The descended scheme of a cover by invariant opens -/

namespace AlgebraicGeometry.DescentDatum

open CategoryTheory CategoryTheory.Limits

variable {S X : Scheme.{u}} {f : X ⟶ S} {D : DescentDatum f}

attribute [local implicit_reducible] restrictOpen

/-- The part of `V ×_S X` lying over an invariant open `W` of `V`, mapped to the fibre product
of `W` with `X` over `S`. -/
private def openSourcePart (W : D.over.left.Opens) (hW : D.IsTransitionInvariant W) :
    (pullback.fst (D.over.hom ≫ f) f ⁻¹ᵁ W).toScheme ⟶
      pullback ((D.restrictOpen W hW).over.hom ≫ f) f :=
  pullback.lift (pullback.fst (D.over.hom ≫ f) f ∣_ W)
    ((pullback.fst (D.over.hom ≫ f) f ⁻¹ᵁ W).ι ≫ pullback.snd (D.over.hom ≫ f) f)
    (by
      change (pullback.fst (D.over.hom ≫ f) f ∣_ W) ≫ (W.ι ≫ D.over.hom) ≫ f =
        ((pullback.fst (D.over.hom ≫ f) f ⁻¹ᵁ W).ι ≫ pullback.snd (D.over.hom ≫ f) f) ≫ f
      rw [Category.assoc, ← Category.assoc ((pullback.fst (D.over.hom ≫ f) f) ∣_ W),
        morphismRestrict_ι, Category.assoc, Category.assoc, pullback.condition])

/-- The part of `V ×_S X` lying over an invariant open factors through the base change of the
inclusion of that open. -/
private lemma openSourcePart_comp_homSourceMap (W : D.over.left.Opens)
    (hW : D.IsTransitionInvariant W) :
    openSourcePart W hW ≫ homSourceMap (D.restrictOpenHom W hW) =
      (pullback.fst (D.over.hom ≫ f) f ⁻¹ᵁ W).ι := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, homSourceMap_comp_fst, restrictOpenHom_hom_left, openSourcePart,
      ← Category.assoc, pullback.lift_fst, morphismRestrict_ι]
  · rw [Category.assoc, pullback.lift_snd, Category.comp_id, openSourcePart, pullback.lift_snd]

/-- If `ρ` restricts on an invariant open `W` to the projection of a scheme `Q` descending the
restricted datum followed by `c`, then the two legs of the gluing isomorphism followed by `ρ`
agree on the part of `V ×_S X` lying over `W`. -/
private lemma homSourceMap_comp_invariant {U : Scheme.{u}} (W : D.over.left.Opens)
    (hW : D.IsTransitionInvariant W) (Q : (D.restrictOpen W hW).Descended) (c : Q.base.left ⟶ U)
    (ρ : D.over.left ⟶ U) (hρ : W.ι ≫ ρ = Q.proj ≫ c) :
    homSourceMap (D.restrictOpenHom W hW) ≫
        D.transitionPullbackIso.hom ≫ pullback.snd f (D.over.hom ≫ f) ≫ ρ =
      homSourceMap (D.restrictOpenHom W hW) ≫ pullback.fst (D.over.hom ≫ f) f ≫ ρ := by
  rw [← Category.assoc, transitionPullbackIso_naturality, Category.assoc,
    homTargetMap_comp_snd_assoc, homSourceMap_comp_fst_assoc, restrictOpenHom_hom_left, hρ,
    reassoc_of% Q.proj_invariant]

/-- **A morphism out of `V` which is a descended projection on each member of a cover of `V` by
invariant opens equalises the two legs of the gluing isomorphism.** Here `ρ` restricted to the
`i`-th member `W i` is the projection of a scheme `Q i` descending the restricted datum followed by
an arbitrary morphism `c i` to `U`. -/
theorem proj_invariant_of_isOpenCover {U : Scheme.{u}} {ι : Type u}
    {W : ι → D.over.left.Opens} (hcov : TopologicalSpace.IsOpenCover W)
    (hinv : ∀ i, D.IsTransitionInvariant (W i))
    (Q : ∀ i, (D.restrictOpen (W i) (hinv i)).Descended) (c : ∀ i, (Q i).base.left ⟶ U)
    (ρ : D.over.left ⟶ U) (hρ : ∀ i, (W i).ι ≫ ρ = (Q i).proj ≫ c i) :
    D.transitionPullbackIso.hom ≫ pullback.snd f (D.over.hom ≫ f) ≫ ρ =
      pullback.fst (D.over.hom ≫ f) f ≫ ρ := by
  refine Scheme.Cover.hom_ext
    ((pullback (D.over.hom ≫ f) f).openCoverOfIsOpenCover
      (fun i ↦ pullback.fst (D.over.hom ≫ f) f ⁻¹ᵁ W i)
      (TopologicalSpace.IsOpenCover.mk (by
        rw [← Scheme.Hom.preimage_iSup, hcov.iSup_eq_top, Scheme.Hom.preimage_top])))
    _ _ fun (i : ι) ↦ ?_
  show (pullback.fst (D.over.hom ≫ f) f ⁻¹ᵁ W i).ι ≫ _ =
    (pullback.fst (D.over.hom ≫ f) f ⁻¹ᵁ W i).ι ≫ _
  rw [← openSourcePart_comp_homSourceMap (W i) (hinv i), Category.assoc, Category.assoc,
    homSourceMap_comp_invariant (W i) (hinv i) (Q i) (c i) ρ (hρ i)]

/-- **The descended scheme of a cover of `V` by invariant opens.** Given a cover of `V` by
invariant opens, a scheme descending the restriction of the datum to each member, a scheme `U`
over `S` receiving all of them, and a morphism `ρ : V ⟶ U` which exhibits `V` as `U ×_S X` and
restricts on each member to the projection of that member followed by the morphism to `U`, the
datum is descended by `U`. -/
def descendedOfIsOpenCover {U : Over S} {ι : Type u} {W : ι → D.over.left.Opens}
    (hcov : TopologicalSpace.IsOpenCover W) (hinv : ∀ i, D.IsTransitionInvariant (W i))
    (Q : ∀ i, (D.restrictOpen (W i) (hinv i)).Descended) (c : ∀ i, (Q i).base.left ⟶ U.left)
    (ρ : D.over.left ⟶ U.left) (hsq : IsPullback D.over.hom ρ f U.hom)
    (hρ : ∀ i, (W i).ι ≫ ρ = (Q i).proj ≫ c i) : D.Descended where
  base := U
  proj := ρ
  isPullback := hsq
  proj_invariant := proj_invariant_of_isOpenCover hcov hinv Q c ρ hρ

end AlgebraicGeometry.DescentDatum

end
