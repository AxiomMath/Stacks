module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfAlgebraicSpacesCounterexample
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfFormalSpacesCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitStageThickening
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceLocalTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountableAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SetTheoreticSmall
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SurjectiveClosedImmersionAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOfAffineEtaleCover
import all StacksFrontier.AlgebraicGeometry.FormalSpace.CountableAtlas

/-!
# Stacks 0GVN for an index admitting coproducts in the site

Let `(X_λ, f_{λμ})` be a directed system of formal algebraic spaces over `S` whose transition
morphisms are closed immersions inducing isomorphisms on reductions (equivalently, by
Stacks 0GVL, representable thickenings). **Stacks 0GVN** says the colimit is a formal algebraic
space. Its proof never checks clause (4) of Definition 0AIM, the set-theoretic condition of
Remark 0AIS, for the colimit, and Remark 0AIS (1) and (3) say that this condition holds when
the index is "not too large (for example countable)". This module proves the condition for
every index `Λ` admitting coproducts in the site
(`AlgebraicGeometry.BigFppfSite.AdmitsCoproductIndex`,
an index below the cofinality of the size cutoff, which includes every countable index), and with
it the tag in that form; for an arbitrary index it proves the tag provided the colimit satisfies
the condition.

## Main results

* `AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_admissible_cover`: a sheaf
  covered by an admissible family of sheaves satisfying the set-theoretic condition satisfies it,
  provided each kernel-pair piece over a member is dominated by an object of the site. This is
  the argument of `satisfiesSetTheoreticCondition_of_countable_atlas` with the countability used
  only through admissibility of the index.
* `AlgebraicGeometry.FormalSpace.exists_epi_pullback_pullback_snd_colimitι`: those pieces, for
  the stages of a directed colimit of formal algebraic spaces along representable thickenings,
  are represented by objects of the site. The base change of the colimit injection along a point
  is representable (`isRepresentableThickeningULift_colimitι_of_small`), and the relative product
  of two points of a formal algebraic space is representable
  (`essImage_pullback_of_isFormalAlgebraicSpace`, the representability half of Stacks 0AIP).
* `AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_colimit_of_admissible`: **Remark
  0AIS** for such a colimit with an admissible index.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_colimit_closedImmersions_of_admissible`:
  **Stacks 0GVN** for an admissible index.
* `isFormalAlgebraicSpace_of_colimit_closedImmersions_of_satisfiesSetTheoreticCondition`:
  **Stacks 0GVN** for an arbitrary directed index, provided the colimit satisfies the
  set-theoretic condition (the corrected form recorded in the erratum).
* `AlgebraicGeometry.FormalSpace.not_forall_isFormalAlgebraicSpace_colimit_closedImmersions`:
  without a bound on the index the conclusion fails, so the bound is forced.

## References

* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0GVN](https://stacks.math.columbia.edu/tag/0GVN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A coproduct of epimorphisms is an epimorphism. -/
private theorem epi_sigmaDesc_comp_ι {C : Type*} [Category* C] {β : Type*} {f g : β → C}
    [HasCoproduct f] [HasCoproduct g] (p : ∀ i, f i ⟶ g i) (hp : ∀ i, Epi (p i)) :
    Epi (Sigma.desc fun i ↦ p i ≫ Sigma.ι g i) := by
  constructor
  intro Z v w hvw
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  have := hp i
  have h := Sigma.ι f i ≫= hvw
  simp only [← Category.assoc, Sigma.ι_desc] at h
  exact (cancel_epi (p i)).mp (by simpa only [Category.assoc] using h)

/-- The map out of a coproduct presented by a colimit cofan is an epimorphism when the
corresponding map out of `∐ f` is. -/
private theorem epi_isColimit_desc_of_epi_sigmaDesc {C : Type*} [Category* C] {β : Type*}
    {f : β → C} [HasCoproduct f] {c : Cofan f} (hc : IsColimit c) {X : C}
    (φ : ∀ i, f i ⟶ X) (hφ : Epi (Sigma.desc φ)) : Epi (hc.desc (Cofan.mk X φ)) := by
  let e := (coproductIsCoproduct f).coconePointUniqueUpToIso hc
  have het : e.hom ≫ hc.desc (Cofan.mk X φ) = Sigma.desc φ := by
    refine Sigma.hom_ext _ _ fun i ↦ ?_
    have hi : Sigma.ι f i ≫ e.hom = c.ι.app (Discrete.mk i) :=
      IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct f) hc (Discrete.mk i)
    rw [← Category.assoc, hi, hc.fac]
    simp
  have : Epi (e.hom ≫ hc.desc (Cofan.mk X φ)) := by rwa [het]
  exact epi_of_epi e.hom _

/-- **A family of objects of the site dominating a jointly surjective family of sheaves gives one
object of the site dominating the target**: the coproduct of the objects is an object of the site
because the index is admissible. -/
private theorem exists_epi_uliftYoneda_sigmaObj {X : FppfSheaf B S hS}
    {I : Type (u + 1)} [Small.{u} I] [B.AdmitsCoproductIndex I]
    [HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS)] (R : I → BigFppfOver B S hS)
    {Y : I → FppfSheaf B S hS} (b : ∀ i, (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj
      (R i) ⟶ Y i) (hb : ∀ i, Epi (b i)) (c : ∀ i, Y i ⟶ X) (hc : Epi (Sigma.desc c)) :
    ∃ t : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj
      (BigFppfOver.sigmaObj B S hS R) ⟶ X, Epi t := by
  let J := BigFppfOver.topology B S hS
  have hLift : IsColimit (Cofan.mk (J.uliftYoneda.{u + 1}.obj (BigFppfOver.sigmaObj B S hS R))
      fun i ↦ J.uliftYoneda.{u + 1}.map (BigFppfOver.sigmaIncl B S hS R i)) :=
    BigFppfOver.isColimitUliftYonedaSigmaCofan B S hS R
  have hdesc : Epi (Sigma.desc fun i ↦ b i ≫ c i) := by
    have hfac : (Sigma.desc fun i ↦ b i ≫ c i) =
        (Sigma.desc fun i ↦ b i ≫ Sigma.ι Y i) ≫ Sigma.desc c := by
      refine Sigma.hom_ext _ _ fun i ↦ ?_
      simp
    rw [hfac]
    exact @epi_comp _ _ _ _ _ _ (epi_sigmaDesc_comp_ι b hb) _ hc
  exact ⟨_, epi_isColimit_desc_of_epi_sigmaDesc hLift _ hdesc⟩

/-- **A family of sheaves with an admissible index, each dominated by an object of the site and
jointly covering `X`, gives one object of the site dominating `X`**: the coproduct of the
dominating objects is an object of the site because the index is admissible
(`AlgebraicGeometry.BigFppfOver.isColimitUliftYonedaSigmaCofan`). This is
`AlgebraicGeometry.FormalSpace.exists_representable_epi_of_countable_cover`, whose proof uses
countability only to obtain admissibility. -/
theorem exists_representable_epi_of_admissible_cover (X : FppfSheaf B S hS)
    {I : Type (u + 1)} [Small.{u} I] [B.AdmitsCoproductIndex I] (Xi : I → FppfSheaf B S hS)
    (f : ∀ i, Xi i ⟶ X)
    (hXi : ∀ i, SatisfiesSetTheoreticCondition B S hS (Xi i))
    (hcover : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc f)) :
    ∃ (U : BigFppfOver B S hS)
      (t : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U ⟶ X), Epi t := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let J := BigFppfOver.topology B S hS
  let : J.Subcanonical := bigFppfOver_subcanonical B S hS
  -- Each member of the family receives a surjection from an object of the site.
  have hsurj : ∀ i, ∃ (Ui : BigFppfOver B S hS) (b : J.uliftYoneda.{u + 1}.obj Ui ⟶ Xi i),
      Epi b := by
    intro i
    obtain ⟨Ui, -, hU, -, ⟨eU⟩, -, a, ha, -, -⟩ := hXi i
    let eS : J.uliftYoneda.{u + 1}.obj Ui ≅ hU :=
      (fullyFaithfulSheafToPresheaf J (Type (u + 1))).preimageIso
        (J.uliftYonedaCompSheafToPresheaf.{u + 1}.app Ui ≪≫ eU.symm)
    have : Epi a := ha
    exact ⟨Ui, eS.hom ≫ a, epi_comp eS.hom a⟩
  choose Ui b hb using hsurj
  -- The coproduct of the chosen objects is an object of the site, and it dominates `X`.
  obtain ⟨t, ht⟩ := exists_epi_uliftYoneda_sigmaObj B S hS Ui b hb f
    ((Sheaf.isLocallySurjective_iff_epi _).mp hcover)
  exact ⟨_, t, ht⟩

/-- The relation `(T ×_X Y) ×_Y (T ×_X Y)` of `t : T ⟶ X` over `g : Y ⟶ X` is the base change of
the kernel pair `T ×_X T ⟶ X` along `g`. -/
private theorem exists_isPullback_pullback_pullback_snd {X T Y : FppfSheaf B S hS} (t : T ⟶ X)
    (g : Y ⟶ X) :
    ∃ c : pullback (pullback.snd t g) (pullback.snd t g) ⟶ pullback t t,
      IsPullback c (pullback.fst (pullback.snd t g) (pullback.snd t g) ≫ pullback.snd t g)
        (pullback.fst t t ≫ t) g := by
  have hEsq : IsPullback (pullback.fst t t) (pullback.snd t t) t t := IsPullback.of_hasPullback t t
  have hcomm : (pullback.fst (pullback.snd t g) (pullback.snd t g) ≫ pullback.fst t g) ≫ t =
      (pullback.snd (pullback.snd t g) (pullback.snd t g) ≫ pullback.fst t g) ≫ t := by
    have h := (IsPullback.of_hasPullback (pullback.snd t g) (pullback.snd t g)).w =≫ g
    simp only [Category.assoc] at h ⊢
    rw [(IsPullback.of_hasPullback t g).w]
    exact h
  exact ⟨hEsq.lift _ _ hcomm, isPullback_chartRelation (IsPullback.of_hasPullback t g)
    (IsPullback.of_hasPullback _ _) hEsq _ (hEsq.lift_fst _ _ hcomm) (hEsq.lift_snd _ _ hcomm)⟩

/-- **The relations of `t : T ⟶ X` over a jointly surjective family `{Xᵢ ⟶ X}` jointly cover the
kernel pair of `t`**: their coproduct is the base change of `T ×_X T` along `∐ Xᵢ ⟶ X`. -/
private theorem exists_epi_sigmaDesc_pullback_pullback_snd {X T : FppfSheaf B S hS}
    {I : Type (u + 1)} [HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS)]
    (Xi : I → FppfSheaf B S hS) (f : ∀ i, Xi i ⟶ X) (hcover : Epi (Sigma.desc f)) (t : T ⟶ X) :
    ∃ c : ∀ i, pullback (pullback.snd t (f i)) (pullback.snd t (f i)) ⟶ pullback t t,
      Epi (Sigma.desc c) := by
  let J := BigFppfOver.topology B S hS
  have hÊ : IsPullback (pullback.fst (pullback.fst t t ≫ t) (Sigma.desc f))
      (pullback.snd (pullback.fst t t ≫ t) (Sigma.desc f)) (pullback.fst t t ≫ t)
      (Sigma.desc f) := IsPullback.of_hasPullback _ _
  have hê : Epi (pullback.fst (pullback.fst t t ≫ t) (Sigma.desc f)) := by
    rw [← Sheaf.isLocallySurjective_iff_epi]
    exact Presheaf.isLocallySurjective_of_isPullback J
      (hÊ.map (sheafToPresheaf J (Type (u + 1))))
      (hf := (Sheaf.isLocallySurjective_iff_epi _).mpr hcover)
  choose c hc using fun i ↦ exists_isPullback_pullback_pullback_snd B S hS t (f i)
  refine ⟨c, ?_⟩
  -- The same cover, read over the coproduct of the atlas rather than over `X`.
  have hrel' : ∀ i, ∃ c' : pullback (pullback.snd t (f i)) (pullback.snd t (f i)) ⟶
      pullback (pullback.fst t t ≫ t) (Sigma.desc f),
      c' ≫ pullback.fst (pullback.fst t t ≫ t) (Sigma.desc f) = c i ∧
        IsPullback c' (pullback.fst (pullback.snd t (f i)) (pullback.snd t (f i)) ≫
          pullback.snd t (f i)) (pullback.snd (pullback.fst t t ≫ t) (Sigma.desc f))
          (Sigma.ι Xi i) := by
    intro i
    refine ⟨hÊ.lift (c i) (pullback.fst (pullback.snd t (f i)) (pullback.snd t (f i)) ≫
      pullback.snd t (f i) ≫ Sigma.ι Xi i) (by rw [(hc i).w]; simp),
      hÊ.lift_fst _ _ _, ?_⟩
    refine IsPullback.of_right ?_ ?_ hÊ
    · rw [hÊ.lift_fst, Sigma.ι_desc]
      exact hc i
    · rw [hÊ.lift_snd]
      simp
  choose c' hc'fac hc' using hrel'
  obtain ⟨hcofan⟩ := Sheaf.nonempty_isColimit_cofanMk_of_isPullback J (Sigma.ι Xi)
    (coproductIsCoproduct Xi) (pullback.snd (pullback.fst t t ≫ t) (Sigma.desc f)) c' _ hc'
  have heq : Sigma.desc c =
      (Sigma.desc c') ≫ pullback.fst (pullback.fst t t ≫ t) (Sigma.desc f) := by
    refine Sigma.hom_ext _ _ fun i ↦ ?_
    rw [Sigma.ι_desc, ← Category.assoc, Sigma.ι_desc, hc'fac i]
  have hiso : Sigma.desc c' = ((coproductIsCoproduct fun i ↦
      pullback (pullback.snd t (f i)) (pullback.snd t (f i))).coconePointUniqueUpToIso
        hcofan).hom := by
    refine Sigma.hom_ext _ _ fun i ↦ ?_
    rw [Sigma.ι_desc]
    exact (IsColimit.comp_coconePointUniqueUpToIso_hom
      (coproductIsCoproduct fun i ↦ pullback (pullback.snd t (f i)) (pullback.snd t (f i)))
      hcofan (Discrete.mk i)).symm
  rw [heq, hiso]
  exact @epi_comp _ _ _ _ _ _ inferInstance _ hê

/-- **Stacks 0AIS for a sheaf covered by an admissible family.** Let `{Xᵢ ⟶ X}` be a jointly
surjective family of sheaves with an admissible index, each satisfying the set-theoretic
condition, such that for every point `t : h_U ⟶ X` from an object of the site and every `i`, the
relation `(U ×_X Xᵢ) ×_{Xᵢ} (U ×_X Xᵢ)` is dominated by an object of the site. Then `X`
satisfies the set-theoretic condition: `U` is the coproduct of the dominating objects of the
`Xᵢ`, and the kernel pair `U ×_X U` is covered by the relations over the members, whose
dominating objects form an admissible family again. This is
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_countable_atlas` with the
algebraic-space step replaced by the hypothesis on the pieces, and countability by
admissibility. -/
theorem satisfiesSetTheoreticCondition_of_admissible_cover (X : FppfSheaf B S hS)
    {I : Type (u + 1)} [Small.{u} I] [B.AdmitsCoproductIndex I] (Xi : I → FppfSheaf B S hS)
    (f : ∀ i, Xi i ⟶ X) (hXi : ∀ i, SatisfiesSetTheoreticCondition B S hS (Xi i))
    (hcover : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc f))
    (hpiece : ∀ (U : BigFppfOver B S hS)
      (t : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U ⟶ X) (i : I),
      ∃ (R : BigFppfOver B S hS) (α : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj R ⟶
        pullback (pullback.snd t (f i)) (pullback.snd t (f i))), Epi α) :
    SatisfiesSetTheoreticCondition B S hS X := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let J := BigFppfOver.topology B S hS
  let : J.Subcanonical := bigFppfOver_subcanonical B S hS
  obtain ⟨U, t, ht⟩ :=
    exists_representable_epi_of_admissible_cover B S hS X Xi f hXi hcover
  obtain ⟨c, hdesc⟩ := exists_epi_sigmaDesc_pullback_pullback_snd B S hS Xi f
    ((Sheaf.isLocallySurjective_iff_epi _).mp hcover) t
  -- Each member of the cover receives a surjection from an object of the site.
  choose R α hα using fun i ↦ hpiece U t i
  -- The coproduct of those objects of the site is an object of the site, and it surjects onto
  -- the kernel pair.
  obtain ⟨s, hs⟩ := exists_epi_uliftYoneda_sigmaObj B S hS R α hα c hdesc
  exact ⟨U, BigFppfOver.sigmaObj B S hS R, J.uliftYoneda.{u + 1}.obj U,
    J.uliftYoneda.{u + 1}.obj (BigFppfOver.sigmaObj B S hS R),
    ⟨J.uliftYonedaCompSheafToPresheaf.{u + 1}.app U⟩,
    ⟨J.uliftYonedaCompSheafToPresheaf.{u + 1}.app (BigFppfOver.sigmaObj B S hS R)⟩, t, ht,
    s, hs⟩

/-- **The kernel-pair pieces of a directed colimit of formal algebraic spaces along
representable thickenings are represented by objects of the site.** For a point
`t : h_U ⟶ colim E` and a stage `E_i`, the base change `U ×_{colim E} E_i` is represented by an
object `V'` of the site, the colimit injection being a representable thickening, and the relation
`V' ×_{E_i} V'` is then represented because `E_i` is a formal algebraic space. -/
theorem exists_epi_pullback_pullback_snd_colimitι {Λ : Type (u + 1)} [Preorder Λ]
    [Nonempty Λ] [IsDirected Λ (· ≤ ·)] (E : Λ ⥤ FppfSheaf B S hS)
    (hform : ∀ i : Λ, IsFormalAlgebraicSpace B S hS (E.obj i))
    (hthick : ∀ ⦃i j : Λ⦄ (g : i ⟶ j),
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom)
    (U : BigFppfOver B S hS)
    (t : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U ⟶ colimit E) (i : Λ) :
    ∃ (R : BigFppfOver B S hS) (α : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj R ⟶
      pullback (pullback.snd t (colimit.ι E i)) (pullback.snd t (colimit.ι E i))), Epi α := by
  classical
  let : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let J := BigFppfOver.topology B S hS
  let G := sheafToPresheaf J (Type (u + 1))
  have hι : Space.IsRepresentableThickeningULift.{u + 1} B S hS (colimit.ι E i).hom :=
    isRepresentableThickeningULift_colimitι_of_small B S hS E hthick
      (fun k ↦ small_of_isFormalAlgebraicSpace B S hS (hform k)) i
  let ξ : uliftYoneda.{u + 1}.obj U ⟶ (colimit E).obj := t.hom
  let hrep := hι.rep
  let V' := hrep.pullback ξ
  let fst' := hrep.fst ξ
  have hV' : IsPullback fst' (uliftYoneda.{u + 1}.map (hrep.snd ξ)) (colimit.ι E i).hom ξ :=
    hrep.isPullback ξ
  -- the base change of the colimit injection along `t`, read on presheaves
  let p := pullback.snd t (colimit.ι E i)
  have hP : IsPullback (G.map p) (G.map (pullback.fst t (colimit.ι E i)))
      (colimit.ι E i).hom ξ :=
    ((IsPullback.of_hasPullback t (colimit.ι E i)).map G).flip
  let e : (pullback t (colimit.ι E i)).obj ≅ uliftYoneda.{u + 1}.obj V' :=
    hP.isoIsPullback _ _ hV'
  have he : e.hom ≫ fst' = p.hom := hP.isoIsPullback_hom_fst _ _ hV'
  -- the relation over the stage, read on presheaves and transported along `e`
  have hQ : IsPullback (G.map (pullback.fst p p) ≫ e.hom) (G.map (pullback.snd p p) ≫ e.hom)
      fst' fst' := by
    have h := (IsPullback.of_hasPullback p p).map G
    refine h.of_iso (Iso.refl _) e e (Iso.refl _) (by simp) (by simp) ?_ ?_
    · simp only [Iso.refl_hom, Category.comp_id]; exact he.symm
    · simp only [Iso.refl_hom, Category.comp_id]; exact he.symm
  obtain ⟨R, ⟨eR⟩⟩ := essImage_pullback_of_isFormalAlgebraicSpace B S hS (hform i) V' V'
    fst' fst'
  let ePre : (J.uliftYoneda.{u + 1}.obj R).obj ≅ (pullback p p).obj :=
    (J.uliftYonedaCompSheafToPresheaf.{u + 1}.app R) ≪≫ eR ≪≫
      (hQ.isoPullback).symm
  let eSh : J.uliftYoneda.{u + 1}.obj R ≅ pullback p p :=
    (fullyFaithfulSheafToPresheaf J (Type (u + 1))).preimageIso ePre
  exact ⟨R, eSh.hom, inferInstance⟩

/-- **Stacks 0AIS for a directed colimit of formal algebraic spaces along representable
thickenings, indexed by a type admitting coproducts in the site.** The stages cover the colimit,
each satisfies the set-theoretic condition, and the kernel-pair pieces over them are represented
by `AlgebraicGeometry.FormalSpace.exists_epi_pullback_pullback_snd_colimitι`. -/
theorem satisfiesSetTheoreticCondition_colimit_of_admissible {Λ : Type (u + 1)} [Preorder Λ]
    [Nonempty Λ] [IsDirected Λ (· ≤ ·)] [Small.{u} Λ] [B.AdmitsCoproductIndex Λ]
    (E : Λ ⥤ FppfSheaf B S hS)
    (hform : ∀ i : Λ, IsFormalAlgebraicSpace B S hS (E.obj i))
    (hthick : ∀ ⦃i j : Λ⦄ (g : i ⟶ j),
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom) :
    SatisfiesSetTheoreticCondition B S hS (colimit E) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  refine satisfiesSetTheoreticCondition_of_admissible_cover B S hS (colimit E) E.obj
    (colimit.ι E) (fun i ↦ (hform i).1) ?_
    (exists_epi_pullback_pullback_snd_colimitι B S hS E hform hthick)
  rw [Sheaf.isLocallySurjective_iff_epi]
  refine ⟨fun {T} k l hkl ↦ colimit.hom_ext fun i ↦ ?_⟩
  simpa using congrArg (fun m ↦ Sigma.ι E.obj i ≫ m) hkl

/-- **Stacks 0GVN for an admissible index, from Stacks 07VS for thickenings.** The colimit of a
directed system of formal algebraic spaces along representable thickenings, indexed by a type
admitting coproducts in the site, is a formal algebraic space, given only `hthickAff`: an
algebraic space receiving a surjective closed immersion from an affine object of the site is
affine. The set-theoretic condition is
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_colimit_of_admissible`, and the
atlas is the chart system of
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_colimit_of_setTheoretic`.
-/
theorem isFormalAlgebraicSpace_of_colimit_closedImmersions_of_admissible_of_affine
    (Λ : Type (u + 1)) [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)] [Small.{u} Λ]
    [B.AdmitsCoproductIndex Λ] (E : Λ ⥤ FppfSheaf B S hS)
    (hform : ∀ i : Λ, IsFormalAlgebraicSpace B S hS (E.obj i))
    (hthick : ∀ ⦃i j : Λ⦄ (g : i ⟶ j),
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom)
    (hthickAff : IsAffineOfSurjectiveClosedImmersion B S hS)
    (Z : FppfSheaf B S hS) (hZ : Nonempty (Z ≅ colimit E)) :
    IsFormalAlgebraicSpace B S hS Z := by
  obtain ⟨eZ⟩ := hZ
  exact isFormalAlgebraicSpace_of_colimit_of_setTheoretic B S hS Λ E hform
    hthick hthickAff Z (satisfiesSetTheoreticCondition_of_iso B S hS eZ.symm
      (satisfiesSetTheoreticCondition_colimit_of_admissible B S hS E hform hthick)) ⟨eZ⟩

/-- **Stacks 0GVN**, in the form its proof establishes. Let `E` be a directed system of formal
algebraic spaces over `S` whose transition morphisms are representable thickenings —
equivalently, by Stacks 0GVL, closed immersions inducing isomorphisms on reductions — indexed by
a type admitting coproducts in the site (every countable index does). Then a sheaf isomorphic to
its colimit is a formal algebraic space over `S`.

The bound is forced: the source's proof never checks the set-theoretic condition of
Definition 0AIM for the colimit, Remark 0AIS (1) and (3) give it only for an index "not too
large (for example countable)", and without a bound the conclusion is false,
`AlgebraicGeometry.FormalSpace.not_forall_isFormalAlgebraicSpace_colimit_closedImmersions`. -/
@[stacks 0GVN "corrected form: the index is required to admit coproducts in the site \
(AlgebraicGeometry.BigFppfSite.AdmitsCoproductIndex, e.g. any countable index), the caveat of \
Remark 0AIS (1) and (3) that the source's proof leaves unchecked; without such a bound the \
statement is false, by \
AlgebraicGeometry.FormalSpace.not_forall_isFormalAlgebraicSpace_colimit_closedImmersions"]
theorem isFormalAlgebraicSpace_of_colimit_closedImmersions_of_admissible
    (Λ : Type (u + 1)) [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)] [Small.{u} Λ]
    [B.AdmitsCoproductIndex Λ] (E : Λ ⥤ FppfSheaf B S hS)
    (hform : ∀ i : Λ, IsFormalAlgebraicSpace B S hS (E.obj i))
    (hthick : ∀ ⦃i j : Λ⦄ (g : i ⟶ j),
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom)
    (Z : FppfSheaf B S hS) (hZ : Nonempty (Z ≅ colimit E)) :
    IsFormalAlgebraicSpace B S hS Z :=
  isFormalAlgebraicSpace_of_colimit_closedImmersions_of_admissible_of_affine B S hS Λ E hform
    hthick (isAffineOfSurjectiveClosedImmersion B S hS) Z hZ

/-- **Stacks 0GVN, corrected per the recorded erratum.** Let `E` be a directed system of formal
algebraic spaces over `S`, indexed by an arbitrary directed set, whose transition morphisms are
representable thickenings — equivalently, by Stacks 0GVL, closed immersions inducing
isomorphisms on reductions. A sheaf `Z` isomorphic to its colimit which satisfies the
set-theoretic condition of Remark 0AIS is a formal algebraic space over `S`.

The set-theoretic condition is the only hypothesis beyond those of the source, and it cannot be
dropped
(`AlgebraicGeometry.FormalSpace.not_forall_isFormalAlgebraicSpace_colimit_closedImmersions`).
The chart system of the source's proof is constructed from an atlas of one stage by the étale
lifting of Stacks 0DEG/0DEE and its stages are affine by Stacks 0DE8
(`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_colimit_of_setTheoretic`, with
`AlgebraicGeometry.FormalSpace.isAffineOfSurjectiveClosedImmersion`); for an index admitting
coproducts in the site the condition is itself a theorem,
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_colimit_closedImmersions_of_admissible`.
-/
@[stacks 0GVN "corrected form per the recorded erratum: for an arbitrary directed index, the \
colimit of a system of formal algebraic spaces along closed immersions inducing isomorphisms on \
reductions (representable thickenings, Stacks 0GVL) is a formal algebraic space provided the \
colimit satisfies the set-theoretic condition of Remark 0AIS; that condition cannot be dropped, \
AlgebraicGeometry.FormalSpace.not_forall_isFormalAlgebraicSpace_colimit_closedImmersions"]
theorem isFormalAlgebraicSpace_of_colimit_closedImmersions_of_satisfiesSetTheoreticCondition
    (Λ : Type (u + 1)) [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (E : Λ ⥤ FppfSheaf B S hS)
    (hform : ∀ i : Λ, IsFormalAlgebraicSpace B S hS (E.obj i))
    (hthick : ∀ ⦃i j : Λ⦄ (g : i ⟶ j),
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom)
    (Z : FppfSheaf B S hS) (hZset : SatisfiesSetTheoreticCondition B S hS Z)
    (hZ : Nonempty (Z ≅ colimit E)) :
    IsFormalAlgebraicSpace B S hS Z :=
  isFormalAlgebraicSpace_of_colimit_of_setTheoretic B S hS Λ E hform hthick
    (isAffineOfSurjectiveClosedImmersion B S hS) Z hZset hZ

/-! ### The unbounded statement is false -/

/-- **Without a bound on the index and without the set-theoretic condition, the conclusion of
Stacks 0GVN fails.** Over any nonempty `S`, the square-zero system of Stacks 0AIU's
counterexample (`AlgebraicGeometry.FormalSpace.sqZeroSheafDiagram`, whose stages are affine
schemes of the site and so formal algebraic spaces) has a colimit which is not a formal algebraic
space
(`AlgebraicGeometry.FormalSpace.not_satisfiesSetTheoreticCondition_colimit_sqZeroSheafDiagram`).
So neither the bound of
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_colimit_closedImmersions_of_admissible`
nor the set-theoretic hypothesis of
`isFormalAlgebraicSpace_of_colimit_closedImmersions_of_satisfiesSetTheoreticCondition` can be
dropped. -/
theorem not_forall_isFormalAlgebraicSpace_colimit_closedImmersions [Nonempty S] :
    ¬ ∀ (Λ : Type (u + 1)) [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
      (E : Λ ⥤ FppfSheaf B S hS),
      (∀ i : Λ, IsFormalAlgebraicSpace B S hS (E.obj i)) →
      (∀ ⦃i j : Λ⦄ (g : i ⟶ j),
        Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom) →
      IsFormalAlgebraicSpace B S hS (colimit E) := by
  intro h
  let x : S := Classical.arbitrary S
  have hk := B.residueField_spec_contains hS x
  let σ : Type u := B.cutoff.out
  exact not_satisfiesSetTheoreticCondition_colimit_sqZeroSheafDiagram B S hS (S.residueField x)
    hk (S.fromSpecResidueField x) σ (Cardinal.mk_out B.cutoff).ge
    (h (ULift.{u + 1} (Finset σ)) (sqZeroSheafDiagram B S hS (S.residueField x) hk
      (S.fromSpecResidueField x) σ)
      (fun μ ↦ isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS
        (isAffineFormalAlgebraicSpace_uliftYoneda B S hS
          ((sqZeroDiagram B S hS (S.residueField x) hk (S.fromSpecResidueField x) σ).obj μ)))
      (fun _ _ g ↦ isRepresentableThickeningULift_sqZeroSheafDiagram_map B S hS _ hk _ σ g)).1

end AlgebraicGeometry.FormalSpace

end
