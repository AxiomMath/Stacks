module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountableAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SectionsDoNotSeparatePoints
public import StacksFrontier.CategoryTheory.Sites.LocallySurjectiveBaseChange
public import StacksFrontier.CategoryTheory.Sites.UliftYonedaCoproduct

/-!
# Countable covers of sheaves on a big fppf site

A countable jointly surjective family of sheaves on a big fppf site, each dominated by an object
of the site, is dominated by a single object of the site.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_representable_epi_of_countable_cover`: a countable jointly
  surjective family of sheaves, each dominated by an object of the site, is dominated by one
  object of the site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Observation (3), first half: a countable cover is dominated by one object of the site -/

/-- **A countable jointly surjective family of sheaves each dominated by an object of the site
is dominated by one object of the site.** This is the first half of the set-theoretic condition
of Stacks 0AIS for `X`, and it uses nothing of the family `{Xᵢ ⟶ X}` beyond the first half of
the condition for each member and countability of the index: the size cutoff of a big fppf site
has uncountable cofinality, so the coproduct `U = ∐ Uᵢ` of the chosen objects is again an object
of the site.

In particular no representability or étaleness of the maps `Xᵢ ⟶ X` is used, which is why the
same step serves both the atlas of Definition 0AIM
(`AlgebraicGeometry.FormalSpace.exists_representable_epi_of_countable_atlas`) and the colimit
cocone of a countable directed system. -/
theorem exists_representable_epi_of_countable_cover (X : FppfSheaf B S hS)
    {I : Type (u + 1)} [Countable I] (Xi : I → FppfSheaf B S hS) (f : ∀ i, Xi i ⟶ X)
    (hXi : ∀ i, SatisfiesSetTheoreticCondition B S hS (Xi i))
    (hcover : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc f)) :
    ∃ (U : BigFppfOver B S hS)
      (t : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U ⟶ X), Epi t := by
  classical
  let : Small.{u} I := Countable.toSmall.{u} I
  let : B.AdmitsCoproductIndex I := BigFppfSite.admitsCoproductIndex_of_countable B I
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
  let U : BigFppfOver B S hS := BigFppfOver.sigmaObj B S hS Ui
  have hLift : IsColimit (Cofan.mk (J.uliftYoneda.{u + 1}.obj U)
      fun i ↦ J.uliftYoneda.{u + 1}.map (BigFppfOver.sigmaIncl B S hS Ui i)) :=
    BigFppfOver.isColimitUliftYonedaSigmaCofan B S hS Ui
  set t := hLift.desc (Cofan.mk X fun i ↦ b i ≫ f i) with ht
  refine ⟨U, t, ?_⟩
  -- The composite of the coproduct of the chosen surjections with `∐ Xᵢ ⟶ X` is a surjection.
  have hdesc : Epi (Sigma.desc fun i ↦ b i ≫ f i) := by
    have := hb
    have := (Sheaf.isLocallySurjective_iff_epi _).mp hcover
    rw [show (Sigma.desc fun i ↦ b i ≫ f i) = Limits.Sigma.map b ≫ Sigma.desc f from
      Sigma.hom_ext _ _ fun i ↦ by simp]
    infer_instance
  -- and it factors through `t`.
  let e : (∐ fun i ↦ J.uliftYoneda.{u + 1}.obj (Ui i)) ≅ J.uliftYoneda.{u + 1}.obj U :=
    (coproductIsCoproduct fun i ↦ J.uliftYoneda.{u + 1}.obj (Ui i)).coconePointUniqueUpToIso hLift
  have het : e.hom ≫ t = Sigma.desc fun i ↦ b i ≫ f i := by
    apply Sigma.hom_ext
    intro i
    have hi : Sigma.ι (fun i ↦ J.uliftYoneda.{u + 1}.obj (Ui i)) i ≫ e.hom =
        J.uliftYoneda.{u + 1}.map (BigFppfOver.sigmaIncl B S hS Ui i) :=
      IsColimit.comp_coconePointUniqueUpToIso_hom
        (coproductIsCoproduct fun i ↦ J.uliftYoneda.{u + 1}.obj (Ui i)) hLift (Discrete.mk i)
    have hfac := hLift.fac (Cofan.mk X fun i ↦ b i ≫ f i) (Discrete.mk i)
    simp only [Cofan.mk_ι_app] at hfac
    rw [← Category.assoc, hi, ht, hfac]
    simp
  have : Epi (e.hom ≫ t) := het ▸ hdesc
  exact epi_of_epi e.hom t

end AlgebraicGeometry.FormalSpace

end
