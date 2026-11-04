module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountableAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCoverCounterexample
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SetTheoreticConditionCriteria
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SetTheoreticDescentRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproduct
public import StacksFrontier.CategoryTheory.Sites.InfinitaryExtensive
import all StacksFrontier.AlgebraicGeometry.FormalSpace.CountableAtlas

/-!
# The set-theoretic condition for an étale cover by formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`, and let `{Xᵢ ⟶ X}_{i ∈ I}` be a family of
maps of fppf sheaves over `S` such that (a) each `Xᵢ` is a formal algebraic space, (b) each
`Xᵢ ⟶ X` is representable by algebraic spaces and étale, and (c) `∐ Xᵢ ⟶ X` is a surjection
of sheaves. **Stacks 0AJ1** concludes that `X` is a formal algebraic space. Its proof composes
the atlases of the `Xᵢ` into an atlas of `X` and says nothing about the set-theoretic condition
of **Stacks 0AIS**, which Definition 0AIM also asks of `X`.

That condition does not follow from (a)–(c) for an arbitrary index: for an index at least as
large as the size cutoff of the site it can fail
(`AlgebraicGeometry.FormalSpace.not_forall_isFormalAlgebraicSpace_of_etaleCover`). Observation
(3) of Remark 0AIS says what is needed: *if `I` is not too large* the condition holds. This file
proves that, for an index admissible for coproducts in the site
(`AlgebraicGeometry.BigFppfSite.AdmitsCoproductIndex`: of cardinality below the cofinality of
the cutoff, for instance countable), and so proves Stacks 0AJ1 for such an index with no
set-theoretic hypothesis on `X`.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_representable_epi_of_etaleCover`: an object of the site
  surjects onto `X`.
* `AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_etaleCover`: `X` satisfies
  the set-theoretic condition of Stacks 0AIS.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_etaleCover_of_admitsCoproductIndex`:
  **Stacks 0AJ1** for an admissible index, with the set-theoretic condition derived.

## Implementation notes

The argument is the one of
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_countable_atlas`, which treats
an atlas by *affine* formal algebraic spaces with a countable index; neither restriction is
used in an essential way. Each `Xᵢ` satisfies the set-theoretic condition, being a formal
algebraic space, so an object `Uᵢ` of the site surjects onto it, and admissibility of the index
puts `U = ∐ Uᵢ` in the site; then `U ⟶ X` is a surjection, through `∐ Xᵢ ⟶ X`. The kernel pair
`U ×_X U` is covered by the fibre products `(U ×_X Xᵢ) ×_{Xᵢ} (U ×_X Xᵢ)`, coproducts of sheaves
being universal. Each `U ×_X Xᵢ` is an algebraic space by condition (b) and Stacks 03XY, its
projection to `Xᵢ` is representable by algebraic spaces by Stacks 0AIQ for the formal algebraic
space `Xᵢ`, and so each member of the cover is an algebraic space, again by Stacks 03XY. The
étale scheme atlases of the members are objects of the site, and admissibility puts their
coproduct in the site as well; it is the required object surjecting onto `U ×_X U`. Only the
representability half of condition (b) enters.

## References

* [Stacks Project, Tag 0AJ1](https://stacks.math.columbia.edu/tag/0AJ1)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIQ](https://stacks.math.columbia.edu/tag/0AIQ)
* [Stacks Project, Tag 03XY](https://stacks.math.columbia.edu/tag/03XY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The first half of the set-theoretic condition for an étale cover by formal algebraic
spaces.** Let `{Xᵢ ⟶ X}` be a family of maps of fppf sheaves over `S`, indexed by a type
admissible for coproducts in the site, whose members are formal algebraic spaces and whose
induced map from the coproduct is a surjection of sheaves. Then an object `U` of the big fppf
site of `S` surjects onto `X`: it is the coproduct, inside the site, of objects `Uᵢ` surjecting
onto the `Xᵢ`, which the set-theoretic condition on the formal algebraic spaces `Xᵢ` provides. -/
theorem exists_representable_epi_of_etaleCover (X : FppfSheaf B S hS)
    {I : Type (u + 1)} [Small.{u} I] [B.AdmitsCoproductIndex I]
    (Xi : I → FppfSheaf B S hS) (f : ∀ i, Xi i ⟶ X)
    (hXi : ∀ i, IsFormalAlgebraicSpace B S hS (Xi i))
    (hsurj : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc f)) :
    ∃ (U : BigFppfOver B S hS)
      (t : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U ⟶ X), Epi t := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  -- Each member of the family receives a surjection from an object of the site.
  choose Ui b hb using fun i ↦ exists_epi_uliftYoneda_of_satisfiesSetTheoreticCondition (hXi i).1
  -- The composites `h_{Uᵢ} ⟶ Xᵢ ⟶ X` are jointly surjective, so their coproduct, an object of
  -- the site, surjects onto `X`.
  have hdesc : Epi (Sigma.desc f) := (Sheaf.isLocallySurjective_iff_epi _).mp hsurj
  obtain ⟨t, ht, -⟩ := exists_epi_uliftYoneda_sigmaObj B S hS Ui (fun i ↦ b i ≫ f i)
    (fun Z g g' hgg' ↦ by
      refine (cancel_epi (Sigma.desc f)).mp (Sigma.hom_ext _ _ fun i ↦ ?_)
      have _ : Epi (b i) := hb i
      refine (cancel_epi (b i)).mp ?_
      simpa only [Sigma.ι_desc_assoc, Category.assoc] using hgg' i)
  exact ⟨_, t, ht⟩

/-- A family of epimorphisms `αᵢ : Aᵢ ⟶ Bᵢ` induces an epimorphism `∐ Aᵢ ⟶ ∐ Bᵢ`. -/
private theorem epi_sigmaDesc_comp_ι {C : Type*} [Category C] {ι : Type*} {A B : ι → C}
    [HasCoproduct A] [HasCoproduct B] (α : ∀ i, A i ⟶ B i) (hα : ∀ i, Epi (α i)) :
    Epi (Sigma.desc fun i ↦ α i ≫ Sigma.ι B i) := by
  refine ⟨fun w₁ w₂ hw ↦ Sigma.hom_ext _ _ fun i ↦ ?_⟩
  have := hα i
  refine (cancel_epi (α i)).mp ?_
  simpa only [Sigma.ι_desc_assoc, Category.assoc] using Sigma.ι A i ≫= hw

/-- If `s` is a colimit cofan over the `βᵢ` and the morphism `∐ βᵢ ⟶ P` induced by a family
`gᵢ : βᵢ ⟶ P` is an epimorphism, then so is the morphism out of the cone point of `s` that the
family induces. -/
private theorem epi_isColimit_desc_of_epi_sigmaDesc {C : Type*} [Category C] {ι : Type*} {β : ι → C}
    [HasCoproduct β] {s : Cofan β} (hs : IsColimit s) {P : C} (g : ∀ i, β i ⟶ P)
    [Epi (Sigma.desc g)] : Epi (hs.desc (Cofan.mk P g)) := by
  let e := (coproductIsCoproduct β).coconePointUniqueUpToIso hs
  have het : e.hom ≫ hs.desc (Cofan.mk P g) = Sigma.desc g := by
    refine Sigma.hom_ext _ _ fun i ↦ ?_
    have hi : Sigma.ι β i ≫ e.hom = s.ι.app (Discrete.mk i) :=
      IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct β) hs (Discrete.mk i)
    have hfac := hs.fac (Cofan.mk P g) (Discrete.mk i)
    simp only [Cofan.mk_ι_app] at hfac
    rw [← Category.assoc, hi, hfac, Sigma.ι_desc]
  have : Epi (e.hom ≫ hs.desc (Cofan.mk P g)) := by rwa [het]
  exact epi_of_epi e.hom _


/-- If `s` is a colimit cofan over the `βᵢ`, the morphism `∐ βᵢ ⟶ P` induced by a family
`gᵢ : βᵢ ⟶ P` is an epimorphism if and only if the morphism out of the cone point of `s`
that the family induces is. -/
private theorem epi_sigmaDesc_iff_epi_isColimit_desc {C : Type*} [Category C] {ι : Type*}
    {β : ι → C} [HasCoproduct β] {s : Cofan β} (hs : IsColimit s) {P : C} (g : ∀ i, β i ⟶ P) :
    Epi (Sigma.desc g) ↔ Epi (hs.desc (Cofan.mk P g)) := by
  let e := (coproductIsCoproduct β).coconePointUniqueUpToIso hs
  have het : Sigma.desc g = e.hom ≫ hs.desc (Cofan.mk P g) := by
    refine Sigma.hom_ext _ _ fun i ↦ ?_
    have hi : Sigma.ι β i ≫ e.hom = s.ι.app (Discrete.mk i) :=
      IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct β) hs (Discrete.mk i)
    have hfac := hs.fac (Cofan.mk P g) (Discrete.mk i)
    simp only [Cofan.mk_ι_app] at hfac
    rw [← Category.assoc, hi, hfac, Sigma.ι_desc]
  rw [het]
  exact ⟨fun h ↦ epi_of_epi e.hom _, fun h ↦ epi_comp _ _⟩

/-- **The kernel pair of a morphism to `X` is covered by its relations over an étale cover.**
If `∐ Xᵢ ⟶ X` is a surjection of sheaves, then for any `t : T ⟶ X` the fibre products
`(T ×_X Xᵢ) ×_{Xᵢ} (T ×_X Xᵢ)` map to `T ×_X T` by a jointly surjective family: they are the
base change of `T ×_X T` along `∐ Xᵢ ⟶ X`, decomposed along the coproduct. -/
private theorem exists_epi_sigmaDesc_pullback_of_isLocallySurjective {T X : FppfSheaf B S hS}
    {I : Type (u + 1)} (Xi : I → FppfSheaf B S hS) (t : T ⟶ X) (f : ∀ i, Xi i ⟶ X)
    (hcover : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc f)) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    ∃ c : ∀ i, pullback (pullback.snd t (f i)) (pullback.snd t (f i)) ⟶ pullback t t,
      Epi (Sigma.desc c) := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let J := BigFppfOver.topology B S hS
  -- The kernel pair of `t`, with its projection to `X`, and the base change of that
  -- projection along the surjection from the coproduct of the cover.
  have hEsq : IsPullback (pullback.fst t t) (pullback.snd t t) t t := IsPullback.of_hasPullback t t
  have hÊ : IsPullback (pullback.fst (pullback.fst t t ≫ t) (Sigma.desc f))
      (pullback.snd (pullback.fst t t ≫ t) (Sigma.desc f)) (pullback.fst t t ≫ t)
      (Sigma.desc f) := IsPullback.of_hasPullback _ _
  have hê : Epi (pullback.fst (pullback.fst t t ≫ t) (Sigma.desc f)) := by
    rw [← Sheaf.isLocallySurjective_iff_epi]
    exact isLocallySurjective_of_isPullback J
      (hÊ.flip.map (sheafToPresheaf J (Type (u + 1)))) hcover
  -- The cover of the kernel pair by the relations of `t` over the members of the family.
  have hrel : ∀ i, ∃ c : pullback (pullback.snd t (f i)) (pullback.snd t (f i)) ⟶ pullback t t,
      IsPullback c (pullback.fst (pullback.snd t (f i)) (pullback.snd t (f i)) ≫
        pullback.snd t (f i)) (pullback.fst t t ≫ t) (f i) := by
    intro i
    have hcomm : (pullback.fst (pullback.snd t (f i)) (pullback.snd t (f i)) ≫
          pullback.fst t (f i)) ≫ t =
        (pullback.snd (pullback.snd t (f i)) (pullback.snd t (f i)) ≫
          pullback.fst t (f i)) ≫ t := by
      have h := (IsPullback.of_hasPullback (pullback.snd t (f i))
        (pullback.snd t (f i))).w =≫ f i
      simp only [Category.assoc] at h ⊢
      rw [(IsPullback.of_hasPullback t (f i)).w]
      exact h
    exact ⟨hEsq.lift _ _ hcomm, isPullback_chartRelation (IsPullback.of_hasPullback t (f i))
      (IsPullback.of_hasPullback _ _) hEsq _ (hEsq.lift_fst _ _ hcomm)
      (hEsq.lift_snd _ _ hcomm)⟩
  choose c hc using hrel
  -- The same cover, read over the coproduct of the family rather than over `X`.
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
  -- The cover is jointly surjective: the coproduct of its members is the base change of the
  -- kernel pair along the surjection from the coproduct of the family.
  have : hcofan.desc (Cofan.mk (pullback t t) c) =
      pullback.fst (pullback.fst t t ≫ t) (Sigma.desc f) :=
    (hcofan.uniq (Cofan.mk (pullback t t) c) _ fun j ↦ hc'fac j.as).symm
  rw [← this, ← epi_sigmaDesc_iff_epi_isColimit_desc hcofan c] at hê
  exact ⟨c, hê⟩

/-- **The set-theoretic condition of Stacks 0AIS for an étale cover by formal algebraic spaces,
with an index which is not too large.** Let `{Xᵢ ⟶ X}` be a family of maps of fppf sheaves
over `S`, indexed by a type admissible for coproducts in the site (for instance a countable
one), such that each `Xᵢ` is a formal algebraic space, each `Xᵢ ⟶ X` is representable by
algebraic spaces, and `∐ Xᵢ ⟶ X` is a surjection of sheaves. Then `X` satisfies the
set-theoretic condition of Stacks 0AIS.

The surjection onto `X` is
`AlgebraicGeometry.FormalSpace.exists_representable_epi_of_etaleCover`. The kernel pair
`U ×_X U` of that surjection is covered by the fibre products `(U ×_X Xᵢ) ×_{Xᵢ} (U ×_X Xᵢ)`:
they are the base change of `U ×_X U` along `∐ Xᵢ ⟶ X`, decomposed along the coproduct. Each
`U ×_X Xᵢ` is an algebraic space by Stacks 03XY, `Xᵢ ⟶ X` being representable by algebraic
spaces; its projection to the formal algebraic space `Xᵢ` is representable by algebraic spaces
by Stacks 0AIQ; so each member of the cover is an algebraic space, by Stacks 03XY once more, and
receives a surjection from its étale scheme atlas. The coproduct of those atlases is an object
of the site, the index being admissible, and it surjects onto `U ×_X U`. -/
theorem satisfiesSetTheoreticCondition_of_etaleCover (X : FppfSheaf B S hS)
    {I : Type (u + 1)} [Small.{u} I] [B.AdmitsCoproductIndex I]
    (Xi : I → FppfSheaf B S hS) (f : ∀ i, Xi i ⟶ X)
    (hXi : ∀ i, IsFormalAlgebraicSpace B S hS (Xi i))
    (hfrep : ∀ i, Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (f i).hom)
    (hcover : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc f)) :
    SatisfiesSetTheoreticCondition B S hS X := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let J := BigFppfOver.topology B S hS
  let : J.Subcanonical := bigFppfOver_subcanonical B S hS
  obtain ⟨U, t, ht⟩ := exists_representable_epi_of_etaleCover B S hS X Xi f hXi hcover
  obtain ⟨c, hdesc⟩ := exists_epi_sigmaDesc_pullback_of_isLocallySurjective B S hS Xi t f hcover
  -- Each member of the cover is an algebraic space over `S` (Stacks 03XY, Stacks 0AIQ, Stacks
  -- 03XY), hence receives a surjection of sheaves from an object of the site.
  have hUalg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (J.uliftYoneda.{u + 1}.obj U).obj :=
    Space.isAlgebraicSpaceULift_of_iso B S hS
      (J.uliftYonedaCompSheafToPresheaf.{u + 1}.app U).symm
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS U)
  have hPalg : ∀ i, Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback t (f i)).obj :=
    fun i ↦ SetTheoreticDescent.isAlgebraicSpaceULift_pullback_of_representable B S hS (f i)
      (hfrep i) t hUalg
  have halg : ∀ i, Space.IsAlgebraicSpaceULift.{u + 1} B S hS
      (pullback (pullback.snd t (f i)) (pullback.snd t (f i))).obj := fun i ↦
    SetTheoreticDescent.isAlgebraicSpaceULift_pullback_of_representable B S hS
      (pullback.snd t (f i))
      (isRepresentableByAlgebraicSpacesULift_of_isAlgebraicSpaceULift_of_isFormal B S hS
        (pullback.snd t (f i)) (hPalg i) (hXi i))
      (pullback.snd t (f i)) (hPalg i)
  choose R α hα using fun i ↦
    exists_epi_uliftYoneda_of_isAlgebraicSpaceULift B S hS _ (halg i)
  -- The coproduct of those objects of the site is an object of the site, and it surjects onto
  -- the kernel pair.
  have hLift : IsColimit (Cofan.mk (J.uliftYoneda.{u + 1}.obj (BigFppfOver.sigmaObj B S hS R))
      fun i ↦ J.uliftYoneda.{u + 1}.map (BigFppfOver.sigmaIncl B S hS R i)) :=
    BigFppfOver.isColimitUliftYonedaSigmaCofan B S hS R
  refine ⟨U, BigFppfOver.sigmaObj B S hS R, J.uliftYoneda.{u + 1}.obj U,
    J.uliftYoneda.{u + 1}.obj (BigFppfOver.sigmaObj B S hS R),
    ⟨J.uliftYonedaCompSheafToPresheaf.{u + 1}.app U⟩,
    ⟨J.uliftYonedaCompSheafToPresheaf.{u + 1}.app (BigFppfOver.sigmaObj B S hS R)⟩, t, ht,
    hLift.desc (Cofan.mk (pullback t t) fun i ↦ α i ≫ c i), ?_⟩
  -- The coproduct of the atlases of the members of the cover is an epimorphism, and so is its
  -- composite with the cover.
  have hmap := epi_sigmaDesc_comp_ι
    (B := fun i ↦ pullback (pullback.snd t (f i)) (pullback.snd t (f i))) α hα
  have htot : Epi (Sigma.desc fun i ↦ α i ≫ c i) := by
    have hfac : (Sigma.desc fun i ↦ α i ≫ c i) =
        (Sigma.desc fun i ↦ α i ≫
          Sigma.ι (fun i ↦ pullback (pullback.snd t (f i)) (pullback.snd t (f i))) i) ≫
            Sigma.desc c := by
      refine Sigma.hom_ext _ _ fun i ↦ ?_
      simp
    rw [hfac]
    exact @epi_comp _ _ _ _ _ _ hmap _ hdesc
  -- and it factors through the representable sheaf of the coproduct.
  exact (epi_sigmaDesc_iff_epi_isColimit_desc hLift _).mp htot

/-- **Stacks 0AJ1, for an index which is not too large.** Let `{Xᵢ ⟶ X}_{i ∈ I}` be a family of
maps of fppf sheaves on the big fppf site of `S`, indexed by a type admissible for coproducts in
the site (of cardinality below the cofinality of its size cutoff; for instance a countable one),
such that (a) each `Xᵢ` is a formal algebraic space over `S`, (b) each `Xᵢ ⟶ X` is
representable by algebraic spaces and étale, and (c) `∐ Xᵢ ⟶ X` is a surjection of sheaves.
Then `X` is a formal algebraic space over `S`.

The atlas is the source's: the atlases of the `Xᵢ` composed with the maps `Xᵢ ⟶ X`
(`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_etaleCover`). The set-theoretic
condition of Stacks 0AIS, which Definition 0AIM asks of `X` as well, is not assumed: it is
derived from (a)–(c) by
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_etaleCover`, which is where
the size of the index enters, as observation (3) of Remark 0AIS says it must. Without a bound
on the index the statement is false
(`AlgebraicGeometry.FormalSpace.not_forall_isFormalAlgebraicSpace_of_etaleCover`). -/
@[stacks 0AJ1 "corrected form: the printed statement is false for an index set as large as the \
size cutoff of the site, the target then failing the set-theoretic condition of Stacks 0AIS that \
Definition 0AIM asks of a formal algebraic space \
(AlgebraicGeometry.FormalSpace.not_forall_isFormalAlgebraicSpace_of_etaleCover); stated, under \
the source's hypotheses (a)-(c), for an index admissible for coproducts in the site, the proviso \
'I not too large' of Stacks 0AIS observation (3), and with that condition derived, not assumed"]
theorem isFormalAlgebraicSpace_of_etaleCover_of_admitsCoproductIndex
    {I : Type (u + 1)} [Small.{u} I] [B.AdmitsCoproductIndex I]
    (X : FppfSheaf B S hS) (Xi : I → FppfSheaf B S hS) (f : ∀ i, Xi i ⟶ X)
    (hXi : ∀ i, IsFormalAlgebraicSpace B S hS (Xi i))
    (hf : ∀ i, ∃ hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (f i).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) (f i).hom hfi)
    (hsurj : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc f)) :
    IsFormalAlgebraicSpace B S hS X :=
  isFormalAlgebraicSpace_of_etaleCover B S hS X Xi f hXi hf hsurj
    (satisfiesSetTheoreticCondition_of_etaleCover B S hS X Xi f hXi (fun i ↦ (hf i).1) hsurj)

end AlgebraicGeometry.FormalSpace

end
