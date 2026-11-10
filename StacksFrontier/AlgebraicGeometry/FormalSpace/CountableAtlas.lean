module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Defs
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalAtlasCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiSeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.CategoryTheory.Sites.InfinitaryExtensive

/-!
# The set-theoretic condition for a countable atlas (Stacks 0AIS, observation (3))

Let `S` be a scheme contained in a big fppf site `B`. Observation (3) of **Stacks 0AIS**
concerns a family of maps `{Xᵢ ⟶ X}_{i ∈ I}` of fppf sheaves satisfying conditions (1), (2)
and (3) of Definition 0AIM — each `Xᵢ` an affine formal algebraic space, each `Xᵢ ⟶ X`
representable by algebraic spaces and étale, and `∐ Xᵢ ⟶ X` a surjection of sheaves — and says
two things about it.

First, for each `i` one may pick an object `Uᵢ` of the site and a surjection of sheaves
`Uᵢ ⟶ Xᵢ`, so that if `I` is not too large — countable, say — then `U = ∐ Uᵢ` is an object of
the site and `U ⟶ X` is a surjection of sheaves. The surjection `Uᵢ ⟶ Xᵢ` is exactly the first
half of the set-theoretic condition carried by the hypothesis that `Xᵢ` is an affine formal
algebraic space, and countability is what makes the coproduct an object of the site: the size
cutoff of a big fppf site has uncountable cofinality, so it is closed under countable
coproducts.

Second, to complete the set-theoretic condition one needs an object `R` of the site surjecting
onto `U ×_X U`. The source gets one from a size estimate: `U ×_X U` is the base change of the
diagonal `Δ : X ⟶ X ×_S X` along `U ×_S U ⟶ X ×_S X`, so if `Δ` is representable and not too
wild — quasi-compact, say — the representing scheme sits inside `U ×_S U` by a quasi-compact
monomorphism and is therefore of size below the cutoff. Countability of `I` makes that estimate
unnecessary, and the argument below never leaves the site. The kernel pair `U ×_X U` is covered
by the family of fibre products `(U ×_X Xᵢ) ×_{Xᵢ} (U ×_X Xᵢ)`, one for each member of the
atlas: that family is the base change of `U ×_X U` along the surjection `∐ Xᵢ ⟶ X` of
condition (3), decomposed along the coproduct, coproducts of sheaves of sets being stable under
base change. Each member is an algebraic space over `S` by condition (2) together with the
affine case of Stacks 0AIQ, which is the step of Stacks 0AIP this library has unconditionally;
and an algebraic space over `S` receives a surjection of sheaves from an *object of the site*,
since that is what its étale scheme atlas is in Definition 025Y. The coproduct of those
atlases, one for each index, is an object of the site because the index is countable, so it is
the required `R`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsFormalAtlas`: conditions (1), (2) and (3) of
  Definition 0AIM for a family of maps into an fppf sheaf.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_representable_epi_of_countable_atlas`:
  **Stacks 0AIS**, observation (3), first half: a countable atlas produces an object of the
  site surjecting onto `X`.
* `AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_countable_atlas`:
  **Stacks 0AIS**, observation (3): a countable atlas gives the set-theoretic condition.
* `…_of_countable_atlas_of_hasQuasiCompactDiagonal`: the same statement; the source's
  hypothesis on the diagonal, which the proof does not need, has been dropped from it.

## Implementation notes

The source's hypothesis on the diagonal is not needed, and is taken nowhere; it would be
spelled as quasi-separatedness of the structure
morphism of `X` in the sense of Stacks 0ARN part (2),
`AlgebraicGeometry.FormalSpace.HasQuasiCompactDiagonal` applied to the morphism from `X` to the
terminal object of the category of fppf sheaves on the big fppf site of `S`, whose relative
self-product is `X ×_S X`. No hypothesis standing in for Stacks 0AIP is taken anywhere: the
earlier form of this file assumed the kernel pairs of representable points of `X` to be
represented by schemes, which is 0AIP-shaped and stronger than anything the source assumes, and
that hypothesis is gone. What replaces it is that a *surjection* onto `U ×_X U` from an object
of the site is all the set-theoretic condition asks for, so the étale atlases of the members of
the cover — objects of the site by definition — suffice, and no representability of the kernel
pair itself is needed.

Sheaves here take values in `Type (u + 1)` while the site has morphisms in `Type u`, so the
representable sheaf of an object of the site is
`CategoryTheory.GrothendieckTopology.uliftYoneda`, not
`CategoryTheory.GrothendieckTopology.yoneda`. The identification of the representable sheaf of
a coproduct of the site with the coproduct of the representable sheaves is taken in that
universe-raised form from
`AlgebraicGeometry.BigFppfOver.isColimitUliftYonedaSigmaCofan`, which sits beside the unraised
`AlgebraicGeometry.BigFppfOver.isColimit_yoneda_sigmaCofan` in
`StacksFrontier/AlgebraicGeometry/Spaces/FiniteCoproduct.lean`.

## References

* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0AIQ](https://stacks.math.columbia.edu/tag/0AIQ)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 05VM](https://stacks.math.columbia.edu/tag/05VM)
* [Stacks Project, Tag 0ARN](https://stacks.math.columbia.edu/tag/0ARN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A family as in Definition 0AIM -/

/-- **Conditions (1), (2) and (3) of Stacks 0AIM** for a family of maps `f i : Xi i ⟶ X` of
fppf sheaves on the big fppf site of `S`: each `Xi i` is an affine formal algebraic space, each
`f i` is representable by algebraic spaces and étale, and the induced map from the coproduct is
a surjection of sheaves.

This is the hypothesis `AlgebraicGeometry.FormalSpace.IsFormalAlgebraicSpace` asks for, minus
the set-theoretic condition of Stacks 0AIS: a formal algebraic space is an fppf sheaf
satisfying the set-theoretic condition which admits such a family. -/
abbrev IsFormalAtlas (X : FppfSheaf B S hS) {I : Type (u + 1)} (Xi : I → FppfSheaf B S hS)
    (f : ∀ i, Xi i ⟶ X) : Prop :=
  letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  (∀ i, IsAffineFormalAlgebraicSpace B S hS (Xi i)) ∧
    (∀ i, ∃ hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (f i).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) (f i).hom hfi) ∧
    Sheaf.IsLocallySurjective (Sigma.desc f)

/-- A formal algebraic space over `S` admits a family as in conditions (1), (2) and (3) of
Definition 0AIM: that is what its definition provides, on top of the set-theoretic condition of
Stacks 0AIS. -/
theorem exists_isFormalAtlas {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) :
    ∃ (I : Type (u + 1)) (Xi : I → FppfSheaf B S hS) (f : ∀ i, Xi i ⟶ X),
      IsFormalAtlas B S hS X Xi f := by
  obtain ⟨-, I, Xi, f, hXi, hf, hcover⟩ := hX
  exact ⟨I, Xi, f, hXi, hf, hcover⟩

/-! ### Observation (3), first half: a countable atlas is dominated by one object of the site -/

/-- Given epimorphisms `b i : P i ⟶ Y i`, an epimorphism `∐ Y ⟶ X` assembled from `g i`, and
a colimit cofan on `P`, the map out of its cone point induced by the `b i ≫ g i` is an epimorphism.
-/
private theorem epi_desc_cofan_of_epi {C : Type*} [Category C] {I : Type*} {P Y : I → C} {X : C}
    [HasCoproduct P] [HasCoproduct Y] (b : ∀ i, P i ⟶ Y i) [∀ i, Epi (b i)]
    (g : ∀ i, Y i ⟶ X) [Epi (Sigma.desc g)] {c : Cofan P} (hc : IsColimit c) :
    Epi (hc.desc (Cofan.mk X fun i ↦ b i ≫ g i)) := by
  let m : (∐ P) ⟶ ∐ Y := Sigma.desc fun i ↦ b i ≫ Sigma.ι Y i
  have hm : ∀ i, Sigma.ι P i ≫ m = b i ≫ Sigma.ι Y i := fun i ↦ Sigma.ι_comp_desc _ _
  have hmap : Epi m := by
    refine ⟨fun v w hvw ↦ Sigma.hom_ext _ _ fun i ↦ (cancel_epi (b i)).mp ?_⟩
    rw [← Category.assoc, ← Category.assoc, ← hm i, Category.assoc, Category.assoc, hvw]
  have hdesc : Epi (Sigma.desc fun i ↦ b i ≫ g i) := by
    have hfac : (Sigma.desc fun i ↦ b i ≫ g i) = m ≫ Sigma.desc g := by
      refine Sigma.hom_ext _ _ fun i ↦ ?_
      rw [Sigma.ι_comp_desc, ← Category.assoc, hm i, Category.assoc, Sigma.ι_comp_desc]
    rw [hfac]
    exact epi_comp _ _
  let e := (coproductIsCoproduct P).coconePointUniqueUpToIso hc
  have het : e.hom ≫ hc.desc (Cofan.mk X fun i ↦ b i ≫ g i) = Sigma.desc fun i ↦ b i ≫ g i := by
    refine Sigma.hom_ext _ _ fun i ↦ ?_
    have hi : Sigma.ι P i ≫ e.hom = c.ι.app ⟨i⟩ :=
      IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct P) hc (Discrete.mk i)
    rw [← Category.assoc, hi, Sigma.ι_comp_desc]
    exact hc.fac (Cofan.mk X fun i ↦ b i ≫ g i) (Discrete.mk i)
  have : Epi (e.hom ≫ hc.desc (Cofan.mk X fun i ↦ b i ≫ g i)) := by rw [het]; exact hdesc
  exact epi_of_epi e.hom _

/-- **Stacks 0AIS, observation (3), first half.** Let `{Xᵢ ⟶ X}` be a family of maps of fppf
sheaves over `S` satisfying conditions (1), (2) and (3) of Definition 0AIM, with a *countable*
index. Then there is an object `U` of the big fppf site of `S` and a surjection of fppf sheaves
from the sheaf it represents onto `X`.

The surjection `Uᵢ ⟶ Xᵢ` from an object of the site onto each member of the family is the
first half of the set-theoretic condition of Stacks 0AIS, which the hypothesis that `Xᵢ` is an
affine formal algebraic space carries; countability makes the coproduct `U = ∐ Uᵢ` an object of
the site, the size cutoff of a big fppf site having uncountable cofinality. -/
@[stacks 0AIS "observation (3), countable atlas"]
theorem exists_representable_epi_of_countable_atlas (X : FppfSheaf B S hS)
    {I : Type (u + 1)} [Countable I] (Xi : I → FppfSheaf B S hS) (f : ∀ i, Xi i ⟶ X)
    (hatlas : IsFormalAtlas B S hS X Xi f) :
    ∃ (U : BigFppfOver B S hS)
      (t : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U ⟶ X), Epi t := by
  classical
  let : Small.{u} I := Countable.toSmall.{u} I
  let : B.AdmitsCoproductIndex I := BigFppfSite.admitsCoproductIndex_of_countable B I
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let J := BigFppfOver.topology B S hS
  let : J.Subcanonical := bigFppfOver_subcanonical B S hS
  obtain ⟨hXi, -, hcover⟩ := hatlas
  -- Each member of the family receives a surjection from an object of the site.
  have hsurj : ∀ i, ∃ (Ui : BigFppfOver B S hS) (b : J.uliftYoneda.{u + 1}.obj Ui ⟶ Xi i),
      Epi b := by
    intro i
    obtain ⟨Ui, -, hU, -, ⟨eU⟩, -, a, ha, -, -⟩ := (hXi i).1
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
  have := hb
  have : Epi (Sigma.desc f) := (Sheaf.isLocallySurjective_iff_epi _).mp hcover
  exact ⟨U, _, epi_desc_cofan_of_epi b f hLift⟩

/-! ### Observation (3), second half: the relation produced by the atlas -/

/-- **The relation of a chart over a member of the atlas.** In any category, let `t : U ⟶ X`
and `fi : Y ⟶ X` be two morphisms, let `V = U ×_X Y` be their fibre product with projections
`v₁, v₂`, let `A = V ×_Y V` be the fibre product of `v₂` with itself with projections `a₁, a₂`,
and let `E = U ×_X U` be the fibre product of `t` with itself with projections `e₁, e₂`. Then
`A` is the fibre product of `E` with `Y` over `X`: the square with the two morphisms
`A ⟶ E`, `A ⟶ Y` assembled from the projections above is cartesian over `E ⟶ X` and `fi`.

This is the categorical content of the cover used in observation (3): a pair of points of `U`
with the same image in `X` together with a lift of that image to `Y` is the same thing as a
pair of points of `V` with the same image in `Y`. Both fibre products are taken as hypotheses
in the form `CategoryTheory.IsPullback`, so no chosen fibre products are imposed. -/
private theorem isPullback_chartRelation {C : Type*} [Category* C]
    {U X Y V A E : C} {t : U ⟶ X} {fi : Y ⟶ X}
    {v₁ : V ⟶ U} {v₂ : V ⟶ Y} (hV : IsPullback v₁ v₂ t fi)
    {a₁ a₂ : A ⟶ V} (hA : IsPullback a₁ a₂ v₂ v₂)
    {e₁ e₂ : E ⟶ U} (hE : IsPullback e₁ e₂ t t)
    (c : A ⟶ E) (hc₁ : c ≫ e₁ = a₁ ≫ v₁) (hc₂ : c ≫ e₂ = a₂ ≫ v₁) :
    IsPullback c (a₁ ≫ v₂) (e₁ ≫ t) fi := by
  have hw : c ≫ e₁ ≫ t = (a₁ ≫ v₂) ≫ fi := by
    rw [← Category.assoc, hc₁, Category.assoc, hV.w, Category.assoc]
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw (fun s ↦ ?_) ?_ ?_ ?_⟩⟩
  · exact hA.lift (hV.lift (s.fst ≫ e₁) s.snd (by simpa only [Category.assoc] using s.condition))
      (hV.lift (s.fst ≫ e₂) s.snd (by
        rw [Category.assoc, ← hE.w, ← Category.assoc]
        simpa only [Category.assoc] using s.condition))
      (by rw [hV.lift_snd, hV.lift_snd])
  · intro s
    refine hE.hom_ext ?_ ?_
    · rw [Category.assoc, hc₁, ← Category.assoc, hA.lift_fst, hV.lift_fst]
    · rw [Category.assoc, hc₂, ← Category.assoc, hA.lift_snd, hV.lift_fst]
  · intro s
    rw [← Category.assoc, hA.lift_fst, hV.lift_snd]
  · intro s m hm₁ hm₂
    refine hA.hom_ext ?_ ?_
    · rw [hA.lift_fst]
      refine hV.hom_ext ?_ ?_
      · rw [hV.lift_fst, Category.assoc, ← hc₁, ← Category.assoc, hm₁]
      · rw [hV.lift_snd, Category.assoc, hm₂]
    · rw [hA.lift_snd]
      refine hV.hom_ext ?_ ?_
      · rw [hV.lift_fst, Category.assoc, ← hc₂, ← Category.assoc, hm₁]
      · rw [hV.lift_snd, Category.assoc, ← hA.w, hm₂]

/-- A base change of a locally surjective morphism of presheaves is locally surjective: a
section of the target of the base change and a local lift of its image to the source of the
original morphism assemble into a local lift along the base change.

A `private` declaration with this name, statement and content also exists in
`StacksFrontier/AlgebraicGeometry/FormalSpace/SchemeAtlas.lean`. -/
private theorem isLocallySurjective_of_isPullback
    {C : Type*} [Category.{u} C] (J : GrothendieckTopology C)
    {F G T P : Cᵒᵖ ⥤ Type (u + 1)} {f : F ⟶ G} {g : T ⟶ G}
    {p : P ⟶ F} {q : P ⟶ T} (hpb : IsPullback p q f g)
    (hf : Presheaf.IsLocallySurjective J f) :
    Presheaf.IsLocallySurjective J q := by
  refine ⟨fun {U} s ↦ J.superset_covering ?_ (hf.imageSieve_mem (g.app _ s))⟩
  intro V i hi
  obtain ⟨x, hx⟩ := hi
  let mF : uliftYoneda.{u + 1}.obj V ⟶ F := uliftYonedaEquiv.symm x
  let mT : uliftYoneda.{u + 1}.obj V ⟶ T := uliftYonedaEquiv.symm (T.map i.op s)
  have hw : mF ≫ f = mT ≫ g := by
    apply uliftYonedaEquiv.injective
    simpa [uliftYonedaEquiv_comp, mF, mT] using
      hx.trans (NatTrans.naturality_apply g i.op s).symm
  refine ⟨uliftYonedaEquiv (hpb.lift mF mT hw), ?_⟩
  rw [← uliftYonedaEquiv_comp, hpb.lift_snd]
  exact uliftYonedaEquiv.apply_symm_apply _

/-- **Stacks 05VM for a surjective étale morphism, in the value universe of a formal algebraic
space.** A morphism of presheaves on the big fppf site of `S` which is surjective and étale
after every base change along a universe-lifted represented presheaf is locally surjective: a
single surjective étale morphism of the site generates a covering sieve, and the section lifts
over it.

A `private` declaration with this name, statement and content also exists in
`StacksFrontier/AlgebraicGeometry/FormalSpace/SectionsDoNotSeparatePoints.lean`; this is the
public version, used by
`StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOverAffineSetCondition`. -/
public theorem isLocallySurjective_of_surjective_etale_uliftYoneda
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (f : F ⟶ G)
    (hs : (MorphismProperty.relative (uliftYoneda.{u + 1}) (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    (he : (MorphismProperty.relative (uliftYoneda.{u + 1}) (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f := by
  constructor
  intro T y
  let ξ : (uliftYoneda.{u + 1}).obj T ⟶ G := uliftYonedaEquiv.symm y
  let q := hs.rep.snd ξ
  have hbase := Space.singleton_mem_bigFppf_topology B q.left
    (hs.property_snd ξ) (he.property ξ (hs.rep.fst ξ) q (hs.rep.isPullback ξ))
  have hcover : Sieve.generate (Presieve.singleton q) ∈
      BigFppfOver.topology B S hS T := by
    change Sieve.generate (Presieve.singleton q) ∈ B.topology.over (B.obj hS) T
    rw [B.topology.mem_over_iff, Sieve.overEquiv_generate,
      ← Sieve.arrows_generate_map_eq_functorPushforward, Sieve.generate_sieve,
      Presieve.map_singleton]
    exact hbase
  apply (BigFppfOver.topology B S hS).superset_covering _ hcover
  apply (Sieve.generate_le_iff _ _).mpr
  rintro _ _ ⟨⟩
  refine ⟨uliftYonedaEquiv (hs.rep.fst ξ), ?_⟩
  have hw := congrArg uliftYonedaEquiv (hs.rep.isPullback ξ).w
  have hn := uliftYonedaEquiv_naturality ξ q.op
  exact (uliftYonedaEquiv_comp _ _).symm.trans (hw.trans
    (by simpa only [q, Quiver.Hom.unop_op, ξ, Equiv.apply_symm_apply] using hn.symm))

/-- **Stacks 05VM for a surjective étale morphism, in the value universe of a formal algebraic
space.** A morphism of presheaves on the big fppf site of `S` which is surjective and étale
after every base change along a universe-lifted represented presheaf is locally surjective: a
single surjective étale morphism of the site generates a covering sieve, and the section lifts
over it.

A `private` declaration with this name, statement and content also exists in
`StacksFrontier/AlgebraicGeometry/FormalSpace/SectionsDoNotSeparatePoints.lean`.

The file-private form of `isLocallySurjective_of_surjective_etale_uliftYoneda`. -/
private alias isLocallySurjective_of_surjective_etale :=
    isLocallySurjective_of_surjective_etale_uliftYoneda

/-- **An algebraic space over `S` receives a surjection of fppf sheaves from an object of the
site.** This is the étale scheme atlas of the definition of an algebraic space (Stacks 025Y),
which is an object of the chosen big fppf site, read as a surjection of sheaves by Stacks
05VM. -/
private theorem exists_epi_uliftYoneda_of_isAlgebraicSpaceULift (A : FppfSheaf B S hS)
    (hA : Space.IsAlgebraicSpaceULift.{u + 1} B S hS A.obj) :
    ∃ (R : BigFppfOver B S hS)
      (α : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj R ⟶ A), Epi α := by
  let J := BigFppfOver.topology B S hS
  obtain ⟨R, a, hsurj, hetale⟩ := hA.exists_atlas
  have hls : Presheaf.IsLocallySurjective J a :=
    isLocallySurjective_of_surjective_etale B S hS a hsurj hetale
  refine ⟨R, ⟨(J.uliftYonedaCompSheafToPresheaf.{u + 1}.app R).hom ≫ a⟩, ?_⟩
  rw [← Sheaf.isLocallySurjective_iff_epi]
  exact Presheaf.isLocallySurjective_comp J _ a

/-- **The relation of a representable point over a member of the atlas is an algebraic space.**
Let `fi : Xᵢ ⟶ X` be a morphism of fppf sheaves over `S` from an affine formal algebraic space
which is representable by algebraic spaces, and let `t` be a point of `X` with values in an
object of the site. Then the fibre product over `Xᵢ` of the chart `U ×_X Xᵢ` with itself is an
algebraic space over `S`.

This is `AlgebraicGeometry.FormalSpace.isAlgebraicSpaceULift_pullback_snd_pullback_snd`, the
step of the proof of Stacks 0AIP which this library has unconditionally, transported from the
chosen fibre products of presheaves to those of sheaves. -/
private theorem isAlgebraicSpaceULift_pullback_snd_self {X Xi : FppfSheaf B S hS}
    (fi : Xi ⟶ X) (hXi : IsAffineFormalAlgebraicSpace B S hS Xi)
    (hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS fi.hom)
    {U : BigFppfOver B S hS}
    (t : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U ⟶ X) :
    Space.IsAlgebraicSpaceULift.{u + 1} B S hS
      (pullback (pullback.snd t fi) (pullback.snd t fi)).obj := by
  let J := BigFppfOver.topology B S hS
  let F := sheafToPresheaf J (Type (u + 1))
  have hUalg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS ((J.uliftYoneda.{u + 1}.obj U).obj) :=
    Space.isAlgebraicSpaceULift_of_iso B S hS
      (J.uliftYonedaCompSheafToPresheaf.{u + 1}.app U).symm
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS U)
  have hbase := isAlgebraicSpaceULift_pullback_snd_pullback_snd B S hS fi hXi hfi t t
    hUalg hUalg
  let iso1 : F.obj (pullback t fi) ≅ pullback t.hom fi.hom := PreservesPullback.iso F t fi
  have hv2 : F.map (pullback.snd t fi) = iso1.hom ≫ pullback.snd t.hom fi.hom :=
    (PreservesPullback.iso_hom_snd F t fi).symm
  have hApre : IsPullback (F.map (pullback.fst (pullback.snd t fi) (pullback.snd t fi)))
      (F.map (pullback.snd (pullback.snd t fi) (pullback.snd t fi)))
      (F.map (pullback.snd t fi)) (F.map (pullback.snd t fi)) :=
    (IsPullback.of_hasPullback _ _).map F
  have hApre2 : IsPullback
      (F.map (pullback.fst (pullback.snd t fi) (pullback.snd t fi)) ≫ iso1.hom)
      (F.map (pullback.snd (pullback.snd t fi) (pullback.snd t fi)) ≫ iso1.hom)
      (pullback.snd t.hom fi.hom) (pullback.snd t.hom fi.hom) := by
    refine hApre.of_iso (Iso.refl _) iso1 iso1 (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp [hv2]
    · simp [hv2]
  exact Space.isAlgebraicSpaceULift_of_iso B S hS
    (hApre2.isoIsPullback _ _ (IsPullback.of_hasPullback _ _)).symm hbase

/-- **Stacks 0AIS, observation (3).** Let `{Xᵢ ⟶ X}` be a family of maps of fppf sheaves over
`S` satisfying conditions (1), (2) and (3) of Definition 0AIM with a *countable* index. Then
`X` satisfies the set-theoretic condition of Stacks 0AIS.

Countability provides the object `U` of the site surjecting onto `X`
(`AlgebraicGeometry.FormalSpace.exists_representable_epi_of_countable_atlas`). For the relation
it provides the second half as well. The kernel pair `U ×_X U` is covered by the family of
fibre products `(U ×_X Xᵢ) ×_{Xᵢ} (U ×_X Xᵢ)`, one for each member of the atlas: that family
is the base change of `U ×_X U` along the surjection `∐ Xᵢ ⟶ X` of condition (3), decomposed
along the coproduct, coproducts of sheaves of sets being stable under base change. Each member
is an algebraic space over `S` — this is the step of Stacks 0AIP available unconditionally in
this library, `AlgebraicGeometry.FormalSpace.isAlgebraicSpaceULift_pullback_snd_pullback_snd` —
and an algebraic space over `S` receives a surjection of sheaves from an *object of the site*,
that being what its étale scheme atlas is by Definition 025Y. The coproduct of those atlases,
one for each index, is an object of the site because the index is countable and the size cutoff
of a big fppf site has uncountable cofinality; it is the required `R`. -/
@[stacks 0AIS "observation (3)"]
theorem satisfiesSetTheoreticCondition_of_countable_atlas (X : FppfSheaf B S hS)
    {I : Type (u + 1)} [Countable I] (Xi : I → FppfSheaf B S hS) (f : ∀ i, Xi i ⟶ X)
    (hatlas : IsFormalAtlas B S hS X Xi f) :
    SatisfiesSetTheoreticCondition B S hS X := by
  classical
  let : Small.{u} I := Countable.toSmall.{u} I
  let : B.AdmitsCoproductIndex I := BigFppfSite.admitsCoproductIndex_of_countable B I
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let J := BigFppfOver.topology B S hS
  let : J.Subcanonical := bigFppfOver_subcanonical B S hS
  obtain ⟨hXi, hfrep, hcover⟩ := hatlas
  obtain ⟨U, t, ht⟩ :=
    exists_representable_epi_of_countable_atlas B S hS X Xi f ⟨hXi, hfrep, hcover⟩
  -- The kernel pair of `t`, with its projection to `X`, and the base change of that
  -- projection along the surjection from the coproduct of the atlas.
  have hEsq : IsPullback (pullback.fst t t) (pullback.snd t t) t t := IsPullback.of_hasPullback t t
  have hÊ : IsPullback (pullback.fst (pullback.fst t t ≫ t) (Sigma.desc f))
      (pullback.snd (pullback.fst t t ≫ t) (Sigma.desc f)) (pullback.fst t t ≫ t)
      (Sigma.desc f) := IsPullback.of_hasPullback _ _
  have hê : Epi (pullback.fst (pullback.fst t t ≫ t) (Sigma.desc f)) := by
    rw [← Sheaf.isLocallySurjective_iff_epi]
    exact isLocallySurjective_of_isPullback J
      (hÊ.flip.map (sheafToPresheaf J (Type (u + 1)))) hcover
  -- The cover of the kernel pair by the relations of `t` over the members of the atlas.
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
    · rw [hÊ.lift_fst, Sigma.ι_comp_desc]
      exact hc i
    · rw [hÊ.lift_snd]
      simp
  choose c' hc'fac hc' using hrel'
  obtain ⟨hcofan⟩ := Sheaf.nonempty_isColimit_cofanMk_of_isPullback J (Sigma.ι Xi)
    (coproductIsCoproduct Xi) (pullback.snd (pullback.fst t t ≫ t) (Sigma.desc f)) c' _ hc'
  -- The cover is jointly surjective: the coproduct of its members is the base change of the
  -- kernel pair along the surjection from the coproduct of the atlas.
  have hdesc : Epi (Sigma.desc c) := by
    have heq : Sigma.desc c =
        (Sigma.desc c') ≫ pullback.fst (pullback.fst t t ≫ t) (Sigma.desc f) := by
      refine Sigma.hom_ext _ _ fun i ↦ ?_
      rw [Sigma.ι_comp_desc, ← Category.assoc, Sigma.ι_comp_desc, hc'fac i]
    have hiso : Sigma.desc c' = ((coproductIsCoproduct fun i ↦
        pullback (pullback.snd t (f i)) (pullback.snd t (f i))).coconePointUniqueUpToIso
          hcofan).hom := by
      refine Sigma.hom_ext _ _ fun i ↦ ?_
      rw [Sigma.ι_comp_desc]
      exact (IsColimit.comp_coconePointUniqueUpToIso_hom
        (coproductIsCoproduct fun i ↦ pullback (pullback.snd t (f i)) (pullback.snd t (f i)))
        hcofan (Discrete.mk i)).symm
    rw [heq, hiso]
    exact @epi_comp _ _ _ _ _ _ inferInstance _ hê
  -- Each member of the cover is an algebraic space over `S`, hence receives a surjection of
  -- sheaves from an object of the site.
  have halg : ∀ i, Space.IsAlgebraicSpaceULift.{u + 1} B S hS
      (pullback (pullback.snd t (f i)) (pullback.snd t (f i))).obj := fun i ↦
    isAlgebraicSpaceULift_pullback_snd_self B S hS (f i) (hXi i) (hfrep i).choose t
  choose R α hα using fun i ↦
    exists_epi_uliftYoneda_of_isAlgebraicSpaceULift B S hS _ (halg i)
  -- The coproduct of those objects of the site is an object of the site, and it surjects onto
  -- the kernel pair.
  have hLift : IsColimit (Cofan.mk (J.uliftYoneda.{u + 1}.obj (BigFppfOver.sigmaObj B S hS R))
      fun i ↦ J.uliftYoneda.{u + 1}.map (BigFppfOver.sigmaIncl B S hS R i)) :=
    BigFppfOver.isColimitUliftYonedaSigmaCofan B S hS R
  have := hα
  have : Epi (Sigma.desc c) := hdesc
  exact ⟨U, BigFppfOver.sigmaObj B S hS R, J.uliftYoneda.{u + 1}.obj U,
    J.uliftYoneda.{u + 1}.obj (BigFppfOver.sigmaObj B S hS R),
    ⟨J.uliftYonedaCompSheafToPresheaf.{u + 1}.app U⟩,
    ⟨J.uliftYonedaCompSheafToPresheaf.{u + 1}.app (BigFppfOver.sigmaObj B S hS R)⟩, t, ht,
    _, epi_desc_cofan_of_epi α c hLift⟩
/-- **Stacks 0AIS, observation (3), without the source's diagonal hypothesis.** Let
`{Xᵢ ⟶ X}` be a family of maps of fppf sheaves over `S` satisfying conditions (1), (2) and
(3) of Definition 0AIM with a *countable* index. Then `X` satisfies the set-theoretic
condition of Stacks 0AIS. The source also asks the diagonal of `X` to be quasi-compact, that
is, `X` to be quasi-separated over `S`; that hypothesis is unused and is not taken here.

Quasi-separatedness of `X` over `S` is quasi-compactness of the relative diagonal of its
structure morphism in the sense of Stacks 0ARN part (2), the structure morphism being the
morphism to the terminal object of the category of fppf sheaves on the big fppf site of `S`,
whose relative self-product is therefore `X ×_S X`. It is the source's hypothesis, and the
source is right that it suffices; it is not needed, and
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_countable_atlas` proves the
same conclusion from the countable atlas alone. The reason is that the source bounds the size
of the relation `R` by that of `U ×_S U`, for which it needs the diagonal to be tame, whereas
the argument here never leaves the site: the relation is assembled from the étale scheme
atlases of the members of a countable cover of `U ×_X U`, and those are objects of the site by
the definition of an algebraic space. -/
@[stacks 0AIS "observation (3), the source's quasi-compact diagonal"]
theorem satisfiesSetTheoreticCondition_of_countable_atlas_of_hasQuasiCompactDiagonal
    (X : FppfSheaf B S hS) {I : Type (u + 1)} [Countable I] (Xi : I → FppfSheaf B S hS)
    (f : ∀ i, Xi i ⟶ X) (hatlas : IsFormalAtlas B S hS X Xi f) :
    SatisfiesSetTheoreticCondition B S hS X :=
  satisfiesSetTheoreticCondition_of_countable_atlas B S hS X Xi f hatlas

end AlgebraicGeometry.FormalSpace

end
