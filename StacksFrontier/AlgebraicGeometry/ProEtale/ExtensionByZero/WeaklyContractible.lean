module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AffineIndEtaleLimits
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.AffineIndEtaleAdjunction
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallBaseChange
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksCore.Tactic.StacksAttribute

/-!
# Inverse image at a weakly contractible affine pro-étale object

Let `i : Z ⟶ X` be a closed immersion of affine objects of a chosen big pro-étale site. On the
affine ind-étale sites, base change along `i` is right adjoint to the lift of affine ind-étale
objects, so inverse image along base change is the *sheafification* of restriction along the
lift. At a weakly contractible object `V` of the affine ind-étale site of `Z` that
sheafification is invisible: the covering families of the site are finite, their total maps
have sections over `V`, and a sheaf of sets turns the finite coproducts of the site into
products, so sheafification is already bijective on sections over `V`.

Restriction from the small pro-étale sites to the affine ind-étale sites is an equivalence of
topoi, and it carries base change on the small sites to base change on the affine ind-étale
sites. Combining the two gives the statement wanted: inverse image of a sheaf on the small
pro-étale site of `X`, evaluated at `V`, is the sheaf evaluated at the lift of `V`.

## Main results

* `AlgebraicGeometry.ProEtale.affineIndEtaleBaseChangeInclusionIso`: base change of the affine
  ind-étale sites is the restriction of base change of the small pro-étale sites.
* `AlgebraicGeometry.ProEtale.affineIndEtaleSheafPullbackIsoLiftOfCategory`: inverse image along
  base change of the affine ind-étale sites is the sheafified restriction along the lift, for an
  arbitrary coefficient category;
  `AlgebraicGeometry.ProEtale.affineIndEtaleSheafPullbackIsoLift` is its instance at sheaves of
  sets in the universe of the sites.
* `AlgebraicGeometry.ProEtale.affineIndEtaleSheafPullbackRestrictionIsoOfCategory`: restriction
  to the affine ind-étale sites identifies the two inverse images, for an arbitrary coefficient
  category; `AlgebraicGeometry.ProEtale.affineIndEtaleSheafPullbackRestrictionIso` is its
  instance at sheaves of sets in the universe of the sites.
* `AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.bijective_toSheafify_app` and
  `AlgebraicGeometry.ProEtale.affineIndEtaleSheafificationEvaluationIso`: at a weakly
  contractible object sheafification is bijective on sections, so the sheafification above may
  be dropped.
* `AlgebraicGeometry.ProEtale.proetaleInverseImage_sections_iso_affineIndEtaleLift`: at a weakly
  contractible affine ind-étale object of the closed fibre, inverse image is evaluation at the
  lift, naturally in the sheaf.

## Implementation notes

The two evaluations are compared as functors from sheaves of sets on the small pro-étale site
of `X` to sets, so the isomorphism includes its naturality in the sheaf. The affine-site object
is viewed in the small pro-étale site through the canonical inclusion, and both sites are those
of the chosen big pro-étale site used for base change.

## References

* [Stacks Project, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL)
-/

@[expose] public noncomputable section


open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.ProEtale

/-! ### Local bijectivity of sheafification at a general universe -/

section Sheafification

universe w w' t

variable {C : Type w} [Category.{w'} C] (J : GrothendieckTopology C) [UnivLE.{max w w', t}]

open GrothendieckTopology.Plus

/-- The plus construction is locally surjective: a section of `P⁺` over `U` is represented by
a family of sections of `P` over a covering of `U`. -/
private instance isLocallySurjective_toPlus (P : Cᵒᵖ ⥤ Type t) :
    Presheaf.IsLocallySurjective J (J.toPlus P) where
  imageSieve_mem x := by
    obtain ⟨S, x, rfl⟩ := exists_rep x
    refine J.superset_covering (fun Y f hf => ⟨x.1 ⟨Y, f, hf⟩, ?_⟩) S.2
    rw [toPlus_eq_mk, res_mk_eq_mk_pullback, eq_mk_iff_exists]
    refine ⟨S.pullback f, homOfLE le_top, 𝟙 _, ?_⟩
    ext ⟨Z, g, hg⟩
    simpa using!
      x.2 { fst.hf := hf, snd.hf := S.1.downward_closed hf g, r.g₁ := g, r.g₂ := 𝟙 Z, .. }

/-- The plus construction is locally injective: two sections of `P` with the same image in
`P⁺` agree on a covering. -/
private instance isLocallyInjective_toPlus (P : Cᵒᵖ ⥤ Type t) :
    Presheaf.IsLocallyInjective J (J.toPlus P) where
  equalizerSieve_mem {X} x y h := by
    rw [toPlus_eq_mk, toPlus_eq_mk, eq_mk_iff_exists] at h
    obtain ⟨W, h₁, h₂, eq⟩ := h
    exact J.superset_covering (fun Y f hf => congr_fun (congr_arg Subtype.val eq) ⟨Y, f, hf⟩) W.2

/-- The map to the double plus construction is the composite of the two plus maps. -/
private lemma toSheafify_eq_toPlus_comp (P : Cᵒᵖ ⥤ Type t) :
    J.toSheafify P = J.toPlus P ≫ J.toPlus (J.plusObj P) := by
  change J.toPlus P ≫ J.plusMap (J.toPlus P) = _
  rw [GrothendieckTopology.plusMap_toPlus]

/-- The map to the double plus construction is locally surjective. -/
private lemma isLocallySurjective_plusPlus (P : Cᵒᵖ ⥤ Type t) :
    Presheaf.IsLocallySurjective J (J.toSheafify P) := by
  rw [toSheafify_eq_toPlus_comp]
  exact Presheaf.isLocallySurjective_comp J (J.toPlus P) (J.toPlus (J.plusObj P))

/-- The map to the double plus construction is locally injective. -/
private lemma isLocallyInjective_plusPlus (P : Cᵒᵖ ⥤ Type t) :
    Presheaf.IsLocallyInjective J (J.toSheafify P) := by
  rw [toSheafify_eq_toPlus_comp]
  exact Presheaf.isLocallyInjective_comp J (J.toPlus P) (J.toPlus (J.plusObj P))

/-- Sheafification is locally surjective, for sheaves of types at any universe above that of
the site. -/
private lemma isLocallySurjective_toSheafify (P : Cᵒᵖ ⥤ Type t) :
    Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P) := by
  have h := isLocallySurjective_plusPlus J P
  rw [← toSheafify_plusPlusIsoSheafify_hom]
  exact Presheaf.isLocallySurjective_comp J _ _

/-- Sheafification is locally injective, for sheaves of types at any universe above that of
the site. -/
private lemma isLocallyInjective_toSheafify (P : Cᵒᵖ ⥤ Type t) :
    Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P) := by
  have h := isLocallyInjective_plusPlus J P
  rw [← toSheafify_plusPlusIsoSheafify_hom]
  exact Presheaf.isLocallyInjective_comp J _ _

end Sheafification


/-! ### Sections of a sheafification at a weakly contractible object -/

/-- A presheaf taking a coproduct to a product has its sections over the coproduct given by
families of sections over the summands. -/
private lemma bijective_sigma_sections {D : Type*} [Category D] {I : Type*} (A : I → D)
    [HasCoproduct A] (P : Dᵒᵖ ⥤ Type*)
    [PreservesLimit (Discrete.functor (fun j ↦ op (A j))) P] :
    Function.Bijective (fun x : P.obj (op (∐ A)) ↦ fun j ↦ P.map (Sigma.ι A j).op x) := by
  have hlim : IsLimit (Fan.mk (P.obj (op (∐ A))) (fun j ↦ P.map (Sigma.ι A j).op)) :=
    (isLimitMapConeFanMkEquiv P (fun j ↦ op (A j)) _)
      (isLimitOfPreserves P (Cofan.IsColimit.op (coproductIsCoproduct A)))
  rw [Function.bijective_iff_existsUnique]
  intro x
  obtain ⟨s, hs, hu⟩ := (Types.isLimit_iff _).mp ⟨hlim⟩ (fun j ↦ x j.as) (by
    rintro ⟨j⟩ ⟨k⟩ f
    obtain rfl := Discrete.eq_of_hom f
    simp)
  exact ⟨s, funext (fun j ↦ hs ⟨j⟩), fun t ht ↦ hu t (fun j ↦ congrFun ht j.as)⟩

namespace AffineIndEtaleProetale

/-- At a weakly contractible object of the affine ind-étale site, a locally bijective morphism
of presheaves of sets whose target is a sheaf is bijective on sections, as soon as its source
already takes the finite coproducts of the site to products. -/
theorem bijective_app_of_isLocallyBijective (B : BigProetaleSite.{u}) (S : B.Scheme)
    [IsAffine S.obj]
    (V : AffineIndEtaleProetale B S) (hV : (topology B S).IsWeaklyContractible V)
    {P Q : (AffineIndEtaleProetale B S)ᵒᵖ ⥤ Type (max (u + 1) v)} (φ : P ⟶ Q)
    (hQ : Presheaf.IsSheaf (topology B S) Q)
    (hinj : Presheaf.IsLocallyInjective (topology B S) φ)
    (hsurj : Presheaf.IsLocallySurjective (topology B S) φ)
    (hP : ∀ {I : Type (u + 1)} [Finite I] (A : I → AffineIndEtaleProetale B S),
      Cardinal.mk I ≤ B.coveringBound →
      PreservesLimit (Discrete.functor (fun j ↦ op (A j))) P) :
    Function.Bijective (φ.app (op V)) := by
  constructor
  · intro x y hxy
    obtain ⟨E, hE, hle⟩ := exists_isCovering_presieve₀_le B S
      (Presheaf.equalizerSieve_mem (topology B S) φ x y hxy)
    have : Finite E.I₀ := hE.2
    have := hP E.X hE.1.2
    obtain ⟨s, hs⟩ := exists_section_sigmaDesc_of_isWeaklyContractible B S hV E hE
    have heq : P.map (Sigma.desc E.f).op x = P.map (Sigma.desc E.f).op y := by
      apply (bijective_sigma_sections E.X P).injective
      funext j
      simpa only [← Functor.map_comp_apply, ← op_comp, Sigma.ι_comp_desc] using
        (show P.map (E.f j).op x = P.map (E.f j).op y from
          hle _ _ (Presieve.ofArrows.mk j))
    simpa only [← Functor.map_comp_apply, ← op_comp, hs, op_id, Functor.map_id_apply] using
      congrArg (P.map s.op) heq
  · intro x
    obtain ⟨E, hE, hle⟩ := exists_isCovering_presieve₀_le B S
      (Presheaf.imageSieve_mem (topology B S) φ (U := op V) x)
    have : Finite E.I₀ := hE.2
    have := hP E.X hE.1.2
    obtain ⟨s, hs⟩ := exists_section_sigmaDesc_of_isWeaklyContractible B S hV E hE
    have hx (j : E.I₀) : ∃ y, φ.app (op (E.X j)) y = Q.map (E.f j).op x :=
      hle _ _ (Presieve.ofArrows.mk j)
    choose y hy using hx
    obtain ⟨t, ht⟩ := (bijective_sigma_sections E.X P).surjective y
    have ht' (j : E.I₀) : P.map (Sigma.ι E.X j).op t = y j := congrFun ht j
    have := sheaf_preservesProduct.{u, v} B S ⟨Q, hQ⟩ E.X hE.1.2
    have heq : φ.app (op (∐ E.X)) t = Q.map (Sigma.desc E.f).op x := by
      apply (bijective_sigma_sections E.X Q).injective
      funext j
      change Q.map (Sigma.ι E.X j).op (φ.app (op (∐ E.X)) t) =
        Q.map (Sigma.ι E.X j).op (Q.map (Sigma.desc E.f).op x)
      rw [← φ.naturality_apply (Sigma.ι E.X j).op t, ht' j, hy j]
      simp only [← Functor.map_comp_apply, ← op_comp, Sigma.ι_comp_desc]
    refine ⟨P.map s.op t, ?_⟩
    rw [φ.naturality_apply s.op t, heq]
    change Q.map s.op (Q.map (Sigma.desc E.f).op x) = x
    simp only [← Functor.map_comp_apply, ← op_comp, hs, op_id, Functor.map_id_apply]


/-- At a weakly contractible object of the affine ind-étale site, sheafification is bijective
on sections for any presheaf that already takes the finite coproducts of the site to products.
-/
theorem bijective_toSheafify_app (B : BigProetaleSite.{u}) (S : B.Scheme) [IsAffine S.obj]
    (V : AffineIndEtaleProetale B S) (hV : (topology B S).IsWeaklyContractible V)
    (P : (AffineIndEtaleProetale B S)ᵒᵖ ⥤ Type (max (u + 1) v))
    (hP : ∀ {I : Type (u + 1)} [Finite I] (A : I → AffineIndEtaleProetale B S),
      Cardinal.mk I ≤ B.coveringBound →
      PreservesLimit (Discrete.functor (fun j ↦ op (A j))) P) :
    Function.Bijective ((toSheafify (topology B S) P).app (op V)) :=
  bijective_app_of_isLocallyBijective B S V hV (toSheafify (topology B S) P)
    ((presheafToSheaf (topology B S) (Type (max (u + 1) v))).obj P).property
    (isLocallyInjective_toSheafify _ P) (isLocallySurjective_toSheafify _ P) hP

end AffineIndEtaleProetale

/-! ### Base change on the affine ind-étale sites and inverse image -/

section

universe w w'

variable (B : BigProetaleSite.{u}) {Z X : B.Scheme} (i : Z ⟶ X)
  [IsAffine Z.obj] [IsAffine X.obj] [IsClosedImmersion (B.inclusion.map i)]

/-- Base change on the affine ind-étale sites is compatible with base change on the small
pro-étale sites: both compute the fibre product with `Z`. -/
def affineIndEtaleBaseChangeInclusionIso :
    affineIndEtaleBaseChange B i ⋙ AffineIndEtaleProetale.inclusion B Z ≅
      AffineIndEtaleProetale.inclusion B X ⋙ smallProetaleBaseChange B Z X i := by
  let aX := AffineIndEtaleProetale.inclusion B X
  let aZ := AffineIndEtaleProetale.inclusion B Z
  let sX := SmallProetale.inclusion B X.obj X.property
  let sZ := SmallProetale.inclusion B Z.obj Z.property
  let u := smallProetaleBaseChange B Z X i
  let b := affineIndEtaleBaseChange B i
  have e₁ : b ⋙ aZ ⋙ sZ ≅ aX ⋙ sX ⋙ Over.pullback i :=
    Classical.choice (affineIndEtaleBaseChange_comp_forget B i)
  have e₂ : aX ⋙ u ⋙ sZ = aX ⋙ sX ⋙ Over.pullback i := by
    rw [smallProetaleBaseChange_comp_inclusion]
  have e₃ : b ⋙ aZ ⋙ sZ ≅ aX ⋙ u ⋙ sZ := e₁.trans (eqToIso e₂.symm)
  exact Functor.fullyFaithfulCancelRight sZ e₃

/-- Inverse image along base change of the affine ind-étale sites is the sheafification of
restriction along the cocontinuous lift, naturally in the sheaf, for an arbitrary coefficient
category. -/
def affineIndEtaleSheafPullbackIsoLiftOfCategory (A : Type w) [Category.{w'} A]
    [HasWeakSheafify (AffineIndEtaleProetale.topology B Z) A]
    [∀ F : (AffineIndEtaleProetale B X)ᵒᵖ ⥤ A,
      (affineIndEtaleBaseChange B i).op.HasLeftKanExtension F] :
    Functor.sheafPullbackConstruction.sheafPullback (affineIndEtaleBaseChange B i)
        A (AffineIndEtaleProetale.topology B X)
        (AffineIndEtaleProetale.topology B Z) ≅
      sheafToPresheaf (AffineIndEtaleProetale.topology B X) A ⋙
        (Functor.whiskeringLeft (AffineIndEtaleProetale B Z)ᵒᵖ (AffineIndEtaleProetale B X)ᵒᵖ
          A).obj (affineIndEtaleLift B i).op ⋙
        presheafToSheaf (AffineIndEtaleProetale.topology B Z) A := by
  let adj := Classical.choice (affineIndEtaleLift_adj_baseChange B i)
  let e := (Functor.restrictionIsoLanOfAdjunction A adj).symm
  exact Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft
      (sheafToPresheaf (AffineIndEtaleProetale.topology B X) A) e)
    (presheafToSheaf (AffineIndEtaleProetale.topology B Z) A)

/-- Restriction to the affine ind-étale sites carries inverse image along base change of the
small pro-étale sites to inverse image along base change of the affine ind-étale sites, for an
arbitrary coefficient category over which the two restrictions are equivalences. -/
def affineIndEtaleSheafPullbackRestrictionIsoOfCategory (A : Type w) [Category.{w'} A]
    [HasWeakSheafify (SmallProetale.topology B Z.obj Z.property) A]
    [HasWeakSheafify (AffineIndEtaleProetale.topology B Z) A]
    [∀ F : (SmallProetale B X.obj X.property)ᵒᵖ ⥤ A,
      (smallProetaleBaseChange B Z X i).op.HasLeftKanExtension F]
    [∀ F : (AffineIndEtaleProetale B X)ᵒᵖ ⥤ A,
      (affineIndEtaleBaseChange B i).op.HasLeftKanExtension F]
    [((AffineIndEtaleProetale.inclusion B X).sheafPushforwardContinuous A
        (AffineIndEtaleProetale.topology B X)
        (SmallProetale.topology B X.obj X.property)).IsEquivalence]
    [((AffineIndEtaleProetale.inclusion B Z).sheafPushforwardContinuous A
        (AffineIndEtaleProetale.topology B Z)
        (SmallProetale.topology B Z.obj Z.property)).IsEquivalence] :
    Functor.sheafPullbackConstruction.sheafPullback (smallProetaleBaseChange B Z X i)
        A (SmallProetale.topology B X.obj X.property)
        (SmallProetale.topology B Z.obj Z.property) ⋙
      (AffineIndEtaleProetale.inclusion B Z).sheafPushforwardContinuous A
        (AffineIndEtaleProetale.topology B Z) (SmallProetale.topology B Z.obj Z.property) ≅
    (AffineIndEtaleProetale.inclusion B X).sheafPushforwardContinuous A
        (AffineIndEtaleProetale.topology B X) (SmallProetale.topology B X.obj X.property) ⋙
      Functor.sheafPullbackConstruction.sheafPullback (affineIndEtaleBaseChange B i)
        A (AffineIndEtaleProetale.topology B X)
        (AffineIndEtaleProetale.topology B Z) := by
  let JX := SmallProetale.topology B X.obj X.property
  let JZ := SmallProetale.topology B Z.obj Z.property
  let KX := AffineIndEtaleProetale.topology B X
  let KZ := AffineIndEtaleProetale.topology B Z
  let u := smallProetaleBaseChange B Z X i
  let b := affineIndEtaleBaseChange B i
  let aX := AffineIndEtaleProetale.inclusion B X
  let aZ := AffineIndEtaleProetale.inclusion B Z
  haveI : u.IsContinuous JX JZ :=
    (smallProetaleBaseChange_isMorphismOfSites B Z X i).toIsContinuous
  haveI : b.IsContinuous KX KZ := affineIndEtaleBaseChange_isContinuous B i
  haveI : aX.IsContinuous KX JX := AffineIndEtaleProetale.inclusion_isContinuous B X
  haveI : aZ.IsContinuous KZ JZ := AffineIndEtaleProetale.inclusion_isContinuous B Z
  haveI : (u.sheafPushforwardContinuous A JX JZ).IsRightAdjoint :=
    (u.sheafAdjunctionContinuous A JX JZ).isRightAdjoint
  haveI : (b.sheafPushforwardContinuous A KX KZ).IsRightAdjoint :=
    (b.sheafAdjunctionContinuous A KX KZ).isRightAdjoint
  let RX := aX.sheafPushforwardContinuous A KX JX
  let RZ := aZ.sheafPushforwardContinuous A KZ JZ
  let rX := RX.asEquivalence.inverse
  let rZ := RZ.asEquivalence.inverse
  let L := Functor.sheafPullbackConstruction.sheafPullback u A JX JZ
  let M := Functor.sheafPullbackConstruction.sheafPullback b A KX KZ
  let adjSmall := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u
    A JX JZ
  let adjApp := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
    A KX KZ
  let adjZX : RZ ⊣ rZ := RZ.asEquivalence.toAdjunction
  let adjXX : RX ⊣ rX := RX.asEquivalence.toAdjunction
  have hLeft : L ⋙ RZ ⊣ rZ ⋙ u.sheafPushforwardContinuous
      A JX JZ := adjSmall.comp adjZX
  have hRight0 : RX ⋙ M ⊣ b.sheafPushforwardContinuous
      A KX KZ ⋙ rX := adjXX.comp adjApp
  haveI : (b ⋙ aZ).IsContinuous KX JZ := Functor.isContinuous_comp b aZ KX KZ JZ
  haveI : (aX ⋙ u).IsContinuous KX JZ := Functor.isContinuous_comp aX u KX JX JZ
  let hsite := affineIndEtaleBaseChangeInclusionIso B i
  have hpush : RZ ⋙ b.sheafPushforwardContinuous A KX KZ ≅
      u.sheafPushforwardContinuous A JX JZ ⋙ RX := by
    let hc₁ := Functor.sheafPushforwardContinuousComp b aZ A KX KZ JZ
    let hc₂ := Functor.sheafPushforwardContinuousComp aX u A KX JX JZ
    exact hc₁ ≪≫ Functor.sheafPushforwardContinuousIso hsite
      A KX JZ ≪≫ hc₂.symm
  have hr : b.sheafPushforwardContinuous A KX KZ ⋙ rX ≅
      rZ ⋙ u.sheafPushforwardContinuous A JX JZ := by
    let e₁ : b.sheafPushforwardContinuous A KX KZ ⋙ rX ≅
        (rZ ⋙ RZ) ⋙ b.sheafPushforwardContinuous A KX KZ ⋙ rX :=
      (Functor.leftUnitor _).symm ≪≫
        Functor.isoWhiskerRight RZ.asEquivalence.counitIso.symm _
    let e₂ : (rZ ⋙ RZ) ⋙ b.sheafPushforwardContinuous
        A KX KZ ⋙ rX ≅
        rZ ⋙ u.sheafPushforwardContinuous A JX JZ := by
      calc
        _ ≅ rZ ⋙ (RZ ⋙ b.sheafPushforwardContinuous
            A KX KZ) ⋙ rX :=
          (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
            (Functor.associator _ _ _) _
        _ ≅ rZ ⋙ (u.sheafPushforwardContinuous
            A JX JZ ⋙ RX) ⋙ rX :=
          Functor.isoWhiskerLeft rZ (Functor.isoWhiskerRight hpush rX)
        _ ≅ (rZ ⋙ u.sheafPushforwardContinuous
            A JX JZ) ⋙ (RX ⋙ rX) :=
          Functor.isoWhiskerRight (Functor.associator rZ
            (u.sheafPushforwardContinuous A JX JZ) RX).symm rX ≪≫
            Functor.associator _ _ _
        _ ≅ rZ ⋙ u.sheafPushforwardContinuous
            A JX JZ :=
          Functor.isoWhiskerLeft _ RX.asEquivalence.unitIso.symm ≪≫ Functor.rightUnitor _
    exact e₁.trans e₂
  let hRight := Adjunction.ofNatIsoRight hRight0 hr
  exact Adjunction.leftAdjointUniq hLeft hRight

/-- Inverse image along base change of the affine ind-étale sites is the sheafification of
restriction along the cocontinuous lift, naturally in the sheaf.

This is `affineIndEtaleSheafPullbackIsoLiftOfCategory` at coefficients `Type (max (u + 1) v)`. -/
def affineIndEtaleSheafPullbackIsoLift :
    Functor.sheafPullbackConstruction.sheafPullback (affineIndEtaleBaseChange B i)
        (Type (max (u + 1) v)) (AffineIndEtaleProetale.topology B X)
        (AffineIndEtaleProetale.topology B Z) ≅
      sheafToPresheaf (AffineIndEtaleProetale.topology B X) (Type (max (u + 1) v)) ⋙
        (Functor.whiskeringLeft (AffineIndEtaleProetale B Z)ᵒᵖ (AffineIndEtaleProetale B X)ᵒᵖ
          (Type (max (u + 1) v))).obj (affineIndEtaleLift B i).op ⋙
        presheafToSheaf (AffineIndEtaleProetale.topology B Z) (Type (max (u + 1) v)) :=
  affineIndEtaleSheafPullbackIsoLiftOfCategory B i (Type (max (u + 1) v))

/-- Restriction to the affine ind-étale sites carries inverse image along base change of the
small pro-étale sites to inverse image along base change of the affine ind-étale sites.

This is `affineIndEtaleSheafPullbackRestrictionIsoOfCategory` at coefficients
`Type (max (u + 1) v)`. -/
def affineIndEtaleSheafPullbackRestrictionIso :
    Functor.sheafPullbackConstruction.sheafPullback (smallProetaleBaseChange B Z X i)
        (Type (max (u + 1) v)) (SmallProetale.topology B X.obj X.property)
        (SmallProetale.topology B Z.obj Z.property) ⋙
      (AffineIndEtaleProetale.inclusion B Z).sheafPushforwardContinuous (Type (max (u + 1) v))
        (AffineIndEtaleProetale.topology B Z) (SmallProetale.topology B Z.obj Z.property) ≅
    (AffineIndEtaleProetale.inclusion B X).sheafPushforwardContinuous (Type (max (u + 1) v))
        (AffineIndEtaleProetale.topology B X) (SmallProetale.topology B X.obj X.property) ⋙
      Functor.sheafPullbackConstruction.sheafPullback (affineIndEtaleBaseChange B i)
        (Type (max (u + 1) v)) (AffineIndEtaleProetale.topology B X)
        (AffineIndEtaleProetale.topology B Z) := by
  haveI : ((AffineIndEtaleProetale.inclusion B X).sheafPushforwardContinuous
      (Type (max (u + 1) v)) (AffineIndEtaleProetale.topology B X)
      (SmallProetale.topology B X.obj X.property)).IsEquivalence :=
    AffineIndEtaleProetale.isEquivalence_restriction.{u, max (u + 1) v} B X
  haveI : ((AffineIndEtaleProetale.inclusion B Z).sheafPushforwardContinuous
      (Type (max (u + 1) v)) (AffineIndEtaleProetale.topology B Z)
      (SmallProetale.topology B Z.obj Z.property)).IsEquivalence :=
    AffineIndEtaleProetale.isEquivalence_restriction.{u, max (u + 1) v} B Z
  exact affineIndEtaleSheafPullbackRestrictionIsoOfCategory B i (Type (max (u + 1) v))

/-- **If the sheafification is invisible at `V`, it may be dropped.** Sections of the
sheafified restriction along the lift at `V` are sections of the original sheaf at the lift of
`V`, naturally in the sheaf, as soon as the unit of sheafification is an isomorphism on sections
over `V` for each of the presheaves in play. -/
def affineIndEtaleSheafificationEvaluationIsoOfIsIso (A : Type w) [Category.{w'} A]
    [HasWeakSheafify (AffineIndEtaleProetale.topology B Z) A]
    (V : AffineIndEtaleProetale B Z)
    (hiso : ∀ F : Sheaf (AffineIndEtaleProetale.topology B X) A,
      IsIso ((toSheafify (AffineIndEtaleProetale.topology B Z)
        ((affineIndEtaleLift B i).op ⋙ F.obj)).app (op V))) :
    (sheafToPresheaf (AffineIndEtaleProetale.topology B X) A ⋙
      (Functor.whiskeringLeft _ _ A).obj (affineIndEtaleLift B i).op ⋙
      presheafToSheaf (AffineIndEtaleProetale.topology B Z) A ⋙
      sheafToPresheaf (AffineIndEtaleProetale.topology B Z) A ⋙
      (evaluation _ _).obj (op V)) ≅
    (sheafToPresheaf (AffineIndEtaleProetale.topology B X) A ⋙
      (evaluation _ _).obj (op ((affineIndEtaleLift B i).obj V))) := by
  let KX := AffineIndEtaleProetale.topology B X
  let KZ := AffineIndEtaleProetale.topology B Z
  let a := affineIndEtaleLift B i
  let L := sheafToPresheaf KX A ⋙ (Functor.whiskeringLeft _ _ A).obj a.op ⋙
    presheafToSheaf KZ A ⋙ sheafToPresheaf KZ A ⋙ (evaluation _ _).obj (op V)
  let R := sheafToPresheaf KX A ⋙ (evaluation _ _).obj (op (a.obj V))
  let η : R ⟶ L :=
    { app F := (toSheafify KZ (a.op ⋙ F.obj)).app (op V)
      naturality F G f := congr_app (toSheafify_naturality KZ
        (Functor.whiskerLeft a.op f.hom)) (op V) }
  haveI (F : Sheaf KX A) : IsIso (η.app F) := hiso F
  haveI : IsIso η := NatIso.isIso_of_isIso_app η
  exact (asIso η).symm

/-- At a weakly contractible object of the affine ind-étale site of `Z`, the sheafification in
the description of inverse image is invisible: sections of the sheafified restriction at `V`
are sections of the original sheaf at the lift of `V`, naturally in the sheaf. -/
def affineIndEtaleSheafificationEvaluationIso (V : AffineIndEtaleProetale B Z)
    (hV : (AffineIndEtaleProetale.topology B Z).IsWeaklyContractible V) :
    (sheafToPresheaf (AffineIndEtaleProetale.topology B X) (Type (max (u + 1) v)) ⋙
      (Functor.whiskeringLeft _ _ (Type (max (u + 1) v))).obj (affineIndEtaleLift B i).op ⋙
      presheafToSheaf (AffineIndEtaleProetale.topology B Z) (Type (max (u + 1) v)) ⋙
      sheafToPresheaf (AffineIndEtaleProetale.topology B Z) (Type (max (u + 1) v)) ⋙
      (evaluation _ _).obj (op V)) ≅
    (sheafToPresheaf (AffineIndEtaleProetale.topology B X) (Type (max (u + 1) v)) ⋙
      (evaluation _ _).obj (op ((affineIndEtaleLift B i).obj V))) := by
  let a := affineIndEtaleLift B i
  haveI : a.IsLeftAdjoint :=
    (Classical.choice (affineIndEtaleLift_adj_baseChange B i)).isLeftAdjoint
  refine affineIndEtaleSheafificationEvaluationIsoOfIsIso B i (Type (max (u + 1) v)) V
    (fun F ↦ ?_)
  apply (isIso_iff_bijective _).mpr
  apply AffineIndEtaleProetale.bijective_toSheafify_app B Z V hV
  intro I hI Aj hbound
  have : PreservesLimit
      (Discrete.functor (((Discrete.functor (fun j ↦ op (Aj j))) ⋙ a.op).obj ∘ Discrete.mk))
      F.obj := AffineIndEtaleProetale.sheaf_preservesProduct B X F (fun j ↦ a.obj (Aj j)) hbound
  have : PreservesLimit ((Discrete.functor (fun j ↦ op (Aj j))) ⋙ a.op) F.obj :=
    preservesLimit_of_iso_diagram F.obj Discrete.natIsoFunctor.symm
  infer_instance

/-- At an affine ind-étale object `V` of the closed fibre over which the unit of sheafification
is invertible on sections, inverse image is evaluation at the lift of `V`, naturally in the
sheaf, for an arbitrary coefficient category. -/
def proetaleInverseImage_sections_iso_affineIndEtaleLiftOfIsIso (A : Type w) [Category.{w'} A]
    [HasWeakSheafify (SmallProetale.topology B Z.obj Z.property) A]
    [HasWeakSheafify (AffineIndEtaleProetale.topology B Z) A]
    [∀ F : (SmallProetale B X.obj X.property)ᵒᵖ ⥤ A,
      (smallProetaleBaseChange B Z X i).op.HasLeftKanExtension F]
    [∀ F : (AffineIndEtaleProetale B X)ᵒᵖ ⥤ A,
      (affineIndEtaleBaseChange B i).op.HasLeftKanExtension F]
    [((AffineIndEtaleProetale.inclusion B X).sheafPushforwardContinuous A
        (AffineIndEtaleProetale.topology B X)
        (SmallProetale.topology B X.obj X.property)).IsEquivalence]
    [((AffineIndEtaleProetale.inclusion B Z).sheafPushforwardContinuous A
        (AffineIndEtaleProetale.topology B Z)
        (SmallProetale.topology B Z.obj Z.property)).IsEquivalence]
    (V : AffineIndEtaleProetale B Z)
    (hiso : ∀ F : Sheaf (AffineIndEtaleProetale.topology B X) A,
      IsIso ((toSheafify (AffineIndEtaleProetale.topology B Z)
        ((affineIndEtaleLift B i).op ⋙ F.obj)).app (op V))) :
    Functor.sheafPullbackConstruction.sheafPullback (smallProetaleBaseChange B Z X i)
        A (SmallProetale.topology B X.obj X.property)
        (SmallProetale.topology B Z.obj Z.property) ⋙
      sheafToPresheaf (SmallProetale.topology B Z.obj Z.property)
        A ⋙
      (evaluation _ _).obj (Opposite.op ((AffineIndEtaleProetale.inclusion B Z).obj V)) ≅
    sheafToPresheaf (SmallProetale.topology B X.obj X.property)
        A ⋙
      (evaluation _ _).obj
        (Opposite.op ((AffineIndEtaleProetale.inclusion B X).obj
          ((affineIndEtaleLift B i).obj V))) := by
  let JX := SmallProetale.topology B X.obj X.property
  let JZ := SmallProetale.topology B Z.obj Z.property
  let KX := AffineIndEtaleProetale.topology B X
  let KZ := AffineIndEtaleProetale.topology B Z
  let u := smallProetaleBaseChange B Z X i
  let aX := AffineIndEtaleProetale.inclusion B X
  let aZ := AffineIndEtaleProetale.inclusion B Z
  let b := affineIndEtaleBaseChange B i
  let a := affineIndEtaleLift B i
  let E_Z := (evaluation (SmallProetale B Z.obj Z.property)ᵒᵖ
    A).obj (Opposite.op (aZ.obj V))
  let E_X := (evaluation (AffineIndEtaleProetale B X)ᵒᵖ
    A).obj (Opposite.op (a.obj V))
  let E_Xsmall := (evaluation (SmallProetale B X.obj X.property)ᵒᵖ
    A).obj (Opposite.op (aX.obj (a.obj V)))
  let E_V := (evaluation (AffineIndEtaleProetale B Z)ᵒᵖ A).obj (Opposite.op V)
  let R_X := aX.sheafPushforwardContinuous A KX JX
  let R_Z := aZ.sheafPushforwardContinuous A KZ JZ
  let L := Functor.sheafPullbackConstruction.sheafPullback u A JX JZ
  let M := Functor.sheafPullbackConstruction.sheafPullback b A KX KZ
  have hsmallX : aX.IsContinuous KX JX := AffineIndEtaleProetale.inclusion_isContinuous B X
  have hsmallZ : aZ.IsContinuous KZ JZ := AffineIndEtaleProetale.inclusion_isContinuous B Z
  let eZ : R_Z ⋙ sheafToPresheaf KZ A ⋙ E_V ≅
      sheafToPresheaf JZ A ⋙ E_Z := by
    let e := aZ.sheafPushforwardContinuousCompSheafToPresheafIso
      A KZ JZ
    have hEval :
        ((sheafToPresheaf JZ A ⋙
          (Functor.whiskeringLeft (AffineIndEtaleProetale B Z)ᵒᵖ
            (SmallProetale B Z.obj Z.property)ᵒᵖ
            A).obj aZ.op) ⋙ E_V) =
        sheafToPresheaf JZ A ⋙ E_Z := by
      rfl
    exact (Functor.isoWhiskerRight e E_V).trans (eqToIso hEval)
  let eX : R_X ⋙ sheafToPresheaf KX A ⋙ E_X ≅
      sheafToPresheaf JX A ⋙ E_Xsmall := by
    let e := aX.sheafPushforwardContinuousCompSheafToPresheafIso
      A KX JX
    have hEval :
        ((sheafToPresheaf JX A ⋙
          (Functor.whiskeringLeft (AffineIndEtaleProetale B X)ᵒᵖ
            (SmallProetale B X.obj X.property)ᵒᵖ
            A).obj aX.op) ⋙ E_X) =
        sheafToPresheaf JX A ⋙ E_Xsmall := by
      rfl
    exact (Functor.isoWhiskerRight e E_X).trans (eqToIso hEval)
  have ePull : L ⋙ R_Z ≅ R_X ⋙ M :=
    affineIndEtaleSheafPullbackRestrictionIsoOfCategory B i A
  have eApp : M ⋙ sheafToPresheaf KZ A ⋙ E_V ≅
      sheafToPresheaf KX A ⋙ E_X :=
    Functor.isoWhiskerRight (affineIndEtaleSheafPullbackIsoLiftOfCategory B i A)
      (sheafToPresheaf KZ A ⋙ E_V) ≪≫
      affineIndEtaleSheafificationEvaluationIsoOfIsIso B i A V hiso
  have e₁ : L ⋙ R_Z ⋙ sheafToPresheaf KZ A ⋙ E_V ≅
      L ⋙ sheafToPresheaf JZ A ⋙ E_Z :=
    Functor.isoWhiskerLeft L eZ |>.trans (Functor.associator _ _ _).symm
  have e₂ : L ⋙ R_Z ⋙ sheafToPresheaf KZ A ⋙ E_V ≅
      R_X ⋙ M ⋙ sheafToPresheaf KZ A ⋙ E_V :=
    Functor.isoWhiskerRight ePull (sheafToPresheaf KZ A ⋙ E_V)
  have e₃ : R_X ⋙ M ⋙ sheafToPresheaf KZ A ⋙ E_V ≅
      R_X ⋙ sheafToPresheaf KX A ⋙ E_X :=
    Functor.isoWhiskerLeft R_X eApp
  have e₄ : R_X ⋙ sheafToPresheaf KX A ⋙ E_X ≅
      sheafToPresheaf JX A ⋙ E_Xsmall := eX
  exact ((e₁.symm.trans e₂).trans e₃).trans e₄


/-- At a weakly contractible affine ind-étale object of the closed fibre, inverse image is
evaluation at its lift, naturally in the sheaf. -/
@[stacks 09BL "weakly_contractible_evaluation"]
def proetaleInverseImage_sections_iso_affineIndEtaleLift (V : AffineIndEtaleProetale B Z)
    (hV : (AffineIndEtaleProetale.topology B Z).IsWeaklyContractible V) :
    Functor.sheafPullbackConstruction.sheafPullback (smallProetaleBaseChange B Z X i)
        (Type (max (u + 1) v)) (SmallProetale.topology B X.obj X.property)
        (SmallProetale.topology B Z.obj Z.property) ⋙
      sheafToPresheaf (SmallProetale.topology B Z.obj Z.property)
        (Type (max (u + 1) v)) ⋙
      (evaluation _ _).obj (Opposite.op ((AffineIndEtaleProetale.inclusion B Z).obj V)) ≅
    sheafToPresheaf (SmallProetale.topology B X.obj X.property)
        (Type (max (u + 1) v)) ⋙
      (evaluation _ _).obj
        (Opposite.op ((AffineIndEtaleProetale.inclusion B X).obj
          ((affineIndEtaleLift B i).obj V))) := by
  haveI : ((AffineIndEtaleProetale.inclusion B X).sheafPushforwardContinuous
      (Type (max (u + 1) v)) (AffineIndEtaleProetale.topology B X)
      (SmallProetale.topology B X.obj X.property)).IsEquivalence :=
    AffineIndEtaleProetale.isEquivalence_restriction.{u, max (u + 1) v} B X
  haveI : ((AffineIndEtaleProetale.inclusion B Z).sheafPushforwardContinuous
      (Type (max (u + 1) v)) (AffineIndEtaleProetale.topology B Z)
      (SmallProetale.topology B Z.obj Z.property)).IsEquivalence :=
    AffineIndEtaleProetale.isEquivalence_restriction.{u, max (u + 1) v} B Z
  let a := affineIndEtaleLift B i
  haveI : a.IsLeftAdjoint :=
    (Classical.choice (affineIndEtaleLift_adj_baseChange B i)).isLeftAdjoint
  refine proetaleInverseImage_sections_iso_affineIndEtaleLiftOfIsIso B i
    (Type (max (u + 1) v)) V (fun F ↦ ?_)
  apply (isIso_iff_bijective _).mpr
  apply AffineIndEtaleProetale.bijective_toSheafify_app B Z V hV
  intro I hI Aj hbound
  have : PreservesLimit
      (Discrete.functor (((Discrete.functor (fun j ↦ op (Aj j))) ⋙ a.op).obj ∘ Discrete.mk))
      F.obj := AffineIndEtaleProetale.sheaf_preservesProduct B X F (fun j ↦ a.obj (Aj j)) hbound
  have : PreservesLimit ((Discrete.functor (fun j ↦ op (Aj j))) ⋙ a.op) F.obj :=
    preservesLimit_of_iso_diagram F.obj Discrete.natIsoFunctor.symm
  infer_instance

end

end AlgebraicGeometry.ProEtale
end
