module

public import StacksFrontier.AlgebraicGeometry.Quot.ContractionUniquenessCompleteSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionSemicontinuity
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallerBaseSubspaces
public import StacksFrontier.AlgebraicGeometry.Quot.ContractionDominanceClosedFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FpqcDescentAlongDominant
import all StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticDensity

/-!
# Uniqueness of contractions over a complete local object of a big fppf site

Let `W` be an object of the big fppf site of a scheme `S` whose underlying scheme is the spectrum
of a complete Noetherian local ring `Λ`. A proper algebraic space over `W` whose closed fibre is
presented by a scheme of dimension at most one is represented by an object of the site over `W`
([Stacks, Tag 0AE7]): the pair is an algebraic space over `Spec Λ` by [Stacks, Tag 04SG], and
there [Stacks, Tag 0AE7] is
`AlgebraicGeometry.Space.exists_schemeModel_of_isProper_of_dimension_adicFibre_le_one`, the
dimension of the closed fibre being read on its presentation.

Consequently the complete case of [Stacks, Tag 0E89] holds over `W`: for algebraic spaces `X`,
`Y₁`, `Y₂` proper and flat over `W` and morphisms `cᵢ : X ⟶ Yᵢ` over `W` whose closed fibres
satisfy the hypotheses of the tag, `Y₁ ≅ Y₂` compatibly with the `cᵢ` and with the identification
of closed fibres; this is the scheme case
`AlgebraicGeometry.exists_iso_comp_eq_of_specialFibre_of_isAdicComplete_holds`. Moreover the
scheme-theoretic image of `c₁` is all of `Y₁`, which is what the reduction of a Noetherian local
base to its completion uses.

## Main results

* `AlgebraicGeometry.Space.dimension_adicFibre_zero_eq_of_isPullback`: over `Spec Λ`, the zeroth
  adic fibre has the dimension of any scheme presenting the closed fibre.
* `AlgebraicGeometry.Space.exists_iso_yoneda_of_isProper_of_closedFibre`: [Stacks, Tag 0AE7] over
  `W`.
* `AlgebraicGeometry.Space.exists_iso_of_closedFibre_of_isAdicComplete_of_siteObject`: the
  complete case of [Stacks, Tag 0E89] over `W`.
* `AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_eq_top_of_closedFibre_of_isAdicComplete`:
  the scheme-theoretic image of `c₁` is everything.

## Implementation notes

The closed point of `W` is given as a morphism `k : K ⟶ W` of the site together with an
identification of `K` with `Spec κ` over `Spec Λ`, and the fibres over it by cartesian squares of
algebraic spaces with a representable corner, the form in which the fibres of families of curves
are presented.

## References

* [Stacks Project, Tag 0AE7](https://stacks.math.columbia.edu/tag/0AE7)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 0E89](https://stacks.math.columbia.edu/tag/0E89)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry.Space

section LambdaSite

variable (A : Type u) [CommRing A] [IsLocalRing A] (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (.of A)))

local notation "𝒯" => BigFppfOver.toScheme B (Spec (CommRingCat.of A)) hS

/-- The closed point of `Spec Λ` is the zeroth adic thickening along the maximal ideal. -/
def residueFieldSpecIsoAdicThickeningZero :
    Spec (.of (ResidueField A)) ≅ adicThickening A (maximalIdeal A) 0 :=
  Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso
    (Ideal.quotEquivOfEq (pow_one (maximalIdeal A)))).op

/-- The isomorphism `residueFieldSpecIsoAdicThickeningZero` followed by the closed immersion of
the zeroth adic thickening into `Spec Λ` is the closed point of `Spec Λ`. -/
theorem residueFieldSpecIsoAdicThickeningZero_hom_ι :
    (residueFieldSpecIsoAdicThickeningZero A).hom ≫ adicThickeningι A (maximalIdeal A) 0 =
      ContractionUniquenessComplete.closedPoint A := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1

/-- **The dimension of the closed fibre, read on a presentation of it by a scheme.** If the fibre
of `X` over a point `k : K ⟶ Spec Λ` which is, through `ι`, the closed point is presented by an
object `F` of the site, the zeroth adic fibre of `X` along the maximal ideal has the dimension of
`F`. -/
theorem dimension_adicFibre_zero_eq_of_isPullback
    {X : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B (Spec (.of A)) hS X)
    (fX : X ⟶ yoneda.obj (baseObject A B hS)) {K F : BigFppfOver B (Spec (.of A)) hS}
    (k : K ⟶ baseObject A B hS) (ι : Spec (.of (ResidueField A)) ≅ (𝒯).obj K)
    (hι : ι.hom ≫ (𝒯).map k = ContractionUniquenessComplete.closedPoint A) (t : F ⟶ K)
    (i : yoneda.obj F ⟶ X) (hi : IsPullback i (yoneda.map t) fX (yoneda.map k)) :
    dimension B (Spec (.of A)) hS
        (adicFibre A (maximalIdeal A) B hS (contains_adicThickening A _ B hS) fX 0)
        (isAlgebraicSpace_adicFibre A _ B hS (contains_adicThickening A _ B hS) hX fX 0) =
      topologicalKrullDim ((𝒯).obj F) := by
  set hSn := contains_adicThickening A (maximalIdeal A) B hS
  set e : adicThickening A (maximalIdeal A) 0 ≅ (𝒯).obj K :=
    (residueFieldSpecIsoAdicThickeningZero A).symm ≪≫ ι
  have he : e.hom ≫ (𝒯).map k = adicThickeningι A (maximalIdeal A) 0 := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc, hι, Iso.inv_comp_eq]
    exact (residueFieldSpecIsoAdicThickeningZero_hom_ι A).symm
  set θ : adicThickeningObject A (maximalIdeal A) B hS hSn 0 ≅ K :=
    Over.isoMk (ObjectProperty.isoMk _ e) (by
      have hk : k.left ≫ 𝟙 _ = K.hom := Over.w k
      rw [Category.comp_id] at hk
      rw [← hk]
      exact ObjectProperty.hom_ext _ he)
  have hθ : θ.hom ≫ k = adicThickeningMap A (maximalIdeal A) B hS hSn 0 :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ he)
  have hi' : IsPullback i (yoneda.map t ≫ yoneda.map θ.inv) fX
      (yoneda.map (adicThickeningMap A (maximalIdeal A) B hS hSn 0)) := by
    rw [← hθ, Functor.map_comp]
    exact IsPullback.of_iso hi (Iso.refl _) (Iso.refl _) (yoneda.mapIso θ.symm) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp [← Functor.map_comp])
  rw [← dimension_eq_of_iso B _ hS (isAlgebraicSpace_yoneda B _ hS F) _ hi'.isoPullback,
    dimension_yoneda_eq_topologicalKrullDim]

end LambdaSite

section SiteObject

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

local notation "𝒯S" => BigFppfOver.toScheme B S hS

/-- **[Stacks, Tag 0AE7] over an object of a big fppf site which is the spectrum of a complete
Noetherian local ring.** Let `W` be an object of the big fppf site of `S` whose underlying scheme
is, through `ε`, the spectrum of a complete Noetherian local ring `Λ`, and let `P` be an algebraic
space with a proper morphism `p : P ⟶ W`. If the fibre of `p` over the closed point is presented
by an object `F` of the site of dimension at most one, then `P` is represented by an object of the
site over `W`.

The pair `(P, p)` is an algebraic space over `Spec Λ` by the equivalence of [Stacks, Tag 04SG],
`AlgebraicGeometry.spacesOverSmallerBaseEquivalence`, proper over `Spec Λ`, whose closed fibre is
presented by `F` read over `Spec Λ`: the equivalence carries the cartesian square presenting the
fibre to a cartesian square over `Spec Λ`. So it is a scheme by
`AlgebraicGeometry.Space.exists_schemeModel_of_isProper_of_dimension_adicFibre_le_one`, with
[Stacks, Tag 0A4Z] supplied by `AlgebraicGeometry.Space.existsUnique_adicFibreMap_eq`, and the
lower-shriek extension carries representable presheaves to representable presheaves. -/
theorem exists_iso_yoneda_of_isProper_of_closedFibre (Λ : Type u) [CommRing Λ] [IsLocalRing Λ]
    [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] (W : BigFppfOver B S hS)
    (ε : (𝒯S).obj W ≅ Spec (.of Λ)) {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : IsAlgebraicSpace B S hS P) (p : P ⟶ yoneda.obj W) (hp : IsProper B S hS p)
    {K F : BigFppfOver B S hS} (k : K ⟶ W) (ι : Spec (.of (ResidueField Λ)) ≅ (𝒯S).obj K)
    (hι : ι.hom ≫ (𝒯S).map k ≫ ε.hom = ContractionUniquenessComplete.closedPoint Λ)
    (t : F ⟶ K) (i : yoneda.obj F ⟶ P) (hi : IsPullback i (yoneda.map t) p (yoneda.map k))
    (hdim : topologicalKrullDim ((𝒯S).obj F) ≤ 1) :
    ∃ (Q : BigFppfOver B S hS) (q : Q ⟶ W) (e : yoneda.obj Q ≅ P), e.hom ≫ p = yoneda.map q := by
  -- `W`, replaced by an isomorphic object whose underlying scheme is `Spec Λ`
  have hA : B.Contains (Spec (.of Λ)) := (Scheme.size_congr ε.symm).trans_lt W.left.property
  let εB : B.obj hA ≅ W.left := ObjectProperty.isoMk _ ε.symm
  let g₀ : B.obj hA ⟶ B.obj hS := εB.hom ≫ W.hom
  let W' : BigFppfOver B S hS := Over.mk g₀
  let θ : W' ≅ W := Over.isoMk εB rfl
  -- `P`, as a presheaf over `Spec Λ`
  let E := smallerBasePresheafEquivalence B (Spec (.of Λ)) S hA hS g₀
  let P' : Over (yoneda.obj W') := Over.mk (p ≫ yoneda.map θ.inv)
  let Pt := E.inverse.obj P'
  have hPt : IsAlgebraicSpace B _ hA Pt :=
    isAlgebraicSpace_smallerBasePresheafEquivalence_inverse B _ S hA hS g₀ P' hP
  let OT : Over (yoneda.obj W') := Over.mk (𝟙 _)
  let hOT : IsTerminal (E.inverse.obj OT) := Over.mkIdTerminal.isTerminalObj E.inverse _
  let τ : E.inverse.obj OT ≅ yoneda.obj (baseObject Λ B hA) :=
    hOT.uniqueUpToIso (isTerminal_yoneda_obj_base B _ hA)
  let term : P' ⟶ OT := Over.homMk (p ≫ yoneda.map θ.inv)
  let fX : Pt ⟶ yoneda.obj (baseObject Λ B hA) := E.inverse.map term ≫ τ.hom
  have hfX : IsProper B _ hA fX := by
    refine (isProper_comp_isIso_iff B _ hA _ τ.hom).2 ?_
    refine isProper_smallerBaseInverse_map B _ S hA hS g₀ term hP
      (isAlgebraicSpace_yoneda B S hS W') ?_
    exact (isProper_comp_isIso_iff B S hS p (yoneda.map θ.inv)).2 hp
  -- the cartesian square presenting the closed fibre, read over `W'`
  let OF : Over (yoneda.obj W') := Over.mk (yoneda.map (t ≫ k ≫ θ.inv))
  let OK : Over (yoneda.obj W') := Over.mk (yoneda.map (k ≫ θ.inv))
  let iO : OF ⟶ P' := Over.homMk i (by
    show i ≫ p ≫ yoneda.map θ.inv = yoneda.map (t ≫ k ≫ θ.inv)
    rw [reassoc_of% hi.w, Functor.map_comp, Functor.map_comp])
  let tO : OF ⟶ OK := Over.homMk (yoneda.map t) (by
    show yoneda.map t ≫ yoneda.map (k ≫ θ.inv) = yoneda.map (t ≫ k ≫ θ.inv)
    rw [← Functor.map_comp])
  let kO : OK ⟶ OT := Over.homMk (yoneda.map (k ≫ θ.inv)) (Category.comp_id _)
  have hO : IsPullback iO tO term kO := by
    refine IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext (by
      show i ≫ p ≫ yoneda.map θ.inv = yoneda.map t ≫ yoneda.map (k ≫ θ.inv)
      rw [reassoc_of% hi.w, Functor.map_comp])) ?_
    exact IsPullback.of_iso hi (Iso.refl _) (Iso.refl _) (Iso.refl _) (yoneda.mapIso θ.symm)
      (by simp [iO]) (by simp [tO]) (by simp [term]) (by simp [kO])
  have hE := hO.map E.inverse
  -- the closed fibre over `Spec Λ`
  let F' : BigFppfOver B (Spec (.of Λ)) hA := Over.mk (t ≫ k ≫ θ.inv).left
  let K' : BigFppfOver B (Spec (.of Λ)) hA := Over.mk (k ≫ θ.inv).left
  let φF : F ≅ (Over.map g₀).obj F' := Over.isoMk (Iso.refl _) (by
    rw [Iso.refl_hom, Category.id_comp]
    exact Over.w (t ≫ k ≫ θ.inv))
  let φK : K ≅ (Over.map g₀).obj K' := Over.isoMk (Iso.refl _) (by
    rw [Iso.refl_hom, Category.id_comp]
    exact Over.w (k ≫ θ.inv))
  let isoOF : OF ≅ smallerBaseYonedaOver B _ S hA hS g₀ F' :=
    Over.isoMk (yoneda.mapIso φF) (by
      show yoneda.map φF.hom ≫ yoneda.map _ = yoneda.map _
      rw [← Functor.map_comp]
      congr 1)
  let isoOK : OK ≅ smallerBaseYonedaOver B _ S hA hS g₀ K' :=
    Over.isoMk (yoneda.mapIso φK) (by
      show yoneda.map φK.hom ≫ yoneda.map _ = yoneda.map _
      rw [← Functor.map_comp]
      congr 1)
  let yF : yoneda.obj F' ≅ E.inverse.obj OF :=
    smallerBaseInverseYonedaIso B _ S hA hS g₀ F' ≪≫ E.inverse.mapIso isoOF.symm
  let yK : yoneda.obj K' ≅ E.inverse.obj OK :=
    smallerBaseInverseYonedaIso B _ S hA hS g₀ K' ≪≫ E.inverse.mapIso isoOK.symm
  let k' : K' ⟶ baseObject Λ B hA := Over.homMk K'.hom (Category.comp_id _)
  let t₀ : F' ⟶ K' := Yoneda.fullyFaithful.preimage (yF.hom ≫ E.inverse.map tO ≫ yK.inv)
  have hsq : IsPullback (yF.hom ≫ E.inverse.map iO) (yoneda.map t₀) fX (yoneda.map k') := by
    refine IsPullback.of_iso hE yF.symm (Iso.refl _) yK.symm τ (by simp) ?_ (by simp [fX])
      ((isTerminal_yoneda_obj_base B _ hA).hom_ext _ _)
    simp [t₀]
  have hdim' := dimension_adicFibre_zero_eq_of_isPullback Λ B hA hPt fX k' ι hι t₀ _ hsq
  -- `P` is a scheme over `Spec Λ`
  obtain ⟨Y, hY, fY, -, eY, -⟩ :=
    exists_schemeModel_of_isProper_of_dimension_adicFibre_le_one Λ B hA
      (fun hX hY fX fY hpX hsY hfY g hg hgc =>
        existsUnique_adicFibreMap_eq Λ (maximalIdeal Λ) B hA (contains_adicThickening Λ _ B hA)
          hX hY fX fY hpX hsY hfY g hg hgc) hPt fX hfX (hdim'.trans_le hdim)
  -- back over `S`
  let Q' : BigFppfOver B (Spec (.of Λ)) hA := siteObject B (Spec (.of Λ)) hA hY fY
  let e₀ : yoneda.obj ((Over.map g₀).obj Q') ≅ P :=
    (relocalizedYonedaIso B (B.obj hA) (B.obj hS) g₀ Q').symm ≪≫
      (OverShriek.relocalizePresheafFunctor g₀).mapIso eY.symm ≪≫
        smallerBaseInverseRelocalizeIso B (Spec (.of Λ)) S hA hS g₀ P'
  exact ⟨_, Yoneda.fullyFaithful.preimage (e₀.hom ≫ p), e₀,
    (Functor.FullyFaithful.map_preimage _ _).symm⟩

/-- A proper (flat) morphism of algebraic spaces to `W` which is, through an isomorphism, the
morphism of a morphism `q : Q ⟶ W` of the site makes the underlying morphism of schemes, read
over `Spec Λ` through `ε`, proper (flat). -/
theorem isProper_and_flat_of_iso_yoneda {R : CommRingCat.{u}} {W Q : BigFppfOver B S hS}
    (ε : (𝒯S).obj W ≅ Spec R) {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : yoneda.obj Q ≅ Z)
    {gZ : Z ⟶ yoneda.obj W} {q : Q ⟶ W} (he : e.hom ≫ gZ = yoneda.map q) :
    (IsProper B S hS gZ → _root_.AlgebraicGeometry.IsProper ((𝒯S).map q ≫ ε.hom)) ∧
      (IsFlat B S hS gZ → Flat ((𝒯S).map q ≫ ε.hom)) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : _root_.AlgebraicGeometry.IsProper ((𝒯S).map q) := by
      rw [← isProper_yoneda_map_iff, ← he]
      exact (isProper_isIso_comp_iff B S hS e.hom gZ).2 h
    infer_instance
  · have : Flat ((𝒯S).map q) := by
      refine (holdsOnEveryEtaleChart_yoneda_map_iff B S hS Flat.isEtaleLocalOnSourceAndTarget
        _).1 ?_
      rw [← he]
      exact (holdsOnEveryEtaleChart_iso_comp_iff B S hS _ e.hom gZ).2 h
    infer_instance

/-- **A scheme presentation of the closed fibre of the space of an object of the site.** If `Z`
is, through `e`, the algebraic space of `q : Q ⟶ W`, a presentation by `F` of the fibre of `Z`
over a point `k : K ⟶ W` which is, through `ι` and `ε`, the closed point of `Spec Λ`, makes `F`
the closed fibre of the scheme `Q` over `Spec Λ`. -/
theorem exists_isPullback_closedPoint_of_isPullback_of_iso (Λ : Type u) [CommRing Λ]
    [IsLocalRing Λ] {W Q : BigFppfOver B S hS} (ε : (𝒯S).obj W ≅ Spec (.of Λ))
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : yoneda.obj Q ≅ Z) {gZ : Z ⟶ yoneda.obj W}
    {q : Q ⟶ W} (he : e.hom ≫ gZ = yoneda.map q) {K F : BigFppfOver B S hS} (k : K ⟶ W)
    (ι : Spec (.of (ResidueField Λ)) ≅ (𝒯S).obj K)
    (hι : ι.hom ≫ (𝒯S).map k ≫ ε.hom = ContractionUniquenessComplete.closedPoint Λ)
    (t : F ⟶ K) (i : yoneda.obj F ⟶ Z) (hi : IsPullback i (yoneda.map t) gZ (yoneda.map k)) :
    ∃ j : F ⟶ Q, yoneda.map j = i ≫ e.inv ∧
      IsPullback ((𝒯S).map j) ((𝒯S).map t ≫ ι.inv) ((𝒯S).map q ≫ ε.hom)
        (ContractionUniquenessComplete.closedPoint Λ) := by
  set j := Yoneda.fullyFaithful.preimage (i ≫ e.inv)
  have hj : yoneda.map j = i ≫ e.inv := Functor.FullyFaithful.map_preimage _ _
  refine ⟨j, hj, ?_⟩
  have hg : gZ = e.inv ≫ yoneda.map q := by rw [← he, Iso.inv_hom_id_assoc]
  have h₁ : IsPullback (yoneda.map j) (yoneda.map t) (yoneda.map q) (yoneda.map k) :=
    IsPullback.of_iso hi (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
      (by simp [hj]) (by simp) (by simp [hg]) (by simp)
  have h₂ : IsPullback j t q k :=
    IsPullback.of_map yoneda (yoneda.map_injective (by simpa only [Functor.map_comp] using h₁.w))
      h₁
  have _ : PreservesLimitsOfShape WalkingCospan (𝒯S) :=
    preservesLimitsOfShape_walkingCospan_toScheme B S hS
  refine IsPullback.of_iso (h₂.map (𝒯S)) (Iso.refl _) (Iso.refl _) ι.symm ε (by simp) (by simp)
    (by simp) ?_
  simp only [Iso.symm_hom]
  rw [← hι, Iso.inv_hom_id_assoc]

open Stacks.AlgebraicGeometry.TopDegreeBaseChange ContractionUniquenessComplete in
/-- **The complete Noetherian local case of [Stacks, Tag 0E89] over an object of a big fppf
site.** Let `W` be an object of the big fppf site of `S` whose underlying scheme is, through `ε`,
the spectrum of a complete Noetherian local ring `Λ`; let `X`, `Y₁`, `Y₂` be algebraic spaces
proper and flat over `W` and `cᵢ : X ⟶ Yᵢ` morphisms over `W`. Let `k : K ⟶ W` be, through `ι`
and `ε`, the closed point, and let the fibres of `X`, `Y₁`, `Y₂` over it be presented by objects
`F_X`, `F₁`, `F₂` of dimension at most one, with `aᵢ : F_X ⟶ Fᵢ` the fibres of `cᵢ` and
`φ : F₁ ≅ F₂` an isomorphism over `K` with `a₁ ≫ φ = a₂`. If `a₁` has fibres of dimension at most
one, `𝒪_{F₁} ≅ a₁,* 𝒪_{F_X}` and `R¹a₁,* 𝒪_{F_X} = 0`, there is an isomorphism `ψ : Y₁ ≅ Y₂` over
`W` with `c₁ ≫ ψ = c₂` whose restriction to the closed fibre is `φ`.

The three spaces are represented by objects of the site over `W`
(`AlgebraicGeometry.Space.exists_iso_yoneda_of_isProper_of_closedFibre`, [Stacks, Tag 0AE7]), and
the statement is the scheme case
`AlgebraicGeometry.exists_iso_comp_eq_of_specialFibre_of_isAdicComplete_holds`, read through the
Yoneda embedding. -/
theorem exists_iso_of_closedFibre_of_isAdicComplete_of_siteObject (Λ : Type u) [CommRing Λ]
    [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ]
    (W : BigFppfOver B S hS) (ε : (𝒯S).obj W ≅ Spec (.of Λ))
    {X Y₁ Y₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY₁ : IsAlgebraicSpace B S hS Y₁)
    (hY₂ : IsAlgebraicSpace B S hS Y₂)
    (fX : X ⟶ yoneda.obj W) (g₁ : Y₁ ⟶ yoneda.obj W) (g₂ : Y₂ ⟶ yoneda.obj W)
    (hpX : IsProper B S hS fX) (hp₁ : IsProper B S hS g₁) (hp₂ : IsProper B S hS g₂)
    (hfX : IsFlat B S hS fX) (hf₁ : IsFlat B S hS g₁) (hf₂ : IsFlat B S hS g₂)
    (c₁ : X ⟶ Y₁) (c₂ : X ⟶ Y₂) (hc₁ : c₁ ≫ g₁ = fX) (hc₂ : c₂ ≫ g₂ = fX)
    {K : BigFppfOver B S hS} (k : K ⟶ W) (ι : Spec (.of (ResidueField Λ)) ≅ (𝒯S).obj K)
    (hι : ι.hom ≫ (𝒯S).map k ≫ ε.hom = ContractionUniquenessComplete.closedPoint Λ)
    {FX F₁ F₂ : BigFppfOver B S hS} (tX : FX ⟶ K) (t₁ : F₁ ⟶ K) (t₂ : F₂ ⟶ K)
    (iX : yoneda.obj FX ⟶ X) (i₁ : yoneda.obj F₁ ⟶ Y₁) (i₂ : yoneda.obj F₂ ⟶ Y₂)
    (hiX : IsPullback iX (yoneda.map tX) fX (yoneda.map k))
    (hi₁ : IsPullback i₁ (yoneda.map t₁) g₁ (yoneda.map k))
    (hi₂ : IsPullback i₂ (yoneda.map t₂) g₂ (yoneda.map k))
    (hdX : topologicalKrullDim ((𝒯S).obj FX) ≤ 1) (hd₁ : topologicalKrullDim ((𝒯S).obj F₁) ≤ 1)
    (hd₂ : topologicalKrullDim ((𝒯S).obj F₂) ≤ 1)
    (a₁ : FX ⟶ F₁) (a₂ : FX ⟶ F₂) (ha₁ : a₁ ≫ t₁ = tX) (ha₂ : a₂ ≫ t₂ = tX)
    (hia₁ : iX ≫ c₁ = yoneda.map a₁ ≫ i₁) (hia₂ : iX ≫ c₂ = yoneda.map a₂ ≫ i₂)
    (φ : F₁ ≅ F₂) (hφ : φ.hom ≫ t₂ = t₁) (hφa : a₁ ≫ φ.hom = a₂)
    (hdimF : ∀ y, topologicalKrullDim (((𝒯S).map a₁).fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit ((𝒯S).map a₁)))
    (hR : IsZero (firstDirectImageStructureSheaf ((𝒯S).map a₁))) :
    ∃ ψ : Y₁ ≅ Y₂, ψ.hom ≫ g₂ = g₁ ∧ c₁ ≫ ψ.hom = c₂ ∧ i₁ ≫ ψ.hom = yoneda.map φ.hom ≫ i₂ := by
  -- the three spaces are represented (Stacks 0AE7)
  obtain ⟨QX, qX, eX, heX⟩ :=
    exists_iso_yoneda_of_isProper_of_closedFibre B S hS Λ W ε hX fX hpX k ι hι tX iX hiX hdX
  obtain ⟨Q₁, q₁, e₁, he₁⟩ :=
    exists_iso_yoneda_of_isProper_of_closedFibre B S hS Λ W ε hY₁ g₁ hp₁ k ι hι t₁ i₁ hi₁ hd₁
  obtain ⟨Q₂, q₂, e₂, he₂⟩ :=
    exists_iso_yoneda_of_isProper_of_closedFibre B S hS Λ W ε hY₂ g₂ hp₂ k ι hι t₂ i₂ hi₂ hd₂
  set fX' := (𝒯S).map qX ≫ ε.hom
  set fY₁' := (𝒯S).map q₁ ≫ ε.hom
  set fY₂' := (𝒯S).map q₂ ≫ ε.hom
  have : _root_.AlgebraicGeometry.IsProper fX' :=
    (isProper_and_flat_of_iso_yoneda B S hS ε eX heX).1 hpX
  have : _root_.AlgebraicGeometry.IsProper fY₁' :=
    (isProper_and_flat_of_iso_yoneda B S hS ε e₁ he₁).1 hp₁
  have : _root_.AlgebraicGeometry.IsProper fY₂' :=
    (isProper_and_flat_of_iso_yoneda B S hS ε e₂ he₂).1 hp₂
  have : Flat fX' := (isProper_and_flat_of_iso_yoneda B S hS ε eX heX).2 hfX
  have : Flat fY₁' := (isProper_and_flat_of_iso_yoneda B S hS ε e₁ he₁).2 hf₁
  have : Flat fY₂' := (isProper_and_flat_of_iso_yoneda B S hS ε e₂ he₂).2 hf₂
  -- the morphisms of schemes
  have hmor : ∀ {Q : BigFppfOver B S hS} {q : Q ⟶ W} {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      {gZ : Z ⟶ yoneda.obj W} (e : yoneda.obj Q ≅ Z) (_ : e.hom ≫ gZ = yoneda.map q) (c : X ⟶ Z)
      (_ : c ≫ gZ = fX), ∃ γ : QX ⟶ Q, yoneda.map γ = eX.hom ≫ c ≫ e.inv ∧
        (𝒯S).map γ ≫ (𝒯S).map q ≫ ε.hom = fX' := by
    intro Q q Z gZ e he c hc
    refine ⟨Yoneda.fullyFaithful.preimage (eX.hom ≫ c ≫ e.inv),
      Functor.FullyFaithful.map_preimage _ _, ?_⟩
    have : Yoneda.fullyFaithful.preimage (eX.hom ≫ c ≫ e.inv) ≫ q = qX := by
      apply yoneda.map_injective
      rw [Functor.map_comp, Functor.FullyFaithful.map_preimage, ← he, Category.assoc,
        Category.assoc, Iso.inv_hom_id_assoc, hc, heX]
    rw [← Category.assoc, ← Functor.map_comp, this]
  obtain ⟨γ₁, hγ₁, hγ₁b⟩ := hmor e₁ he₁ c₁ hc₁
  obtain ⟨γ₂, hγ₂, hγ₂b⟩ := hmor e₂ he₂ c₂ hc₂
  -- the closed fibres
  obtain ⟨jX, hjX, sqX⟩ :=
    exists_isPullback_closedPoint_of_isPullback_of_iso B S hS Λ ε eX heX k ι hι tX iX hiX
  obtain ⟨j₁, hj₁, sq₁⟩ :=
    exists_isPullback_closedPoint_of_isPullback_of_iso B S hS Λ ε e₁ he₁ k ι hι t₁ i₁ hi₁
  obtain ⟨j₂, hj₂, sq₂⟩ :=
    exists_isPullback_closedPoint_of_isPullback_of_iso B S hS Λ ε e₂ he₂ k ι hι t₂ i₂ hi₂
  have hja : ∀ {F Q : BigFppfOver B S hS} {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (e : yoneda.obj Q ≅ Z) (c : X ⟶ Z) (γ : QX ⟶ Q) (_ : yoneda.map γ = eX.hom ≫ c ≫ e.inv)
      (a : FX ⟶ F) (i : yoneda.obj F ⟶ Z) (j : F ⟶ Q) (_ : yoneda.map j = i ≫ e.inv)
      (_ : iX ≫ c = yoneda.map a ≫ i), jX ≫ γ = a ≫ j := by
    intro F Q Z e c γ hγ a i j hj hia
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_comp, hjX, hj, hγ, Category.assoc, Iso.inv_hom_id_assoc,
      reassoc_of% hia]
  have hθ : ∀ {F Q : BigFppfOver B S hS} {q : Q ⟶ W} (γ : QX ⟶ Q)
      (hγb : (𝒯S).map γ ≫ (𝒯S).map q ≫ ε.hom = fX') (a : FX ⟶ F) (t : F ⟶ K)
      (ha : a ≫ t = tX) (j : F ⟶ Q)
      (sq : IsPullback ((𝒯S).map j) ((𝒯S).map t ≫ ι.inv) ((𝒯S).map q ≫ ε.hom)
        (ContractionUniquenessComplete.closedPoint Λ))
      (_ : jX ≫ γ = a ≫ j),
      sqX.isoPullback.hom ≫ specialMap fX' ((𝒯S).map q ≫ ε.hom) ((𝒯S).map γ) hγb =
        (𝒯S).map a ≫ sq.isoPullback.hom := by
    intro F Q q γ hγb a t ha j sq hjγ
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, IsPullback.isoPullback_hom_fst,
        Category.assoc, IsPullback.isoPullback_hom_fst, ← Functor.map_comp, ← Functor.map_comp,
        hjγ]
    · rw [Category.assoc, specialMap_snd, IsPullback.isoPullback_hom_snd, Category.assoc,
        IsPullback.isoPullback_hom_snd, ← Category.assoc, ← Functor.map_comp, ha]
  have hθ₁ := hθ γ₁ hγ₁b a₁ t₁ ha₁ j₁ sq₁ (hja e₁ c₁ γ₁ hγ₁ a₁ i₁ j₁ hj₁ hia₁)
  have hθ₂ := hθ γ₂ hγ₂b a₂ t₂ ha₂ j₂ sq₂ (hja e₂ c₂ γ₂ hγ₂ a₂ i₂ j₂ hj₂ hia₂)
  -- the special-fibre hypotheses, transported to the scheme morphism
  set sm₁ := specialMap fX' fY₁' ((𝒯S).map γ₁) hγ₁b
  have : _root_.AlgebraicGeometry.IsProper ((𝒯S).map γ₁) := by
    have : _root_.AlgebraicGeometry.IsProper ((𝒯S).map γ₁ ≫ fY₁') := by
      rw [hγ₁b]; infer_instance
    exact _root_.AlgebraicGeometry.IsProper.of_comp _ fY₁'
  have : _root_.AlgebraicGeometry.IsProper sm₁ := by
    have : _root_.AlgebraicGeometry.IsProper
        (sm₁ ≫ pullback.snd fY₁' (ContractionUniquenessComplete.closedPoint Λ)) := by
      rw [specialMap_snd]; infer_instance
    exact _root_.AlgebraicGeometry.IsProper.of_comp _
      (pullback.snd fY₁' (ContractionUniquenessComplete.closedPoint Λ))
  have ha₁e : (𝒯S).map a₁ = sqX.isoPullback.hom ≫ sm₁ ≫ sq₁.isoPullback.inv := by
    rw [← Category.assoc, hθ₁, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have : _root_.AlgebraicGeometry.IsProper ((𝒯S).map a₁) := by rw [ha₁e]; infer_instance
  have H : IsPullback sqX.isoPullback.inv sm₁ ((𝒯S).map a₁) sq₁.isoPullback.inv :=
    IsPullback.of_horiz_isIso ⟨by rw [ha₁e, Iso.inv_hom_id_assoc]⟩
  obtain ⟨hR', h0'⟩ := isZero_and_isIso_of_isPullback H hdimF hR h0
  have hR'' : IsZero (((Scheme.Modules.pushforward sm₁).rightDerived 1).obj
      (SheafOfModules.unit
        (pullback fX' (ContractionUniquenessComplete.closedPoint Λ)).ringCatSheaf)) := by
    let := HasDerivedCategory.standard
      (pullback fX' (ContractionUniquenessComplete.closedPoint Λ)).Modules
    let := HasDerivedCategory.standard
      (pullback fY₁' (ContractionUniquenessComplete.closedPoint Λ)).Modules
    exact (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff (Scheme.Modules.pushforward sm₁)
      (m := (1 : ℤ)) (n := 1) rfl _).1 hR'
  -- the identification of the closed fibres of `Y₁` and `Y₂`
  set φ' : pullback fY₁' (ContractionUniquenessComplete.closedPoint Λ) ≅
      pullback fY₂' (ContractionUniquenessComplete.closedPoint Λ) :=
    sq₁.isoPullback.symm ≪≫ (𝒯S).mapIso φ ≪≫ sq₂.isoPullback
  have hφ' : φ'.hom ≫ pullback.snd fY₂' (ContractionUniquenessComplete.closedPoint Λ) =
      pullback.snd fY₁' (ContractionUniquenessComplete.closedPoint Λ) := by
    show (sq₁.isoPullback.inv ≫ (𝒯S).map φ.hom ≫ sq₂.isoPullback.hom) ≫ _ = _
    rw [Category.assoc, Category.assoc, IsPullback.isoPullback_hom_snd,
      ← Category.assoc ((𝒯S).map φ.hom), ← Functor.map_comp, hφ, Iso.inv_comp_eq,
      IsPullback.isoPullback_hom_snd]
  have hφc' : sm₁ ≫ φ'.hom = specialMap fX' fY₂' ((𝒯S).map γ₂) hγ₂b := by
    show sm₁ ≫ sq₁.isoPullback.inv ≫ (𝒯S).map φ.hom ≫ sq₂.isoPullback.hom = _
    rw [← cancel_epi sqX.isoPullback.hom, hθ₂, ← Category.assoc, hθ₁, Category.assoc,
      Iso.hom_inv_id_assoc, ← Category.assoc ((𝒯S).map a₁), ← Functor.map_comp, hφa]
  -- the scheme case
  obtain ⟨ψ', hψ'b, hψ'c, hψ'f⟩ := exists_iso_comp_eq_of_specialFibre_of_isAdicComplete_holds
    (Λ := Λ) inferInstance fX' fY₁' fY₂' ((𝒯S).map γ₁) hγ₁b ((𝒯S).map γ₂) hγ₂b φ' hφ' hφc' h0'
    hR''
  -- back to algebraic spaces
  have hψq : ψ'.hom ≫ (𝒯S).map q₂ = (𝒯S).map q₁ := by
    rw [← cancel_mono ε.hom, Category.assoc]
    exact hψ'b
  set Ψ : Q₁ ≅ Q₂ := Over.isoMk (ObjectProperty.isoMk _ ψ') (by
    rw [← Over.w q₁, ← Over.w q₂, ← Category.assoc]
    congr 1
    exact ObjectProperty.hom_ext _ hψq)
  have hΨ : ∀ {F : BigFppfOver B S hS} (u : F ⟶ Q₁) (v : F ⟶ Q₂),
      (𝒯S).map u ≫ ψ'.hom = (𝒯S).map v → u ≫ Ψ.hom = v := by
    intro F u v h
    exact Over.OverMorphism.ext (ObjectProperty.hom_ext _ h)
  have hΨq : Ψ.hom ≫ q₂ = q₁ := Over.OverMorphism.ext (ObjectProperty.hom_ext _ hψq)
  refine ⟨e₁.symm ≪≫ yoneda.mapIso Ψ ≪≫ e₂, ?_, ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
    rw [he₂, ← Functor.map_comp, hΨq, ← he₁, Iso.inv_hom_id_assoc]
  · have h := hΨ γ₁ γ₂ hψ'c
    have hc : c₁ ≫ e₁.inv = eX.inv ≫ yoneda.map γ₁ := by rw [hγ₁, Iso.inv_hom_id_assoc]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [reassoc_of% hc, ← Functor.map_comp_assoc, h, hγ₂, Category.assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
  · have h : j₁ ≫ Ψ.hom = φ.hom ≫ j₂ := by
      refine hΨ _ _ ?_
      rw [Functor.map_comp, ← IsPullback.isoPullback_hom_fst sq₁, Category.assoc, hψ'f,
        ← IsPullback.isoPullback_hom_fst sq₂]
      show sq₁.isoPullback.hom ≫ (sq₁.isoPullback.inv ≫ (𝒯S).map φ.hom ≫
        sq₂.isoPullback.hom) ≫ _ = _
      rw [Category.assoc, Iso.hom_inv_id_assoc, Category.assoc]
    have hi₁' : i₁ ≫ e₁.inv = yoneda.map j₁ := hj₁.symm
    have hi₂' : i₂ = yoneda.map j₂ ≫ e₂.hom := by rw [hj₂, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [reassoc_of% hi₁', ← Functor.map_comp_assoc, h, Functor.map_comp, Category.assoc, hi₂']

open Stacks.AlgebraicGeometry.TopDegreeBaseChange ContractionUniquenessComplete in
/-- **The contraction is scheme-theoretically dominant in the complete case.** Under the
hypotheses of `AlgebraicGeometry.Space.exists_iso_of_closedFibre_of_isAdicComplete_of_siteObject`
on `X`, `Y₁` and `c₁`, the scheme-theoretic image of `c₁` is all of `Y₁`: both spaces are
represented by schemes over `Spec Λ` ([Stacks, Tag 0AE7]), and the morphism of schemes is
scheme-theoretically dominant by
`AlgebraicGeometry.isSchemeTheoreticallyDominant_of_closedFibre`. -/
theorem schemeTheoreticImageSubfunctor_eq_top_of_closedFibre_of_isAdicComplete (Λ : Type u)
    [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ]
    (W : BigFppfOver B S hS) (ε : (𝒯S).obj W ≅ Spec (.of Λ))
    {X Y₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY₁ : IsAlgebraicSpace B S hS Y₁)
    (fX : X ⟶ yoneda.obj W) (g₁ : Y₁ ⟶ yoneda.obj W)
    (hpX : IsProper B S hS fX) (hp₁ : IsProper B S hS g₁) (hfX : IsFlat B S hS fX)
    (c₁ : X ⟶ Y₁) (hc₁ : c₁ ≫ g₁ = fX)
    {K : BigFppfOver B S hS} (k : K ⟶ W) (ι : Spec (.of (ResidueField Λ)) ≅ (𝒯S).obj K)
    (hι : ι.hom ≫ (𝒯S).map k ≫ ε.hom = ContractionUniquenessComplete.closedPoint Λ)
    {FX F₁ : BigFppfOver B S hS} (tX : FX ⟶ K) (t₁ : F₁ ⟶ K)
    (iX : yoneda.obj FX ⟶ X) (i₁ : yoneda.obj F₁ ⟶ Y₁)
    (hiX : IsPullback iX (yoneda.map tX) fX (yoneda.map k))
    (hi₁ : IsPullback i₁ (yoneda.map t₁) g₁ (yoneda.map k))
    (hdX : topologicalKrullDim ((𝒯S).obj FX) ≤ 1) (hd₁ : topologicalKrullDim ((𝒯S).obj F₁) ≤ 1)
    (a₁ : FX ⟶ F₁) (ha₁ : a₁ ≫ t₁ = tX) (hia₁ : iX ≫ c₁ = yoneda.map a₁ ≫ i₁)
    (hdimF : ∀ y, topologicalKrullDim (((𝒯S).map a₁).fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit ((𝒯S).map a₁)))
    (hR : IsZero (firstDirectImageStructureSheaf ((𝒯S).map a₁))) :
    schemeTheoreticImageSubfunctor B S hS c₁ = ⊤ := by
  obtain ⟨QX, qX, eX, heX⟩ :=
    exists_iso_yoneda_of_isProper_of_closedFibre B S hS Λ W ε hX fX hpX k ι hι tX iX hiX hdX
  obtain ⟨Q₁, q₁, e₁, he₁⟩ :=
    exists_iso_yoneda_of_isProper_of_closedFibre B S hS Λ W ε hY₁ g₁ hp₁ k ι hι t₁ i₁ hi₁ hd₁
  set fX' := (𝒯S).map qX ≫ ε.hom
  set fY₁' := (𝒯S).map q₁ ≫ ε.hom
  have : _root_.AlgebraicGeometry.IsProper fX' :=
    (isProper_and_flat_of_iso_yoneda B S hS ε eX heX).1 hpX
  have : _root_.AlgebraicGeometry.IsProper fY₁' :=
    (isProper_and_flat_of_iso_yoneda B S hS ε e₁ he₁).1 hp₁
  have : Flat fX' := (isProper_and_flat_of_iso_yoneda B S hS ε eX heX).2 hfX
  -- the morphism of schemes
  set γ₁ := Yoneda.fullyFaithful.preimage (eX.hom ≫ c₁ ≫ e₁.inv)
  have hγ₁ : yoneda.map γ₁ = eX.hom ≫ c₁ ≫ e₁.inv := Functor.FullyFaithful.map_preimage _ _
  have hγ₁q : γ₁ ≫ q₁ = qX := by
    apply yoneda.map_injective
    rw [Functor.map_comp, hγ₁, ← he₁, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, hc₁,
      heX]
  have hγ₁b : (𝒯S).map γ₁ ≫ fY₁' = fX' := by
    rw [← Category.assoc, ← Functor.map_comp, hγ₁q]
  -- the closed fibres
  obtain ⟨jX, hjX, sqX⟩ :=
    exists_isPullback_closedPoint_of_isPullback_of_iso B S hS Λ ε eX heX k ι hι tX iX hiX
  obtain ⟨j₁, hj₁, sq₁⟩ :=
    exists_isPullback_closedPoint_of_isPullback_of_iso B S hS Λ ε e₁ he₁ k ι hι t₁ i₁ hi₁
  have hjγ : jX ≫ γ₁ = a₁ ≫ j₁ := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_comp, hjX, hj₁, hγ₁, Category.assoc, Iso.inv_hom_id_assoc,
      reassoc_of% hia₁]
  set sm₁ := specialMap fX' fY₁' ((𝒯S).map γ₁) hγ₁b
  have hθ₁ : sqX.isoPullback.hom ≫ sm₁ = (𝒯S).map a₁ ≫ sq₁.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, IsPullback.isoPullback_hom_fst,
        Category.assoc, IsPullback.isoPullback_hom_fst, ← Functor.map_comp, ← Functor.map_comp,
        hjγ]
    · rw [Category.assoc, specialMap_snd, IsPullback.isoPullback_hom_snd, Category.assoc,
        IsPullback.isoPullback_hom_snd, ← Category.assoc, ← Functor.map_comp, ha₁]
  have : _root_.AlgebraicGeometry.IsProper ((𝒯S).map γ₁) := by
    have : _root_.AlgebraicGeometry.IsProper ((𝒯S).map γ₁ ≫ fY₁') := by
      rw [hγ₁b]; infer_instance
    exact _root_.AlgebraicGeometry.IsProper.of_comp _ fY₁'
  have : _root_.AlgebraicGeometry.IsProper sm₁ := by
    have : _root_.AlgebraicGeometry.IsProper
        (sm₁ ≫ pullback.snd fY₁' (ContractionUniquenessComplete.closedPoint Λ)) := by
      rw [specialMap_snd]; infer_instance
    exact _root_.AlgebraicGeometry.IsProper.of_comp _
      (pullback.snd fY₁' (ContractionUniquenessComplete.closedPoint Λ))
  have ha₁e : (𝒯S).map a₁ = sqX.isoPullback.hom ≫ sm₁ ≫ sq₁.isoPullback.inv := by
    rw [← Category.assoc, hθ₁, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have : _root_.AlgebraicGeometry.IsProper ((𝒯S).map a₁) := by rw [ha₁e]; infer_instance
  have H : IsPullback sqX.isoPullback.inv sm₁ ((𝒯S).map a₁) sq₁.isoPullback.inv :=
    IsPullback.of_horiz_isIso ⟨by rw [ha₁e, Iso.inv_hom_id_assoc]⟩
  obtain ⟨hR', h0'⟩ := isZero_and_isIso_of_isPullback H hdimF hR h0
  have H' : IsPullback sqX.isoPullback.hom ((𝒯S).map a₁) sm₁ sq₁.isoPullback.hom :=
    IsPullback.of_horiz_isIso ⟨hθ₁⟩
  have hdim : ∀ y, topologicalKrullDim (sm₁.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
    intro y
    have h := topologicalKrullDim_fiber_le_of_isPullback' H' 1 (sq₁.isoPullback.inv y) (hdimF _)
    have e : sq₁.isoPullback.hom (sq₁.isoPullback.inv y) = y := by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl
    rwa [e] at h
  have hdom := isSchemeTheoreticallyDominant_of_closedFibre fX' fY₁' ((𝒯S).map γ₁) hγ₁b hdim h0'
    hR'
  -- back to algebraic spaces
  have h₁ : schemeTheoreticImageSubfunctor B S hS (yoneda.map γ₁) = ⊤ :=
    (schemeTheoreticImageSubfunctor_yoneda_eq_top_iff B S hS γ₁).2 hdom
  have h₂ : schemeTheoreticImageSubfunctor B S hS (eX.inv ≫ yoneda.map γ₁) = ⊤ := by
    have : Epi eX.inv := IsIso.epi_of_iso _
    rw [schemeTheoreticImageSubfunctor_congr_range B S hS _ (yoneda.map γ₁)
      (isAlgebraicSpace_yoneda B S hS Q₁) (by
        rw [Subfunctor.range_comp, Subfunctor.range_eq_top eX.inv, Subfunctor.image_top])]
    exact h₁
  have hc : c₁ = (eX.inv ≫ yoneda.map γ₁) ≫ e₁.hom := by
    rw [hγ₁]
    simp
  rw [hc]
  exact schemeTheoreticImageSubfunctor_comp_eq_top_of_isIso (isAlgebraicSpace_yoneda B S hS Q₁) hY₁
    _ e₁.hom h₂

end SiteObject

end AlgebraicGeometry.Space

end
