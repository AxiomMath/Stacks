module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.PointSectionCartier
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveTwists

/-!
# Exceptional curves of the first kind along open immersions

Let `j : Y ⟶ X` be an open immersion and `D` an ideal sheaf on `X` whose support lies in the
image of `j`. Then the closed subscheme cut out by the inverse image `D.comap j` is identified
with the one cut out by `D` (`AlgebraicGeometry.Scheme.IdealSheafData.comapSubschemeIso`), and
`D` is an exceptional curve of the first kind exactly when `D.comap j` is, the presentation
`𝐏¹_k ≅ E` being transported along that identification.

The comparison of the two conditions goes through the Picard group. The normal-sheaf clause of
an exceptional curve of the first kind says that `𝒪_X(E)`, restricted to `E` and pulled back to
`𝐏¹_k`, has the class of `𝒪(-1)`
(`AlgebraicGeometry.Scheme.IdealSheafData.isExceptionalCurveOfFirstKind_iff_pullbackPicardClass`),
and the class of `𝒪_X(E)` pulls back along an open immersion to the class of `𝒪_Y(j^{-1}E)`
([Stacks, Tag 0C4U]).

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.comapSubschemeHom`: the open immersion
  `(D.comap j).subscheme ⟶ D.subscheme` over `j`.
* `AlgebraicGeometry.Scheme.IdealSheafData.comapSubschemeIso`: the same, an isomorphism when the
  support of `D` lies in the image of `j`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.isExceptionalCurveOfFirstKind_iff_pullbackPicardClass`:
  the normal-sheaf clause read in the Picard group.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.comap`: an exceptional
  curve of the first kind restricts to one on an open subscheme containing it.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.of_comap`: conversely,
  an ideal sheaf supported in an open subscheme on which it restricts to an exceptional curve of
  the first kind is one.

## References

* [Stacks Project, Tag 0C4U](https://stacks.math.columbia.edu/tag/0C4U)
* [Stacks Project, Tag 0B3P](https://stacks.math.columbia.edu/tag/0B3P)
-/

@[expose] public noncomputable section

open CategoryTheory Limits RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] (D : X.IdealSheafData)

/-- The morphism from the subscheme cut out by the inverse image of `D` along an open immersion
`j` to the subscheme cut out by `D`, lying over `j`. -/
def comapSubschemeHom : (D.comap j).subscheme ⟶ D.subscheme :=
  (D.comapIso j).hom ≫ pullback.snd j D.subschemeι

omit [IsOpenImmersion j] in
/-- The morphism `D.comapSubschemeHom j` followed by the closed immersion of `D.subscheme` equals
the closed immersion of `(D.comap j).subscheme` followed by `j`. -/
@[reassoc (attr := simp)]
theorem comapSubschemeHom_subschemeι :
    D.comapSubschemeHom j ≫ D.subschemeι = (D.comap j).subschemeι ≫ j := by
  simp [comapSubschemeHom]

/-- The morphism `D.comapSubschemeHom j` is an open immersion. -/
instance : IsOpenImmersion (D.comapSubschemeHom j) := by
  unfold comapSubschemeHom
  infer_instance

/-- When the support of `D` lies in the image of the open immersion `j`, the subschemes cut out
by `D` and by its inverse image along `j` are identified. -/
theorem isIso_comapSubschemeHom (h : (D.support : Set X) ⊆ Set.range j.base) :
    IsIso (D.comapSubschemeHom j) := by
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨inferInstance, ⟨fun z => ?_⟩⟩
  have hz : D.subschemeι.base z ∈ Set.range j.base :=
    h (by rw [← D.range_subschemeι]; exact ⟨z, rfl⟩)
  have hz' : z ∈ Set.range (pullback.snd j D.subschemeι).base := by
    rw [Scheme.Pullback.range_snd]
    exact hz
  obtain ⟨w, rfl⟩ := hz'
  refine ⟨(D.comapIso j).inv.base w, ?_⟩
  have hw : (D.comapIso j).hom.base ((D.comapIso j).inv.base w) = w := by
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl
  change (pullback.snd j D.subschemeι).base ((D.comapIso j).hom.base
    ((D.comapIso j).inv.base w)) = _
  rw [hw]

/-- The identification of the subschemes cut out by `D` and by its inverse image along an open
immersion containing the support of `D`. -/
def comapSubschemeIso (h : (D.support : Set X) ⊆ Set.range j.base) :
    (D.comap j).subscheme ≅ D.subscheme :=
  haveI := D.isIso_comapSubschemeHom j h
  asIso (D.comapSubschemeHom j)

/-- The forward morphism of `D.comapSubschemeIso j h` is `D.comapSubschemeHom j`. -/
@[simp]
theorem comapSubschemeIso_hom (h : (D.support : Set X) ⊆ Set.range j.base) :
    (D.comapSubschemeIso j h).hom = D.comapSubschemeHom j := rfl

/-- The class of `𝒪_X(D)` pulls back along a flat morphism to the class of `𝒪_Y(f^{-1}D)`; this
is [Stacks, Tag 0C4U] read in the Picard group. -/
theorem schemePullbackClass_picardClass {X Y : Scheme.{u}} (f : Y ⟶ X) [Flat f]
    (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    haveI : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap f) :=
      Stacks.Divisors.isPullbackDefined_of_flat f D inferInstance
    Stacks.Picard.schemePullbackClass f (Stacks.Divisors.picardClass D) =
      Stacks.Divisors.picardClass (D.comap f) := by
  have : Stacks.Divisors.IsPullbackDefined f D :=
    Stacks.Divisors.isPullbackDefined_of_flat f D inferInstance
  refine (Stacks.Picard.pullbackClass_classOf f.toLRSHom.toShHom
    (Stacks.Divisors.invertibleSheaf' D)
    (Stacks.Divisors.isInvertible_invertibleSheaf_picard D)).trans ?_
  exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _
    (Stacks.Divisors.isInvertible_invertibleSheaf_picard (D.comap f))).2
      ⟨Stacks.Divisors.invertibleSheafPullbackIso f D⟩

variable {k : Type u} [Field k]

/-- **The normal-sheaf clause of an exceptional curve of the first kind, in the Picard group.**
For an effective Cartier divisor `D` and an isomorphism `e : 𝐏¹_k ≅ E` with the subscheme it
cuts out, `D` is an exceptional curve of the first kind exactly when `𝒪_X(E)`, restricted to `E`
and pulled back along `e`, has the class of `𝒪(-1)`. -/
theorem isExceptionalCurveOfFirstKind_iff_pullbackPicardClass
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (e : projectiveLineProj k ≅ D.subscheme) :
    D.IsExceptionalCurveOfFirstKind k e ↔
      Stacks.Picard.pullbackClass e.hom.toLRSHom.toShHom
          (Stacks.Picard.pullbackClass D.subschemeι.toLRSHom.toShHom
            (Stacks.Divisors.picardClass D)) =
        twistingSheafPicardClass k (-1) := by
  refine ⟨fun hE => hE.pullbackPicardClass_invertibleSheaf, fun h => ⟨inferInstance, ?_⟩⟩
  have h' := (Stacks.Picard.pullbackClass_classOf e.hom.toLRSHom.toShHom _ _).symm.trans
    ((congrArg (Stacks.Picard.pullbackClass e.hom.toLRSHom.toShHom)
      (Stacks.Picard.pullbackClass_classOf D.subschemeι.toLRSHom.toShHom
        (Stacks.Divisors.invertibleSheaf' D)
        (Stacks.Divisors.isInvertible_invertibleSheaf_picard D)).symm).trans h)
  obtain ⟨i⟩ := (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _
    (isInvertible_twistingSheaf_projectiveLineProj k (-1))).1 h'
  exact ⟨(modulePullback e.hom.toLRSHom.toShHom).mapIso
    (Stacks.Divisors.normalSheafIsoInvertibleSheaf D) ≪≫ i⟩

/-- The Picard-group form of the normal-sheaf clause, transported along an open immersion whose
image contains the support: pulling back to `𝐏¹_k` through the subscheme of `D` or through that of
`D.comap j` gives the same class. -/
private theorem pullbackClass_comap_eq [Stacks.Divisors.IsEffectiveCartierDivisor D]
    [Stacks.Divisors.IsEffectiveCartierDivisor (D.comap j)]
    (h : (D.support : Set X) ⊆ Set.range j.base) (e : projectiveLineProj k ≅ D.subscheme) :
    Stacks.Picard.pullbackClass (e ≪≫ (D.comapSubschemeIso j h).symm).hom.toLRSHom.toShHom
        (Stacks.Picard.pullbackClass (D.comap j).subschemeι.toLRSHom.toShHom
          (Stacks.Divisors.picardClass (D.comap j))) =
      Stacks.Picard.pullbackClass e.hom.toLRSHom.toShHom
        (Stacks.Picard.pullbackClass D.subschemeι.toLRSHom.toShHom
          (Stacks.Divisors.picardClass D)) := by
  have hcomp : (e ≪≫ (D.comapSubschemeIso j h).symm).hom ≫ (D.comap j).subschemeι ≫ j =
      e.hom ≫ D.subschemeι := by
    rw [← comapSubschemeHom_subschemeι, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      ← Category.assoc (D.comapSubschemeIso j h).inv, ← comapSubschemeIso_hom j D h,
      Iso.inv_hom_id, Category.id_comp]
  rw [← schemePullbackClass_picardClass j D]
  change Stacks.Picard.schemePullbackClass _ (Stacks.Picard.schemePullbackClass _
      (Stacks.Picard.schemePullbackClass j _)) =
    Stacks.Picard.schemePullbackClass _ (Stacks.Picard.schemePullbackClass _ _)
  rw [Stacks.Picard.schemePullbackClass_comp, Stacks.Picard.schemePullbackClass_comp,
    Stacks.Picard.schemePullbackClass_comp, Category.assoc, hcomp]

/-- **An exceptional curve of the first kind restricts to an open subscheme containing it.** If
the support of `D` lies in the image of the open immersion `j`, and `D` is an exceptional curve
of the first kind presented by `e : 𝐏¹_k ≅ E`, then so is `D.comap j`, presented by `e` followed
by the identification of the two subschemes. -/
theorem IsExceptionalCurveOfFirstKind.comap {e : projectiveLineProj k ≅ D.subscheme}
    (hE : D.IsExceptionalCurveOfFirstKind k e) (h : (D.support : Set X) ⊆ Set.range j.base) :
    (D.comap j).IsExceptionalCurveOfFirstKind k (e ≪≫ (D.comapSubschemeIso j h).symm) := by
  have : Stacks.Divisors.IsEffectiveCartierDivisor D := hE.1
  have : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap j) :=
    Stacks.Divisors.isPullbackDefined_of_flat j D inferInstance
  rw [isExceptionalCurveOfFirstKind_iff_pullbackPicardClass, pullbackClass_comap_eq j D h e]
  exact hE.pullbackPicardClass_invertibleSheaf

/-- **An exceptional curve of the first kind on an open subscheme is one on the whole scheme**,
when the ideal sheaf is supported in that open subscheme. If the support of `D` lies in the image
of the open immersion `j` and `D.comap j` is an exceptional curve of the first kind presented by
`e' : 𝐏¹_k ≅ E`, then so is `D`, presented by `e'` followed by the identification of the two
subschemes. -/
theorem IsExceptionalCurveOfFirstKind.of_comap (h : (D.support : Set X) ⊆ Set.range j.base)
    {e' : projectiveLineProj k ≅ (D.comap j).subscheme}
    (hE : (D.comap j).IsExceptionalCurveOfFirstKind k e') :
    D.IsExceptionalCurveOfFirstKind k (e' ≪≫ D.comapSubschemeIso j h) := by
  have : Stacks.Divisors.IsEffectiveCartierDivisor D :=
    Stacks.Chow.isEffectiveCartierDivisor_of_comap_of_isOpenImmersion D j
      (fun x hx => h (mem_supportSet_iff_mem_support.mp hx)) hE.1
  have : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap j) := hE.1
  rw [isExceptionalCurveOfFirstKind_iff_pullbackPicardClass, ← pullbackClass_comap_eq j D h,
    Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
  exact hE.pullbackPicardClass_invertibleSheaf

end AlgebraicGeometry.Scheme.IdealSheafData

end
