module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessAndStrictTransformImageUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.OpenImmersionFromDenseOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformProperties

/-!
# The strict transform of a space over the open where the blowup is an isomorphism

Let `b : A' ⟶ A` be the blowup of an algebraic space `A` in a closed subspace `Z`, let
`U ⊆ A` be an open subspace whose points avoid those of `Z`, and let `f : X ⟶ A` be an
algebraic space over `A`.  The strict transform `X'` of `X` is a closed subspace of
`X ×_A A'`, and over the inverse image `b⁻¹(U)` nothing is cut away: there `X'` is all of
`X ×_A A'`, which is `X ×_A b⁻¹(U)`.  So if `X` is an isomorphism over `U`, then `X'` is an
isomorphism over `b⁻¹(U)`.  Moreover the strict transform of a separated morphism is
separated, being a closed subspace of a base change.

These are the properties of the strict transform used in the applications of flattening by
blowing up: they are the inputs of the last step of the proofs of [Stacks, Tag 0GUW] and
[Stacks, Tag 087F], where Stacks 0879 is applied to `X' ⟶ A'`.  Scheme-theoretic density of
`U` survives the blowup, as those proofs remark: the complement of the exceptional divisor is
scheme-theoretically dense and étale over `A`.

## Main results

* `AlgebraicGeometry.Space.isSeparated_strictTransformSpaceToBlowUp`: the strict transform of
  a separated morphism is separated.
* `AlgebraicGeometry.Space.range_pullbackFst_preimage_le_strictTransform`: the part of
  `X ×_A A'` lying over `b⁻¹(U)` is contained in the strict transform.
* `AlgebraicGeometry.Space.isIso_pullbackSnd_strictTransformSpaceToBlowUp`: if `X ⟶ A` is an
  isomorphism over `U`, then the strict transform `X' ⟶ A'` is an isomorphism over `b⁻¹(U)`.
* `Space.isSchemeTheoreticallyDense_preimage_of_isBlowupAlong_of_isSchemeTheoreticallyDense`:
  the inverse image of a scheme-theoretically dense open subspace under a blowup is
  scheme-theoretically dense.
* `AlgebraicGeometry.Space.isOpenImmersion_strictTransformSpaceToBlowUp`: if moreover `U` is
  scheme-theoretically dense with quasi-compact inclusion, `X ⟶ A` is separated, and the strict
  transform is flat and locally of finite type over `A'`, then it is an open immersion
  (Stacks 0879).

## References

* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 085T](https://stacks.math.columbia.edu/tag/085T)
* [Stacks Project, Tag 087F](https://stacks.math.columbia.edu/tag/087F)
* [Stacks Project, Tag 0GUW](https://stacks.math.columbia.edu/tag/0GUW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
instance (priority := high) hasPullbacks_presheaf_StrictTransformOverAdmissibleOpen
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

instance (priority := high) hasPullback_presheaf_StrictTransformOverAdmissibleOpen
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {A X A' : AlgebraicSpaces B S hS} (f : X ⟶ A) (b : A' ⟶ A)

/-- **The strict transform of a separated morphism is separated.**  The strict transform
`X' ⟶ A'` is the composite of the closed immersion `X' ⟶ X ×_A A'`, which is separated by
Stacks 04CH, with the base change `X ×_A A' ⟶ A'` of `f`, which is separated by Stacks 03KL. -/
theorem isSeparated_strictTransformSpaceToBlowUp (E : Subfunctor A'.1)
    (hf : IsSeparated B S hS f.hom) :
    IsSeparated B S hS (strictTransformSpaceToBlowUp B S hS f b E).hom :=
  isSeparated_comp B S hS _ _
    (isSeparated_of_isClosedImmersion B S hS _ (strictTransform B S hS f b E).2.2)
    (isSeparated_pullbackSnd B S hS b.hom hf)

/-- An open subspace whose points avoid those of a closed subspace `Z` is contained in the open
complement of `Z`. -/
theorem le_openComplementOfClosedSubspace (Z : ClosedSubspaces B S hS A.1)
    (U : OpenSubspaces B S hS A.1)
    (hUZ : Disjoint (subspacePointSet B S hS A.1 U.1) (subspacePointSet B S hS A.1 Z.1)) :
    U.1 ≤ (openComplementOfClosedSubspace B S hS A Z).1 := by
  have h : U ≤ openComplementOfClosedSubspace B S hS A Z := by
    rw [← (openSubspacesOrderIso B S hS A.1 A.2).le_iff_le]
    change subspacePointSet B S hS A.1 U.1 ⊆
      subspacePointSet B S hS A.1 (openComplementOfClosedSubspace B S hS A Z).1
    rw [subspacePointSet_openComplement]
    exact hUZ.subset_compl_right
  exact h

/-- **Over `b⁻¹(U)` the strict transform cuts nothing away.**  For `b` the blowup of `A` in
`Z` and `U ⊆ A` an open subspace avoiding `Z`, the part of `X ×_A A'` lying over the inverse
image `b⁻¹(U) ⊆ A'` is contained in the strict transform of `X`.

That part lies over `U`, hence over the complement of `Z`, along `X ×_A A' ⟶ X ⟶ A`, and the
part over the complement of the centre is contained in the strict transform by
`AlgebraicGeometry.Space.preimage_openComplement_le_strictTransform_of_isBlowupAlong`. -/
theorem range_pullbackFst_preimage_le_strictTransform (Z : ClosedSubspaces B S hS A.1)
    (hb : IsBlowupAlong B S hS Z b) (U : OpenSubspaces B S hS A.1)
    (hUZ : Disjoint (subspacePointSet B S hS A.1 U.1) (subspacePointSet B S hS A.1 Z.1)) :
    Subfunctor.range (pullback.fst (strictTransformPullbackToBlowUp B S hS f b).hom
        (U.1.preimage b.hom).ι) ≤
      (strictTransform B S hS f b (Z.1.preimage b.hom)).1 := by
  refine le_trans ?_ (preimage_openComplement_le_strictTransform_of_isBlowupAlong B S hS f b Z hb)
  have hU := le_openComplementOfClosedSubspace Z U hUZ
  rintro T _ ⟨y, rfl⟩
  apply hU
  have hw := (AlgebraicSpaces.isPullback_fiberProduct B S hS f b).w
  have h1 := ConcreteCategory.congr_hom (NatTrans.congr_app (pullback.condition
    (f := (strictTransformPullbackToBlowUp B S hS f b).hom)
    (g := (U.1.preimage b.hom).ι)) T) y
  have h2 := ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg InducedCategory.Hom.hom hw) T)
    ((pullback.fst (strictTransformPullbackToBlowUp B S hS f b).hom
      (U.1.preimage b.hom).ι).app T y)
  simp only [NatTrans.comp_app_apply] at h1 h2
  change f.hom.app T ((pullback.fst f.hom b.hom).app T _) ∈ U.1.obj T
  rw [show f.hom.app T ((pullback.fst f.hom b.hom).app T ((pullback.fst
      (strictTransformPullbackToBlowUp B S hS f b).hom (U.1.preimage b.hom).ι).app T y)) =
    b.hom.app T ((pullback.snd f.hom b.hom).app T ((pullback.fst
      (strictTransformPullbackToBlowUp B S hS f b).hom (U.1.preimage b.hom).ι).app T y)) from
    h2]
  change b.hom.app T ((strictTransformPullbackToBlowUp B S hS f b).hom.app T _) ∈ U.1.obj T
  rw [h1]
  exact ((pullback.snd (strictTransformPullbackToBlowUp B S hS f b).hom
    (U.1.preimage b.hom).ι).app T y).2

/-- **The base change `X ×_A A'` is an isomorphism over `b⁻¹(U)` when `X` is one over `U`.**
For any morphism `b : A' ⟶ A` and any open subspace `U ⊆ A` over which `f : X ⟶ A` is an
isomorphism, the base change `X ×_A A' ⟶ A'` is an isomorphism over the inverse image
`b⁻¹(U)`: the part of `X ×_A A'` over `b⁻¹(U)` is `(X ×_A U) ×_U b⁻¹(U)`, a base change of the
isomorphism `X ×_A U ⟶ U`. -/
theorem isIso_pullbackSnd_strictTransformPullbackToBlowUp (U : OpenSubspaces B S hS A.1)
    (hiso : IsIso (pullback.snd f.hom U.1.ι)) :
    IsIso (pullback.snd (strictTransformPullbackToBlowUp B S hS f b).hom
      (U.1.preimage b.hom).ι) := by
  set U' := U.1.preimage b.hom
  have sq1 : IsPullback (pullback.fst f.hom b.hom) (pullback.snd f.hom b.hom) f.hom b.hom :=
    IsPullback.of_hasPullback _ _
  have sq2 : IsPullback (pullback.fst (pullback.snd f.hom b.hom) U'.ι)
      (pullback.snd (pullback.snd f.hom b.hom) U'.ι) (pullback.snd f.hom b.hom) U'.ι :=
    IsPullback.of_hasPullback _ _
  have sq3 := Subfunctor.isPullback_preimage b.hom U.1
  have sq4 : IsPullback (pullback.fst f.hom U.1.ι) (pullback.snd f.hom U.1.ι) f.hom U.1.ι :=
    IsPullback.of_hasPullback _ _
  have outer := sq2.paste_horiz sq1
  rw [← sq3.w] at outer
  have hw : (pullback.fst (pullback.snd f.hom b.hom) U'.ι ≫ pullback.fst f.hom b.hom) ≫ f.hom =
      (pullback.snd (pullback.snd f.hom b.hom) U'.ι ≫ U.1.fromPreimage b.hom) ≫ U.1.ι := by
    rw [outer.w, Category.assoc]
  have hs : IsPullback ((pullback.lift _ _ hw) ≫ pullback.fst f.hom U.1.ι)
      (pullback.snd (pullback.snd f.hom b.hom) U'.ι) f.hom
      (U.1.fromPreimage b.hom ≫ U.1.ι) := by
    rw [pullback.lift_fst]
    exact outer
  have top := IsPullback.of_right hs (pullback.lift_snd _ _ hw) sq4
  exact top.isIso_snd_of_isIso

/-- **If `X` is an isomorphism over `U`, its strict transform is an isomorphism over
`b⁻¹(U)`.**  Let `b : A' ⟶ A` be the blowup of `A` in a closed subspace `Z`, let `U ⊆ A` be an
open subspace whose points avoid those of `Z`, and let `f : X ⟶ A` be such that
`f⁻¹(U) ⟶ U` is an isomorphism.  Then the strict transform `X' ⟶ A'` of `X` with respect to `b`
is an isomorphism over `b⁻¹(U)`.

The base change `X ×_A A' ⟶ A'` is an isomorphism over `b⁻¹(U)` by
`AlgebraicGeometry.Space.isIso_pullbackSnd_strictTransformPullbackToBlowUp`, and over `b⁻¹(U)`
the strict transform is all of `X ×_A A'` by
`AlgebraicGeometry.Space.range_pullbackFst_preimage_le_strictTransform`. -/
theorem isIso_pullbackSnd_strictTransformSpaceToBlowUp (Z : ClosedSubspaces B S hS A.1)
    (hb : IsBlowupAlong B S hS Z b) (U : OpenSubspaces B S hS A.1)
    (hUZ : Disjoint (subspacePointSet B S hS A.1 U.1) (subspacePointSet B S hS A.1 Z.1))
    (hiso : IsIso (pullback.snd f.hom U.1.ι)) :
    IsIso (pullback.snd (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)).hom
      (U.1.preimage b.hom).ι) := by
  set U' := U.1.preimage b.hom
  set p := (strictTransformPullbackToBlowUp B S hS f b).hom
  set i := (strictTransform B S hS f b (Z.1.preimage b.hom)).1.ι
  have hp : IsIso (pullback.snd p U'.ι) :=
    isIso_pullbackSnd_strictTransformPullbackToBlowUp f b U hiso
  have hfac := range_pullbackFst_preimage_le_strictTransform f b Z hb U hUZ
  set h := Subfunctor.lift (pullback.fst p U'.ι) hfac
  have hh : h ≫ i = pullback.fst p U'.ι := Subfunctor.lift_ι _ _
  change IsIso (pullback.snd (i ≫ p) U'.ι)
  have hlift : (inv (pullback.snd p U'.ι) ≫ h) ≫ i ≫ p = 𝟙 _ ≫ U'.ι := by
    rw [Category.assoc, reassoc_of% hh, pullback.condition, IsIso.inv_hom_id_assoc,
      Category.id_comp]
  have hm : pullback.snd (i ≫ p) U'.ι ≫ inv (pullback.snd p U'.ι) =
      pullback.lift (pullback.fst (i ≫ p) U'.ι ≫ i) (pullback.snd (i ≫ p) U'.ι)
        (by rw [Category.assoc, pullback.condition]) := by
    rw [IsIso.comp_inv_eq, pullback.lift_snd]
  refine ⟨⟨pullback.lift (inv (pullback.snd p U'.ι) ≫ h) (𝟙 _) hlift, ?_, ?_⟩⟩
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp, ← Category.assoc, hm]
      rw [← cancel_mono i, Category.assoc, hh, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]
  · exact pullback.lift_snd _ _ _

/-! ### Scheme-theoretic density after an admissible blowup -/

/-- **An étale morphism restricts to an étale morphism over an open subspace.**  For an étale
morphism `φ : V ⟶ Y` of algebraic spaces and an open subspace `C ⊆ Y`, the induced morphism
`φ⁻¹(C) ⟶ C` is étale, being a base change of `φ` (Stacks 03FU). -/
theorem isEtale_fromPreimage_of_isOpenSubspace {V Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : IsAlgebraicSpace B S hS V) (hY : IsAlgebraicSpace B S hS Y) (φ : V ⟶ Y)
    (hφ : IsEtale B S hS φ) (C : Subfunctor Y) (hC : IsOpenSubspace B S hS C) :
    IsEtale B S hS (C.fromPreimage φ) := by
  have hCpre : IsOpenSubspace B S hS (C.preimage φ) :=
    isOpenSubspace_preimage B S hS φ C hY hV hC
  exact isEtale_of_isPullback B S hS _ _ _ _
    (show IsPullback
        (ObjectProperty.homMk (C.fromPreimage φ) :
          (⟨(C.preimage φ).toFunctor, hCpre.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨C.toFunctor, hC.1⟩)
        (ObjectProperty.homMk (C.preimage φ).ι : _ ⟶ ⟨V, hV⟩)
        (ObjectProperty.homMk C.ι : _ ⟶ ⟨Y, hY⟩)
        (ObjectProperty.homMk φ : (⟨V, hV⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) from
      IsPullback.of_map_of_faithful
        (F := ObjectProperty.ι (fun T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
          IsAlgebraicSpace B S hS T)) (Subfunctor.isPullback_preimage φ C)).flip hφ

/-- **Scheme-theoretic closures are all of the space through a dense open.**  Let `W ⊆ V` be
an open subspace of an algebraic space whose scheme-theoretic closure is all of `V`, and let
`Y ⊆ V` be a subspace whose trace on `W` has scheme-theoretic closure all of `W`.  Then the
scheme-theoretic closure of `Y` is all of `V`.

The scheme-theoretic closure of `Y ∩ W` in `W` lies in the inverse image of the closure of `Y`
in `V` (Stacks 0CP2), so `W` lies in the closure of `Y`, which is a closed subspace; hence so
does the closure of `W`, which is `V`. -/
theorem schemeTheoreticClosure_eq_top_of_preimage_open {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : IsAlgebraicSpace B S hS V) (W : Subfunctor V) (hW : IsOpenSubspace B S hS W)
    (hWd : schemeTheoreticClosure B S hS W = ⊤) (Y : Subfunctor V)
    (hY : schemeTheoreticClosure B S hS (Y.preimage W.ι) = ⊤) :
    schemeTheoreticClosure B S hS Y = ⊤ := by
  have hsq : (Y.preimage W.ι).ι ≫ W.ι = Y.fromPreimage W.ι ≫ Y.ι :=
    (Subfunctor.isPullback_preimage W.ι Y).w.symm
  have hle := schemeTheoreticImageSubfunctor_le_preimage B S hS hW.1 hV hsq
  change schemeTheoreticClosure B S hS (Y.preimage W.ι) ≤ _ at hle
  rw [hY] at hle
  have hWle : Subfunctor.range W.ι ≤ schemeTheoreticClosure B S hS Y := by
    rintro T _ ⟨w, rfl⟩
    exact hle T (Set.mem_univ w)
  refine top_unique ?_
  rw [← hWd]
  exact schemeTheoreticImageSubfunctor_le B S hS W.ι
    (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS Y.ι hV) hWle

/-- **Scheme-theoretic density survives a blowup.**  Let `b : A' ⟶ A` be the blowup of `A` in a
closed subspace `Z`, and let `U ⊆ A` be a scheme-theoretically dense open subspace.  Then
`b⁻¹(U)` is scheme-theoretically dense in `A'`.

The complement `C = b⁻¹(A ∖ Z)` of the exceptional divisor is scheme-theoretically dense in
`A'` (Stacks 085T (2) and Stacks 083S), and `C ⟶ A` is étale, being the isomorphism
`C ≅ A ∖ Z` of Stacks 085T (1) followed by an open immersion.  So for an étale `φ : V ⟶ A'`
the trace of `φ⁻¹b⁻¹(U)` on `φ⁻¹(C)` is the inverse image of `U` along the étale morphism
`φ⁻¹(C) ⟶ A`, whose scheme-theoretic closure is everything by density of `U`; and
`φ⁻¹(C)` is scheme-theoretically dense in `V`.  Conclude by
`AlgebraicGeometry.Space.schemeTheoreticClosure_eq_top_of_preimage_open`.

This is the remark "Note that `U` is still scheme theoretically dense" in the proofs of
[Stacks, Tag 087F] and [Stacks, Tag 0GUW], for a `U`-admissible blowup. -/
theorem isSchemeTheoreticallyDense_preimage_of_isBlowupAlong_of_isSchemeTheoreticallyDense
    (Z : ClosedSubspaces B S hS A.1) (hb : IsBlowupAlong B S hS Z b) (U : Subfunctor A.1)
    (hU : IsSchemeTheoreticallyDense B S hS U) :
    IsSchemeTheoreticallyDense B S hS (U.preimage b.hom) := by
  set W := openComplementOfClosedSubspace B S hS A Z
  have hZW : subspacePointSet B S hS A.1 Z.1 = (subspacePointSet B S hS A.1 W.1)ᶜ := by
    rw [subspacePointSet_openComplement, compl_compl]
  have hCd : IsSchemeTheoreticallyDense B S hS (W.1.preimage b.hom) :=
    isSchemeTheoreticallyDense_preimage_of_isBlowupAlong W Z hb hZW
  have hCo : IsOpenSubspace B S hS (W.1.preimage b.hom) :=
    isOpenSubspace_preimage B S hS b.hom W.1 A.2 A'.2 W.2
  have hCet : IsEtale B S hS ((W.1.preimage b.hom).ι ≫ b.hom) := by
    rw [← (Subfunctor.isPullback_preimage b.hom W.1).w]
    have := isIso_fromPreimage_openComplement hb
    exact isEtale_comp B S hS (isEtale_of_isIso B S hS _) (isEtale_ι_of_isOpenSubspace W.2)
  intro V hV φ hφ
  set C := W.1.preimage b.hom
  have hVC : IsOpenSubspace B S hS (C.preimage φ) :=
    isOpenSubspace_preimage B S hS φ C A'.2 hV hCo
  refine schemeTheoreticClosure_eq_top_of_preimage_open hV (C.preimage φ) hVC (hCd hV φ hφ) _ ?_
  have hψ : IsEtale B S hS ((C.preimage φ).ι ≫ φ ≫ b.hom) := by
    rw [← Category.assoc, ← (Subfunctor.isPullback_preimage φ C).w, Category.assoc]
    exact isEtale_comp B S hS (isEtale_fromPreimage_of_isOpenSubspace hV A'.2 φ hφ C hCo) hCet
  have h := hU hVC.1 _ hψ
  rwa [Subfunctor.preimage_comp, Subfunctor.preimage_comp] at h

/-! ### The open immersion of the last step -/

/-- **A flat strict transform over a scheme-theoretically dense open is an open immersion.**
Let `b : A' ⟶ A` be the blowup of `A` in a closed subspace `Z`, let `U ⊆ A` be a
scheme-theoretically dense open subspace with quasi-compact inclusion whose points avoid those
of `Z`, and let `f : X ⟶ A` be separated with `f⁻¹(U) ⟶ U` an isomorphism.  If the strict
transform `X' ⟶ A'` of `X` is flat and locally of finite type, then it is an open immersion. -/
theorem isOpenImmersion_strictTransformSpaceToBlowUp (Z : ClosedSubspaces B S hS A.1)
    (hb : IsBlowupAlong B S hS Z b) (U : OpenSubspaces B S hS A.1)
    (hUZ : Disjoint (subspacePointSet B S hS A.1 U.1) (subspacePointSet B S hS A.1 Z.1))
    (hUqc : IsQuasiCompact B S hS U.1.ι) (hUd : IsSchemeTheoreticallyDense B S hS U.1)
    (hf : IsSeparated B S hS f.hom) (hiso : IsIso (pullback.snd f.hom U.1.ι))
    (hflat : IsFlat B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)).hom)
    (hlft : IsLocallyOfFiniteType B S hS
      (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)).hom) :
    IsOpenImmersion B S hS
      (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)).hom :=
  isOpenImmersion_of_isIso_pullback_snd B S hS
    (strictTransformSpace B S hS f b (Z.1.preimage b.hom)).2 A'.2 _ (U.1.preimage b.hom)
    (isOpenSubspace_preimage B S hS b.hom U.1 A.2 A'.2 U.2)
    (isSeparated_strictTransformSpaceToBlowUp f b _ hf) hlft hflat
    (isIso_pullbackSnd_strictTransformSpaceToBlowUp f b Z hb U hUZ hiso)
    (isQuasiCompact_of_isPullback B S hS (Subfunctor.isPullback_preimage b.hom U.1) hUqc)
    (isSchemeTheoreticallyDense_preimage_of_isBlowupAlong_of_isSchemeTheoreticallyDense b Z hb
      U.1 hUd)

end AlgebraicGeometry.Space

end
