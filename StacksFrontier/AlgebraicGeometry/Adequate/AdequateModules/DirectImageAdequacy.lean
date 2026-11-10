module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.DirectImage
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.BaseChangeFamilyCohomology
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineLocalUnconditional
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineSheafTopology
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.StandardAffineDescentReduction
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainDescent
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.Abelian

/-!
# Adequacy of the direct images along a quasi-compact, quasi-separated morphism

This module proves [Stacks, Tag 06VR]: for a quasi-compact and quasi-separated morphism
`f : T ⟶ S` and an adequate `𝒪`-module `𝓕` on a chosen big `τ`-site over `T`, the direct image
`f_*𝓕` and every higher direct image `R^i f_*𝓕` are adequate on a chosen big `τ`-site over `S`.

## The argument

It is the source's. Over an affine `Spec A` of the site over `S`, the base changes
`T_B = T ×_S Spec B`, for the `A`-algebras `B` of the site, form a family of objects of the site
over `T`, and `B ↦ H^q(T_B, 𝓕)` is a module-valued functor on those algebras.

* `R^i f_*𝓕` is the sheafification of the presheaf `V ↦ H^i(V ×_S T, 𝓕)`, because sheafification
  is exact ([Stacks, Tag 072W]); the affine sections of that presheaf over `Spec A` are
  `B ↦ H^i(T_B, 𝓕)`, because evaluation is exact; so by [Stacks, Tag 06VP] it suffices that these
  functors are adequate.
* `T_A` is quasi-compact and quasi-separated, being the base change of `f` to `Spec A`, so the
  induction principle of [Stacks, Tag 08DR] applies to its opens with the Mayer–Vietoris sequence
  as induction step (`Stacks.Adequate.prop_rightDerived_openFamilySections`): adequacy is a weak
  Serre property of the module-valued functors on the algebras of the site
  ([Stacks, Tags 06V3, 06V2, 06V8]).
* For an affine open `U = Spec R` of `T_A`, the preimages `U_B = Spec(R ⊗_A B)` are affine, so
  the higher cohomology vanishes by [Stacks, Tag 06VM] (3), and the sections `B ↦ 𝓕(U_B)` are
  `B ↦ F_{𝓕, R}(R ⊗_A B)`, adequate by [Stacks, Tags 06VI and 06VA].

## Main results

* `Stacks.Adequate.isAdequate_directImage` — **[Stacks, Tag 06VR] for `f_*𝓕`**.
* `Stacks.Adequate.isAdequate_higherDirectImage` — **[Stacks, Tag 06VR] for `R^i f_*𝓕`**, every
  `i`. The injectives and the sheafification that the derived functor needs are instances on the
  sites ([Stacks, Tag 01DU]), not hypotheses.

## References

* [Stacks Project, Tag 06VR](https://stacks.math.columbia.edu/tag/06VR)
* [Stacks Project, Tag 06VM](https://stacks.math.columbia.edu/tag/06VM)
* [Stacks Project, Tag 06VP](https://stacks.math.columbia.edu/tag/06VP)
* [Stacks Project, Tag 06VA](https://stacks.math.columbia.edu/tag/06VA)
* [Stacks Project, Tag 06VI](https://stacks.math.columbia.edu/tag/06VI)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 01DU](https://stacks.math.columbia.edu/tag/01DU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S T : Scheme.{u}}

/-! ### Base change squares -/

section BaseChange

variable (B : BigSite τ S) (C : BigSite τ T) (f : T ⟶ S) (Φ : B.category ⥤ C.category)
  (ν : Φ ⋙ C.toOver ⋙ Over.forget T ⟶ B.toOver ⋙ Over.forget S)

/-- **The transition maps of the base change are base changes.** If `Φ` computes base change
along `f`, then for a morphism `g : V' ⟶ V` of the site over `S` the square
`V' ×_S T ⟶ V ×_S T` over `V' ⟶ V` is a pullback square: both `V' ×_S T` and `V ×_S T` are
pullbacks of `f`, and a pullback of a pullback is cancelled off. -/
public theorem isPullback_map_of_isBaseChangeAlong (hbc : IsBaseChangeAlong B C f Φ ν)
    {V' V : B.category} (g : V' ⟶ V) :
    IsPullback ((Φ ⋙ C.toOver ⋙ Over.forget T).map g) (ν.app V') (ν.app V)
      ((B.toOver ⋙ Over.forget S).map g) := by
  refine IsPullback.of_right (h₁₂ := (C.toOver.obj (Φ.obj V)).hom)
    (h₂₂ := (B.toOver.obj V).hom) ?_ (ν.naturality g) (hbc V).flip
  have h₁ : (Φ ⋙ C.toOver ⋙ Over.forget T).map g ≫ (C.toOver.obj (Φ.obj V)).hom =
      (C.toOver.obj (Φ.obj V')).hom := Over.w (C.toOver.map (Φ.map g))
  have h₂ : (B.toOver ⋙ Over.forget S).map g ≫ (B.toOver.obj V).hom =
      (B.toOver.obj V').hom := Over.w (B.toOver.map g)
  rw [h₁, h₂]
  exact (hbc V').flip

end BaseChange

/-! ### The family of base changes over an affine of the site -/

section Family

variable (B : BigSite τ S) (C : BigSite τ T) (f : T ⟶ S) (Φ : B.category ⥤ C.category)
  (ν : Φ ⋙ C.toOver ⋙ Over.forget T ⟶ B.toOver ⋙ Over.forget S)
  (A : CommRingCat.{u}) (a : Spec A ⟶ S) (hA : schemeSizeBelow B.cutoff (Spec A))

/-- **The family of base changes `B ↦ T ×_S Spec B`**, for the `A`-algebras `B` of the site over
`S`, as a family of objects of the site over `T`. -/
public abbrev baseChangeFamily :
    (AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff))ᵒᵖ ⥤ C.category :=
  affineSpecOver B A a ⋙ Φ

/-- The base ring `A` as an algebra of the site. -/
public abbrev baseAlgebraOp :
    (AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff))ᵒᵖ :=
  op (AdequateFunctor.BaseAlgebraObject.siteOfSpecMem (schemeSizeBelow B.cutoff) hA).base

/-- The structure morphism `A ⟶ B` of an algebra of the site, as a morphism `B ⟶ A` of the
opposite category. -/
public abbrev toBaseAlgebra
    (d : (AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff))ᵒᵖ) :
    d ⟶ baseAlgebraOp B A hA :=
  ((AdequateFunctor.BaseAlgebraObject.siteOfSpecMem (schemeSizeBelow B.cutoff) hA).hom d.unop).op

/-- There is at most one morphism to the base algebra: `A`-algebra maps out of `A` are unique. -/
public theorem toBaseAlgebra_ext
    {d : (AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff))ᵒᵖ}
    (g g' : d ⟶ baseAlgebraOp B A hA) : g = g' := by
  refine Quiver.Hom.unop_inj (ObjectProperty.hom_ext _ (CommAlgCat.hom_ext
    (AlgHom.ext fun x => ?_)))
  exact (AlgHom.commutes g.unop.hom.hom x).trans (AlgHom.commutes g'.unop.hom.hom x).symm

/-- The base change `T_A = T ×_S Spec A` itself, as an object of the site over `T`. -/
public abbrev baseChangeBase : C.category :=
  (baseChangeFamily B C Φ A a).obj (baseAlgebraOp B A hA)

/-- The maps `T_B ⟶ T_A` of the family to its member at the base algebra. -/
public def baseChangeFamilyπ :
    baseChangeFamily B C Φ A a ⟶ (Functor.const _).obj (baseChangeBase B C Φ A a hA) where
  app d := (baseChangeFamily B C Φ A a).map (toBaseAlgebra B A hA d)
  naturality d d' g := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
      ← Functor.map_comp]
    exact congrArg _ (toBaseAlgebra_ext B A hA _ _)

variable [Φ.IsContinuous B.topology C.topology]

/-- The ring maps of the family: `B ⟶ Γ(Spec B) ⟶ Γ(T_B)`, the second induced by the first
projection of the fibre square. -/
public abbrev baseChangeFamilyRingMap :
    AdequateFunctor.algebraRingDiagramOn
        (AdequateFunctor.siteAlgebraInclusion (A : Type u) (schemeSizeBelow B.cutoff)) ⟶
      (baseChangeFamily B C Φ A a).op ⋙ C.structureSheaf.obj :=
  affineRingMap B A a ≫
    Functor.whiskerLeft (affineSpecOver B A a).op (directImageScalars B C Φ ν).hom

/-- **The affine sections of the direct image are the sections along the family of base
changes**: `(f_*𝓖)(Spec B) = 𝓖(T_B)`, with the same module structure, on the nose. -/
public theorem affineSectionFunctor_directImage (G : SheafOfModules.{u} C.structureSheaf) :
    affineSectionFunctor B ((directImage.{u, u} B C Φ ν).obj G) A a =
      (sectionsAlong C (baseChangeFamily B C Φ A a)
        (baseChangeFamilyRingMap B C Φ ν A a)).obj G := rfl

variable {B C f Φ ν} (hbc : IsBaseChangeAlong B C f Φ ν)
include hbc

omit [Φ.IsContinuous B.topology C.topology] in
/-- The morphism `T_A ⟶ Spec A` is a base change of `f`. -/
public theorem isPullback_baseChangeBase :
    IsPullback (ν.app ((affineSpecOver B A a).obj (baseAlgebraOp B A hA)))
      ((C.toOver.obj (baseChangeBase B C Φ A a hA)).hom)
      ((B.toOver.obj ((affineSpecOver B A a).obj (baseAlgebraOp B A hA))).hom) f :=
  hbc _

omit [Φ.IsContinuous B.topology C.topology] in
/-- **`T_A` is quasi-compact** when `f` is: it is the base change of `f` to the affine `Spec A`. -/
public theorem compactSpace_baseChangeBase [QuasiCompact f] :
    CompactSpace (baseChangeBase B C Φ A a hA).left.obj := by
  have : QuasiCompact (ν.app ((affineSpecOver B A a).obj (baseAlgebraOp B A hA))) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (isPullback_baseChangeBase A a hA hbc).flip inferInstance
  exact @QuasiCompact.compactSpace_of_compactSpace _ _ _ this
    (inferInstanceAs (CompactSpace (Spec _)))

omit [Φ.IsContinuous B.topology C.topology] in
/-- **`T_A` is quasi-separated** when `f` is: it is the base change of `f` to the affine
`Spec A`. -/
public theorem quasiSeparatedSpace_baseChangeBase [QuasiSeparated f] :
    QuasiSeparatedSpace (baseChangeBase B C Φ A a hA).left.obj := by
  have : QuasiSeparated (ν.app ((affineSpecOver B A a).obj (baseAlgebraOp B A hA))) :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated)
      (isPullback_baseChangeBase A a hA hbc).flip inferInstance
  exact @quasiSeparatedSpace_of_quasiSeparated _ _ _
    (inferInstanceAs (QuasiSeparatedSpace (Spec _))) this

omit [Φ.IsContinuous B.topology C.topology] in
/-- **The maps `T_B ⟶ T_A` are base changes of `Spec B ⟶ Spec A`.** -/
public theorem isPullback_baseChangeFamilyπ
    (d : (AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff))ᵒᵖ) :
    IsPullback ((baseChangeFamilyπ B C Φ A a hA).app d).left.hom
      (ν.app ((affineSpecOver B A a).obj d))
      (ν.app ((affineSpecOver B A a).obj (baseAlgebraOp B A hA)))
      ((affineSpecOver B A a).map (toBaseAlgebra B A hA d)).left.hom :=
  isPullback_map_of_isBaseChangeAlong B C f Φ ν hbc _

omit [Φ.IsContinuous B.topology C.topology] in
/-- **The maps `T_B ⟶ T_A` are affine morphisms**, being base changes of morphisms of affine
schemes. -/
public theorem isAffineHom_baseChangeFamilyπ
    (d : (AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff))ᵒᵖ) :
    IsAffineHom ((baseChangeFamilyπ B C Φ A a hA).app d).left.hom := by
  have : IsAffineHom ((affineSpecOver B A a).map (toBaseAlgebra B A hA d)).left.hom :=
    @isAffineHom_of_isAffine _ _ _ (inferInstanceAs (IsAffine (Spec _)))
      (inferInstanceAs (IsAffine (Spec _)))
  exact MorphismProperty.of_isPullback (P := @IsAffineHom)
    (isPullback_baseChangeFamilyπ A a hA hbc d).flip this

omit [Φ.IsContinuous B.topology C.topology] in
/-- **Over an affine open `U` of `T_A`, every `U_B` is affine**: it is the preimage of `U` under
the affine morphism `T_B ⟶ T_A`. -/
public theorem isAffine_openFamily_obj {U : (baseChangeBase B C Φ A a hA).left.obj.Opens}
    (hU : IsAffineOpen U)
    (d : (AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff))ᵒᵖ) :
    IsAffine ((openFamily C (baseChangeFamily B C Φ A a) (baseChangeBase B C Φ A a hA)
      (baseChangeFamilyπ B C Φ A a hA) U).obj d).left.obj := by
  have := isAffineHom_baseChangeFamilyπ A a hA hbc d
  exact hU.preimage ((baseChangeFamilyπ B C Φ A a hA).app d).left.hom

/-- **The higher cohomology vanishes over the preimages of an affine open**:
[Stacks, Tag 06VM] (3) at each `U_B`, which is affine. -/
public theorem isZero_rightDerived_openFamilySections_of_isAffineOpen
    (F : SheafOfModules.{u} C.structureSheaf) (hF : IsAdequate C F)
    {U : (baseChangeBase B C Φ A a hA).left.obj.Opens} (hU : IsAffineOpen U) (k : ℕ)
    (hk : 0 < k) :
    IsZero (((openFamilySections C (baseChangeFamily B C Φ A a) (baseChangeBase B C Φ A a hA)
      (baseChangeFamilyπ B C Φ A a hA) (baseChangeFamilyRingMap B C Φ ν A a) U).rightDerived
        k).obj F) := by
  apply isZero_rightDerived_sectionsAlong
  intro d
  have := isAffine_openFamily_obj A a hA hbc hU d
  exact isZero_rightDerived_evaluation_of_isAdequate C F hF _ k hk

end Family

/-! ### An affine open of the base change -/

section AffinePiece

variable {B : BigSite τ S} {C : BigSite τ T} {f : T ⟶ S} {Φ : B.category ⥤ C.category}
  {ν : Φ ⋙ C.toOver ⋙ Over.forget T ⟶ B.toOver ⋙ Over.forget S}
  [Φ.IsContinuous B.topology C.topology] (hbc : IsBaseChangeAlong B C f Φ ν)
  (A : CommRingCat.{u}) (a : Spec A ⟶ S) (hA : schemeSizeBelow B.cutoff (Spec A))
  {U : (baseChangeBase B C Φ A a hA).left.obj.Opens} (hU : IsAffineOpen U)

/-- The morphism from an open `U` of `T_A` to `Spec A`. -/
public abbrev pieceToBase : (U : Scheme.{u}) ⟶ Spec (CommRingCat.of (A : Type u)) :=
  U.ι ≫ ν.app ((affineSpecOver B A a).obj (baseAlgebraOp B A hA))

/-- The `A`-algebra structure of the ring of functions on an open `U` of `T_A`. -/
public abbrev pieceAlgebraMap :
    CommRingCat.of (A : Type u) ⟶ Γ((U : Scheme.{u}), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (A : Type u))).inv ≫
    (pieceToBase A a hA (ν := ν) (U := U)).appTop

/-- A scheme isomorphic to one with an open immersion into a scheme of size below `κ` has size
below `κ`. -/
private theorem schemeSizeBelow_of_iso_of_isOpenImmersion {κ : Cardinal.{u}}
    {X Y Z : Scheme.{u}} (e : X ≅ Y) (i : X ⟶ Z) [IsOpenImmersion i]
    (hZ : schemeSizeBelow κ Z) : schemeSizeBelow κ Y :=
  lt_of_eq_of_lt (Scheme.size_congr e).symm (Scheme.size_lt_of_isOpenImmersion i hZ)

omit [Φ.IsContinuous B.topology C.topology] in
/-- On an affine open `U` of `T_A`, the morphism to `Spec A` is `Spec` of the algebra
structure of `Γ(U)`, read through `U ≅ Spec Γ(U)`. -/
public theorem isoSpec_hom_SpecMap_pieceAlgebraMap [IsAffine (U : Scheme.{u})] :
    (U : Scheme.{u}).isoSpec.hom ≫ Spec.map (pieceAlgebraMap A a hA (ν := ν)) =
      pieceToBase A a hA (ν := ν) (U := U) := by
  rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
    Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

/-- The base change `B ⊗_A Γ(U)` of an algebra of the site. -/
public abbrev pieceTensor
    (B' : AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff)) :
    CommAlgCat.{u} Γ((U : Scheme.{u}), ⊤) :=
  (AdequateFunctor.baseChangeFunctor (pieceAlgebraMap A a hA (ν := ν) (U := U)).hom).obj B'.obj

/-- The structure map `A ⟶ B'` of an algebra of the site, as a map of rings. -/
public abbrev siteStructureMap
    (B' : AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff)) :
    CommRingCat.of (A : Type u) ⟶ CommRingCat.of B'.obj :=
  ((commAlgCatEquivUnder (CommRingCat.of (A : Type u))).functor.obj B'.obj).hom

/-- The map `B' ⟶ B' ⊗_A Γ(U)`. -/
public abbrev tensorInl
    (B' : AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff)) :
    CommRingCat.of B'.obj ⟶ CommRingCat.of (pieceTensor A a hA (ν := ν) (U := U) B') :=
  pushout.inl (siteStructureMap A B')
    (CommRingCat.ofHom (pieceAlgebraMap A a hA (ν := ν) (U := U)).hom)

/-- The map `Γ(U) ⟶ B' ⊗_A Γ(U)`. -/
public abbrev tensorInr
    (B' : AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff)) :
    Γ((U : Scheme.{u}), ⊤) ⟶ CommRingCat.of (pieceTensor A a hA (ν := ν) (U := U) B') :=
  pushout.inr (siteStructureMap A B')
    (CommRingCat.ofHom (pieceAlgebraMap A a hA (ν := ν) (U := U)).hom)

omit [Φ.IsContinuous B.topology C.topology] in
/-- `Spec (B ⊗_A Γ(U))` is the fibre product `Spec B ×_{Spec A} Spec Γ(U)`. -/
public theorem isPullback_pieceTensor
    (B' : AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff)) :
    IsPullback
      (Spec.map (tensorInl A a hA (ν := ν) (U := U) B'))
      (Spec.map (tensorInr A a hA (ν := ν) (U := U) B'))
      (Spec.map (siteStructureMap A B'))
      (Spec.map (CommRingCat.ofHom (pieceAlgebraMap A a hA (ν := ν) (U := U)).hom)) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (IsPushout.of_hasPushout _ _)

/-- The transition map `Spec B' ⟶ Spec A` of the family of spectra is `Spec` of the structure
map. -/
public theorem affineSpecOver_map_toBaseAlgebra
    (B' : AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff)) :
    ((affineSpecOver B A a).map (toBaseAlgebra B A hA (op B'))).left.hom =
      Spec.map (siteStructureMap A B') := rfl

/-- The preimage of `U` in the base change. -/
public abbrev piecePreimage
    (B' : AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff)) :
    ((baseChangeFamily B C Φ A a).obj (op B')).left.obj.Opens :=
  ((baseChangeFamilyπ B C Φ A a hA).app (op B')).left.hom ⁻¹ᵁ U

include hbc in
omit [Φ.IsContinuous B.topology C.topology] in
/-- **The preimage `U_{B'}` of `U` in `T_{B'}` is the fibre product `Spec B' ×_{Spec A} U`.** -/
public theorem isPullback_piecePreimage
    (B' : AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff)) :
    IsPullback (((baseChangeFamilyπ B C Φ A a hA).app (op B')).left.hom ∣_ U)
      ((piecePreimage A a hA (U := U) B').ι ≫ ν.app ((affineSpecOver B A a).obj (op B')))
      (pieceToBase A a hA (ν := ν) (U := U)) (Spec.map (siteStructureMap A B')) :=
  (isPullback_morphismRestrict _ U).paste_vert (isPullback_baseChangeFamilyπ A a hA hbc (op B'))

omit [Φ.IsContinuous B.topology C.topology] in
/-- `Spec (B' ⊗_A Γ(U))` is the fibre product `Spec B' ×_{Spec A} U`. -/
public theorem isPullback_pieceTensor' [IsAffine (U : Scheme.{u})]
    (B' : AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff)) :
    IsPullback
      (Spec.map (tensorInr A a hA (ν := ν) (U := U) B') ≫
          (U : Scheme.{u}).isoSpec.inv)
      (Spec.map (tensorInl A a hA (ν := ν) (U := U) B'))
      (pieceToBase A a hA (ν := ν) (U := U)) (Spec.map (siteStructureMap A B')) := by
  refine (isPullback_pieceTensor A a hA B').flip.of_iso (Iso.refl _)
    (U : Scheme.{u}).isoSpec.symm (Iso.refl _) (Iso.refl _) (by simp) (by simp) ?_ (by simp)
  simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, CommRingCat.ofHom_hom]
  rw [Iso.eq_inv_comp]
  exact isoSpec_hom_SpecMap_pieceAlgebraMap A a hA

/-- **The comparison `U_{B'} ≅ Spec (B' ⊗_A Γ(U))`**, of two fibre products of the same
cospan. -/
public def piecePreimageIso [IsAffine (U : Scheme.{u})]
    (B' : AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff)) :
    (piecePreimage A a hA (U := U) B' : Scheme.{u}) ≅
      Spec (CommRingCat.of (pieceTensor A a hA (ν := ν) (U := U) B')) :=
  (isPullback_piecePreimage hbc A a hA B').isoIsPullback _ _ (isPullback_pieceTensor' A a hA B')

include hbc in
omit [Φ.IsContinuous B.topology C.topology] in
/-- The base change `B' ⊗_A Γ(U)` of an algebra of the site over `S` has its spectrum in the site
over `T`: it is the preimage `U_{B'}`, an open subscheme of an object of that site. -/
public theorem pieceTensor_mem [IsAffine (U : Scheme.{u})]
    (B' : AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff)) :
    AdequateFunctor.algebraInSite.{u, u} (Γ((U : Scheme.{u}), ⊤) : Type u)
      (schemeSizeBelow C.cutoff) (pieceTensor A a hA (ν := ν) (U := U) B') :=
  schemeSizeBelow_of_iso_of_isOpenImmersion (piecePreimageIso hbc A a hA B')
    (piecePreimage A a hA (U := U) B').ι ((baseChangeFamily B C Φ A a).obj (op B')).left.property

/-- **Base change `B' ↦ B' ⊗_A Γ(U)`** from the `A`-algebras of the site over `S` to the
`Γ(U)`-algebras of the site over `T`. -/
public abbrev pieceBaseChange [IsAffine (U : Scheme.{u})] :
    AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff) ⥤
      AdequateFunctor.AlgebrasInSite (Γ((U : Scheme.{u}), ⊤) : Type u) (schemeSizeBelow C.cutoff) :=
  AdequateFunctor.baseChangeFunctorBetween (pieceAlgebraMap A a hA (ν := ν) (U := U)).hom _ _
    (pieceTensor_mem hbc A a hA)

/-- The morphism `Spec Γ(U) ⟶ T`. -/
public abbrev pieceToT [IsAffine (U : Scheme.{u})] : Spec Γ((U : Scheme.{u}), ⊤) ⟶ T :=
  (U : Scheme.{u}).isoSpec.inv ≫ U.ι ≫ (baseChangeBase B C Φ A a hA).hom.hom

/-- The family `B' ↦ Spec (B' ⊗_A Γ(U))` of objects of the site over `T`. -/
public abbrev pieceSpecFamily [IsAffine (U : Scheme.{u})] :
    (AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff))ᵒᵖ ⥤ C.category :=
  (pieceBaseChange hbc A a hA (U := U)).op ⋙
    affineSpecOver C (Γ((U : Scheme.{u}), ⊤)) (pieceToT A a hA (U := U))

include hbc in
omit [Φ.IsContinuous B.topology C.topology] in
/-- The restriction `U_{B'} ⟶ U` of `T_{B'} ⟶ T_A` followed by `U ≅ Spec Γ(U)`. -/
public theorem piecePreimageIso_hom_fst [IsAffine (U : Scheme.{u})]
    (B' : AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff)) :
    (piecePreimageIso hbc A a hA B').hom ≫
        (Spec.map (tensorInr A a hA (ν := ν) (U := U) B') ≫
          (U : Scheme.{u}).isoSpec.inv) =
      ((baseChangeFamilyπ B C Φ A a hA).app (op B')).left.hom ∣_ U :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

include hbc in
omit [Φ.IsContinuous B.topology C.topology] in
/-- The comparison `U_{B'} ≅ Spec (B' ⊗_A Γ(U))` followed by `Spec` of `B' ⟶ B' ⊗_A Γ(U)` is
the inclusion `U_{B'} ⟶ T_{B'}` followed by `T_{B'} ⟶ Spec B'`. -/
public theorem piecePreimageIso_hom_snd [IsAffine (U : Scheme.{u})]
    (B' : AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff)) :
    (piecePreimageIso hbc A a hA B').hom ≫
        Spec.map (tensorInl A a hA (ν := ν) (U := U) B') =
      (piecePreimage A a hA (U := U) B').ι ≫ ν.app ((affineSpecOver B A a).obj (op B')) :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

include hbc in
/-- **The comparison `U_{B'} ≅ Spec (B' ⊗_A Γ(U))` in the site over `T`.** -/
public def pieceObjIso [IsAffine (U : Scheme.{u})]
    (B' : AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff)) :
    (openFamily C (baseChangeFamily B C Φ A a) (baseChangeBase B C Φ A a hA)
        (baseChangeFamilyπ B C Φ A a hA) U).obj (op B') ≅
      (pieceSpecFamily hbc A a hA (U := U)).obj (op B') :=
  Over.isoMk (ObjectProperty.isoMk _ (piecePreimageIso hbc A a hA B')) (by
    apply ObjectProperty.hom_ext
    change (piecePreimageIso hbc A a hA B').hom ≫
        Spec.map (tensorInr A a hA (ν := ν) (U := U) B') ≫
          pieceToT A a hA (U := U) =
      (piecePreimage A a hA (U := U) B').ι ≫ ((baseChangeFamily B C Φ A a).obj (op B')).hom.hom
    have hw : ((baseChangeFamilyπ B C Φ A a hA).app (op B')).left.hom ≫
        (baseChangeBase B C Φ A a hA).hom.hom =
          ((baseChangeFamily B C Φ A a).obj (op B')).hom.hom :=
      congrArg (fun k => k.hom) (Over.w ((baseChangeFamilyπ B C Φ A a hA).app (op B')))
    rw [pieceToT, ← Category.assoc (Spec.map _), ← Category.assoc,
      piecePreimageIso_hom_fst hbc A a hA B', ← Category.assoc, morphismRestrict_ι,
      Category.assoc, hw])

/-- The transition maps of the family of spectra of the algebras of a site are `Spec` of the
algebra maps. -/
public theorem affineSpecOver_map_left_hom {S' : Scheme.{u}} (B'' : BigSite τ S')
    (R : CommRingCat.{u}) (b : Spec R ⟶ S')
    {d₁ d₂ : (AdequateFunctor.AlgebrasInSite (R : Type u) (schemeSizeBelow B''.cutoff))ᵒᵖ}
    (g : d₁ ⟶ d₂) :
    ((affineSpecOver B'' R b).map g).left.hom =
      Spec.map (CommRingCat.ofHom g.unop.hom.hom.toRingHom) := rfl

omit [Φ.IsContinuous B.topology C.topology] in
/-- The transition maps of the base changes `B' ⊗_A Γ(U)` restrict to the identity on `Γ(U)`. -/
public theorem pieceSpecFamily_map_inr [IsAffine (U : Scheme.{u})]
    {d₁ d₂ : (AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff))ᵒᵖ}
    (g : d₁ ⟶ d₂) :
    ((pieceSpecFamily hbc A a hA (U := U)).map g).left.hom ≫
        Spec.map (tensorInr A a hA (ν := ν) (U := U) (d₂.unop)) =
      Spec.map (tensorInr A a hA (ν := ν) (U := U) (d₁.unop)) := by
  rw [Functor.comp_map, affineSpecOver_map_left_hom]
  refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
  ext x
  exact ((pieceBaseChange hbc A a hA (U := U)).map g.unop).hom.hom.commutes x

omit [Φ.IsContinuous B.topology C.topology] in
/-- The transition maps of the base changes `B' ⊗_A Γ(U)` restrict to the given algebra maps
on the algebras of the site. -/
public theorem pieceSpecFamily_map_inl [IsAffine (U : Scheme.{u})]
    {d₁ d₂ : (AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff))ᵒᵖ}
    (g : d₁ ⟶ d₂) :
    ((pieceSpecFamily hbc A a hA (U := U)).map g).left.hom ≫
        Spec.map (tensorInl A a hA (ν := ν) (U := U) (d₂.unop)) =
      Spec.map (tensorInl A a hA (ν := ν) (U := U) (d₁.unop)) ≫
        Spec.map (CommRingCat.ofHom g.unop.hom.hom.toRingHom) := by
  rw [Functor.comp_map, affineSpecOver_map_left_hom]
  refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_comp _ _))
  ext x
  exact (ConcreteCategory.congr_hom
    ((AdequateFunctor.baseChangeRingHom (pieceAlgebraMap A a hA (ν := ν) (U := U)).hom).naturality
      g.unop.hom.op.op) x).symm

omit [Φ.IsContinuous B.topology C.topology] in
/-- The restriction maps of the preimages of `U` are compatible with the restrictions of the maps
`T_{B'} ⟶ T_A` to `U`. -/
public theorem resLE_comp_morphismRestrict
    {d₁ d₂ : (AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff))ᵒᵖ}
    (g : d₁ ⟶ d₂) (e) :
    ((baseChangeFamily B C Φ A a).map g).left.hom.resLE (piecePreimage A a hA (U := U) d₂.unop)
        (piecePreimage A a hA (U := U) d₁.unop) e ≫
        (((baseChangeFamilyπ B C Φ A a hA).app d₂).left.hom ∣_ U) =
      ((baseChangeFamilyπ B C Φ A a hA).app d₁).left.hom ∣_ U := by
  rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, morphismRestrict_ι,
    Scheme.Hom.resLE_comp_ι_assoc, openFamily_comp]

include hbc in
/-- **The preimages `U_{B'}` and the spectra `Spec (B' ⊗_A Γ(U))` are isomorphic families of
objects of the site over `T`.** -/
public def pieceIso [IsAffine (U : Scheme.{u})] :
    openFamily C (baseChangeFamily B C Φ A a) (baseChangeBase B C Φ A a hA)
        (baseChangeFamilyπ B C Φ A a hA) U ≅ pieceSpecFamily hbc A a hA (U := U) :=
  NatIso.ofComponents (fun d => pieceObjIso hbc A a hA d.unop) (by
    intro d₁ d₂ g
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change ((openFamily C (baseChangeFamily B C Φ A a) (baseChangeBase B C Φ A a hA)
        (baseChangeFamilyπ B C Φ A a hA) U).map g).left.hom ≫
          (piecePreimageIso hbc A a hA d₂.unop).hom =
      (piecePreimageIso hbc A a hA d₁.unop).hom ≫
        ((pieceSpecFamily hbc A a hA (U := U)).map g).left.hom
    change ((baseChangeFamily B C Φ A a).map g).left.hom.resLE
        (piecePreimage A a hA (U := U) d₂.unop) (piecePreimage A a hA (U := U) d₁.unop) _ ≫
          (piecePreimageIso hbc A a hA d₂.unop).hom = _
    apply (isPullback_pieceTensor' A a hA (U := U) d₂.unop).hom_ext
    · rw [Category.assoc, piecePreimageIso_hom_fst, resLE_comp_morphismRestrict]
      refine (piecePreimageIso_hom_fst hbc A a hA d₁.unop).symm.trans ?_
      refine (congrArg (fun k => (piecePreimageIso hbc A a hA d₁.unop).hom ≫ k ≫
        (U : Scheme.{u}).isoSpec.inv) (pieceSpecFamily_map_inr hbc A a hA g).symm).trans ?_
      exact (congrArg ((piecePreimageIso hbc A a hA d₁.unop).hom ≫ ·)
        (Category.assoc _ _ _)).trans (Category.assoc _ _ _).symm
    · rw [Category.assoc, piecePreimageIso_hom_snd]
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ ν.app ((affineSpecOver B A a).obj d₂))
        (Scheme.Hom.resLE_comp_ι _ _)).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (_ ≫ ·) (ν.naturality ((affineSpecOver B A a).map g))).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ _) (piecePreimageIso_hom_snd hbc A a hA d₁.unop).symm).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (_ ≫ ·) (pieceSpecFamily_map_inl hbc A a hA g).symm).trans ?_
      exact (Category.assoc _ _ _).symm)

include hbc in
omit [Φ.IsContinuous B.topology C.topology] in
/-- On rings: `B' ⟶ Γ(Spec B') ⟶ Γ(T_{B'}) ⟶ Γ(U_{B'}) ⟶ Γ(Spec (B' ⊗_A Γ(U)))` is
`B' ⟶ B' ⊗_A Γ(U) ⟶ Γ(Spec (B' ⊗_A Γ(U)))`. -/
public theorem pieceRingMap_app [IsAffine (U : Scheme.{u})]
    (B' : AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff)) :
    (Scheme.ΓSpecIso (CommRingCat.of B'.obj)).inv ≫
        (ν.app ((affineSpecOver B A a).obj (op B'))).appTop ≫
          (piecePreimage A a hA (U := U) B').ι.appTop ≫
            (piecePreimageIso hbc A a hA B').inv.appTop =
      tensorInl A a hA (ν := ν) (U := U) B' ≫
        (Scheme.ΓSpecIso (CommRingCat.of (pieceTensor A a hA (ν := ν) (U := U) B'))).inv := by
  have h₁ : (piecePreimage A a hA (U := U) B').ι.appTop ≫
        (piecePreimageIso hbc A a hA B').inv.appTop =
      ((piecePreimageIso hbc A a hA B').inv ≫ (piecePreimage A a hA (U := U) B').ι).appTop :=
    (Scheme.Hom.comp_appTop _ _).symm
  have h₂ : (ν.app ((affineSpecOver B A a).obj (op B'))).appTop ≫
        ((piecePreimageIso hbc A a hA B').inv ≫ (piecePreimage A a hA (U := U) B').ι).appTop =
      (Spec.map (tensorInl A a hA (ν := ν) (U := U) B')).appTop := by
    refine (Scheme.Hom.comp_appTop _ _).symm.trans ?_
    refine congrArg Scheme.Hom.appTop ((Category.assoc _ _ _).trans ?_)
    exact IsPullback.isoIsPullback_inv_snd _ _ _ _
  refine (congrArg (fun k => (Scheme.ΓSpecIso (CommRingCat.of B'.obj)).inv ≫
    (ν.app ((affineSpecOver B A a).obj (op B'))).appTop ≫ k) h₁).trans ?_
  refine (congrArg (fun k => (Scheme.ΓSpecIso (CommRingCat.of B'.obj)).inv ≫ k) h₂).trans ?_
  exact (Scheme.ΓSpecIso_inv_naturality _).symm

include hbc in
/-- **The ring maps of the two families agree** across `Stacks.Adequate.pieceIso`. -/
public theorem pieceRingMap_compat [IsAffine (U : Scheme.{u})] :
    openFamilyRingMap C (baseChangeFamily B C Φ A a) (baseChangeBase B C Φ A a hA)
        (baseChangeFamilyπ B C Φ A a hA) (baseChangeFamilyRingMap B C Φ ν A a) U ≫
      Functor.whiskerRight (NatIso.op (pieceIso hbc A a hA (U := U))).inv C.structureSheaf.obj =
    AdequateFunctor.baseChangeRingHomBetween (pieceAlgebraMap A a hA (ν := ν) (U := U)).hom _ _
        (pieceTensor_mem hbc A a hA) ≫
      Functor.whiskerLeft (pieceBaseChange hbc A a hA (U := U)).op.op
        (affineRingMap C (Γ((U : Scheme.{u}), ⊤)) (pieceToT A a hA (U := U))) := by
  refine NatTrans.ext (funext fun X => ?_)
  exact congrArg (fun k => (forget₂ CommRingCat.{u} RingCat.{u}).map k)
    (pieceRingMap_app hbc A a hA X.unop.unop)

include hbc in
/-- **The sections over the preimages of an affine open `U` are a base change of an affine-section
functor**: `𝓖(U_{B'}) = F_{𝓖, Γ(U)}(B' ⊗_A Γ(U))`, as module-valued functors. -/
public def openFamilySectionsIsoPushforward [IsAffine (U : Scheme.{u})]
    (G : SheafOfModules.{u} C.structureSheaf) :
    (openFamilySections C (baseChangeFamily B C Φ A a) (baseChangeBase B C Φ A a hA)
        (baseChangeFamilyπ B C Φ A a hA) (baseChangeFamilyRingMap B C Φ ν A a) U).obj G ≅
      AdequateFunctor.pushforwardBetween (pieceAlgebraMap A a hA (ν := ν) (U := U)).hom _ _
        (pieceTensor_mem hbc A a hA)
        (affineSectionFunctor C G (Γ((U : Scheme.{u}), ⊤)) (pieceToT A a hA (U := U))) :=
  (Stacks.PresheafOfModules.pushforwardIsoOfIndexIso.{u} (pieceIso hbc A a hA (U := U))
    (pieceRingMap_compat hbc A a hA)).app G.val

include hbc in
/-- **The sections over the preimages of an affine open of `T_A` are adequate**, for an adequate
`𝓖`: they are `B' ↦ F_{𝓖, Γ(U)}(B' ⊗_A Γ(U))`, adequate by [Stacks, Tag 06VI] and
[Stacks, Tag 06VA]. -/
public theorem isAdequate_openFamilySections_of_isAffineOpen
    (G : SheafOfModules.{u} C.structureSheaf) (hG : IsAdequate C G) (hU : IsAffineOpen U) :
    AdequateFunctor.IsAdequate
      (AdequateFunctor.siteAlgebraInclusion (A : Type u) (schemeSizeBelow B.cutoff))
      ((openFamilySections C (baseChangeFamily B C Φ A a) (baseChangeBase B C Φ A a hA)
        (baseChangeFamilyπ B C Φ A a hA) (baseChangeFamilyRingMap B C Φ ν A a) U).obj G) := by
  have : IsAffine (U : Scheme.{u}) := hU
  have hR : schemeSizeBelow C.cutoff (Spec Γ((U : Scheme.{u}), ⊤)) :=
    schemeSizeBelow_of_iso_of_isOpenImmersion (U : Scheme.{u}).isoSpec U.ι
      (baseChangeBase B C Φ A a hA).left.property
  refine AdequateFunctor.IsAdequate.of_iso ?_ (openFamilySectionsIsoPushforward hbc A a hA G)
  exact AdequateFunctor.isAdequate_pushforwardBetween.{u, u} _ _ _ _ _
    (isAdequate_affineSectionFunctor.{u, u} C G hG _ _ hR)

end AffinePiece


/-! ### Adequacy is a weak Serre property on the algebras of the site -/

/-- **Adequacy is a weak Serre property of the module-valued functors on the algebras of a chosen
big site**: it contains zero and is closed under isomorphisms, kernels, cokernels and extensions,
[Stacks, Tags 06V3, 06V2 and 06V8] on that domain of algebras. -/
public theorem isWeakSerreClass_adequateOn_site (B : BigSite τ S) (A : CommRingCat.{u})
    (hA : schemeSizeBelow B.cutoff (Spec A)) :
    (AdequateFunctor.adequateOn.{u, u}
      (AdequateFunctor.siteAlgebraInclusion (A : Type u)
        (schemeSizeBelow B.cutoff))).IsWeakSerreClass :=
  let := AdequateFunctor.adequateOn_isClosedUnderKernels_site B.aleph0_lt_cutoff
    B.cutoff_isStrongPrelimit hA
  let := AdequateFunctor.adequateOn_isClosedUnderCokernels_site B.aleph0_lt_cutoff
    B.cutoff_isStrongPrelimit hA
  let : (AdequateFunctor.adequateOn.{u, u} (AdequateFunctor.siteAlgebraInclusion (A : Type u)
      (schemeSizeBelow B.cutoff))).IsClosedUnderExtensions :=
    ⟨fun hS h₁ h₃ => affineAdequateExtensions.{u, u} B A hA _ hS h₁ h₃⟩
  { }

/-! ### The cohomology of the base changes is adequate -/

section Cohomology

variable {B : BigSite τ S} {C : BigSite τ T} {f : T ⟶ S} {Φ : B.category ⥤ C.category}
  {ν : Φ ⋙ C.toOver ⋙ Over.forget T ⟶ B.toOver ⋙ Over.forget S}
  [Φ.IsContinuous B.topology C.topology] (hbc : IsBaseChangeAlong B C f Φ ν)

include hbc in
/-- **The claim of the source's proof of [Stacks, Tag 06VR]**: for a quasi-compact and
quasi-separated `f` and an adequate `𝓕` on the site over `T`, the module-valued functor
`B ↦ H^q(T_B, 𝓕)` on the `A`-algebras of the site over `S` is adequate, in every degree `q`.

This is Cases I–III of the source: the induction principle of [Stacks, Tag 08DR] over the
quasi-compact opens of the quasi-compact, quasi-separated scheme `T_A`, with the Mayer–Vietoris
sequence as induction step and the affine opens as base case. -/
public theorem isAdequate_rightDerived_sectionsAlong_baseChangeFamily (hqc : QuasiCompact f)
    (hqs : QuasiSeparated f) (F : SheafOfModules.{u} C.structureSheaf) (hF : IsAdequate C F)
    (A : CommRingCat.{u}) (a : Spec A ⟶ S) (hA : schemeSizeBelow B.cutoff (Spec A)) (q : ℕ) :
    AdequateFunctor.IsAdequate
      (AdequateFunctor.siteAlgebraInclusion (A : Type u) (schemeSizeBelow B.cutoff))
      (((sectionsAlong C (baseChangeFamily B C Φ A a)
        (baseChangeFamilyRingMap B C Φ ν A a)).rightDerived q).obj F) := by
  let := isWeakSerreClass_adequateOn_site B A hA
  have := compactSpace_baseChangeBase A a hA hbc
  have := quasiSeparatedSpace_baseChangeBase A a hA hbc
  have htop := prop_rightDerived_openFamilySections C (baseChangeFamily B C Φ A a)
    (baseChangeBase B C Φ A a hA) (baseChangeFamilyπ B C Φ A a hA)
    (baseChangeFamilyRingMap B C Φ ν A a)
    (AdequateFunctor.adequateOn.{u, u}
      (AdequateFunctor.siteAlgebraInclusion (A : Type u) (schemeSizeBelow B.cutoff))) F
    (fun U hU k => by
      cases k with
      | zero =>
        exact AdequateFunctor.IsAdequate.of_iso
          (isAdequate_openFamilySections_of_isAffineOpen hbc A a hA F hF hU)
          ((Functor.rightDerivedZeroIsoSelf _).app F)
      | succ k =>
        exact AdequateFunctor.isAdequate_of_isZero _
          (isZero_rightDerived_openFamilySections_of_isAffineOpen A a hA hbc F hF hU (k + 1)
            (Nat.succ_pos k)))
    ⊤ (by simpa using isCompact_univ (X := (baseChangeBase B C Φ A a hA).left.obj)) q
  exact AdequateFunctor.IsAdequate.of_iso htop
    ((Functor.rightDerivedIsoOfNatIso (openFamilySectionsTopIso C (baseChangeFamily B C Φ A a)
      (baseChangeBase B C Φ A a hA) (baseChangeFamilyπ B C Φ A a hA)
      (baseChangeFamilyRingMap B C Φ ν A a)) q).app F).symm

end Cohomology

/-! ### [Stacks, Tag 06VR] -/

section Tag06VR

variable (B : BigSite τ S) (C : BigSite τ T) (f : T ⟶ S) (Φ : B.category ⥤ C.category)
  (ν : Φ ⋙ C.toOver ⋙ Over.forget T ⟶ B.toOver ⋙ Over.forget S)
  [Φ.IsContinuous B.topology C.topology]

/-- **[Stacks, Tag 06VR] for the direct image.** Let `f : T ⟶ S` be a quasi-compact and
quasi-separated morphism of schemes and let `𝓕` be an adequate `𝒪`-module on a chosen big
`τ`-site over `T`. Then the direct image `f_*𝓕` is an adequate `𝒪`-module on a chosen big
`τ`-site over `S`.

The direct image is restriction along the base-change functor `Φ` of the two sites, with the
scalars transported along the first projection `ν` of the fibre squares
(`Stacks.Adequate.directImage`); `hbc` says that `Φ` and `ν` are base change along `f`. Over an
affine `Spec A` of the site over `S` the affine sections of `f_*𝓕` are `B ↦ 𝓕(T ×_S Spec B)`,
the degree-zero case of `Stacks.Adequate.isAdequate_rightDerived_sectionsAlong_baseChangeFamily`.
-/
@[stacks 06VR "`f_*𝓕` is adequate"]
public theorem isAdequate_directImage
    (F : SheafOfModules.{u} C.structureSheaf) (hF : IsAdequate C F)
    (hqc : QuasiCompact f) (hqs : QuasiSeparated f) (hbc : IsBaseChangeAlong B C f Φ ν) :
    IsAdequate B ((directImage.{u, u} B C Φ ν).obj F) := by
  refine isAdequate_of_forall_affineSectionFunctor B _ fun A a hA => ?_
  rw [affineSectionFunctor_directImage]
  exact AdequateFunctor.IsAdequate.of_iso
    (isAdequate_rightDerived_sectionsAlong_baseChangeFamily hbc hqc hqs F hF A a hA 0)
    ((Functor.rightDerivedZeroIsoSelf _).app F).symm

/-- The direct image followed by the inclusion into presheaves of modules. -/
public abbrev directImagePresheaf :
    SheafOfModules.{u} C.structureSheaf ⥤ PresheafOfModules.{u} B.structureSheaf.obj :=
  directImage.{u, u} B C Φ ν ⋙ (SheafOfModules.forget B.structureSheaf ⋙
    PresheafOfModules.restrictScalars (𝟙 B.structureSheaf.obj))

/-- The direct image followed by the inclusion into presheaves of modules is additive. -/
public instance additive_directImagePresheaf : (directImagePresheaf B C Φ ν).Additive where
  map_add := rfl

/-- **[Stacks, Tag 072W] for the direct image**: `R^i f_*` is the sheafification of the
`i`-th right derived functor of `f_*` read in presheaves of modules, sheafification being exact. -/
public def higherDirectImageIsoSheafification (i : ℕ) :
    higherDirectImage.{u, u} B C Φ ν i ≅
      (directImagePresheaf B C Φ ν).rightDerived i ⋙ sheafification.{u, u} B :=
  have : ((SheafOfModules.forget B.structureSheaf : SheafOfModules.{u} _ ⥤ _) ⋙
      PresheafOfModules.restrictScalars.{u} (𝟙 B.structureSheaf.obj)).Additive := ⟨rfl⟩
  have : (sheafification.{u, u} B).Additive :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 B.structureSheaf.obj)).left_adjoint_additive
  have : PreservesColimitsOfSize.{0, 0} (sheafification.{u, u} B) :=
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 B.structureSheaf.obj)).leftAdjoint_preservesColimits
  have : (sheafification.{u, u} B).PreservesHomology := Functor.preservesHomologyOfExact _
  Functor.rightDerivedIsoOfNatIso
      ((Functor.rightUnitor _).symm ≪≫
        Functor.isoWhiskerLeft (directImage.{u, u} B C Φ ν)
          (sheafificationCounitIso.{u, u} B).symm ≪≫
          (Functor.associator _ _ _).symm) i ≪≫
    Functor.rightDerivedCompIso _ _ i

/-- **[Stacks, Tag 06VR] for the higher direct images.** Let `f : T ⟶ S` be a quasi-compact and
quasi-separated morphism of schemes and let `𝓕` be an adequate `𝒪`-module on a chosen big
`τ`-site over `T`. Then every higher direct image `R^i f_*𝓕` is an adequate `𝒪`-module on a
chosen big `τ`-site over `S`.

`R^i f_*` is the `i`-th right derived functor of `Stacks.Adequate.directImage`, the source's
definition. It is the sheafification of the presheaf `V ↦ H^i(V ×_S T, 𝓕)`
(`Stacks.Adequate.higherDirectImageIsoSheafification`), whose affine sections over `Spec A` are
`B ↦ H^i(T ×_S Spec B, 𝓕)` because evaluation is exact; these are adequate by
`Stacks.Adequate.isAdequate_rightDerived_sectionsAlong_baseChangeFamily`, so the sheafification
is adequate by [Stacks, Tag 06VP].

The statement assumes nothing beyond the source. The typeclass arguments of
`Stacks.Adequate.higherDirectImage` are supplied by proved instances on the two sites: the
sheafification of abelian presheaves and the identification of its weak equivalences with the
locally bijective maps are `Stacks.Adequate.BigSite.hasSheafify_addCommGrpCat` and
`Stacks.Adequate.BigSite.wEqualsLocallyBijective_addCommGrpCat`, and the injectives in the
category of sheaves of modules on the site over `T` are
`Stacks.Adequate.BigSite.enoughInjectives_sheafOfModules`, which is [Stacks, Tag 01DU] on that
site (sheaves of modules on it form a Grothendieck abelian category). -/
@[stacks 06VR "`R^i f_*𝓕` is adequate for every `i`"]
public theorem isAdequate_higherDirectImage
    (F : SheafOfModules.{u} C.structureSheaf) (hF : IsAdequate C F)
    (hqc : QuasiCompact f) (hqs : QuasiSeparated f) (hbc : IsBaseChangeAlong B C f Φ ν)
    (i : ℕ) :
    IsAdequate B ((higherDirectImage.{u, u} B C Φ ν i).obj F) := by
  refine (adequate.{u, u} B).prop_of_iso
    ((higherDirectImageIsoSheafification B C Φ ν i).app F).symm ?_
  refine isAdequate_sheafification.{u, u} B (affineAdequateSheafTopology B) _ _
    (toSheafification.{u, u} B _) inferInstance inferInstance fun A a hA => ?_
  have : PreservesFiniteColimits (PresheafOfModules.pushforward.{u} (affineRingMap B A a)) :=
    ⟨fun _ _ _ => inferInstance⟩
  have : (PresheafOfModules.pushforward.{u} (affineRingMap B A a)).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  have : (PresheafOfModules.pushforward.{u} (affineRingMap B A a)).Additive := ⟨rfl⟩
  have : (directImagePresheaf B C Φ ν ⋙
      PresheafOfModules.pushforward.{u} (affineRingMap B A a)).Additive := ⟨rfl⟩
  let e : directImagePresheaf B C Φ ν ⋙ PresheafOfModules.pushforward.{u} (affineRingMap B A a) ≅
      sectionsAlong C (baseChangeFamily B C Φ A a) (baseChangeFamilyRingMap B C Φ ν A a) :=
    Iso.refl _
  change AdequateFunctor.IsAdequate _ (((directImagePresheaf B C Φ ν).rightDerived i ⋙
    PresheafOfModules.pushforward.{u} (affineRingMap B A a)).obj F)
  exact AdequateFunctor.IsAdequate.of_iso
    (isAdequate_rightDerived_sectionsAlong_baseChangeFamily hbc hqc hqs F hF A a hA i)
    (((Functor.rightDerivedCompIso _ _ i).app F).symm ≪≫
      (Functor.rightDerivedIsoOfNatIso e i).app F)

end Tag06VR

end Stacks.Adequate

end
