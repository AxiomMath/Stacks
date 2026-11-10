module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.ZariskiBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeSpecRepresentability.Basic

/-!
# Sections of an adequate module along a flat morphism of affines

Let `S` be a scheme, let `B` be a chosen big `τ`-site over `S` and let `𝓕` be an adequate
`𝒪`-module on `B`. For a morphism `g : T ⟶ T'` of the site between affine objects whose
underlying morphism of schemes is flat, the restriction map of `𝓕` along `g` is a base change:

`𝒪(T) ⊗_{𝒪(T')} 𝓕(T') ≅ 𝓕(T)`.

This is the formula `𝓕(U) = 𝓕(V) ⊗_{𝒪(V)} 𝒪(U)` "for any flat morphism of affines `U → V` over
`S`" with which the source's proof of [Stacks, Tag 06VM] opens, read on arbitrary affine objects
of the site rather than on the spectra of algebras of the site.

## Main definitions

* `Stacks.Adequate.BigSite.commStructurePresheaf` — the presheaf of commutative rings of global
  functions on a chosen big site, whose underlying presheaf of rings is the structure sheaf.

## Main results

* `Stacks.Adequate.BigSite.bijective_restrictionBaseChange_of_flat` — the base-change
  comparison of the restriction map of an adequate `𝒪`-module along a flat morphism of affine
  objects of the site is bijective.

## Implementation notes

The formula on the spectra of algebras of the site is [Stacks, Tag 06UW] applied to
[Stacks, Tag 06VI], `Stacks.Adequate.bijective_affineSectionBaseChangeMap`. An affine object `T'`
of the site is isomorphic, in the site, to the spectrum of `𝒪(T')` over `S`, by
`AlgebraicGeometry.Scheme.isoSpec`, and an affine object `T` over it to the spectrum of the
`𝒪(T')`-algebra `𝒪(T)`, compatibly with `g` by `AlgebraicGeometry.Scheme.isoSpec_hom_naturality`;
the sections are transported along these isomorphisms by `Stacks.Adequate.BigSite.sectionsCongr`.
The two base-change maps then agree on pure tensors, which identifies them.

## References

* [Stacks Project, Tag 06VM](https://stacks.math.columbia.edu/tag/06VM)
* [Stacks Project, Tag 06UW](https://stacks.math.columbia.edu/tag/06UW)
* [Stacks Project, Tag 06VI](https://stacks.math.columbia.edu/tag/06VI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.PresheafOfModules

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

open scoped _root_.Stacks.PresheafOfModules.ChangeOfRings in
/-- **The base-change comparison of a restriction map is bijective as soon as some equivalence
`R Y ⊗[R X] M X ≃ M Y` agrees with it on pure tensors.** -/
public theorem bijective_restrictionBaseChange_of_equiv
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    letI := (R.map f).hom.toAlgebra
    ∀ (e : TensorProduct (R.obj X) (R.obj Y) (M.obj X) ≃ₗ[R.obj Y] M.obj Y),
      (∀ (c : R.obj Y) (x : M.obj X), e (c ⊗ₜ x) = c • M.map f x) →
        Function.Bijective (restrictionBaseChange M f) := by
  let := (R.map f).hom.toAlgebra
  intro e he
  have hfun : ∀ z, restrictionBaseChange M f z = e z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add z w hz hw =>
      exact (map_add _ z w).trans ((congrArg₂ (· + ·) hz hw).trans (map_add e z w).symm)
    | tmul c x => exact (restrictionBaseChange_tmul M f c x).trans (he c x).symm
  refine ⟨fun z w h ↦ e.injective ?_, fun y ↦ ?_⟩
  · rw [← hfun, ← hfun]
    exact h
  · obtain ⟨z, rfl⟩ := e.surjective y
    exact ⟨z, hfun z⟩

end Stacks.PresheafOfModules

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}}

/-- The presheaf of commutative rings of global functions on the underlying schemes of a chosen
big site. Forgetting commutativity gives the structure sheaf of the site on the nose. -/
public noncomputable abbrev BigSite.commStructurePresheaf (B : BigSite τ S) :
    B.categoryᵒᵖ ⥤ CommRingCat.{u} :=
  (B.toOver ⋙ Over.forget S).op ⋙ Scheme.Γ

/-- **The restriction map of an adequate `𝒪`-module along a flat morphism of affine objects of the
site is a base change.** For a morphism `g : T ⟶ T'` of a chosen big site over `S` between affine
objects whose underlying morphism of schemes is flat, the comparison
`𝒪(T) ⊗_{𝒪(T')} 𝓕(T') → 𝓕(T)` is bijective. -/
public theorem BigSite.bijective_restrictionBaseChange_of_flat (B : BigSite τ S)
    (F : SheafOfModules.{u} B.structureSheaf) (hF : IsAdequate B F) {T T' : B.category}
    (g : T ⟶ T') [IsAffine T.left.obj] [IsAffine T'.left.obj] (hg : Flat g.left.hom) :
    Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange
      (R := B.commStructurePresheaf) F.val g.op) := by
  let M : PresheafOfModules (B.commStructurePresheaf ⋙ forget₂ CommRingCat RingCat) := F.val
  let R' : CommRingCat.{u} := B.commStructurePresheaf.obj (op T')
  let R : CommRingCat.{u} := B.commStructurePresheaf.obj (op T)
  let φ : R' ⟶ R := B.commStructurePresheaf.map g.op
  let instA : Algebra R' R := φ.hom.toAlgebra
  have hszT' : schemeSizeBelow B.cutoff (Spec R') :=
    lt_of_eq_of_lt (Scheme.size_congr T'.left.obj.isoSpec).symm T'.left.property
  have hszT : schemeSizeBelow B.cutoff (Spec R) :=
    lt_of_eq_of_lt (Scheme.size_congr T.left.obj.isoSpec).symm T.left.property
  let f' : Spec R' ⟶ S := T'.left.obj.isoSpec.inv ≫ T'.hom.hom
  let XA : AdequateFunctor.AlgebrasInSite R' (schemeSizeBelow B.cutoff) :=
    ⟨CommAlgCat.of R' R', hszT'⟩
  let YA : AdequateFunctor.AlgebrasInSite R' (schemeSizeBelow B.cutoff) :=
    ⟨CommAlgCat.of R' R, hszT⟩
  let gA : XA ⟶ YA := ObjectProperty.homMk (CommAlgCat.ofHom (Algebra.ofId R' R))
  let aV : B.category := (affineSpecOver B R' f').obj (op XA)
  let aU : B.category := (affineSpecOver B R' f').obj (op YA)
  have hgw : g.left.hom ≫ T'.hom.hom = T.hom.hom :=
    congrArg (fun k : T.left ⟶ (⟨S, B.base_mem⟩ : SchemeBelow B.cutoff) => k.hom) (Over.w g)
  let isoV : T' ≅ aV := Over.isoMk (ObjectProperty.isoMk _ T'.left.obj.isoSpec) (by
    apply ObjectProperty.hom_ext
    change T'.left.obj.isoSpec.hom ≫ Spec.map (𝟙 Γ(T'.left.obj, ⊤)) ≫
      T'.left.obj.isoSpec.inv ≫ T'.hom.hom = T'.hom.hom
    rw [Spec.map_id, Category.id_comp, Iso.hom_inv_id_assoc])
  let isoU : T ≅ aU := Over.isoMk (ObjectProperty.isoMk _ T.left.obj.isoSpec) (by
    apply ObjectProperty.hom_ext
    change T.left.obj.isoSpec.hom ≫ Spec.map g.left.hom.appTop ≫
      T'.left.obj.isoSpec.inv ≫ T'.hom.hom = T.hom.hom
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id_assoc]
    exact hgw)
  have hsq : g.op ≫ isoU.inv.op = isoV.inv.op ≫ ((affineSpecOver B R' f').map gA.op).op := by
    rw [← op_comp, ← op_comp]
    congr 1
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact Over.OverMorphism.ext (ObjectProperty.hom_ext _ (Scheme.isoSpec_hom_naturality _).symm)
  have hV : 𝟙 (RingCat.of R') ≫ B.structureSheaf.obj.map isoV.inv.op =
      (forget₂ CommRingCat RingCat).map (Scheme.ΓSpecIso R').inv := by
    ext r
    exact congrArg (fun k : R' ⟶ Γ(Spec R', ⊤) ↦ k.hom r)
      (Stacks.RelativeSpec.isoSpec_inv_appTop T'.left.obj)
  have hU : 𝟙 (RingCat.of R) ≫ B.structureSheaf.obj.map isoU.inv.op =
      (forget₂ CommRingCat RingCat).map (Scheme.ΓSpecIso R).inv := by
    ext r
    exact congrArg (fun k : R ⟶ Γ(Spec R, ⊤) ↦ k.hom r)
      (Stacks.RelativeSpec.isoSpec_inv_appTop T.left.obj)
  let eM : M.obj (op T') ≃ₗ[R'] (affineSectionFunctor B F R' f').obj (op (op XA)) :=
    BigSite.sectionsCongr B F isoV.symm _ _ hV
  let eN : M.obj (op T) ≃ₗ[R] (affineSectionFunctor B F R' f').obj (op (op YA)) :=
    BigSite.sectionsCongr B F isoU.symm _ _ hU
  have hflat : RingHom.Flat ((AdequateFunctor.siteAlgebraInclusion R'
      (schemeSizeBelow B.cutoff)).map gA).hom.toRingHom :=
    (HasRingHomProperty.iff_of_isAffine (P := @Flat) (f := g.left.hom)).mp hg
  have hbij := bijective_affineSectionBaseChangeMap B F hF R' f' hszT' gA hflat
  let eBC : TensorProduct R' R
      ((affineSectionFunctor B F R' f').obj (op (op XA))) ≃ₗ[R]
      ((affineSectionFunctor B F R' f').obj (op (op YA))) := LinearEquiv.ofBijective _ hbij
  let etot : TensorProduct R' R (M.obj (op T')) ≃ₗ[R] M.obj (op T) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R R) eM ≪≫ₗ eBC ≪≫ₗ eN.symm
  have key : ∀ x, (affineSectionFunctor B F R' f').map gA.op.op (eM x) =
      eN (M.map g.op x) := by
    intro x
    change F.val.map ((affineSpecOver B R' f').map gA.op).op (F.val.map isoV.inv.op x) =
      F.val.map isoU.inv.op (F.val.map g.op x)
    exact (F.val.map_comp_apply isoV.inv.op ((affineSpecOver B R' f').map gA.op).op x).symm.trans
      ((F.val.congr_map_apply hsq.symm x).trans (F.val.map_comp_apply g.op isoU.inv.op x))
  refine Stacks.PresheafOfModules.bijective_restrictionBaseChange_of_equiv M g.op etot
    fun c x ↦ ?_
  change eN.symm (c • (affineSectionFunctor B F R' f').map gA.op.op (eM x)) = _
  rw [key]
  exact (eN.symm.map_smul c _).trans (congrArg (fun y ↦ c • y) (eN.symm_apply_apply _))

end Stacks.Adequate

end
