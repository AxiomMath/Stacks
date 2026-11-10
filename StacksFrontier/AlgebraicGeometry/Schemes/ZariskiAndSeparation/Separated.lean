module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.SchemePropertiesPermanence

/-!
# Separated morphisms and affine intersections

A morphism of schemes is separated precisely when suitable affine neighbourhoods of the points
of each fibre have affine intersection and surjective multiplication map on their rings of
sections.

## Main definitions

* `AlgebraicGeometry.sectionTensorMap`: the canonical map from the tensor product of the rings
  of sections of two opens to the ring of sections of their intersection.

## Main results

* `AlgebraicGeometry.sectionTensorMap_surjective_of_isSeparated`: for a separated morphism, that
  map is surjective on compatible affine opens.
* `AlgebraicGeometry.isSeparated_of_affine_intersections`: the converse criterion.
* `AlgebraicGeometry.isAffineOpen_inf_of_isSeparated` and
  `AlgebraicGeometry.isClosedImmersion_prodLift_of_isSeparated`: **Stacks 01KW**, the
  intersection of two affine opens over a separated base is affine, and sits in their absolute
  product as a closed subscheme.

## Implementation notes

Part (1)(a) of the source is Mathlib's stronger characterization of affine diagonals,
`AlgebraicGeometry.isAffineHom_diagonal_iff`; a separated morphism has an affine diagonal. Part
(1)(b) is stated separately. In part (2) the neighbourhoods may depend on the pair of points in
a fibre, as in the source.

Both directions rest on one computation: the chart `pullback U.ι V.ι ⟶ pullback (U.ι ≫ f)
(V.ι ≫ f)` of the diagonal of `f` cut out by two opens has affine source and target when the
opens are affine over an affine open of the base, and its map on global sections identifies with
`sectionTensorMap` after transporting along canonical isomorphisms. That factorization is
isolated as `comp_chartSectionMap_eq_sectionTensorMap` and used in both directions, which keeps
the two proofs small enough to elaborate without raising any limit.

## References

* [Stacks Project, Tag 01KP](https://stacks.math.columbia.edu/tag/01KP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

add_to_stacks 01KP "part (1)(a)" AlgebraicGeometry.isAffineHom_diagonal_iff
add_to_ega "I 5.5.10" "special case" AlgebraicGeometry.isAffineHom_diagonal_iff
add_to_ega "I 5.5.6" "necessity" AlgebraicGeometry.isAffineHom_diagonal_iff
add_to_ega "III 6.6.4" "binary intersections" AlgebraicGeometry.isAffineHom_diagonal_iff

/-- The canonical multiplication map on sections of an intersection. -/
public abbrev sectionTensorMap (X : Scheme.{u}) (U V : X.Opens) :
    Γ(X, U) ⊗[ℤ] Γ(X, V) →ₐ[ℤ] Γ(X, U ⊓ V) :=
  Algebra.TensorProduct.lift
    ((X.presheaf.map (homOfLE inf_le_left).op).hom.toIntAlgHom)
    ((X.presheaf.map (homOfLE inf_le_right).op).hom.toIntAlgHom)
    (fun _ _ ↦ Commute.all _ _)

/-- The chart of the diagonal of `f` cut out by two opens of the source: the canonical map from
the fibre product of `U` and `V` over the source to their fibre product over the base. -/
private noncomputable def diagonalChart {X S : Scheme.{u}} (f : X ⟶ S) (U V : X.Opens) :
    pullback U.ι V.ι ⟶ pullback (U.ι ≫ f) (V.ι ≫ f) :=
  pullback.map U.ι V.ι (U.ι ≫ f) (V.ι ≫ f) (𝟙 U.toScheme) (𝟙 V.toScheme) f
    (by simp) (by simp)

private lemma diagonalChart_comp_fst {X S : Scheme.{u}} (f : X ⟶ S) (U V : X.Opens) :
    diagonalChart f U V ≫ pullback.fst (U.ι ≫ f) (V.ι ≫ f) = pullback.fst U.ι V.ι := by
  dsimp [diagonalChart, pullback.map]
  exact pullback.lift_fst _ _ _

private lemma diagonalChart_comp_snd {X S : Scheme.{u}} (f : X ⟶ S) (U V : X.Opens) :
    diagonalChart f U V ≫ pullback.snd (U.ι ≫ f) (V.ι ≫ f) = pullback.snd U.ι V.ι := by
  dsimp [diagonalChart, pullback.map]
  exact pullback.lift_snd _ _ _

/-- The intersection of two opens is their fibre product over the ambient scheme. -/
private noncomputable def opensInfIsoPullback {X : Scheme.{u}} (U V : X.Opens) :
    (U ⊓ V : X.Opens).toScheme ≅ pullback U.ι V.ι :=
  (isPullback_opens_inf U V).isoPullback

/-- Global sections of the chart of the diagonal, transported to sections over `U ⊓ V`. -/
private noncomputable def intersectionSectionMap {X S : Scheme.{u}} (f : X ⟶ S)
    (U V : X.Opens) :
    Γ(pullback (U.ι ≫ f) (V.ι ≫ f), ⊤) ⟶ Γ(X, U ⊓ V) :=
  (diagonalChart f U V).appTop ≫ (opensInfIsoPullback U V).hom.appTop ≫
    (U ⊓ V : X.Opens).topIso.hom

private lemma isIso_appTop_of_isIso {X Y : Scheme.{u}} (e : X ≅ Y) : IsIso e.hom.appTop :=
  ⟨⟨e.inv.appTop, by rw [← Scheme.Hom.comp_appTop]; simp,
    by rw [← Scheme.Hom.comp_appTop]; simp⟩⟩

/-- The comparison between the fibre product of two opens over an affine open of the base and
their fibre product over the base itself; it is an isomorphism because the diagonal of an open
immersion is. -/
private noncomputable def affineChartIso {X S : Scheme.{u}} (f : X ⟶ S) (U V : X.Opens)
    (W : S.Opens) (hUW : U ≤ f ⁻¹ᵁ W) (hVW : V ≤ f ⁻¹ᵁ W) :
    pullback (f.resLE W U hUW) (f.resLE W V hVW) ≅ pullback (U.ι ≫ f) (V.ι ≫ f) :=
  let m := pullback.map (f.resLE W U hUW) (f.resLE W V hVW)
    (f.resLE W U hUW ≫ W.ι) (f.resLE W V hVW ≫ W.ι) (𝟙 _) (𝟙 _) W.ι (by simp) (by simp)
  haveI : IsIso m :=
    (pullback_map_diagonal_isPullback (f.resLE W U hUW) (f.resLE W V hVW) W.ι).isIso_snd_of_isIso
  asIso m ≪≫
    pullback.congrHom (Scheme.Hom.resLE_comp_ι f hUW) (Scheme.Hom.resLE_comp_ι f hVW)

private lemma affineChartIso_inv_comp_fst {X S : Scheme.{u}} (f : X ⟶ S) (U V : X.Opens)
    (W : S.Opens) (hUW : U ≤ f ⁻¹ᵁ W) (hVW : V ≤ f ⁻¹ᵁ W) :
    (affineChartIso f U V W hUW hVW).inv ≫ pullback.fst (f.resLE W U hUW) (f.resLE W V hVW) =
      pullback.fst (U.ι ≫ f) (V.ι ≫ f) := by
  have hhom : (affineChartIso f U V W hUW hVW).hom ≫ pullback.fst (U.ι ≫ f) (V.ι ≫ f) =
      pullback.fst (f.resLE W U hUW) (f.resLE W V hVW) := by
    dsimp [affineChartIso, pullback.congrHom, pullback.map]
    rw [Category.assoc, pullback.lift_fst]
    exact pullback.lift_fst _ _ _
  rw [← hhom]
  simp

private lemma affineChartIso_inv_comp_snd {X S : Scheme.{u}} (f : X ⟶ S) (U V : X.Opens)
    (W : S.Opens) (hUW : U ≤ f ⁻¹ᵁ W) (hVW : V ≤ f ⁻¹ᵁ W) :
    (affineChartIso f U V W hUW hVW).inv ≫ pullback.snd (f.resLE W U hUW) (f.resLE W V hVW) =
      pullback.snd (U.ι ≫ f) (V.ι ≫ f) := by
  have hhom : (affineChartIso f U V W hUW hVW).hom ≫ pullback.snd (U.ι ≫ f) (V.ι ≫ f) =
      pullback.snd (f.resLE W U hUW) (f.resLE W V hVW) := by
    dsimp [affineChartIso, pullback.congrHom, pullback.map]
    rw [Category.assoc, pullback.lift_snd]
    exact pullback.lift_snd _ _ _
  rw [← hhom]
  simp

/-- The multiplication map into sections of the fibre product of two opens over an affine open
of the base. -/
private noncomputable def affineChartSectionMap {X S : Scheme.{u}} (f : X ⟶ S) (U V : X.Opens)
    (W : S.Opens) (hUW : U ≤ f ⁻¹ᵁ W) (hVW : V ≤ f ⁻¹ᵁ W) :
    Γ(X, U) ⊗[ℤ] Γ(X, V) →ₐ[ℤ] Γ(pullback (f.resLE W U hUW) (f.resLE W V hVW), ⊤) :=
  Algebra.TensorProduct.lift
    (((pullback.fst (f.resLE W U hUW) (f.resLE W V hVW)).appTop.hom.comp
      U.topIso.symm.commRingCatIsoToRingEquiv.toRingHom).toIntAlgHom)
    (((pullback.snd (f.resLE W U hUW) (f.resLE W V hVW)).appTop.hom.comp
      V.topIso.symm.commRingCatIsoToRingEquiv.toRingHom).toIntAlgHom)
    (fun _ _ ↦ Commute.all _ _)

/-- The multiplication map into sections of the fibre product of two opens over the base,
obtained from `affineChartSectionMap` through `affineChartIso`. -/
private noncomputable def chartSectionMap {X S : Scheme.{u}} (f : X ⟶ S) (U V : X.Opens)
    (W : S.Opens) (hUW : U ≤ f ⁻¹ᵁ W) (hVW : V ≤ f ⁻¹ᵁ W) :
    Γ(X, U) ⊗[ℤ] Γ(X, V) →ₐ[ℤ] Γ(pullback (U.ι ≫ f) (V.ι ≫ f), ⊤) :=
  ((affineChartIso f U V W hUW hVW).inv.appTop.hom.toIntAlgHom).comp
    (affineChartSectionMap f U V W hUW hVW)

/-- Restriction from `U` to `U ⊓ V` factors through the chart of the diagonal, for either of the
two projections. The statement is given once, with the projection supplied as data. -/
private lemma topIso_inv_comp_proj_comp_intersectionSectionMap
    {X S : Scheme.{u}} (f : X ⟶ S) (U V : X.Opens) (W : S.Opens)
    (hUW : U ≤ f ⁻¹ᵁ W) (hVW : V ≤ f ⁻¹ᵁ W)
    {T : X.Opens} (hT : (U ⊓ V : X.Opens) ≤ T)
    (p : pullback (f.resLE W U hUW) (f.resLE W V hVW) ⟶ T.toScheme)
    (hpath : (opensInfIsoPullback U V).hom ≫ diagonalChart f U V ≫
      (affineChartIso f U V W hUW hVW).inv ≫ p = X.homOfLE hT) :
    T.topIso.inv ≫ p.appTop ≫ (affineChartIso f U V W hUW hVW).inv.appTop ≫
        (diagonalChart f U V).appTop ≫ (opensInfIsoPullback U V).hom.appTop ≫
        (U ⊓ V : X.Opens).topIso.hom =
      X.presheaf.map (homOfLE hT).op := by
  have hres : T.topIso.inv ≫ (X.homOfLE hT).appTop ≫ (U ⊓ V : X.Opens).topIso.hom =
      X.presheaf.map (homOfLE hT).op := by
    have hle : (U ⊓ V : X.Opens) ≤ (𝟙 X) ⁻¹ᵁ T := hT
    have hrL : Scheme.Hom.resLE (𝟙 X) T (U ⊓ V) hle = X.homOfLE hT := by
      rw [show hle = hT from Subsingleton.elim _ _, Scheme.Hom.resLE_id]
    have hw := Arrow.w (arrowResLEAppIso (𝟙 X) T (U ⊓ V) hle).hom
    change T.topIso.hom ≫ Scheme.Hom.appLE (𝟙 X) T (U ⊓ V) hle =
      (Scheme.Hom.resLE (𝟙 X) T (U ⊓ V) hle).appTop ≫ (U ⊓ V : X.Opens).topIso.hom at hw
    have happ : Scheme.Hom.appLE (𝟙 X) T (U ⊓ V) hle =
        X.presheaf.map (homOfLE hT).op := by
      simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
      congr 1
    rw [← hrL, ← hw, ← happ]
    rw [← Category.assoc, T.topIso.inv_hom_id, Category.id_comp]
  rw [← hres, ← hpath]
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
  simp only [Category.assoc]

/-- **The factorization.** Transporting the multiplication map on the chart of the diagonal
along the canonical isomorphisms gives exactly `sectionTensorMap`. -/
private lemma comp_chartSectionMap_eq_sectionTensorMap
    {X S : Scheme.{u}} (f : X ⟶ S) (U V : X.Opens) (W : S.Opens)
    (hUW : U ≤ f ⁻¹ᵁ W) (hVW : V ≤ f ⁻¹ᵁ W) :
    ((intersectionSectionMap f U V).hom.toIntAlgHom).comp
        (chartSectionMap f U V W hUW hVW) = sectionTensorMap X U V := by
  have hpathL : (opensInfIsoPullback U V).hom ≫ diagonalChart f U V ≫
      (affineChartIso f U V W hUW hVW).inv ≫
        pullback.fst (f.resLE W U hUW) (f.resLE W V hVW) =
      X.homOfLE (inf_le_left : (U ⊓ V : X.Opens) ≤ U) := by
    rw [affineChartIso_inv_comp_fst, diagonalChart_comp_fst]
    exact (isPullback_opens_inf U V).isoPullback_hom_fst
  have hpathR : (opensInfIsoPullback U V).hom ≫ diagonalChart f U V ≫
      (affineChartIso f U V W hUW hVW).inv ≫
        pullback.snd (f.resLE W U hUW) (f.resLE W V hVW) =
      X.homOfLE (inf_le_right : (U ⊓ V : X.Opens) ≤ V) := by
    rw [affineChartIso_inv_comp_snd, diagonalChart_comp_snd]
    exact (isPullback_opens_inf U V).isoPullback_hom_snd
  have hLmap := topIso_inv_comp_proj_comp_intersectionSectionMap f U V W hUW hVW
    (inf_le_left : (U ⊓ V : X.Opens) ≤ U) _ hpathL
  have hRmap := topIso_inv_comp_proj_comp_intersectionSectionMap f U V W hUW hVW
    (inf_le_right : (U ⊓ V : X.Opens) ≤ V) _ hpathR
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ hz₁ hz₂ => rw [map_add, map_add, hz₁, hz₂]
  | tmul a b =>
    have hla := congrArg (fun k : Γ(X, U) ⟶ Γ(X, U ⊓ V) => k.hom a) hLmap
    have hra := congrArg (fun k : Γ(X, V) ⟶ Γ(X, U ⊓ V) => k.hom b) hRmap
    simp only [ConcreteCategory.comp_apply] at hla hra
    simp [chartSectionMap, affineChartSectionMap, intersectionSectionMap, hla, hra,
      -Scheme.Opens.topIso_hom, -Scheme.Opens.topIso_inv]

/-- Surjectivity of the map on sections of the chart of the diagonal, deduced from surjectivity
of `sectionTensorMap`. -/
private lemma surjective_diagonalChart_appTop_of_sectionTensorMap_surjective
    {X S : Scheme.{u}} (f : X ⟶ S) (U V : X.Opens) (W : S.Opens)
    (hUW : U ≤ f ⁻¹ᵁ W) (hVW : V ≤ f ⁻¹ᵁ W)
    (hsec : Function.Surjective (sectionTensorMap X U V)) :
    Function.Surjective (diagonalChart f U V).appTop := by
  have hfac := comp_chartSectionMap_eq_sectionTensorMap f U V W hUW hVW
  have hκ : Function.Surjective (intersectionSectionMap f U V).hom := by
    intro y
    obtain ⟨z, hz⟩ := hsec y
    exact ⟨chartSectionMap f U V W hUW hVW z,
      (congrArg (fun g => g z) hfac).trans hz⟩
  have hInf : IsIso (opensInfIsoPullback U V).hom.appTop :=
    isIso_appTop_of_isIso (opensInfIsoPullback U V)
  intro y
  obtain ⟨z, hz⟩ := hκ ((U ⊓ V : X.Opens).topIso.hom
    ((opensInfIsoPullback U V).hom.appTop y))
  refine ⟨z, ?_⟩
  have hx : (U ⊓ V : X.Opens).topIso.hom ((opensInfIsoPullback U V).hom.appTop
      ((diagonalChart f U V).appTop z)) =
      (U ⊓ V : X.Opens).topIso.hom ((opensInfIsoPullback U V).hom.appTop y) := hz
  exact (ConcreteCategory.bijective_of_isIso ((opensInfIsoPullback U V).hom.appTop)).1
    ((ConcreteCategory.bijective_of_isIso (U ⊓ V : X.Opens).topIso.hom).1 hx)

/-- On affine charts, the multiplication map into sections of the fibre product over an affine
open of the base is surjective, because that fibre product is the spectrum of a tensor
product. -/
private lemma surjective_affineChartSectionMap
    {X S : Scheme.{u}} (f : X ⟶ S) (U V : X.Opens) (W : S.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hUW : U ≤ f ⁻¹ᵁ W) (hVW : V ≤ f ⁻¹ᵁ W) :
    Function.Surjective (affineChartSectionMap f U V W hUW hVW) := by
  let u : U.toScheme ⟶ W.toScheme := f.resLE W U hUW
  let v : V.toScheme ⟶ W.toScheme := f.resLE W V hVW
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  let : IsAffine W.toScheme := hW
  let : IsAffine (pullback u v) := Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine u v
  let A := (Γ(U.toScheme, ⊤)).1
  let B := (Γ(V.toScheme, ⊤)).1
  let R := (Γ(W.toScheme, ⊤)).1
  let C := (Γ(pullback u v, ⊤)).1
  algebraize [u.appTop.hom, v.appTop.hom,
    (pullback.fst u v).appTop.hom, (pullback.snd u v).appTop.hom]
  have hcat : u.appTop ≫ (pullback.fst u v).appTop =
      v.appTop ≫ (pullback.snd u v).appTop := by
    simpa only [Scheme.Hom.comp_appTop] using
      congrArg Scheme.Hom.appTop (pullback.condition (f := u) (g := v))
  let : Algebra R C := ((pullback.fst u v).appTop.hom.comp u.appTop.hom).toAlgebra
  let : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq' (by ext r; rfl)
  let : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' (by
    ext r
    have hh := congrArg (fun k : Γ(W.toScheme, ⊤) ⟶ Γ(pullback u v, ⊤) => k.hom r) hcat
    simpa [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
      RingHom.algebraMap_toAlgebra] using hh)
  let : IsScalarTower ℤ R A :=
    IsScalarTower.of_algebraMap_eq' (by ext z; simp [RingHom.algebraMap_toAlgebra])
  let : IsScalarTower ℤ R B :=
    IsScalarTower.of_algebraMap_eq' (by ext z; simp [RingHom.algebraMap_toAlgebra])
  let : IsScalarTower ℤ R C :=
    IsScalarTower.of_algebraMap_eq' (by ext z; simp [RingHom.algebraMap_toAlgebra])
  have hpo : IsPushout u.appTop v.appTop (pullback.fst u v).appTop
      (pullback.snd u v).appTop :=
    isPushout_appTop_of_isPullback (IsPullback.of_hasPullback u v)
  let : Algebra.IsPushout R A B C := (CommRingCat.isPushout_iff_isPushout).mp hpo
  let ePush := Algebra.IsPushout.equiv R A B C
  let ψ : A ⊗[ℤ] B →ₐ[ℤ] C := Algebra.TensorProduct.lift
    (pullback.fst u v).appTop.hom.toIntAlgHom
    (pullback.snd u v).appTop.hom.toIntAlgHom
    (fun _ _ ↦ Commute.all _ _)
  have hTensorPre : ∀ z : A ⊗[R] B, ∃ x : A ⊗[ℤ] B, ψ x = ePush z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add z₁ z₂ hz₁ hz₂ =>
        obtain ⟨x₁, hx₁⟩ := hz₁
        obtain ⟨x₂, hx₂⟩ := hz₂
        exact ⟨x₁ + x₂, by simp [map_add, hx₁, hx₂]⟩
    | tmul a b =>
        refine ⟨a ⊗ₜ[ℤ] b, ?_⟩
        change ψ (a ⊗ₜ[ℤ] b) = (Algebra.IsPushout.equiv R A B C) (a ⊗ₜ[R] b)
        rw [Algebra.IsPushout.equiv_tmul]
        simp [ψ, RingHom.algebraMap_toAlgebra]
  have hψsurj : Function.Surjective ψ := by
    intro c
    obtain ⟨z, rfl⟩ := ePush.surjective c
    exact hTensorPre z
  have hpre : ∀ z : A ⊗[ℤ] B,
      ∃ y : Γ(X, U) ⊗[ℤ] Γ(X, V), affineChartSectionMap f U V W hUW hVW y = ψ z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add z₁ z₂ hz₁ hz₂ =>
        obtain ⟨y₁, hy₁⟩ := hz₁
        obtain ⟨y₂, hy₂⟩ := hz₂
        exact ⟨y₁ + y₂, by simp [hy₁, hy₂]⟩
    | tmul a b =>
        obtain ⟨a', ha'⟩ := U.topIso.symm.commRingCatIsoToRingEquiv.surjective a
        obtain ⟨b', hb'⟩ := V.topIso.symm.commRingCatIsoToRingEquiv.surjective b
        refine ⟨a' ⊗ₜ[ℤ] b', ?_⟩
        change (pullback.fst u v).appTop.hom
            (U.topIso.symm.commRingCatIsoToRingEquiv a') *
            (pullback.snd u v).appTop.hom
              (V.topIso.symm.commRingCatIsoToRingEquiv b') =
          (pullback.fst u v).appTop.hom a * (pullback.snd u v).appTop.hom b
        rw [ha', hb']
  intro c
  obtain ⟨z, hz⟩ := hψsurj c
  obtain ⟨y, hy⟩ := hpre z
  exact ⟨y, hy.trans hz⟩

/-- The fibre product of two affine opens over the base is affine when both lie over one affine
open of the base. -/
private lemma isAffine_pullback_comp_ι {X S : Scheme.{u}} (f : X ⟶ S) (U V : X.Opens)
    (W : S.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hUW : U ≤ f ⁻¹ᵁ W) (hVW : V ≤ f ⁻¹ᵁ W) : IsAffine (pullback (U.ι ≫ f) (V.ι ≫ f)) := by
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  let : IsAffine W.toScheme := hW
  let : IsAffine (pullback (f.resLE W U hUW) (f.resLE W V hVW)) :=
    Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine _ _
  exact IsAffine.of_isIso (affineChartIso f U V W hUW hVW).inv

/-- For a separated morphism, the tensor product of sections surjects onto
sections of the intersection of compatible affine opens. -/
@[stacks 01KP "part (1)(b)", ega "I 5.5.6" "necessity of generation"]
public theorem sectionTensorMap_surjective_of_isSeparated {X S : Scheme.{u}}
    (f : X ⟶ S) [IsSeparated f] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (W : S.Opens) (hW : IsAffineOpen W)
    (hUW : U ≤ f ⁻¹ᵁ W) (hVW : V ≤ f ⁻¹ᵁ W) :
    Function.Surjective (sectionTensorMap X U V) := by
  have hfac := comp_chartSectionMap_eq_sectionTensorMap f U V W hUW hVW
  have := isAffine_pullback_comp_ι f U V W hU hV hW hUW hVW
  have hInvIso : IsIso (affineChartIso f U V W hUW hVW).inv.appTop :=
    isIso_appTop_of_isIso (affineChartIso f U V W hUW hVW).symm
  have hChart : Function.Surjective (chartSectionMap f U V W hUW hVW) :=
    (ConcreteCategory.bijective_of_isIso
      ((affineChartIso f U V W hUW hVW).inv.appTop)).surjective.comp
      (surjective_affineChartSectionMap f U V W hU hV hW hUW hVW)
  have : IsClosedImmersion (diagonalChart f U V) :=
    MorphismProperty.of_isPullback (pullback_map_diagonal_isPullback U.ι V.ι f)
      (show IsClosedImmersion (pullback.diagonal f) from inferInstance)
  let : IsAffine (pullback U.ι V.ι) := isAffine_of_isAffineHom (diagonalChart f U V)
  have hInf : IsIso (opensInfIsoPullback U V).hom.appTop :=
    isIso_appTop_of_isIso (opensInfIsoPullback U V)
  have hκ : Function.Surjective (intersectionSectionMap f U V).hom :=
    (ConcreteCategory.bijective_of_isIso (U ⊓ V : X.Opens).topIso.hom).surjective.comp
      (((ConcreteCategory.bijective_of_isIso
          ((opensInfIsoPullback U V).hom.appTop)).surjective).comp
        (IsClosedImmersion.isAffine_surjective_of_isAffine
          (diagonalChart f U V) |>.2))
  exact hfac ▸ hκ.comp hChart

/-- Affine neighborhoods of every pair of points in a fiber, with affine
intersection and surjective tensor map on sections, imply separatedness. -/
@[stacks 01KP "part (2)", ega "I 5.5.6" "sufficiency"]
public theorem isSeparated_of_affine_intersections {X S : Scheme.{u}}
    (f : X ⟶ S)
    (h : ∀ x₁ x₂ : X, f.base x₁ = f.base x₂ →
      ∃ (U V : X.Opens) (W : S.Opens),
        x₁ ∈ U ∧ x₂ ∈ V ∧ IsAffineOpen U ∧ IsAffineOpen V ∧
        IsAffineOpen W ∧ U ≤ f ⁻¹ᵁ W ∧ V ≤ f ⁻¹ᵁ W ∧
        IsAffineOpen (U ⊓ V) ∧ Function.Surjective (sectionTensorMap X U V)) :
    IsSeparated f := by
  let T : Scheme.{u} := pullback f f
  have hex : ∀ z : T, ∃ (U V : X.Opens) (W : S.Opens),
      (pullback.fst f f) z ∈ U ∧ (pullback.snd f f) z ∈ V ∧
      IsAffineOpen U ∧ IsAffineOpen V ∧ IsAffineOpen W ∧
      U ≤ f ⁻¹ᵁ W ∧ V ≤ f ⁻¹ᵁ W ∧ IsAffineOpen (U ⊓ V) ∧
      Function.Surjective (sectionTensorMap X U V) := by
    intro z
    refine h _ _ ?_
    simpa [Scheme.Hom.comp_base, TopCat.coe_comp, ContinuousMap.comp_apply] using
      congrArg (fun k : T ⟶ S => k.base z) (pullback.condition (f := f) (g := f))
  choose U V W hUpt hVpt hU hV hW hUW hVW hUV hsec using hex
  let q (z : T) :
      pullback ((U z).ι ≫ f) ((V z).ι ≫ f) ⟶ T :=
    pullback.map ((U z).ι ≫ f) ((V z).ι ≫ f) f f (U z).ι (V z).ι (𝟙 S)
      (by simp) (by simp)
  let O (z : T) : T.Opens := (q z).opensRange
  have hO : iSup O = ⊤ := by
    refine le_antisymm le_top fun z _ => ?_
    change z ∈ (⨆ z, O z : T.Opens)
    simp only [Opens.mem_iSup]
    refine ⟨z, ?_⟩
    change z ∈ Set.range (q z).base
    rw [Scheme.Pullback.range_map]
    exact ⟨⟨⟨(pullback.fst f f) z, hUpt z⟩, rfl⟩,
      ⟨⟨(pullback.snd f f) z, hVpt z⟩, rfl⟩⟩
  refine ⟨IsClosedImmersion.isZariskiLocalAtTarget.of_iSup_eq_top O hO fun z => ?_⟩
  have hjSurj := surjective_diagonalChart_appTop_of_sectionTensorMap_surjective
    f (U z) (V z) (W z) (hUW z) (hVW z) (hsec z)
  let : IsAffine ((U z ⊓ V z : X.Opens)).toScheme := hUV z
  let : IsAffine (pullback (U z).ι (V z).ι) :=
    IsAffine.of_isIso (opensInfIsoPullback (U z) (V z)).inv
  have := isAffine_pullback_comp_ι f (U z) (V z) (W z) (hU z) (hV z) (hW z) (hUW z) (hVW z)
  have hj : IsClosedImmersion (diagonalChart f (U z) (V z)) :=
    IsClosedImmersion.of_surjective_of_isAffine (diagonalChart f (U z) (V z)) hjSurj
  let ePull := (pullback_map_diagonal_isPullback (U z).ι (V z).ι f).isoPullback
  let eArrow : Arrow.mk (diagonalChart f (U z) (V z)) ≅
      Arrow.mk (pullback.snd (pullback.diagonal f) (q z)) :=
    Arrow.isoMk ePull (Iso.refl _) (by simp [ePull, diagonalChart, q])
  exact (MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion)
    ((morphismRestrictOpensRange (pullback.diagonal f) (q z)).trans eArrow.symm)).mpr hj

/-! ### Intersections of affine opens over a separated base -/

/-- **Stacks 01KW.** For a separated morphism `f : X ⟶ S` over a separated scheme `S`, the
intersection of two affine opens of `X` is affine. The hypotheses make `X` separated over the
terminal scheme, so its absolute diagonal is affine. -/
@[stacks 01KW "the intersection is affine", ega "III 6.6.4" "binary intersections"]
public theorem isAffineOpen_inf_of_isSeparated {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [S.IsSeparated] {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsAffineOpen (U ⊓ V) := by
  have : X.IsSeparated := (isSeparated_iff_scheme_isSeparated f).1 ‹_›
  exact hU.inf hV

/-- **Stacks 01KW.** Under the hypotheses, `U ∩ V` is a closed subscheme of the absolute
product `U × V`, the product being taken over the terminal scheme.

The map exhibiting it is the canonical `prod.lift` of the two inclusions `U ⊓ V ⟶ U` and
`U ⊓ V ⟶ V`. It is obtained from the base change `pullback U.ι V.ι ⟶ pullback (U.ι ≫ 𝟙_)
(V.ι ≫ 𝟙_)` of the absolute diagonal of `X`, which is a closed immersion because `X` is a
separated scheme, by transporting along `(isPullback_opens_inf U V).isoPullback` on the source
and `prodIsoPullback` on the target. -/
@[stacks 01KW "closed subscheme of the absolute product"]
public theorem isClosedImmersion_prodLift_of_isSeparated {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [S.IsSeparated] (U V : X.Opens) :
    IsClosedImmersion (prod.lift (X.homOfLE (inf_le_left : U ⊓ V ≤ U))
      (X.homOfLE (inf_le_right : U ⊓ V ≤ V))) := by
  have : X.IsSeparated := (isSeparated_iff_scheme_isSeparated f).1 ‹_›
  rw [show prod.lift (X.homOfLE (inf_le_left : U ⊓ V ≤ U))
        (X.homOfLE (inf_le_right : U ⊓ V ≤ V))
      = (isPullback_opens_inf U V).isoPullback.hom ≫
        pullback.mapDesc U.ι V.ι (terminal.from X) ≫
        (prodIsoPullback U.toScheme V.toScheme ≪≫
          (pullback.congrHom (terminal.comp_from U.ι) (terminal.comp_from V.ι)).symm).inv from
    prod.hom_ext
      (by simp [pullback.mapDesc, pullback.map, pullback.congrHom])
      (by simp [pullback.mapDesc, pullback.map, pullback.congrHom])]
  rw [MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion,
    MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion]
  infer_instance

end AlgebraicGeometry

end
