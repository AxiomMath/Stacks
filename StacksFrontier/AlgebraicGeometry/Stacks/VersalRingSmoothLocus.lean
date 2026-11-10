module

public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocusSchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRingFieldExtension
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRingExistence
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.StalkFormallySmoothNAdic
public import StacksFrontier.RingTheory.FormallySmooth.CompleteLocalTransfer
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRingFlatChartPoint
public import StacksFrontier.Deformation.Smooth.Unobstructed
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Smoothness of a stack at a point and its versal rings (Stacks 0DZS)

In Situation 0DQU let `x₀ : Spec k ⟶ 𝒳` be a point with `k` of finite type over `S`, with image
`s ∈ S`, and let `A` be a versal ring to `𝒳` at `x₀`. Condition (2) of Stacks 0DZS asks that
`𝒪_{S, s} ⟶ A` be formally smooth for the `𝔪_A`-adic topology. This file proves Stacks 0DZS by
the source's argument: the condition does not depend on the versal ring (Lemma 0DQX), it is
unchanged by a finite extension of `k` (Lemma 0DQY), and at a point of a smooth chart, where the
versal ring is the completed local ring (Lemma 0DQZ), membership in the smooth locus (Lemma 0DZR)
is formal smoothness of the completed local ring over `𝒪_{S, s}` (Lemma 07VH). The equivalence
with unobstructedness is Lemma 0DZK.

## Main definitions

* `AlgebraicGeometry.Stack.IsFormallySmoothAtClosedPoint`: for a local ring `A` and a morphism
  `φ : Spec A ⟶ X`, formal smoothness of `𝒪_{X, φ(𝔪_A)} ⟶ A` for the `𝔪_A`-adic topology.
* `AlgebraicGeometry.Stack.VersalRingsFormallySmoothAt`: condition (2) of Stacks 0DZS for every
  presentation of a point and every versal ring at it.

## Main results

* `AlgebraicGeometry.Stack.versalRingsFormallySmoothAt_iff`: one versal ring suffices.
* `AlgebraicGeometry.Stack.versalRingsFormallySmoothAt_iff_of_fieldExtension`: invariance under
  a finite extension of the residue field.
* `AlgebraicGeometry.Stack.IsSmoothLocus.property_iff_of_fieldValuedPoint_hom`: membership of a
  field-valued point in the smooth locus depends only on the point of `|𝒳|` it represents.
* `AlgebraicGeometry.Stack.IsSmoothLocus.property_iff_of_smoothObject`: membership in the smooth
  locus is read on a smooth chart.
* `AlgebraicGeometry.Stack.IsSmoothLocus.property_iff_isFormallySmoothAtClosedPoint`:
  **Stacks 0DZS**, the equivalence of (1) and (2).
* `AlgebraicGeometry.Stack.isFormallySmoothAtClosedPoint_iff_isSmooth_baseProjection`:
  **Stacks 0DZS**, the equivalence of (2) and (3).
* `AlgebraicGeometry.Stack.tfae_smoothLocus_formallySmooth_unobstructed`: **Stacks 0DZS**.

## References

* [Stacks Project, Tag 0DZS](https://stacks.math.columbia.edu/tag/0DZS)
* [Stacks Project, Tag 0DQX](https://stacks.math.columbia.edu/tag/0DQX)
* [Stacks Project, Tag 0DQY](https://stacks.math.columbia.edu/tag/0DQY)
* [Stacks Project, Tag 0DZR](https://stacks.math.columbia.edu/tag/0DZR)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry.Stack

universe u w

/-! ### Formal smoothness at the closed point -/

/-- For a local ring `A` and `φ : Spec A ⟶ X`, the local homomorphism `𝒪_{X, φ(𝔪_A)} ⟶ A` is
formally smooth for the `𝔪_A`-adic topology. This is condition (2) of Stacks 0DZS. -/
abbrev IsFormallySmoothAtClosedPoint {X : Scheme.{u}} {A : Type u} [CommRing A] [IsLocalRing A]
    (φ : Spec (.of A) ⟶ X) : Prop :=
  RingHom.FormallySmoothNAdic.{u} (Scheme.stalkClosedPointTo φ).hom (maximalIdeal A)

/-- Precomposing with the spectrum of a local homomorphism `g : A ⟶ B` composes the local
homomorphism at the closed point with `g`. -/
theorem isFormallySmoothAtClosedPoint_specMap_comp_iff {X : Scheme.{u}} {A B : Type u}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (g : A →+* B) [IsLocalHom g]
    (φ : Spec (.of A) ⟶ X) :
    IsFormallySmoothAtClosedPoint (Spec.map (CommRingCat.ofHom g) ≫ φ) ↔
      RingHom.FormallySmoothNAdic.{u} (g.comp (Scheme.stalkClosedPointTo φ).hom)
        (maximalIdeal B) := by
  have : IsLocalHom (CommRingCat.ofHom g).hom := ‹IsLocalHom g›
  unfold IsFormallySmoothAtClosedPoint
  rw [stalkClosedPointTo_specMap_comp (CommRingCat.ofHom g) φ]
  exact RingHom.formallySmoothNAdic_comp_ringEquiv_iff _ (Iso.commRingCatIsoToRingEquiv _) _

/-- Adjoining formal power series variables does not change formal smoothness at the closed
point. -/
theorem isFormallySmoothAtClosedPoint_specMap_C_comp_iff {X : Scheme.{u}} {A : Type u}
    [CommRing A] [IsLocalRing A] (r : ℕ) (φ : Spec (.of A) ⟶ X) :
    IsFormallySmoothAtClosedPoint
        (Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin r) (R := A))) ≫ φ) ↔
      IsFormallySmoothAtClosedPoint φ := by
  have : IsLocalHom (MvPowerSeries.C (σ := Fin r) (R := A)) :=
    ⟨fun a ha => by simpa using MvPowerSeries.isUnit_iff_constantCoeff.mp ha⟩
  rw [isFormallySmoothAtClosedPoint_specMap_comp_iff]
  let : Algebra (X.presheaf.stalk (φ (closedPoint (CommRingCat.of A)))) A :=
    (Scheme.stalkClosedPointTo φ).hom.toAlgebra
  have h := RingHom.formallySmoothNAdic_algebraMap_mvPowerSeries_iff
    (Λ := X.presheaf.stalk (φ (closedPoint (CommRingCat.of A)))) (A := A) r
  have hC : algebraMap (X.presheaf.stalk (φ (closedPoint (CommRingCat.of A))))
      (MvPowerSeries (Fin r) A) =
        (MvPowerSeries.C (σ := Fin r) (R := A)).comp (Scheme.stalkClosedPointTo φ).hom :=
    RingHom.ext fun a => MvPowerSeries.algebraMap_apply (σ := Fin r) (A := A) (r := a)
  rw [hC] at h
  exact h.symm

/-- Precomposing with the spectrum of a local homomorphism of Noetherian complete local rings
which is formally smooth for the adic topology of the target does not change formal smoothness at
the closed point, over a locally Noetherian scheme. -/
theorem isFormallySmoothAtClosedPoint_specMap_comp_iff_of_formallySmoothNAdic
    {X : Scheme.{u}} [IsLocallyNoetherian X] {A A' : Type u}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A]
    [CommRing A'] [IsLocalRing A'] [IsNoetherianRing A'] [IsAdicComplete (maximalIdeal A') A']
    (f : A →+* A') [IsLocalHom f] (hf : RingHom.FormallySmoothNAdic.{u} f (maximalIdeal A'))
    (φ : Spec (.of A) ⟶ X) :
    IsFormallySmoothAtClosedPoint (Spec.map (CommRingCat.ofHom f) ≫ φ) ↔
      IsFormallySmoothAtClosedPoint φ := by
  rw [isFormallySmoothAtClosedPoint_specMap_comp_iff]
  set O := X.presheaf.stalk (φ (closedPoint (CommRingCat.of A)))
  let : Algebra O A := (Scheme.stalkClosedPointTo φ).hom.toAlgebra
  let : Algebra O A' := (f.comp (Scheme.stalkClosedPointTo φ).hom).toAlgebra
  let fO : A →ₐ[O] A' := { f with commutes' := fun _ => rfl }
  have : IsLocalHom fO.toRingHom := ‹IsLocalHom f›
  exact (RingHom.formallySmoothNAdic_algebraMap_iff_of_formallySmoothNAdic fO hf).symm

/-- A point `x` lies in the smooth locus of `f : X ⟶ Y`, locally of finite type over a locally
Noetherian `Y`, exactly when `Spec R ⟶ Y` through `𝒪^∧_{X, x} ≃ R` is formally smooth at the
closed point. -/
private theorem mem_smoothLocus_iff_isFormallySmoothAtClosedPoint_of_ringEquiv {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f] (x : X) {R : Type u}
    [CommRing R] [IsLocalRing R] (e : X.completedLocalRing x ≃+* R) (φ : Spec (.of R) ⟶ Y)
    (hφ : φ = Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) (X.completedLocalRing x))) ≫
        X.fromSpecStalk x ≫ f) :
    x ∈ f.smoothLocus ↔ IsFormallySmoothAtClosedPoint φ := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := Scheme.completedLocalRing_isLocal X x
  subst hφ
  exact (mem_smoothLocus_iff_formallySmoothNAdic_completedLocalRing f x).trans
    (formallySmoothNAdic_stalkClosedPointTo_specMap_ringEquiv_comp_iff e _).symm

/-! ### Condition (2) of Stacks 0DZS does not depend on the versal ring -/

variable (D : VersalSituation.{u, w})

/-- The structure morphism `Spec A ⟶ Spec Λ ⟶ S` of a complete local `Λ`-algebra. -/
abbrev versalRingToBase {Λ : Type u} [CommRing Λ] (iΛ : Spec (.of Λ) ⟶ D.S) (A : Type u)
    [CommRing A] [Algebra Λ A] : Spec (.of A) ⟶ D.S :=
  Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ

/-- Comparing algebra structures along a ring map `g` factors the structure morphism to the base
through `Spec g`. -/
private theorem versalRingToBase_eq_specMap_comp {Λ : Type u} [CommRing Λ] {A₁ A₂ : Type u}
    [CommRing A₁] [CommRing A₂] [Algebra Λ A₁] [Algebra Λ A₂] (iΛ : Spec (.of Λ) ⟶ D.S)
    (g : A₁ →+* A₂) (h : algebraMap Λ A₂ = g.comp (algebraMap Λ A₁)) :
    versalRingToBase D iΛ A₂ = Spec.map (CommRingCat.ofHom g) ≫ versalRingToBase D iΛ A₁ := by
  rw [versalRingToBase, versalRingToBase, h, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

/-- **Stacks 0DZS, independence of the versal ring.** Two versal rings at the same point, for any
two presentations of it, satisfy condition (2) of Stacks 0DZS together: by Stacks 0DQX one is
isomorphic over `S` to a formal power series ring over the other. -/
theorem isFormallySmoothAtClosedPoint_iff_of_isVersalRingAt
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k] [Algebra Λ k] [Algebra Λ' k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (iΛ' : Spec (.of Λ') ⟶ D.S) (hiΛ' : _root_.AlgebraicGeometry.IsOpenImmersion iΛ')
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₀' : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite' : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ') ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (A' : Deformation.CompleteLocalAlgCat.{u, u, u} Λ' k)
    (hA : IsVersalRingAt D iΛ hiΛ x₀ hx₀ hfinite A)
    (hA' : IsVersalRingAt D iΛ' hiΛ' x₀ hx₀' hfinite' A') :
    IsFormallySmoothAtClosedPoint (versalRingToBase D iΛ A) ↔
      IsFormallySmoothAtClosedPoint (versalRingToBase D iΛ' A') := by
  have key : ∀ {Λ₁ Λ₂ : Type u} [CommRing Λ₁] [CommRing Λ₂] [Algebra Λ₁ k] [Algebra Λ₂ k]
      (i₁ : Spec (.of Λ₁) ⟶ D.S) (i₂ : Spec (.of Λ₂) ⟶ D.S)
      (A₁ : Deformation.CompleteLocalAlgCat.{u, u, u} Λ₁ k)
      (A₂ : Deformation.CompleteLocalAlgCat.{u, u, u} Λ₂ k) (r : ℕ)
      (e : A₁ ≃+* MvPowerSeries (Fin r) A₂),
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ versalRingToBase D i₁ A₁ =
        versalRingToBase D i₂ (MvPowerSeries (Fin r) A₂) →
      (IsFormallySmoothAtClosedPoint (versalRingToBase D i₁ A₁) ↔
        IsFormallySmoothAtClosedPoint (versalRingToBase D i₂ A₂)) := by
    intro Λ₁ Λ₂ _ _ _ _ i₁ i₂ A₁ A₂ r e he
    refine (formallySmoothNAdic_stalkClosedPointTo_specMap_ringEquiv_comp_iff e
      (versalRingToBase D i₁ A₁)).symm.trans ?_
    change IsFormallySmoothAtClosedPoint (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ _) ↔ _
    rw [he, versalRingToBase_eq_specMap_comp D i₂ (MvPowerSeries.C (σ := Fin r) (R := A₂))
      (RingHom.ext fun a => MvPowerSeries.algebraMap_apply (σ := Fin r) (A := A₂) (r := a))]
    exact isFormallySmoothAtClosedPoint_specMap_C_comp_iff r _
  rcases versalRing_powerSeries_comparison D iΛ hiΛ iΛ' hiΛ' x₀ hx₀ hx₀' hfinite hfinite' A A'
      hA hA' with ⟨r, e, he⟩ | ⟨r, e, he⟩
  · exact key iΛ iΛ' A A' r e he
  · exact (key iΛ' iΛ A' A r e he).symm

/-- **Condition (2) of Stacks 0DZS at a point**, for every presentation of the point over an
affine open of `S` and every versal ring at it. -/
def VersalRingsFormallySmoothAt (x₀ : D.𝒳.val.val.obj) (k : Type u) [Field k] : Prop :=
  ∀ (Λ : Type u) [CommRing Λ] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ D.S)
    (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k),
    IsVersalRingAt D iΛ hiΛ x₀ hx₀ hfinite A →
      IsFormallySmoothAtClosedPoint (versalRingToBase D iΛ A)

/-- Condition (2) of Stacks 0DZS holds for every versal ring at a point as soon as it holds for
one. -/
theorem versalRingsFormallySmoothAt_iff
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (hA : IsVersalRingAt D iΛ hiΛ x₀ hx₀ hfinite A) :
    VersalRingsFormallySmoothAt D x₀ k ↔
      IsFormallySmoothAtClosedPoint (versalRingToBase D iΛ A) :=
  ⟨fun h => h Λ iΛ hiΛ hx₀ hfinite A hA, fun h _Λ' _ _ iΛ' hiΛ' hx₀' hfinite' A' hA' =>
    (isFormallySmoothAtClosedPoint_iff_of_isVersalRingAt D iΛ hiΛ iΛ' hiΛ' x₀ hx₀ hx₀'
      hfinite hfinite' A A' hA hA').1 h⟩

/-- **Stacks 0DZS, invariance under a finite extension of the residue field.** For a finite
extension `l/k` and the induced point `x_{l,0}`, condition (2) holds at `x₀` if and only if it
holds at `x_{l,0}`: by Stacks 0DQY a versal ring at `x₀` maps to one at `x_{l,0}` by a local
homomorphism which is formally smooth for the adic topology, and formal smoothness over `𝒪_{S,s}`
ascends and descends along it. -/
theorem versalRingsFormallySmoothAt_iff_of_fieldExtension
    {Λ k l : Type u} [CommRing Λ] [Field k] [Field l] [Algebra Λ k] [Algebra k l]
    [Algebra Λ l] [IsScalarTower Λ k l] [Module.Finite k l]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (xₗ : D.𝒳.val.val.obj)
    (hxₗ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj xₗ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
    (η : xₗ ⟶ x₀)
    (hηbase : eqToHom (congrArg Over.left hxₗ).symm ≫
      ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).map η).left ≫
      eqToHom (congrArg Over.left hx₀) = Spec.map (CommRingCat.ofHom (algebraMap k l))) :
    VersalRingsFormallySmoothAt D x₀ k ↔ VersalRingsFormallySmoothAt D xₗ l := by
  obtain ⟨A, hA⟩ := exists_isVersalRingAt D iΛ hiΛ x₀ hx₀ hfinite
  obtain ⟨A', f, hA', hloc, -, hsm⟩ :=
    exists_isVersalRingAt_fieldExtension D iΛ hiΛ x₀ hx₀ hfinite xₗ hxₗ η hηbase A hA
  rw [versalRingsFormallySmoothAt_iff D iΛ hiΛ x₀ hx₀ hfinite A hA,
    versalRingsFormallySmoothAt_iff D iΛ hiΛ xₗ hxₗ _ A' hA']
  have hcomp := versalRingToBase_eq_specMap_comp D iΛ f.toRingHom
    (RingHom.ext fun a => (f.commutes a).symm)
  have : IsLocalHom f.toRingHom := hloc
  have : IsLocallyNoetherian D.S := D.locallyNoetherian
  rw [hcomp]
  exact (isFormallySmoothAtClosedPoint_specMap_comp_iff_of_formallySmoothNAdic f.toRingHom hsm
    _).symm

/-! ### Membership of a point in the smooth locus -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The smooth locus is cut out by its points.** An object of `𝒳` lies in the smooth locus of a
1-morphism as soon as every point it sees lies in the point set of the smooth locus: the open
substack cut out by that point set is the open image of the inclusion of the smooth locus, on
which the 1-morphism is smooth, so it is contained in the smooth locus by maximality. -/
theorem IsSmoothLocus.property_of_pointsWithin {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ 𝒴} {W : OpenSubstack 𝒳} (hW : IsSmoothLocus B S hS f W) {x : 𝒳.val.val.obj}
    (hx : pointsWithin 𝒳 (W.pointSet B S hS) x) : W.property x := by
  refine hW.2 _ (isSmooth_openImage_inclusion_comp B S hS W.inclusion f
    (AlgebraicStacks.isSmooth_of_isOpenImmersion B S hS W.inclusion W.isOpenImmersion) hW.1) x ?_
  rwa [openSubstackOfPoints_property]

/-- **Membership of a field-valued point in the smooth locus depends only on its point.** For a
morphism `m : p₁ ⟶ p₂` between the objects of two field-valued points, `p₁` lies in the smooth
locus exactly when `p₂` does. -/
theorem IsSmoothLocus.property_iff_of_fieldValuedPoint_hom {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ 𝒴} {W : OpenSubstack 𝒳} (hW : IsSmoothLocus B S hS f W)
    (p₁ p₂ : FieldValuedPoint B S hS 𝒳.val.val) (m : p₁.obj ⟶ p₂.obj) :
    W.property p₁.obj ↔ W.property p₂.obj := by
  refine ⟨fun h => hW.property_of_pointsWithin fun q ψ => ?_,
    fun h => OpenSubstack.prop_of_hom B S hS W m h⟩
  have hq : pointClass B S hS 𝒳.val.val 𝒳.val.property q =
      pointClass B S hS 𝒳.val.val 𝒳.val.property p₁ := by
    rw [class_eq_class_iff_hasCommonExtension]
    refine FieldValuedPoint.hasCommonExtension_equivalence 𝒳.val.property |>.trans
      (y := p₂) ⟨q, ⟨𝟙 _⟩, ⟨ψ⟩⟩ ?_
    exact FieldValuedPoint.hasCommonExtension_equivalence 𝒳.val.property |>.symm
      ⟨p₁, ⟨𝟙 _⟩, ⟨m⟩⟩
  rw [hq]
  exact (OpenSubstack.mem_pointSet_iff B S hS W _).2 ⟨p₁, h, rfl⟩

/-- **Membership in the smooth locus over `S` is read on a smooth chart.** Let `x` be a smooth
object of `𝒳` over `U` with `U ⟶ S` locally of finite presentation, and let `τ : y ⟶ x` be a
morphism of `𝒳`. Then `y` lies in the smooth locus of `𝒳 ⟶ S` exactly when every point of the
scheme `y` lies over is mapped by `τ` into the smooth locus of `U ⟶ S`. -/
theorem IsSmoothLocus.property_iff_of_smoothObject {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {W : OpenSubstack 𝒳} (hW : IsSmoothLocus B S hS (structureMorphism B S hS 𝒳) W)
    {x : 𝒳.val.val.obj} (hx : smoothObject.{u, w} B S hS 𝒳 x)
    [LocallyOfFinitePresentation (B.inclusion.map (𝒳.val.val.p.obj x).hom)]
    {y : 𝒳.val.val.obj} (τ : y ⟶ x) :
    W.property y ↔ ∀ t : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y),
      (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map τ) t ∈
        (B.inclusion.map (𝒳.val.val.p.obj x).hom).smoothLocus := by
  set gx := objectStackMap B S hS 𝒳 x
  obtain ⟨W', hW'⟩ := exists_isSmoothLocus B S hS (gx ≫ structureMorphism B S hS 𝒳)
  have hclause := isSmoothLocus_comp_of_isSmooth B S hS hx hW hW'
  rw [comp_structureMorphism] at hW'
  let z : Over (𝒳.val.val.p.obj x) := Over.mk (𝒳.val.val.p.map τ)
  have hS1 := IsSmoothLocus.property_schemeStack_iff B S hS (𝒳.val.val.p.obj x) hW' z
  rw [hclause] at hS1
  refine Iff.trans ?_ hS1
  -- the image of `z` under `x : (Sch/U) ⟶ 𝒳` is a pullback of `x` along `p τ`, isomorphic to `y`
  have hp := 𝒳.val.isFiberedInGroupoids
  let c := Functor.TwoYoneda.chosenLift 𝒳.val.val.p hp (𝒳.val.val.p.obj x)
    (Functor.Fiber.mk (a := x) rfl) z
  change W.property y ↔ W.property c.y
  have : 𝒳.val.val.p.IsStronglyCartesian (𝒳.val.val.p.map τ) τ :=
    hp.isStronglyCartesian_homLift _ _
  let φc : c.y ⟶ x := c.φ
  have : 𝒳.val.val.p.IsStronglyCartesian (𝒳.val.val.p.map τ) φc := c.isStronglyCartesian
  have : 𝒳.val.val.p.IsHomLift (𝒳.val.val.p.map τ) τ := IsHomLift.map _ τ
  have h : 𝒳.val.val.p.map τ = 𝟙 _ ≫ 𝒳.val.val.p.map τ := (Category.id_comp _).symm
  exact ⟨OpenSubstack.prop_of_hom B S hS W
      (Functor.IsStronglyCartesian.map 𝒳.val.val.p (𝒳.val.val.p.map τ) τ h φc),
    OpenSubstack.prop_of_hom B S hS W
      (Functor.IsStronglyCartesian.map 𝒳.val.val.p (𝒳.val.val.p.map τ) φc h τ)⟩

/-! ### Stacks 0DZS -/

variable (D : VersalSituation.{u, w})

/-- **Stacks 0DZS, the equivalence of (1) and (2).** In Situation 0DQU — `𝒳` an algebraic stack
locally of finite type over a locally Noetherian scheme `S` — let `x₀ : Spec k ⟶ 𝒳` be a point with
`Spec k ⟶ S` of finite type, presented over an affine open `Spec Λ ⊆ S`, with image `s`, and let
`A` be a versal ring to `𝒳` at `x₀`. Then `x₀` lies in the smooth locus `W` of `𝒳 ⟶ S`
(Stacks 0DZR) if and only if `𝒪_{S, s} ⟶ A` is formally smooth for the `𝔪_A`-adic topology.

The proof is the source's: condition (2) does not depend on the versal ring (Stacks 0DQX) and is
unchanged by finite extensions of the residue field (Stacks 0DQY), so it may be tested at a point
of a smooth chart `U ⟶ 𝒳`, where the versal ring is `𝒪^∧_{U, u₀}` (Stacks 0DQZ); there
membership in the smooth locus of `𝒳 ⟶ S` is membership of `u₀` in the smooth locus of `U ⟶ S`
(Stacks 0DZR), which is formal smoothness of `𝒪_{S, s} ⟶ 𝒪^∧_{U, u₀}` (Stacks 07VH). -/
@[stacks 0DZS "the equivalence of (1) and (2): x₀ is in the smooth locus of 𝒳 → S iff \
𝒪_{S,s} → A is formally smooth in the 𝔪_A-adic topology"]
theorem IsSmoothLocus.property_iff_isFormallySmoothAtClosedPoint
    {W : OpenSubstack D.𝒳}
    (hW : IsSmoothLocus D.B D.S D.hS (structureMorphism D.B D.S D.hS D.𝒳) W)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (hA : IsVersalRingAt D iΛ hiΛ x₀ hx₀ hfinite A) :
    W.property x₀ ↔
      IsFormallySmoothAtClosedPoint (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) := by
  change W.property x₀ ↔ IsFormallySmoothAtClosedPoint (versalRingToBase D iΛ A)
  rw [← versalRingsFormallySmoothAt_iff D iΛ hiΛ x₀ hx₀ hfinite A hA]
  obtain ⟨l, _, _, _, _, hkl, xₗ, hxₗ, η, hη, xR, ξ, -, alg, hΛ,
    ⟨x', τ, hx'sm, hlft, u₀', hpt, e, hbase⟩, -, -, hξversal, _, _, hfin, η', hη'⟩ :=
    exists_chartPoint_closedFibre_completedLocalRing D iΛ hiΛ x₀ hx₀ hfinite
  have : IsLocallyNoetherian (D.B.inclusion.obj (D.B.obj D.hS)) := D.locallyNoetherian
  have : LocallyOfFiniteType (D.B.inclusion.map (D.𝒳.val.val.p.obj x').hom) := hlft
  -- the smooth locus of the chart at `u₀'` is read on the versal ring of the chart
  have hiff : (∀ t : (BigFppfOver.toScheme D.B D.S D.hS).obj (D.𝒳.val.val.p.obj xₗ),
      (BigFppfOver.toScheme D.B D.S D.hS).map (D.𝒳.val.val.p.map τ) t ∈
        (D.B.inclusion.map (D.𝒳.val.val.p.obj x').hom).smoothLocus) ↔
      IsFormallySmoothAtClosedPoint
        (Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ) := by
    let t₀ : (BigFppfOver.toScheme D.B D.S D.hS).obj (D.𝒳.val.val.p.obj xₗ) :=
      (eqToHom (congrArg Over.left hxₗ).symm).base (closedPoint l)
    have hL : (∀ t : (BigFppfOver.toScheme D.B D.S D.hS).obj (D.𝒳.val.val.p.obj xₗ),
        (BigFppfOver.toScheme D.B D.S D.hS).map (D.𝒳.val.val.p.map τ) t ∈
          (D.B.inclusion.map (D.𝒳.val.val.p.obj x').hom).smoothLocus) ↔
        u₀' ∈ (D.B.inclusion.map (D.𝒳.val.val.p.obj x').hom).smoothLocus :=
      ⟨fun h => hpt t₀ ▸ h t₀, fun h t => (hpt t).symm ▸ h⟩
    exact hL.trans (mem_smoothLocus_iff_isFormallySmoothAtClosedPoint_of_ringEquiv
      (D.B.inclusion.map (D.𝒳.val.val.p.obj x').hom) u₀' e _ (hΛ.trans hbase))
  -- the point `x₀` and the point `xₗ` over the finite extension
  let p₀ : FieldValuedPoint D.B D.S D.hS D.𝒳.val.val :=
    { carrier := k, base := D.𝒳.val.val.p.obj x₀, isSpec := eqToIso (congrArg Over.left hx₀),
      obj := x₀, «over» := rfl }
  let pₗ : FieldValuedPoint D.B D.S D.hS D.𝒳.val.val :=
    { carrier := l, base := D.𝒳.val.val.p.obj xₗ, isSpec := eqToIso (congrArg Over.left hxₗ),
      obj := xₗ, «over» := rfl }
  have h₁ : W.property x₀ ↔ W.property xₗ :=
    (hW.property_iff_of_fieldValuedPoint_hom pₗ p₀ η).symm
  -- read the smooth locus on the chart `x'`, and the chart on its versal ring
  have h₂ := hW.property_iff_of_smoothObject hx'sm τ
  -- the versal ring of the chart is a versal ring at the closed fibre of `ξ`
  have hξring : IsVersalRingAt D iΛ hiΛ (ξ.level 0) (ξ.basePoint Λ iΛ hΛ)
      (locallyOfFiniteType_and_quasiCompact_residueField_formalBase D ξ Λ iΛ hΛ)
      (ξ.completeLocalBase Λ) :=
    Deformation.Artin.FormalObject.exists_versalPredeformationFormalObject
      D.B D.S D.hS D.𝒳.val.val.p D.𝒳.val.property ξ Λ iΛ hΛ hξversal
  have h₃ := versalRingsFormallySmoothAt_iff D iΛ hiΛ (ξ.level 0) (ξ.basePoint Λ iΛ hΛ)
    (locallyOfFiniteType_and_quasiCompact_residueField_formalBase D ξ Λ iΛ hΛ)
    (ξ.completeLocalBase Λ) hξring
  have h₄ := versalRingsFormallySmoothAt_iff_of_fieldExtension D iΛ hiΛ (ξ.level 0)
    (ξ.basePoint Λ iΛ hΛ) (locallyOfFiniteType_and_quasiCompact_residueField_formalBase D ξ Λ iΛ hΛ)
    xₗ hxₗ η' hη'
  have h₅ := versalRingsFormallySmoothAt_iff_of_fieldExtension D iΛ hiΛ x₀ hx₀ hfinite xₗ hxₗ η hη
  rwa [h₁, h₂, h₅, ← h₄, h₃]

/-- **Stacks 0DZS, the equivalence of (2) and (3).** In Situation 0DQU let `x₀ : Spec k ⟶ 𝒳` be a
point with `Spec k ⟶ S` of finite type, presented over an affine open `Spec Λ ⊆ S` with `Λ → k`
finite (the presentation of Artin's Axioms, Section 07T2, on which the predeformation category
`𝓕_{𝒳, k, x₀}` is built), and let `A` be a versal ring to `𝒳` at `x₀`. Then `𝒪_{S, s} ⟶ A` is
formally smooth for the `𝔪_A`-adic topology if and only if `𝓕_{𝒳, k, x₀}` is unobstructed, that
is its structure functor to `𝒞_Λ` is smooth. This is Formal Deformation Theory, Lemma 0DZK,
together with the observation that `𝒪_{S, s}` is a localization of `Λ`. -/
@[stacks 0DZS "the equivalence of (2) and (3): 𝒪_{S,s} → A is formally smooth in the 𝔪_A-adic \
topology iff the predeformation category of x₀ is unobstructed", sga "7 VI 1.14" "special case"]
theorem isFormallySmoothAtClosedPoint_iff_isSmooth_baseProjection
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (hA : IsVersalRingAt D iΛ hiΛ x₀ hx₀ hfinite A) :
    IsFormallySmoothAtClosedPoint (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) ↔
      let C := Deformation.Artin.predeformationCategory iΛ
        (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀
      letI : Category C.carrier := C.category
      Deformation.IsSmooth (Deformation.baseProjection C.projection) := by
  have : IsLocallyNoetherian (Spec (.of Λ)) :=
    isLocallyNoetherian_of_isOpenImmersion iΛ
  have : IsNoetherianRing Λ :=
    (isLocallyNoetherian_Spec (R := CommRingCat.of Λ)).mp inferInstance
  let : _root_.AlgebraicGeometry.IsOpenImmersion iΛ := hiΛ
  -- `𝒪_{S, s}` is a localization of `Λ`
  obtain ⟨c, hloc, hc⟩ := exists_isLocalization_stalk_comp_stalkClosedPointTo iΛ (A := A)
  let := c.toAlgebra
  let : Algebra (D.S.presheaf.stalk ((Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ)
      (closedPoint (CommRingCat.of A)))) A :=
    (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ)).hom.toAlgebra
  have : IsScalarTower Λ (D.S.presheaf.stalk ((Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫
      iΛ) (closedPoint (CommRingCat.of A)))) A :=
    IsScalarTower.of_algebraMap_eq fun a => (congrArg (fun g => g a) hc).symm
  have hL := RingHom.formallySmoothNAdic_algebraMap_iff_of_isLocalization
    (R := Λ) (R' := D.S.presheaf.stalk ((Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ)
      (closedPoint (CommRingCat.of A)))) (A := A)
    ((maximalIdeal A).comap (algebraMap Λ A)).primeCompl (maximalIdeal A)
  change _ ↔ _ at hL
  refine hL.symm.trans ?_
  obtain ⟨ξ, rfl, hξ⟩ := hA
  exact (Deformation.isSmooth_baseProjection_iff_formallySmoothNAdic
    (Deformation.Artin.predeformationCategory_isPredeformationCategory D.B D.hS iΛ
      D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property) ξ hξ).symm

/-- **Stacks 0DZS.** In Situation 0DQU let `x₀ : Spec k ⟶ 𝒳` be a point with `Spec k ⟶ S` of finite
type, presented over an affine open `Spec Λ ⊆ S` with `Λ → k` finite, with image `s ∈ S`, and let
`A` be a versal ring to `𝒳` at `x₀`. The following are equivalent:

1. `x₀` is in the smooth locus of `𝒳 ⟶ S` (Stacks 0DZR);
2. `𝒪_{S, s} ⟶ A` is formally smooth in the `𝔪_A`-adic topology;
3. `𝓕_{𝒳, k, x₀}` is unobstructed. -/
@[stacks 0DZS]
theorem tfae_smoothLocus_formallySmooth_unobstructed
    {W : OpenSubstack D.𝒳}
    (hW : IsSmoothLocus D.B D.S D.hS (structureMorphism D.B D.S D.hS D.𝒳) W)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (hA : IsVersalRingAt D iΛ hiΛ x₀ hx₀ hfinite A) :
    List.TFAE [W.property x₀,
      IsFormallySmoothAtClosedPoint (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ),
      let C := Deformation.Artin.predeformationCategory iΛ
        (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀
      letI : Category C.carrier := C.category
      Deformation.IsSmooth (Deformation.baseProjection C.projection)] := by
  tfae_have 1 ↔ 2 := hW.property_iff_isFormallySmoothAtClosedPoint D iΛ hiΛ x₀ hx₀ hfinite A hA
  tfae_have 2 ↔ 3 :=
    isFormallySmoothAtClosedPoint_iff_isSmooth_baseProjection D iΛ hiΛ x₀ hx₀ hfinite A hA
  tfae_finish

end AlgebraicGeometry.Stack

end
