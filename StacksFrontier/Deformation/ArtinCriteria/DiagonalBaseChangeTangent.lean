module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicMorphismFromAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonal
public import StacksFrontier.Deformation.Artin.RimSchlessinger.ArtinianAtlas
public import StacksFrontier.Deformation.Artin.SliceTangentSpaceAnyBase
public import StacksFrontier.Deformation.ArtinCriteria.TwoFibreProductFiniteDimensional

/-!
# Finite-dimensional tangent spaces for a base change of the diagonal

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S` satisfying (RS),
whose tangent spaces and infinitesimal automorphisms are finite dimensional (axiom `[3]` of
Section 07XJ). For an object `V` of the site locally of finite type over `S` and a 1-morphism
`y : (Sch/V)_{fppf} ⥤ 𝒳 × 𝒳`, the tangent spaces of

`𝒴 = (Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳`

are finite dimensional. This is the step "Axiom [3] for `Y` follows from Lemmas 07X1 and 07X2" of
the proof of Stacks 07Y5: the tangent spaces of `(Sch/V)_{fppf}` are finite dimensional (the
scheme case of Stacks 07X1, over any deformation base:
`Deformation.Artin.SliceTangent.finiteDimensional_artinianTangentSpace_sliceBased_anyBase`), the
infinitesimal automorphisms of `𝒳 × 𝒳` are finite dimensional (Stacks 07X2 for the product, a
2-fibre product over the final object), and Stacks 07X2 for `𝒴` bounds its tangent spaces by
these. The statement transports along any equivalence over the site, which is how it reaches the
category fibred in sets of the functor of isomorphism classes of `𝒴`.

## Main definitions

* `Deformation.Artin.HasFiniteDimensionalTangentSpacesOf`: the tangent-space half of axiom `[3]`,
  for a functor to the site; `AlgebraicGeometry.Stack.HasFiniteDimensionalTangentSpaces` is this
  predicate for the structure functor of a bundled category fibred in groupoids.
* `Deformation.Artin.HasFiniteDimensionalInfinitesimalAutomorphismsOf`: the
  infinitesimal-automorphism half of axiom `[3]`, at every point of the special fibre and for every
  choice of pushforwards.

## Main results

* `Deformation.Artin.hasFiniteDimensionalTangentSpacesOf_overMap`: the scheme case.
* `Deformation.Artin.hasFiniteDimensionalInfinitesimalAutomorphismsOf_product`.
* `Deformation.Artin.hasFiniteDimensionalTangentSpacesOf_diagonalBaseChange`: axiom `[3]` (the
  tangent half) for `𝒴`.
* `Deformation.Artin.hasFiniteDimensionalTangentSpacesOf_of_equivalenceOver`: transport along an
  equivalence over the site.
* `Deformation.Artin.hasFiniteDimensionalTangentSpacesOf_of_equivalenceOver_diagonalBaseChange`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

universe u v w v₁ w₁ v₂ w₂

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The tangent-space half of axiom `[3]`**, for a functor `p` to the big fppf site of `S`: for
every finite type field `k` over `S`, every object `x₀` over `Spec k` and the local ring of `S` at
the image point as deformation base, the tangent space of the predeformation category of `x₀` is
finite dimensional for its canonical structure. For the structure functor of a category fibred in
groupoids this is `AlgebraicGeometry.Stack.HasFiniteDimensionalTangentSpaces`. -/
public abbrev HasFiniteDimensionalTangentSpacesOf {X : Type v} [Category.{w} X]
    (p : X ⥤ BigFppfOver B S hS) : Prop :=
  ∀ (k : Type u) [Field k] (i₀ : Spec (.of k) ⟶ S) (x₀ : X)
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ = Over.mk i₀),
    LocallyOfFiniteType i₀ → QuasiCompact i₀ →
    ∀ (s : S), i₀ (IsLocalRing.closedPoint k) = s →
    ∀ (Λ : Type u) [CommRing Λ] [Algebra Λ k]
      (_hΛstalk : Λ = S.presheaf.stalk s)
      (iΛ : Spec (.of Λ) ⟶ S)
      (_hiΛ : HEq iΛ (S.fromSpecStalk s))
      (hbase : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ = i₀),
      let hx : (p ⋙ Over.post B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) :=
        hx₀.trans (congrArg Over.mk hbase.symm)
      let D := predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx
      letI : Category D.carrier := D.category
      ∀ hD : Deformation.IsDeformationCategory D.projection,
        let 𝓕 := BasedCategory.ofFunctor D.projection
        let hS2 := schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓕 hD
        letI : Fact (Deformation.IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
        letI : Fact (Deformation.SchlessingerConditionS2
          (Functor.Elements.π
            (Deformation.isomorphismClasses 𝓕 hD.predeformation.cofibered))) := ⟨hS2⟩
        let F := Deformation.isomorphismClasses 𝓕 hD.predeformation.cofibered
        let T := Deformation.artinianTangentSpace Λ k F
        letI : AddCommGroup T := Deformation.associatedTangentSpaceAddCommGroupUnlifted 𝓕
        letI : Module k T := Deformation.associatedTangentSpaceModuleUnlifted 𝓕
        FiniteDimensional k T

/-- `AlgebraicGeometry.Stack.HasFiniteDimensionalTangentSpaces` is
`Deformation.Artin.HasFiniteDimensionalTangentSpacesOf` for the structure functor. -/
theorem hasFiniteDimensionalTangentSpaces_iff
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, u + 1} (BigFppfOver B S hS)) :
    Stack.HasFiniteDimensionalTangentSpaces B S hS 𝒳 ↔
      HasFiniteDimensionalTangentSpacesOf B S hS 𝒳.val.p :=
  Iff.rfl

/-- **The infinitesimal-automorphism half of axiom `[3]`**, for a functor `p` to the big fppf site
of `S`: with the data of `Deformation.Artin.HasFiniteDimensionalTangentSpacesOf`, the
infinitesimal automorphisms of the predeformation category of `x₀` are finite dimensional at
every point of its special fibre and for every choice of pushforwards there. -/
public abbrev HasFiniteDimensionalInfinitesimalAutomorphismsOf {X : Type v} [Category.{w} X]
    (p : X ⥤ BigFppfOver B S hS) : Prop :=
  ∀ (k : Type u) [Field k] (i₀ : Spec (.of k) ⟶ S) (x₀ : X)
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ = Over.mk i₀),
    LocallyOfFiniteType i₀ → QuasiCompact i₀ →
    ∀ (s : S), i₀ (IsLocalRing.closedPoint k) = s →
    ∀ (Λ : Type u) [CommRing Λ] [Algebra Λ k]
      (_hΛstalk : Λ = S.presheaf.stalk s)
      (iΛ : Spec (.of Λ) ⟶ S)
      (_hiΛ : HEq iΛ (S.fromSpecStalk s))
      (hbase : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ = i₀),
      let hx : (p ⋙ Over.post B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) :=
        hx₀.trans (congrArg Over.mk hbase.symm)
      let D := predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx
      letI : Category D.carrier := D.category
      ∀ (hD : Deformation.IsDeformationCategory D.projection) (x : D.carrier)
        (_hx : D.projection.obj x = residueFieldObject Λ k)
        (P : ChosenPushforwardsAt D.projection x),
        letI := naturalLocalizedTangentAddCommGroup P hD.satisfiesRS
        letI := naturalLocalizedTangentModule P hD.satisfiesRS
        FiniteDimensional k (localizedAutomorphismFunctorTangent P)

/-! ### The scheme case -/

/-- **The tangent spaces of `(Sch/V)_{fppf}` are finite dimensional, over any deformation base**,
for `V` locally of finite type over `S`, regarded over the site through `Over.map V.hom`. This
is `Deformation.Artin.SliceTangent.finiteDimensional_artinianTangentSpace_sliceBased_anyBase`
for the slice `Over V`, transported along the iterated-slice equivalence. -/
theorem finiteDimensional_tangentModuleAt_overMap (V : BigFppfOver B S hS)
    [LocallyOfFiniteType (B.inclusion.map V.hom)]
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
    (x₀ : BigFppfOver B V.left.1 V.left.2)
    (hx₀ : (Over.map V.hom ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hD : IsDeformationCategory.{u, u, u} (predeformationCategory iΛ
      (Over.map V.hom ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    FiniteDimensional k ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
      (predeformationCategory iΛ (Over.map V.hom ⋙ Over.post B.inclusion) x₀ hx₀).projection)
      hD (FGModuleCat.of k k)) := by
  let Φ := Over.iteratedSliceBackward V
  have : Φ.IsEquivalence := inferInstanceAs (Over.iteratedSliceEquiv V).inverse.IsEquivalence
  have hess : ∀ y : Over V, ∃ (x : Over V.left) (e : y ≅ Φ.obj x),
      (Over.forget V).IsHomLift (𝟙 ((Over.forget V).obj y)) e.hom := by
    intro y
    refine ⟨(Over.iteratedSliceForward V).obj y, (Over.iteratedSliceEquiv V).unitIso.app y, ?_⟩
    have hc : (Over.forget V).obj (Φ.obj ((Over.iteratedSliceForward V).obj y)) =
        (Over.forget V).obj y := by
      change Over.mk (y.hom.left ≫ V.hom) = y.left
      rw [Over.w y.hom]
      rfl
    refine IsHomLift.of_fac' _ _ _ rfl hc ?_
    apply Over.OverMorphism.ext
    simp [Over.eqToHom_left]
    rfl
  have hy₀ := (transport_obj_eq B hS (Over.map V.hom) (Over.forget V) Φ rfl x₀).trans hx₀
  have hDY := isDeformationCategory_predeformationCategory B S hS (Over.forget V)
    (Functor.IsFiberedInGroupoids.over_forget V) (satisfiesRS_over_forget B S hS V) iΛ
    (Φ.obj x₀) hy₀ hfinite hqc
  have hT := (finiteDimensional_artinianTangentSpace_iff_tangentModuleAt hDY).mp
    (SliceTangent.finiteDimensional_artinianTangentSpace_sliceBased_anyBase hDY.predeformation
      (tangentConditionS2 hDY))
  exact (finiteDimensional_tangentModuleAt_iff_of_fullyFaithful B hS iΛ (Over.map V.hom)
    (Over.forget V) Φ rfl (Functor.IsFiberedInGroupoids.over_map V.hom)
    (Functor.IsFiberedInGroupoids.over_forget V) hess x₀ hx₀ hD hDY _).mpr hT

/-! ### The product and the base change of the diagonal -/

/-- Condition (RS) for the final object, an algebraic stack (Stacks 07WQ). -/
theorem satisfiesRS_siteIdentity :
    SatisfiesRS B S hS (𝟭 (BigFppfOver B S hS)) Functor.isFiberedInGroupoids_id :=
  satisfiesRS_of_isAlgebraicStack B S hS
    (⟨CatFiberedInGroupoids.mk (BasedCategory.ofFunctor (𝟭 (BigFppfOver B S hS)))
        Functor.isFiberedInGroupoids_id,
      Stack.isAlgebraicStack_terminal.{u, u + 1} B S hS⟩ :
      Stack.AlgebraicStacks.{u, u + 1} B S hS)

/-- Condition (RS) for `(Sch/V)_{fppf}`, an algebraic stack (Stacks 07WQ). -/
theorem satisfiesRS_overMap (V : BigFppfOver B S hS) :
    SatisfiesRS B S hS (Over.map V.hom) (Functor.IsFiberedInGroupoids.over_map V.hom) :=
  satisfiesRS_of_isAlgebraicStack B S hS
    (⟨CatFiberedInGroupoids.mk (BasedCategory.ofFunctor (Over.map V.hom))
        (Functor.IsFiberedInGroupoids.over_map V.hom),
      Stack.isAlgebraicStack_overMap.{u, u + 1} B S hS V⟩ :
      Stack.AlgebraicStacks.{u, u + 1} B S hS)

/-- Condition (RS) for `𝒳 × 𝒳`, the 2-fibre product over the final object (Stacks 07WR). -/
theorem satisfiesRS_product (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    (hRS : SatisfiesRS B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids) :
    SatisfiesRS B S hS (CatFiberedInGroupoids.product 𝒳 𝒳).val.p
      (CatFiberedInGroupoids.product 𝒳 𝒳).isFiberedInGroupoids :=
  satisfiesRS_twoFibreProductOver B S hS 𝒳.val.p (𝟭 _) 𝒳.val.p 𝒳.val.p 𝒳.val.p
    𝒳.isFiberedInGroupoids Functor.isFiberedInGroupoids_id 𝒳.isFiberedInGroupoids
    (Functor.comp_id _) (Functor.comp_id _) hRS (satisfiesRS_siteIdentity B S hS) hRS

/-- Condition (RS) for `(Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳` (Stacks 07WR). -/
theorem satisfiesRS_diagonalBaseChange
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    (hRS : SatisfiesRS B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids) (V : BigFppfOver B S hS)
    (y : BigFppfOver B V.left.1 V.left.2 ⥤ (CatFiberedInGroupoids.product 𝒳 𝒳).val.obj)
    (hy : y ⋙ (CatFiberedInGroupoids.product 𝒳 𝒳).val.p = Over.map V.hom) :
    SatisfiesRS B S hS
      (TwoFibreProductOver.structureFunctor (Over.map V.hom) 𝒳.val.p
        (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
        (Stack.diagonalBasedFunctor B S hS 𝒳).toFunctor)
      (TwoFibreProductOver.isFiberedInGroupoids (Over.map V.hom) 𝒳.val.p
        (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
        (Stack.diagonalBasedFunctor B S hS 𝒳).toFunctor
        (Functor.IsFiberedInGroupoids.over_map V.hom) 𝒳.isFiberedInGroupoids
        (CatFiberedInGroupoids.product 𝒳 𝒳).isFiberedInGroupoids hy
        (Stack.diagonalBasedFunctor B S hS 𝒳).w) :=
  satisfiesRS_twoFibreProductOver B S hS (Over.map V.hom)
    (CatFiberedInGroupoids.product 𝒳 𝒳).val.p 𝒳.val.p y
    (Stack.diagonalBasedFunctor B S hS 𝒳).toFunctor
    (Functor.IsFiberedInGroupoids.over_map V.hom)
    (CatFiberedInGroupoids.product 𝒳 𝒳).isFiberedInGroupoids 𝒳.isFiberedInGroupoids hy
    (Stack.diagonalBasedFunctor B S hS 𝒳).w (satisfiesRS_overMap B S hS V)
    (satisfiesRS_product B S hS 𝒳 hRS) hRS

/-- Finite type and quasi-compactness transfer along `Spec Λ → Spec k → S` equal to `i₀`. -/
private theorem finiteType_quasiCompact_of_comp_eq {Λ k : Type u} [CommRing Λ] [Field k]
    [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S} {i₀ : Spec (.of k) ⟶ S}
    (hbase : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ = i₀)
    (hft : LocallyOfFiniteType i₀) (hqc : QuasiCompact i₀) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) :=
  hbase ▸ ⟨hft, hqc⟩

/-- **The infinitesimal automorphisms of `𝒳 × 𝒳` are finite dimensional when those of `𝒳`
are**: the product is the 2-fibre product over the final object, so this is the injectivity of
`Inf(𝓕_{𝒳 × 𝒳}) → Inf(𝓕_𝒳) ⊕ Inf(𝓕_𝒳)` in Stacks 07X2. -/
theorem hasFiniteDimensionalInfinitesimalAutomorphismsOf_product
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    (hRS : SatisfiesRS B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (h : HasFiniteDimensionalInfinitesimalAutomorphismsOf B S hS 𝒳.val.p) :
    HasFiniteDimensionalInfinitesimalAutomorphismsOf B S hS
      (CatFiberedInGroupoids.product 𝒳 𝒳).val.p := by
  intro k _ i₀ z₀ hz₀ hft hqc s hs Λ _ _ hΛ iΛ hiΛ hbase hx D hD x hx' P
  obtain ⟨hfin, hqc'⟩ := finiteType_quasiCompact_of_comp_eq S hbase hft hqc
  exact finiteDimensional_inf_twoFibreProduct B S hS iΛ 𝒳.val.p (𝟭 _) 𝒳.val.p 𝒳.val.p
    𝒳.val.p (Functor.comp_id _) (Functor.comp_id _) 𝒳.isFiberedInGroupoids
    Functor.isFiberedInGroupoids_id 𝒳.isFiberedInGroupoids hRS (satisfiesRS_siteIdentity B S hS) hRS
    z₀ hx hfin hqc'
    (fun hX hD' x' hx'' P' => h k i₀ _ (hX.trans (congrArg Over.mk hbase)) hft hqc s hs Λ hΛ
      iΛ hiΛ hbase hD' x' hx'' P')
    (fun hZ hD' x' hx'' P' => h k i₀ _ (hZ.trans (congrArg Over.mk hbase)) hft hqc s hs Λ hΛ
      iΛ hiΛ hbase hD' x' hx'' P')
    hD x hx' P

/-- **Axiom `[3]` (the tangent half) for `(Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳`** (the step "Axiom [3]
for `Y` follows from Lemmas 07X1 and 07X2" of the proof of Stacks 07Y5). Let `𝒳` satisfy (RS)
and axiom `[3]`, let `V` be an object of the site locally of finite type over `S` and
`y : (Sch/V)_{fppf} ⥤ 𝒳 × 𝒳` a 1-morphism over the site. Then the tangent spaces of the 2-fibre
product of `y` and the diagonal are finite dimensional. -/
theorem hasFiniteDimensionalTangentSpacesOf_diagonalBaseChange
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    (hRS : SatisfiesRS B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (hT : HasFiniteDimensionalTangentSpacesOf B S hS 𝒳.val.p)
    (hInf : HasFiniteDimensionalInfinitesimalAutomorphismsOf B S hS 𝒳.val.p)
    (V : BigFppfOver B S hS) [LocallyOfFiniteType (B.inclusion.map V.hom)]
    (y : BigFppfOver B V.left.1 V.left.2 ⥤ (CatFiberedInGroupoids.product 𝒳 𝒳).val.obj)
    (hy : y ⋙ (CatFiberedInGroupoids.product 𝒳 𝒳).val.p = Over.map V.hom) :
    HasFiniteDimensionalTangentSpacesOf B S hS
      (TwoFibreProductOver.structureFunctor (Over.map V.hom) 𝒳.val.p
        (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
        (Stack.diagonalBasedFunctor B S hS 𝒳).toFunctor) := by
  intro k _ i₀ w₀ hw₀ hft hqc s hs Λ _ _ hΛ iΛ hiΛ hbase hx D hD
  obtain ⟨hfin, hqc'⟩ := finiteType_quasiCompact_of_comp_eq S hbase hft hqc
  exact (finiteDimensional_artinianTangentSpace_iff_tangentModuleAt hD).mpr
    (finiteDimensional_tangentModuleAt_twoFibreProduct B S hS iΛ (Over.map V.hom)
      (CatFiberedInGroupoids.product 𝒳 𝒳).val.p 𝒳.val.p y
      (Stack.diagonalBasedFunctor B S hS 𝒳).toFunctor w₀ hx hy
      (Stack.diagonalBasedFunctor B S hS 𝒳).w (Functor.IsFiberedInGroupoids.over_map V.hom)
      (CatFiberedInGroupoids.product 𝒳 𝒳).isFiberedInGroupoids 𝒳.isFiberedInGroupoids
      (satisfiesRS_overMap B S hS V) (satisfiesRS_product B S hS 𝒳 hRS) hRS hfin hqc'
      (fun hX hD' => finiteDimensional_tangentModuleAt_overMap B S hS V iΛ _ hX hfin hqc' hD')
      (fun hZ hD' => (finiteDimensional_artinianTangentSpace_iff_tangentModuleAt hD').mp
        (hT k i₀ _ (hZ.trans (congrArg Over.mk hbase)) hft hqc s hs Λ hΛ iΛ hiΛ hbase hD'))
      (fun hY hD' x hx' P => hasFiniteDimensionalInfinitesimalAutomorphismsOf_product B S hS 𝒳
        hRS hInf k i₀ _ (hY.trans (congrArg Over.mk hbase)) hft hqc s hs Λ hΛ iΛ hiΛ hbase hD'
        x hx' P)
      hD)

/-! ### Transport along an equivalence over the site -/

/-- **The tangent-space half of axiom `[3]` transports along an equivalence over the site**: if
`P` satisfies (RS) and has finite-dimensional tangent spaces and `Q` is equivalent to `P` over
the big fppf site, then `Q` has finite-dimensional tangent spaces. -/
theorem hasFiniteDimensionalTangentSpacesOf_of_equivalenceOver
    {X₁ : Type v₁} [Category.{w₁} X₁] {X₂ : Type v₂} [Category.{w₂} X₂]
    {P : X₁ ⥤ BigFppfOver B S hS} {Q : X₂ ⥤ BigFppfOver B S hS}
    (hP : P.IsFiberedInGroupoids) (hQ : Q.IsFiberedInGroupoids)
    (hRS : SatisfiesRS B S hS P hP)
    (e : StacksRepresentableCFG.EquivalenceOver (𝒞 := BigFppfOver B S hS) P Q)
    (h : HasFiniteDimensionalTangentSpacesOf B S hS P) :
    HasFiniteDimensionalTangentSpacesOf B S hS Q := by
  intro k _ i₀ x₀ hx₀ hft hqc s hs Λ _ _ hΛ iΛ hiΛ hbase hx D hD
  obtain ⟨hfin, hqc'⟩ := finiteType_quasiCompact_of_comp_eq S hbase hft hqc
  have : e.inv.functor.IsEquivalence := e.toEquivalence.isEquivalence_inverse
  have hess : ∀ y : X₁, ∃ (x : X₂) (f : y ≅ e.inv.functor.obj x),
      P.IsHomLift (𝟙 (P.obj y)) f.hom :=
    fun y => ⟨e.hom.functor.obj y, e.unitIso.app y, e.isHomLift_unitIso_hom_app y⟩
  have hy₀ := (transport_obj_eq B hS Q P e.inv.functor e.inv.w x₀).trans hx
  have hDY := isDeformationCategory_predeformationCategory B S hS P hP hRS iΛ
    (e.inv.functor.obj x₀) hy₀ hfin hqc'
  have hTY := (finiteDimensional_artinianTangentSpace_iff_tangentModuleAt hDY).mp
    (h k i₀ (e.inv.functor.obj x₀) (hy₀.trans (congrArg Over.mk hbase)) hft hqc s hs Λ hΛ iΛ
      hiΛ hbase hDY)
  exact (finiteDimensional_artinianTangentSpace_iff_tangentModuleAt hD).mpr
    ((finiteDimensional_tangentModuleAt_iff_of_fullyFaithful B hS iΛ Q P e.inv.functor e.inv.w
      hQ hP hess x₀ hx hD hDY _).mpr hTY)

/-- **Axiom `[3]` (the tangent half) for a category equivalent to
`(Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳`** — for instance the category fibred in sets of its functor of
isomorphism classes. This is axiom `[3]` for the functor `Y` in the proof of Stacks 07Y5. -/
theorem hasFiniteDimensionalTangentSpacesOf_of_equivalenceOver_diagonalBaseChange
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    (hRS : SatisfiesRS B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (hT : HasFiniteDimensionalTangentSpacesOf B S hS 𝒳.val.p)
    (hInf : HasFiniteDimensionalInfinitesimalAutomorphismsOf B S hS 𝒳.val.p)
    (V : BigFppfOver B S hS) [LocallyOfFiniteType (B.inclusion.map V.hom)]
    (y : BigFppfOver B V.left.1 V.left.2 ⥤ (CatFiberedInGroupoids.product 𝒳 𝒳).val.obj)
    (hy : y ⋙ (CatFiberedInGroupoids.product 𝒳 𝒳).val.p = Over.map V.hom)
    {X₂ : Type v₂} [Category.{w₂} X₂] {Q : X₂ ⥤ BigFppfOver B S hS}
    (hQ : Q.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver (𝒞 := BigFppfOver B S hS)
      (TwoFibreProductOver.structureFunctor (Over.map V.hom) 𝒳.val.p
        (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
        (Stack.diagonalBasedFunctor B S hS 𝒳).toFunctor) Q) :
    HasFiniteDimensionalTangentSpacesOf B S hS Q :=
  hasFiniteDimensionalTangentSpacesOf_of_equivalenceOver B S hS
    (TwoFibreProductOver.isFiberedInGroupoids (Over.map V.hom) 𝒳.val.p
      (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
      (Stack.diagonalBasedFunctor B S hS 𝒳).toFunctor
      (Functor.IsFiberedInGroupoids.over_map V.hom) 𝒳.isFiberedInGroupoids
      (CatFiberedInGroupoids.product 𝒳 𝒳).isFiberedInGroupoids hy
      (Stack.diagonalBasedFunctor B S hS 𝒳).w) hQ
    (satisfiesRS_diagonalBaseChange B S hS 𝒳 hRS V y hy) e
    (hasFiniteDimensionalTangentSpacesOf_diagonalBaseChange B S hS 𝒳 hRS hT hInf V y hy)

end Deformation.Artin

end
