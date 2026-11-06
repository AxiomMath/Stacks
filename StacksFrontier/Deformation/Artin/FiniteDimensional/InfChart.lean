module

public import StacksFrontier.Deformation.Artin.FiniteDimensional.TangentChart
public import StacksFrontier.Deformation.Artin.FiniteDimensional.SpaceChart
public import StacksFrontier.Deformation.ArtinCriteria.TangentSpace

/-!
# The infinitesimal automorphisms at a point of a category with a smooth chart

The infinitesimal automorphism half of Stacks 07X1. Let `𝒳` satisfy (RS), with a smooth
surjective chart `f : (Sch/V) ⟶ 𝒳`, `V` locally of finite type over `S`, and let `u₀` be a point
of `(Sch/V)` over a field `l` of finite type over `S`. Then the infinitesimal automorphisms of
`𝓕_{𝒳,l,f(u₀)}` are finite-dimensional over `l`.

## Main results

* `Deformation.Artin.subsingleton_localizedAutomorphismFunctorTangent_of_faithful`: a faithful
  projection has no infinitesimal automorphisms.
* `Deformation.Artin.exists_finiteDimensional_localized_of_smoothChart`: the infinitesimal
  automorphisms of `𝓕_{𝒳,l,f(u₀)}` are finite-dimensional.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Artin

attribute [local implicit_reducible]
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.mk
  CategoryTheory.Functor.Fiber.fiberInclusion

/-- In an exact pair whose first map has subsingleton source, the second map has trivial
kernel. -/
theorem eq_zero_of_exact_of_subsingleton {R M N P : Type*} {_ : Semiring R}
    {_ : AddCommMonoid M} {_ : AddCommMonoid N} {_ : AddCommMonoid P} {_ : Module R M}
    {_ : Module R N} {_ : Module R P} {g : M →ₗ[R] N} {h : N →ₗ[R] P}
    (hgh : Function.Exact g h) (hM : Subsingleton M) (y : N) (hy : h y = 0) : y = 0 := by
  obtain ⟨m, rfl⟩ := (hgh y).1 hy
  rw [Subsingleton.elim m 0, map_zero]

/-- A vector space with an injective linear map into a finite-dimensional one is
finite-dimensional. -/
theorem finiteDimensional_of_map_eq_zero {K M N : Type*} {_ : Field K} {_ : AddCommGroup M}
    {_ : Module K M} {_ : AddCommGroup N} {_ : Module K N} (g : M →ₗ[K] N)
    (hg : ∀ y, g y = 0 → y = 0) (hN : FiniteDimensional K N) : FiniteDimensional K M :=
  Module.Finite.of_injective g ((injective_iff_map_eq_zero g).2 hg)

/-- Faithfulness of a functor, in the form "arrows with the same image agree", transports along an
equality of functors. -/
theorem faithful_of_eq {C D : Type*} [Category C] [Category D] (G P : C ⥤ D) (h : G = P)
    (hP : ∀ {a b : C} (φ ψ : a ⟶ b), P.map φ = P.map ψ → φ = ψ) :
    ∀ {a b : C} (φ ψ : a ⟶ b), G.map φ = G.map ψ → φ = ψ := by
  subst h; exact hP

/-- An object of a fibre lies over the base object of the fibre. -/
theorem fiber_obj_eq {C D : Type*} [Category C] [Category D] {p : C ⥤ D} {A : D}
    (z : p.Fiber A) : p.obj z.1 = A := z.2

/-- The induced functor of predeformation categories commutes with the projections, on
objects. -/
theorem InducedPredeformationFunctor.projection_obj {Λ k : Type u} [CommRing Λ] [Field k]
    [Algebra Λ k] {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S} {X : Type*} [Category X]
    {qX : X ⥤ Over S} {Y : Type*} [Category Y] {qY : Y ⥤ Over S} {F : X ⥤ Y} {hF : F ⋙ qY = qX}
    {x₀ : X} {hx₀ : qX.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (G : InducedPredeformationFunctor iΛ qX qY F hF x₀ hx₀)
    (a : (predeformationCategory iΛ qX x₀ hx₀).carrier) :
    (predeformationCategory iΛ qY (F.obj x₀)
      (imageBasePoint (qY := qY) iΛ qX F hF x₀ hx₀)).projection.obj (G.toFunctor.obj a) =
      (predeformationCategory iΛ qX x₀ hx₀).projection.obj a :=
  Functor.congr_obj G.projection_comm a

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A faithful projection has no infinitesimal automorphisms**: the tangent space at the
identity of the automorphism functor is a subsingleton when two arrows with the same image in
`𝒞_Λ` agree. -/
theorem subsingleton_localizedAutomorphismFunctorTangent_of_faithful {Λ l : Type u} [CommRing Λ]
    [Field l] [Algebra Λ l] {C : Type*} [Category C] (pp : C ⥤ ArtinianLocalAlgCat.{u, u, u} Λ l)
    (hpp : ∀ {a b : C} (φ ψ : a ⟶ b), pp.map φ = pp.map ψ → φ = ψ) {x : C}
    (Q : ChosenPushforwardsAt pp x) :
    Subsingleton (localizedAutomorphismFunctorTangent Q) := by
  have key : ∀ {A : ArtinianLocalAlgCat.{u, u, u} Λ l} (X Y : pp.Fiber A),
      Subsingleton (X ⟶ Y) := fun {A} X Y => ⟨fun α β => by
    apply Functor.Fiber.hom_ext
    apply hpp
    have := α.2
    have := β.2
    show pp.map α.1 = pp.map β.1
    rw [IsHomLift.fac' pp (𝟙 A) α.1, IsHomLift.fac' pp (𝟙 A) β.1]⟩
  refine (localizedTangentEquivKernel Q).subsingleton_congr.mpr ⟨fun a b => ?_⟩
  exact Subtype.ext (Aut.ext (Iso.ext (Subsingleton.elim _ _)))

/-- **The projection of the deformation category of a point of `(Sch/V)` is faithful**: a
morphism of deformations of a point of a represented category is determined by its ring map. -/
theorem faithful_slice_projection (V : BigFppfOver B S hS)
    {Λ l : Type u} [CommRing Λ] [Field l] [Algebra Λ l] (iΛ : Spec (.of Λ) ⟶ S) (u₀ : Over V)
    (hu₀ : (Over.forget V ⋙ Over.post B.inclusion).obj u₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
    {a b : (predeformationCategory iΛ (Over.forget V ⋙ Over.post B.inclusion) u₀ hu₀).carrier}
    (φ ψ : a ⟶ b)
    (h : (predeformationCategory iΛ (Over.forget V ⋙ Over.post B.inclusion) u₀ hu₀).projection.map
      φ = (predeformationCategory iΛ (Over.forget V ⋙ Over.post B.inclusion) u₀
        hu₀).projection.map ψ) : φ = ψ :=
  SliceTangent.deformationMorphism_ext_of_ringHom h

/-- **The infinitesimal automorphisms of a point of a category with a smooth chart, at the level
of a point of the chart.** Let `𝒳` satisfy (RS), with a chart `f : (Sch/V) ⟶ 𝒳` as in Stacks
07X1, `V` locally of finite type over `S`, and let `u₀` be a point of `(Sch/V)` over a field `l`
of finite type over `S`. Then the infinitesimal automorphisms of `𝓕_{𝒳,l,f(u₀)}` are
finite-dimensional, at some point of its special fibre and some choice of pushforwards. -/
theorem exists_finiteDimensional_localized_of_smoothChart [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (hRS : SatisfiesRS B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (V : BigFppfOver B S hS) [LocallyOfFiniteType (B.inclusion.map V.hom)]
    (f : Stack.schemeFibredCategory B S hS V ⟶ 𝒳)
    (hf : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hprop : ∀ (W : BigFppfOver B S hS)
      (yv : BigFppfOver B W.left.1 W.left.2 ⥤ 𝒳.val.obj)
      (_hyv : yv ⋙ 𝒳.val.p = Over.map W.hom)
      (F : (BigFppfOver B W.left.1 W.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B W.left.1 W.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map W.hom) (Stack.schemeFibredCategory B S hS V).val.p
          𝒳.val.p yv (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (let h := (algebraicSpaceMap B S hS W
        ((spacesOverSmallerBaseFunctor B W.left.1 S W.left.2 hS W.hom).obj ⟨F, hF⟩)).hom
       Space.IsSurjective B S hS h ∧ Space.IsSmooth B S hS h))
    {Λ l : Type u} [CommRing Λ] [Field l] [Algebra Λ l] [Module.Finite Λ l]
    (iΛ : Spec (.of Λ) ⟶ S) (hiΛ : IsOpenImmersion iΛ) (u₀ : Over V)
    (hu₀ : (Over.forget V ⋙ Over.post B.inclusion).obj u₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
    (hxₗ : (𝒳.val.p ⋙ Over.post B.inclusion).obj ((CatFiberedInGroupoids.homFunctor f).obj u₀) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
    (hfin : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ)) :
    letI := (predeformationCategory iΛ (𝒳.val.p ⋙ Over.post B.inclusion)
      ((CatFiberedInGroupoids.homFunctor f).obj u₀) hxₗ).category
    ∃ (y : (predeformationCategory iΛ (𝒳.val.p ⋙ Over.post B.inclusion)
        ((CatFiberedInGroupoids.homFunctor f).obj u₀) hxₗ).carrier)
      (_ : (predeformationCategory iΛ (𝒳.val.p ⋙ Over.post B.inclusion)
        ((CatFiberedInGroupoids.homFunctor f).obj u₀) hxₗ).projection.obj y =
          residueFieldObject Λ l)
      (P : ChosenPushforwardsAt (predeformationCategory iΛ (𝒳.val.p ⋙ Over.post B.inclusion)
        ((CatFiberedInGroupoids.homFunctor f).obj u₀) hxₗ).projection y),
      letI := naturalLocalizedTangentAddCommGroup P
        (isDeformationCategory_predeformationCategory B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids
          hRS iΛ _ hxₗ hfin.1 hfin.2).satisfiesRS
      letI := naturalLocalizedTangentModule P
        (isDeformationCategory_predeformationCategory B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids
          hRS iΛ _ hxₗ hfin.1 hfin.2).satisfiesRS
      FiniteDimensional l (localizedAutomorphismFunctorTangent P) := by
  have : IsOpenImmersion iΛ := hiΛ
  let 𝒰 := Stack.schemeFibredCategory B S hS V
  have hU : 𝒰.val.p = Over.forget V := rfl
  have hRSU : SatisfiesRS B S hS 𝒰.val.p 𝒰.isFiberedInGroupoids := satisfiesRS_over_forget B S hS V
  have hΦ := CatFiberedInGroupoids.homFunctor_comp_p f
  have hbase : 𝒳.val.p.obj ((CatFiberedInGroupoids.homFunctor f).obj u₀) = u₀.left :=
    Functor.congr_obj hΦ u₀
  let w₀ : TwoFibreProductOver 𝒰.val.p 𝒰.val.p 𝒳.val.p (CatFiberedInGroupoids.homFunctor f)
      (CatFiberedInGroupoids.homFunctor f) :=
    ⟨u₀.left, u₀, u₀, rfl, rfl, Iso.refl _, by
      show 𝒳.val.p.IsHomLift (𝟙 u₀.left) (𝟙 ((CatFiberedInGroupoids.homFunctor f).obj u₀))
      rw [← hbase]; infer_instance⟩
  have hw₀ : (TwoFibreProductOver.structureFunctor 𝒰.val.p 𝒰.val.p 𝒳.val.p
      (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor f) ⋙
        Over.post B.inclusion).obj w₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ) := hu₀
  obtain ⟨-, -, hex, -, -⟩ := sixTermExact_twoFibreProduct B S hS iΛ 𝒰.val.p 𝒳.val.p 𝒰.val.p
    (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor f) hΦ hΦ
    𝒰.isFiberedInGroupoids 𝒳.isFiberedInGroupoids 𝒰.isFiberedInGroupoids hRSU hRS hRSU
    w₀ hw₀ hfin.1 hfin.2
  have hinj := eq_zero_of_exact_of_subsingleton hex ?sub
  case sub =>
    refine @instSubsingletonProd _ _
      (subsingleton_localizedAutomorphismFunctorTangent_of_faithful _ ?f1 _)
      (subsingleton_localizedAutomorphismFunctorTangent_of_faithful _ ?f2 _)
    · exact faithful_of_eq _ _ (InducedPredeformationFunctor.projection_comm _)
        (faithful_slice_projection V iΛ u₀ hu₀)
    · exact faithful_of_eq _ _ (PredeformationFibreProductData.rightFunctor_projection _)
        (faithful_slice_projection V iΛ u₀ hu₀)
  let Q := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f f
  have hQ : Bicategory.IsTwoFibreProduct Q :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f f
  have hR : Stack.IsRepresentableByAlgebraicSpace B S hS Q.pt :=
    Stack.isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS _ _ _ f f Q hQ
      hf (Stack.isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V)
  have hfsm : Stack.HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.smoothMorphismProperty B S hS) f hf :=
    fun W y hy F hF he => (hprop W y hy F hF he).2
  have hπ : Stack.IsRelativelySmooth B S hS Q.fst :=
    ⟨Stack.isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ f f Q hQ hf,
      Stack.hasRelativeProperty_baseChange.{u, u, u + 1, u + 1} B S hS _ _ _ _ f f Q hQ hf hfsm⟩
  obtain ⟨W, hW, k, hk, hkS, hkM⟩ :=
    Stack.exists_smoothChart_of_isRepresentableByAlgebraicSpace Q.pt hR V Q.fst hπ
  have hRSR : SatisfiesRS B S hS Q.pt.val.p Q.pt.isFiberedInGroupoids :=
    satisfiesRS_twoFibreProductOver B S hS 𝒰.val.p 𝒳.val.p 𝒰.val.p
      (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor f)
      𝒰.isFiberedInGroupoids 𝒳.isFiberedInGroupoids 𝒰.isFiberedInGroupoids hΦ hΦ hRSU hRS hRSU
  have hT := finiteDimensional_tangentModuleAt_of_smoothChart Q.pt hRSR W k hk
    (fun W' y hy G hG he => ⟨hkS W' y hy G hG he, hkM W' y hy G hG he⟩) iΛ hiΛ w₀ hw₀ hfin
  have hT' := (finiteDimensional_tangentModuleAt_uLift_iff _).mpr hT
  refine ⟨_, ?_, _, finiteDimensional_of_map_eq_zero _ hinj hT'⟩
  refine (InducedPredeformationFunctor.projection_obj _ _).trans ?_
  dsimp only
  refine (InducedPredeformationFunctor.projection_obj _ _).trans ?_
  exact fiber_obj_eq _

end Deformation.Artin
