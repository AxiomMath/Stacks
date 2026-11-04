module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentabilityCriteria
public import StacksFrontier.Deformation.Artin.AlgebraicSpaceCriterion
public import StacksFrontier.Deformation.Artin.FiniteDimensional.TangentTransfer
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalSituationFiniteDimensional
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionVersalityStack
public import StacksFrontier.AlgebraicGeometry.Spaces.SizeBoundFieldPoints
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable

/-!
# A subfunctor of an algebraic space satisfying Artin's axioms (Stacks 07Y2)

Let `S` be locally Noetherian and `a : F ⟶ G` an injective transformation of functors on
`(Sch/S)_{fppf}`, with `G` an algebraic space locally of finite type over `S`. If `F` satisfies
Artin's axioms [0], [1], [2], [4] and [5] and the local rings of `S` at finite type points are
G-rings, then `F` is an algebraic space (Stacks 07Y2). The remaining inputs of Stacks 07Y1 are
inherited from `G`: the diagonal of `F` is a base change of the diagonal of `G`, axiom [3] follows
from Stacks 07X1 for `G` through a fully faithful map of predeformation categories, and the
set-theoretic condition [-1] holds for every algebraic space
(`AlgebraicGeometry.Space.exists_sizeBound_fieldPoints`).

## Main results

* `Deformation.Artin.isRepresentableByAlgebraicSpaces_diag_of_mono`: the diagonal of a
  subfunctor of an algebraic space is representable by algebraic spaces.
* `Deformation.Artin.full_mapPredeformationCategory`,
  `Deformation.Artin.faithful_mapPredeformationCategory`: a fully faithful functor over the base
  induces a fully faithful map of predeformation categories.
* `Deformation.Artin.finiteDimensional_tangentSpaceArtinian_of_injective`: axiom [3] for a
  subfunctor of an algebraic space locally of finite type.
* `Deformation.Artin.isAlgebraicSpace_of_injective_of_artinAxioms`: **Stacks 07Y2**.

## References

* [Stacks Project, Tag 07Y2](https://stacks.math.columbia.edu/tag/07Y2)
* [Stacks Project, Tag 07Y1](https://stacks.math.columbia.edu/tag/07Y1)
* [Stacks Project, Tag 07X1](https://stacks.math.columbia.edu/tag/07X1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- For a monomorphism `a : F ⟶ G` the square formed by `a`, the two diagonals and `a × a` is
cartesian: two sections of `F` with the same image in `G` are equal. -/
theorem isPullback_diag_of_mono {C : Type*} [Category C] [HasBinaryProducts C] {X Y : C}
    (a : X ⟶ Y) [Mono a] : IsPullback a (diag X) (diag Y) (prod.map a a) := by
  refine ⟨⟨by ext <;> simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => s.snd ≫ prod.fst) ?_ ?_ ?_⟩⟩
  · intro s
    have h := congrArg (· ≫ prod.fst) s.condition
    simp only [Category.assoc, diag, prod.lift_fst, Category.comp_id, prod.map_fst] at h
    simpa using h.symm
  · intro s
    have h₁ := congrArg (· ≫ prod.fst) s.condition
    have h₂ := congrArg (· ≫ prod.snd) s.condition
    simp only [Category.assoc, diag, prod.lift_fst, prod.lift_snd, Category.comp_id,
      prod.map_fst, prod.map_snd] at h₁ h₂
    have h : s.snd ≫ prod.fst = s.snd ≫ prod.snd :=
      (cancel_mono a).mp (by rw [Category.assoc, Category.assoc, ← h₁, ← h₂])
    ext
    · simp
    · simp [h]
  · intro s m _ hm
    simpa using congrArg (· ≫ prod.fst) hm

/-- **The diagonal of a subfunctor of an algebraic space is representable.** If `a : F ⟶ G` is a
monomorphism of presheaves on the big fppf site of `S` and `G` is an algebraic space, then the
diagonal of `F` is representable by algebraic spaces: it is the base change of the diagonal of
`G` along `a × a`. -/
theorem isRepresentableByAlgebraicSpaces_diag_of_mono {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G) [Mono a] (hG : IsAlgebraicSpace B S hS G) :
    Space.IsRepresentableByAlgebraicSpaces B S hS (diag F) :=
  Space.IsRepresentableByAlgebraicSpaces.of_isPullback (isPullback_diag_of_mono a)
    (Space.IsRepresentableByAlgebraicSpaces.of_relativelyRepresentable hG.diagonal_representable)

/-! ### Fully faithful maps of predeformation categories -/

section Predeformation

universe v₁ v₂ w₁ w₂

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {S' : Scheme.{u}}
  (iΛ : Spec (.of Λ) ⟶ S')
  {X : Type v₁} [Category.{w₁} X] (qX : X ⥤ Over S')
  {Y : Type v₂} [Category.{w₂} Y] (qY : Y ⥤ Over S')
  (Φ : X ⥤ Y) (hΦ : Φ ⋙ qY = qX) (x₀ : X)
  (hx₀ : qX.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))

/-- The spectrum of an arrow of `𝒞_Λ` conjugated by equalities of its endpoints is the spectrum of
the arrow conjugated by the corresponding equalities of spectra. -/
theorem spec_map_eqToHom_comp_comp_eqToHom {A A' B B' : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (hA : A = A') (hB : B = B') (r : A ⟶ B) :
    Spec.map (CommRingCat.ofHom (eqToHom hA.symm ≫ r ≫ eqToHom hB : A' ⟶ B').hom.toRingHom) =
      eqToHom (congrArg (fun C : ArtinianLocalAlgCat.{u, u, u} Λ k => Spec (CommRingCat.of C))
          hB.symm) ≫
        Spec.map (CommRingCat.ofHom r.hom.toRingHom) ≫
          eqToHom (congrArg (fun C : ArtinianLocalAlgCat.{u, u, u} Λ k =>
            Spec (CommRingCat.of C)) hA) := by
  subst hA hB
  simp

include hΦ in
/-- **A faithful functor over the base induces a faithful map of predeformation categories.** A
morphism of deformations is determined by its arrow of `𝒞_Λ`, which the induced map preserves,
and by its reversed arrow, whose image under `Φ` the induced map records. -/
theorem faithful_mapPredeformationCategory [Φ.Faithful] :
    (mapPredeformationCategory iΛ qX qY Φ hΦ x₀ hx₀).toFunctor.Faithful := by
  let T := mapPredeformationCategory iΛ qX qY Φ hΦ x₀ hx₀
  let Cx := predeformationCategory iΛ qX x₀ hx₀
  let Cy := predeformationCategory iΛ qY (Φ.obj x₀) (imageBasePoint (qY := qY) iΛ qX Φ hΦ x₀ hx₀)
  let := Cx.category
  let := Cy.category
  refine ⟨fun {a b} f g h => ?_⟩
  apply (Cx.morphisms a b).injective
  apply DeformationMorphism.ext_of_components
  · rw [← Cx.morphism_projection f, ← Cx.morphism_projection g,
      Functor.congr_hom T.projection_comm.symm f, Functor.congr_hom T.projection_comm.symm g]
    simp only [Functor.comp_map]
    change _ ≫ (_ ≫ Cy.projection.map (T.toFunctor.map f) ≫ _) ≫ _ =
      _ ≫ (_ ≫ Cy.projection.map (T.toFunctor.map g) ≫ _) ≫ _
    rw [h]
  · apply Φ.map_injective
    have hf := T.morphism_arrow f
    have hg := T.morphism_arrow g
    change _ = eqToHom _ ≫ Φ.map (Cx.morphisms a b f).arrow ≫ eqToHom _ at hf
    rw [show T.toFunctor.map f = T.toFunctor.map g from h] at hf
    have h' := hf.symm.trans hg
    rwa [cancel_epi, cancel_mono] at h'

include hΦ in
/-- **A fully faithful functor over the base induces a full map of predeformation categories.** A
morphism between the images of two deformations is lifted by the preimage under `Φ` of its
reversed arrow, over the same arrow of `𝒞_Λ`. -/
theorem full_mapPredeformationCategory [Φ.Full] [Φ.Faithful] :
    (mapPredeformationCategory iΛ qX qY Φ hΦ x₀ hx₀).toFunctor.Full := by
  subst hΦ
  let T := mapPredeformationCategory iΛ (Φ ⋙ qY) qY Φ rfl x₀ hx₀
  let Cx := predeformationCategory iΛ (Φ ⋙ qY) x₀ hx₀
  let Cy := predeformationCategory iΛ qY (Φ.obj x₀)
    (imageBasePoint (qY := qY) iΛ (Φ ⋙ qY) Φ rfl x₀ hx₀)
  let := Cx.category
  let := Cy.category
  have halg : ∀ a : Cx.carrier, (Cy.objects (T.toFunctor.obj a)).algebra = (Cx.objects a).algebra :=
    fun a => (Cy.object_projection (T.toFunctor.obj a)).symm.trans
      ((Functor.congr_obj T.projection_comm a).trans (Cx.object_projection a))
  refine ⟨fun {a b} g => ?_⟩
  let mg := Cy.morphisms _ _ g
  let m : DeformationMorphism iΛ (Φ ⋙ qY) x₀ hx₀ (Cx.objects a) (Cx.objects b) :=
    { ringHom := eqToHom (halg a).symm ≫ mg.ringHom ≫ eqToHom (halg b)
      arrow := Φ.preimage (eqToHom (T.object_point b).symm ≫ mg.arrow ≫
        eqToHom (T.object_point a))
      triangle := by
        apply Φ.map_injective
        have hobj (c) : Φ.map (Cx.objects c).arrow =
            (Cy.objects (T.toFunctor.obj c)).arrow ≫ eqToHom (T.object_point c) := by
          rw [T.object_arrow c]
          simp
          rfl
        rw [Φ.map_comp, Φ.map_preimage, hobj a, hobj b]
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        rw [← Category.assoc, mg.triangle]
      arrow_base := by
        rw [Functor.comp_map, Φ.map_preimage, Functor.map_comp, Functor.map_comp, eqToHom_map,
          eqToHom_map, Over.comp_left, Over.comp_left, Over.eqToHom_left, Over.eqToHom_left,
          spec_map_eqToHom_comp_comp_eqToHom (halg a) (halg b), ← mg.arrow_base]
        simp }
  refine ⟨(Cx.morphisms a b).symm m, (Cy.morphisms _ _).injective ?_⟩
  apply DeformationMorphism.ext_of_components
  · rw [← Cy.morphism_projection]
    have hc : Cy.projection.map (T.toFunctor.map ((Cx.morphisms a b).symm m)) =
        eqToHom (Functor.congr_obj T.projection_comm a) ≫
          Cx.projection.map ((Cx.morphisms a b).symm m) ≫
            eqToHom (Functor.congr_obj T.projection_comm b).symm :=
      Functor.congr_hom T.projection_comm ((Cx.morphisms a b).symm m)
    have hp : Cx.projection.map ((Cx.morphisms a b).symm m) =
        eqToHom (Cx.object_projection a) ≫ m.ringHom ≫ eqToHom (Cx.object_projection b).symm := by
      have h := Cx.morphism_projection ((Cx.morphisms a b).symm m)
      rw [Equiv.apply_symm_apply] at h
      rw [← h]
      simp
    rw [hc, hp]
    simp [m, mg]
  · rw [T.morphism_arrow, Equiv.apply_symm_apply]
    simp [m, mg]

end Predeformation

/-! ### The map of categories fibred in sets attached to an injective transformation -/

section FibredInSets

/-- Conjugating by a pair of equalities of objects and then back is the identity. -/
theorem eqToHom_comp_conj_comp_eqToHom {C : Type*} [Category C] {X X' Y Y' : C} (hx : X = X')
    (hy : Y = Y') (g : X ⟶ Y) :
    eqToHom hx ≫ (eqToHom hx.symm ≫ g ≫ eqToHom hy) ≫ eqToHom hy.symm = g := by
  subst hx hy
  simp

/-- Two arrows with the same image under `φ` have the same image under `φ ⋙ p`. -/
theorem map_eq_map_of_comp_eq {C D E : Type*} [Category C] [Category D] [Category E]
    {φ : C ⥤ D} {p : D ⥤ E} {p' : C ⥤ E} (hcomp : φ ⋙ p = p') {x y : C} {f g : x ⟶ y}
    (h : φ.map f = φ.map g) : p'.map f = p'.map g := by
  subst hcomp
  simp [h]

/-- The image under `p` of the image under `φ` of an arrow, conjugated by equalities of objects,
is the image of the arrow under `p' = φ ⋙ p`, conjugated by the induced equalities. -/
theorem map_eqToHom_comp_map_comp_eqToHom {C D E : Type*} [Category C] [Category D]
    [Category E] {φ : C ⥤ D} {p : D ⥤ E} {p' : C ⥤ E} (hcomp : φ ⋙ p = p') {x y : C}
    {X' Y' : D} (hx : φ.obj x = X') (hy : φ.obj y = Y') (hX : p.obj X' = p'.obj x)
    (hY : p.obj Y' = p'.obj y) (f : x ⟶ y) :
    p.map (eqToHom hx.symm ≫ φ.map f ≫ eqToHom hy) = eqToHom hX ≫ p'.map f ≫ eqToHom hY.symm := by
  subst hcomp hx hy
  simp

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The functor `𝒮_F ⥤ 𝒮_G` attached to a transformation `a : F ⟶ G` is faithful: morphisms of
`𝒮_F` are determined by their image in the site, which the functor preserves. -/
theorem faithful_homFunctor_associatedMap (a : F ⟶ G) :
    (CatFiberedInGroupoids.homFunctor (Stack.associatedMap B S hS a).1).Faithful :=
  ⟨fun {_ _} f g h => fibredCategory_hom_ext f g <| map_eq_map_of_comp_eq
    (CatFiberedInGroupoids.homFunctor_comp_p (Stack.associatedMap B S hS a).1) h⟩

/-- The functor `𝒮_F ⥤ 𝒮_G` attached to an injective transformation `a : F ⟶ G` is full: a
morphism between the images of `(U, x)` and `(V, y)` over `f : U ⟶ V` says `a(x) = a(F(f)(y))`,
hence `x = F(f)(y)`. -/
theorem full_homFunctor_associatedMap (a : F ⟶ G) (ha : ∀ U, Function.Injective (a.app U)) :
    (CatFiberedInGroupoids.homFunctor (Stack.associatedMap B S hS a).1).Full := by
  refine ⟨fun {x y} ψ => ?_⟩
  let φ := CatFiberedInGroupoids.homFunctor (Stack.associatedMap B S hS a).1
  have hx := Stack.associatedMap_obj B S hS a x
  have hy := Stack.associatedMap_obj B S hS a y
  let ψ' : (⟨x.base, Discrete.mk (a.app (op x.base) x.fiber.as)⟩ :
      (Stack.fibredCategory B S hS G).val.obj) ⟶
        ⟨y.base, Discrete.mk (a.app (op y.base) y.fiber.as)⟩ :=
    eqToHom hx.symm ≫ ψ ≫ eqToHom hy
  have hfib : x.fiber.as = F.map ψ'.base.op y.fiber.as :=
    ha _ <| by
      rw [NatTrans.naturality_apply]
      exact fiber_as_eq_of_hom ψ'
  let f : x ⟶ y := ⟨ψ'.base, Discrete.eqToHom hfib⟩
  have key : eqToHom hx.symm ≫ φ.map f ≫ eqToHom hy = ψ' :=
    fibredCategory_hom_ext _ _ <| (map_eqToHom_comp_map_comp_eqToHom
      (CatFiberedInGroupoids.homFunctor_comp_p (Stack.associatedMap B S hS a).1) hx hy rfl rfl
        f).trans (by simp; rfl)
  refine ⟨f, ?_⟩
  rw [← eqToHom_comp_conj_comp_eqToHom hx hy (φ.map f), key]
  exact eqToHom_comp_conj_comp_eqToHom hx hy ψ

end FibredInSets

/-! ### Axiom [3] for a subfunctor of an algebraic space -/

/-- **Axiom [3] passes to a subfunctor of an algebraic space locally of finite type.** Let
`a : F ⟶ G` be injective, with `G` an algebraic space locally of finite type over the locally
Noetherian scheme `S`. For a field `k` of finite type over `S`, an affine open `Spec Λ ⊆ S`
through which `Spec k ⟶ S` factors with `Λ → k` finite, and an object `x₀` of `𝒮_F` over
`Spec k`, the tangent space of the deformation category `𝓕_{𝒮_F,k,x₀}` is finite-dimensional:
`a` induces a fully faithful map to `𝓕_{𝒮_G,k,a(x₀)}`, whose tangent space is finite-dimensional
by Stacks 07X1 for the algebraic stack `𝒮_G` (in the form of Stacks 0DQW), and a fully faithful map
of deformation categories is injective on tangent spaces. -/
theorem finiteDimensional_tangentSpaceArtinian_of_injective [IsLocallyNoetherian S]
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    (ha : ∀ U, Function.Injective (a.app U)) (hG : IsAlgebraicSpace B S hS G)
    (hGft : Space.IsLocallyOfFiniteType B S hS (terminal.from G)) :
    ∀ {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
      (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ]
      (x₀ : (Stack.fibredCategory B S hS F).val.obj)
      (hx₀ : ((Stack.fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)),
      LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) →
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) →
      letI := (predeformationCategory iΛ ((Stack.fibredCategory B S hS F).val.p ⋙
        Over.post B.inclusion) x₀ hx₀).category
      ∀ hD : IsDeformationCategory (predeformationCategory iΛ
          ((Stack.fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion) x₀ hx₀).projection,
        letI : Fact (IsPredeformationCategory (BasedCategory.ofFunctor
            (predeformationCategory iΛ ((Stack.fibredCategory B S hS F).val.p ⋙
              Over.post B.inclusion) x₀ hx₀).projection).p) := ⟨hD.predeformation⟩
        letI : Fact (SchlessingerConditionS2 (CategoryOfElements.π (isomorphismClasses
            (BasedCategory.ofFunctor (predeformationCategory iΛ
              ((Stack.fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion) x₀
                hx₀).projection)
            hD.predeformation.cofibered))) := ⟨tangentConditionS2 hD⟩
        FiniteDimensional k (tangentSpaceArtinian Λ k (isomorphismClasses
          (BasedCategory.ofFunctor (predeformationCategory iΛ
            ((Stack.fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion) x₀
              hx₀).projection)
          hD.predeformation.cofibered)) := by
  intro Λ k _ _ _ _ iΛ _ x₀ hx₀ hLFT hQC
  let qF := (Stack.fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion
  let qG := (Stack.fibredCategory B S hS G).val.p ⋙ Over.post B.inclusion
  let Cx := predeformationCategory iΛ qF x₀ hx₀
  let := Cx.category
  intro hD
  let D : Stack.VersalSituation.{u, u} :=
    { B := B
      S := S
      hS := hS
      𝒳 := Stack.algebraicSpaceStack.{u, u} B S hS G hG
      locallyFiniteType :=
        Stack.isLocallyOfFiniteType_structureMorphism_algebraicSpaceStack B S hS G hG hGft }
  let φ := CatFiberedInGroupoids.homFunctor (Stack.associatedMap B S hS a).1
  have hφ : φ ⋙ qG = qF := congrArg (fun H => H ⋙ Over.post B.inclusion)
    (CatFiberedInGroupoids.homFunctor_comp_p (Stack.associatedMap B S hS a).1)
  have := full_homFunctor_associatedMap a ha
  have := faithful_homFunctor_associatedMap a
  let T := mapPredeformationCategory iΛ qF qG φ hφ x₀ hx₀
  let y₀ := imageBasePoint (qY := qG) iΛ qF φ hφ x₀ hx₀
  let Cy := predeformationCategory iΛ qG (φ.obj x₀) y₀
  let := Cy.category
  obtain ⟨hDG, hTG, -⟩ := Stack.isFiniteDimensionalDeformationCategory_of_versalSituation D iΛ
    inferInstance (φ.obj x₀) y₀ ⟨hLFT, hQC⟩
  let : Fact (IsPredeformationCategory (BasedCategory.ofFunctor Cy.projection).p) :=
    ⟨hDG.predeformation⟩
  let : Fact (SchlessingerConditionS2 (CategoryOfElements.π (isomorphismClasses
      (BasedCategory.ofFunctor Cy.projection) hDG.predeformation.cofibered))) :=
    ⟨tangentConditionS2 hDG⟩
  have hTG' : FiniteDimensional k ↥(tangentModuleAt (BasedCategory.ofFunctor Cy.projection) hDG
      (FGModuleCat.of k (ULift.{u} k))) :=
    have := hTG
    (associatedTangentSpaceCarrierLinearEquiv (BasedCategory.ofFunctor Cy.projection)
      hDG.predeformation (tangentConditionS2 hDG)).symm.finiteDimensional
  have : T.toBasedFunctor.toFunctor.Full := full_mapPredeformationCategory iΛ qF qG φ hφ x₀ hx₀
  have : T.toBasedFunctor.toFunctor.Faithful :=
    faithful_mapPredeformationCategory iΛ qF qG φ hφ x₀ hx₀
  exact finiteDimensional_tangentSpaceArtinian_of_tangentModuleAt hD
    (finiteDimensional_tangentModuleAt_of_fullyFaithful hD hDG T.toBasedFunctor _ hTG')

/-! ### Stacks 07Y2 -/

/-- **Stacks 07Y2.** Let `S` be a locally Noetherian scheme and `a : F ⟶ G` a transformation of
functors `(Sch/S)_{fppf}^{opp} ⟶ Sets`. Assume that

1. `a` is injective;
2. `F` satisfies axioms [0] (`F` is an étale sheaf), [1] (`F` is limit preserving), [2]
   (condition (RS) for `F`), [4] (every formal object of `𝒮_F` is effective) and [5]
   (openness of versality for `𝒮_F`);
3. `𝒪_{S,s}` is a G-ring for every finite type point `s` of `S`;
4. `G` is an algebraic space locally of finite type over `S`.

Then `F` is an algebraic space.

As in the source, the proof applies Stacks 07Y1 to `F`: the diagonal of `F` is the base change of
the diagonal of `G` along `a × a`, hence representable; axiom [3] holds for `F` because
`a` induces fully faithful maps of predeformation categories into those of `𝒮_G`, whose tangent
spaces are finite-dimensional by Stacks 07X1; and the set-theoretic condition [-1] holds for `F`
because it holds for the algebraic space `G` and `F(U) ⟶ G(U)` is injective. -/
@[stacks 07Y2]
theorem isAlgebraicSpace_of_injective_of_artinAxioms [IsLocallyNoetherian S]
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    (ha : ∀ U, Function.Injective (a.app U))
    (hF : Presheaf.IsSheaf ((etaleTopology B).over (B.obj hS)) F)
    (hlim : LimitPreserving.{u, u, u, u, u + 1} (BigFppfOver.toScheme B S hS) F)
    (hRS : SatisfiesRSFunctor B S hS F)
    (heff : ∀ ξ : FormalObject B S hS (Stack.fibredCategory B S hS F).val.p,
      FormalObject.IsEffective B S hS (Stack.fibredCategory B S hS F).val.p
        (Stack.fibredCategory B S hS F).property ξ)
    (hopen : ∀ (U : Over S), LocallyOfFiniteType U.hom →
      ∀ (x : (Stack.fibredCategory B S hS F).val.obj)
        (hx : ((Stack.fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion).obj x = U)
        (u₀ : U.left), IsFiniteTypePoint u₀ →
        IsVersalAt U ((Stack.fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion) u₀ x hx →
        ∃ W : U.left.Opens, u₀ ∈ W.1 ∧ ∀ u : U.left, u ∈ W.1 → IsFiniteTypePoint u →
          IsVersalAt U ((Stack.fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion) u x hx)
    (hGring : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s))
    (hG : IsAlgebraicSpace B S hS G)
    (hGft : Space.IsLocallyOfFiniteType B S hS (terminal.from G)) :
    IsAlgebraicSpace B S hS F := by
  have : ∀ U, Mono (a.app U) := fun U => (mono_iff_injective _).2 (ha U)
  have : Mono a := NatTrans.mono_of_mono_app a
  have hdiag := isRepresentableByAlgebraicSpaces_diag_of_mono a hG
  have hGu : Space.IsAlgebraicSpaceULift.{u} B S hS (G ⋙ uliftFunctor.{u}) :=
    (Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS G).2 hG
  obtain ⟨T₀, hT₀⟩ := Space.exists_sizeBound_fieldPoints hGu
  refine isAlgebraicSpace_of_artinAxioms hdiag ⟨T₀, fun U k _ he hl => ?_⟩
    hF hlim hRS (finiteDimensional_tangentSpaceArtinian_of_injective a ha hG hGft) heff hopen
    hGring
  have h : #(ULift.{u} (G.obj (op U))) ≤
      Cardinal.lift.{u} ((BigFppfOver.toScheme B S hS).obj T₀).size := hT₀ U k he hl
  rw [Cardinal.mk_uLift, Cardinal.lift_id, Cardinal.lift_id] at h
  exact (Cardinal.mk_le_of_injective (ha (op U))).trans h

end Deformation.Artin

end
