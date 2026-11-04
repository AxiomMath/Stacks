module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRingCogroupoid
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalSituationFiniteDimensional
public import StacksFrontier.Deformation.CofiberedPresentation.Criteria
public import StacksFrontier.Deformation.CofiberedPresentation.VersalPresentation
public import StacksFrontier.Deformation.GroupoidQuotient.CompletedPresentation
public import StacksFrontier.Deformation.Formal.Groupoid.Prorepresentable
public import StacksFrontier.Deformation.Smooth.CompleteLocalAlgebra
public import StacksFrontier.Deformation.VersalRing.Uniqueness

/-!
# The presentation of the deformation category of a point of an algebraic stack (Stacks 0DR3)

In Situation 0DQU let `x₀ : Spec k ⟶ 𝒳` be a morphism with `k` a field of finite type over `S`,
and let `Spec Λ ⊆ S` be an affine open through which `Spec k ⟶ S` factors with `Λ → k` finite.
**Stacks 0DR3** observes that `𝓕 = 𝓕_{𝒳,k,x₀}` has a presentation by a smooth prorepresentable
groupoid in functors on `𝒞_Λ` (by Stacks 0DQW and Stacks 06L8), and unwinds this: there are a
versal formal object `ξ` over a Noetherian complete local `Λ`-algebra `A` with residue field `k`
and a second such algebra `B` with `B|_{𝒞_Λ} ≅ A|_{𝒞_Λ} ×_{ξ, 𝓕, ξ} A|_{𝒞_Λ}`; the two projections
are formally smooth maps `s, t : A → B`; a map `c : B → B ⊗̂_{s, A, t} B` makes `(A, B, s, t, c)`
a cogroupoid; `ξ` induces an equivalence `[A|_{𝒞_Λ} / B|_{𝒞_Λ}] → 𝓕` over `𝒞_Λ`; there is also an
equivalence `[A/B] → 𝓕^` over `𝒞^_Λ` with the completion of `𝓕`; and `A` is a versal ring to `𝒳`
at `x₀`.

## Main results

* `AlgebraicGeometry.Stack.hasSmoothPresentation_predeformationCategory`: **Stacks 0DR3**, the
  presentation of `𝓕_{𝒳,k,x₀}` by a smooth prorepresentable groupoid in functors.
* `Deformation.exists_versalCogroupoid`: the unwinding for an arbitrary category cofibered in
  groupoids over `𝒞_Λ` satisfying the three conditions of Stacks 06L8.
* `AlgebraicGeometry.Stack.exists_versalCogroupoid_predeformationCategory`: **Stacks 0DR3**, the
  unwinding for `𝓕_{𝒳,k,x₀}`.

## Implementation notes

The groupoid in functors is the one of Stacks 06KY attached to a versal formal object `ξ`
(`Deformation.versalGroupoid`): its objects are `A|_{𝒞_Λ}` and its arrows are the self `2`-fibre
product `A|_{𝒞_Λ} ×_{ξ, 𝓕, ξ} A|_{𝒞_Λ}`. Its arrow functor is prorepresentable by Stacks 06L7, and
the representable presentation on `𝒞^_Λ` is then built on the two prorepresenting algebras
themselves (`Deformation.GroupoidInFunctors.exists_representablePresentation_completion_of_isos`),
so that the algebra of objects is literally the base of `ξ`. The equivalence
`[A|_{𝒞_Λ} / B|_{𝒞_Λ}] → 𝓕` is the transport along that isomorphism of the presentation of Stacks
06L1 by the groupoid of `ξ` (`Deformation.presentationOfIsVersal`), whose functor is the quotient
morphism induced by the associated morphism `ξ̲ : A|_{𝒞_Λ} → 𝓕`. The equivalence `[A/B] → 𝓕^` is
`Deformation.RepresentablePresentation.completedPresentation`, which uses smoothness of the
groupoid.

Formal smoothness of `s` and `t` is read off Stacks 06HL (the induced morphisms of restricted
representable functors are smooth, so `B` is a power series ring over `A` along each of them) and
Stacks 0DYL over the base `A`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Opposite

namespace Deformation

universe u v w uF

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The `R`-algebra structure on the residue field `k` of a complete local algebra `R`, through
the residue identification of `R`. -/
private abbrev residueFieldAlgebraOver (R : CompleteLocalAlgCat.{u, v, w} Λ k) : Algebra R k :=
  (R.residueEquiv.toRingEquiv.toRingHom.comp (IsLocalRing.residue R)).toAlgebra

/-- The algebra `S` of a morphism `f : R ⟶ S` of complete local algebras, read as a complete
local algebra over `R`, the residue field `k` of `R` being an `R`-algebra through the residue
identification of `R`. -/
private def completeLocalOverSource {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S) :
    letI := residueFieldAlgebraOver R
    CompleteLocalAlgCat.{v, v, w} R k :=
  letI := residueFieldAlgebraOver R
  letI : Algebra R S := f.hom.toRingHom.toAlgebra
  letI : Algebra R (ResidueField S) := ((IsLocalRing.residue S).comp f.hom.toRingHom).toAlgebra
  { carrier := S
    completeLocal := S.completeLocal
    residueEquiv := AlgEquiv.ofRingEquiv (f := S.residueEquiv.toRingEquiv)
      (fun r => f.residue_comm r) }

/-- **A power series map of complete local algebras is formally smooth.** If `f : R ⟶ S`
exhibits `S` as a power series ring in finitely many variables over `R`, then `R → S` is
formally smooth for the `𝔪_S`-adic topology. This is Stacks 0DYL, (5) ⟹ (2), over the
base `R`. -/
theorem formallySmoothNAdic_of_isPowerSeriesOver {R S : CompleteLocalAlgCat.{u, v, w} Λ k}
    {f : R ⟶ S} (hf : IsPowerSeriesOver f) :
    RingHom.FormallySmoothNAdic.{v} f.hom.toRingHom (maximalIdeal S) := by
  let := residueFieldAlgebraOver R
  let : IsNoetherianRing R := R.completeLocal.isNoetherian
  have hsurj : Function.Surjective (algebraMap R k) :=
    R.residueEquiv.surjective.comp IsLocalRing.residue_surjective
  let : Module.Finite R k := Module.Finite.of_surjective (Algebra.linearMap R k) hsurj
  have hcl : IsClassical R k :=
    ⟨R.completeLocal, ⟨AlgEquiv.ofRingEquiv (f := R.residueEquiv.toRingEquiv) (fun _ => rfl)⟩⟩
  exact ((smooth_formallySmooth_flat_specialFibre_powerSeries_tfae
    (completeLocalOverSource f) hcl).out 5 2).mp hf

/-- The isomorphism of object functors underlying an isomorphism of groupoids in functors. -/
private def objectsIsoOfIso {C : Type*} [Category C] {G H : GroupoidInFunctors C} (e : G ≅ H) :
    G.objects ≅ H.objects where
  hom := e.hom.mapObjects
  inv := e.inv.mapObjects
  hom_inv_id := congrArg (fun f : GroupoidInFunctors.Hom G G => f.mapObjects) e.hom_inv_id
  inv_hom_id := congrArg (fun f : GroupoidInFunctors.Hom H H => f.mapObjects) e.inv_hom_id

/-- **A smooth projection, read on prorepresenting algebras, is a power series map.** If the
object and arrow functors of a groupoid in functors `K` on `𝒞_Λ` are prorepresented by `A` and
`B`, `π` is a smooth projection of `K` and `σ : A ⟶ B` induces `π` on points, then `σ` exhibits
`B` as a power series ring over `A` (Stacks 06HL). -/
@[sga "7 VI 2.10" "(a), special case"]
private theorem isPowerSeriesOver_of_smooth
    {K : GroupoidInFunctors.{_, w, w} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    {A B : CompleteLocalAlgCat.{u, w, w} Λ k}
    (uA : K.objects ≅ restrictedCoyoneda A) (uB : K.arrows ≅ restrictedCoyoneda B)
    (π : K.arrows ⟶ K.objects) (σ : A ⟶ B) (hσ : restrictedCoyonedaMap σ = uB.inv ≫ π ≫ uA.hom)
    (hsmooth : IsSmooth (elementsBasedFunctor π)) : IsPowerSeriesOver σ := by
  have h := isSmooth_elementsBasedFunctor_conj π uB uA hsmooth
  rw [← hσ] at h
  exact (restrictedRepresentableMap_isSmooth_iff_isPowerSeriesOver σ).mp h

/-- Smoothness of a groupoid in functors on `𝒞_Λ` transports along an isomorphism. -/
private theorem groupoidInFunctors_isSmooth_of_iso
    {G K : GroupoidInFunctors.{_, w, w} (ArtinianLocalAlgCat.{u, w, w} Λ k)} (eG : G ≅ K)
    (hG : GroupoidInFunctors.IsSmooth G) : GroupoidInFunctors.IsSmooth K := by
  have key : ∀ (πG : G.arrows ⟶ G.objects) (πK : K.arrows ⟶ K.objects),
      (∀ T a, πK.app T (eG.hom.mapArrows.app T a) = eG.hom.mapObjects.app T (πG.app T a)) →
      IsSmooth (elementsBasedFunctor πG) → IsSmooth (elementsBasedFunctor πK) := by
    intro πG πK hπ hs
    have h := isSmooth_elementsBasedFunctor_conj πG (groupoidArrowsIso eG) (objectsIsoOfIso eG) hs
    have hK : (groupoidArrowsIso eG).inv ≫ πG ≫ (objectsIsoOfIso eG).hom = πK := by
      ext T a
      have h₁ := hπ T ((groupoidArrowsIso eG).inv.app T a)
      have h₂ : eG.hom.mapArrows.app T ((groupoidArrowsIso eG).inv.app T a) = a :=
        (groupoidArrowsIso eG).inv_hom_id_app_apply T a
      rw [h₂] at h₁
      exact h₁.symm
    rwa [hK] at h
  exact ⟨key G.source K.source eG.hom.map_source hG.1, key G.target K.target eG.hom.map_target hG.2⟩

/-- **Stacks 0DR3, the unwinding.** Let `𝓕` be a category cofibered in groupoids over `𝒞_Λ`
which is a deformation category with finite-dimensional tangent space and finite-dimensional
infinitesimal automorphisms (the conditions of Stacks 06L8). Then there are
1. a versal formal object `ξ` of `𝓕` over a Noetherian complete local `Λ`-algebra `A` with
   residue field `k`, and
2. a Noetherian complete local `Λ`-algebra `B` with residue field `k` and an isomorphism
   `B|_{𝒞_Λ} ≅ A|_{𝒞_Λ} ×_{ξ, 𝓕, ξ} A|_{𝒞_Λ}`,

namely a representable presentation `P` on `𝒞^_Λ` with objects `A` and arrows `B`, whose
restriction to `𝒞_Λ` is isomorphic, as a groupoid in functors, to the groupoid
`(A|_{𝒞_Λ}, A|_{𝒞_Λ} ×_{ξ, 𝓕, ξ} A|_{𝒞_Λ}, s, t, c)` of Stacks 06KY. The two projections are
induced by maps `s, t : A ⟶ B` which are power series maps, hence formally smooth for the
`𝔪_B`-adic topology; the comultiplication `c` makes `(A, B, s, t, c)` a cogroupoid; and `ξ`
induces an equivalence `[A|_{𝒞_Λ} / B|_{𝒞_Λ}] → 𝓕` over `𝒞_Λ`, here the presentation of
`𝓕` by the restriction of `P`; and there is an equivalence `[A/B] → 𝓕^` over `𝒞^_Λ` with the
completion of `𝓕`. -/
theorem exists_versalCogroupoid [IsNoetherianRing Λ] [Module.Finite Λ k] {F : Type uF}
    [Category.{w} F] (p : F ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k)
    (hp : IsPredeformationCategory.{u, w, w} p)
    (h : IsFiniteDimensionalDeformationCategory.{u, w, w} p) :
    ∃ (ξ : FormalObject p) (_ : IsVersal hp.cofibered ξ)
      (P : RepresentablePresentation.{_, w, w} (CompleteLocalAlgCat.{u, w, w} Λ k)),
      P.objects = ξ.base ∧
      Nonempty (versalGroupoid p hp ξ ≅
        GroupoidInFunctors.restrict P.groupoidInFunctors artinianToComplete) ∧
      (IsPowerSeriesOver P.source ∧
        RingHom.FormallySmoothNAdic.{w} P.source.hom.toRingHom (maximalIdeal P.arrows)) ∧
      (IsPowerSeriesOver P.target ∧
        RingHom.FormallySmoothNAdic.{w} P.target.hom.toRingHom (maximalIdeal P.arrows)) ∧
      IsCogroupoid.{_, w, w} P.source P.target P.comultiplication ∧
      Nonempty (Presentation (GroupoidInFunctors.restrict P.groupoidInFunctors
        artinianToComplete) p) ∧
      Nonempty (Presentation P.groupoidInFunctors (FormalObject.projection (p := p))) := by
  classical
  obtain ⟨hdef, hT, hInf⟩ := h
  obtain ⟨ξ, hξ⟩ := exists_versalFormalObject Λ k (BasedCategory.ofFunctor p) hp
    (schlessingerConditionS1_of_satisfiesRS hdef.satisfiesRS)
    (schlessingerConditionS2_of_satisfiesRS hdef.satisfiesRS) hT
  let G := versalGroupoid p hp ξ
  let U := restrictedCoyoneda.{u, w, w} ξ.base
  let f := (associatedMorphism hp.cofibered ξ
    (chosenPushforwardsOfCofibered p hp.cofibered)).toBasedFunctor
  have hU : IsProrepresentable U := ⟨ξ.base, ⟨Iso.refl _⟩⟩
  obtain ⟨hu₀⟩ := restrictedCoyoneda_isPredeformationFunctor.{u, w, w} ξ.base
  let y₀ : U.Elements := ⟨residueFieldObject.{u, w, w} Λ k, hu₀.default⟩
  have hbase : p.obj (f.toFunctor.obj y₀) = residueFieldObject.{u, w, w} Λ k :=
    Functor.congr_obj f.w y₀
  have hGpro : GroupoidInFunctors.IsProrepresentable G :=
    isProrepresentable_presentationGroupoid.{u, w, w, uF, w} p U f.toFunctor f.w hU hdef
      (chosenPushforwardsAtOfCofibered hp.cofibered (f.toFunctor.obj y₀))
      (hInf (f.toFunctor.obj y₀) hbase _)
  obtain ⟨B, ⟨eR⟩⟩ := exists_representingArrowFunctor G hGpro
  obtain ⟨P, hPo, hPa, ⟨eC⟩⟩ :=
    GroupoidInFunctors.exists_representablePresentation_completion_of_isos G ξ.base B
      (versalGroupoidObjectsIso p hp ξ) eR
  let K := GroupoidInFunctors.restrict P.groupoidInFunctors artinianToComplete
  let eG : G ≅ K := (GroupoidInFunctors.completionRestrictIso G).1.symm ≪≫
    GroupoidInFunctors.restrictIso eC artinianToComplete
  let uA : K.objects ≅ restrictedCoyoneda P.objects := Functor.isoWhiskerLeft artinianToComplete
    ((CategoryTheory.uliftCoyonedaIsoCoyoneda.{w}).app (op P.objects))
  let uB : K.arrows ≅ restrictedCoyoneda P.arrows := Functor.isoWhiskerLeft artinianToComplete
    ((CategoryTheory.uliftCoyonedaIsoCoyoneda.{w}).app (op P.arrows))
  have hKs : GroupoidInFunctors.IsSmooth K :=
    groupoidInFunctors_isSmooth_of_iso eG (isSmooth_versalGroupoid p hp ξ hξ)
  have hs : IsPowerSeriesOver P.source :=
    isPowerSeriesOver_of_smooth uA uB K.source P.source (by ext T b; rfl) hKs.1
  have ht : IsPowerSeriesOver P.target :=
    isPowerSeriesOver_of_smooth uA uB K.target P.target (by ext T b; rfl) hKs.2
  let E := GroupoidInFunctors.presentationOfIso eG (presentationOfIsVersal p hp ξ hξ)
  exact ⟨ξ, hξ, P, hPo, ⟨eG⟩, ⟨hs, formallySmoothNAdic_of_isPowerSeriesOver hs⟩,
    ⟨ht, formallySmoothNAdic_of_isPowerSeriesOver ht⟩, P.isCogroupoid_comultiplication, ⟨E⟩,
    ⟨P.completedPresentation hKs E⟩⟩

end Deformation

namespace AlgebraicGeometry.Stack

universe u w

/-- **Stacks 0DR3**, first sentence. In Situation 0DQU, let `x₀` be an object of `𝒳` over
`Spec k` for a field `k` of finite type over `S`, and let `Spec Λ ⊆ S` be an affine open through
which `Spec k ⟶ S` factors with `Λ → k` finite. Then `𝓕_{𝒳,k,x₀}` has a presentation by a smooth
prorepresentable groupoid in functors on `𝒞_Λ`: this is Stacks 0DQW and Stacks 06L8. -/
@[stacks 0DR3 "F_{X,k,x₀} has a presentation by a smooth prorepresentable groupoid in functors"]
theorem hasSmoothPresentation_predeformationCategory
    (D : VersalSituation.{u, w}) {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    letI := (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).category
    Deformation.HasSmoothPresentation
      (Deformation.Artin.predeformationCategory iΛ
        (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection := by
  have : IsNoetherianRing Λ := (isLocallyNoetherian_Spec (R := CommRingCat.of Λ)).mp
    (isLocallyNoetherian_of_isOpenImmersion iΛ)
  exact (Deformation.hasSmoothPresentation_iff_isFiniteDimensionalDeformationCategory _).mpr
    (isFiniteDimensionalDeformationCategory_of_versalSituation D iΛ hiΛ x₀ hx₀ hfinite)

/-- **Stacks 0DR3**, the unwinding for `𝓕_{𝒳,k,x₀}`. In Situation 0DQU, let `x₀` be an object of
`𝒳` over `Spec k` for a field `k` of finite type over `S`, and let `Spec Λ ⊆ S` be an affine open
through which `Spec k ⟶ S` factors with `Λ → k` finite. Then there are
1. a versal formal object `ξ` of `𝓕 = 𝓕_{𝒳,k,x₀}` over a Noetherian complete local `Λ`-algebra
   `A` with residue field `k`, and
2. a Noetherian complete local `Λ`-algebra `B` with residue field `k` and an isomorphism
   `B|_{𝒞_Λ} ≅ A|_{𝒞_Λ} ×_{ξ, 𝓕, ξ} A|_{𝒞_Λ}`,

namely a representable presentation `P` on `𝒞^_Λ` with objects `A` and arrows `B` whose
restriction to `𝒞_Λ` is isomorphic to the groupoid in functors of `ξ` (Stacks 06KY), such that
the projections are induced by formally smooth maps `s, t : A ⟶ B` (power series maps, formally
smooth for the `𝔪_B`-adic topology), the comultiplication `c : B ⟶ B ⊗̂_{s, A, t} B` makes
`(A, B, s, t, c)` a cogroupoid, `ξ` induces an equivalence `[A|_{𝒞_Λ} / B|_{𝒞_Λ}] → 𝓕` of groupoids
cofibred over `𝒞_Λ`, there is an equivalence `[A/B] → 𝓕^` of groupoids cofibred over `𝒞^_Λ`, and
`A` is a versal ring to `𝒳` at `x₀`. -/
@[stacks 0DR3 "the unwinding: A with a versal formal object ξ, B with B|_{𝒞_Λ} ≅ A|_{𝒞_Λ} ×_{ξ,F,ξ} \
A|_{𝒞_Λ}, the projections formally smooth maps s, t : A → B, (A,B,s,t,c) a cogroupoid, the \
equivalence [A|_{𝒞_Λ}/B|_{𝒞_Λ}] → F induced by ξ, the equivalence [A/B] → F^ over the completed \
category, and A a versal ring to 𝒳 at x₀"]
theorem exists_versalCogroupoid_predeformationCategory
    (D : VersalSituation.{u, w}) {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    let C := Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀
    letI := C.category
    let hp := Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property
    ∃ (ξ : Deformation.FormalObject C.projection) (_ : Deformation.IsVersal hp.cofibered ξ)
      (P : Deformation.RepresentablePresentation.{_, u, u}
        (Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)),
      P.objects = ξ.base ∧
      Nonempty (Deformation.versalGroupoid C.projection hp ξ ≅
        Deformation.GroupoidInFunctors.restrict P.groupoidInFunctors
          Deformation.artinianToComplete) ∧
      (Deformation.IsPowerSeriesOver P.source ∧
        RingHom.FormallySmoothNAdic.{u} P.source.hom.toRingHom
          (IsLocalRing.maximalIdeal P.arrows)) ∧
      (Deformation.IsPowerSeriesOver P.target ∧
        RingHom.FormallySmoothNAdic.{u} P.target.hom.toRingHom
          (IsLocalRing.maximalIdeal P.arrows)) ∧
      Deformation.IsCogroupoid.{_, u, u} P.source P.target P.comultiplication ∧
      Nonempty (Deformation.Presentation (Deformation.GroupoidInFunctors.restrict
        P.groupoidInFunctors Deformation.artinianToComplete) C.projection) ∧
      Nonempty (Deformation.Presentation P.groupoidInFunctors
        (Deformation.FormalObject.projection (p := C.projection))) ∧
      IsVersalRingAt D iΛ hiΛ x₀ hx₀ hfinite P.objects := by
  intro C hp
  have : IsNoetherianRing Λ := (isLocallyNoetherian_Spec (R := CommRingCat.of Λ)).mp
    (isLocallyNoetherian_of_isOpenImmersion iΛ)
  obtain ⟨ξ, hξ, P, hPo, heG, hs, ht, hc, hE, hÊ⟩ := Deformation.exists_versalCogroupoid
    C.projection hp
    (isFiniteDimensionalDeformationCategory_of_versalSituation D iΛ hiΛ x₀ hx₀ hfinite)
  refine ⟨ξ, hξ, P, hPo, heG, hs, ht, hc, hE, hÊ, ?_⟩
  rw [hPo]
  exact isVersalRingAt_base D iΛ hiΛ x₀ hx₀ hfinite ξ hξ

end AlgebraicGeometry.Stack
