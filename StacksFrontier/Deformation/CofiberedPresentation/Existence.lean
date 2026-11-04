module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.FibrewiseEquivalence
public import StacksFrontier.Deformation.Applications.TwoFibreProductSixTermExact
public import StacksFrontier.Deformation.Cofibered.BasedEquivalenceFibre
public import StacksFrontier.Deformation.CofiberedPresentation.Prorepresentable
public import StacksFrontier.Deformation.CofiberedPresentation.QuotientEquivalence
public import StacksFrontier.Deformation.CofiberedPresentation.Smooth
public import StacksFrontier.Deformation.Presentation
public import StacksFrontier.Deformation.RimSchlessingerCategory.Prorepresentable
public import StacksFrontier.Deformation.Schlessinger.VersalExistence
import StacksFrontier.Deformation.CofiberedPresentation.Groupoid
import StacksFrontier.Deformation.CofiberedPresentation.Morphism
import StacksFrontier.Deformation.FormalObject.Associated
import StacksFrontier.Deformation.Groupoid.Basic
import StacksFrontier.Deformation.PredeformationTangent.TangentVectorSpace
import StacksFrontier.Deformation.RimSchlessinger.Basic
import StacksFrontier.Deformation.Smooth.Versal

/-!
# Existence of smooth prorepresentable presentations

A deformation category over `𝒞_Λ` whose tangent space and whose space of infinitesimal
automorphisms are finite-dimensional over `k` is presented by a smooth prorepresentable
groupoid in functors on `𝒞_Λ`.

The construction is the one of the source. Condition (RS) gives Schlessinger's conditions
(S1) and (S2), so the finite-dimensionality of the tangent space produces a versal formal
object `ξ` over a complete local algebra `R` by Schlessinger's existence theorem. The
prorepresentable functor `U = R̲|_{𝒞_Λ}` and the associated morphism `ξ̲ : U → ℱ`, smooth
because `ξ` is versal, give a groupoid in functors `(U, R, s, t, c)`. That groupoid is smooth
and its quotient morphism `[U/R] → ℱ` is an equivalence, and the finite-dimensionality of the
infinitesimal automorphisms makes it prorepresentable.

## Main definitions

* `Deformation.presentationOfQuotientEquivalence` reads an equivalence over the base out of the
  quotient of a groupoid in functors as a presentation by that groupoid.

## Main results

* `Deformation.exists_isSmooth_isProrepresentable_presentation`: a deformation category with
  finite-dimensional tangent space and finite-dimensional infinitesimal automorphisms has a
  presentation by a smooth prorepresentable groupoid in functors.

## Implementation notes

The tangent space is the tangent module `T ℱ(M)` of the deformation category at the rank-one
coordinate module, which carries the canonical vector-space structure; the infinitesimal
automorphism space is the value at the same module of the canonical linear lift of the
automorphism functor, quantified over the objects of the special fibre and over the choices of
pushforwards, so that the hypothesis does not depend on those choices.

The morphism universe of `ℱ` is the universe `w` of the residue field. This is the restriction
already carried by the prorepresentability criterion
`Deformation.isProrepresentable_presentationGroupoid`, which is available only when the
hom-set universe of `ℱ` does not exceed that of `𝒞_Λ`.

## References

* [Stacks Project, Tag 06L8](https://stacks.math.columbia.edu/tag/06L8)
-/

@[expose] public section

namespace Deformation

/-! ### An equivalence over the base read as a presentation -/

section
open CategoryTheory CategoryTheory.Functor
universe uC vC uG uF vF

/-- A fully faithful and essentially surjective functor over `C` out of the quotient of a
groupoid in functors is a presentation by that groupoid: the quasi-inverse produced by
`CategoryTheory.Functor.isEquivalenceOver_of_exists_vertical_iso` is again a functor over `C`
and its unit and counit are vertical, which is exactly the data of an equivalence over `C`.
Vertical preimages are available because the quotient projection is cofibered in groupoids. -/
noncomputable def presentationOfQuotientEquivalence {C : Type uC} [Category.{vC} C]
    (G : GroupoidInFunctors.{uC, vC, uG} C) {F : Type uF} [Category.{vF} F] (p : F ⥤ C)
    (K : Grothendieck (evaluationFunctor G) ⥤ F)
    (hw : K ⋙ p = Grothendieck.forget (evaluationFunctor G))
    [K.Full] [K.Faithful] [K.EssSurj] :
    Presentation G p := by
  let φ : BasedFunctor (BasedCategory.ofFunctor (Grothendieck.forget (evaluationFunctor G)))
      (BasedCategory.ofFunctor p) := ⟨K, hw⟩
  let : φ.toFunctor.EssSurj := inferInstanceAs K.EssSurj
  have hess : ∀ A : C,
      (Fiber.mapOfComp (Grothendieck.forget (evaluationFunctor G)) p K hw A).EssSurj :=
    fun A => essSurj_fiberFunctor (quotientProjection_cofibered G) φ A
  let e := isEquivalenceOver_of_exists_vertical_iso hw
    (exists_vertical_iso_of_fiber_essSurj hw hess)
  refine ⟨⟨K, hw⟩, ⟨e.inv, e.inv_over⟩, e.unitIso.symm, e.counitIso, ?_, ?_⟩
  · ext X
    let : (Grothendieck.forget (evaluationFunctor G)).IsHomLift
        (𝟙 ((K ⋙ e.inv).obj X).base) (e.unitIso.hom.app X) := e.unit_vertical X
    let := IsHomLift.lift_id_inv_isIso
      (Grothendieck.forget (evaluationFunctor G))
      ((K ⋙ e.inv).obj X).base (e.unitIso.hom.app X)
    simpa using IsHomLift.fac'
      (Grothendieck.forget (evaluationFunctor G))
      (𝟙 ((K ⋙ e.inv).obj X).base) (inv (e.unitIso.hom.app X))
  · ext X
    let : p.IsHomLift (𝟙 (p.obj ((e.inv ⋙ K).obj X)))
        (e.counitIso.hom.app X) := e.counit_vertical X
    simpa using IsHomLift.fac' p
      (𝟙 (p.obj ((e.inv ⋙ K).obj X))) (e.counitIso.hom.app X)

end

/-! ### Existence of a smooth prorepresentable presentation -/

section
open CategoryTheory CategoryTheory.Functor
universe u w uF

variable {Λ : Type u} {k : Type w} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k] {F : Type uF} [Category.{w} F]

omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
/-- Any two objects of the special fibre of a predeformation category are isomorphic. -/
private theorem nonempty_iso_specialFiber (p : F ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k)
    (hpre : IsPredeformationCategory.{u, w, w} p)
    (a b : p.Fiber (residueFieldObject.{u, w, w} Λ k)) : Nonempty (a ≅ b) := by
  obtain ⟨E⟩ := hpre.specialFiber
  have h : E.functor.obj a = E.functor.obj b := Discrete.ext (Subsingleton.elim _ _)
  exact ⟨E.unitIso.app a ≪≫ E.inverse.mapIso (eqToIso h) ≪≫ (E.unitIso.app b).symm⟩

/-- **Stacks Project, Tag 06L8**, the existence direction. A category `ℱ` cofibered in
groupoids over `𝒞_Λ` which is a deformation category and whose tangent space and space of
infinitesimal automorphisms are finite-dimensional over `k` has a presentation by a smooth
prorepresentable groupoid in functors on `𝒞_Λ`.

The proof of the source. Condition (RS) gives (S1) and (S2) by Tag 06J7, so Schlessinger's
existence theorem, Tag 06IW, produces a versal formal object `ξ` over a complete local algebra
`R` from the finite-dimensionality of the tangent space. Put `U = R̲|_{𝒞_Λ}`; the associated
morphism `ξ̲ : U → ℱ` of Tag 06HC is smooth, which is what versality of `ξ` says, and the
groupoid in functors `(U, R, s, t, c)` built from it is the one of Tag 06KY. Tag 06L1 makes it
smooth and its quotient morphism an equivalence — the quotient morphism is an equivalence
because `ξ̲` is essentially surjective, which follows from smoothness together with essential
surjectivity on the special fibre, and the latter holds because the special fibre of `ℱ` is
equivalent to a point. Tag 06L7 makes it prorepresentable from the finite-dimensionality of
the infinitesimal automorphisms. -/
@[stacks 06L8 "the construction of the tag's existence direction: (1)(2)(3) ⟹ ℱ admits a \
presentation by a smooth prorepresentable groupoid in functors on 𝒞_Λ, built as the source \
builds it, from a versal formal object and the groupoid in functors of 06KY. Only that \
direction, and only when the hom-set universe of ℱ equals that of k, the restriction 06L7 \
carries here. The tag in full — the biconditional, at the general universes, both directions \
— is Deformation.hasSmoothPresentation_iff_isFiniteDimensionalDeformationCategory, whose \
existence direction goes through 06L2 instead and whose converse direction is \
Deformation.isFiniteDimensionalDeformationCategory_of_hasSmoothPresentation, proved from part \
(3) of 06KU, Inf([U/R]) = Ker(ds ⊕ dt), which the library now has as \
Deformation.quotientInfinitesimalBoundary_exact"]
theorem exists_isSmooth_isProrepresentable_presentation
    (p : F ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k)
    (hp : IsDeformationCategory.{u, w, w} p)
    (hT : FiniteDimensional k
      ↥(tangentModuleAt.{u, w, w} (BasedCategory.ofFunctor p) hp
        (FGModuleCat.of k (ULift.{w} k))))
    (hInf : ∀ (x : F) (P : ChosenPushforwardsAt p x),
      p.obj x = residueFieldObject.{u, w, w} Λ k →
      FiniteDimensional k
        ↥((infinitesimalAutomorphismLinearLift.{u, w, w} P hp.satisfiesRS).functor.obj
          (FGModuleCat.of k (ULift.{w} k)))) :
    ∃ G : GroupoidInFunctors.{_, w, w} (ArtinianLocalAlgCat.{u, w, w} Λ k),
      GroupoidInFunctors.IsSmooth G ∧
        GroupoidInFunctors.IsProrepresentable.{u, w, w, w} G ∧
          Nonempty (Presentation G p) := by
  classical
  have hS2' : SchlessingerConditionS2 (CategoryOfElements.π
      (isomorphismClasses (BasedCategory.ofFunctor p) hp.predeformation.cofibered)) :=
    tangentConditionS2.{u, w, w} hp
  let : Fact (IsPredeformationCategory.{u, w, w} (BasedCategory.ofFunctor p).p) :=
    ⟨hp.predeformation⟩
  let : Fact (SchlessingerConditionS2 (CategoryOfElements.π
    (isomorphismClasses (BasedCategory.ofFunctor p) hp.predeformation.cofibered))) := ⟨hS2'⟩
  let : FiniteDimensional k (tangentSpaceArtinian.{u, w, w} Λ k
      (isomorphismClasses (BasedCategory.ofFunctor p) hp.predeformation.cofibered)) := by
    let := hT
    exact (associatedTangentSpaceCarrierLinearEquiv.{u, w, w}
      (BasedCategory.ofFunctor p) hp.predeformation hS2').finiteDimensional
  obtain ⟨ξ, hversal⟩ := exists_versalFormalObject.{u, w, w} Λ k (BasedCategory.ofFunctor p)
    hp.predeformation (schlessingerConditionS1_of_satisfiesRS hp.satisfiesRS)
    (schlessingerConditionS2_of_satisfiesRS hp.satisfiesRS) inferInstance
  let U := restrictedCoyoneda.{u, w, w} ξ.base
  have hUpro : IsProrepresentable U := ⟨ξ.base, ⟨Iso.refl _⟩⟩
  let f := (associatedMorphism hp.predeformation.cofibered ξ
    (chosenPushforwardsOfCofibered p hp.predeformation.cofibered)).toBasedFunctor
  have hf : IsSmooth f := hversal _
  -- the point of `U` over the residue field, and its image in `ℱ`
  obtain ⟨hu₀⟩ := restrictedCoyoneda_isPredeformationFunctor.{u, w, w} ξ.base
  let y₀ : U.Elements := ⟨residueFieldObject.{u, w, w} Λ k, hu₀.default⟩
  have hbase : p.obj (f.toFunctor.obj y₀) = residueFieldObject.{u, w, w} Λ k :=
    Functor.congr_obj f.w y₀
  refine ⟨(presentationGroupoid p U f.toFunctor f.w
      hp.predeformation.cofibered).toGroupoidInFunctors,
    isSmooth_presentationGroupoid p U f hp.predeformation.cofibered hf, ?_, ?_⟩
  · exact isProrepresentable_presentationGroupoid.{u, w, w, uF, w} p U f.toFunctor f.w
      hUpro hp (chosenPushforwardsAtOfCofibered hp.predeformation.cofibered
        (f.toFunctor.obj y₀))
      (hInf (f.toFunctor.obj y₀) _ hbase)
  · have h₀ : (fiberFunctor f (residueFieldObject.{u, w, w} Λ k)).EssSurj :=
      ⟨fun z => ⟨⟨y₀, rfl⟩, nonempty_iso_specialFiber p hp.predeformation _ z⟩⟩
    let : (presentationMorphism p U f.toFunctor f.w
        (presentationGroupoid p U f.toFunctor f.w hp.predeformation.cofibered)).1.Full :=
      presentationMorphism_full p U f.toFunctor f.w _ hp.predeformation.cofibered
    let : (presentationMorphism p U f.toFunctor f.w
        (presentationGroupoid p U f.toFunctor f.w hp.predeformation.cofibered)).1.Faithful :=
      presentationMorphism_faithful p U f.toFunctor f.w _
    let : (presentationMorphism p U f.toFunctor f.w
        (presentationGroupoid p U f.toFunctor f.w hp.predeformation.cofibered)).1.EssSurj :=
      (presentationMorphism_isEquivalence_of_isSmooth_of_fiber_essSurj
        p U f hp.predeformation.cofibered hf h₀).essSurj
    exact ⟨presentationOfQuotientEquivalence _ p _
      (presentationMorphism p U f.toFunctor f.w
        (presentationGroupoid p U f.toFunctor f.w hp.predeformation.cofibered)).2.1⟩

end

end Deformation

end
