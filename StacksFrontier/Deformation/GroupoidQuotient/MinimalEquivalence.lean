module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.GroupoidQuotient.MinimalAutoequivalence
public import StacksFrontier.Deformation.GroupoidQuotient.Realization

/-!
# Equivalences between the quotients of two minimal groupoids in functors

Let `(U, R, s, t, c)` and `(U', R', s', t', c')` be minimal smooth prorepresentable groupoids in
functors on `𝒞_Λ`. An equivalence `[U/R] → [U'/R']` of categories cofibered in groupoids is an
isomorphism.

The argument is the one of the source: a quasi-inverse `ψ` of `φ` is again a morphism of
groupoids in functors, the two composites `ψ ∘ φ` and `φ ∘ ψ` are autoequivalences of
`[U/R]` and of `[U'/R']`, hence isomorphisms by Stacks 06KQ, and a morphism of any category
whose composites with a morphism in the opposite direction are both isomorphisms is itself an
isomorphism.

## Main definitions

* `Deformation.GroupoidInFunctors.inverseMorphismOver`: a quasi-inverse of a `1`-morphism of
  quotients over `𝒞_Λ`, corrected to lie over `𝒞_Λ` on the nose.

## Main results

* `Deformation.GroupoidInFunctors.exists_isIso_hom_of_isEquivalence_endo`: **Stacks 06KQ**.
* `Deformation.GroupoidInFunctors.exists_isIso_hom_of_isEquivalence`: **Stacks 06KR**.
* `Deformation.GroupoidInFunctors.exists_inverse_morphismOver_of_isIso`: the sense in which the
  conclusion is that the `1`-morphism "is an isomorphism" — it has a two-sided inverse
  `1`-morphism over `𝒞_Λ` up to `2`-isomorphism.
* `Deformation.GroupoidInFunctors.isIso_hom_of_quotientMaps_isEquivalence`: the auxiliary in
  which both directions are given as morphisms of groupoids in functors.
* `Deformation.GroupoidInFunctors.isIso_quotientMap_of_quotientMaps_isEquivalence`: in that
  auxiliary the induced functor is an isomorphism of categories on the nose.

## Implementation notes

### What "is an isomorphism" means

The source's conclusion is that the `1`-morphism of quotients is an isomorphism, which for a
`1`-morphism in the `2`-category of categories cofibered in groupoids over `𝒞_Λ` means that it
has a two-sided inverse up to `2`-isomorphism. The results carrying the two tags conclude
something which gives that: the given `1`-morphism is isomorphic, as a functor, to the one
induced by an **isomorphism** of groupoids in functors, whose inverse induces a strict
two-sided inverse lying over `𝒞_Λ`. That last step is
`Deformation.GroupoidInFunctors.exists_inverse_morphismOver_of_isIso`.

### The quasi-inverse

The source's proof picks a quasi-inverse `ψ` of `φ` and treats it as a `1`-morphism of the
quotients. A quasi-inverse of the underlying functor commutes with the projections to `𝒞_Λ`
only up to isomorphism; `Deformation.GroupoidInFunctors.inverseMorphismOver` corrects it by
transporting its value at each object along that isomorphism of base objects, which is
`CategoryTheory.Grothendieck.rectify`. So no quasi-inverse has to be assumed: the hypothesis is
just that the functor of the given `1`-morphism is an equivalence of categories.

## References

* [Stacks Project, Tag 06KR](https://stacks.math.columbia.edu/tag/06KR)
* [Stacks Project, Tag 06KQ](https://stacks.math.columbia.edu/tag/06KQ)
* [Stacks Project, Tag 06K3](https://stacks.math.columbia.edu/tag/06K3)
* [Stacks Project, Tag 06K4](https://stacks.math.columbia.edu/tag/06K4)
* [Stacks Project, Tag 06KM](https://stacks.math.columbia.edu/tag/06KM)
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory

/-- A morphism whose composites with a morphism in the opposite direction are both isomorphisms
is an isomorphism: the retraction supplied by the one composite and the section supplied by the
other agree, so either is a two-sided inverse. -/
private theorem isIso_of_comp_isIso_of_comp_isIso {C : Type*} [Category* C] {X Y : C}
    (f : X ⟶ Y) (g : Y ⟶ X) [IsIso (f ≫ g)] [IsIso (g ≫ f)] : IsIso f := by
  have hr : f ≫ g ≫ inv (f ≫ g) = 𝟙 X := by
    rw [← Category.assoc]
    exact IsIso.hom_inv_id _
  have hl : (inv (g ≫ f) ≫ g) ≫ f = 𝟙 Y := by
    rw [Category.assoc]
    exact IsIso.inv_hom_id _
  have heq : inv (g ≫ f) ≫ g = g ≫ inv (f ≫ g) :=
    calc inv (g ≫ f) ≫ g
        = (inv (g ≫ f) ≫ g) ≫ f ≫ g ≫ inv (f ≫ g) := by rw [hr, Category.comp_id]
      _ = ((inv (g ≫ f) ≫ g) ≫ f) ≫ g ≫ inv (f ≫ g) :=
        (Category.assoc _ _ _).symm
      _ = g ≫ inv (f ≫ g) := by rw [hl, Category.id_comp]
  refine ⟨g ≫ inv (f ≫ g), hr, ?_⟩
  rw [← heq]
  exact hl

end

/-! ### Equivalences between the quotients of two minimal groupoids in functors -/

section
open CategoryTheory

universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

namespace GroupoidInFunctors

variable (G H : GroupoidInFunctors.{_, max v w, max v w}
  (ArtinianLocalAlgCat.{u, max v w, w} Λ k))

/-- A morphism of minimal smooth prorepresentable groupoids in functors inducing an equivalence
of the quotient categories cofibered in groupoids, and admitting a morphism in the opposite
direction that also induces an equivalence, is an isomorphism: the two composites are
autoequivalences of the quotients, hence isomorphisms by Stacks 06KQ. -/
public theorem isIso_hom_of_quotientMaps_isEquivalence [IsNoetherianRing Λ] [Module.Finite Λ k]
    (hproG : IsProrepresentable G) (hsmoothG : IsSmooth G) (hminG : IsMinimal.{u, v, w, v} G)
    (hproH : IsProrepresentable H) (hsmoothH : IsSmooth H) (hminH : IsMinimal.{u, v, w, v} H)
    (F : G ⟶ H) (F' : H ⟶ G)
    [(quotientMap F).IsEquivalence] [(quotientMap F').IsEquivalence] :
    IsIso F := by
  have e₁ : quotientMap (F ≫ F') = quotientMap F ⋙ quotientMap F' := quotientMap_comp F F'
  have e₂ : quotientMap (F' ≫ F) = quotientMap F' ⋙ quotientMap F := quotientMap_comp F' F
  let _ : (quotientMap (F ≫ F')).IsEquivalence := by rw [e₁]; infer_instance
  let _ : (quotientMap (F' ≫ F)).IsEquivalence := by rw [e₂]; infer_instance
  let _ : IsIso (F ≫ F') :=
    isIso_of_quotientMap_isEquivalence G hproG hsmoothG hminG (F ≫ F')
  let _ : IsIso (F' ≫ F) :=
    isIso_of_quotientMap_isEquivalence H hproH hsmoothH hminH (F' ≫ F)
  exact isIso_of_comp_isIso_of_comp_isIso F F'

/-- An equivalence `[U/R] → [U'/R']` of minimal smooth prorepresentable quotients induced by a
morphism of groupoids in functors, and admitting a quasi-inverse induced by one in the opposite
direction, induces an isomorphism of categories on the nose. -/
@[stacks 06KR "equivalence and quasi-inverse taken as induced by morphisms of groupoids, and \
the conclusion read as strict isomorphism of categories. Neither is the source's reading, so \
this is an auxiliary and not the tag's covering declaration: the tag is carried outright by \
`Deformation.GroupoidInFunctors.exists_isIso_hom_of_isEquivalence` below, which takes an \
arbitrary 1-morphism of the quotients over 𝒞_Λ whose functor is an equivalence of categories. \
What this auxiliary adds is that the induced functor is then an isomorphism of categories on \
the nose, which is stronger than the source's conclusion and not invariant under isomorphism \
of functors"]
public theorem isIso_quotientMap_of_quotientMaps_isEquivalence
    [IsNoetherianRing Λ] [Module.Finite Λ k]
    (hproG : IsProrepresentable G) (hsmoothG : IsSmooth G) (hminG : IsMinimal.{u, v, w, v} G)
    (hproH : IsProrepresentable H) (hsmoothH : IsSmooth H) (hminH : IsMinimal.{u, v, w, v} H)
    (F : G ⟶ H) (F' : H ⟶ G)
    [(quotientMap F).IsEquivalence] [(quotientMap F').IsEquivalence] :
    IsIso (quotientMap F).toCatHom :=
  let _ := isIso_hom_of_quotientMaps_isEquivalence G H hproG hsmoothG hminG hproH hsmoothH
    hminH F F'
  isIso_quotientMap F

end GroupoidInFunctors

end

/-! ### Rectifying a quasi-inverse to lie over the base -/

section
open CategoryTheory

universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

namespace GroupoidInFunctors

variable (G H : GroupoidInFunctors.{_, max v w, max v w}
  (ArtinianLocalAlgCat.{u, max v w, w} Λ k))

/-- A quasi-inverse of a `1`-morphism of quotients over `𝒞_Λ` whose functor is an equivalence of
categories lies over the base only up to isomorphism: the counit of the equivalence, whiskered
with the projection. -/
noncomputable def inverseOverIso
    (Φ : StacksRepresentableCFG.MorphismOver
      (Grothendieck.forget (evaluationFunctor G))
      (Grothendieck.forget (evaluationFunctor H))) [Φ.functor.IsEquivalence] :
    Φ.functor.inv ⋙ Grothendieck.forget (evaluationFunctor G) ≅
      Grothendieck.forget (evaluationFunctor H) :=
  eqToIso (show Φ.functor.inv ⋙ Grothendieck.forget (evaluationFunctor G) =
      (Φ.functor.inv ⋙ Φ.functor) ⋙ Grothendieck.forget (evaluationFunctor H) by
    rw [Functor.assoc, Φ.w]) ≪≫
    Functor.isoWhiskerRight Φ.functor.asEquivalence.counitIso
      (Grothendieck.forget (evaluationFunctor H)) ≪≫
    eqToIso (Functor.id_comp _)

/-- A `1`-morphism of quotients over `𝒞_Λ` whose functor is an equivalence of categories admits
a `1`-morphism of quotients over `𝒞_Λ` in the opposite direction whose functor is a
quasi-inverse: a quasi-inverse of the underlying functor lies over the base only up to
isomorphism, and `CategoryTheory.Grothendieck.rectify` corrects that. -/
noncomputable def inverseMorphismOver
    (Φ : StacksRepresentableCFG.MorphismOver
      (Grothendieck.forget (evaluationFunctor G))
      (Grothendieck.forget (evaluationFunctor H))) [Φ.functor.IsEquivalence] :
    StacksRepresentableCFG.MorphismOver
      (Grothendieck.forget (evaluationFunctor H))
      (Grothendieck.forget (evaluationFunctor G)) where
  functor := Grothendieck.rectify Φ.functor.inv (inverseOverIso G H Φ)
  w := Grothendieck.rectify_comp_forget _ _

/-- The functor of `inverseMorphismOver G H Φ` is an equivalence of categories. -/
instance isEquivalence_inverseMorphismOver_functor
    (Φ : StacksRepresentableCFG.MorphismOver
      (Grothendieck.forget (evaluationFunctor G))
      (Grothendieck.forget (evaluationFunctor H))) [Φ.functor.IsEquivalence] :
    (inverseMorphismOver G H Φ).functor.IsEquivalence :=
  Functor.isEquivalence_of_iso
    (Grothendieck.rectifyIso Φ.functor.inv (inverseOverIso G H Φ)).symm

/-! ### Invertibility up to 2-isomorphism -/

/-- A `1`-morphism of quotients over `𝒞_Λ` isomorphic to the one induced by an isomorphism of
groupoids in functors is invertible up to `2`-isomorphism in the `2`-category of categories
cofibered in groupoids over `𝒞_Λ`: the inverse morphism of groupoids in functors induces a
strict two-sided inverse of the induced functor, and that inverse lies over `𝒞_Λ`. -/
theorem exists_inverse_morphismOver_of_isIso {F : G ⟶ H} [IsIso F]
    (Φ : StacksRepresentableCFG.MorphismOver
      (Grothendieck.forget (evaluationFunctor G))
      (Grothendieck.forget (evaluationFunctor H)))
    (α : quotientMap F ≅ Φ.functor) :
    ∃ Ψ : StacksRepresentableCFG.MorphismOver
      (Grothendieck.forget (evaluationFunctor H))
      (Grothendieck.forget (evaluationFunctor G)),
      Nonempty (Φ.functor ⋙ Ψ.functor ≅ Functor.id (Grothendieck (evaluationFunctor G))) ∧
        Nonempty (Ψ.functor ⋙ Φ.functor ≅
          Functor.id (Grothendieck (evaluationFunctor H))) := by
  have h1 : quotientMap F ⋙ quotientMap (inv F) =
      Functor.id (Grothendieck (evaluationFunctor G)) := by
    rw [← quotientMap_comp]
    exact (congrArg (quotientMap (G := G) (H := G)) (IsIso.hom_inv_id F)).trans
      (quotientMap_id G)
  have h2 : quotientMap (inv F) ⋙ quotientMap F =
      Functor.id (Grothendieck (evaluationFunctor H)) := by
    rw [← quotientMap_comp]
    exact (congrArg (quotientMap (G := H) (H := H)) (IsIso.inv_hom_id F)).trans
      (quotientMap_id H)
  refine ⟨⟨quotientMap (inv F), quotientMap_over (inv F)⟩,
    ⟨Functor.isoWhiskerRight α.symm (quotientMap (inv F)) ≪≫ eqToIso h1⟩,
    ⟨Functor.isoWhiskerLeft (quotientMap (inv F)) α.symm ≪≫ eqToIso h2⟩⟩

/-! ### Stacks 06KQ and Stacks 06KR -/

/-- **Stacks Project, Tag 06KQ.** Let `(U, R, s, t, c)` be a minimal smooth prorepresentable
groupoid in functors on `𝒞_Λ`. A `1`-morphism `[U/R] → [U/R]` over `𝒞_Λ` whose functor is an
equivalence of categories is an isomorphism: it is isomorphic to the functor induced by an
**isomorphism** of groupoids in functors, and therefore has a two-sided inverse `1`-morphism
over `𝒞_Λ` up to `2`-isomorphism, by
`Deformation.GroupoidInFunctors.exists_inverse_morphismOver_of_isIso`.

The `1`-morphism is realised by a morphism `F` of groupoids in functors, which is the assertion
opening the source proof and is
`Deformation.GroupoidInFunctors.exists_hom_of_morphismOver`; the functor induced by `F` is then
an equivalence, so `F` is an isomorphism by
`Deformation.GroupoidInFunctors.isIso_of_quotientMap_isEquivalence`, which is the differential
argument of the source proof. -/
@[stacks 06KQ]
theorem exists_isIso_hom_of_isEquivalence_endo [IsNoetherianRing Λ] [Module.Finite Λ k]
    (hpro : IsProrepresentable G) (hsmooth : IsSmooth G) (hmin : IsMinimal.{u, v, w, v} G)
    (Φ : StacksRepresentableCFG.MorphismOver
      (Grothendieck.forget (evaluationFunctor G))
      (Grothendieck.forget (evaluationFunctor G))) [Φ.functor.IsEquivalence] :
    ∃ F : G ⟶ G, IsIso F ∧ Nonempty (quotientMap F ≅ Φ.functor) := by
  obtain ⟨F, ⟨α⟩⟩ := exists_hom_of_morphismOver G G hpro hsmooth Φ
  have hF : (quotientMap F).IsEquivalence := Functor.isEquivalence_of_iso α.symm
  exact ⟨F, isIso_of_quotientMap_isEquivalence G hpro hsmooth hmin F, ⟨α⟩⟩

/-- **Stacks Project, Tag 06KR.** Let `(U, R, s, t, c)` and `(U', R', s', t', c')` be minimal
smooth prorepresentable groupoids in functors on `𝒞_Λ`. A `1`-morphism `[U/R] → [U'/R']` over
`𝒞_Λ` whose functor is an equivalence of categories is an isomorphism: it is isomorphic to the
functor induced by an **isomorphism** of groupoids in functors, and therefore has a two-sided
inverse `1`-morphism over `𝒞_Λ` up to `2`-isomorphism, by
`Deformation.GroupoidInFunctors.exists_inverse_morphismOver_of_isIso`.

This is the source's proof: a quasi-inverse of the given `1`-morphism, corrected to lie over
`𝒞_Λ` by `Deformation.GroupoidInFunctors.inverseMorphismOver`, is realised by a morphism of
groupoids in functors in the opposite direction, and the two composites are autoequivalences of
the two quotients, hence isomorphisms by Tag 06KQ. -/
@[stacks 06KR]
theorem exists_isIso_hom_of_isEquivalence [IsNoetherianRing Λ] [Module.Finite Λ k]
    (hproG : IsProrepresentable G) (hsmoothG : IsSmooth G) (hminG : IsMinimal.{u, v, w, v} G)
    (hproH : IsProrepresentable H) (hsmoothH : IsSmooth H) (hminH : IsMinimal.{u, v, w, v} H)
    (Φ : StacksRepresentableCFG.MorphismOver
      (Grothendieck.forget (evaluationFunctor G))
      (Grothendieck.forget (evaluationFunctor H))) [Φ.functor.IsEquivalence] :
    ∃ F : G ⟶ H, IsIso F ∧ Nonempty (quotientMap F ≅ Φ.functor) := by
  obtain ⟨F, ⟨α⟩⟩ := exists_hom_of_morphismOver G H hproG hsmoothH Φ
  obtain ⟨F', ⟨β⟩⟩ := exists_hom_of_morphismOver H G hproH hsmoothG
    (inverseMorphismOver G H Φ)
  have hF : (quotientMap F).IsEquivalence := Functor.isEquivalence_of_iso α.symm
  have hF' : (quotientMap F').IsEquivalence := Functor.isEquivalence_of_iso β.symm
  exact ⟨F, isIso_hom_of_quotientMaps_isEquivalence G H hproG hsmoothG hminG hproH hsmoothH
    hminH F F', ⟨α⟩⟩

end GroupoidInFunctors

end

end Deformation
