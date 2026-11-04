module

public import StacksFrontier.AlgebraicGeometry.Descent.Algebra.FiniteEtaleEffective
public import StacksFrontier.AlgebraicGeometry.Descent.Algebra.TransitionCocycle
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical

/-!
# The algebra transition of a sheaf presented by affine objects, and its cocycle condition

Let `J` be a subcanonical topology on a category `C` of objects over `Spec R` — the étale site
of a scheme over `Spec R`, say — and let `F` be a sheaf on it.  Suppose two objects `X` and `Y`
of `C` both represent `F`, and that they are affine: `X` is `Spec A₁` and `Y` is `Spec A₂` over
`Spec R`.  Then `F` *forces* an isomorphism `A₂ ≃ₐ[R] A₁`, with no choice entering: the
presentations differ by a unique isomorphism of sheaves, that isomorphism comes from a unique
morphism of the site because `J` is subcanonical, and that morphism is `Spec` of a unique algebra
map because `Spec` is fully faithful on algebras over a base.

The consequence this file is written for is the **cocycle condition**, which is the one piece of
coherence data a descent argument normally has to construct and check by hand.  Here it is free:
three objects representing one sheaf give three such algebra isomorphisms, and they compose,
because the underlying isomorphisms of the site compose
(`CategoryTheory.Sheaf.transition_trans`).  Combined with
`Stacks.AlgebraDescent.cocycle_of_cocycleAlg` this discharges the cocycle hypothesis of effective
descent for algebras, and hence produces the descended finite étale morphism of Stacks 0245.

## Main definitions

* `Stacks.AlgebraDescent.pairTransitionAlgEquiv` — the algebra isomorphism forced by two affine
  presentations of one sheaf.
* `Stacks.AlgebraDescent.transitionOfSheaf` — the transition `B ⊗[R] A ≃ₐ[R] A ⊗[R] B` of a
  sheaf presented both by `Spec (B ⊗[R] A)` and by `Spec (A ⊗[R] B)`.

## Main results

* `CategoryTheory.Sheaf.representingIso_trans`, `...representingIso_refl` and
  `...representingIso_mapIso` — the isomorphism of objects underlying an isomorphism of
  sheafified representables is functorial in that isomorphism.
* `Stacks.AlgebraDescent.algEquivOfSpecOverIso_mapIso_comp` — the crossing of a composite of
  isomorphisms of the site is the composite of the crossings.
* `Stacks.AlgebraDescent.pairTransitionAlgEquiv_comp` — **the cocycle condition for the algebra
  transitions of a sheaf holds unconditionally**, together with
  `...pairTransitionAlgEquiv_self` and `...pairTransitionAlgEquiv_symm`.
* `Stacks.AlgebraDescent.left_of_specOverMap` and `...right_of_specOverMap` — the two hypotheses
  saying that a transition is a morphism over `A ⊗[R] A`, obtained from the corresponding
  equations between morphisms of spectra.
* `Stacks.AlgebraDescent.exists_finiteEtale_spec_of_sheafTransition` — **the descended finite
  étale morphism `Spec C ⟶ Spec R`, produced from a sheaf.**  All three hypotheses that
  `Stacks.AlgebraDescent.exists_finiteEtale_spec_tensorEquiv_of_faithfullyFlat` needs are
  supplied: the transition itself, its two base components, and the cocycle condition.
* `Stacks.AlgebraDescent.pairTransitionAlgEquiv_id_mapIso`,
  `...pairTransitionAlgEquiv_id_mapIso_refl` and `...transitionOfSheaf_id_mapIso` — the
  transition of presentations that are themselves induced by `Spec` of algebra isomorphisms.
* `Stacks.AlgebraDescent.exists_finiteEtale_spec_of_sheafTransition_trivial` — every hypothesis
  of the previous statement is satisfiable, so it is not vacuous.

## Scope

The presentations of the sheaf are hypotheses, and so are the two equations saying that the
transition is a morphism over `A ⊗[R] A` and the three equations identifying the triple-level
transitions with the cocycle maps of the double-level one.  What this file supplies is everything
that is *forced*: the transition isomorphism and the cocycle condition.  The identifications are
the functoriality of restriction — restricting a representable presentation along a projection of
the triple product gives the representable presentation of the restriction — and are not proved
here.

## Implementation notes

The site is kept arbitrary and the passage to `Over (Spec R)` is a functor
`ι : C ⥤ Over (Spec R)` together with, for each object used, an isomorphism of its image with the
spectrum of an algebra.  That is weaker than asking the objects of `C` to *be* spectra, and it is
the shape in which a site of schemes over a base presents itself.

`Stacks.AlgebraDescent.pairTransitionAlgEquiv` is `CategoryTheory.Sheaf.representingIso` of the
comparison of the two presentations, carried across by
`AlgebraicGeometry.algEquivOfSpecOverIso`; it is the two-object form of
`CategoryTheory.Sheaf.transition`, which is indexed by a family.  The two-object form is the one
usable here because the three triple-level objects are spectra of three *different* rings.

## References

* [Stacks Project, Tag 03RV](https://stacks.math.columbia.edu/tag/03RV)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 00WR](https://stacks.math.columbia.edu/tag/00WR)
-/

@[expose] public section

noncomputable section

universe v u₁ u

open CategoryTheory AlgebraicGeometry CommRingCat TensorProduct

namespace CategoryTheory.Sheaf

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type max u₁ v)] [J.Subcanonical]

/-- **The isomorphisms of representing objects compose.**  This is the two-object form of
`CategoryTheory.Sheaf.transition_trans`: the isomorphism of objects underlying a composite of
isomorphisms of sheafified representables is the composite of the underlying isomorphisms. -/
theorem representingIso_trans {X Y Z : C}
    (e : (sheafifiedYoneda J).obj X ≅ (sheafifiedYoneda J).obj Y)
    (f : (sheafifiedYoneda J).obj Y ≅ (sheafifiedYoneda J).obj Z) :
    representingIso e ≪≫ representingIso f = representingIso (e ≪≫ f) :=
  Iso.ext ((fullyFaithfulSheafifiedYoneda J).map_injective (by
    rw [Iso.trans_hom, Functor.map_comp, map_representingIso_hom, map_representingIso_hom,
      map_representingIso_hom, Iso.trans_hom]))

/-- The isomorphism of objects underlying the identity isomorphism of a sheafified representable
is the identity of the representing object. -/
theorem representingIso_refl (X : C) :
    representingIso (Iso.refl ((sheafifiedYoneda J).obj X)) = Iso.refl X :=
  (representingIso_unique (by rw [Iso.refl_hom, Iso.refl_hom, Functor.map_id])).symm

/-- The isomorphism of objects underlying the image of an isomorphism under the sheafified
Yoneda embedding is that isomorphism. -/
theorem representingIso_mapIso {X Y : C} (χ : X ≅ Y) :
    representingIso ((sheafifiedYoneda J).mapIso χ) = χ :=
  (representingIso_unique rfl).symm

end CategoryTheory.Sheaf

namespace Stacks.AlgebraDescent

open CategoryTheory.Sheaf

/-! ### The algebra transition forced by two affine presentations of one sheaf -/

section Pair

variable {R : Type u} [CommRing R]
  {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type max u₁ v)] [J.Subcanonical]
  (ι : C ⥤ Over (Spec (.of R))) {F : Sheaf J (Type max u₁ v)}

/-- **The algebra transition of two affine presentations of one sheaf.**  Two objects of a
subcanonical site representing the same sheaf, both affine over `Spec R`, are the spectra of
`R`-algebras that are canonically isomorphic — no choice enters. -/
def pairTransitionAlgEquiv {X Y : C} {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
    [Algebra R A₁] [Algebra R A₂]
    (wX : ι.obj X ≅ specOver R A₁) (wY : ι.obj Y ≅ specOver R A₂)
    (eX : (sheafifiedYoneda J).obj X ≅ F) (eY : (sheafifiedYoneda J).obj Y ≅ F) :
    A₂ ≃ₐ[R] A₁ :=
  algEquivOfSpecOverIso (wX.symm ≪≫ ι.mapIso (representingIso (eX ≪≫ eY.symm)) ≪≫ wY)

variable {X Y Z : C} {A₁ A₂ A₃ : Type u} [CommRing A₁] [CommRing A₂] [CommRing A₃]
  [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]
  (wX : ι.obj X ≅ specOver R A₁) (wY : ι.obj Y ≅ specOver R A₂)
  (wZ : ι.obj Z ≅ specOver R A₃)
  (eX : (sheafifiedYoneda J).obj X ≅ F) (eY : (sheafifiedYoneda J).obj Y ≅ F)
  (eZ : (sheafifiedYoneda J).obj Z ≅ F)

/-- The crossing of a composite of isomorphisms of the site, read through realizations of the
three objects as spectra, is the composite of the crossings. -/
theorem algEquivOfSpecOverIso_mapIso_comp (χ₁ : X ≅ Y) (χ₂ : Y ≅ Z) :
    (algEquivOfSpecOverIso (wX.symm ≪≫ ι.mapIso χ₁ ≪≫ wY)).toAlgHom.comp
        (algEquivOfSpecOverIso (wY.symm ≪≫ ι.mapIso χ₂ ≪≫ wZ)).toAlgHom =
      (algEquivOfSpecOverIso (wX.symm ≪≫ ι.mapIso (χ₁ ≪≫ χ₂) ≪≫ wZ)).toAlgHom := by
  rw [algEquivOfSpecOverIso_toAlgHom, algEquivOfSpecOverIso_toAlgHom,
    algEquivOfSpecOverIso_toAlgHom, ← algHomOfSpecOverMap_comp]
  congr 1
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [← Category.assoc (ι.map χ₁.hom), ← ι.map_comp, ← Iso.trans_hom]

/-- **The cocycle condition for the algebra transitions of a sheaf is automatic.**  Three affine
presentations of one sheaf give three transition isomorphisms, and they compose.  No hypothesis
is needed: this is faithfulness of the sheafified Yoneda embedding of a subcanonical site
together with faithfulness of `Spec` on algebras over the base. -/
theorem pairTransitionAlgEquiv_comp :
    (pairTransitionAlgEquiv ι wX wY eX eY).toAlgHom.comp
        (pairTransitionAlgEquiv ι wY wZ eY eZ).toAlgHom =
      (pairTransitionAlgEquiv ι wX wZ eX eZ).toAlgHom := by
  have hiso : (eX ≪≫ eY.symm) ≪≫ eY ≪≫ eZ.symm = eX ≪≫ eZ.symm := by
    rw [Iso.trans_assoc, Iso.symm_self_id_assoc]
  have h := algEquivOfSpecOverIso_mapIso_comp ι wX wY wZ
    (representingIso (eX ≪≫ eY.symm)) (representingIso (eY ≪≫ eZ.symm))
  rw [representingIso_trans, hiso] at h
  exact h

/-- The transition from a presentation to itself is the identity. -/
@[simp]
theorem pairTransitionAlgEquiv_self :
    pairTransitionAlgEquiv ι wX wX eX eX = AlgEquiv.refl := by
  rw [pairTransitionAlgEquiv, Iso.self_symm_id, representingIso_refl, Functor.mapIso_refl,
    Iso.refl_trans, Iso.symm_self_id, algEquivOfSpecOverIso_refl]

/-- The transitions of two presentations of one sheaf are inverse to each other. -/
theorem pairTransitionAlgEquiv_symm :
    (pairTransitionAlgEquiv ι wX wY eX eY).symm = pairTransitionAlgEquiv ι wY wX eY eX := by
  refine AlgEquiv.coe_toAlgHom_injective (AlgHom.ext fun a ↦ ?_)
  have h := pairTransitionAlgEquiv_comp ι wX wY wX eX eY eX
  rw [pairTransitionAlgEquiv_self] at h
  have h' : pairTransitionAlgEquiv ι wX wY eX eY
      (pairTransitionAlgEquiv ι wY wX eY eX a) = a := by
    simpa using congrArg (fun k ↦ (k : A₁ →ₐ[R] A₁) a) h
  rw [AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_eq]
  exact h'.symm

end Pair

/-! ### The transition of a sheaf presented over a double tensor product -/

section Transition

variable {R : Type u} [CommRing R] (A B : Type u) [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type max u₁ v)] [J.Subcanonical]
  (ι : C ⥤ Over (Spec (.of R))) {F : Sheaf J (Type max u₁ v)} {X₀ X₁ : C}
  (w₀ : ι.obj X₀ ≅ specOver R (B ⊗[R] A)) (w₁ : ι.obj X₁ ≅ specOver R (A ⊗[R] B))
  (e₀ : (sheafifiedYoneda J).obj X₀ ≅ F) (e₁ : (sheafifiedYoneda J).obj X₁ ≅ F)

/-- **The algebra transition of a sheaf.**  A sheaf presented both by `Spec (B ⊗[R] A)` and by
`Spec (A ⊗[R] B)` forces a transition isomorphism `B ⊗[R] A ≃ₐ[R] A ⊗[R] B`, which is the datum
effective descent for algebras consumes. -/
def transitionOfSheaf : (B ⊗[R] A) ≃ₐ[R] (A ⊗[R] B) :=
  pairTransitionAlgEquiv ι w₁ w₀ e₁ e₀

/-- **The first base component of a transition, from an equation between morphisms of spectra.**
This is the hypothesis `hleft` of effective descent for algebras, obtained from the
corresponding equation at the level of schemes. -/
theorem left_of_specOverMap (θ : (B ⊗[R] A) ≃ₐ[R] (A ⊗[R] B))
    (h : specOverMap (θ.toAlgHom.comp
          ((Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := B) (B := A)).comp
            (IsScalarTower.toAlgHom R A B))) =
        specOverMap (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := A) (B := B))) :
    ∀ a : A, θ (algebraMap A B a ⊗ₜ[R] (1 : A)) = a ⊗ₜ[R] (1 : B) :=
  fun a ↦ congrArg (fun k ↦ (k : A →ₐ[R] A ⊗[R] B) a) (specOverMap_injective h)

/-- **The second base component of a transition, from an equation between morphisms of spectra.**
This is the hypothesis `hright` of effective descent for algebras. -/
theorem right_of_specOverMap (θ : (B ⊗[R] A) ≃ₐ[R] (A ⊗[R] B))
    (h : specOverMap (θ.toAlgHom.comp
          (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := A))) =
        specOverMap ((Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).comp
          (IsScalarTower.toAlgHom R A B))) :
    ∀ a : A, θ ((1 : B) ⊗ₜ[R] a) = (1 : A) ⊗ₜ[R] algebraMap A B a :=
  fun a ↦ congrArg (fun k ↦ (k : A →ₐ[R] A ⊗[R] B) a) (specOverMap_injective h)

end Transition

/-! ### The descended finite étale morphism, produced from a sheaf -/

section Descend

variable {R : Type u} [CommRing R] (A B : Type u) [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type max u₁ v)] [J.Subcanonical]
  (ι : C ⥤ Over (Spec (.of R)))

omit [Algebra A B] [IsScalarTower R A B] in
/-- **The cocycle condition of effective descent for algebras, produced from a sheaf.**  Three
affine presentations of one sheaf, by the spectra of the three threefold tensor products, give
the cocycle condition on a transition `θ` as soon as the three transitions they force are the
three cocycle maps of `θ`. -/
theorem cocycle_of_sheafTransition (θ : (B ⊗[R] A) ≃ₐ[R] (A ⊗[R] B))
    {G : Sheaf J (Type max u₁ v)} {Y₀ Y₁ Y₂ : C}
    (v₀ : ι.obj Y₀ ≅ specOver R ((B ⊗[R] A) ⊗[R] A))
    (v₁ : ι.obj Y₁ ≅ specOver R ((A ⊗[R] B) ⊗[R] A))
    (v₂ : ι.obj Y₂ ≅ specOver R ((A ⊗[R] A) ⊗[R] B))
    (f₀ : (sheafifiedYoneda J).obj Y₀ ≅ G) (f₁ : (sheafifiedYoneda J).obj Y₁ ≅ G)
    (f₂ : (sheafifiedYoneda J).obj Y₂ ≅ G)
    (h₀₁ : (pairTransitionAlgEquiv ι v₁ v₀ f₁ f₀).toAlgHom = cocycleAlg01 R A B θ)
    (h₁₂ : (pairTransitionAlgEquiv ι v₂ v₁ f₂ f₁).toAlgHom = cocycleAlg12 R A B θ)
    (h₀₂ : (pairTransitionAlgEquiv ι v₂ v₀ f₂ f₀).toAlgHom = cocycleAlg02 R A B θ) :
    cocycle12 R A B θ.toLinearMap ∘ₗ cocycle01 R A B θ.toLinearMap =
      cocycle02 R A B θ.toLinearMap := by
  refine cocycle_of_cocycleAlg R A B θ ?_
  rw [← h₀₁, ← h₁₂, ← h₀₂]
  exact pairTransitionAlgEquiv_comp ι v₂ v₁ v₀ f₂ f₁ f₀

/-- **The affine case of Stacks 0245 for finite étale morphisms, with every input produced from a
sheaf.**  Let `R → A` be faithfully flat and let `B` be a finite étale `A`-algebra.  Suppose a
sheaf on a subcanonical site over `Spec R` is presented both by `Spec (B ⊗[R] A)` and by
`Spec (A ⊗[R] B)`, so that it forces a transition `θ`; suppose that transition is a morphism
over `A ⊗[R] A`; and suppose a second sheaf is presented by the spectra of the three threefold
tensor products with the three forced transitions being the cocycle maps of `θ`.  Then `B`
descends: there is an `R`-subalgebra `C ⊆ B` with `Spec C ⟶ Spec R` finite and étale and
`A ⊗[R] C ≅ B`. -/
theorem exists_finiteEtale_spec_of_sheafTransition
    [Module.FaithfullyFlat R A] [Module.Finite A B] [Algebra.Etale A B]
    {F : Sheaf J (Type max u₁ v)} {X₀ X₁ : C}
    (w₀ : ι.obj X₀ ≅ specOver R (B ⊗[R] A)) (w₁ : ι.obj X₁ ≅ specOver R (A ⊗[R] B))
    (e₀ : (sheafifiedYoneda J).obj X₀ ≅ F) (e₁ : (sheafifiedYoneda J).obj X₁ ≅ F)
    (hleft : ∀ a : A, transitionOfSheaf A B ι w₀ w₁ e₀ e₁
      (algebraMap A B a ⊗ₜ[R] (1 : A)) = a ⊗ₜ[R] (1 : B))
    (hright : ∀ a : A, transitionOfSheaf A B ι w₀ w₁ e₀ e₁
      ((1 : B) ⊗ₜ[R] a) = (1 : A) ⊗ₜ[R] algebraMap A B a)
    {G : Sheaf J (Type max u₁ v)} {Y₀ Y₁ Y₂ : C}
    (v₀ : ι.obj Y₀ ≅ specOver R ((B ⊗[R] A) ⊗[R] A))
    (v₁ : ι.obj Y₁ ≅ specOver R ((A ⊗[R] B) ⊗[R] A))
    (v₂ : ι.obj Y₂ ≅ specOver R ((A ⊗[R] A) ⊗[R] B))
    (f₀ : (sheafifiedYoneda J).obj Y₀ ≅ G) (f₁ : (sheafifiedYoneda J).obj Y₁ ≅ G)
    (f₂ : (sheafifiedYoneda J).obj Y₂ ≅ G)
    (h₀₁ : (pairTransitionAlgEquiv ι v₁ v₀ f₁ f₀).toAlgHom =
      cocycleAlg01 R A B (transitionOfSheaf A B ι w₀ w₁ e₀ e₁))
    (h₁₂ : (pairTransitionAlgEquiv ι v₂ v₁ f₂ f₁).toAlgHom =
      cocycleAlg12 R A B (transitionOfSheaf A B ι w₀ w₁ e₀ e₁))
    (h₀₂ : (pairTransitionAlgEquiv ι v₂ v₀ f₂ f₀).toAlgHom =
      cocycleAlg02 R A B (transitionOfSheaf A B ι w₀ w₁ e₀ e₁)) :
    ∃ D : Subalgebra R B,
      AlgebraicGeometry.IsFinite (Spec.map (ofHom (algebraMap R D))) ∧
        AlgebraicGeometry.Etale (Spec.map (ofHom (algebraMap R D))) ∧
          Nonempty ((A ⊗[R] D) ≃ₐ[A] B) :=
  exists_finiteEtale_spec_tensorEquiv_of_faithfullyFlat R A B
    (transitionOfSheaf A B ι w₀ w₁ e₀ e₁) hleft hright
    (cocycle_of_sheafTransition A B ι (transitionOfSheaf A B ι w₀ w₁ e₀ e₁)
      v₀ v₁ v₂ f₀ f₁ f₂ h₀₁ h₁₂ h₀₂)

end Descend

/-! ### The presentations induced by isomorphisms of spectra -/

section Induced

variable {R : Type u} [CommRing R]
  (J : GrothendieckTopology (Over (Spec (.of R)))) [HasWeakSheafify J (Type (u + 1))]
  [J.Subcanonical]
  {A₀ A₁ A₂ : Type u} [CommRing A₀] [CommRing A₁] [CommRing A₂]
  [Algebra R A₀] [Algebra R A₁] [Algebra R A₂]

/-- The transition forced by two presentations of one sheaf that are themselves induced by
isomorphisms of spectra is the evident comparison of those isomorphisms. -/
theorem pairTransitionAlgEquiv_id_mapIso
    (ψ₁ : specOver R A₁ ≅ specOver R A₀) (ψ₂ : specOver R A₂ ≅ specOver R A₀) :
    pairTransitionAlgEquiv (J := J) (𝟭 (Over (Spec (.of R))))
        (Iso.refl (specOver R A₁)) (Iso.refl (specOver R A₂))
        ((sheafifiedYoneda J).mapIso ψ₁) ((sheafifiedYoneda J).mapIso ψ₂) =
      algEquivOfSpecOverIso (ψ₁ ≪≫ ψ₂.symm) := by
  rw [pairTransitionAlgEquiv, ← Functor.mapIso_symm, ← Functor.mapIso_trans,
    representingIso_mapIso, show (𝟭 (Over (Spec (.of R)))).mapIso (ψ₁ ≪≫ ψ₂.symm) = ψ₁ ≪≫ ψ₂.symm
      from Iso.ext rfl]
  congr 1

/-- The special case of `Stacks.AlgebraDescent.pairTransitionAlgEquiv_id_mapIso` in which the
second presentation is the sheaf itself. -/
theorem pairTransitionAlgEquiv_id_mapIso_refl (ψ : specOver R A₁ ≅ specOver R A₀) :
    pairTransitionAlgEquiv (J := J) (𝟭 (Over (Spec (.of R))))
        (Iso.refl (specOver R A₁)) (Iso.refl (specOver R A₀))
        ((sheafifiedYoneda J).mapIso ψ) (Iso.refl ((sheafifiedYoneda J).obj (specOver R A₀))) =
      algEquivOfSpecOverIso ψ := by
  rw [← Functor.mapIso_refl (sheafifiedYoneda J), pairTransitionAlgEquiv_id_mapIso]
  congr 1

end Induced

/-! ### The transition of presentations induced by isomorphisms of spectra -/

section InducedTransition

variable {R : Type u} [CommRing R] (A B : Type u) [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (J : GrothendieckTopology (Over (Spec (.of R)))) [HasWeakSheafify J (Type (u + 1))]
  [J.Subcanonical]

/-- The transition of a sheaf whose second presentation is induced by `Spec` of an algebra
isomorphism and whose first presentation is the sheaf itself is that isomorphism. -/
theorem transitionOfSheaf_id_mapIso (θ : (B ⊗[R] A) ≃ₐ[R] (A ⊗[R] B)) :
    transitionOfSheaf A B (𝟭 (Over (Spec (.of R))))
        (Iso.refl (specOver R (B ⊗[R] A))) (Iso.refl (specOver R (A ⊗[R] B)))
        (Iso.refl ((sheafifiedYoneda J).obj (specOver R (B ⊗[R] A))))
        ((sheafifiedYoneda J).mapIso (specOverMapIso θ)) = θ := by
  rw [transitionOfSheaf, pairTransitionAlgEquiv_id_mapIso_refl,
    algEquivOfSpecOverIso_specOverMapIso]

end InducedTransition

/-! ### Every hypothesis is satisfiable -/

section Nonvacuity

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
  [Module.Finite R B] [Algebra.Etale R B]

/-- **Every hypothesis of
`Stacks.AlgebraDescent.exists_finiteEtale_spec_of_sheafTransition` is satisfiable, so it is not
vacuous.**  They all hold for the identity covering `R → R`, an arbitrary finite étale
`R`-algebra `B`, the canonical topology on schemes over `Spec R`, and the presentations induced
by `Spec` of the canonical transition `Stacks.SchemeDescent.trivialTransition` and of its two
cocycle maps; the third cocycle map is then forced, and the equation identifying it is the
cocycle condition `Stacks.SchemeDescent.trivialTransition_cocycle`. -/
theorem exists_finiteEtale_spec_of_sheafTransition_trivial :
    ∃ D : Subalgebra R B,
      AlgebraicGeometry.IsFinite (Spec.map (ofHom (algebraMap R D))) ∧
        AlgebraicGeometry.Etale (Spec.map (ofHom (algebraMap R D))) ∧
          Nonempty ((R ⊗[R] D) ≃ₐ[R] B) := by
  set J := Sheaf.canonicalTopology (Over (Spec (.of R)))
  set θ₀ := Stacks.SchemeDescent.trivialTransition R B
  refine exists_finiteEtale_spec_of_sheafTransition R B (J := J) (𝟭 _)
    (Iso.refl (specOver R (B ⊗[R] R))) (Iso.refl (specOver R (R ⊗[R] B)))
    (Iso.refl ((sheafifiedYoneda J).obj (specOver R (B ⊗[R] R))))
    ((sheafifiedYoneda J).mapIso (specOverMapIso θ₀)) ?_ ?_
    (Iso.refl (specOver R ((B ⊗[R] R) ⊗[R] R))) (Iso.refl (specOver R ((R ⊗[R] B) ⊗[R] R)))
    (Iso.refl (specOver R ((R ⊗[R] R) ⊗[R] B)))
    ((sheafifiedYoneda J).mapIso (specOverMapIso (cocycleAlgEquiv01 R R B θ₀).symm))
    (Iso.refl ((sheafifiedYoneda J).obj (specOver R ((R ⊗[R] B) ⊗[R] R))))
    ((sheafifiedYoneda J).mapIso (specOverMapIso (cocycleAlgEquiv12 R R B θ₀)))
    ?_ ?_ ?_
  · rw [transitionOfSheaf_id_mapIso]
    exact Stacks.SchemeDescent.trivialTransition_left R B
  · rw [transitionOfSheaf_id_mapIso]
    exact Stacks.SchemeDescent.trivialTransition_right R B
  · rw [transitionOfSheaf_id_mapIso,
      ← Functor.mapIso_refl (sheafifiedYoneda J), pairTransitionAlgEquiv_id_mapIso,
      specOverMapIso_symm, AlgEquiv.symm_symm, Iso.refl_trans,
      algEquivOfSpecOverIso_specOverMapIso]
    exact cocycleAlgEquiv01_toAlgHom R R B θ₀
  · rw [transitionOfSheaf_id_mapIso, pairTransitionAlgEquiv_id_mapIso_refl,
      algEquivOfSpecOverIso_specOverMapIso]
    exact cocycleAlgEquiv12_toAlgHom R R B θ₀
  · rw [transitionOfSheaf_id_mapIso, pairTransitionAlgEquiv_id_mapIso, specOverMapIso_symm,
      AlgEquiv.symm_symm, ← specOverMapIso_trans, algEquivOfSpecOverIso_specOverMapIso]
    exact cocycleAlg_comp_of_cocycle R R B θ₀
      (Stacks.SchemeDescent.trivialTransition_cocycle R B)

end Nonvacuity

end Stacks.AlgebraDescent

end

end
