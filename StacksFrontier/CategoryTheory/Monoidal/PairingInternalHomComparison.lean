module

public import StacksFrontier.CategoryTheory.Monoidal.Rigid
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackInvertibility
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomEquivalenceTransport

/-!
# The internal hom out of a dualizable object, and the comparison of a monoidal functor with it

Let `C` be a monoidal category equipped with an internal hom `H : Cᵒᵖ ⥤ C ⥤ C` in the weak sense
of a bijection `e : (A ⟶ H(B, C)) ≃ (A ⊗' B ⟶ C)` natural in `A`, where `⊗'` is a bifunctor
`T : C × C ⥤ C` identified with the monoidal tensor product by a natural isomorphism
`b : A ⊗ B ≅ T(A, B)`. If `E` has a left dual `E'` (an exact pairing `η : 𝟙 ⟶ E ⊗ E'`,
`ε : E' ⊗ E ⟶ 𝟙`), the functor `- ⊗ E` has two right adjoints, `- ⊗ E'` and `H(E, -)`, so
there is a canonical isomorphism

`θ_M : M ⊗ E' ⟶ H(E, M)`,

the transpose of the contraction `(M ⊗ E') ⊗ E ⟶ M ⊗ (E' ⊗ E) ⟶ M ⊗ 𝟙 ⟶ M`.

For a monoidal functor `F : C ⥤ D` between two such categories and a comparison
`m : T₁ ⋙ F ≅ F.prod F ⋙ T₂` matching the oplax structure `δ` of `F` under `b`, the canonical
map `c : F(H₁(E, M)) ⟶ H₂(F E, F M)` of `homComparison` is computed by `θ`: with `F E'` the left
dual of `F E` given by `CategoryTheory.ExactPairing.map`,

`F(θ_M) ≫ c = δ_{M, E'} ≫ θ'_{F M}`.

This is the abstract form of the statement that, for a perfect `E` on a ringed space, the
canonical map of Stacks 08I3 `Lh^*R𝓗om(E, M) ⟶ R𝓗om(Lh^*E, Lh^*M)` is, under the
identifications `R𝓗om(E, -) ≅ - ⊗^L E^∨` of Stacks 08DQ, the monoidality comparison of
Stacks 079U.

Declarations are in the namespace `Stacks.Cohomology.DerivedInternalHomPullback.Transpose`.

## Main definitions

* `pairingToInternalHom`: the map `θ`.

## Main results

* `isIso_pairingToInternalHom`: `θ` is an isomorphism.
* `pairingToInternalHom_naturality`: `θ` is natural in `M` when `e` is natural in its target.
* `map_pairingToInternalHom_comp_homComparison`: the compatibility `F(θ_M) ≫ c = δ ≫ θ'`.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedInternalHomPullback.Transpose

section OneCategory

variable {C : Type*} [Category C] [mC : MonoidalCategory C]
  (H : Cᵒᵖ ⥤ C ⥤ C) (T : C × C ⥤ C)
  (e : ∀ A B M : C, (A ⟶ (H.obj (op B)).obj M) ≃ (T.obj (A, B) ⟶ M))
  (b : ∀ A B : C, A ⊗ B ≅ T.obj (A, B))

/-- **The canonical map `θ : M ⊗ E' ⟶ H(E, M)` out of a left dual.** For an exact pairing
`(E, E')`, the transpose under `e` of the contraction `(M ⊗ E') ⊗ E ⟶ M` against the
evaluation `ε : E' ⊗ E ⟶ 𝟙`, read on `T` through `b`. -/
def pairingToInternalHom (E E' : C) [pE : ExactPairing E E'] (M : C) :
    M ⊗ E' ⟶ (H.obj (op E)).obj M :=
  (e (M ⊗ E') E M).symm
    ((b (M ⊗ E') E).inv ≫ (tensorRightHomEquiv (M ⊗ E') E E' M).symm (𝟙 _))

variable {H T e b}

/-- The transpose of `θ_M` is the contraction. -/
theorem e_pairingToInternalHom (E E' : C) [pE : ExactPairing E E'] (M : C) :
    e (M ⊗ E') E M (pairingToInternalHom H T e b E E' M) =
      (b (M ⊗ E') E).inv ≫ (tensorRightHomEquiv (M ⊗ E') E E' M).symm (𝟙 _) :=
  (e (M ⊗ E') E M).apply_symm_apply _

/-- Precomposing `θ_M` with `x : Z ⟶ M ⊗ E'` gives the transpose of the contraction of `x`. -/
theorem e_comp_pairingToInternalHom
    (hn : TensorHomEquivNaturalLeft H T e)
    (hb : ∀ {A A' : C} (f : A ⟶ A') (B : C),
      f ▷ B ≫ (b A' B).hom = (b A B).hom ≫ T.map (f ×ₘ 𝟙 B))
    (E E' : C) [pE : ExactPairing E E'] (M Z : C) (x : Z ⟶ M ⊗ E') :
    e Z E M (x ≫ pairingToInternalHom H T e b E E' M) =
      (b Z E).inv ≫ (tensorRightHomEquiv Z E E' M).symm x := by
  rw [hn _ _ _ _ x, e_pairingToInternalHom]
  have hb' : T.map (x ×ₘ 𝟙 E) ≫ (b (M ⊗ E') E).inv = (b Z E).inv ≫ x ▷ E := by
    rw [Iso.comp_inv_eq, Category.assoc, hb, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hb', Category.assoc, ← tensorRightHomEquiv_symm_naturality,
    Category.comp_id]

/-- **`θ` is an isomorphism**: precomposition with it is the composite of the bijection `e`,
the isomorphism `b` and the bijection `tensorRightHomEquiv` of the exact pairing. -/
theorem isIso_pairingToInternalHom
    (hn : TensorHomEquivNaturalLeft H T e)
    (hb : ∀ {A A' : C} (f : A ⟶ A') (B : C),
      f ▷ B ≫ (b A' B).hom = (b A B).hom ≫ T.map (f ×ₘ 𝟙 B))
    (E E' : C) [pE : ExactPairing E E'] (M : C) :
    IsIso (pairingToInternalHom H T e b E E' M) := by
  rw [isIso_iff_yoneda_map_bijective]
  intro Z
  have key : (fun x : Z ⟶ M ⊗ E' => x ≫ pairingToInternalHom H T e b E E' M) =
      (e Z E M).symm ∘ (fun y => (b Z E).inv ≫ y) ∘ (tensorRightHomEquiv Z E E' M).symm := by
    funext x
    apply (e Z E M).injective
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
      e_comp_pairingToInternalHom hn hb E E' M Z x
  rw [key]
  refine (e Z E M).symm.bijective.comp (Function.Bijective.comp ?_
    (tensorRightHomEquiv Z E E' M).symm.bijective)
  refine ⟨fun y₁ y₂ h => ?_, fun y => ⟨(b Z E).hom ≫ y, Iso.inv_hom_id_assoc _ _⟩⟩
  simpa using congrArg (fun t => (b Z E).hom ≫ t) h

/-- **`θ` is natural in `M`**, when `e` is natural in its target. -/
theorem pairingToInternalHom_naturality
    (hn : TensorHomEquivNaturalLeft H T e)
    (ht : EquivalenceTranspose.CurriedTargetNatural H T e)
    (hb : ∀ {A A' : C} (f : A ⟶ A') (B : C),
      f ▷ B ≫ (b A' B).hom = (b A B).hom ≫ T.map (f ×ₘ 𝟙 B))
    (E E' : C) [pE : ExactPairing E E'] {M M' : C} (f : M ⟶ M') :
    pairingToInternalHom H T e b E E' M ≫ (H.obj (op E)).map f =
      f ▷ E' ≫ pairingToInternalHom H T e b E E' M' := by
  apply (e (M ⊗ E') E M').injective
  rw [ht _ _ _ _ f, e_comp_pairingToInternalHom hn hb, e_pairingToInternalHom, Category.assoc]
  congr 1
  apply (tensorRightHomEquiv (M ⊗ E') E E' M').injective
  rw [tensorRightHomEquiv_naturality, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    Category.id_comp]

end OneCategory

section TwoCategories

variable {C D : Type*} [Category C] [Category D] [mC : MonoidalCategory C] [mD : MonoidalCategory D]
  (F : C ⥤ D) [mF : F.Monoidal]
  {H₁ : Cᵒᵖ ⥤ C ⥤ C} {H₂ : Dᵒᵖ ⥤ D ⥤ D} {T₁ : C × C ⥤ C} {T₂ : D × D ⥤ D}
  {e₁ : ∀ A B M : C, (A ⟶ (H₁.obj (op B)).obj M) ≃ (T₁.obj (A, B) ⟶ M)}
  {e₂ : ∀ A B M : D, (A ⟶ (H₂.obj (op B)).obj M) ≃ (T₂.obj (A, B) ⟶ M)}
  {m : T₁ ⋙ F ≅ F.prod F ⋙ T₂}
  {b₁ : ∀ A B : C, A ⊗ B ≅ T₁.obj (A, B)} {b₂ : ∀ A B : D, A ⊗ B ≅ T₂.obj (A, B)}

/-- The contraction against the evaluation of the image pairing is the image of the contraction,
read through the structure maps of the monoidal functor. -/
theorem μ_comp_map_contraction (E E' M : C) [pE : ExactPairing E E'] :
    letI := ExactPairing.map F E E'
    μ F (M ⊗ E') E ≫ F.map ((tensorRightHomEquiv (M ⊗ E') E E' M).symm (𝟙 _)) =
      δ F M E' ▷ F.obj E ≫
        (tensorRightHomEquiv (F.obj M ⊗ F.obj E') (F.obj E) (F.obj E') (F.obj M)).symm
          (𝟙 _) := by
  let := ExactPairing.map F E E'
  simp only [tensorRightHomEquiv, Equiv.coe_fn_symm_mk, id_whiskerRight, Category.id_comp,
    ExactPairing.map_evaluation, Functor.map_comp, Functor.Monoidal.map_associator,
    Functor.Monoidal.map_whiskerLeft, Functor.Monoidal.map_rightUnitor,
    MonoidalCategory.whiskerLeft_comp, Category.assoc, Functor.Monoidal.μ_δ_assoc]

/-- **The comparison of a monoidal functor with the internal hom out of a dualizable object.**
With `θ` the map `pairingToInternalHom` on each side, the image pairing on the target side, and
`c` the comparison `homComparison` built from a tensor comparison `m` which matches `δ` under
the identifications `b₁`, `b₂`:

`F(θ_M) ≫ c_{E, M} = δ_{M, E'} ≫ θ'_{F M}`. -/
theorem map_pairingToInternalHom_comp_homComparison
    (hn₁ : TensorHomEquivNaturalLeft H₁ T₁ e₁)
    (hn₂ : TensorHomEquivNaturalLeft H₂ T₂ e₂)
    (hb₂ : ∀ {A A' : D} (f : A ⟶ A') (B : D),
      f ▷ B ≫ (b₂ A' B).hom = (b₂ A B).hom ≫ T₂.map (f ×ₘ 𝟙 B))
    (hm : ∀ A B : C, F.map (b₁ A B).hom ≫ m.hom.app (A, B) =
      δ F A B ≫ (b₂ (F.obj A) (F.obj B)).hom)
    (E E' : C) [pE : ExactPairing E E'] (M : C) :
    letI := ExactPairing.map F E E'
    F.map (pairingToInternalHom H₁ T₁ e₁ b₁ E E' M) ≫
        homComparison F H₁ H₂ T₁ T₂ e₁ e₂ m E M =
      δ F M E' ≫ pairingToInternalHom H₂ T₂ e₂ b₂ (F.obj E) (F.obj E') (F.obj M) := by
  let := ExactPairing.map F E E'
  have hm' : m.inv.app (M ⊗ E', E) ≫ F.map (b₁ (M ⊗ E') E).inv =
      (b₂ (F.obj (M ⊗ E')) (F.obj E)).inv ≫ μ F (M ⊗ E') E := by
    calc m.inv.app (M ⊗ E', E) ≫ F.map (b₁ (M ⊗ E') E).inv
        = (b₂ (F.obj (M ⊗ E')) (F.obj E)).inv ≫ μ F (M ⊗ E') E ≫
            (δ F (M ⊗ E') E ≫ (b₂ (F.obj (M ⊗ E')) (F.obj E)).hom) ≫
              m.inv.app (M ⊗ E', E) ≫ F.map (b₁ (M ⊗ E') E).inv := by
          simp
      _ = (b₂ (F.obj (M ⊗ E')) (F.obj E)).inv ≫ μ F (M ⊗ E') E := by
          rw [← hm (M ⊗ E') E]
          simp [← Functor.map_comp]
  have hnat := m.inv.naturality (X := (M ⊗ E', E)) (Y := ((H₁.obj (op E)).obj M, E))
    (pairingToInternalHom H₁ T₁ e₁ b₁ E E' M ×ₘ 𝟙 E)
  dsimp only [Functor.comp_map, Functor.prod_map] at hnat
  rw [CategoryTheory.Functor.map_id] at hnat
  apply (e₂ _ _ _).injective
  calc e₂ _ _ _ (F.map (pairingToInternalHom H₁ T₁ e₁ b₁ E E' M) ≫
          homComparison F H₁ H₂ T₁ T₂ e₁ e₂ m E M)
      = T₂.map (F.map (pairingToInternalHom H₁ T₁ e₁ b₁ E E' M) ×ₘ 𝟙 (F.obj E)) ≫
          m.inv.app ((H₁.obj (op E)).obj M, E) ≫ F.map (evaluation H₁ T₁ e₁ E M) := by
        rw [hn₂ _ _ _ _ (F.map (pairingToInternalHom H₁ T₁ e₁ b₁ E E' M)), homComparison_adjoint]
        rfl
    _ = m.inv.app (M ⊗ E', E) ≫ F.map (e₁ _ E M (pairingToInternalHom H₁ T₁ e₁ b₁ E E' M)) := by
        rw [← Category.assoc, hnat, Category.assoc, ← Functor.map_comp]
        congr 2
        rw [evaluation, ← hn₁ _ _ _ _ (pairingToInternalHom H₁ T₁ e₁ b₁ E E' M), Category.comp_id]
    _ = (b₂ (F.obj (M ⊗ E')) (F.obj E)).inv ≫ δ F M E' ▷ F.obj E ≫
          (tensorRightHomEquiv (F.obj M ⊗ F.obj E') (F.obj E) (F.obj E') (F.obj M)).symm
            (𝟙 _) := by
        rw [e_pairingToInternalHom, Functor.map_comp, ← Category.assoc, hm', Category.assoc,
          μ_comp_map_contraction]
    _ = e₂ _ _ _ (δ F M E' ≫
          pairingToInternalHom H₂ T₂ e₂ b₂ (F.obj E) (F.obj E') (F.obj M)) := by
        rw [e_comp_pairingToInternalHom hn₂ hb₂, ← tensorRightHomEquiv_symm_naturality,
          Category.comp_id]

end TwoCategories

end Stacks.Cohomology.DerivedInternalHomPullback.Transpose
