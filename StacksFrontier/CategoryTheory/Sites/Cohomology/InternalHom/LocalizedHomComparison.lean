module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.MonoidalHomComparison

/-!
# Localizing the comparison of a monoidal functor with the derived internal Hom

Let `Φ : D(O_X) ⥤ D(O_Y)` be a monoidal triangulated functor between derived categories of
ringed sites, let `ρ : D(O_X) ⥤ D(O_{X'})` and `ρ' : D(O_Y) ⥤ D(O_{Y'})` be monoidal functors —
in the application, restrictions to an open `U` of the Zariski site and to its image on the
small étale site — and let `ρ` have a fully faithful left adjoint `L` (extension by zero). If
`ρ' ∘ Φ` kills every object `ρ` kills, the comparison of `Φ` with the derived internal Hom can be
read on `X'` and `Y'`: there is a monoidal functor

`Φ_U = L ⋙ Φ ⋙ ρ' : D(O_{X'}) ⥤ D(O_{Y'})`

with a monoidal isomorphism `ρ ⋙ Φ_U ≅ Φ ⋙ ρ'`, and when the comparisons of `ρ` and `ρ'` are
isomorphisms the restriction along `ρ'` of the comparison of `Φ` at `(A, B)` is invertible
(after any functor) exactly when the comparison of `Φ_U` at `(ρ A, ρ B)` is.

The monoidal structure of `Φ_U` is the one doctrinal adjunction gives: `L`, the left adjoint of
the monoidal functor `ρ`, is oplax monoidal (`CategoryTheory.Adjunction.leftAdjointOplaxMonoidal`),
so `Φ_U` is oplax monoidal, and its structure maps are invertible because `ρ` carries those of `L`
to isomorphisms and `ρ' ∘ Φ` inverts every morphism `ρ` inverts.

This is the step "we may work locally" of the proof of Stacks 08JP, done without a morphism of
ringed topoi on the slices.

## Main definitions

* `AlgebraicGeometry.RingedSite.localizedFunctorMonoidal`: the monoidal structure of
  `Φ_U = L ⋙ Φ ⋙ ρ'`.
* `AlgebraicGeometry.RingedSite.localizedFunctorIso`: the isomorphism `ρ ⋙ Φ_U ≅ Φ ⋙ ρ'`.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_map_map_of_isIso_map`: `ρ' ∘ Φ` inverts what `ρ` inverts.
* `AlgebraicGeometry.RingedSite.localizedFunctorIso_hom_δ`: the isomorphism is monoidal.
* `AlgebraicGeometry.RingedSite.isIso_map_map_homComparisonMonoidal_iff`: the transfer of
  invertibility of the comparison.

## References

* [Stacks Project, Tag 08JP](https://stacks.math.columbia.edu/tag/08JP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedInternalHomPullback
open Functor.LaxMonoidal Functor.OplaxMonoidal

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal

section Congr

variable {X Y : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]

/-- **The comparison is invariant under an isomorphism compatible with the tensorators**, in the
form `c ≫ δ' = δ ≫ (c ⊗ c)`, which does not ask for compatibility with the units. -/
theorem homComparisonMonoidal_congr_of_δ
    {P P' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    [P.Monoidal] [P'.Monoidal] (c : P ≅ P')
    (hc : ∀ A B, c.hom.app (A ⊗ B) ≫ δ P' A B = δ P A B ≫ (c.hom.app A ⊗ₘ c.hom.app B))
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    homComparisonMonoidal P' A B =
      c.inv.app _ ≫ homComparisonMonoidal P A B ≫
        ((derivedSheafHomBifunctor Y).map (c.inv.app A).op).app (P.obj B) ≫
          ((derivedSheafHomBifunctor Y).obj (op (P'.obj A))).map (c.hom.app B) := by
  refine Transpose.homComparison_congr' _ _ _ _ _ _ _ _ c (monoidalCurryEquiv_naturalLeft Y)
    (monoidalCurryEquiv_dinatural Y) (monoidalCurryEquiv_targetNatural Y) (fun W => ?_) A B
  rw [monoidalTensorIso_hom_app, monoidalTensorIso_hom_app, monoidalTensorPair_map_prod]
  exact hc W.1 W.2

end Congr

section Localized

variable {X X' Y Y' : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X'.J AddCommGrpCat.{u}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y'.J AddCommGrpCat.{u}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (Φ : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
  (ρ : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)))
  (ρ' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O)))
  {L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) ⥤
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
  (adj : L ⊣ ρ)

section Inverts

variable [Φ.CommShift ℤ] [Φ.IsTriangulated] [ρ.CommShift ℤ] [ρ.IsTriangulated]
  [ρ'.CommShift ℤ] [ρ'.IsTriangulated]

/-- **`ρ' ∘ Φ` inverts every morphism `ρ` inverts**, as soon as it kills every object `ρ`
kills: the cone of such a morphism is killed by `ρ`. -/
theorem isIso_map_map_of_isIso_map
    (hK : ∀ K, IsZero (ρ.obj K) → IsZero (ρ'.obj (Φ.obj K)))
    {A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (f : A ⟶ B) (hf : IsIso (ρ.map f)) : IsIso (ρ'.map (Φ.map f)) := by
  obtain ⟨C, g, h, hT⟩ := distinguished_cocone_triangle f
  have hC : IsZero (ρ.obj C) :=
    Triangle.isZero₃_of_isIso₁ _ (ρ.map_distinguished _ hT) hf
  have hT' := (Φ ⋙ ρ').map_distinguished _ hT
  exact (Triangle.isZero₃_iff_isIso₁ _ hT').1 (hK C hC)

end Inverts

variable [ρ.Monoidal] [IsIso adj.unit]

/-- `ρ` carries the counit of `L ⊣ ρ` to isomorphisms, the unit being invertible. -/
instance isIso_map_counit_app (A) : IsIso (ρ.map (adj.counit.app A)) := by
  have : IsIso (adj.unit.app (ρ.obj A) ≫ ρ.map (adj.counit.app A)) := by
    rw [adj.right_triangle_components A]
    exact IsIso.id _
  exact IsIso.of_isIso_comp_left (adj.unit.app (ρ.obj A)) _

/-- `ρ` carries the oplax unit of `L` to an isomorphism. -/
theorem isIso_map_η :
    letI := adj.leftAdjointOplaxMonoidal
    IsIso (ρ.map (η L)) := by
  let := adj.leftAdjointOplaxMonoidal
  rw [Adjunction.leftAdjointOplaxMonoidal_η, Adjunction.homEquiv_counit, Functor.map_comp]
  infer_instance

/-- `ρ` carries the oplax tensorator of `L` to isomorphisms. -/
theorem isIso_map_δ (A B) :
    letI := adj.leftAdjointOplaxMonoidal
    IsIso (ρ.map (δ L A B)) := by
  let := adj.leftAdjointOplaxMonoidal
  rw [Adjunction.leftAdjointOplaxMonoidal_δ, Adjunction.homEquiv_counit, Functor.map_comp]
  infer_instance

variable [Φ.Monoidal] [ρ'.Monoidal]
  [Φ.CommShift ℤ] [Φ.IsTriangulated] [ρ.CommShift ℤ] [ρ.IsTriangulated]
  [ρ'.CommShift ℤ] [ρ'.IsTriangulated]

/-- **The monoidal structure of `Φ_U`.** `L` is oplax monoidal as the left adjoint of the
monoidal functor `ρ`, so `L ⋙ Φ ⋙ ρ'` is oplax monoidal; its unit and tensorator are carried by
`ρ` to isomorphisms, hence are inverted by `ρ' ∘ Φ`, so the structure is strong. -/
@[instance_reducible]
def localizedFunctorMonoidal (hK : ∀ K, IsZero (ρ.obj K) → IsZero (ρ'.obj (Φ.obj K))) :
    (L ⋙ Φ ⋙ ρ').Monoidal :=
  letI := adj.leftAdjointOplaxMonoidal
  haveI : IsIso (η (L ⋙ Φ ⋙ ρ')) := by
    have h := isIso_map_map_of_isIso_map Φ ρ ρ' hK _ (isIso_map_η ρ adj)
    simp only [Functor.OplaxMonoidal.comp_η]
    exact IsIso.comp_isIso' h inferInstance
  haveI : ∀ A B, IsIso (δ (L ⋙ Φ ⋙ ρ') A B) := fun A B => by
    have h := isIso_map_map_of_isIso_map Φ ρ ρ' hK _ (isIso_map_δ ρ adj A B)
    simp only [Functor.OplaxMonoidal.comp_δ]
    exact IsIso.comp_isIso' h inferInstance
  (Functor.CoreMonoidal.ofOplaxMonoidal _).toMonoidal

/-- The tensorator of `localizedFunctorMonoidal` is the oplax tensorator of the composite. -/
theorem localizedFunctorMonoidal_δ
    (hK : ∀ K, IsZero (ρ.obj K) → IsZero (ρ'.obj (Φ.obj K))) (A B) :
    letI := localizedFunctorMonoidal Φ ρ ρ' adj hK
    δ (L ⋙ Φ ⋙ ρ') A B =
      (Φ ⋙ ρ').map (letI := adj.leftAdjointOplaxMonoidal; δ L A B) ≫
        δ (Φ ⋙ ρ') (L.obj A) (L.obj B) :=
  rfl

/-- **The isomorphism `ρ ⋙ Φ_U ≅ Φ ⋙ ρ'`**: the counit of `L ⊣ ρ` carried by `ρ' ∘ Φ`. -/
def localizedFunctorIso (hK : ∀ K, IsZero (ρ.obj K) → IsZero (ρ'.obj (Φ.obj K))) :
    ρ ⋙ L ⋙ Φ ⋙ ρ' ≅ Φ ⋙ ρ' :=
  NatIso.ofComponents
    (fun A => @asIso _ _ _ _ ((Φ ⋙ ρ').map (adj.counit.app A))
      (isIso_map_map_of_isIso_map Φ ρ ρ' hK _ inferInstance))
    (fun {A B} f => by
      simp only [Functor.comp_map, asIso_hom]
      rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
      congr 2
      exact adj.counit.naturality f)

omit [ρ.Monoidal] [Φ.Monoidal] [ρ'.Monoidal] in
/-- The component of `localizedFunctorIso` at `A` is the image under `Φ ⋙ ρ'` of the counit of
`L ⊣ ρ` at `A`. -/
@[simp]
theorem localizedFunctorIso_hom_app
    (hK : ∀ K, IsZero (ρ.obj K) → IsZero (ρ'.obj (Φ.obj K))) (A) :
    (localizedFunctorIso Φ ρ ρ' adj hK).hom.app A = (Φ ⋙ ρ').map (adj.counit.app A) := rfl

/-- **The isomorphism `ρ ⋙ Φ_U ≅ Φ ⋙ ρ'` is compatible with the tensorators.** This is the
compatibility of the counit of a doctrinal adjunction with the tensorators,
`CategoryTheory.Adjunction.map_μ_comp_counit_app_tensor`, carried by `ρ' ∘ Φ`. -/
theorem localizedFunctorIso_hom_δ (hK : ∀ K, IsZero (ρ.obj K) → IsZero (ρ'.obj (Φ.obj K)))
    (A B) :
    letI := localizedFunctorMonoidal Φ ρ ρ' adj hK
    (localizedFunctorIso Φ ρ ρ' adj hK).hom.app (A ⊗ B) ≫ δ (Φ ⋙ ρ') A B =
      ((L ⋙ Φ ⋙ ρ').map (δ ρ A B) ≫ δ (L ⋙ Φ ⋙ ρ') (ρ.obj A) (ρ.obj B)) ≫
        ((localizedFunctorIso Φ ρ ρ' adj hK).hom.app A ⊗ₘ
          (localizedFunctorIso Φ ρ ρ' adj hK).hom.app B) := by
  let := adj.leftAdjointOplaxMonoidal
  let := localizedFunctorMonoidal Φ ρ ρ' adj hK
  have h := Adjunction.map_μ_comp_counit_app_tensor adj A B
  have hc : adj.counit.app (A ⊗ B) =
      L.map (δ ρ A B) ≫ δ L (ρ.obj A) (ρ.obj B) ≫ (adj.counit.app A ⊗ₘ adj.counit.app B) := by
    rw [← h, ← Category.assoc, ← CategoryTheory.Functor.map_comp, Functor.Monoidal.δ_μ,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have key := Functor.OplaxMonoidal.δ_natural (Φ ⋙ ρ') (adj.counit.app A) (adj.counit.app B)
  dsimp only [Functor.comp_obj, Functor.id_obj] at key
  have e : (Φ ⋙ ρ').map (adj.counit.app (A ⊗ B)) ≫ δ (Φ ⋙ ρ') A B =
      (Φ ⋙ ρ').map (L.map (δ ρ A B)) ≫ (Φ ⋙ ρ').map (δ L (ρ.obj A) (ρ.obj B)) ≫
        δ (Φ ⋙ ρ') (L.obj (ρ.obj A)) (L.obj (ρ.obj B)) ≫
          ((Φ ⋙ ρ').map (adj.counit.app A) ⊗ₘ (Φ ⋙ ρ').map (adj.counit.app B)) := by
    rw [key, hc, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      Category.assoc, Category.assoc]
  rw [localizedFunctorIso_hom_app, localizedFunctorIso_hom_app, localizedFunctorIso_hom_app,
    localizedFunctorMonoidal_δ]
  exact e.trans (by simp only [Functor.comp_map, Category.assoc])

end Localized

section Transfer

variable {X X' Y Y' : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X'.J AddCommGrpCat.{u}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y'.J AddCommGrpCat.{u}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X'.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X'.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X'.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X'.O)
      (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y'.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y'.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y'.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y'.O)
      (ComplexShape.up ℤ)]
  (Φ : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
  (ρ : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)))
  (ρ' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O)))
  {L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) ⥤
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
  (adj : L ⊣ ρ) [ρ.Monoidal] [IsIso adj.unit] [Φ.Monoidal] [ρ'.Monoidal]
  [Φ.CommShift ℤ] [Φ.IsTriangulated] [ρ.CommShift ℤ] [ρ.IsTriangulated]
  [ρ'.CommShift ℤ] [ρ'.IsTriangulated]

/-- **The comparison of `Φ` restricted along `ρ'` is the comparison of `Φ_U`**, up to
isomorphisms, when the comparisons of `ρ` and of `ρ'` are invertible: after any functor `Ψ`,
the first is invertible exactly when the second is. The two are the two factorizations of the
comparison of `Φ ⋙ ρ' ≅ ρ ⋙ Φ_U` (`homComparisonMonoidal_comp`,
`homComparisonMonoidal_congr_of_δ`). -/
theorem isIso_map_map_homComparisonMonoidal_iff
    (hK : ∀ K, IsZero (ρ.obj K) → IsZero (ρ'.obj (Φ.obj K)))
    (hρ : ∀ A B, IsIso (homComparisonMonoidal ρ A B))
    (hρ' : ∀ A B, IsIso (homComparisonMonoidal ρ' A B))
    {E : Type*} [Category E]
    (Ψ : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O)) ⥤ E)
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    letI := localizedFunctorMonoidal Φ ρ ρ' adj hK
    IsIso (Ψ.map (ρ'.map (homComparisonMonoidal Φ A B))) ↔
      IsIso (Ψ.map (homComparisonMonoidal (L ⋙ Φ ⋙ ρ') (ρ.obj A) (ρ.obj B))) := by
  let := localizedFunctorMonoidal Φ ρ ρ' adj hK
  have h₁ := homComparisonMonoidal_comp Φ ρ' A B
  have h₂ := homComparisonMonoidal_comp ρ (L ⋙ Φ ⋙ ρ') A B
  have h₃ := homComparisonMonoidal_congr_of_δ (localizedFunctorIso Φ ρ ρ' adj hK)
    (fun A B => localizedFunctorIso_hom_δ Φ ρ ρ' adj hK A B) A B
  have := hρ A B
  have := hρ' (Φ.obj A) (Φ.obj B)
  have e₁ : IsIso (Ψ.map (ρ'.map (homComparisonMonoidal Φ A B))) ↔
      IsIso (Ψ.map (homComparisonMonoidal (Φ ⋙ ρ') A B)) :=
    (Transpose.isIso_map_iff_of_eq_conj Ψ _ _ (𝟙 _) (homComparisonMonoidal ρ' (Φ.obj A) (Φ.obj B))
      (by rw [h₁, Category.id_comp])).symm
  have e₂ : IsIso (Ψ.map (homComparisonMonoidal (Φ ⋙ ρ') A B)) ↔
      IsIso (Ψ.map (homComparisonMonoidal (ρ ⋙ L ⋙ Φ ⋙ ρ') A B)) :=
    Transpose.isIso_map_iff_of_eq_conj Ψ (homComparisonMonoidal (Φ ⋙ ρ') A B)
      (homComparisonMonoidal (ρ ⋙ L ⋙ Φ ⋙ ρ') A B)
      ((localizedFunctorIso Φ ρ ρ' adj hK).inv.app _)
      (((derivedSheafHomBifunctor Y').map
          ((localizedFunctorIso Φ ρ ρ' adj hK).inv.app A).op).app _ ≫
        ((derivedSheafHomBifunctor Y').obj (op ((Φ ⋙ ρ').obj A))).map
          ((localizedFunctorIso Φ ρ ρ' adj hK).hom.app B)) h₃
  have e₃ : IsIso (Ψ.map (homComparisonMonoidal (ρ ⋙ L ⋙ Φ ⋙ ρ') A B)) ↔
      IsIso (Ψ.map (homComparisonMonoidal (L ⋙ Φ ⋙ ρ') (ρ.obj A) (ρ.obj B))) :=
    Transpose.isIso_map_iff_of_eq_conj Ψ _ _ ((L ⋙ Φ ⋙ ρ').map (homComparisonMonoidal ρ A B))
      (𝟙 _) (by rw [h₂, Category.comp_id])
  exact e₁.trans (e₂.trans e₃)

end Transfer

end AlgebraicGeometry.RingedSite

end
