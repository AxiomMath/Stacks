module

public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ProZeroCover

/-!
# Pro-isomorphisms of inverse systems of complexes are local on a quasi-compact scheme

Let `X` be a quasi-compact scheme and let `φ : (A_n) ⟶ (B_n)` be a morphism of inverse systems
of complexes of `𝒪_X`-modules. We show that if every point of `X` lies in the image of an open
immersion `f : Y ⟶ X` such that the restricted morphism `(A_n|_Y) ⟶ (B_n|_Y)` is an isomorphism
of pro-objects of `D(𝒪_Y)`, then `(A_n) ⟶ (B_n)` is an isomorphism of pro-objects of `D(𝒪_X)`.

The mapping cones `C_n` of the `φ_n` form an inverse system of distinguished triangles
`A_n ⟶ B_n ⟶ C_n ⟶ A_n[1]` in `D(𝒪_X)`. Restriction along an open immersion `f` is an exact
functor, so it carries these to an inverse system of distinguished triangles in `D(𝒪_Y)` whose
first morphisms are the restrictions of the `φ_n`; when those form an isomorphism of pro-objects,
the third terms `C_n|_Y` form a pro-zero system
(`CategoryTheory.Pretriangulated.proZero_π₃_of_proInverse_mor₁`). Being pro-zero is local on a
quasi-compact scheme (`AlgebraicGeometry.proZero_of_isOpenImmersion_cover`), so `(C_n)` is
pro-zero in `D(𝒪_X)`, and [Stacks, Tag 0G3C]
(`CategoryTheory.Pretriangulated.exists_proInverse_mor₁_of_proZero_π₃`) gives the conclusion.

## Main definitions

* `CochainComplex.mappingCone.triangleFunctor`: the system of mapping cone triangles of a natural
  transformation between diagrams of cochain complexes.

## Main results

* `AlgebraicGeometry.proInverse_whiskerRight_Q_of_cover`: a morphism of inverse systems of
  complexes on a quasi-compact scheme which is an isomorphism of pro-objects of the derived
  category locally on an open covering is one globally.

## Implementation notes

Everything is at `CategoryTheory.HasDerivedCategory.standard`. That a morphism `φ : A ⟶ B` of
systems indexed by `ℕᵒᵖ` is an isomorphism of pro-objects is spelled out as: for every `n` there
are `m ≥ n` and a morphism `s : B_m ⟶ A_n` such that `A_m ⟶ B_m ⟶ A_n` and `B_m ⟶ A_n ⟶ B_n`
are the transition morphisms.

## References

* [Stacks Project, Tag 0G3C](https://stacks.math.columbia.edu/tag/0G3C)
* [Stacks Project, Tag 0G4U](https://stacks.math.columbia.edu/tag/0G4U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace CochainComplex.mappingCone

variable {J C : Type*} [Category* J] [Category* C] [Preadditive C] [HasBinaryBiproducts C]
  {A B : J ⥤ CochainComplex C ℤ}

/-- The diagram of mapping cone triangles `A_j ⟶ B_j ⟶ cone(φ_j) ⟶ A_j⟦1⟧` of a natural
transformation `φ : A ⟶ B` between diagrams of cochain complexes, with the transition morphisms
of triangles induced by the naturality squares of `φ`. -/
@[simps]
def triangleFunctor (φ : A ⟶ B) : J ⥤ Triangle (CochainComplex C ℤ) where
  obj j := triangle (φ.app j)
  map {j k} g := triangleMap (φ.app j) (φ.app k) (A.map g) (B.map g) (φ.naturality g).symm
  map_id j := by
    have key : ∀ (a : A.obj j ⟶ A.obj j) (b : B.obj j ⟶ B.obj j) (ha : a = 𝟙 _)
        (hb : b = 𝟙 _) (comm : φ.app j ≫ b = a ≫ φ.app j),
        triangleMap (φ.app j) (φ.app j) a b comm = 𝟙 _ := by
      rintro _ _ rfl rfl _
      exact Triangle.hom_ext _ _ rfl rfl (map_id (φ.app j))
    exact key _ _ (A.map_id j) (B.map_id j) _
  map_comp {j k l} g g' := by
    have key : ∀ (a : A.obj j ⟶ A.obj l) (b : B.obj j ⟶ B.obj l)
        (ha : a = A.map g ≫ A.map g') (hb : b = B.map g ≫ B.map g')
        (comm : φ.app j ≫ b = a ≫ φ.app l),
        triangleMap (φ.app j) (φ.app l) a b comm =
          triangleMap (φ.app j) (φ.app k) (A.map g) (B.map g) (φ.naturality g).symm ≫
            triangleMap (φ.app k) (φ.app l) (A.map g') (B.map g') (φ.naturality g').symm := by
      rintro _ _ rfl rfl _
      exact Triangle.hom_ext _ _ rfl rfl (map_comp (φ.app j) (φ.app k) (φ.app l) _ _
        (φ.naturality g).symm _ _ (φ.naturality g').symm)
    exact key _ _ (A.map_comp g g') (B.map_comp g g') _

end CochainComplex.mappingCone

namespace AlgebraicGeometry

/-- **Pro-isomorphisms of systems of complexes are local on a quasi-compact scheme.** Let `X` be
a quasi-compact scheme and `φ : A ⟶ B` a morphism of inverse systems of complexes of
`𝒪_X`-modules. Suppose every point of `X` lies in the image of an open immersion `f : Y ⟶ X`
such that the restriction of `φ` along `f` is an isomorphism of pro-objects of `D(𝒪_Y)`: for every
`n` there are `m ≥ n` and `s : B_m|_Y ⟶ A_n|_Y` such that `A_m|_Y ⟶ B_m|_Y ⟶ A_n|_Y` and
`B_m|_Y ⟶ A_n|_Y ⟶ B_n|_Y` are the transition morphisms. Then `φ` is an isomorphism of
pro-objects of `D(𝒪_X)`, in the same sense. -/
public theorem proInverse_whiskerRight_Q_of_cover {X : Scheme.{u}} [CompactSpace X]
    {A B : ℕᵒᵖ ⥤ CochainComplex X.Modules ℤ} (φ : A ⟶ B)
    (h : ∀ x : X, ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (_ : IsOpenImmersion f), x ∈ Set.range f.base ∧
      ∀ n : ℕ, ∃ (m : ℕ) (hnm : n ≤ m)
        (s : (B ⋙ (Scheme.Modules.restrictFunctor f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            DerivedCategory.Q).obj (op m) ⟶
          (A ⋙ (Scheme.Modules.restrictFunctor f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            DerivedCategory.Q).obj (op n)),
        (Functor.whiskerRight φ ((Scheme.Modules.restrictFunctor f).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)).app (op m) ≫ s =
          (A ⋙ (Scheme.Modules.restrictFunctor f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            DerivedCategory.Q).map (homOfLE hnm).op ∧
        s ≫ (Functor.whiskerRight φ ((Scheme.Modules.restrictFunctor f).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)).app (op n) =
          (B ⋙ (Scheme.Modules.restrictFunctor f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            DerivedCategory.Q).map (homOfLE hnm).op) :
    ∀ n : ℕ, ∃ (m : ℕ) (hnm : n ≤ m)
      (s : (B ⋙ DerivedCategory.Q).obj (op m) ⟶ (A ⋙ DerivedCategory.Q).obj (op n)),
      (Functor.whiskerRight φ DerivedCategory.Q).app (op m) ≫ s =
        (A ⋙ DerivedCategory.Q).map (homOfLE hnm).op ∧
      s ≫ (Functor.whiskerRight φ DerivedCategory.Q).app (op n) =
        (B ⋙ DerivedCategory.Q).map (homOfLE hnm).op := by
  -- the inverse system of mapping cone triangles in `D(𝒪_X)`
  let T : ℕᵒᵖ ⥤ Triangle (DerivedCategory X.Modules) :=
    CochainComplex.mappingCone.triangleFunctor φ ⋙ DerivedCategory.Q.mapTriangle
  have hT : ∀ j, T.obj j ∈ distTriang _ := fun j =>
    DerivedCategory.mappingCone_triangle_distinguished (φ.app j)
  -- its third terms are pro-zero after restriction to the members of the covering
  have hC := proZero_of_isOpenImmersion_cover (T ⋙ Triangle.π₃) (fun x => by
    obtain ⟨Y, f, hf, hx, hpro⟩ := h x
    refine ⟨Y, f, hf, hx, fun n => ?_⟩
    let F := (Scheme.Modules.restrictFunctor f).mapDerivedCategory
    let e := (Scheme.Modules.restrictFunctor f).mapDerivedCategoryFactors
    let S := T ⋙ F.mapTriangle
    have hS : ∀ j, S.obj j ∈ distTriang _ := fun j => F.map_distinguished _ (hT j)
    have h₁ : ∀ j : ℕᵒᵖ, ∃ (k : ℕᵒᵖ) (g : k ⟶ j) (s : (S.obj k).obj₂ ⟶ (S.obj j).obj₁),
        (S.obj k).mor₁ ≫ s = (S.map g).hom₁ ∧ s ≫ (S.obj j).mor₁ = (S.map g).hom₂ := by
      rintro ⟨j⟩
      obtain ⟨m, hjm, s, hs₁, hs₂⟩ := hpro j
      let Fc := (Scheme.Modules.restrictFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)
      let g : op m ⟶ op j := (homOfLE hjm).op
      have hs₁' : DerivedCategory.Q.map (Fc.map (φ.app (op m))) ≫ s =
          DerivedCategory.Q.map (Fc.map (A.map g)) := hs₁
      have hs₂' : s ≫ DerivedCategory.Q.map (Fc.map (φ.app (op j))) =
          DerivedCategory.Q.map (Fc.map (B.map g)) := hs₂
      have nA : ∀ {K L : CochainComplex X.Modules ℤ} (u : K ⟶ L),
          e.inv.app K ≫ F.map (DerivedCategory.Q.map u) =
            DerivedCategory.Q.map (Fc.map u) ≫ e.inv.app L := fun u =>
        (e.inv.naturality u).symm
      refine ⟨op m, g, e.hom.app (B.obj (op m)) ≫ s ≫ e.inv.app (A.obj (op j)), ?_, ?_⟩
      · change F.map (DerivedCategory.Q.map (φ.app (op m))) ≫
            e.hom.app (B.obj (op m)) ≫ s ≫ e.inv.app (A.obj (op j)) =
          F.map (DerivedCategory.Q.map (A.map g))
        rw [Functor.mapDerivedCategoryFactors_hom_naturality_assoc, ← Category.assoc _ s, hs₁',
          ← Category.assoc, ← Functor.mapDerivedCategoryFactors_hom_naturality, Category.assoc,
          Iso.hom_inv_id_app]
        exact Category.comp_id _
      · change (e.hom.app (B.obj (op m)) ≫ s ≫ e.inv.app (A.obj (op j))) ≫
            F.map (DerivedCategory.Q.map (φ.app (op j))) =
          F.map (DerivedCategory.Q.map (B.map g))
        rw [Category.assoc, Category.assoc, nA, ← Category.assoc s, hs₂', ← nA,
          Iso.hom_inv_id_app_assoc]
    obtain ⟨⟨k⟩, g, hg⟩ := proZero_π₃_of_proInverse_mor₁ S hS h₁ (op n)
    exact ⟨k, leOfHom g.unop, hg⟩)
  -- hence they are pro-zero, and Stacks 0G3C applies
  intro n
  obtain ⟨⟨m⟩, g, s, hs₁, hs₂⟩ := exists_proInverse_mor₁_of_proZero_π₃ T hT (fun j => by
    obtain ⟨m, hjm, hm⟩ := hC j.unop
    exact ⟨op m, (homOfLE hjm).op, hm⟩) (op n)
  exact ⟨m, leOfHom g.unop, s, hs₁, hs₂⟩

end AlgebraicGeometry

end
