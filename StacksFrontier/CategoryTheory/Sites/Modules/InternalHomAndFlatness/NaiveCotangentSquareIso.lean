module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalSequenceSquareIdentity
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentSquare

/-!
# A square of isomorphisms induces an isomorphism of naive cotangent complexes

Stacks 08TX attaches to a commutative square
```
B ──β──▸ B'
▲         ▲
a         a'
│         │
A ──f──▸ A'
```
of sheaves of commutative rings on a site a canonical `B`-linear chain map
`NL_{B/A} ⟶ NL_{B'/A'}`, where the target is read as a complex of sheaves of `B`-modules through
restriction of scalars along `β`
(`Stacks.SheafOfModules.naiveCotangentComplexMapOfSquare`).  This file proves that when `f` and
`β` are isomorphisms that chain map is an isomorphism.

## Main definitions

* `Stacks.SheafOfModules.naiveCotangentComplexIsoOfSquare`: the resulting identification
  `NL_{B/A} ≅ NL_{B'/A'}` in complexes of sheaves of `B`-modules.

## Main results

* `Stacks.SheafOfModules.canonicalFreeAlgebraMapOfSquare_id`, together with
  `Stacks.SheafOfModules.naiveCotangentConormalMapOfSquare_id`,
  `Stacks.SheafOfModules.naiveCotangentTensorMapOfSquare_id` and
  `Stacks.SheafOfModules.naiveCotangentComplexMapOfSquare_id`: the identity square induces the
  identity in each of the three constructions.
* `Stacks.SheafOfModules.naiveCotangentComplexMapOfSquare_comp_inv`: two squares that are
  mutually inverse on both the base and the top ring induce chain maps whose composite is the
  transport along the inverse pair of equations.
* `Stacks.SheafOfModules.isIso_naiveCotangentComplexMapOfSquare`: the chain map attached to a
  square whose two horizontal morphisms are isomorphisms is an isomorphism.

## Implementation notes

The chain map of a square lands in complexes of sheaves of `B`-modules only after restriction of
scalars along `β`, so the composite of the chain maps of a square and of its inverse lands in the
double restriction along `β` and `β'`, and is compared with `NL_{B/A}` by an `eqToHom`.
`Stacks.SheafOfModules.naiveCotangentComplexMapOfSquare_comp_inv` states the source and target of
that `eqToHom` explicitly, so that instance search sees that it is invertible.

## References

* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX)
* [Stacks Project, Tag 08TW](https://stacks.math.columbia.edu/tag/08TW), the naive cotangent
  complex of a homomorphism of sheaves of rings on a site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w z

namespace CategoryTheory

/-- Functors `F` and `G` in opposite directions, a morphism `φ : X ⟶ F.obj Y` and a morphism
`ψ : Y ⟶ G.obj X` whose composites `φ ≫ F.map ψ` and `ψ ≫ G.map φ` are isomorphisms: then `φ`
is an isomorphism. -/
private lemma isIso_of_comp_map_eq {D : Type*} [Category D] {E : Type*} [Category E]
    {F : E ⥤ D} {G : D ⥤ E} {X : D} {Y : E} (φ : X ⟶ F.obj Y) (ψ : Y ⟶ G.obj X)
    {i₁ : X ⟶ F.obj (G.obj X)} {i₂ : Y ⟶ G.obj (F.obj Y)} [IsIso i₁] [IsIso i₂]
    (h1 : φ ≫ F.map ψ = i₁) (h2 : ψ ≫ G.map φ = i₂) : IsIso φ := by
  have h1' : φ ≫ F.map ψ ≫ inv i₁ = 𝟙 X := by
    rw [← Category.assoc, h1, IsIso.hom_inv_id]
  have h2' : ψ ≫ G.map φ ≫ inv i₂ = 𝟙 Y := by
    rw [← Category.assoc, h2, IsIso.hom_inv_id]
  have : IsSplitEpi (F.map ψ ≫ inv i₁) := IsSplitEpi.mk' ⟨φ, h1'⟩
  have : IsSplitMono (F.map ψ) := by
    refine IsSplitMono.mk' ⟨F.map (G.map φ ≫ inv i₂), ?_⟩
    rw [← CategoryTheory.Functor.map_comp, h2', CategoryTheory.Functor.map_id]
  have : Mono (F.map ψ ≫ inv i₁) := mono_comp _ _
  have : IsIso (F.map ψ ≫ inv i₁) := isIso_of_mono_of_isSplitEpi _
  exact IsIso.of_isIso_fac_right h1'

end CategoryTheory

namespace Stacks.SheafOfModules

open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

variable (A B : Sheaf J CommRingCat.{w})

omit [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- A morphism of sheaves of commutative rings read on the underlying presheaves of sets takes
the identity to the identity. -/
lemma underlyingPresheafMap_id : underlyingPresheafMap J B B (𝟙 B) = 𝟙 _ := by
  simp [underlyingPresheafMap]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The morphism `A[B] ⟶ A[B]` of free algebra sheaves attached to the identity square is the
identity. -/
lemma canonicalFreeAlgebraMapOfSquare_id :
    canonicalFreeAlgebraMapOfSquare J A A B B (𝟙 A) (𝟙 B) = 𝟙 _ := by
  refine Stacks.Sites.FreeAlgebra.freeAlgebraSheaf_hom_ext J A _
    (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B) ?_ ?_
  · rw [freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare, Category.id_comp,
      Category.comp_id]
  · rw [freeAlgebraSheafVariable_comp_freeAlgebraMapOfSquare, underlyingPresheafMap_id,
      Category.id_comp, CategoryTheory.Functor.map_id, Functor.whiskerRight_id']
    exact (Category.comp_id _).symm

variable (a : A ⟶ B)

/-- The map of conormal sheaves attached to the identity square is the identity of `I/I²`. -/
lemma naiveCotangentConormalMapOfSquare_id (hsq : a ≫ 𝟙 B = 𝟙 A ≫ a) :
    naiveCotangentConormalMapOfSquare.{v, u, w, z} J A B a A B a (𝟙 A) (𝟙 B) hsq = 𝟙 _ :=
  Stacks.Sites.Conormal.conormalSheafMapOfSquare_eq_id.{v, u, w, z} J _ B
    (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B a)
    (canonicalFreeAlgebraMapOfSquare J A A B B (𝟙 A) (𝟙 B))
    (canonicalFreeAlgebraMapOfSquare_id J A B) _

/-- The map of the scalar extensions of the differentials attached to the identity square is the
identity of `B ⊗_{A[B]} Ω_{A[B]/A}`. -/
lemma naiveCotangentTensorMapOfSquare_id (hsq : a ≫ 𝟙 B = 𝟙 A ≫ a) :
    naiveCotangentTensorMapOfSquare.{v, u, w, z} J A B a A B a (𝟙 A) (𝟙 B) hsq = 𝟙 _ :=
  Stacks.Sites.Conormal.tensorSheafMapOfSquare_eq_id.{v, u, w, z} J A _ B
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A _)
    (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B a)
    (canonicalFreeAlgebraMapOfSquare J A A B B (𝟙 A) (𝟙 B))
    (canonicalFreeAlgebraMapOfSquare_id J A B) (𝟙 A) rfl _ _

/-- **Stacks 08TX for the identity square.**  The chain map attached to the identity square is
the identity of `NL_{B/A}`. -/
lemma naiveCotangentComplexMapOfSquare_id (hsq : a ≫ 𝟙 B = 𝟙 A ≫ a) :
    naiveCotangentComplexMapOfSquare.{v, u, w, z} J A B a A B a (𝟙 A) (𝟙 B) hsq =
      𝟙 (naiveCotangentComplex.{v, u, w, z} J A B a) := by
  have : HasZeroObject
      (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  have key {X Y : _root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)}
      (h : X = Y) : eqToHom h ≫ 𝟙 Y ≫ eqToHom h.symm = 𝟙 X := by
    subst h
    simp
  refine HomologicalComplex.from_double_hom_ext
    (hi₀₁ := show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) ?_ ?_
  · rw [naiveCotangentComplexMapOfSquare_f_negOne, naiveCotangentConormalMapOfSquare_id]
    exact key (naiveCotangentComplex_X_negOne.{v, u, w, z} J A B a)
  · rw [naiveCotangentComplexMapOfSquare_f_zero, naiveCotangentTensorMapOfSquare_id]
    exact key (naiveCotangentComplex_X_zero.{v, u, w, z} J A B a)

variable (A' B' : Sheaf J CommRingCat.{w}) (a' : A' ⟶ B')

/-- The chain map attached to a square depends on the two horizontal morphisms only through
their values, the transport accounting for the change of the restriction of scalars. -/
private lemma naiveCotangentComplexMapOfSquare_congr
    {f₁ f₂ : A ⟶ A'} {β₁ β₂ : B ⟶ B'} (hf : f₁ = f₂) (hβ : β₁ = β₂)
    (hsq₁ : a ≫ β₁ = f₁ ≫ a') (hsq₂ : a ≫ β₂ = f₂ ≫ a') :
    naiveCotangentComplexMapOfSquare.{v, u, w, z} J A B a A' B' a' f₁ β₁ hsq₁ =
      naiveCotangentComplexMapOfSquare.{v, u, w, z} J A B a A' B' a' f₂ β₂ hsq₂ ≫
        eqToHom (congrArg (fun t : B ⟶ B' ↦
          ((_root_.SheafOfModules.restrictScalars.{max w u v z}
              (underlyingRingHomOfSite t)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (naiveCotangentComplex.{v, u, w, z} J A' B' a')) hβ.symm) := by
  subst hβ hf
  rw [eqToHom_refl, Category.comp_id]

/-- **Stacks 08TX for a pair of mutually inverse squares.**  If `f ≫ f' = 𝟙 A` and
`β ≫ β' = 𝟙 B`, the composite of the chain map of the square `(f, β)` with the restriction of
scalars of the chain map of the square `(f', β')` is the transport of the identity of `NL_{B/A}`
along `β ≫ β' = 𝟙 B`. -/
theorem naiveCotangentComplexMapOfSquare_comp_inv
    (f : A ⟶ A') (f' : A' ⟶ A) (β : B ⟶ B') (β' : B' ⟶ B)
    (hf : f ≫ f' = 𝟙 A) (hβ : β ≫ β' = 𝟙 B)
    (hsq : a ≫ β = f ≫ a') (hsq' : a' ≫ β' = f' ≫ a) :
    naiveCotangentComplexMapOfSquare.{v, u, w, z} J A B a A' B' a' f β hsq ≫
        ((_root_.SheafOfModules.restrictScalars.{max w u v z}
            (underlyingRingHomOfSite β)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (naiveCotangentComplexMapOfSquare.{v, u, w, z} J A' B' a' A B a f' β' hsq') =
      eqToHom (show naiveCotangentComplex.{v, u, w, z} J A B a =
          ((_root_.SheafOfModules.restrictScalars.{max w u v z}
              (underlyingRingHomOfSite β)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((_root_.SheafOfModules.restrictScalars.{max w u v z}
                (underlyingRingHomOfSite β')).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (naiveCotangentComplex.{v, u, w, z} J A B a)) from
        congrArg (fun t : B ⟶ B ↦
          ((_root_.SheafOfModules.restrictScalars.{max w u v z}
              (underlyingRingHomOfSite t)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (naiveCotangentComplex.{v, u, w, z} J A B a)) hβ.symm) := by
  have hid : a ≫ 𝟙 B = 𝟙 A ≫ a := by rw [Category.comp_id, Category.id_comp]
  rw [naiveCotangentComplexMapOfSquare_comp.{v, u, w, z} J A B a A' B' a' f β hsq
      A B a f' β' hsq',
    naiveCotangentComplexMapOfSquare_congr.{v, u, w, z} J A B a A B a hf hβ
      (square_comp hsq hsq') hid,
    naiveCotangentComplexMapOfSquare_id.{v, u, w, z} J A B a hid]
  exact Category.id_comp _

/-- **Stacks 08TX for a square of isomorphisms.**  If the two horizontal morphisms `f : A ≅ A'`
and `β : B ≅ B'` of a commutative square of sheaves of commutative rings are isomorphisms, the
chain map `NL_{B/A} ⟶ NL_{B'/A'}` it induces is an isomorphism. -/
theorem isIso_naiveCotangentComplexMapOfSquare (e : A ≅ A') (b : B ≅ B')
    (hsq : a ≫ b.hom = e.hom ≫ a') :
    IsIso (naiveCotangentComplexMapOfSquare.{v, u, w, z} J A B a A' B' a' e.hom b.hom hsq) := by
  have hsq' : a' ≫ b.inv = e.inv ≫ a := by
    rw [Iso.eq_inv_comp, ← reassoc_of% hsq]
    simp
  exact CategoryTheory.isIso_of_comp_map_eq _ _
    (naiveCotangentComplexMapOfSquare_comp_inv.{v, u, w, z} J A B a A' B' a' e.hom e.inv
      b.hom b.inv e.hom_inv_id b.hom_inv_id hsq hsq')
    (naiveCotangentComplexMapOfSquare_comp_inv.{v, u, w, z} J A' B' a' A B a e.inv e.hom
      b.inv b.hom e.inv_hom_id b.inv_hom_id hsq' hsq)

/-- **Stacks 08TX for a square of isomorphisms, as an isomorphism.**  The identification
`NL_{B/A} ≅ NL_{B'/A'}` attached to a commutative square of sheaves of commutative rings whose
two horizontal morphisms are isomorphisms; the target is read as a complex of sheaves of
`B`-modules through restriction of scalars along `b`.  Its forward map is the canonical chain map
of Stacks 08TX. -/
noncomputable def naiveCotangentComplexIsoOfSquare (e : A ≅ A') (b : B ≅ B')
    (hsq : a ≫ b.hom = e.hom ≫ a') :
    naiveCotangentComplex.{v, u, w, z} J A B a ≅
      ((_root_.SheafOfModules.restrictScalars.{max w u v z}
          (underlyingRingHomOfSite b.hom)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (naiveCotangentComplex.{v, u, w, z} J A' B' a') :=
  haveI := isIso_naiveCotangentComplexMapOfSquare.{v, u, w, z} J A B a A' B' a' e b hsq
  asIso (naiveCotangentComplexMapOfSquare.{v, u, w, z} J A B a A' B' a' e.hom b.hom hsq)

/-- The forward map of `Stacks.SheafOfModules.naiveCotangentComplexIsoOfSquare` is the canonical
chain map of Stacks 08TX. -/
theorem naiveCotangentComplexIsoOfSquare_hom (e : A ≅ A') (b : B ≅ B')
    (hsq : a ≫ b.hom = e.hom ≫ a') :
    (naiveCotangentComplexIsoOfSquare.{v, u, w, z} J A B a A' B' a' e b hsq).hom =
      naiveCotangentComplexMapOfSquare.{v, u, w, z} J A B a A' B' a' e.hom b.hom hsq :=
  rfl

end Stacks.SheafOfModules

end
