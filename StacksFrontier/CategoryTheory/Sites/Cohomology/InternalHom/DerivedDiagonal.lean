module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TotalComplexNaturality
public import StacksFrontier.CategoryTheory.CommutingSquares
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurrying
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorHomInterchange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DiagonalKFlatRoof
import StacksCore.Tactic.StacksAttribute

/-!
# The derived diagonal into the internal Hom of a derived tensor product

Let `(C, O)` be a ringed site and let `K`, `L` be objects of `D(O)`.  **Stacks 0A99** asserts a
canonical morphism

`K ⟶ RSheafHom(L, K ⊗_O^L L)`

in `D(O)`, functorial in both `K` and `L`.  This file constructs that morphism twice.

`AlgebraicGeometry.RingedSite.derivedDiagonal` is the short construction: the image of the
identity of `K ⊗_O^L L` under the derived tensor–internal Hom bijection of morphism groups of
Stacks 08J8, `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv`.  It is the unit of that
bijection.

`AlgebraicGeometry.RingedSite.canonicalDerivedDiagonal` is the construction the source gives,
and it is the one that carries the tag: a K-flat complex `A` representing `K` and a K-injective
complex `B` representing `L` are chosen, the diagonal morphism of complexes of Stacks 0A93

`A ⟶ SheafHom(B, Tot(A ⊗_O B))`

is followed by the augmentation of `Tot(A ⊗_O B)` into its chosen K-injective resolution `J`,
and the class of the resulting morphism `A ⟶ SheafHom(B, J)` is read through the comparisons
identifying `K` with the class of `A` and `RSheafHom(L, K ⊗_O^L L)` with the class of
`SheafHom(B, J)`.  Both functoriality squares are proved for it.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedDiagonal`: the morphism as the unit of Stacks 08J8.
* `AlgebraicGeometry.RingedSite.diagonalComplexMap`: the diagonal of Stacks 0A93 followed by the
  K-injective resolution augmentation.
* `AlgebraicGeometry.RingedSite.diagonalTensorModelIso` and
  `AlgebraicGeometry.RingedSite.diagonalTargetIso`: the comparisons identifying `K ⊗_O^L L` and
  `RSheafHom(N, K ⊗_O^L L)` with classes of complexes.
* `AlgebraicGeometry.RingedSite.canonicalDerivedDiagonal`: **Stacks 0A99**, the canonical
  morphism.

## Main results

* `AlgebraicGeometry.RingedSite.diagonalComplexMap_natural_left` and
  `AlgebraicGeometry.RingedSite.diagonalComplexMap_natural_right`: the two functoriality squares
  at the level of complexes, from Stacks 0A93.
* `AlgebraicGeometry.RingedSite.canonicalDerivedDiagonal_eq`: the canonical morphism is the class
  of that morphism of complexes, read through the two comparisons.
* `AlgebraicGeometry.RingedSite.canonicalDerivedDiagonal_natural_left`: **Stacks 0A99**,
  functoriality in `K`.
* `AlgebraicGeometry.RingedSite.canonicalDerivedDiagonal_natural_right`: **Stacks 0A99**,
  functoriality in `L`.

## Implementation notes

The unit construction `derivedDiagonal` is pinned down by its definition rather than by a
separate characterisation: it *is* the image of `𝟙 (K ⊗_O^L L)` under the bijection, so it is not
an unconstrained morphism of its type, and it is zero only if that identity is.  The
corresponding equation `derivedCurryHomEquiv … (derivedDiagonal …) = 𝟙 _` is therefore a
convenience and not a soundness requirement; it is omitted because elaborating the coercion of
the morphism-group `AddEquiv` at these arguments exhausts the recursion depth, and raising that
limit by a compiler option is a workaround this development does not accept.

**The tag sits on `canonicalDerivedDiagonal` and its two functoriality squares, and not on
`derivedDiagonal`.**  The two morphisms are not identified here, and the reason is an explicitly
recorded gap of this development rather than a choice.  The unit of `derivedCurryHomEquiv` is
natural exactly when that bijection is, and `derivedCurryHomEquiv` is the currying isomorphism
of Stacks 08J9 read on degree-zero global hypercohomology with both ends identified with
morphism groups by Stacks 08JA.  The object-level half is available —
`AlgebraicGeometry.RingedSite.derivedCurryIso_natural` is the naturality of the currying
isomorphism in all three objects — and of the naturality of Stacks 08JA,
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv`, the source-variable clause is
now available too, as
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_source` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurrySourceNaturality`.  The
characterising structure `AlgebraicGeometry.RingedSite.SheafHomComplex` records no compatibility
of its `globalSectionsIso` field with `AlgebraicGeometry.RingedSite.homMap`; that compatibility
is
`AlgebraicGeometry.RingedSite.globalSectionsIso_homMap_v`, outside the structure, and the global
half of the naturality of Stacks 0A94 is
`AlgebraicGeometry.RingedSite.sheafHomGlobalHomologyEquivDerivedCategoryHom_naturality`.
Identifying the two morphisms here needs more than the source-variable clause: it amounts to
computing `derivedCurryHomEquiv` on a given class, and for that the target-variable clause of
Stacks 08JA is what is wanted.  That clause is
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_target` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryTargetNaturality`, where it
is proved by reducing to morphisms of complexes with
`AlgebraicGeometry.RingedSite.exists_Q_map_eq_of_isKInjective` rather than by a calculus of
fractions, and the bijection is bundled there as
`AlgebraicGeometry.RingedSite.derivedTensorSheafHomAdjunction`.  So what the identification needs
is available, and what remains is the computation itself.  Nothing below depends on the
identification: the tag's two assertions are the existence of a canonical morphism and its
functoriality, and both are discharged by `canonicalDerivedDiagonal` on its own.

The functoriality in `L` needs no localisation argument: the chosen representative of `L` is the
K-injective model, so every morphism `L' ⟶ L` of `D(O)` is the class of a morphism of the chosen
representatives by `AlgebraicGeometry.RingedSite.exists_Q_map_eq_of_isKInjective`, and the square
is the complex-level dinaturality of Stacks 0A93 conjugated by the comparisons.  The
functoriality in `K` does need one, because the chosen representative of `K` is K-flat and not
K-injective: the given morphism is written as a right fraction (`DerivedCategory.right_fac`) and
the apex of that fraction is replaced by a K-flat resolution of it (Stacks 06YS), giving a roof
`A ⟵ P ⟶ A'` with all three complexes K-flat and the left leg invertible in `D(O)`.  The
one-sided K-flat comparison of Stacks 06YU is then available at all three vertices, which makes
the tensored left leg invertible with no K-flatness of the other factor.  This is the argument of
`AlgebraicGeometry.RingedSite.derivedTensorHomDiagonal_natural_left` for Stacks 0BYS.

The characterisation `canonicalDerivedDiagonal_eq` is stated at the *chosen* representatives —
`AlgebraicGeometry.RingedSite.kFlatModel` for `K`,
`AlgebraicGeometry.RingedSite.kInjectiveModel` for `L` and the functorial K-injective resolution
of `Tot(A ⊗_O B)` for `J` — and not at an arbitrary K-flat `A`, arbitrary `B`, K-injective `J`
and quasi-isomorphism `Tot(A ⊗_O B) ⟶ J`.  Generalising it is a further transport along the
comparisons of the kind already carried out for the functorialities, and it is not done here.

The target comparison is stated for three objects, `RSheafHom(N, K ⊗_O^L L)`, rather than two:
the functoriality in `L` compares the diagonal at `L` with the diagonal at `L'` inside
`RSheafHom(L', K ⊗_O^L L)`, where the source of the internal Hom and the tensor factor are
modelled by different complexes.

The universes are the diagonal `RingedSite.{u, u, u}` of the whole derived internal Hom cluster;
see the implementation notes of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurrying`.

## References

* [Stacks Project, Tag 0A99](https://stacks.math.columbia.edu/tag/0A99)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0A93](https://stacks.math.columbia.edu/tag/0A93)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

variable (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- The derived diagonal `K ⟶ RSheafHom(L, K ⊗_O^L L)`: the morphism corresponding to the
identity of `K ⊗_O^L L` under the derived tensor–internal Hom bijection of Stacks 08J8. -/
def derivedDiagonal :
    K ⟶ ((derivedSheafHomBifunctor X).obj (op L)).obj
      (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L) :=
  (derivedCurryHomEquiv X K L
    (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L)).symm (𝟙 _)

end AlgebraicGeometry.RingedSite

end

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

/-- Transposing a commuting square across the inverses of its two horizontal isomorphisms. -/
private lemma diagonalTranspose {C : Type*} [Category C] {P P' T T' : C}
    (e : P ≅ T) (e' : P' ≅ T') {β : P ⟶ P'} {τ : T ⟶ T'}
    (hβ : β ≫ e'.hom = e.hom ≫ τ) : e.inv ≫ β = τ ≫ e'.inv := by
  rw [← Category.comp_id (e.inv ≫ β), ← e'.hom_inv_id, ← Category.assoc,
    Category.assoc e.inv, hβ, ← Category.assoc, e.inv_hom_id, Category.id_comp]

/-- A square conjugated by a source comparison pointing into the complex model and a target
comparison pointing out of it commutes as soon as both comparisons are compatible with the given
morphisms and the conjugated square commutes. -/
private lemma diagonalConjSquare {C : Type*} [Category C]
    {Src Src' S S' Tgt Tgt' T T' : C}
    (eS : S ≅ Src) (eS' : S' ≅ Src') (eT : Tgt ≅ T) (eT' : Tgt' ≅ T')
    {α : Src ⟶ Src'} {β : Tgt ⟶ Tgt'} {σ : S ⟶ S'} {τ : T ⟶ T'}
    {θ : S ⟶ T} {θ' : S' ⟶ T'}
    (hα : α ≫ eS'.inv = eS.inv ≫ σ) (hβ : β ≫ eT'.hom = eT.hom ≫ τ)
    (hθ : θ ≫ τ = σ ≫ θ') :
    α ≫ eS'.inv ≫ θ' ≫ eT'.inv = (eS.inv ≫ θ ≫ eT.inv) ≫ β := by
  have hβ' := diagonalTranspose eT eT' hβ
  have h1 : α ≫ eS'.inv ≫ θ' ≫ eT'.inv = eS.inv ≫ σ ≫ θ' ≫ eT'.inv := by
    rw [← Category.assoc, hα, Category.assoc]
  have h2 : σ ≫ θ' ≫ eT'.inv = θ ≫ τ ≫ eT'.inv := by
    rw [← Category.assoc, ← hθ, Category.assoc]
  rw [h1, h2, ← hβ']
  simp only [Category.assoc]

/-- The diagonal of Stacks 0A93 followed by the map of internal Hom complexes induced by the
augmentation and the resolution of `Tot(c ⊗ g)` is the diagonal at `(A₀, B)`, conjugated by `c`
and `g`, followed by the augmentation. -/
private lemma diagonalMap_comp_homMap_resolution (X : RingedSite.{u, u, u})
    {A A₀ B B' : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ} (c : A ⟶ A₀) (g : B' ⟶ B) :
    diagonalMap X A B' ≫ homMap X (𝟙 B')
        ((kInjectiveAugmentation X).app (tensorTotal X A B') ≫
          (kInjectiveResolution X).map (tensorTotalMap X c g)) =
      c ≫ diagonalMap X A₀ B ≫
        homMap X g ((kInjectiveAugmentation X).app (tensorTotal X A₀ B)) := by
  have haug := (kInjectiveAugmentation X).naturality (tensorTotalMap X c g)
  rw [Functor.id_map] at haug
  have hsplit : homMap X (𝟙 B') (tensorTotalMap X c g ≫
        (kInjectiveAugmentation X).app (tensorTotal X A₀ B)) =
      homMap X (𝟙 B') (tensorTotalMap X c g) ≫
        homMap X (𝟙 B') ((kInjectiveAugmentation X).app (tensorTotal X A₀ B)) := by
    rw [homMap_comp, Category.comp_id]
  rw [← haug, hsplit, ← Category.assoc, diagonalMap_natural, Category.assoc, Category.assoc,
    homMap_comp, Category.id_comp, Category.id_comp]

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **The diagonal morphism of complexes of Stacks 0A93, resolved.** It is the diagonal
`A ⟶ SheafHom(B, Tot(A ⊗_O B))` followed by the map of internal Hom complexes induced by the
augmentation of `Tot(A ⊗_O B)` into its chosen K-injective resolution. -/
def diagonalComplexMap
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    A ⟶ (sheafHomComplex X B ((kInjectiveResolution X).obj (tensorTotal X A B))).obj :=
  diagonalMap X A B ≫ homMap X (𝟙 B) ((kInjectiveAugmentation X).app (tensorTotal X A B))

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
      HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
        (ComplexShape.up ℤ)] in
/-- **The resolved diagonal of complexes is natural in the first complex.** This is the
functoriality of Stacks 0A93 in its first complex, together with the naturality of the
K-injective resolution augmentation.  No condition is placed on either complex. -/
theorem diagonalComplexMap_natural_left
    {A A₀ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (c : A ⟶ A₀)
    (B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    c ≫ diagonalComplexMap X A₀ B =
      diagonalComplexMap X A B ≫
        homMap X (𝟙 B) ((kInjectiveResolution X).map (tensorTotalMap X c (𝟙 B))) := by
  unfold diagonalComplexMap
  simp only [Category.assoc, homMap_comp, Category.comp_id, diagonalMap_comp_homMap_resolution]

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
      HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
        (ComplexShape.up ℤ)] in
/-- **The resolved diagonal of complexes is dinatural in the second complex**: a morphism
`g : B' ⟶ B` acts covariantly inside the tensor product and contravariantly in the source of the
internal Hom.  This is the functoriality of Stacks 0A93 in its second complex, together with the
naturality of the K-injective resolution augmentation. -/
theorem diagonalComplexMap_natural_right
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (g : B' ⟶ B) :
    diagonalComplexMap X A B ≫
        homMap X g (𝟙 ((kInjectiveResolution X).obj (tensorTotal X A B))) =
      diagonalComplexMap X A B' ≫
        homMap X (𝟙 B') ((kInjectiveResolution X).map (tensorTotalMap X (𝟙 A) g)) := by
  have h := diagonalMap_comp_homMap_resolution X (𝟙 A) g
  unfold diagonalComplexMap
  simp only [Category.assoc, homMap_comp, Category.comp_id, Category.id_comp] at h ⊢
  exact h.symm

/-- `K ⊗_O^L L` is the class of the total tensor product of the chosen K-flat representative of
`K` with the chosen K-injective representative of `L`, by the one-sided K-flat comparison of
Stacks 06YU. -/
def diagonalTensorModelIso
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L ≅
      DerivedCategory.Q.obj (tensorTotal X (kFlatModel X K) (kInjectiveModel X L)) :=
  ((Stacks.SheafOfModules.derivedTensorProductFunctor X).mapIso
      (kFlatModelIso X K).symm).app L ≪≫
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
        (DerivedCategory.Q.obj (kFlatModel X K))).mapIso (kInjectiveModelIso X L).symm ≪≫
      tensorTotalKFlatComparison X (kFlatModel X K) (kInjectiveModel X L)
        (isKFlat_kFlatModel X K)

/-- `RSheafHom(N, K ⊗_O^L L)` is the class of the internal Hom complex from the chosen
representative of `N` into the chosen K-injective resolution of the complex model of
`K ⊗_O^L L`: the derived internal Hom into the class of an arbitrary complex is the internal Hom
complex into that resolution (Stacks 0A97). -/
def diagonalTargetIso
    (K L N : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((derivedSheafHomBifunctor X).obj (op N)).obj
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L) ≅
      DerivedCategory.Q.obj (sheafHomComplex X (kInjectiveModel X N)
        ((kInjectiveResolution X).obj
          (tensorTotal X (kFlatModel X K) (kInjectiveModel X L)))).obj :=
  ((derivedSheafHomBifunctor X).obj (op N)).mapIso (diagonalTensorModelIso X K L) ≪≫
    ((derivedSheafHomBifunctor X).mapIso (kInjectiveModelIso X N).op).app
        (DerivedCategory.Q.obj (tensorTotal X (kFlatModel X K) (kInjectiveModel X L))) ≪≫
      derivedSheafHomResolutionComparison X (kInjectiveModel X N)
        (tensorTotal X (kFlatModel X K) (kInjectiveModel X L))

/-- **Stacks 0A99.** For objects `K`, `L` of `D(O)` the canonical morphism

`K ⟶ RSheafHom(L, K ⊗_O^L L)`

in `D(O)`: on the chosen K-flat representative `A` of `K` and the chosen K-injective
representative `B` of `L` it is the diagonal morphism of complexes of Stacks 0A93, followed by
the augmentation of `Tot(A ⊗_O B)` into its chosen K-injective resolution. -/
@[stacks 0A99 "the canonical morphism"]
def canonicalDerivedDiagonal
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    K ⟶ ((derivedSheafHomBifunctor X).obj (op L)).obj
      (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L) :=
  (kFlatModelIso X K).inv ≫
    DerivedCategory.Q.map (diagonalComplexMap X (kFlatModel X K) (kInjectiveModel X L)) ≫
      (diagonalTargetIso X K L L).inv

/-- **The canonical morphism of Stacks 0A99 is the class of the resolved diagonal of complexes**,
read through the comparisons of its source and target with classes of complexes.  In particular
it is not an arbitrary morphism between the two objects. -/
@[stacks 0A99 "the characterisation on representatives"]
theorem canonicalDerivedDiagonal_eq
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (kFlatModelIso X K).hom ≫ canonicalDerivedDiagonal X K L ≫
        (diagonalTargetIso X K L L).hom =
      DerivedCategory.Q.map (diagonalComplexMap X (kFlatModel X K) (kInjectiveModel X L)) := by
  rw [canonicalDerivedDiagonal]
  simp

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
      HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
        (ComplexShape.up ℤ)] in
/-- The comparison with the chosen K-injective resolution of the target is natural in that
target. -/
private lemma diagonalResolutionComparison_natural
    (C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {M M' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (m : M ⟶ M') :
    ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj C))).map
          (DerivedCategory.Q.map m) ≫
        (derivedSheafHomResolutionComparison X C M').hom =
      (derivedSheafHomResolutionComparison X C M).hom ≫
        DerivedCategory.Q.map (homMap X (𝟙 C) ((kInjectiveResolution X).map m)) := by
  simpa using derivedSheafHomResolutionComparison_naturality X (𝟙 C) m

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
      HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
        (ComplexShape.up ℤ)] in
/-- The comparison with the chosen K-injective resolution of the target is natural in the source
of the internal Hom. -/
private lemma diagonalResolutionComparison_natural_source
    {C C' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (c : C' ⟶ C)
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map c).op).app
          (DerivedCategory.Q.obj M) ≫
        (derivedSheafHomResolutionComparison X C' M).hom =
      (derivedSheafHomResolutionComparison X C M).hom ≫
        DerivedCategory.Q.map (homMap X c (𝟙 ((kInjectiveResolution X).obj M))) := by
  simpa using derivedSheafHomResolutionComparison_naturality X c (𝟙 M)

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
      HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
        (ComplexShape.up ℤ)] in
/-- Moving a morphism of `D(O)` past the comparisons with the chosen K-injective representatives
of the source of an internal Hom replaces it by the class of its lift. -/
private lemma diagonalMapOpKInjectiveModelIso
    {N N' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {l : N' ⟶ N}
    {t : kInjectiveModel X N' ⟶ kInjectiveModel X N}
    (ht : DerivedCategory.Q.map t =
      (kInjectiveModelIso X N').hom ≫ l ≫ (kInjectiveModelIso X N).inv)
    (Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((derivedSheafHomBifunctor X).map l.op).app Z ≫
        ((derivedSheafHomBifunctor X).map (kInjectiveModelIso X N').hom.op).app Z =
      ((derivedSheafHomBifunctor X).map (kInjectiveModelIso X N).hom.op).app Z ≫
        ((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map t).op).app Z := by
  have hcomp : (kInjectiveModelIso X N').hom ≫ l =
      DerivedCategory.Q.map t ≫ (kInjectiveModelIso X N).hom := by
    rw [ht, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← Functor.map_comp, ← Functor.map_comp,
    ← op_comp, ← op_comp, hcomp]

/-- The target comparison intertwines a morphism of `D(O)` in the source of the internal Hom with
the map of internal Hom complexes induced by its lift to the chosen representatives. -/
private lemma diagonalTargetIso_natural_source
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {N N' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {l : N' ⟶ N}
    {t : kInjectiveModel X N' ⟶ kInjectiveModel X N}
    (ht : DerivedCategory.Q.map t =
      (kInjectiveModelIso X N').hom ≫ l ≫ (kInjectiveModelIso X N).inv) :
    ((derivedSheafHomBifunctor X).map l.op).app
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L) ≫
        (diagonalTargetIso X K L N').hom =
      (diagonalTargetIso X K L N).hom ≫
        DerivedCategory.Q.map (homMap X t (𝟙 ((kInjectiveResolution X).obj
          (tensorTotal X (kFlatModel X K) (kInjectiveModel X L))))) := by
  have sq1 := (((derivedSheafHomBifunctor X).map l.op).naturality
    (diagonalTensorModelIso X K L).hom).symm
  have sq2 := diagonalMapOpKInjectiveModelIso X ht
    (DerivedCategory.Q.obj (tensorTotal X (kFlatModel X K) (kInjectiveModel X L)))
  have sq3 := diagonalResolutionComparison_natural_source X t
    (tensorTotal X (kFlatModel X K) (kInjectiveModel X L))
  unfold diagonalTargetIso
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.op_hom]
  exact square_comp sq1 (square_comp sq2 sq3)

/-- The comparison of `K ⊗_O^L L` with the total tensor product of the chosen representatives
intertwines a morphism of `D(O)` in the second variable with the morphism of total tensor
products induced by its lift. -/
private lemma diagonalTensorModelIso_natural_tensor
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {l : L' ⟶ L}
    {g : kInjectiveModel X L' ⟶ kInjectiveModel X L}
    (hg : DerivedCategory.Q.map g =
      (kInjectiveModelIso X L').hom ≫ l ≫ (kInjectiveModelIso X L).inv) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map l ≫
        (diagonalTensorModelIso X K L).hom =
      (diagonalTensorModelIso X K L').hom ≫
        DerivedCategory.Q.map (tensorTotalMap X (𝟙 (kFlatModel X K)) g) := by
  have sq1 := ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
    (kFlatModelIso X K).inv).naturality l
  have sq2 : ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          (DerivedCategory.Q.obj (kFlatModel X K))).map l ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          (DerivedCategory.Q.obj (kFlatModel X K))).map (kInjectiveModelIso X L).inv =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          (DerivedCategory.Q.obj (kFlatModel X K))).map (kInjectiveModelIso X L').inv ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          (DerivedCategory.Q.obj (kFlatModel X K))).map (DerivedCategory.Q.map g) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hg, Iso.inv_hom_id_assoc]
  have sq3 : ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          (DerivedCategory.Q.obj (kFlatModel X K))).map (DerivedCategory.Q.map g) ≫
        (tensorTotalKFlatComparison X (kFlatModel X K) (kInjectiveModel X L)
          (isKFlat_kFlatModel X K)).hom =
      (tensorTotalKFlatComparison X (kFlatModel X K) (kInjectiveModel X L')
          (isKFlat_kFlatModel X K)).hom ≫
        DerivedCategory.Q.map (tensorTotalMap X (𝟙 (kFlatModel X K)) g) := by
    simpa using tensorTotalKFlatComparison_natural X (isKFlat_kFlatModel X K)
      (isKFlat_kFlatModel X K) (𝟙 (kFlatModel X K)) g
  unfold diagonalTensorModelIso
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom]
  exact square_comp sq1 (square_comp sq2 sq3)

/-- The target comparison intertwines a morphism of `D(O)` in the tensor factor coming from the
second variable with the morphism of internal Hom complexes induced by the resolution of its
lift. -/
private lemma diagonalTargetIso_natural_tensor
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (N : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {l : L' ⟶ L}
    {g : kInjectiveModel X L' ⟶ kInjectiveModel X L}
    (hg : DerivedCategory.Q.map g =
      (kInjectiveModelIso X L').hom ≫ l ≫ (kInjectiveModelIso X L).inv) :
    ((derivedSheafHomBifunctor X).obj (op N)).map
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map l) ≫
        (diagonalTargetIso X K L N).hom =
      (diagonalTargetIso X K L' N).hom ≫
        DerivedCategory.Q.map (homMap X (𝟙 (kInjectiveModel X N))
          ((kInjectiveResolution X).map
            (tensorTotalMap X (𝟙 (kFlatModel X K)) g))) := by
  have sq1 : ((derivedSheafHomBifunctor X).obj (op N)).map
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map l) ≫
        ((derivedSheafHomBifunctor X).obj (op N)).map
          (diagonalTensorModelIso X K L).hom =
      ((derivedSheafHomBifunctor X).obj (op N)).map
          (diagonalTensorModelIso X K L').hom ≫
        ((derivedSheafHomBifunctor X).obj (op N)).map
          (DerivedCategory.Q.map (tensorTotalMap X (𝟙 (kFlatModel X K)) g)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, diagonalTensorModelIso_natural_tensor X K hg]
  have sq2 := ((derivedSheafHomBifunctor X).map (kInjectiveModelIso X N).hom.op).naturality
    (DerivedCategory.Q.map (tensorTotalMap X (𝟙 (kFlatModel X K)) g))
  have sq3 := diagonalResolutionComparison_natural X (kInjectiveModel X N)
    (tensorTotalMap X (𝟙 (kFlatModel X K)) g)
  unfold diagonalTargetIso
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.op_hom]
  exact square_comp sq1 (square_comp sq2 sq3)

/-- **Stacks 0A99: the canonical morphism is functorial in `L`.** For a morphism `l : L' ⟶ L` of
`D(O)` the square

`u_{K,L} ≫ RSheafHom(l, 𝟙) = u_{K,L'} ≫ RSheafHom(𝟙, 𝟙_K ⊗ l)`

commutes in `D(O)`: the second variable of the diagonal acts contravariantly in the source of
the internal Hom and covariantly inside the derived tensor product, which is the dinaturality
that the statement of the tag asserts.

The chosen representative of `L` is K-injective, so `l` is the class of a morphism of the chosen
representatives and the square is the dinaturality of Stacks 0A93 at the level of complexes,
conjugated by the target comparisons. -/
@[stacks 0A99 "functoriality in L"]
theorem canonicalDerivedDiagonal_natural_right
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (l : L' ⟶ L) :
    canonicalDerivedDiagonal X K L ≫
        ((derivedSheafHomBifunctor X).map l.op).app
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L) =
      canonicalDerivedDiagonal X K L' ≫
        ((derivedSheafHomBifunctor X).obj (op L')).map
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map l) := by
  obtain ⟨g, hg⟩ := exists_Q_map_eq_of_isKInjective X
    ((kInjectiveModelIso X L').hom ≫ l ≫ (kInjectiveModelIso X L).inv)
  have h1 := diagonalTranspose (diagonalTargetIso X K L L) (diagonalTargetIso X K L L')
    (diagonalTargetIso_natural_source X K L hg)
  have h2 := diagonalTranspose (diagonalTargetIso X K L' L') (diagonalTargetIso X K L L')
    (diagonalTargetIso_natural_tensor X K L' hg)
  have hmodel : DerivedCategory.Q.map
          (diagonalComplexMap X (kFlatModel X K) (kInjectiveModel X L)) ≫
        DerivedCategory.Q.map (homMap X g (𝟙 ((kInjectiveResolution X).obj
          (tensorTotal X (kFlatModel X K) (kInjectiveModel X L))))) =
      DerivedCategory.Q.map
          (diagonalComplexMap X (kFlatModel X K) (kInjectiveModel X L')) ≫
        DerivedCategory.Q.map (homMap X (𝟙 (kInjectiveModel X L'))
          ((kInjectiveResolution X).map
            (tensorTotalMap X (𝟙 (kFlatModel X K)) g))) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg DerivedCategory.Q.map
      (diagonalComplexMap_natural_right X (kFlatModel X K) g)
  unfold canonicalDerivedDiagonal
  simp only [Category.assoc]
  rw [h1, h2, reassoc_of% hmodel]

section DiagonalTensorVariable

variable {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {f : K ⟶ K'}

/-- The comparison of a derived tensor product with a K-flat left factor and the total tensor
product is natural in that factor, the second factor being arbitrary. -/
private lemma diagonalTensorComparison_natural
    {A A₀ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A)
    (hA₀ : Stacks.SheafOfModules.IsKFlat X.O A₀) (c : A ⟶ A₀)
    (Z : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
          (DerivedCategory.Q.map c)).app (DerivedCategory.Q.obj Z) ≫
        (tensorTotalKFlatComparison X A₀ Z hA₀).hom =
      (tensorTotalKFlatComparison X A Z hA).hom ≫
        DerivedCategory.Q.map (tensorTotalMap X c (𝟙 Z)) := by
  simpa using tensorTotalKFlatComparison_natural X hA hA₀ c (𝟙 Z)

section DiagonalRoof

variable {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
  (hP : Stacks.SheafOfModules.IsKFlat X.O P)
  {sr : P ⟶ kFlatModel X K} {gr : P ⟶ kFlatModel X K'}
  (hsr : IsIso (DerivedCategory.Q.map sr))
  (hfac : DerivedCategory.Q.map sr ≫ (kFlatModelIso X K).hom ≫ f ≫
    (kFlatModelIso X K').inv = DerivedCategory.Q.map gr)

include hP hsr hfac in
/-- **The roof square.** Moving the given morphism of `D(O)` past the comparisons with the two
chosen K-flat representatives replaces it by the morphism of the classes of the total tensor
products that the roof determines, for an arbitrary second factor. -/
private lemma diagonalRoofComparison
    (Z : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {σ : DerivedCategory.Q.obj (tensorTotal X (kFlatModel X K) Z) ⟶
      DerivedCategory.Q.obj (tensorTotal X (kFlatModel X K') Z)}
    (hσ : DerivedCategory.Q.map (tensorTotalMap X sr (𝟙 Z)) ≫ σ =
      DerivedCategory.Q.map (tensorTotalMap X gr (𝟙 Z))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
            ((kFlatModelIso X K).hom ≫ f ≫ (kFlatModelIso X K').inv)).app
          (DerivedCategory.Q.obj Z) ≫
        (tensorTotalKFlatComparison X (kFlatModel X K') Z
          (isKFlat_kFlatModel X K')).hom =
      (tensorTotalKFlatComparison X (kFlatModel X K) Z (isKFlat_kFlatModel X K)).hom ≫ σ := by
  have := hsr
  have hcomp : ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
        (DerivedCategory.Q.map sr)).app (DerivedCategory.Q.obj Z) ≫
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
        ((kFlatModelIso X K).hom ≫ f ≫ (kFlatModelIso X K').inv)).app
          (DerivedCategory.Q.obj Z) =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
        (DerivedCategory.Q.map gr)).app (DerivedCategory.Q.obj Z) := by
    rw [← NatTrans.comp_app, ← Functor.map_comp, hfac]
  rw [← cancel_epi (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
      (DerivedCategory.Q.map sr)).app (DerivedCategory.Q.obj Z)),
    ← Category.assoc, hcomp,
    diagonalTensorComparison_natural X hP (isKFlat_kFlatModel X K') gr Z,
    ← Category.assoc,
    diagonalTensorComparison_natural X hP (isKFlat_kFlatModel X K) sr Z]
  simp only [Category.assoc]
  rw [hσ]

include hP hsr in
/-- The roof square for the K-injective resolution comparison: the morphism of the classes of the
total tensor products that the roof determines is matched by the morphism of internal Hom
complexes induced by the resolution of the roof. -/
private lemma diagonalRoofResolutionComparison
    (L N : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {σ : DerivedCategory.Q.obj (tensorTotal X (kFlatModel X K) (kInjectiveModel X L)) ⟶
      DerivedCategory.Q.obj (tensorTotal X (kFlatModel X K') (kInjectiveModel X L))}
    (hσ : DerivedCategory.Q.map (tensorTotalMap X sr (𝟙 (kInjectiveModel X L))) ≫ σ =
      DerivedCategory.Q.map (tensorTotalMap X gr (𝟙 (kInjectiveModel X L))))
    {τ : DerivedCategory.Q.obj (sheafHomComplex X (kInjectiveModel X N)
          ((kInjectiveResolution X).obj
            (tensorTotal X (kFlatModel X K) (kInjectiveModel X L)))).obj ⟶
        DerivedCategory.Q.obj (sheafHomComplex X (kInjectiveModel X N)
          ((kInjectiveResolution X).obj
            (tensorTotal X (kFlatModel X K') (kInjectiveModel X L)))).obj}
    (hτ : DerivedCategory.Q.map (homMap X (𝟙 (kInjectiveModel X N))
          ((kInjectiveResolution X).map
            (tensorTotalMap X sr (𝟙 (kInjectiveModel X L))))) ≫ τ =
      DerivedCategory.Q.map (homMap X (𝟙 (kInjectiveModel X N))
        ((kInjectiveResolution X).map
          (tensorTotalMap X gr (𝟙 (kInjectiveModel X L)))))) :
    ((derivedSheafHomBifunctor X).obj
            (op (DerivedCategory.Q.obj (kInjectiveModel X N)))).map σ ≫
        (derivedSheafHomResolutionComparison X (kInjectiveModel X N)
          (tensorTotal X (kFlatModel X K') (kInjectiveModel X L))).hom =
      (derivedSheafHomResolutionComparison X (kInjectiveModel X N)
          (tensorTotal X (kFlatModel X K) (kInjectiveModel X L))).hom ≫ τ := by
  have := isIso_Q_map_tensorTotalMap_roof X hP hsr (kInjectiveModel X L)
  rw [← cancel_epi (((derivedSheafHomBifunctor X).obj
      (op (DerivedCategory.Q.obj (kInjectiveModel X N)))).map
      (DerivedCategory.Q.map (tensorTotalMap X sr (𝟙 (kInjectiveModel X L))))),
    ← Category.assoc, ← Functor.map_comp, hσ,
    diagonalResolutionComparison_natural X (kInjectiveModel X N)
      (tensorTotalMap X gr (𝟙 (kInjectiveModel X L))),
    ← Category.assoc,
    diagonalResolutionComparison_natural X (kInjectiveModel X N)
      (tensorTotalMap X sr (𝟙 (kInjectiveModel X L))),
    Category.assoc, hτ]

include hP hsr hfac in
/-- The comparison of `K ⊗_O^L L` with the total tensor product of the chosen representatives
intertwines the map induced on the first variable with the morphism of classes of total tensor
products that the roof determines. -/
private lemma diagonalTensorModelIso_natural_left
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {σ : DerivedCategory.Q.obj (tensorTotal X (kFlatModel X K) (kInjectiveModel X L)) ⟶
      DerivedCategory.Q.obj (tensorTotal X (kFlatModel X K') (kInjectiveModel X L))}
    (hσ : DerivedCategory.Q.map (tensorTotalMap X sr (𝟙 (kInjectiveModel X L))) ≫ σ =
      DerivedCategory.Q.map (tensorTotalMap X gr (𝟙 (kInjectiveModel X L)))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map f).app L ≫
        (diagonalTensorModelIso X K' L).hom =
      (diagonalTensorModelIso X K L).hom ≫ σ := by
  have sq1 := map_kFlatModelIso_inv_comp X (w := f) L
  have sq2 := (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
    ((kFlatModelIso X K).hom ≫ f ≫ (kFlatModelIso X K').inv)).naturality
      (kInjectiveModelIso X L).inv).symm
  unfold diagonalTensorModelIso
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom]
  exact square_comp sq1 (square_comp sq2
    (diagonalRoofComparison X hP hsr hfac (kInjectiveModel X L) hσ))

include hP hsr hfac in
/-- The target comparison intertwines the map induced on the first variable with the morphism of
internal Hom complexes induced by the resolution of the roof. -/
private lemma diagonalTargetIso_natural_left
    (L N : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {σ : DerivedCategory.Q.obj (tensorTotal X (kFlatModel X K) (kInjectiveModel X L)) ⟶
      DerivedCategory.Q.obj (tensorTotal X (kFlatModel X K') (kInjectiveModel X L))}
    (hσ : DerivedCategory.Q.map (tensorTotalMap X sr (𝟙 (kInjectiveModel X L))) ≫ σ =
      DerivedCategory.Q.map (tensorTotalMap X gr (𝟙 (kInjectiveModel X L))))
    {τ : DerivedCategory.Q.obj (sheafHomComplex X (kInjectiveModel X N)
          ((kInjectiveResolution X).obj
            (tensorTotal X (kFlatModel X K) (kInjectiveModel X L)))).obj ⟶
        DerivedCategory.Q.obj (sheafHomComplex X (kInjectiveModel X N)
          ((kInjectiveResolution X).obj
            (tensorTotal X (kFlatModel X K') (kInjectiveModel X L)))).obj}
    (hτ : DerivedCategory.Q.map (homMap X (𝟙 (kInjectiveModel X N))
          ((kInjectiveResolution X).map
            (tensorTotalMap X sr (𝟙 (kInjectiveModel X L))))) ≫ τ =
      DerivedCategory.Q.map (homMap X (𝟙 (kInjectiveModel X N))
        ((kInjectiveResolution X).map
          (tensorTotalMap X gr (𝟙 (kInjectiveModel X L)))))) :
    ((derivedSheafHomBifunctor X).obj (op N)).map
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map f).app L) ≫
        (diagonalTargetIso X K' L N).hom =
      (diagonalTargetIso X K L N).hom ≫ τ := by
  have sq1 : ((derivedSheafHomBifunctor X).obj (op N)).map
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map f).app L) ≫
        ((derivedSheafHomBifunctor X).obj (op N)).map
          (diagonalTensorModelIso X K' L).hom =
      ((derivedSheafHomBifunctor X).obj (op N)).map
          (diagonalTensorModelIso X K L).hom ≫
        ((derivedSheafHomBifunctor X).obj (op N)).map σ := by
    rw [← Functor.map_comp, ← Functor.map_comp,
      diagonalTensorModelIso_natural_left X hP hsr hfac L hσ]
  have sq2 := ((derivedSheafHomBifunctor X).map
    (kInjectiveModelIso X N).hom.op).naturality σ
  unfold diagonalTargetIso
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.op_hom]
  exact square_comp sq1 (square_comp sq2
    (diagonalRoofResolutionComparison X hP hsr L N hσ hτ))

include hsr hfac in
/-- The complex-level square for the roof, pushed into the derived category. -/
private lemma diagonalComplexMap_natural_roof
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {τ : DerivedCategory.Q.obj (sheafHomComplex X (kInjectiveModel X L)
          ((kInjectiveResolution X).obj
            (tensorTotal X (kFlatModel X K) (kInjectiveModel X L)))).obj ⟶
        DerivedCategory.Q.obj (sheafHomComplex X (kInjectiveModel X L)
          ((kInjectiveResolution X).obj
            (tensorTotal X (kFlatModel X K') (kInjectiveModel X L)))).obj}
    (hτ : DerivedCategory.Q.map (homMap X (𝟙 (kInjectiveModel X L))
          ((kInjectiveResolution X).map
            (tensorTotalMap X sr (𝟙 (kInjectiveModel X L))))) ≫ τ =
      DerivedCategory.Q.map (homMap X (𝟙 (kInjectiveModel X L))
        ((kInjectiveResolution X).map
          (tensorTotalMap X gr (𝟙 (kInjectiveModel X L)))))) :
    DerivedCategory.Q.map
          (diagonalComplexMap X (kFlatModel X K) (kInjectiveModel X L)) ≫ τ =
      ((kFlatModelIso X K).hom ≫ f ≫ (kFlatModelIso X K').inv) ≫
        DerivedCategory.Q.map
          (diagonalComplexMap X (kFlatModel X K') (kInjectiveModel X L)) := by
  have := hsr
  have hcS := congrArg DerivedCategory.Q.map
    (diagonalComplexMap_natural_left X sr (kInjectiveModel X L))
  have hcG := congrArg DerivedCategory.Q.map
    (diagonalComplexMap_natural_left X gr (kInjectiveModel X L))
  simp only [Functor.map_comp] at hcS hcG
  rw [← cancel_epi (DerivedCategory.Q.map sr), ← Category.assoc, hcS, Category.assoc, hτ,
    ← hcG, ← Category.assoc, hfac]

end DiagonalRoof

/-- **Stacks 0A99: the canonical morphism is functorial in `K`.** For a morphism `f : K ⟶ K'` of
`D(O)` the square

`f ≫ u_{K',L} = u_{K,L} ≫ RSheafHom(𝟙_L, f ⊗ 𝟙_L)`

commutes in `D(O)`: the first variable of the diagonal acts covariantly.

A morphism of `D(O)` does not lift to the chosen K-flat representatives, which are not
K-injective.  It is instead written as a right fraction `inv (Q s₀) ≫ Q g₀`
(`DerivedCategory.right_fac`) and the apex of that roof is replaced by a K-flat resolution of it
(Stacks 06YS), giving a roof `A ⟵ P ⟶ A'` with all three complexes K-flat and the left leg
invertible in `D(O)`.  The one-sided K-flat comparison of Stacks 06YU is then available at all
three vertices, which makes the tensored left leg invertible with no K-flatness of the other
factor, and the square closes from the complex-level functoriality of Stacks 0A93. -/
@[stacks 0A99 "functoriality in K"]
theorem canonicalDerivedDiagonal_natural_left
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (f : K ⟶ K') :
    f ≫ canonicalDerivedDiagonal X K' L =
      canonicalDerivedDiagonal X K L ≫
        ((derivedSheafHomBifunctor X).obj (op L)).map
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map f).app L) := by
  obtain ⟨P₀, s₀, hs₀, g₀, hfac₀⟩ := DerivedCategory.right_fac
    ((kFlatModelIso X K).hom ≫ f ≫ (kFlatModelIso X K').inv)
  obtain ⟨P, p, hP, hp⟩ := Stacks.SheafOfModules.exists_kFlat_quasiIso X P₀
  have := hs₀
  have : QuasiIso p := hp
  have : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hp
  have hsr : IsIso (DerivedCategory.Q.map (p ≫ s₀)) := by
    rw [Functor.map_comp]; infer_instance
  have hfac : DerivedCategory.Q.map (p ≫ s₀) ≫ (kFlatModelIso X K).hom ≫ f ≫
      (kFlatModelIso X K').inv = DerivedCategory.Q.map (p ≫ g₀) := by
    rw [hfac₀, Functor.map_comp, Functor.map_comp, Category.assoc, IsIso.hom_inv_id_assoc]
  have := isIso_Q_map_tensorTotalMap_roof X hP hsr (kInjectiveModel X L)
  have := isIso_Q_map_homMap_roof X L L hP hsr
  obtain ⟨σ, hσ⟩ : ∃ σ, DerivedCategory.Q.map (tensorTotalMap X (p ≫ s₀)
        (𝟙 (kInjectiveModel X L))) ≫ σ =
      DerivedCategory.Q.map (tensorTotalMap X (p ≫ g₀) (𝟙 (kInjectiveModel X L))) :=
    ⟨_, IsIso.hom_inv_id_assoc _ _⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, DerivedCategory.Q.map (homMap X (𝟙 (kInjectiveModel X L))
        ((kInjectiveResolution X).map
          (tensorTotalMap X (p ≫ s₀) (𝟙 (kInjectiveModel X L))))) ≫ τ =
      DerivedCategory.Q.map (homMap X (𝟙 (kInjectiveModel X L))
        ((kInjectiveResolution X).map
          (tensorTotalMap X (p ≫ g₀) (𝟙 (kInjectiveModel X L))))) :=
    ⟨_, IsIso.hom_inv_id_assoc _ _⟩
  have hα : f ≫ (kFlatModelIso X K').inv =
      (kFlatModelIso X K).inv ≫
        ((kFlatModelIso X K).hom ≫ f ≫ (kFlatModelIso X K').inv) := by
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  unfold canonicalDerivedDiagonal
  exact diagonalConjSquare (kFlatModelIso X K) (kFlatModelIso X K')
    (diagonalTargetIso X K L L) (diagonalTargetIso X K' L L) hα
    (diagonalTargetIso_natural_left X hP hsr hfac L L hσ hτ)
    (diagonalComplexMap_natural_roof X hsr hfac L hτ)

end DiagonalTensorVariable

end AlgebraicGeometry.RingedSite

end
