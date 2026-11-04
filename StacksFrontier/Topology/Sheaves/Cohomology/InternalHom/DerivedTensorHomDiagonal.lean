module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TotalComplexNaturality
public import StacksFrontier.CategoryTheory.CommutingSquares
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOnDerivedObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DiagonalKFlatRoof
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorHomInterchange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplexComparison
public import
  StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.InternalHomComplexQuasiIso
import StacksCore.Tactic.StacksAttribute

/-! # Moving a derived tensor factor inside a derived internal Hom

Let `(X, O_X)` be a ringed space and let `K`, `L`, `M` be objects of the derived category
`D(O_X)` of sheaves of `O_X`-modules. **Stacks 0BYS** asserts a canonical morphism

`K ⊗^L_{O_X} RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^L_{O_X} L)`

in `D(O_X)`. This file constructs it, exactly as the source does.

Choose a K-flat complex `A` representing `K`, a K-injective complex `I` representing `L` and
any complex `N` representing `M`. Then `SheafHom(N, I)` represents `RSheafHom(M, L)`, because a
K-injective target computes the derived internal Hom (Stacks 0A97); a K-flat left factor
computes the derived tensor product (Stacks 06YU), so the source of the morphism is the class
of `Tot(A ⊗_{O_X} SheafHom(N, I))` and `K ⊗^L_{O_X} L` is the class of `Tot(A ⊗_{O_X} I)`.
Choosing a quasi-isomorphism `q : Tot(A ⊗_{O_X} I) ⟶ J` with `J` K-injective, the target is the
class of `SheafHom(N, J)`, and the morphism is the class of the composite

`Tot(A ⊗ SheafHom(N, I)) ⟶ SheafHom(N, Tot(A ⊗ I)) ⟶ SheafHom(N, J)`

whose first map is the canonical complex-level morphism of Stacks 0BYR (equivalently, of its
ringed-site form Stacks 0BYT) and whose second is induced by `q`.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedTensorHomModelMap`: the complex-level composite above,
  between the chosen representatives.
* `AlgebraicGeometry.RingedSite.derivedTensorHomSourceIso` and
  `AlgebraicGeometry.RingedSite.derivedTensorHomTargetIso`: the comparisons identifying the
  source and the target of the morphism with classes of complexes.
* `AlgebraicGeometry.RingedSite.derivedTensorHomDiagonal`: the canonical morphism, on a ringed
  site.
* `Stacks.SheafOfModules.DerivedTensorHomDiagonal`: on a ringed space, the datum of such a
  morphism for every triple of objects of `D(O_X)`, together with the characterisation that
  pins it down on the chosen representatives and its functoriality in all three objects.
* `Stacks.SheafOfModules.canonicalDerivedTensorHomDiagonal`: **Stacks 0BYS**, the canonical
  such datum.

## Main results

* `AlgebraicGeometry.RingedSite.derivedTensorHomDiagonal_eq`: the morphism is the class of the
  complex-level morphism, conjugated by the two comparisons. This is what makes the datum
  content rather than an arbitrary morphism, and
  `AlgebraicGeometry.RingedSite.eq_derivedTensorHomDiagonal` is the resulting uniqueness.
* `AlgebraicGeometry.RingedSite.derivedTensorHomDiagonal_natural_left`,
  `AlgebraicGeometry.RingedSite.derivedTensorHomDiagonal_natural_hom` and
  `AlgebraicGeometry.RingedSite.derivedTensorHomDiagonal_natural_right`: **Stacks 0BYS**, the
  morphism is covariant in the tensor factor `K`, covariant in the target `L` of the internal
  Hom and contravariant in its source `M`, for arbitrary morphisms of `D(O)`.
* `Stacks.SheafOfModules.DerivedTensorHomDiagonal.map_unique`: the characterisation determines
  the morphism, so any two such data agree.
* `Stacks.SheafOfModules.exists_derivedTensorHomDiagonal`: the datum exists.

## What this file does not contain

The characterisation `derivedTensorHomDiagonal_eq` is stated at the *chosen* representatives —
`kFlatModel` for `K`, `kInjectiveModel` for `L` and for `M`, and the functorial K-injective
resolution of `Tot(A ⊗ I)` for `J` — and not at an arbitrary K-flat `A`, K-injective `I`,
arbitrary `N`, K-injective `J` and quasi-isomorphism `q : Tot(A ⊗ I) ⟶ J`. It is still what
determines the morphism, by `DerivedTensorHomDiagonal.map_unique`, but it is weaker than the
form in which the source states its construction. Generalising it is now a matter of
transporting the construction along the comparisons once more: for `I`, `N`, `J` and `q` the
lift exists because the chosen models there are K-injective, and for `A` the roof argument used
for the functoriality in the tensor factor applies verbatim. Both are duplications of work
already done here rather than new input, and neither is carried out.

## Implementation notes

Everything is carried out on the ringed site of the opens of the space, along
`Stacks.SheafOfModules.ringedSite`, because that is where all the inputs live in one
vocabulary: the derived internal Hom bifunctor and its K-injective model comparisons
(`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor`,
`derivedSheafHomResolutionComparison`, `derivedSheafHomComparison`), the derived tensor product
with its one-sided K-flat comparison
(`Stacks.SheafOfModules.canonicalDerivedTensorProduct`), and the complex-level morphism. For
that complex-level morphism the ringed-site form `tensorHomInterchange` of Stacks 0BYT is used
rather than the ringed-space form `Stacks.SheafOfModules.diagonalBetter` of Stacks 0BYR: the
two are the same morphism, both being characterised by `k ⊗ φ ↦ (m ↦ k ⊗ φ(m))` on homogeneous
local pure tensors, but they are stated against the two parallel spellings of the induced map
of internal Hom complexes — `AlgebraicGeometry.RingedSite.homMap` and
`Stacks.Cohomology.InternalHom.sheafHomComplexMap` — and only the first is the spelling in
which the comparisons of the derived internal Hom are stated. Identifying the two spellings is
not done here.

There are likewise two total tensor-product complexes on a ringed site, and both occur. The
complex-level morphism is stated at `AlgebraicGeometry.RingedSite.tensorTotal`, which
sheafifies the total complex of the presheaf tensor double complex, while the K-flat
comparisons of the derived tensor product are stated at
`Stacks.SheafOfModules.Tensor.tensorComplex`, which totalises the sheaf tensor double complex.
The bridge is `AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex`, and it appears once
in each of the two comparison isomorphisms.

The functoriality in the tensor factor is the one clause that does not follow from lifting the
given morphism of `D(O)` to the chosen representatives: those are K-flat and not K-injective,
so `AlgebraicGeometry.RingedSite.exists_Q_map_eq_of_isKInjective` does not apply, as it does
for the other two variables. It is obtained instead from a roof with a **K-flat apex**: a
morphism `Q A ⟶ Q A'` is a right fraction `inv (Q s₀) ≫ Q g₀` by `DerivedCategory.right_fac`,
and replacing the apex of that fraction by a K-flat resolution of it (Stacks 06YS,
`Stacks.SheafOfModules.exists_kFlat_quasiIso`) gives `A ⟵ P ⟶ A'` with all three complexes
K-flat and the left leg invertible in `D(O)`. The one-sided K-flat comparison of Stacks 06YU is
then available at all three vertices, and `isIso_of_square` turns that into invertibility of
`Q(Tot(s ⊗ 1_Z))` for an **arbitrary** second factor `Z` — which is what the internal Hom
complex `SheafHom(N, I)` and the complex `I` occurring here need, neither being K-flat. No
acyclicity or mapping-cone argument is involved: the mapping cone of the right leg of the
obvious roof `A ⟶ kInjectiveModel K' ⟵ A'` is *not* K-flat, since `kInjectiveModel K'` is not,
so that roof does not work and the K-flat apex is what makes the argument go through.

The chosen representatives are `AlgebraicGeometry.RingedSite.kFlatModel` for `K`,
`AlgebraicGeometry.RingedSite.kInjectiveModel` for `L` and for `M`, and the functorial
K-injective resolution `AlgebraicGeometry.RingedSite.kInjectiveResolution` of `Tot(A ⊗ I)` for
`J`, with `q` its augmentation. No condition is placed on the representative of `M`: the
derived internal Hom out of an arbitrary source is computed by a K-injective target, and the
K-injective model is used there only as *some* complex representing the object.

The comparison isomorphisms are composites of three and of four factors, and each functoriality
proof is assembled from one commuting square per factor by the two private gluing lemmas
`CategoryTheory.square_comp` and `CategoryTheory.square_comp'`, which differ only in how the
right-hand side is bracketed; this keeps every step a single `rw` against a term whose size would
otherwise make associativity normalisation the dominant cost. The last square of the tensor side is
closed in term mode rather than by `rw`, because `HomologicalComplex.mapBifunctorMap` and
`Stacks.SheafOfModules.Tensor.tensorComplex` are two spellings of one object that `rw` cannot
reconcile while Mathlib's `getColimitCocone` stays unexposed — the hazard already recorded in the
implementation notes of `StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.OnARingedSite`.

The universes are the diagonal `RingedSite.{u, u, u}` of the whole derived internal Hom
cluster, which is where `derivedSheafHomBifunctor` is stated; see the implementation notes of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedInternalHom`.

## References

* [Stacks Project, Tag 0BYS](https://stacks.math.columbia.edu/tag/0BYS)
* [Stacks Project, Tag 0BYR](https://stacks.math.columbia.edu/tag/0BYR)
* [Stacks Project, Tag 0BYT](https://stacks.math.columbia.edu/tag/0BYT)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

/-- A morphism fitting into a commuting square whose other three sides are isomorphisms is an
isomorphism. -/
private lemma isIso_of_square {C : Type*} [Category C] {P P' Q Q' : C}
    {α : P ⟶ P'} {u : P ⟶ Q} {u' : P' ⟶ Q'} {k : Q ⟶ Q'}
    [IsIso α] [IsIso u] [IsIso u'] (h : α ≫ u' = u ≫ k) : IsIso k := by
  have : IsIso (u ≫ k) := by rw [← h]; infer_instance
  exact IsIso.of_isIso_comp_left u k

/-- A square of morphisms conjugated by four comparison isomorphisms commutes as soon as both
comparisons are compatible with the given morphisms and the conjugated square commutes.
Stated in an arbitrary category so that it is applied, rather than re-elaborated, at the
functorialities below. -/
private lemma conjugated_square {C : Type*} [Category C]
    {Src Src' Tgt Tgt' S S' T T' : C}
    (sIso : Src ≅ S) (sIso' : Src' ≅ S') (tIso : Tgt ≅ T) (tIso' : Tgt' ≅ T')
    {α : Src ⟶ Src'} {β : Tgt ⟶ Tgt'} {σ : S ⟶ S'} {τ : T ⟶ T'} {θ : S ⟶ T} {θ' : S' ⟶ T'}
    (hα : α ≫ sIso'.hom = sIso.hom ≫ σ) (hβ : β ≫ tIso'.hom = tIso.hom ≫ τ)
    (hθ : θ ≫ τ = σ ≫ θ') :
    α ≫ sIso'.hom ≫ θ' ≫ tIso'.inv = (sIso.hom ≫ θ ≫ tIso.inv) ≫ β := by
  have hβ' : tIso.inv ≫ β = τ ≫ tIso'.inv := by
    rw [← Category.comp_id (tIso.inv ≫ β), ← tIso'.hom_inv_id, ← Category.assoc,
      Category.assoc tIso.inv, hβ, ← Category.assoc, tIso.inv_hom_id, Category.id_comp]
  have h1 : α ≫ sIso'.hom ≫ θ' ≫ tIso'.inv = sIso.hom ≫ σ ≫ θ' ≫ tIso'.inv := by
    rw [← Category.assoc, hα, Category.assoc]
  have h2 : σ ≫ θ' ≫ tIso'.inv = θ ≫ τ ≫ tIso'.inv := by
    rw [← Category.assoc, ← hθ, Category.assoc]
  rw [h1, h2, ← hβ']
  simp only [Category.assoc]

/-- A commuting square stays commuting after applying any functor. -/
private lemma map_square {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {P P' Q Q' : C}
    {f : P ⟶ P'} {g : Q ⟶ Q'} {u : P ⟶ Q} {u' : P' ⟶ Q'} (h : f ≫ u' = u ≫ g) :
    F.map f ≫ F.map u' = F.map u ≫ F.map g := by
  rw [← F.map_comp, ← F.map_comp, h]

variable (X : RingedSite.{u, u, u})

section SourceLift

variable {M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
  {h : M' ⟶ M} {t : kInjectiveModel X M' ⟶ kInjectiveModel X M}
  (ht : DerivedCategory.Q.map t =
    (kInjectiveModelIso X M').hom ≫ h ≫ (kInjectiveModelIso X M).inv)

include ht in
/-- Moving a morphism of `D(O)` past the comparisons with the chosen K-injective
representatives of the source of an internal Hom replaces it by the class of its lift. -/
private lemma map_op_kInjectiveModelIso_comp
    (Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((derivedSheafHomBifunctor X).map h.op).app Z ≫
        ((derivedSheafHomBifunctor X).map (kInjectiveModelIso X M').hom.op).app Z =
      ((derivedSheafHomBifunctor X).map (kInjectiveModelIso X M).hom.op).app Z ≫
        ((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map t).op).app Z := by
  have hcomp : (kInjectiveModelIso X M').hom ≫ h =
      DerivedCategory.Q.map t ≫ (kInjectiveModelIso X M).hom := by
    rw [ht, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← Functor.map_comp, ← Functor.map_comp,
    ← op_comp, ← op_comp, hcomp]

end SourceLift

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

section Construction

variable (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- The chosen complex model of `K ⊗^L_O L`: the total tensor product of the chosen K-flat
representative of `K` with the chosen K-injective representative of `L`. -/
abbrev derivedTensorHomTensorModel :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  tensorTotal X (kFlatModel X K) (kInjectiveModel X L)

/-- The chosen complex model of `K ⊗^L_O RSheafHom(M, L)`: the total tensor product of the
chosen K-flat representative of `K` with the internal Hom complex from the chosen
representative of `M` into the chosen K-injective representative of `L`. -/
abbrev derivedTensorHomSourceModel :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  tensorTotal X (kFlatModel X K)
    (sheafHomComplex X (kInjectiveModel X M) (kInjectiveModel X L)).obj

/-- The chosen complex model of `RSheafHom(M, K ⊗^L_O L)`: the internal Hom complex from the
chosen representative of `M` into the chosen K-injective resolution of the complex model of
`K ⊗^L_O L`. -/
abbrev derivedTensorHomTargetModel :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  (sheafHomComplex X (kInjectiveModel X M)
    ((kInjectiveResolution X).obj (derivedTensorHomTensorModel X K L))).obj

/-- The complex-level morphism of Stacks 0BYR out of an arbitrary complex `A` in the tensor
slot, followed by the map induced by the K-injective resolution of `Tot(A ⊗_O I)`. The chosen
K-flat representative is only one instance of it, and the functoriality in the tensor factor
needs the others. -/
def derivedTensorHomComplexMap
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    tensorTotal X A (sheafHomComplex X (kInjectiveModel X M) (kInjectiveModel X L)).obj ⟶
      (sheafHomComplex X (kInjectiveModel X M)
        ((kInjectiveResolution X).obj (tensorTotal X A (kInjectiveModel X L)))).obj :=
  tensorHomInterchange X A (kInjectiveModel X L) (kInjectiveModel X M) ≫
    homMap X (𝟙 (kInjectiveModel X M))
      ((kInjectiveAugmentation X).app (tensorTotal X A (kInjectiveModel X L)))

/-- The complex-level morphism of Stacks 0BYR between the chosen representatives, followed by
the map induced by the K-injective resolution of the total tensor product. -/
def derivedTensorHomModelMap :
    derivedTensorHomSourceModel X K L M ⟶ derivedTensorHomTargetModel X K L M :=
  tensorHomInterchange X (kFlatModel X K) (kInjectiveModel X L) (kInjectiveModel X M) ≫
    homMap X (𝟙 (kInjectiveModel X M))
      ((kInjectiveAugmentation X).app (derivedTensorHomTensorModel X K L))

/-- The chosen complex-level morphism is the one attached to the chosen K-flat
representative. -/
theorem derivedTensorHomModelMap_eq_complexMap :
    derivedTensorHomModelMap X K L M =
      derivedTensorHomComplexMap X (kFlatModel X K) L M := rfl

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
      HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
        (ComplexShape.up ℤ)] in
/-- **The complex-level morphism is covariant in the tensor slot**: this is the functoriality
of Stacks 0BYR in its first complex, together with the naturality of the K-injective resolution
augmentation. No condition is placed on the two complexes. -/
theorem derivedTensorHomComplexMap_naturality_left
    {A A₀ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (c : A ⟶ A₀) :
    derivedTensorHomComplexMap X A L M ≫
        homMap X (𝟙 (kInjectiveModel X M)) ((kInjectiveResolution X).map
          (tensorTotalMap X c (𝟙 (kInjectiveModel X L)))) =
      tensorTotalMap X c
          (𝟙 (sheafHomComplex X (kInjectiveModel X M) (kInjectiveModel X L)).obj) ≫
        derivedTensorHomComplexMap X A₀ L M := by
  have hn := tensorHomInterchange_natural X c (𝟙 (kInjectiveModel X L))
    (𝟙 (kInjectiveModel X M))
  rw [homMap_id] at hn
  have haug : tensorTotalMap X c (𝟙 (kInjectiveModel X L)) ≫
      (kInjectiveAugmentation X).app (tensorTotal X A₀ (kInjectiveModel X L)) =
      (kInjectiveAugmentation X).app (tensorTotal X A (kInjectiveModel X L)) ≫
        (kInjectiveResolution X).map (tensorTotalMap X c (𝟙 (kInjectiveModel X L))) :=
    (kInjectiveAugmentation X).naturality _
  unfold derivedTensorHomComplexMap
  rw [Category.assoc, homMap_comp, ← Category.assoc, ← hn, Category.assoc, homMap_comp,
    ← haug]

/-- `RSheafHom(M, L)` is the class of the internal Hom complex from the chosen representative
of `M` into the chosen K-injective representative of `L`. -/
def derivedSheafHomObjectsKInjectiveModelIso :
    ((derivedSheafHomBifunctor X).obj (op M)).obj L ≅
      DerivedCategory.Q.obj
        (sheafHomComplex X (kInjectiveModel X M) (kInjectiveModel X L)).obj :=
  derivedSheafHomObjectsModelIso X (kInjectiveModelIso X M) (kInjectiveModelIso X L) ≪≫
    derivedSheafHomComparison X (kInjectiveModel X M) (kInjectiveModel X L)

/-- `K ⊗^L_O L` is the class of the total tensor product of the chosen K-flat representative
of `K` with the chosen K-injective representative of `L`, by the one-sided K-flat comparison
of Stacks 06YU and the comparison of the two total tensor-product complexes. -/
def derivedTensorObjectsKFlatLeftModelIso :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L ≅
      DerivedCategory.Q.obj (derivedTensorHomTensorModel X K L) :=
  ((Stacks.SheafOfModules.derivedTensorProductFunctor X).mapIso
      (kFlatModelIso X K).symm).app L ≪≫
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
        (DerivedCategory.Q.obj (kFlatModel X K))).mapIso (kInjectiveModelIso X L).symm ≪≫
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft
          (kFlatModel X K) (kInjectiveModel X L) (isKFlat_kFlatModel X K) ≪≫
        (DerivedCategory.Q.mapIso (tensorTotalIsoTensorComplex X (kFlatModel X K)
          (kInjectiveModel X L))).symm

/-- The source of the diagonal morphism is the class of its chosen complex model. -/
def derivedTensorHomSourceIso :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj
        (((derivedSheafHomBifunctor X).obj (op M)).obj L) ≅
      DerivedCategory.Q.obj (derivedTensorHomSourceModel X K L M) :=
  ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).mapIso
      (derivedSheafHomObjectsKInjectiveModelIso X L M) ≪≫
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).mapIso
        (kFlatModelIso X K).symm).app
      (DerivedCategory.Q.obj
        (sheafHomComplex X (kInjectiveModel X M) (kInjectiveModel X L)).obj) ≪≫
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft
          (kFlatModel X K)
          (sheafHomComplex X (kInjectiveModel X M) (kInjectiveModel X L)).obj
          (isKFlat_kFlatModel X K) ≪≫
        (DerivedCategory.Q.mapIso (tensorTotalIsoTensorComplex X (kFlatModel X K)
          (sheafHomComplex X (kInjectiveModel X M) (kInjectiveModel X L)).obj)).symm

/-- The target of the diagonal morphism is the class of its chosen complex model. -/
def derivedTensorHomTargetIso :
    ((derivedSheafHomBifunctor X).obj (op M)).obj
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L) ≅
      DerivedCategory.Q.obj (derivedTensorHomTargetModel X K L M) :=
  ((derivedSheafHomBifunctor X).obj (op M)).mapIso
      (derivedTensorObjectsKFlatLeftModelIso X K L) ≪≫
    ((derivedSheafHomBifunctor X).mapIso (kInjectiveModelIso X M).op).app
        (DerivedCategory.Q.obj (derivedTensorHomTensorModel X K L)) ≪≫
      derivedSheafHomResolutionComparison X (kInjectiveModel X M)
        (derivedTensorHomTensorModel X K L)

/-- **The diagonal morphism of Stacks 0BYS.** For objects `K`, `L`, `M` of `D(O)` the canonical
morphism

`K ⊗^L_O RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^L_O L)`

in `D(O)`: the class of the complex-level morphism of Stacks 0BYR between the chosen
representatives, conjugated by the comparisons identifying source and target with classes of
complexes. -/
def derivedTensorHomDiagonal :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj
        (((derivedSheafHomBifunctor X).obj (op M)).obj L) ⟶
      ((derivedSheafHomBifunctor X).obj (op M)).obj
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L) :=
  (derivedTensorHomSourceIso X K L M).hom ≫
    DerivedCategory.Q.map (derivedTensorHomModelMap X K L M) ≫
      (derivedTensorHomTargetIso X K L M).inv

/-- **The diagonal morphism is the complex-level morphism of Stacks 0BYR**, read through the
two comparisons. In particular it is not an arbitrary morphism between the two objects. -/
theorem derivedTensorHomDiagonal_eq :
    (derivedTensorHomSourceIso X K L M).inv ≫ derivedTensorHomDiagonal X K L M ≫
        (derivedTensorHomTargetIso X K L M).hom =
      DerivedCategory.Q.map (derivedTensorHomModelMap X K L M) := by
  rw [derivedTensorHomDiagonal]
  simp

/-- A morphism satisfying the characterisation of `derivedTensorHomDiagonal` is that
morphism. -/
theorem eq_derivedTensorHomDiagonal
    {φ : ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj
        (((derivedSheafHomBifunctor X).obj (op M)).obj L) ⟶
      ((derivedSheafHomBifunctor X).obj (op M)).obj
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L)}
    (hφ : (derivedTensorHomSourceIso X K L M).inv ≫ φ ≫
        (derivedTensorHomTargetIso X K L M).hom =
      DerivedCategory.Q.map (derivedTensorHomModelMap X K L M)) :
    φ = derivedTensorHomDiagonal X K L M := by
  have h := hφ.trans (derivedTensorHomDiagonal_eq X K L M).symm
  refine (Iso.cancel_iso_inv_left (derivedTensorHomSourceIso X K L M) _ _).mp ?_
  refine (Iso.cancel_iso_hom_right _ _ (derivedTensorHomTargetIso X K L M)).mp ?_
  simpa only [Category.assoc] using h

end Construction

section Naturality

variable (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  {M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
  {h : M' ⟶ M} {t : kInjectiveModel X M' ⟶ kInjectiveModel X M}
  (ht : DerivedCategory.Q.map t =
    (kInjectiveModelIso X M').hom ≫ h ≫ (kInjectiveModelIso X M).inv)

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
      HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
        (ComplexShape.up ℤ)] in
include ht in
/-- The comparison of `RSheafHom(M, L)` with the internal Hom complex of the chosen
representatives intertwines a morphism of `D(O)` in the source variable with the map of
internal Hom complexes induced by its lift. -/
private lemma derivedSheafHomObjectsKInjectiveModelIso_naturality_hom :
    ((derivedSheafHomBifunctor X).map h.op).app L ≫
        (derivedSheafHomObjectsKInjectiveModelIso X L M').hom =
      (derivedSheafHomObjectsKInjectiveModelIso X L M).hom ≫
        DerivedCategory.Q.map (homMap X t (𝟙 (kInjectiveModel X L))) := by
  have key : ((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map t).op).app
          (DerivedCategory.Q.obj (kInjectiveModel X L)) ≫
        (derivedSheafHomComparison X (kInjectiveModel X M') (kInjectiveModel X L)).hom =
      (derivedSheafHomComparison X (kInjectiveModel X M) (kInjectiveModel X L)).hom ≫
        DerivedCategory.Q.map (homMap X t (𝟙 (kInjectiveModel X L))) := by
    simpa using derivedSheafHomComparison_naturality X t (𝟙 (kInjectiveModel X L))
  unfold derivedSheafHomObjectsKInjectiveModelIso derivedSheafHomObjectsModelIso
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  exact square_comp' (map_op_kInjectiveModelIso_comp X ht L)
    (square_comp' (((derivedSheafHomBifunctor X).map
      (DerivedCategory.Q.map t).op).naturality (kInjectiveModelIso X L).inv).symm key)

include ht in
/-- The source comparison intertwines the map induced on `RSheafHom(-, L)` with the map of
total tensor products induced by the lift. -/
private lemma derivedTensorHomSourceIso_naturality_hom :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map
          (((derivedSheafHomBifunctor X).map h.op).app L) ≫
        (derivedTensorHomSourceIso X K L M').hom =
      (derivedTensorHomSourceIso X K L M).hom ≫
        DerivedCategory.Q.map (tensorTotalMap X (𝟙 (kFlatModel X K))
          (homMap X t (𝟙 (kInjectiveModel X L)))) := by
  have sq1 := map_square ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K)
    (derivedSheafHomObjectsKInjectiveModelIso_naturality_hom X L ht)
  have sq2 := ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
      (kFlatModelIso X K).inv).naturality
    (DerivedCategory.Q.map (homMap X t (𝟙 (kInjectiveModel X L))))
  have sq34 := comparisonLeft_tensorTotal_naturality_right X (kFlatModel X K)
    (homMap X t (𝟙 (kInjectiveModel X L))) (isKFlat_kFlatModel X K)
  unfold derivedTensorHomSourceIso
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.mapIso_inv, Iso.symm_hom]
  simpa only [Category.assoc] using square_comp sq1 (square_comp sq2 sq34)

include ht in
/-- The target comparison intertwines the map induced on `RSheafHom(-, K ⊗^L_O L)` with the map
of internal Hom complexes induced by the lift. -/
private lemma derivedTensorHomTargetIso_naturality_hom :
    ((derivedSheafHomBifunctor X).map h.op).app
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L) ≫
        (derivedTensorHomTargetIso X K L M').hom =
      (derivedTensorHomTargetIso X K L M).hom ≫
        DerivedCategory.Q.map (homMap X t
          (𝟙 ((kInjectiveResolution X).obj (derivedTensorHomTensorModel X K L)))) := by
  have key : ((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map t).op).app
          (DerivedCategory.Q.obj (derivedTensorHomTensorModel X K L)) ≫
        (derivedSheafHomResolutionComparison X (kInjectiveModel X M')
          (derivedTensorHomTensorModel X K L)).hom =
      (derivedSheafHomResolutionComparison X (kInjectiveModel X M)
          (derivedTensorHomTensorModel X K L)).hom ≫
        DerivedCategory.Q.map (homMap X t
          (𝟙 ((kInjectiveResolution X).obj (derivedTensorHomTensorModel X K L)))) := by
    simpa using derivedSheafHomResolutionComparison_naturality X t
      (𝟙 (derivedTensorHomTensorModel X K L))
  unfold derivedTensorHomTargetIso
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.op_hom]
  exact square_comp (((derivedSheafHomBifunctor X).map h.op).naturality
      (derivedTensorObjectsKFlatLeftModelIso X K L).hom).symm
    (square_comp (map_op_kInjectiveModelIso_comp X ht
      (DerivedCategory.Q.obj (derivedTensorHomTensorModel X K L))) key)

/-- The complex-level morphism is contravariant in the source of the internal Hom: this is the
functoriality of Stacks 0BYR in its third complex, together with the compatibility of the
K-injective resolution with the map induced on internal Hom complexes. -/
private lemma derivedTensorHomModelMap_naturality_hom
    (s : kInjectiveModel X M' ⟶ kInjectiveModel X M) :
    derivedTensorHomModelMap X K L M ≫
        homMap X s (𝟙 ((kInjectiveResolution X).obj (derivedTensorHomTensorModel X K L))) =
      tensorTotalMap X (𝟙 (kFlatModel X K)) (homMap X s (𝟙 (kInjectiveModel X L))) ≫
        derivedTensorHomModelMap X K L M' := by
  have hn := tensorHomInterchange_natural X (𝟙 (kFlatModel X K))
    (𝟙 (kInjectiveModel X L)) s
  rw [tensorTotalMap_id] at hn
  unfold derivedTensorHomModelMap
  rw [Category.assoc, homMap_comp, ← Category.assoc, ← hn, Category.assoc, homMap_comp]
  simp only [Category.comp_id, Category.id_comp]

/-- **Stacks 0BYS.** The diagonal morphism is contravariant in the source of the internal Hom,
for an arbitrary morphism of `D(O)`. -/
@[stacks 0BYS "functoriality in the source of the internal Hom"]
theorem derivedTensorHomDiagonal_natural_hom (g : M' ⟶ M) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map
          (((derivedSheafHomBifunctor X).map g.op).app L) ≫
        derivedTensorHomDiagonal X K L M' =
      derivedTensorHomDiagonal X K L M ≫
        ((derivedSheafHomBifunctor X).map g.op).app
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L) := by
  obtain ⟨s, hs⟩ := exists_Q_map_eq_of_isKInjective X
    ((kInjectiveModelIso X M').hom ≫ g ≫ (kInjectiveModelIso X M).inv)
  have hθ := map_square DerivedCategory.Q (derivedTensorHomModelMap_naturality_hom X K L s)
  unfold derivedTensorHomDiagonal
  exact conjugated_square (derivedTensorHomSourceIso X K L M)
    (derivedTensorHomSourceIso X K L M') (derivedTensorHomTargetIso X K L M)
    (derivedTensorHomTargetIso X K L M')
    (derivedTensorHomSourceIso_naturality_hom X K L hs)
    (derivedTensorHomTargetIso_naturality_hom X K L hs) hθ

section TargetVariable

variable (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  {L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
  (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  {v : L ⟶ L'} {s : kInjectiveModel X L ⟶ kInjectiveModel X L'}
  (hs : DerivedCategory.Q.map s =
    (kInjectiveModelIso X L).hom ≫ v ≫ (kInjectiveModelIso X L').inv)

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
      HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
        (ComplexShape.up ℤ)] in
include hs in
/-- A morphism of `D(O)` composed with the comparison of its target with the chosen
K-injective representative is that comparison for the source followed by the class of the
lift. -/
private lemma kInjectiveModelIso_inv_comp :
    v ≫ (kInjectiveModelIso X L').inv =
      (kInjectiveModelIso X L).inv ≫ DerivedCategory.Q.map s := by
  rw [hs, ← Category.assoc, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
      HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
        (ComplexShape.up ℤ)] in
include hs in
/-- The comparison of `RSheafHom(M, L)` with the internal Hom complex of the chosen
representatives intertwines a morphism of `D(O)` in the target variable with the map of
internal Hom complexes induced by its lift. -/
private lemma derivedSheafHomObjectsKInjectiveModelIso_naturality_right :
    ((derivedSheafHomBifunctor X).obj (op M)).map v ≫
        (derivedSheafHomObjectsKInjectiveModelIso X L' M).hom =
      (derivedSheafHomObjectsKInjectiveModelIso X L M).hom ≫
        DerivedCategory.Q.map (homMap X (𝟙 (kInjectiveModel X M)) s) := by
  have key : ((derivedSheafHomBifunctor X).obj
            (op (DerivedCategory.Q.obj (kInjectiveModel X M)))).map
          (DerivedCategory.Q.map s) ≫
        (derivedSheafHomComparison X (kInjectiveModel X M) (kInjectiveModel X L')).hom =
      (derivedSheafHomComparison X (kInjectiveModel X M) (kInjectiveModel X L)).hom ≫
        DerivedCategory.Q.map (homMap X (𝟙 (kInjectiveModel X M)) s) := by
    simpa using derivedSheafHomComparison_naturality X (𝟙 (kInjectiveModel X M)) s
  have sqb := map_square ((derivedSheafHomBifunctor X).obj
    (op (DerivedCategory.Q.obj (kInjectiveModel X M)))) (kInjectiveModelIso_inv_comp X hs)
  unfold derivedSheafHomObjectsKInjectiveModelIso derivedSheafHomObjectsModelIso
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.op_hom,
    Category.assoc]
  exact square_comp' (((derivedSheafHomBifunctor X).map
    (kInjectiveModelIso X M).hom.op).naturality v) (square_comp' sqb key)

include hs in
/-- The comparison of `K ⊗^L_O L` with the total tensor product of the chosen representatives
intertwines a morphism of `D(O)` in the right factor with the map of total tensor products
induced by its lift. -/
private lemma derivedTensorObjectsKFlatLeftModelIso_naturality_right :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map v ≫
        (derivedTensorObjectsKFlatLeftModelIso X K L').hom =
      (derivedTensorObjectsKFlatLeftModelIso X K L).hom ≫
        DerivedCategory.Q.map (tensorTotalMap X (𝟙 (kFlatModel X K)) s) := by
  have sqb := map_square ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
    (DerivedCategory.Q.obj (kFlatModel X K))) (kInjectiveModelIso_inv_comp X hs)
  have sqcd := comparisonLeft_tensorTotal_naturality_right X (kFlatModel X K) s
    (isKFlat_kFlatModel X K)
  unfold derivedTensorObjectsKFlatLeftModelIso
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.mapIso_inv, Iso.symm_hom]
  simpa only [Category.assoc] using square_comp
    (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
      (kFlatModelIso X K).inv).naturality v) (square_comp sqb sqcd)

include hs in
/-- The source comparison intertwines the map induced on `RSheafHom(M, -)` with the map of
total tensor products induced by the lift. -/
private lemma derivedTensorHomSourceIso_naturality_right :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map
          (((derivedSheafHomBifunctor X).obj (op M)).map v) ≫
        (derivedTensorHomSourceIso X K L' M).hom =
      (derivedTensorHomSourceIso X K L M).hom ≫
        DerivedCategory.Q.map (tensorTotalMap X (𝟙 (kFlatModel X K))
          (homMap X (𝟙 (kInjectiveModel X M)) s)) := by
  have sq1 := map_square ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K)
    (derivedSheafHomObjectsKInjectiveModelIso_naturality_right X M hs)
  have sq2 := ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
      (kFlatModelIso X K).inv).naturality
    (DerivedCategory.Q.map (homMap X (𝟙 (kInjectiveModel X M)) s))
  have sq34 := comparisonLeft_tensorTotal_naturality_right X (kFlatModel X K)
    (homMap X (𝟙 (kInjectiveModel X M)) s) (isKFlat_kFlatModel X K)
  unfold derivedTensorHomSourceIso
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.mapIso_inv, Iso.symm_hom]
  simpa only [Category.assoc] using square_comp sq1 (square_comp sq2 sq34)

include hs in
/-- The target comparison intertwines the map induced on `K ⊗^L_O -` with the map of internal
Hom complexes induced by the resolution of the lift. -/
private lemma derivedTensorHomTargetIso_naturality_right :
    ((derivedSheafHomBifunctor X).obj (op M)).map
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map v) ≫
        (derivedTensorHomTargetIso X K L' M).hom =
      (derivedTensorHomTargetIso X K L M).hom ≫
        DerivedCategory.Q.map (homMap X (𝟙 (kInjectiveModel X M))
          ((kInjectiveResolution X).map (tensorTotalMap X (𝟙 (kFlatModel X K)) s))) := by
  have sq1 := map_square ((derivedSheafHomBifunctor X).obj (op M))
    (derivedTensorObjectsKFlatLeftModelIso_naturality_right X K hs)
  have sq2 := ((derivedSheafHomBifunctor X).map
      (kInjectiveModelIso X M).hom.op).naturality
    (DerivedCategory.Q.map (tensorTotalMap X (𝟙 (kFlatModel X K)) s))
  have sq3 : ((derivedSheafHomBifunctor X).obj
            (op (DerivedCategory.Q.obj (kInjectiveModel X M)))).map
          (DerivedCategory.Q.map (tensorTotalMap X (𝟙 (kFlatModel X K)) s)) ≫
        (derivedSheafHomResolutionComparison X (kInjectiveModel X M)
          (derivedTensorHomTensorModel X K L')).hom =
      (derivedSheafHomResolutionComparison X (kInjectiveModel X M)
          (derivedTensorHomTensorModel X K L)).hom ≫
        DerivedCategory.Q.map (homMap X (𝟙 (kInjectiveModel X M))
          ((kInjectiveResolution X).map (tensorTotalMap X (𝟙 (kFlatModel X K)) s))) := by
    simpa using derivedSheafHomResolutionComparison_naturality X
      (𝟙 (kInjectiveModel X M)) (tensorTotalMap X (𝟙 (kFlatModel X K)) s)
  unfold derivedTensorHomTargetIso
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.op_hom]
  exact square_comp sq1 (square_comp sq2 sq3)

/-- The complex-level morphism is covariant in the target of the internal Hom: this is the
functoriality of Stacks 0BYR in its second complex, together with the naturality of the
K-injective resolution augmentation. -/
private lemma derivedTensorHomModelMap_naturality_right
    (r : kInjectiveModel X L ⟶ kInjectiveModel X L') :
    derivedTensorHomModelMap X K L M ≫
        homMap X (𝟙 (kInjectiveModel X M)) ((kInjectiveResolution X).map
          (tensorTotalMap X (𝟙 (kFlatModel X K)) r)) =
      tensorTotalMap X (𝟙 (kFlatModel X K)) (homMap X (𝟙 (kInjectiveModel X M)) r) ≫
        derivedTensorHomModelMap X K L' M := by
  have hn := tensorHomInterchange_natural X (𝟙 (kFlatModel X K)) r
    (𝟙 (kInjectiveModel X M))
  have haug : tensorTotalMap X (𝟙 (kFlatModel X K)) r ≫
      (kInjectiveAugmentation X).app (derivedTensorHomTensorModel X K L') =
      (kInjectiveAugmentation X).app (derivedTensorHomTensorModel X K L) ≫
        (kInjectiveResolution X).map (tensorTotalMap X (𝟙 (kFlatModel X K)) r) :=
    (kInjectiveAugmentation X).naturality _
  unfold derivedTensorHomModelMap
  rw [Category.assoc, homMap_comp, ← Category.assoc, ← hn, Category.assoc, homMap_comp,
    ← haug]

/-- **Stacks 0BYS.** The diagonal morphism is covariant in the target of the internal Hom, for
an arbitrary morphism of `D(O)`. -/
@[stacks 0BYS "functoriality in the target of the internal Hom"]
theorem derivedTensorHomDiagonal_natural_right (g : L ⟶ L') :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map
          (((derivedSheafHomBifunctor X).obj (op M)).map g) ≫
        derivedTensorHomDiagonal X K L' M =
      derivedTensorHomDiagonal X K L M ≫
        ((derivedSheafHomBifunctor X).obj (op M)).map
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map g) := by
  obtain ⟨r, hr⟩ := exists_Q_map_eq_of_isKInjective X
    ((kInjectiveModelIso X L).hom ≫ g ≫ (kInjectiveModelIso X L').inv)
  have hθ := map_square DerivedCategory.Q (derivedTensorHomModelMap_naturality_right X K M r)
  unfold derivedTensorHomDiagonal
  exact conjugated_square (derivedTensorHomSourceIso X K L M)
    (derivedTensorHomSourceIso X K L' M) (derivedTensorHomTargetIso X K L M)
    (derivedTensorHomTargetIso X K L' M)
    (derivedTensorHomSourceIso_naturality_right X K M hr)
    (derivedTensorHomTargetIso_naturality_right X K M hr) hθ

end TargetVariable

section TensorVariable

variable (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
      HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
        (ComplexShape.up ℤ)] in
/-- The resolution comparison of the derived internal Hom is natural in its target along the
morphism of total tensor products induced by a morphism in the tensor slot. -/
private lemma derivedSheafHomResolutionComparison_naturality_tensorTotalMap
    {A A₀ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (c : A ⟶ A₀) :
    ((derivedSheafHomBifunctor X).obj
            (op (DerivedCategory.Q.obj (kInjectiveModel X M)))).map
          (DerivedCategory.Q.map (tensorTotalMap X c (𝟙 (kInjectiveModel X L)))) ≫
        (derivedSheafHomResolutionComparison X (kInjectiveModel X M)
          (tensorTotal X A₀ (kInjectiveModel X L))).hom =
      (derivedSheafHomResolutionComparison X (kInjectiveModel X M)
          (tensorTotal X A (kInjectiveModel X L))).hom ≫
        DerivedCategory.Q.map (homMap X (𝟙 (kInjectiveModel X M))
          ((kInjectiveResolution X).map
            (tensorTotalMap X c (𝟙 (kInjectiveModel X L))))) := by
  simpa using derivedSheafHomResolutionComparison_naturality X (𝟙 (kInjectiveModel X M))
    (tensorTotalMap X c (𝟙 (kInjectiveModel X L)))

variable {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
  {w : K ⟶ K'}

section Roof

variable {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
  (hP : Stacks.SheafOfModules.IsKFlat X.O P)
  {sr : P ⟶ kFlatModel X K} {gr : P ⟶ kFlatModel X K'}
  (hsr : IsIso (DerivedCategory.Q.map sr))
  (hfac : DerivedCategory.Q.map sr ≫ (kFlatModelIso X K).hom ≫ w ≫
    (kFlatModelIso X K').inv = DerivedCategory.Q.map gr)

include hP hsr hfac in
/-- **The roof square.** Moving the given morphism of `D(O)` past the comparisons with the two
chosen K-flat representatives replaces it by the morphism of the classes of the total tensor
products that the roof determines, for an arbitrary second factor. -/
private lemma roofComparison
    (Z : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {σ : DerivedCategory.Q.obj (tensorTotal X (kFlatModel X K) Z) ⟶
      DerivedCategory.Q.obj (tensorTotal X (kFlatModel X K') Z)}
    (hσ : DerivedCategory.Q.map (tensorTotalMap X sr (𝟙 Z)) ≫ σ =
      DerivedCategory.Q.map (tensorTotalMap X gr (𝟙 Z))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
            ((kFlatModelIso X K).hom ≫ w ≫ (kFlatModelIso X K').inv)).app
          (DerivedCategory.Q.obj Z) ≫
        ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft
            (kFlatModel X K') Z (isKFlat_kFlatModel X K')).hom ≫
          DerivedCategory.Q.map (tensorTotalIsoTensorComplex X (kFlatModel X K') Z).inv =
      (((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft
            (kFlatModel X K) Z (isKFlat_kFlatModel X K)).hom ≫
          DerivedCategory.Q.map
            (tensorTotalIsoTensorComplex X (kFlatModel X K) Z).inv) ≫ σ := by
  have := hsr
  have hcomp : ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
        (DerivedCategory.Q.map sr)).app (DerivedCategory.Q.obj Z) ≫
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
        ((kFlatModelIso X K).hom ≫ w ≫ (kFlatModelIso X K').inv)).app
          (DerivedCategory.Q.obj Z) =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
        (DerivedCategory.Q.map gr)).app (DerivedCategory.Q.obj Z) := by
    rw [← NatTrans.comp_app, ← Functor.map_comp, hfac]
  rw [← cancel_epi (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
      (DerivedCategory.Q.map sr)).app (DerivedCategory.Q.obj Z)),
    ← Category.assoc, hcomp,
    comparisonLeft_tensorTotal_naturality_left X hP (isKFlat_kFlatModel X K') gr Z]
  simp only [Category.assoc]
  rw [reassoc_of% (comparisonLeft_tensorTotal_naturality_left X hP (isKFlat_kFlatModel X K) sr Z),
    hσ]

include hP hsr in
/-- The roof square for the K-injective resolution comparison: the morphism of the classes of
the total tensor products that the roof determines is matched by the morphism of internal Hom
complexes induced by the resolution of the roof. -/
private lemma roofResolutionComparison
    {σ : DerivedCategory.Q.obj (derivedTensorHomTensorModel X K L) ⟶
      DerivedCategory.Q.obj (derivedTensorHomTensorModel X K' L)}
    (hσ : DerivedCategory.Q.map (tensorTotalMap X sr (𝟙 (kInjectiveModel X L))) ≫ σ =
      DerivedCategory.Q.map (tensorTotalMap X gr (𝟙 (kInjectiveModel X L))))
    {τ : DerivedCategory.Q.obj (derivedTensorHomTargetModel X K L M) ⟶
      DerivedCategory.Q.obj (derivedTensorHomTargetModel X K' L M)}
    (hτ : DerivedCategory.Q.map (homMap X (𝟙 (kInjectiveModel X M))
          ((kInjectiveResolution X).map
            (tensorTotalMap X sr (𝟙 (kInjectiveModel X L))))) ≫ τ =
      DerivedCategory.Q.map (homMap X (𝟙 (kInjectiveModel X M))
        ((kInjectiveResolution X).map
          (tensorTotalMap X gr (𝟙 (kInjectiveModel X L)))))) :
    ((derivedSheafHomBifunctor X).obj
            (op (DerivedCategory.Q.obj (kInjectiveModel X M)))).map σ ≫
        (derivedSheafHomResolutionComparison X (kInjectiveModel X M)
          (derivedTensorHomTensorModel X K' L)).hom =
      (derivedSheafHomResolutionComparison X (kInjectiveModel X M)
          (derivedTensorHomTensorModel X K L)).hom ≫ τ := by
  have := isIso_Q_map_tensorTotalMap_roof X hP hsr (kInjectiveModel X L)
  rw [← cancel_epi (((derivedSheafHomBifunctor X).obj
      (op (DerivedCategory.Q.obj (kInjectiveModel X M)))).map
      (DerivedCategory.Q.map (tensorTotalMap X sr (𝟙 (kInjectiveModel X L))))),
    ← Category.assoc, ← Functor.map_comp, hσ,
    derivedSheafHomResolutionComparison_naturality_tensorTotalMap X L M gr,
    ← Category.assoc,
    derivedSheafHomResolutionComparison_naturality_tensorTotalMap X L M sr,
    Category.assoc, hτ]

include hP hsr hfac in
/-- The source comparison intertwines the map induced on the tensor factor with the morphism of
classes of total tensor products that the roof determines. -/
private lemma derivedTensorHomSourceIso_naturality_left
    {σ : DerivedCategory.Q.obj (derivedTensorHomSourceModel X K L M) ⟶
      DerivedCategory.Q.obj (derivedTensorHomSourceModel X K' L M)}
    (hσ : DerivedCategory.Q.map (tensorTotalMap X sr
          (𝟙 (sheafHomComplex X (kInjectiveModel X M) (kInjectiveModel X L)).obj)) ≫ σ =
      DerivedCategory.Q.map (tensorTotalMap X gr
        (𝟙 (sheafHomComplex X (kInjectiveModel X M) (kInjectiveModel X L)).obj))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map w).app
          (((derivedSheafHomBifunctor X).obj (op M)).obj L) ≫
        (derivedTensorHomSourceIso X K' L M).hom =
      (derivedTensorHomSourceIso X K L M).hom ≫ σ := by
  have sq1 := (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map w).naturality
    (derivedSheafHomObjectsKInjectiveModelIso X L M).hom).symm
  have sq2 := map_kFlatModelIso_inv_comp X (w := w)
    (DerivedCategory.Q.obj
      (sheafHomComplex X (kInjectiveModel X M) (kInjectiveModel X L)).obj)
  unfold derivedTensorHomSourceIso
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.mapIso_inv, Iso.symm_hom]
  exact square_comp sq1 (square_comp sq2 (roofComparison X hP hsr hfac _ hσ))

include hP hsr hfac in
/-- The comparison of `K ⊗^L_O L` with the total tensor product of the chosen representatives
intertwines the map induced on the tensor factor with the morphism of classes of total tensor
products that the roof determines. -/
private lemma derivedTensorObjectsKFlatLeftModelIso_naturality_left
    {σ : DerivedCategory.Q.obj (derivedTensorHomTensorModel X K L) ⟶
      DerivedCategory.Q.obj (derivedTensorHomTensorModel X K' L)}
    (hσ : DerivedCategory.Q.map (tensorTotalMap X sr (𝟙 (kInjectiveModel X L))) ≫ σ =
      DerivedCategory.Q.map (tensorTotalMap X gr (𝟙 (kInjectiveModel X L)))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map w).app L ≫
        (derivedTensorObjectsKFlatLeftModelIso X K' L).hom =
      (derivedTensorObjectsKFlatLeftModelIso X K L).hom ≫ σ := by
  have sq2 := map_kFlatModelIso_inv_comp X (w := w) L
  have sq3 := (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
    ((kFlatModelIso X K).hom ≫ w ≫ (kFlatModelIso X K').inv)).naturality
      (kInjectiveModelIso X L).inv).symm
  unfold derivedTensorObjectsKFlatLeftModelIso
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.mapIso_inv, Iso.symm_hom]
  exact square_comp sq2 (square_comp sq3 (roofComparison X hP hsr hfac _ hσ))

include hP hsr hfac in
/-- The target comparison intertwines the map induced on the tensor factor with the morphism of
internal Hom complexes induced by the resolution of the roof. -/
private lemma derivedTensorHomTargetIso_naturality_left
    {σ : DerivedCategory.Q.obj (derivedTensorHomTensorModel X K L) ⟶
      DerivedCategory.Q.obj (derivedTensorHomTensorModel X K' L)}
    (hσ : DerivedCategory.Q.map (tensorTotalMap X sr (𝟙 (kInjectiveModel X L))) ≫ σ =
      DerivedCategory.Q.map (tensorTotalMap X gr (𝟙 (kInjectiveModel X L))))
    {τ : DerivedCategory.Q.obj (derivedTensorHomTargetModel X K L M) ⟶
      DerivedCategory.Q.obj (derivedTensorHomTargetModel X K' L M)}
    (hτ : DerivedCategory.Q.map (homMap X (𝟙 (kInjectiveModel X M))
          ((kInjectiveResolution X).map
            (tensorTotalMap X sr (𝟙 (kInjectiveModel X L))))) ≫ τ =
      DerivedCategory.Q.map (homMap X (𝟙 (kInjectiveModel X M))
        ((kInjectiveResolution X).map
          (tensorTotalMap X gr (𝟙 (kInjectiveModel X L)))))) :
    ((derivedSheafHomBifunctor X).obj (op M)).map
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map w).app L) ≫
        (derivedTensorHomTargetIso X K' L M).hom =
      (derivedTensorHomTargetIso X K L M).hom ≫ τ := by
  have sq1 := map_square ((derivedSheafHomBifunctor X).obj (op M))
    (derivedTensorObjectsKFlatLeftModelIso_naturality_left X L hP hsr hfac hσ)
  have sq2 := ((derivedSheafHomBifunctor X).map
    (kInjectiveModelIso X M).hom.op).naturality σ
  unfold derivedTensorHomTargetIso
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.op_hom]
  exact square_comp sq1 (square_comp sq2
    (roofResolutionComparison X L M hP hsr hσ hτ))

include hP hsr in
/-- The complex-level square for the roof, pushed into the derived category. -/
private lemma derivedTensorHomModelMap_naturality_left
    {σ : DerivedCategory.Q.obj (derivedTensorHomSourceModel X K L M) ⟶
      DerivedCategory.Q.obj (derivedTensorHomSourceModel X K' L M)}
    (hσ : DerivedCategory.Q.map (tensorTotalMap X sr
          (𝟙 (sheafHomComplex X (kInjectiveModel X M) (kInjectiveModel X L)).obj)) ≫ σ =
      DerivedCategory.Q.map (tensorTotalMap X gr
        (𝟙 (sheafHomComplex X (kInjectiveModel X M) (kInjectiveModel X L)).obj)))
    {τ : DerivedCategory.Q.obj (derivedTensorHomTargetModel X K L M) ⟶
      DerivedCategory.Q.obj (derivedTensorHomTargetModel X K' L M)}
    (hτ : DerivedCategory.Q.map (homMap X (𝟙 (kInjectiveModel X M))
          ((kInjectiveResolution X).map
            (tensorTotalMap X sr (𝟙 (kInjectiveModel X L))))) ≫ τ =
      DerivedCategory.Q.map (homMap X (𝟙 (kInjectiveModel X M))
        ((kInjectiveResolution X).map
          (tensorTotalMap X gr (𝟙 (kInjectiveModel X L)))))) :
    DerivedCategory.Q.map (derivedTensorHomModelMap X K L M) ≫ τ =
      σ ≫ DerivedCategory.Q.map (derivedTensorHomModelMap X K' L M) := by
  have := isIso_Q_map_tensorTotalMap_roof X hP hsr
    (sheafHomComplex X (kInjectiveModel X M) (kInjectiveModel X L)).obj
  have hcS := congrArg DerivedCategory.Q.map
    (derivedTensorHomComplexMap_naturality_left X L M sr)
  have hcG := congrArg DerivedCategory.Q.map
    (derivedTensorHomComplexMap_naturality_left X L M gr)
  simp only [Functor.map_comp] at hcS hcG
  rw [derivedTensorHomModelMap_eq_complexMap X K L M,
    derivedTensorHomModelMap_eq_complexMap X K' L M,
    ← cancel_epi (DerivedCategory.Q.map (tensorTotalMap X sr
      (𝟙 (sheafHomComplex X (kInjectiveModel X M) (kInjectiveModel X L)).obj))),
    ← Category.assoc, ← hcS, Category.assoc, hτ, ← Category.assoc, hσ, ← hcG]

end Roof

/-- **Stacks 0BYS.** The diagonal morphism is covariant in the tensor factor, for an arbitrary
morphism of `D(O)`.

A morphism of `D(O)` does not lift to the chosen K-flat representatives, which are not
K-injective. It is instead written as a right fraction `inv (Q s₀) ≫ Q g₀`
(`DerivedCategory.right_fac`) and the apex of that roof is replaced by a K-flat resolution of
it (Stacks 06YS), giving a roof `A ⟵ P ⟶ A'` with all three complexes K-flat and the left leg
invertible in `D(O)`. The one-sided K-flat comparison of Stacks 06YU is then available at all
three vertices, which makes the tensored left leg invertible with no K-flatness of the other
factor, and the square closes from the complex-level functoriality of Stacks 0BYR. -/
@[stacks 0BYS "functoriality in the tensor factor"]
theorem derivedTensorHomDiagonal_natural_left (f : K ⟶ K') :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map f).app
          (((derivedSheafHomBifunctor X).obj (op M)).obj L) ≫
        derivedTensorHomDiagonal X K' L M =
      derivedTensorHomDiagonal X K L M ≫
        ((derivedSheafHomBifunctor X).obj (op M)).map
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
  have := isIso_Q_map_tensorTotalMap_roof X hP hsr
    (sheafHomComplex X (kInjectiveModel X M) (kInjectiveModel X L)).obj
  have := isIso_Q_map_tensorTotalMap_roof X hP hsr (kInjectiveModel X L)
  have := isIso_Q_map_homMap_roof X L M hP hsr
  obtain ⟨σ, hσ⟩ : ∃ σ, DerivedCategory.Q.map (tensorTotalMap X (p ≫ s₀)
        (𝟙 (sheafHomComplex X (kInjectiveModel X M) (kInjectiveModel X L)).obj)) ≫ σ =
      DerivedCategory.Q.map (tensorTotalMap X (p ≫ g₀)
        (𝟙 (sheafHomComplex X (kInjectiveModel X M) (kInjectiveModel X L)).obj)) :=
    ⟨_, IsIso.hom_inv_id_assoc _ _⟩
  obtain ⟨σI, hσI⟩ : ∃ σI, DerivedCategory.Q.map (tensorTotalMap X (p ≫ s₀)
        (𝟙 (kInjectiveModel X L))) ≫ σI =
      DerivedCategory.Q.map (tensorTotalMap X (p ≫ g₀) (𝟙 (kInjectiveModel X L))) :=
    ⟨_, IsIso.hom_inv_id_assoc _ _⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, DerivedCategory.Q.map (homMap X (𝟙 (kInjectiveModel X M))
        ((kInjectiveResolution X).map
          (tensorTotalMap X (p ≫ s₀) (𝟙 (kInjectiveModel X L))))) ≫ τ =
      DerivedCategory.Q.map (homMap X (𝟙 (kInjectiveModel X M))
        ((kInjectiveResolution X).map
          (tensorTotalMap X (p ≫ g₀) (𝟙 (kInjectiveModel X L))))) :=
    ⟨_, IsIso.hom_inv_id_assoc _ _⟩
  unfold derivedTensorHomDiagonal
  exact conjugated_square (derivedTensorHomSourceIso X K L M)
    (derivedTensorHomSourceIso X K' L M) (derivedTensorHomTargetIso X K L M)
    (derivedTensorHomTargetIso X K' L M)
    (derivedTensorHomSourceIso_naturality_left X L M hP hsr hfac hσ)
    (derivedTensorHomTargetIso_naturality_left X L M hP hsr hfac hσI hτ)
    (derivedTensorHomModelMap_naturality_left X L M hP hsr hσ hτ)

end TensorVariable

end Naturality

end AlgebraicGeometry.RingedSite

namespace Stacks.SheafOfModules

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ A, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- Diagonal morphisms `K ⊗^L_{O_X} RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^L_{O_X} L)` on a ringed
space, specified by their value on the chosen representatives: the class of the complex-level
morphism of Stacks 0BYR followed by the map induced by the chosen K-injective resolution of
the total tensor product, conjugated by the K-flat and K-injective comparisons. They are
covariant in the tensor factor and in the target of the internal Hom, and contravariant in its
source. -/
structure DerivedTensorHomDiagonal where
  /-- The diagonal morphism attached to three objects of `D(O_X)`. -/
  map (K L M : DerivedCategory (StructureSheafModules Rc)) :
    ((derivedTensorProductFunctor (ringedSite Rc)).obj K).obj
        (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op M)).obj L) ⟶
      ((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op M)).obj
        (((derivedTensorProductFunctor (ringedSite Rc)).obj K).obj L)
  /-- On the chosen representatives the morphism is the class of the complex-level morphism of
  Stacks 0BYR, read through the two comparisons. -/
  map_eq (K L M : DerivedCategory (StructureSheafModules Rc)) :
    (RingedSite.derivedTensorHomSourceIso (ringedSite Rc) K L M).inv ≫ map K L M ≫
        (RingedSite.derivedTensorHomTargetIso (ringedSite Rc) K L M).hom =
      DerivedCategory.Q.map
        (RingedSite.derivedTensorHomModelMap (ringedSite Rc) K L M)
  /-- The morphism is contravariant in the source of the internal Hom. -/
  map_natural_hom (K L : DerivedCategory (StructureSheafModules Rc))
      {M M' : DerivedCategory (StructureSheafModules Rc)} (g : M' ⟶ M) :
    ((derivedTensorProductFunctor (ringedSite Rc)).obj K).map
          (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).map g.op).app L) ≫
        map K L M' =
      map K L M ≫
        ((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).map g.op).app
          (((derivedTensorProductFunctor (ringedSite Rc)).obj K).obj L)
  /-- The morphism is covariant in the tensor factor. -/
  map_natural_left {K K' : DerivedCategory (StructureSheafModules Rc)}
      (L M : DerivedCategory (StructureSheafModules Rc)) (f : K ⟶ K') :
    ((derivedTensorProductFunctor (ringedSite Rc)).map f).app
          (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op M)).obj L) ≫
        map K' L M =
      map K L M ≫
        ((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op M)).map
          (((derivedTensorProductFunctor (ringedSite Rc)).map f).app L)
  /-- The morphism is covariant in the target of the internal Hom. -/
  map_natural_right (K : DerivedCategory (StructureSheafModules Rc))
      {L L' : DerivedCategory (StructureSheafModules Rc)}
      (M : DerivedCategory (StructureSheafModules Rc)) (g : L ⟶ L') :
    ((derivedTensorProductFunctor (ringedSite Rc)).obj K).map
          (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op M)).map g) ≫
        map K L' M =
      map K L M ≫
        ((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op M)).map
          (((derivedTensorProductFunctor (ringedSite Rc)).obj K).map g)

namespace DerivedTensorHomDiagonal

variable {Rc}

/-- The characterisation on the chosen representatives determines the diagonal morphism: any
two such data agree. -/
theorem map_unique (D D' : DerivedTensorHomDiagonal Rc)
    (K L M : DerivedCategory (StructureSheafModules Rc)) :
    D.map K L M = D'.map K L M :=
  (RingedSite.eq_derivedTensorHomDiagonal (ringedSite Rc) K L M (D.map_eq K L M)).trans
    (RingedSite.eq_derivedTensorHomDiagonal (ringedSite Rc) K L M (D'.map_eq K L M)).symm

end DerivedTensorHomDiagonal

/-- **Stacks 0BYS exists.** For objects `K`, `L`, `M` of `D(O_X)` on a ringed space there is a
canonical morphism `K ⊗^L_{O_X} RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^L_{O_X} L)`, namely the
class of the complex-level morphism of Stacks 0BYR between the chosen representatives, and it
is functorial in all three objects. -/
theorem exists_derivedTensorHomDiagonal : Nonempty (DerivedTensorHomDiagonal Rc) :=
  by
  refine ⟨{ map K L M := RingedSite.derivedTensorHomDiagonal (ringedSite Rc) K L M
            map_eq K L M := RingedSite.derivedTensorHomDiagonal_eq (ringedSite Rc) K L M
            map_natural_hom := ?_
            map_natural_left := ?_
            map_natural_right := ?_ }⟩
  · intro K L M M' g
    exact RingedSite.derivedTensorHomDiagonal_natural_hom (ringedSite Rc) K L g
  · intro K K' L M f
    exact RingedSite.derivedTensorHomDiagonal_natural_left (ringedSite Rc) L M f
  · intro K L L' M g
    exact RingedSite.derivedTensorHomDiagonal_natural_right (ringedSite Rc) K M g

/-- **Stacks 0BYS.** The canonical morphism

`K ⊗^L_{O_X} RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^L_{O_X} L)`

in `D(O_X)` for objects `K`, `L`, `M` of the derived category of a ringed space. -/
@[stacks 0BYS "the canonical morphism"]
def canonicalDerivedTensorHomDiagonal : DerivedTensorHomDiagonal Rc :=
  Classical.choice (exists_derivedTensorHomDiagonal Rc)

/-- The canonical diagonal morphism attached to three objects of `D(O_X)`. -/
abbrev derivedTensorHomDiagonal (K L M : DerivedCategory (StructureSheafModules Rc)) :
    ((derivedTensorProductFunctor (ringedSite Rc)).obj K).obj
        (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op M)).obj L) ⟶
      ((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op M)).obj
        (((derivedTensorProductFunctor (ringedSite Rc)).obj K).obj L) :=
  (canonicalDerivedTensorHomDiagonal Rc).map K L M

/-- **Stacks 0BYS.** The canonical morphism is the class of the complex-level morphism of
Stacks 0BYR between the chosen representatives, read through the K-flat and K-injective
comparisons. -/
@[stacks 0BYS "the characterisation on representatives"]
theorem derivedTensorHomDiagonal_eq (K L M : DerivedCategory (StructureSheafModules Rc)) :
    (RingedSite.derivedTensorHomSourceIso (ringedSite Rc) K L M).inv ≫
        derivedTensorHomDiagonal Rc K L M ≫
        (RingedSite.derivedTensorHomTargetIso (ringedSite Rc) K L M).hom =
      DerivedCategory.Q.map
        (RingedSite.derivedTensorHomModelMap (ringedSite Rc) K L M) :=
  (canonicalDerivedTensorHomDiagonal Rc).map_eq K L M

/-- **Stacks 0BYS.** The canonical morphism is contravariant in the source `M` of the internal
Hom, for an arbitrary morphism of `D(O_X)`. -/
@[stacks 0BYS "functoriality in the source of the internal Hom"]
theorem derivedTensorHomDiagonal_natural_hom
    (K L : DerivedCategory (StructureSheafModules Rc))
    {M M' : DerivedCategory (StructureSheafModules Rc)} (g : M' ⟶ M) :
    ((derivedTensorProductFunctor (ringedSite Rc)).obj K).map
          (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).map g.op).app L) ≫
        derivedTensorHomDiagonal Rc K L M' =
      derivedTensorHomDiagonal Rc K L M ≫
        ((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).map g.op).app
          (((derivedTensorProductFunctor (ringedSite Rc)).obj K).obj L) :=
  (canonicalDerivedTensorHomDiagonal Rc).map_natural_hom K L g

/-- **Stacks 0BYS.** The canonical morphism is covariant in the tensor factor `K`, for an
arbitrary morphism of `D(O_X)`. -/
@[stacks 0BYS "functoriality in the tensor factor"]
theorem derivedTensorHomDiagonal_natural_left
    {K K' : DerivedCategory (StructureSheafModules Rc)}
    (L M : DerivedCategory (StructureSheafModules Rc)) (f : K ⟶ K') :
    ((derivedTensorProductFunctor (ringedSite Rc)).map f).app
          (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op M)).obj L) ≫
        derivedTensorHomDiagonal Rc K' L M =
      derivedTensorHomDiagonal Rc K L M ≫
        ((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op M)).map
          (((derivedTensorProductFunctor (ringedSite Rc)).map f).app L) :=
  (canonicalDerivedTensorHomDiagonal Rc).map_natural_left L M f

/-- **Stacks 0BYS.** The canonical morphism is covariant in the target `L` of the internal Hom,
for an arbitrary morphism of `D(O_X)`. -/
@[stacks 0BYS "functoriality in the target of the internal Hom"]
theorem derivedTensorHomDiagonal_natural_right
    (K : DerivedCategory (StructureSheafModules Rc))
    {L L' : DerivedCategory (StructureSheafModules Rc)}
    (M : DerivedCategory (StructureSheafModules Rc)) (g : L ⟶ L') :
    ((derivedTensorProductFunctor (ringedSite Rc)).obj K).map
          (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op M)).map g) ≫
        derivedTensorHomDiagonal Rc K L' M =
      derivedTensorHomDiagonal Rc K L M ≫
        ((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op M)).map
          (((derivedTensorProductFunctor (ringedSite Rc)).obj K).map g) :=
  (canonicalDerivedTensorHomDiagonal Rc).map_natural_right K M g

end Stacks.SheafOfModules

end
