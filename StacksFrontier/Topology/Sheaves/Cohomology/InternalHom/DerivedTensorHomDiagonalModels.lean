module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TotalComplexNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomComparisonTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.QuasiIsoInvariance
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.QuasiIsomorphismLocality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomQuasiIso
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomDiagonal

/-!
# Arbitrary complex models for the diagonal of Stacks 0BYS

Let `X` be a ringed site and let `K`, `L`, `M` be objects of `D(O)`. The diagonal morphism of
Stacks 0BYS

`K ⊗^L_O RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^L_O L)`

is constructed in
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomDiagonal` from one
particular choice of representatives — `kFlatModel K`, `kInjectiveModel L`, `kInjectiveModel M`,
and the chosen functorial K-injective resolution of the total tensor product — and its
characterisation `derivedTensorHomDiagonal_eq` is stated at that choice only. The source states
its construction for an *arbitrary* K-flat `A` representing `K`, an arbitrary K-injective `I`
representing `L`, an arbitrary `N` representing `M`, an arbitrary K-injective `J` and an
arbitrary quasi-isomorphism `q : Tot(A ⊗_O I) ⟶ J`.

This file sets up that arbitrary choice — the three comparison isomorphisms identifying the
source and target of the diagonal with classes of complexes built from `A`, `I`, `N` and `J`,
and the complex-level morphism of Stacks 0BYR between them — and **proves the characterisation
there**, in `derivedTensorHomDiagonal_eq_ofModels`. Each construction is a direct generalisation
of the corresponding chosen-representative one, and each is *pinned* to it: specialising the
data to the chosen representatives returns the chosen construction definitionally, which is what
`derivedTensorObjectsIsoOfModels_chosen`, `derivedTensorHomSourceIsoOfModels_chosen` and
`derivedTensorHomMapOfModels_chosen` record.

The constructions need no new input, because the pieces they are assembled from are already
stated at arbitrary complexes: `derivedSheafHomObjectsModelIso` takes the two representing
isomorphisms as arguments, `derivedSheafHomComparison` takes an arbitrary source and any
K-injective target, `DerivedTensorProduct.comparisonLeft` takes any K-flat left factor, and
`tensorTotalIsoTensorComplex` is natural in both complexes.

The 0BYS module's own account of this generalisation says it is a duplication of the roof
argument it already carries out. That is right for the K-flat variable and wrong for the rest:
three of the four variables need no roof at all, and the roof itself needs, beyond the 0BYS
argument, that the characterisation is insensitive to replacing `q` by another morphism with the
same class — which comes from
`AlgebraicGeometry.RingedSite.Q_map_homMap_congr_of_isKInjective` and not from anything in that
module.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedTensorObjectsIsoOfModels`: `K ⊗^L_O L` is the class of
  `Tot(A ⊗_O I)`, for any K-flat `A` representing `K` and any `I` representing `L`.
* `AlgebraicGeometry.RingedSite.derivedTensorHomSourceIsoOfModels`: the source
  `K ⊗^L_O RSheafHom(M, L)` of the diagonal is the class of `Tot(A ⊗_O SheafHom(N, I))`, for
  K-injective `I`.
* `AlgebraicGeometry.RingedSite.derivedTensorHomTargetIsoOfModels`: the target
  `RSheafHom(M, K ⊗^L_O L)` is the class of `SheafHom(N, J)`, for K-injective `J` and a
  quasi-isomorphism `q : Tot(A ⊗_O I) ⟶ J`.
* `AlgebraicGeometry.RingedSite.derivedTensorHomMapOfModels`: the complex-level morphism of
  Stacks 0BYR between those two complexes, followed by the map induced by `q`.

## Main results

* `AlgebraicGeometry.RingedSite.derivedTensorObjectsIsoOfModels_chosen`,
  `AlgebraicGeometry.RingedSite.derivedTensorHomSourceIsoOfModels_chosen` and
  `AlgebraicGeometry.RingedSite.derivedTensorHomMapOfModels_chosen`: at the chosen
  representatives these are the chosen constructions, definitionally. This is what makes the
  definitions above generalisations rather than independent constructions of objects of the same
  type.
* `AlgebraicGeometry.RingedSite.derivedTensorHomDiagonal_eq_ofModels_kInjectiveTarget`: **the
  characterisation of the diagonal at an arbitrary K-injective target.** With `A`, `I` and `N`
  the chosen representatives but `J` and `q : Tot(A ⊗_O I) ⟶ J` arbitrary, the diagonal is the
  class of the complex-level morphism built from `q`, conjugated by the comparisons above. This
  generalises `derivedTensorHomDiagonal_eq` in the `J`/`q` variable.
* `AlgebraicGeometry.RingedSite.derivedTensorHomTargetIso_inv_comp_targetIsoOfModels`: the two
  target comparisons differ only in their last leg, which is what reduces the previous statement
  to a fact about internal Hom complexes.
* `AlgebraicGeometry.RingedSite.derivedTensorHomDiagonal_eq_ofModels_kInjective`: **the
  characterisation at an arbitrary K-injective representative of `L` as well.** This generalises
  the previous one in the `I` variable.
* `AlgebraicGeometry.RingedSite.derivedTensorHomDiagonal_eq_ofModels_kFlatModel`: **the
  characterisation at arbitrary `I`, `N`, `J` and `q`.** Only the K-flat representative of `K`
  is still the chosen one. This generalises the previous one in the `N` variable.
* `AlgebraicGeometry.RingedSite.derivedTensorObjectsIsoOfModels_naturality_right`,
  `AlgebraicGeometry.RingedSite.derivedTensorHomSourceIsoOfModels_naturality_right`,
  `AlgebraicGeometry.RingedSite.derivedTensorHomTargetIsoOfModels_comp_tensorTotalMap` and
  `AlgebraicGeometry.RingedSite.derivedTensorHomMapOfModels_comp`: the compatibilities of the
  constructions above with a change of the representative of `L`.
* `AlgebraicGeometry.RingedSite.derivedTensorHomSourceIsoOfModels_naturality_source`,
  `AlgebraicGeometry.RingedSite.derivedTensorHomTargetIsoOfModels_naturality_source` and
  `AlgebraicGeometry.RingedSite.derivedTensorHomMapOfModels_naturality_source`: the same for a
  change of the representative of `M`, contravariantly.
* `AlgebraicGeometry.RingedSite.derivedTensorHomDiagonal_eq_ofModels`: **the characterisation at
  an arbitrary choice of all five models**, which is the form in which the source states the
  construction of the diagonal. This is the goal of the file.
* `AlgebraicGeometry.RingedSite.isIso_derivedTensorHomDiagonal_iff_quasiIso_ofModels`: hence the
  diagonal is invertible exactly when the complex-level morphism of Stacks 0BYR at *any one*
  choice of models is a quasi-isomorphism, so a proof may pick models adapted to its hypothesis.
* `AlgebraicGeometry.RingedSite.isIso_derivedTensorHomDiagonal_of_coversTop`: and it is enough
  for that morphism to be a quasi-isomorphism *locally* on the site. This is the "we may work
  locally" step, and it needs no compatibility of the diagonal itself with restriction.
* `AlgebraicGeometry.RingedSite.isIso_derivedTensorHomDiagonal_iff_quasiIso_tensorHomInterchange`:
  when `Tot(A ⊗_O I)` is K-injective the map induced by `q` cancels, so the diagonal is
  invertible exactly when the interchange morphism of Stacks 0BYR is a quasi-isomorphism.
* `isIso_derivedTensorHomDiagonal_iff_quasiIso_tensorHomInterchange_of_isFiniteFreeSummand`, in
  the same namespace: the same reduction under the hypothesis that the representative of `M` is
  strictly perfect instead, where the cancellation is Stacks 08JH's input and no K-injectivity
  of `Tot(A ⊗_O I)` is needed.
* `AlgebraicGeometry.RingedSite.derivedTensorHomDiagonal_eq_ofModels_iff_of_kFlatMap`: the
  transport of the characterisation along a morphism of K-flat representatives of `K`, stated as
  an equivalence so that both legs of a roof can be traversed.
* `AlgebraicGeometry.RingedSite.derivedTensorHomDiagonal_eq_ofModels_congr_q`: the
  characterisation depends on `q` only through its class in `D(O)`.
* `AlgebraicGeometry.RingedSite.derivedTensorObjectsIsoOfModels_naturality_left`,
  `AlgebraicGeometry.RingedSite.derivedTensorHomSourceIsoOfModels_naturality_left`,
  `AlgebraicGeometry.RingedSite.derivedTensorHomTargetIsoOfModels_comp_tensorTotalMap_left` and
  `AlgebraicGeometry.RingedSite.derivedTensorHomMapOfModels_comp_left`: the compatibilities for
  a change of the K-flat representative of `K`.

## Implementation notes

The generalisation is carried out one variable at a time, each step reducing to the previous
one: `J`/`q` first, then `I`, then `N`, then the K-flat `A`. The first three all go the same
way — the chosen model is compared with the arbitrary one by a *morphism of complexes*, which
exists because the relevant chosen model is K-injective, and the comparison is transported by
naturality. None of them needs any homotopy-theoretic input.

The K-flat variable is different: K-flat complexes have no universal property against
quasi-isomorphisms, so there is no morphism of complexes between an arbitrary K-flat `A` and
`kFlatModel K` in either direction. They are compared through a roof `A ⟵ P ⟶ kFlatModel K`
with `P` itself K-flat, and the transport is therefore stated as an equivalence, so that the two
legs can be traversed in opposite directions. The two legs also do not carry the same morphism
into `J`, only morphisms with the same class in `D(O)`, which is why the characterisation is
first shown to depend on `q` through its class alone.

## What this file does not contain

Nothing about Stacks 0ATN itself, and neither of its two bridges: that the diagonal commutes
with restriction to an open subspace, and that on `Spec A` it corresponds, under the comparisons
of Stacks 0A6H and Stacks 08DX, to the diagonal of Stacks 0BYN over `A`. Those are what
`derivedTensorHomDiagonal_eq_ofModels` is the prerequisite for — each compares the models on two
different spaces, which the chosen-representative characterisation of the 0BYS module could not
express.

For the *local* half of that programme, `isIso_derivedTensorHomDiagonal_of_coversTop` is a
substitute that avoids the first bridge entirely: invertibility of the diagonal is reduced to
quasi-isomorphy of one morphism of complexes, and that is local by
`Stacks.SheafOfModules.quasiIso_of_coversTop`. What it does *not* supply is the identification
of the restriction of the complex-level morphism of Stacks 0BYR with the corresponding morphism
on the slice — that is, the compatibility of `tensorHomInterchange` with restriction, which is
not in the library and is what a local argument choosing better models on each member of the
covering would need.

## References

* [Stacks Project, Lemma 20.49.11 (Tag 0BYS)](https://stacks.math.columbia.edu/tag/0BYS)
* [Stacks Project, Lemma 20.49.10 (Tag 0BYR)](https://stacks.math.columbia.edu/tag/0BYR)
* [Stacks Project, Lemma 36.10.11 (Tag 0ATN)](https://stacks.math.columbia.edu/tag/0ATN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

variable {K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
  {A I N J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- **`K ⊗^L_O L` is the class of `Tot(A ⊗_O I)`** for any K-flat complex `A` representing `K`
and any complex `I` representing `L`: the one-sided K-flat comparison of Stacks 06YU, read
through the bridge between the two total tensor-product complexes. -/
def derivedTensorObjectsIsoOfModels (hA : Stacks.SheafOfModules.IsKFlat X.O A)
    (eA : DerivedCategory.Q.obj A ≅ K) (eI : DerivedCategory.Q.obj I ≅ L) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L ≅
      DerivedCategory.Q.obj (tensorTotal X A I) :=
  ((Stacks.SheafOfModules.derivedTensorProductFunctor X).mapIso eA.symm).app L ≪≫
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
        (DerivedCategory.Q.obj A)).mapIso eI.symm ≪≫
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft A I hA ≪≫
        (DerivedCategory.Q.mapIso (tensorTotalIsoTensorComplex X A I)).symm

/-- **The source of the diagonal is the class of `Tot(A ⊗_O SheafHom(N, I))`** for any K-flat
`A` representing `K`, any K-injective `I` representing `L` and any `N` representing `M`: the
internal Hom complex into a K-injective target computes the derived internal Hom, and the
K-flat comparison then computes the derived tensor product. -/
def derivedTensorHomSourceIsoOfModels [I.IsKInjective]
    (hA : Stacks.SheafOfModules.IsKFlat X.O A)
    (eA : DerivedCategory.Q.obj A ≅ K) (eI : DerivedCategory.Q.obj I ≅ L)
    (eN : DerivedCategory.Q.obj N ≅ M) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj
        (((derivedSheafHomBifunctor X).obj (op M)).obj L) ≅
      DerivedCategory.Q.obj (tensorTotal X A (sheafHomComplex X N I).obj) :=
  ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).mapIso
      (derivedSheafHomObjectsModelIso X eN eI ≪≫ derivedSheafHomComparison X N I) ≪≫
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).mapIso eA.symm).app
        (DerivedCategory.Q.obj (sheafHomComplex X N I).obj) ≪≫
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft A
          (sheafHomComplex X N I).obj hA ≪≫
        (DerivedCategory.Q.mapIso
          (tensorTotalIsoTensorComplex X A (sheafHomComplex X N I).obj)).symm

/-- **The target of the diagonal is the class of `SheafHom(N, J)`** for any K-injective `J`
receiving a quasi-isomorphism `q : Tot(A ⊗_O I) ⟶ J`: the tensor product is first identified
with the class of `Tot(A ⊗_O I)`, then transported along `q`, and the internal Hom complex into
the K-injective `J` computes the derived internal Hom. -/
def derivedTensorHomTargetIsoOfModels [J.IsKInjective]
    (hA : Stacks.SheafOfModules.IsKFlat X.O A)
    (eA : DerivedCategory.Q.obj A ≅ K) (eI : DerivedCategory.Q.obj I ≅ L)
    (eN : DerivedCategory.Q.obj N ≅ M) (q : tensorTotal X A I ⟶ J)
    (hq : IsIso (DerivedCategory.Q.map q)) :
    ((derivedSheafHomBifunctor X).obj (op M)).obj
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L) ≅
      DerivedCategory.Q.obj (sheafHomComplex X N J).obj :=
  haveI := hq
  ((derivedSheafHomBifunctor X).obj (op M)).mapIso
      (derivedTensorObjectsIsoOfModels X hA eA eI) ≪≫
    ((derivedSheafHomBifunctor X).mapIso eN.op).app
        (DerivedCategory.Q.obj (tensorTotal X A I)) ≪≫
      ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj N))).mapIso
          (asIso (DerivedCategory.Q.map q)) ≪≫
        derivedSheafHomComparison X N J

/-- **The complex-level morphism of Stacks 0BYR at an arbitrary choice of models**, followed by
the map induced by `q`: the interchange morphism
`Tot(A ⊗_O SheafHom(N, I)) ⟶ SheafHom(N, Tot(A ⊗_O I))` composed with `SheafHom(N, q)`. -/
def derivedTensorHomMapOfModels (q : tensorTotal X A I ⟶ J) :
    tensorTotal X A (sheafHomComplex X N I).obj ⟶ (sheafHomComplex X N J).obj :=
  tensorHomInterchange X A I N ≫ homMap X (𝟙 N) q

/-- At the chosen K-flat and K-injective representatives, the comparison of `K ⊗^L_O L` with a
class of complexes is the chosen one. -/
theorem derivedTensorObjectsIsoOfModels_chosen
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedTensorObjectsIsoOfModels X (isKFlat_kFlatModel X K) (kFlatModelIso X K)
        (kInjectiveModelIso X L) =
      derivedTensorObjectsKFlatLeftModelIso X K L :=
  rfl

/-- At the chosen representatives, the comparison of the source of the diagonal with a class of
complexes is the chosen one. -/
theorem derivedTensorHomSourceIsoOfModels_chosen
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedTensorHomSourceIsoOfModels X (I := kInjectiveModel X L) (N := kInjectiveModel X M)
        (isKFlat_kFlatModel X K) (kFlatModelIso X K) (kInjectiveModelIso X L)
        (kInjectiveModelIso X M) =
      derivedTensorHomSourceIso X K L M :=
  rfl

/-- At the chosen representatives and the chosen K-injective resolution, the complex-level
morphism is the chosen one. -/
theorem derivedTensorHomMapOfModels_chosen
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedTensorHomMapOfModels X (N := kInjectiveModel X M)
        ((kInjectiveAugmentation X).app (derivedTensorHomTensorModel X K L)) =
      derivedTensorHomModelMap X K L M :=
  rfl

/-- The chosen target comparison and the one attached to an arbitrary K-injective `J` with a
quasi-isomorphism `q : Tot(A ⊗ I) ⟶ J` differ only in their last leg: the two agree on the
identification of `RSheafHom(M, K ⊗^L_O L)` with `RSheafHom(Q N, Q Tot(A ⊗ I))`, after which one
takes the chosen resolution of `Tot(A ⊗ I)` and the other crosses `q` into `J`. -/
theorem derivedTensorHomTargetIso_inv_comp_targetIsoOfModels
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [J.IsKInjective]
    (q : tensorTotal X (kFlatModel X K) (kInjectiveModel X L) ⟶ J)
    (hq : IsIso (DerivedCategory.Q.map q)) :
    (derivedTensorHomTargetIso X K L M).inv ≫
        (derivedTensorHomTargetIsoOfModels X (I := kInjectiveModel X L)
          (N := kInjectiveModel X M) (isKFlat_kFlatModel X K) (kFlatModelIso X K)
          (kInjectiveModelIso X L) (kInjectiveModelIso X M) q hq).hom =
      (derivedSheafHomResolutionComparison X (kInjectiveModel X M)
          (derivedTensorHomTensorModel X K L)).inv ≫
        ((derivedSheafHomBifunctor X).obj
            (op (DerivedCategory.Q.obj (kInjectiveModel X M)))).map
          (DerivedCategory.Q.map q) ≫
        (derivedSheafHomComparison X (kInjectiveModel X M) J).hom := by
  dsimp only [derivedTensorHomTargetIso, derivedTensorHomTargetIsoOfModels,
    derivedTensorHomTensorModel, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom]
  rw [derivedTensorObjectsIsoOfModels_chosen]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simp only [CategoryTheory.Functor.mapIso_hom, asIso_hom]

/-- **The characterisation of the diagonal of Stacks 0BYS at an arbitrary K-injective target.**
For the chosen K-flat and K-injective representatives of `K`, `L` and `M`, but an *arbitrary*
K-injective complex `J` and an *arbitrary* quasi-isomorphism `q : Tot(A ⊗ I) ⟶ J`, the diagonal
is the class of the complex-level morphism of Stacks 0BYR built from `q`, conjugated by the
corresponding comparisons. The chosen K-injective resolution of the total tensor product is one
instance of such a `J` and `q`, and this generalises `derivedTensorHomDiagonal_eq` in that
variable. -/
theorem derivedTensorHomDiagonal_eq_ofModels_kInjectiveTarget
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [J.IsKInjective]
    (q : tensorTotal X (kFlatModel X K) (kInjectiveModel X L) ⟶ J)
    (hq : IsIso (DerivedCategory.Q.map q)) :
    (derivedTensorHomSourceIsoOfModels X (I := kInjectiveModel X L)
          (N := kInjectiveModel X M) (isKFlat_kFlatModel X K) (kFlatModelIso X K)
          (kInjectiveModelIso X L) (kInjectiveModelIso X M)).inv ≫
        derivedTensorHomDiagonal X K L M ≫
        (derivedTensorHomTargetIsoOfModels X (I := kInjectiveModel X L)
          (N := kInjectiveModel X M) (isKFlat_kFlatModel X K) (kFlatModelIso X K)
          (kInjectiveModelIso X L) (kInjectiveModelIso X M) q hq).hom =
      DerivedCategory.Q.map
        (derivedTensorHomMapOfModels X (N := kInjectiveModel X M) q) := by
  rw [derivedTensorHomSourceIsoOfModels_chosen]
  have h := derivedTensorHomDiagonal_eq X K L M
  have h2 : (derivedTensorHomSourceIso X K L M).inv ≫ derivedTensorHomDiagonal X K L M =
      DerivedCategory.Q.map (derivedTensorHomModelMap X K L M) ≫
        (derivedTensorHomTargetIso X K L M).inv := by
    rw [← h]; simp
  rw [← Category.assoc, h2, Category.assoc,
    derivedTensorHomTargetIso_inv_comp_targetIsoOfModels X K L M q hq]
  dsimp only [derivedTensorHomModelMap, derivedTensorHomMapOfModels]
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc,
    Q_map_homMap_augmentation_comp_comparison]

/-! ### Changing the K-injective representative of `L` -/

/-- The tensor comparison at arbitrary models is natural in the representative of `L`. -/
theorem derivedTensorObjectsIsoOfModels_naturality_right
    (hA : Stacks.SheafOfModules.IsKFlat X.O A)
    (eA : DerivedCategory.Q.obj A ≅ K) (eI : DerivedCategory.Q.obj I ≅ L)
    {I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eI' : DerivedCategory.Q.obj I' ≅ L) (i : I ⟶ I')
    (hi : DerivedCategory.Q.map i = eI.hom ≫ eI'.inv) :
    (derivedTensorObjectsIsoOfModels X hA eA eI).hom ≫
        DerivedCategory.Q.map (tensorTotalMap X (𝟙 A) i) =
      (derivedTensorObjectsIsoOfModels X hA eA eI').hom := by
  dsimp only [derivedTensorObjectsIsoOfModels, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.mapIso_inv, Iso.app_hom]
  simp only [Category.assoc]
  rw [← comparisonLeft_tensorTotal_naturality_right X A i hA,
    ← CategoryTheory.Functor.map_comp_assoc, hi, Iso.inv_hom_id_assoc]

/-- The source comparison at arbitrary models is natural in the representative of `L`. -/
theorem derivedTensorHomSourceIsoOfModels_naturality_right [I.IsKInjective]
    (hA : Stacks.SheafOfModules.IsKFlat X.O A)
    (eA : DerivedCategory.Q.obj A ≅ K) (eI : DerivedCategory.Q.obj I ≅ L)
    {I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I'.IsKInjective]
    (eI' : DerivedCategory.Q.obj I' ≅ L) (eN : DerivedCategory.Q.obj N ≅ M)
    (i : I ⟶ I') (hi : DerivedCategory.Q.map i = eI.hom ≫ eI'.inv) :
    (derivedTensorHomSourceIsoOfModels X hA eA eI eN).hom ≫
        DerivedCategory.Q.map (tensorTotalMap X (𝟙 A) (homMap X (𝟙 N) i)) =
      (derivedTensorHomSourceIsoOfModels X hA eA eI' eN).hom := by
  dsimp only [derivedTensorHomSourceIsoOfModels, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.mapIso_inv, Iso.app_hom]
  simp only [Category.assoc]
  rw [← comparisonLeft_tensorTotal_naturality_right X A (homMap X (𝟙 N) i) hA,
    ← NatTrans.naturality_assoc, ← CategoryTheory.Functor.map_comp_assoc]
  simp only [Category.assoc]
  rw [derivedSheafHomObjectsModelIso_comparison_naturality_right X eI eI' eN i hi]

/-- The target comparison is unchanged by moving the representative of `L` along `i` and
precomposing `q` with the induced map of total tensor products. -/
theorem derivedTensorHomTargetIsoOfModels_comp_tensorTotalMap [J.IsKInjective]
    (hA : Stacks.SheafOfModules.IsKFlat X.O A)
    (eA : DerivedCategory.Q.obj A ≅ K) (eI : DerivedCategory.Q.obj I ≅ L)
    {I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eI' : DerivedCategory.Q.obj I' ≅ L) (eN : DerivedCategory.Q.obj N ≅ M)
    (i : I ⟶ I') (hi : DerivedCategory.Q.map i = eI.hom ≫ eI'.inv)
    (q : tensorTotal X A I' ⟶ J) (hq : IsIso (DerivedCategory.Q.map q))
    (hq0 : IsIso (DerivedCategory.Q.map (tensorTotalMap X (𝟙 A) i ≫ q))) :
    derivedTensorHomTargetIsoOfModels X hA eA eI eN
          (tensorTotalMap X (𝟙 A) i ≫ q) hq0 =
      derivedTensorHomTargetIsoOfModels X hA eA eI' eN q hq := by
  apply Iso.ext
  dsimp only [derivedTensorHomTargetIsoOfModels, Iso.trans_hom,
    CategoryTheory.Functor.mapIso_hom, Iso.app_hom, asIso_hom]
  rw [CategoryTheory.Functor.map_comp DerivedCategory.Q,
    CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [← NatTrans.naturality_assoc, ← CategoryTheory.Functor.map_comp_assoc,
    derivedTensorObjectsIsoOfModels_naturality_right X hA eA eI eI' i hi]

omit [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ B, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj B).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- Precomposing `q` with the map induced by `i` precomposes the complex-level morphism of
Stacks 0BYR with the map induced by `SheafHom(N, i)`. -/
theorem derivedTensorHomMapOfModels_comp
    {I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (i : I ⟶ I') (q : tensorTotal X A I' ⟶ J) :
    derivedTensorHomMapOfModels X (N := N) (tensorTotalMap X (𝟙 A) i ≫ q) =
      tensorTotalMap X (𝟙 A) (homMap X (𝟙 N) i) ≫
        derivedTensorHomMapOfModels X (N := N) q := by
  dsimp only [derivedTensorHomMapOfModels]
  rw [← Category.assoc, ← tensorHomInterchange_natural X (𝟙 A) i (𝟙 N), Category.assoc,
    homMap_comp, Category.id_comp]

/-- **The characterisation of the diagonal of Stacks 0BYS at an arbitrary K-injective
representative of `L` and an arbitrary K-injective target.** The chosen K-flat representative of
`K` and the chosen representative of `M` are still used; `I`, `J` and `q` are arbitrary. This
generalises `derivedTensorHomDiagonal_eq_ofModels_kInjectiveTarget` in the `I` variable.

An arbitrary K-injective `I` representing `L` is compared with the chosen one by a morphism of
complexes `i`, which exists because `I` is K-injective; tensoring with the K-flat `A` keeps `i`
a quasi-isomorphism, so `q` may be pulled back along it to the chosen representative, where the
previous characterisation applies. -/
theorem derivedTensorHomDiagonal_eq_ofModels_kInjective
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective]
    (eI : DerivedCategory.Q.obj I ≅ L)
    {J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [J.IsKInjective]
    (q : tensorTotal X (kFlatModel X K) I ⟶ J)
    (hq : IsIso (DerivedCategory.Q.map q)) :
    (derivedTensorHomSourceIsoOfModels X (N := kInjectiveModel X M)
          (isKFlat_kFlatModel X K) (kFlatModelIso X K) eI (kInjectiveModelIso X M)).inv ≫
        derivedTensorHomDiagonal X K L M ≫
        (derivedTensorHomTargetIsoOfModels X (N := kInjectiveModel X M)
          (isKFlat_kFlatModel X K) (kFlatModelIso X K) eI
          (kInjectiveModelIso X M) q hq).hom =
      DerivedCategory.Q.map
        (derivedTensorHomMapOfModels X (N := kInjectiveModel X M) q) := by
  obtain ⟨i, hi⟩ := exists_Q_map_eq_of_isKInjective X
    ((kInjectiveModelIso X L).hom ≫ eI.inv)
  have hiIso : IsIso (DerivedCategory.Q.map i) := by rw [hi]; infer_instance
  have hq0 : IsIso (DerivedCategory.Q.map
      (tensorTotalMap X (𝟙 (kFlatModel X K)) i ≫ q)) := by
    rw [CategoryTheory.Functor.map_comp]
    exact IsIso.comp_isIso'
      (isIso_Q_map_tensorTotalMap_right X _ i (isKFlat_kFlatModel X K) hiIso) hq
  have hknown := derivedTensorHomDiagonal_eq_ofModels_kInjectiveTarget X K L M
    (tensorTotalMap X (𝟙 (kFlatModel X K)) i ≫ q) hq0
  rw [derivedTensorHomTargetIsoOfModels_comp_tensorTotalMap X (isKFlat_kFlatModel X K)
      (kFlatModelIso X K) (kInjectiveModelIso X L) eI (kInjectiveModelIso X M) i hi q hq hq0,
    derivedTensorHomMapOfModels_comp, CategoryTheory.Functor.map_comp] at hknown
  have hC := derivedTensorHomSourceIsoOfModels_naturality_right X
    (isKFlat_kFlatModel X K) (kFlatModelIso X K) (kInjectiveModelIso X L) eI
    (kInjectiveModelIso X M) i hi
  rw [(Iso.eq_inv_comp _).2 hC, Category.assoc] at hknown
  rw [(cancel_epi _).mp hknown, Iso.inv_hom_id_assoc]

/-! ### Changing the representative of `M` -/

/-- The source comparison at arbitrary models is natural in the representative of `M`. -/
theorem derivedTensorHomSourceIsoOfModels_naturality_source [I.IsKInjective]
    (hA : Stacks.SheafOfModules.IsKFlat X.O A)
    (eA : DerivedCategory.Q.obj A ≅ K) (eI : DerivedCategory.Q.obj I ≅ L)
    (eN : DerivedCategory.Q.obj N ≅ M)
    {N₁ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eN₁ : DerivedCategory.Q.obj N₁ ≅ M) (n : N₁ ⟶ N)
    (hn : DerivedCategory.Q.map n = eN₁.hom ≫ eN.inv) :
    (derivedTensorHomSourceIsoOfModels X hA eA eI eN).hom ≫
        DerivedCategory.Q.map (tensorTotalMap X (𝟙 A) (homMap X n (𝟙 I))) =
      (derivedTensorHomSourceIsoOfModels X hA eA eI eN₁).hom := by
  dsimp only [derivedTensorHomSourceIsoOfModels, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.mapIso_inv, Iso.app_hom]
  simp only [Category.assoc]
  rw [← comparisonLeft_tensorTotal_naturality_right X A (homMap X n (𝟙 I)) hA,
    ← NatTrans.naturality_assoc, ← CategoryTheory.Functor.map_comp_assoc]
  simp only [Category.assoc]
  rw [derivedSheafHomObjectsModelIso_comparison_naturality_source X eI eN eN₁ n hn]

/-- The target comparison at arbitrary models is natural in the representative of `M`. -/
theorem derivedTensorHomTargetIsoOfModels_naturality_source [J.IsKInjective]
    (hA : Stacks.SheafOfModules.IsKFlat X.O A)
    (eA : DerivedCategory.Q.obj A ≅ K) (eI : DerivedCategory.Q.obj I ≅ L)
    (eN : DerivedCategory.Q.obj N ≅ M)
    {N₁ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eN₁ : DerivedCategory.Q.obj N₁ ≅ M) (n : N₁ ⟶ N)
    (hn : DerivedCategory.Q.map n = eN₁.hom ≫ eN.inv)
    (q : tensorTotal X A I ⟶ J) (hq : IsIso (DerivedCategory.Q.map q)) :
    (derivedTensorHomTargetIsoOfModels X hA eA eI eN q hq).hom ≫
        DerivedCategory.Q.map (homMap X n (𝟙 J)) =
      (derivedTensorHomTargetIsoOfModels X hA eA eI eN₁ q hq).hom := by
  dsimp only [derivedTensorHomTargetIsoOfModels, Iso.trans_hom,
    CategoryTheory.Functor.mapIso_hom, Iso.app_hom, asIso_hom]
  simp only [Category.assoc]
  rw [← derivedSheafHomComparison_naturality_id_target X J n, ← NatTrans.naturality_assoc,
    reassoc_of% (derivedSheafHomBifunctor_map_op_comp X eN eN₁ n hn
      (DerivedCategory.Q.obj J)), NatTrans.naturality_assoc]

omit [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ B, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj B).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- The complex-level morphism of Stacks 0BYR is natural in the representative of `M`. -/
theorem derivedTensorHomMapOfModels_naturality_source
    {N₁ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (n : N₁ ⟶ N) (q : tensorTotal X A I ⟶ J) :
    derivedTensorHomMapOfModels X (N := N) q ≫ homMap X n (𝟙 J) =
      tensorTotalMap X (𝟙 A) (homMap X n (𝟙 I)) ≫
        derivedTensorHomMapOfModels X (N := N₁) q := by
  dsimp only [derivedTensorHomMapOfModels]
  rw [Category.assoc, homMap_comp, Category.comp_id, Category.comp_id,
    ← Category.assoc, ← tensorHomInterchange_natural_source X A I n, Category.assoc,
    homMap_comp, Category.id_comp, Category.id_comp]

/-- **The characterisation of the diagonal of Stacks 0BYS at arbitrary `I`, `N`, `J` and `q`.**
Only the K-flat representative of `K` is still the chosen one: `I` is any K-injective complex
representing `L`, `N` is *any* complex representing `M`, `J` is any K-injective complex and
`q : Tot(A ⊗_O I) ⟶ J` any quasi-isomorphism. This generalises
`derivedTensorHomDiagonal_eq_ofModels_kInjective` in the `N` variable.

An arbitrary `N` is compared with the chosen representative of `M` by a morphism of complexes
`n` going *into* it, which exists because the chosen one is K-injective. The diagonal is
contravariant in the source of the internal Hom, so that direction is the one the three
naturality statements need. -/
theorem derivedTensorHomDiagonal_eq_ofModels_kFlatModel
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective]
    (eI : DerivedCategory.Q.obj I ≅ L)
    {N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eN : DerivedCategory.Q.obj N ≅ M)
    {J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [J.IsKInjective]
    (q : tensorTotal X (kFlatModel X K) I ⟶ J)
    (hq : IsIso (DerivedCategory.Q.map q)) :
    (derivedTensorHomSourceIsoOfModels X (isKFlat_kFlatModel X K)
          (kFlatModelIso X K) eI eN).inv ≫
        derivedTensorHomDiagonal X K L M ≫
        (derivedTensorHomTargetIsoOfModels X (isKFlat_kFlatModel X K)
          (kFlatModelIso X K) eI eN q hq).hom =
      DerivedCategory.Q.map (derivedTensorHomMapOfModels X (N := N) q) := by
  obtain ⟨n, hn⟩ := exists_Q_map_eq_of_isKInjective X
    (eN.hom ≫ (kInjectiveModelIso X M).inv)
  have hknown := derivedTensorHomDiagonal_eq_ofModels_kInjective X K L M eI q hq
  have h2 : derivedTensorHomDiagonal X K L M ≫
      (derivedTensorHomTargetIsoOfModels X (isKFlat_kFlatModel X K)
        (kFlatModelIso X K) eI (kInjectiveModelIso X M) q hq).hom =
      (derivedTensorHomSourceIsoOfModels X (isKFlat_kFlatModel X K)
          (kFlatModelIso X K) eI (kInjectiveModelIso X M)).hom ≫
        DerivedCategory.Q.map (derivedTensorHomMapOfModels X
          (N := kInjectiveModel X M) q) := by
    rw [← hknown, Iso.hom_inv_id_assoc]
  have key : derivedTensorHomDiagonal X K L M ≫
      (derivedTensorHomTargetIsoOfModels X (isKFlat_kFlatModel X K)
        (kFlatModelIso X K) eI eN q hq).hom =
      (derivedTensorHomSourceIsoOfModels X (isKFlat_kFlatModel X K)
          (kFlatModelIso X K) eI eN).hom ≫
        DerivedCategory.Q.map (derivedTensorHomMapOfModels X (N := N) q) := by
    rw [← derivedTensorHomTargetIsoOfModels_naturality_source X (isKFlat_kFlatModel X K)
        (kFlatModelIso X K) eI (kInjectiveModelIso X M) eN n hn q hq,
      ← Category.assoc, h2, Category.assoc, ← CategoryTheory.Functor.map_comp,
      derivedTensorHomMapOfModels_naturality_source X n q,
      CategoryTheory.Functor.map_comp, ← Category.assoc,
      derivedTensorHomSourceIsoOfModels_naturality_source X (isKFlat_kFlatModel X K)
        (kFlatModelIso X K) eI (kInjectiveModelIso X M) eN n hn]
  rw [key, Iso.inv_hom_id_assoc]

/-! ### Changing the K-flat representative of `K`: the roof -/

/-- Two representing isomorphisms of `K` compared by a morphism of complexes induce the same
map of derived tensor product functors. -/
theorem derivedTensorProductFunctor_map_inv_comp
    {A₀ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eA : DerivedCategory.Q.obj A ≅ K) (eA₀ : DerivedCategory.Q.obj A₀ ≅ K) (c : A ⟶ A₀)
    (hc : DerivedCategory.Q.map c = eA.hom ≫ eA₀.inv)
    (Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map eA.inv).app Z ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
          (DerivedCategory.Q.map c)).app Z =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map eA₀.inv).app Z := by
  rw [← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp]
  congr 2
  rw [hc, Iso.inv_hom_id_assoc]

/-- The tensor comparison at arbitrary models is natural in the K-flat representative of `K`. -/
theorem derivedTensorObjectsIsoOfModels_naturality_left
    {A₀ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A)
    (hA₀ : Stacks.SheafOfModules.IsKFlat X.O A₀)
    (eA : DerivedCategory.Q.obj A ≅ K) (eA₀ : DerivedCategory.Q.obj A₀ ≅ K)
    (eI : DerivedCategory.Q.obj I ≅ L) (c : A ⟶ A₀)
    (hc : DerivedCategory.Q.map c = eA.hom ≫ eA₀.inv) :
    (derivedTensorObjectsIsoOfModels X hA eA eI).hom ≫
        DerivedCategory.Q.map (tensorTotalMap X c (𝟙 I)) =
      (derivedTensorObjectsIsoOfModels X hA₀ eA₀ eI).hom := by
  dsimp only [derivedTensorObjectsIsoOfModels, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.mapIso_inv, Iso.app_hom]
  simp only [Category.assoc]
  rw [← comparisonLeft_tensorTotal_naturality_left X hA hA₀ c I, ← NatTrans.naturality_assoc,
    reassoc_of% (derivedTensorProductFunctor_map_inv_comp X eA eA₀ c hc
      (DerivedCategory.Q.obj I)), NatTrans.naturality_assoc]

/-- The source comparison at arbitrary models is natural in the K-flat representative of `K`. -/
theorem derivedTensorHomSourceIsoOfModels_naturality_left [I.IsKInjective]
    {A₀ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A)
    (hA₀ : Stacks.SheafOfModules.IsKFlat X.O A₀)
    (eA : DerivedCategory.Q.obj A ≅ K) (eA₀ : DerivedCategory.Q.obj A₀ ≅ K)
    (eI : DerivedCategory.Q.obj I ≅ L) (eN : DerivedCategory.Q.obj N ≅ M)
    (c : A ⟶ A₀) (hc : DerivedCategory.Q.map c = eA.hom ≫ eA₀.inv) :
    (derivedTensorHomSourceIsoOfModels X hA eA eI eN).hom ≫
        DerivedCategory.Q.map
          (tensorTotalMap X c (𝟙 (sheafHomComplex X N I).obj)) =
      (derivedTensorHomSourceIsoOfModels X hA₀ eA₀ eI eN).hom := by
  dsimp only [derivedTensorHomSourceIsoOfModels, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.mapIso_inv, Iso.app_hom]
  simp only [Category.assoc]
  rw [← comparisonLeft_tensorTotal_naturality_left X hA hA₀ c (sheafHomComplex X N I).obj,
    reassoc_of% (derivedTensorProductFunctor_map_inv_comp X eA eA₀ c hc
      (DerivedCategory.Q.obj (sheafHomComplex X N I).obj))]

/-- The target comparison is unchanged by moving the K-flat representative of `K` along `c` and
precomposing `q` with the induced map of total tensor products. -/
theorem derivedTensorHomTargetIsoOfModels_comp_tensorTotalMap_left [J.IsKInjective]
    {A₀ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A)
    (hA₀ : Stacks.SheafOfModules.IsKFlat X.O A₀)
    (eA : DerivedCategory.Q.obj A ≅ K) (eA₀ : DerivedCategory.Q.obj A₀ ≅ K)
    (eI : DerivedCategory.Q.obj I ≅ L) (eN : DerivedCategory.Q.obj N ≅ M)
    (c : A ⟶ A₀) (hc : DerivedCategory.Q.map c = eA.hom ≫ eA₀.inv)
    (q : tensorTotal X A₀ I ⟶ J) (hq : IsIso (DerivedCategory.Q.map q))
    (hq0 : IsIso (DerivedCategory.Q.map (tensorTotalMap X c (𝟙 I) ≫ q))) :
    derivedTensorHomTargetIsoOfModels X hA eA eI eN
          (tensorTotalMap X c (𝟙 I) ≫ q) hq0 =
      derivedTensorHomTargetIsoOfModels X hA₀ eA₀ eI eN q hq := by
  apply Iso.ext
  dsimp only [derivedTensorHomTargetIsoOfModels, Iso.trans_hom,
    CategoryTheory.Functor.mapIso_hom, Iso.app_hom, asIso_hom]
  rw [CategoryTheory.Functor.map_comp DerivedCategory.Q,
    CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [← NatTrans.naturality_assoc, ← CategoryTheory.Functor.map_comp_assoc,
    derivedTensorObjectsIsoOfModels_naturality_left X hA hA₀ eA eA₀ eI c hc]

omit [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ B, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj B).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- Precomposing `q` with the map induced by `c` precomposes the complex-level morphism of
Stacks 0BYR with the map induced by `c ⊗ 𝟙`. -/
theorem derivedTensorHomMapOfModels_comp_left
    {A₀ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (c : A ⟶ A₀) (q : tensorTotal X A₀ I ⟶ J) :
    derivedTensorHomMapOfModels X (N := N) (tensorTotalMap X c (𝟙 I) ≫ q) =
      tensorTotalMap X c (𝟙 (sheafHomComplex X N I).obj) ≫
        derivedTensorHomMapOfModels X (N := N) q := by
  dsimp only [derivedTensorHomMapOfModels]
  rw [← Category.assoc, ← tensorHomInterchange_natural_tensor X c I N, Category.assoc,
    homMap_comp, Category.id_comp]

/-- **The characterisation depends on `q` only through its class in `D(O)`.** -/
theorem derivedTensorHomDiagonal_eq_ofModels_congr_q [I.IsKInjective] [J.IsKInjective]
    (hA : Stacks.SheafOfModules.IsKFlat X.O A)
    (eA : DerivedCategory.Q.obj A ≅ K) (eI : DerivedCategory.Q.obj I ≅ L)
    (eN : DerivedCategory.Q.obj N ≅ M)
    (q q' : tensorTotal X A I ⟶ J) (hq : IsIso (DerivedCategory.Q.map q))
    (hq' : IsIso (DerivedCategory.Q.map q'))
    (h : DerivedCategory.Q.map q = DerivedCategory.Q.map q')
    (hyp : (derivedTensorHomSourceIsoOfModels X hA eA eI eN).inv ≫
        derivedTensorHomDiagonal X K L M ≫
        (derivedTensorHomTargetIsoOfModels X hA eA eI eN q' hq').hom =
      DerivedCategory.Q.map (derivedTensorHomMapOfModels X (N := N) q')) :
    (derivedTensorHomSourceIsoOfModels X hA eA eI eN).inv ≫
        derivedTensorHomDiagonal X K L M ≫
        (derivedTensorHomTargetIsoOfModels X hA eA eI eN q hq).hom =
      DerivedCategory.Q.map (derivedTensorHomMapOfModels X (N := N) q) := by
  have htgt : (derivedTensorHomTargetIsoOfModels X hA eA eI eN q hq).hom =
      (derivedTensorHomTargetIsoOfModels X hA eA eI eN q' hq').hom := by
    dsimp only [derivedTensorHomTargetIsoOfModels, Iso.trans_hom,
      CategoryTheory.Functor.mapIso_hom, Iso.app_hom, asIso_hom]
    rw [h]
  have hmap : DerivedCategory.Q.map (derivedTensorHomMapOfModels X (N := N) q) =
      DerivedCategory.Q.map (derivedTensorHomMapOfModels X (N := N) q') := by
    dsimp only [derivedTensorHomMapOfModels]
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      Q_map_homMap_congr_of_isKInjective X N (tensorTotal X A I) h]
  rw [htgt, hmap]
  exact hyp

/-- **Transporting the characterisation along a morphism of K-flat representatives of `K`.**
Both directions hold, the comparison of the two source identifications being an isomorphism;
that is what lets a roof be traversed in both of its legs. -/
theorem derivedTensorHomDiagonal_eq_ofModels_iff_of_kFlatMap [I.IsKInjective] [J.IsKInjective]
    {A₀ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A)
    (hA₀ : Stacks.SheafOfModules.IsKFlat X.O A₀)
    (eA : DerivedCategory.Q.obj A ≅ K) (eA₀ : DerivedCategory.Q.obj A₀ ≅ K)
    (eI : DerivedCategory.Q.obj I ≅ L) (eN : DerivedCategory.Q.obj N ≅ M)
    (c : A ⟶ A₀) (hc : DerivedCategory.Q.map c = eA.hom ≫ eA₀.inv)
    (q : tensorTotal X A₀ I ⟶ J) (hq : IsIso (DerivedCategory.Q.map q))
    (hq0 : IsIso (DerivedCategory.Q.map (tensorTotalMap X c (𝟙 I) ≫ q))) :
    ((derivedTensorHomSourceIsoOfModels X hA eA eI eN).inv ≫
          derivedTensorHomDiagonal X K L M ≫
          (derivedTensorHomTargetIsoOfModels X hA eA eI eN
            (tensorTotalMap X c (𝟙 I) ≫ q) hq0).hom =
        DerivedCategory.Q.map (derivedTensorHomMapOfModels X (N := N)
          (tensorTotalMap X c (𝟙 I) ≫ q))) ↔
      ((derivedTensorHomSourceIsoOfModels X hA₀ eA₀ eI eN).inv ≫
          derivedTensorHomDiagonal X K L M ≫
          (derivedTensorHomTargetIsoOfModels X hA₀ eA₀ eI eN q hq).hom =
        DerivedCategory.Q.map (derivedTensorHomMapOfModels X (N := N) q)) := by
  rw [derivedTensorHomTargetIsoOfModels_comp_tensorTotalMap_left X hA hA₀ eA eA₀ eI eN c hc
      q hq hq0,
    derivedTensorHomMapOfModels_comp_left X c q, CategoryTheory.Functor.map_comp,
    (Iso.eq_inv_comp _).2 (derivedTensorHomSourceIsoOfModels_naturality_left X hA hA₀ eA eA₀ eI eN
      c hc), Category.assoc, cancel_epi, Iso.inv_comp_eq]

/-- **The characterisation of the diagonal of Stacks 0BYS at an arbitrary choice of all five
models.** For any K-flat `A` representing `K`, any K-injective `I` representing `L`, any complex
`N` representing `M`, any K-injective `J` and any quasi-isomorphism `q : Tot(A ⊗_O I) ⟶ J`, the
diagonal is the class of the complex-level morphism of Stacks 0BYR built from those models,
conjugated by the corresponding comparisons.

This is the form in which the source states the construction, and it is what
`derivedTensorHomDiagonal_eq` — stated at the chosen representatives only — is generalised to.

The K-flat variable is the one that cannot be moved by a morphism of complexes: K-flat complexes
have no universal property against quasi-isomorphisms. An arbitrary K-flat `A` and the chosen
`kFlatModel K` are instead compared through a roof `A ⟵ P ⟶ kFlatModel K` whose apex is itself
K-flat, obtained by writing the comparison isomorphism of `D(O)` as a right fraction
(`DerivedCategory.right_fac`) and replacing the apex of that fraction by a K-flat resolution
(Stacks 06YS). Both legs are then traversed with
`derivedTensorHomDiagonal_eq_ofModels_iff_of_kFlatMap`, in opposite directions, which is why
that transport is stated as an equivalence. The two legs do not carry the *same* morphism into
`J`, only morphisms with the same class in `D(O)`, and
`derivedTensorHomDiagonal_eq_ofModels_congr_q` closes that gap. -/
theorem derivedTensorHomDiagonal_eq_ofModels
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (eA : DerivedCategory.Q.obj A ≅ K)
    {I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective]
    (eI : DerivedCategory.Q.obj I ≅ L)
    {N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eN : DerivedCategory.Q.obj N ≅ M)
    {J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [J.IsKInjective]
    (q : tensorTotal X A I ⟶ J) (hq : IsIso (DerivedCategory.Q.map q)) :
    (derivedTensorHomSourceIsoOfModels X hA eA eI eN).inv ≫
        derivedTensorHomDiagonal X K L M ≫
        (derivedTensorHomTargetIsoOfModels X hA eA eI eN q hq).hom =
      DerivedCategory.Q.map (derivedTensorHomMapOfModels X (N := N) q) := by
  obtain ⟨P₀, s₀, hs₀, g₀, hfac₀⟩ := DerivedCategory.right_fac
    (eA.hom ≫ (kFlatModelIso X K).inv)
  obtain ⟨P, p, hP, hp⟩ := Stacks.SheafOfModules.exists_kFlat_quasiIso X P₀
  have := hs₀
  have : QuasiIso p := hp
  have hpiso : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hp
  have hsr : IsIso (DerivedCategory.Q.map (p ≫ s₀)) := by
    rw [CategoryTheory.Functor.map_comp]; infer_instance
  have hfac : DerivedCategory.Q.map (p ≫ s₀) ≫ eA.hom ≫ (kFlatModelIso X K).inv =
      DerivedCategory.Q.map (p ≫ g₀) := by
    rw [hfac₀, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      Category.assoc, IsIso.hom_inv_id_assoc]
  have := hsr
  have hc_sr : DerivedCategory.Q.map (p ≫ s₀) =
      (asIso (DerivedCategory.Q.map (p ≫ s₀)) ≪≫ eA).hom ≫ eA.inv := by
    simp
  have hc_gr : DerivedCategory.Q.map (p ≫ g₀) =
      (asIso (DerivedCategory.Q.map (p ≫ s₀)) ≪≫ eA).hom ≫
        (kFlatModelIso X K).inv := by
    simp only [Iso.trans_hom, asIso_hom, Category.assoc]
    exact hfac.symm
  have hgriso : IsIso (DerivedCategory.Q.map (p ≫ g₀)) := by
    rw [hc_gr]; infer_instance
  have hτsr : IsIso (DerivedCategory.Q.map (tensorTotalMap X (p ≫ s₀) (𝟙 I))) :=
    isIso_Q_map_tensorTotalMap_left X hP hA (p ≫ s₀) hsr I
  have hτgr : IsIso (DerivedCategory.Q.map (tensorTotalMap X (p ≫ g₀) (𝟙 I))) :=
    isIso_Q_map_tensorTotalMap_left X hP (isKFlat_kFlatModel X K) (p ≫ g₀) hgriso I
  have hqsr : IsIso (DerivedCategory.Q.map
      (tensorTotalMap X (p ≫ s₀) (𝟙 I) ≫ q)) := by
    rw [CategoryTheory.Functor.map_comp]; exact IsIso.comp_isIso' hτsr hq
  obtain ⟨q', hq'eq⟩ := exists_Q_map_eq_of_isKInjective X
    (inv (DerivedCategory.Q.map (tensorTotalMap X (p ≫ g₀) (𝟙 I))) ≫
      DerivedCategory.Q.map (tensorTotalMap X (p ≫ s₀) (𝟙 I) ≫ q))
  have hq'iso : IsIso (DerivedCategory.Q.map q') := by
    rw [hq'eq]
    have := hτgr
    have := hqsr
    infer_instance
  have hqgr : IsIso (DerivedCategory.Q.map
      (tensorTotalMap X (p ≫ g₀) (𝟙 I) ≫ q')) := by
    rw [CategoryTheory.Functor.map_comp]; exact IsIso.comp_isIso' hτgr hq'iso
  have heq : DerivedCategory.Q.map (tensorTotalMap X (p ≫ g₀) (𝟙 I) ≫ q') =
      DerivedCategory.Q.map (tensorTotalMap X (p ≫ s₀) (𝟙 I) ≫ q) := by
    rw [CategoryTheory.Functor.map_comp, hq'eq, IsIso.hom_inv_id_assoc]
  have hknown := derivedTensorHomDiagonal_eq_ofModels_kFlatModel X K L M eI eN q' hq'iso
  have hP_gr := (derivedTensorHomDiagonal_eq_ofModels_iff_of_kFlatMap X hP
    (isKFlat_kFlatModel X K) (asIso (DerivedCategory.Q.map (p ≫ s₀)) ≪≫ eA)
    (kFlatModelIso X K) eI eN (p ≫ g₀) hc_gr q' hq'iso hqgr).mpr hknown
  have hP_sr := derivedTensorHomDiagonal_eq_ofModels_congr_q X hP
    (asIso (DerivedCategory.Q.map (p ≫ s₀)) ≪≫ eA) eI eN
    (tensorTotalMap X (p ≫ s₀) (𝟙 I) ≫ q)
    (tensorTotalMap X (p ≫ g₀) (𝟙 I) ≫ q') hqsr hqgr heq.symm hP_gr
  exact (derivedTensorHomDiagonal_eq_ofModels_iff_of_kFlatMap X hP hA
    (asIso (DerivedCategory.Q.map (p ≫ s₀)) ≪≫ eA) eA eI eN (p ≫ s₀) hc_sr q hq hqsr).mp hP_sr

/-- **The diagonal of Stacks 0BYS is invertible exactly when the complex-level morphism of
Stacks 0BYR at any one choice of models is a quasi-isomorphism.** The criterion is free of the
chosen representatives: any K-flat `A`, K-injective `I`, arbitrary `N`,
K-injective `J` and quasi-isomorphism `q` may be used, so a proof is free to pick models adapted
to the hypothesis at hand. -/
theorem isIso_derivedTensorHomDiagonal_iff_quasiIso_ofModels
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (eA : DerivedCategory.Q.obj A ≅ K)
    {I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective]
    (eI : DerivedCategory.Q.obj I ≅ L)
    {N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eN : DerivedCategory.Q.obj N ≅ M)
    {J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [J.IsKInjective]
    (q : tensorTotal X A I ⟶ J) (hq : IsIso (DerivedCategory.Q.map q)) :
    IsIso (derivedTensorHomDiagonal X K L M) ↔
      QuasiIso (derivedTensorHomMapOfModels X (N := N) q) := by
  have h := derivedTensorHomDiagonal_eq_ofModels X K L M hA eA eI eN q hq
  have hD : derivedTensorHomDiagonal X K L M =
      (derivedTensorHomSourceIsoOfModels X hA eA eI eN).hom ≫
        DerivedCategory.Q.map (derivedTensorHomMapOfModels X (N := N) q) ≫
        (derivedTensorHomTargetIsoOfModels X hA eA eI eN q hq).inv := by
    rw [← h]; simp
  rw [hD, isIso_comp_left_iff, isIso_comp_right_iff,
    DerivedCategory.isIso_Q_map_iff_quasiIso]

/-- **The diagonal of Stacks 0BYS is invertible as soon as the complex-level morphism of
Stacks 0BYR is a quasi-isomorphism locally on the site.** This is the "we may work locally" step
in the form that needs no compatibility of the *diagonal* with restriction: the diagonal is
first replaced by the complex-level morphism at one choice of models
(`isIso_derivedTensorHomDiagonal_iff_quasiIso_ofModels`), and quasi-isomorphy of a morphism of
complexes of `O`-modules is already known to be local
(`Stacks.SheafOfModules.quasiIso_of_coversTop`). -/
theorem isIso_derivedTensorHomDiagonal_of_coversTop
    [HasWeakSheafify X.J AddCommGrpCat.{u}]
    [∀ V : X.C, HasWeakSheafify (X.J.over V) AddCommGrpCat.{u}]
    [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (eA : DerivedCategory.Q.obj A ≅ K)
    {I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective]
    (eI : DerivedCategory.Q.obj I ≅ L)
    {N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eN : DerivedCategory.Q.obj N ≅ M)
    {J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [J.IsKInjective]
    (q : tensorTotal X A I ⟶ J) (hq : IsIso (DerivedCategory.Q.map q))
    {ι : Type*} {V : ι → X.C} (hV : X.J.CoversTop V)
    (h : ∀ i, QuasiIso (((SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (V i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (derivedTensorHomMapOfModels X (N := N) q))) :
    IsIso (derivedTensorHomDiagonal X K L M) := by
  rw [isIso_derivedTensorHomDiagonal_iff_quasiIso_ofModels X K L M hA eA eI eN q hq]
  exact Stacks.SheafOfModules.quasiIso_of_coversTop hV _ h

/-- If `SheafHom(N, q)` is a quasi-isomorphism, the diagonal of Stacks 0BYS is invertible exactly
when the interchange morphism of Stacks 0BYR is a quasi-isomorphism. -/
private theorem isIso_derivedTensorHomDiagonal_iff_quasiIso_interchange_of_quasiIso_homMap
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (eA : DerivedCategory.Q.obj A ≅ K)
    {I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective]
    (eI : DerivedCategory.Q.obj I ≅ L)
    {N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eN : DerivedCategory.Q.obj N ≅ M)
    {J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [J.IsKInjective]
    (q : tensorTotal X A I ⟶ J) (hq : IsIso (DerivedCategory.Q.map q))
    (hhm : QuasiIso (homMap X (𝟙 N) q)) :
    IsIso (derivedTensorHomDiagonal X K L M) ↔
      QuasiIso (tensorHomInterchange X A I N) := by
  have hhmi : IsIso (DerivedCategory.Q.map (homMap X (𝟙 N) q)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hhm
  rw [isIso_derivedTensorHomDiagonal_iff_quasiIso_ofModels X K L M hA eA eI eN q hq]
  dsimp only [derivedTensorHomMapOfModels]
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso, ← DerivedCategory.isIso_Q_map_iff_quasiIso,
    CategoryTheory.Functor.map_comp]
  exact isIso_comp_right_iff _ _

/-- **When the total tensor product of the chosen models is itself K-injective, the diagonal of
Stacks 0BYS is invertible exactly when the interchange morphism of Stacks 0BYR is a
quasi-isomorphism.**

The complex-level morphism of Stacks 0BYR at a choice of models is the interchange morphism
followed by the map induced by `q`. When `Tot(A ⊗_O I)` is K-injective that second factor is a
quasi-isomorphism between internal Hom complexes with K-injective targets, hence invertible in
`D(O)` by Stacks 0A95, so it cancels and only the interchange is left.

The hypothesis holds in the case the source of Stacks 0ATN calls clear: for `A` a bounded
complex of finite free modules `Tot(A ⊗_O I)` is a finite direct sum of shifts of the
K-injective `I`. So this isolates the one statement that case needs — that the interchange
morphism of Stacks 0BYR is a quasi-isomorphism for a strictly perfect tensor factor — which is
not in the library. -/
theorem isIso_derivedTensorHomDiagonal_iff_quasiIso_tensorHomInterchange
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (eA : DerivedCategory.Q.obj A ≅ K)
    {I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective]
    (eI : DerivedCategory.Q.obj I ≅ L)
    {N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eN : DerivedCategory.Q.obj N ≅ M)
    {J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [J.IsKInjective]
    (q : tensorTotal X A I ⟶ J) (hq : IsIso (DerivedCategory.Q.map q))
    [(tensorTotal X A I).IsKInjective] :
    IsIso (derivedTensorHomDiagonal X K L M) ↔
      QuasiIso (tensorHomInterchange X A I N) := by
  have : QuasiIso q := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 hq
  exact isIso_derivedTensorHomDiagonal_iff_quasiIso_interchange_of_quasiIso_homMap X K L M hA eA
    eI eN q hq (homMap_quasiIso X q (𝟙 N))

/-- **For a strictly perfect representative of `M`, the diagonal of Stacks 0BYS is invertible
exactly when the interchange morphism of Stacks 0BYR is a quasi-isomorphism.**

This is the companion of
`isIso_derivedTensorHomDiagonal_iff_quasiIso_tensorHomInterchange` on the other side of the
interchange, and it needs no K-injectivity of `Tot(A ⊗_O I)`: for a bounded `N` whose terms are
direct summands of finite free modules, the internal Hom complex out of `N` carries a
quasi-isomorphism of targets to a quasi-isomorphism — that is Stacks 08JH's input
`homMap_quasiIso_of_isFiniteFreeSummand` — so the factor induced by `q` cancels directly.

Both reductions leave the same single statement, that the interchange morphism of Stacks 0BYR is
a quasi-isomorphism when one of its two complexes is strictly perfect. That statement is not in
the library. -/
theorem isIso_derivedTensorHomDiagonal_iff_quasiIso_tensorHomInterchange_of_isFiniteFreeSummand
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (eA : DerivedCategory.Q.obj A ≅ K)
    {I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective]
    (eI : DerivedCategory.Q.obj I ≅ L)
    {N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eN : DerivedCategory.Q.obj N ≅ M)
    {J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [J.IsKInjective]
    (q : tensorTotal X A I ⟶ J) (hq : IsIso (DerivedCategory.Q.map q))
    (hNbdd : {i : ℤ | ¬ IsZero (N.X i)}.Finite)
    (hNterm : ∀ i, IsFiniteFreeSummand X (N.X i)) :
    IsIso (derivedTensorHomDiagonal X K L M) ↔
      QuasiIso (tensorHomInterchange X A I N) := by
  have : QuasiIso q := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 hq
  exact isIso_derivedTensorHomDiagonal_iff_quasiIso_interchange_of_quasiIso_homMap X K L M hA eA
    eI eN q hq (homMap_quasiIso_of_isFiniteFreeSummand X q N hNbdd hNterm)

end AlgebraicGeometry.RingedSite

end
