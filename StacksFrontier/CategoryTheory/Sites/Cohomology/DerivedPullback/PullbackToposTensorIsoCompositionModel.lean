module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOnRingedTopoi
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorTotalSquare
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorIsoAlongAComposite

/-!
# The Tag 07A4 comparison along a composite, at a pair of K-flat complexes with flat terms

Let `f : (Sh(C), O) ⟶ (Sh(D), O')` and `g : (Sh(D), O') ⟶ (Sh(E), O'')` be morphisms of ringed
topoi, so that `g.comp f : (Sh(C), O) ⟶ (Sh(E), O'')` is one too (**Stacks 03CC**).
`Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso` is the comparison of **Stacks 07A4**,

`Lf^*(K ⊗^L_{O'} L) ≅ Lf^*K ⊗^L_O Lf^*L`,

and `Stacks.Cohomology.DerivedPullbackCompositionOnTopoi.derivedPullbackCompIso` is the
composition isomorphism `Lg^* ⋙ Lf^* ≅ L(g ∘ f)^*` of **Stacks 0D6D**.  This file proves that the
second carries the comparison for `g ∘ f` to the derived pullback along `f` of the comparison for
`g`, followed by the comparison for `f` and by the composition isomorphism in each tensor factor,
at a pair of K-flat complexes of `O''`-modules with flat terms.

## Main results

* `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_comp_app_of_kFlat`: **the composition
  law for Stacks 07A4 at a pair of K-flat complexes with flat terms**, conditional on the three
  named hypotheses listed below.  No diagram chase is performed here: every comparison in sight
  is computed on such a pair by an ordinary total tensor complex
  (`Stacks.Sheaves.DerivedPullback.toTensor_square_of_kFlat`, which is Stacks 0FPH at a pair of
  models), so the identity is an instance of the category-generic assembly
  `Stacks.Cohomology.DerivedPullbackTensor.tensorComparison_comp_of_models`.
* `Stacks.Sheaves.DerivedPullback.toTensor_naturality_prod`: naturality of the canonical map from
  the derived tensor product to the ordinary total tensor complex, with the action of the derived
  tensor bifunctor on a pair of morphisms written through `CategoryTheory.Functor.uncurry` rather
  than as a two-step composite.
* `isIso_pullbackComparisonQ_of_kFlatBifunctor` (private),
  `Stacks.Sheaves.DerivedPullback.mono_derivedTensorMap_pullbackComparisonQ` and
  `Stacks.Sheaves.DerivedPullback.mono_toTensor_pullbackComplex`: the two monomorphisms the
  assembly cancels, at a pair of K-flat complexes with flat terms.

## Implementation notes

*Which inputs are carried, and why.*  Three facts the assembly consumes are not available in the
tree at the time of writing, and each is taken as a named explicit hypothesis rather than
reproved or weakened around:

* `e`, the degreewise composition isomorphism
  `g^* ⋙ f^* ≅ (g ∘ f)^*` on cochain complexes of modules.  The ringed-space development has it
  as `Stacks.PullbackTensorComposition.pullbackComplexCompIso`; the ringed-topos tree has the
  underlying `AlgebraicGeometry.RingedToposSiteHom.pullbackToposCompIso` on modules and its image
  on homotopy categories, but not the cochain-complex isomorphism itself.  Parametrising over it
  keeps this module free of anything unfinished: nothing below inspects `e`, so any construction
  of it may be substituted.
* `hcompQ`, the composition law for the comparison `Lf^*(QM) ⟶ Q(f^*M)` of **Stacks 06YY**, read
  against `e`.  This fills three slots of the assembly at once — the resolutions of `K`, of `L`
  and of the total tensor complex `Tot(K ⊗ L)` — which is why it is stated for an *arbitrary*
  complex `M` and not only for K-flat ones: the assembly needs it at `Tot(K ⊗ L)`, whose
  K-flatness is irrelevant to the slot it fills.
* `htotal`, the composition law of **Stacks 03EL** for the comparison
  `f^*Tot(K ⊗ L) ≅ Tot(f^*K ⊗ f^*L)`, carried along `DerivedCategory.Q`, again against `e` and
  again for arbitrary complexes.  Its exact shape is the one the `hβ` slot of
  `Stacks.Cohomology.DerivedPullbackTensor.tensorComparison_comp_of_models` consumes once the
  other slots have been filled: the tensor action on the pair `(e.hom.app P, e.hom.app N)` is
  forced to be `CategoryTheory.HomologicalComplex.mapBifunctorMap` by the `hcmp` slot, which is
  naturality of the canonical map to the ordinary total tensor complex.

Nothing is assumed about the conclusion, and the conclusion is not restricted: the K-flatness and
termwise flatness of `K` and `L` are exactly the hypotheses the models
(`Stacks.Sheaves.DerivedPullback.toTensor_square_of_kFlat`) already carry, and no boundedness or
further flatness is asked for.

*Where the chase is.*  Nowhere here.
`Stacks.Cohomology.DerivedPullbackTensor.tensorComparison_comp_of_models` is stated for arbitrary
categories, bifunctors, functors and transformations of the right shapes, and this file only
instantiates it.  That lemma was written for the ringed-space development, but its statement
mentions no geometry at all, and its module's import closure meets nothing of the ringed-topos
derived tensor product, so it may be imported here.

*Why the assembly is handed over through a `have`.*  Writing the fourteen-argument application as
the body of the theorem would elaborate it against the goal, unifying the assembled type and the
goal side by side as the arguments are processed.  Computing its type from its arguments first and
checking the two finished terms once is what keeps this inside the elaboration budget; the three
model identities are ascribed `: _` for the same reason one step down, so that each is elaborated
on its own — its type is fully determined by `f`, `g`, `K`, `L` — rather than against a slot that
is only half solved when it is reached.  This is the discipline of the ringed-space instantiation
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_comp_app_of_kFlat`.

*The morphism-of-sites hypotheses.*  `AlgebraicGeometry.RingedToposSiteHom` asks only that the
underlying functor be *continuous*; exactness of the inverse image is not a field of it, so such
an `f` need not present a morphism of topoi at all.  `hmosf` and `hmosg` supply that exactness and
are not hypotheses beyond the source's.  The composite needs no third assumption: it is
`AlgebraicGeometry.RingedToposSiteHom.isMorphismOfSites_comp_u`, which is Stacks 03CC.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 0FPH](https://stacks.math.columbia.edu/tag/0FPH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.DerivedPullbackCompositionOnTopoi
open Stacks.Sheaves.DerivedPullback.KFlatPullback
open scoped CategoryTheory.Prod

namespace Stacks.Sheaves.DerivedPullback

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ## Naturality of the canonical map to the ordinary total tensor complex -/

section TensorNaturality

variable (W : RingedTopos.{u, u, u})
  [HasSheafify W.J AddCommGrpCat.{u}] [W.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O) (ComplexShape.up ℤ)]

/-- **The canonical map from the derived tensor product to the ordinary total tensor complex is
natural in both complexes**, with the action of the derived tensor bifunctor on the pair of
morphisms written as the value of the uncurried bifunctor on a morphism of the product category.

This is the `toTensor_naturality` field of
`Stacks.SheafOfModules.DerivedTensorProduct`, reassociated: the field brackets its left-hand side
as a map followed by a map followed by the comparison, whereas the uncurried bifunctor contributes
the first two as a single arrow.  Composition is associative only up to a propositional equality,
so the two are not interchangeable by unification, and the reassociation is recorded once here
rather than performed on the concrete terms below. -/
lemma toTensor_naturality_prod
    {K K' L L' :
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.O)) ℤ}
    (a : K ⟶ K') (b : L ⟶ L') :
    (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor W.O)).map
          (DerivedCategory.Q.map a ×ₘ DerivedCategory.Q.map b) ≫
        (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct W.O).toTensor K' L' =
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct W.O).toTensor K L ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap a b
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O) (ComplexShape.up ℤ)) :=
  (Category.assoc _ _ _).trans
    ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct W.O).toTensor_naturality a b)

end TensorNaturality

/-! ## The two monomorphisms the assembly cancels -/

section Monos

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  (hmos : f.u.IsMorphismOfSites Y.J X.J)

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (A B : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)] in
include hmos in
/-- **The comparison `Lf^*(QK) ⟶ Q(f^*K)` of Stacks 06YY is invertible at a K-flat complex with
flat terms**: there it is the isomorphism of Stacks 06YY itself, by
`flatPullbackIso_hom_eq_pullbackComparisonQ`. -/
private lemma isIso_pullbackComparisonQ_of_kFlatBifunctor
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i)) :
    IsIso (pullbackComparisonQ f K) := by
  rw [← flatPullbackIso_hom_eq_pullbackComparisonQ f hmos K hK hflat]
  infer_instance

include hmos in
/-- **The derived tensor product of the two comparisons `Lf^*(QK) ⟶ Q(f^*K)` is a monomorphism at
a pair of K-flat complexes with flat terms**, being there the derived tensor product of two
isomorphisms.  This is the first of the two monomorphisms
`Stacks.Cohomology.DerivedPullbackTensor.tensorComparison_comp_of_models` cancels. -/
lemma mono_derivedTensorMap_pullbackComparisonQ
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i)) :
    Mono ((Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).map
      (pullbackComparisonQ f K ×ₘ pullbackComparisonQ f L)) := by
  have hiK := isIso_pullbackComparisonQ_of_kFlatBifunctor f hmos K hK hflatK
  have hiL := isIso_pullbackComparisonQ_of_kFlatBifunctor f hmos L hL hflatL
  have hprod : IsIso (pullbackComparisonQ f K ×ₘ pullbackComparisonQ f L) := by
    rw [isIso_prod_iff]
    exact ⟨hiK, hiL⟩
  infer_instance

omit [(pullbackOnHomotopy f).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))] in
include hmos in
/-- **The canonical map to the ordinary total tensor complex on the source is a monomorphism at
the degreewise pullbacks of a pair of K-flat complexes with flat terms**: those pullbacks are
again K-flat by Stacks 0G7E, and there the canonical map is the two-sided K-flat comparison of
Stacks 06YU.  This is the second of the two monomorphisms
`Stacks.Cohomology.DerivedPullbackTensor.tensorComparison_comp_of_models` cancels. -/
lemma mono_toTensor_pullbackComplex
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i)) :
    Mono ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).toTensor
      ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)) := by
  rw [(Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).toTensor_eq_comparison
    _ _ (kFlat_pullbackComplex' f hmos K hK hflatK) (kFlat_pullbackComplex' f hmos L hL hflatL)]
  infer_instance

end Monos

/-! ## The composition law at a pair of K-flat complexes with flat terms -/

section Composite

variable {X Y Z : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O) (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y) (g : RingedToposSiteHom Y Z)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy g).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (g.comp f)).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) (ComplexShape.up ℤ))]
  (hmosf : f.u.IsMorphismOfSites Y.J X.J) (hmosg : g.u.IsMorphismOfSites Z.J Y.J)

/-- **The comparison of Stacks 07A4 is compatible with composition of morphisms of ringed topoi,
at a pair of K-flat complexes with flat terms.**  For such complexes `K`, `L` of `O''`-modules,
the composition isomorphism `Lg^* ⋙ Lf^* ≅ L(g ∘ f)^*` of Stacks 0D6D, followed by the comparison

`L(g ∘ f)^*(QK ⊗^L_{O''} QL) ≅ L(g ∘ f)^*(QK) ⊗^L_O L(g ∘ f)^*(QL)`

of Stacks 07A4, is the derived pullback along `f` of the comparison for `g`, followed by the
comparison for `f` and by the composition isomorphism in each tensor factor.

Three inputs are supplied as explicit hypotheses rather than taken from the tree, each stated for
arbitrary complexes because the assembly needs it both in the tensor factors and at the total
tensor complex:

* `e` is the degreewise composition isomorphism `g^* ⋙ f^* ≅ (g ∘ f)^*` on cochain complexes of
  modules; supplied, since the ringed-topos tree has
  `AlgebraicGeometry.RingedToposSiteHom.pullbackToposCompIso` on modules and
  `Stacks.Cohomology.DerivedPullbackCompositionOnTopoi.pullbackOnHomotopyCompIso` on homotopy
  categories, but no isomorphism of the functors on cochain complexes.  It is the ringed-topos
  analogue of `Stacks.PullbackTensorComposition.pullbackComplexCompIso`, and nothing below
  inspects it, so any construction of it may be substituted.
* `hcompQ` is the composition law for the Stacks 06YY comparison `Lf^*(QM) ⟶ Q(f^*M)` read
  against `e`; supplied, proved in `PullbackComparisonQCompositionLaw.lean` of
  `StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/`.
* `htotal` is the composition law of Stacks 03EL for `f^*Tot(K ⊗ L) ≅ Tot(f^*K ⊗ f^*L)`, carried
  along `DerivedCategory.Q` and read against `e`; supplied, proved in
  `PullbackToposTensorCompositionLaw.lean` of the same directory.

Everything else the assembly asks for is discharged here: the two monomorphisms
(`mono_derivedTensorMap_pullbackComparisonQ` and `mono_toTensor_pullbackComplex`), naturality of
the Stacks 06YY comparison along the Stacks 03EL isomorphism for `g`
(`pullbackComparisonQ_naturality`), naturality of the canonical map to the ordinary total tensor
complex (`toTensor_naturality_prod`), and the three model identities, which are Stacks 0FPH at a
pair of K-flat complexes with flat terms (`toTensor_square_of_kFlat`) at `g`, at `f` — applied to
the degreewise pullbacks `g^*K`, `g^*L`, which are again K-flat with flat terms by Stacks 0G7E —
and at `g ∘ f`. -/
theorem derivedPullbackTensorIso_comp_app_of_kFlat
    (e : pullbackComplex g ⋙ pullbackComplex f ≅ pullbackComplex (g.comp f))
    (hcompQ : ∀ M : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ,
      (derivedPullbackCompIso f g hmosf hmosg).hom.app (DerivedCategory.Q.obj M) ≫
          pullbackComparisonQ (g.comp f) M =
        (derivedPullback f).map (pullbackComparisonQ g M) ≫
          pullbackComparisonQ f ((pullbackComplex g).obj M) ≫
            DerivedCategory.Q.map (e.hom.app M))
    (htotal : ∀ P N : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ,
      DerivedCategory.Q.map
            (e.hom.app (((Stacks.SheafOfModules.Tensor.tensorComplex Z.O).obj P).obj N)) ≫
          DerivedCategory.Q.map (pullbackTensorComplexIso (g.comp f)
            (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg) P N).hom =
        DerivedCategory.Q.map
            ((pullbackComplex f).map (pullbackTensorComplexIso g hmosg P N).hom) ≫
          DerivedCategory.Q.map (pullbackTensorComplexIso f hmosf
              ((pullbackComplex g).obj P) ((pullbackComplex g).obj N)).hom ≫
            DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
              (e.hom.app P) (e.hom.app N)
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
              (ComplexShape.up ℤ)))
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Z.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Z.O) (L.X i)) :
    (derivedPullbackCompIso f g hmosf hmosg).hom.app
          ((Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.O)).obj
            (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)) ≫
        (derivedPullbackTensorIso (g.comp f)
          (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg)).hom.app
            (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) =
      (derivedPullback f).map
          ((derivedPullbackTensorIso g hmosg).hom.app
            (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)) ≫
        (derivedPullbackTensorIso f hmosf).hom.app
            ((derivedPullback g).obj (DerivedCategory.Q.obj K),
              (derivedPullback g).obj (DerivedCategory.Q.obj L)) ≫
          (Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).map
            ((derivedPullbackCompIso f g hmosf hmosg).hom.app (DerivedCategory.Q.obj K) ×ₘ
              (derivedPullbackCompIso f g hmosf hmosg).hom.app (DerivedCategory.Q.obj L)) := by
  -- The assembled term is handed over through a `have` rather than written as the body: that
  -- computes its type from its arguments and then checks the two against each other once, where
  -- elaborating it against the goal unifies the two side by side and does not finish inside the
  -- heartbeat budget.  The three model identities are ascribed `: _` for the same reason one step
  -- down: each is elaborated on its own, its type being fully determined by `f`, `g`, `K`, `L`.
  have h := Stacks.Cohomology.DerivedPullbackTensor.tensorComparison_comp_of_models
    (derivedPullbackCompIso f g hmosf hmosg).hom
    (derivedPullbackTensorIso g hmosg).hom
    (derivedPullbackTensorIso f hmosf).hom
    (derivedPullbackTensorIso (g.comp f)
      (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg)).hom
    (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
    (mono_derivedTensorMap_pullbackComparisonQ (g.comp f)
      (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg) K L hK hL hflatK hflatL)
    (mono_toTensor_pullbackComplex (g.comp f)
      (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg) K L hK hL hflatK hflatL)
    (hcompQ K) (hcompQ L)
    (hcompQ (((Stacks.SheafOfModules.Tensor.tensorComplex Z.O).obj K).obj L))
    (pullbackComparisonQ_naturality f (pullbackTensorComplexIso g hmosg K L).hom)
    (toTensor_naturality_prod X (e.hom.app K) (e.hom.app L))
    ((toTensor_square_of_kFlat g hmosg K L hK hL hflatK hflatL).symm : _)
    ((toTensor_square_of_kFlat f hmosf ((pullbackComplex g).obj K) ((pullbackComplex g).obj L)
      (kFlat_pullbackComplex' g hmosg K hK hflatK)
      (kFlat_pullbackComplex' g hmosg L hL hflatL)
      (fun i => isFlat_pullbackComplex_X g hmosg
        (RingedToposSiteHom.pullbackPreservesIsFlat g) K hflatK i)
      (fun i => isFlat_pullbackComplex_X g hmosg
        (RingedToposSiteHom.pullbackPreservesIsFlat g) L hflatL i)).symm : _)
    ((toTensor_square_of_kFlat (g.comp f)
      (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg) K L hK hL
      hflatK hflatL).symm : _)
    (htotal K L)
  exact h

end Composite

end Stacks.Sheaves.DerivedPullback

end
