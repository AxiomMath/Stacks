module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Pi.Basic
public import StacksFrontier.Homology.KFlat.FilteredColimitShifts
public import StacksFrontier.Homology.TorAmplitude.FlatResolution

/-!
# Flat representatives of a direct sum

Let `R` be a ring and let `(K_i)_{i ∈ I}` be a family of complexes of `R`-modules, each of which
is represented in `D(R)` by a complex of flat modules concentrated in degrees `[a, b]`. Then so
is their termwise direct sum `⊕ K_i`: if `K_i ≅ E_i` in `D(R)` with `E_i` flat in `[a, b]`, then
`⊕ E_i` is flat in `[a, b]`, being a termwise direct sum of flat modules, and `⊕ K_i ≅ ⊕ E_i`
in `D(R)` because the localization `C(R) ⥤ D(R)` preserves direct sums (Stacks 0A5L), so that
both sides are direct sums in `D(R)` of isomorphic families. By Stacks 0654 this says that Tor
amplitude in `[a, b]` is stable under arbitrary direct sums.

## Main results

* `StacksDraft.TorAmplitude.derivedCategoryQ_preservesCoproducts_moduleCat`: the localization
  `C(R) ⥤ D(R)` preserves direct sums indexed by the module universe.
* `StacksDraft.TorAmplitude.hasFlatRepresentative_of_isColimit_cofan`: a direct sum of complexes
  with flat representatives in `[a, b]` has a flat representative in `[a, b]`.
* `StacksDraft.TorAmplitude.hasFlatRepresentative_mapDerivedCategory_of_iso_sigma`: the same for
  an exact functor which is a direct sum of exact functors `G_i`, read on the derived category.

## Implementation notes

The ring universe `u` and the module universe `max u v` are independent, as for
`StacksDraft.TorAmplitude.HasFlatRepresentative`, and the index type lives in the module
universe. The direct sum is given as an arbitrary colimit cofan rather than as `∐`, so that a
consumer may use whichever presentation of the direct sum it has to hand.

## References

* [Stacks Project, Tag 0654](https://stacks.math.columbia.edu/tag/0654)
* [Stacks Project, Tag 0A5L](https://stacks.math.columbia.edu/tag/0A5L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace StacksDraft.TorAmplitude

universe u v

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 0A5L for modules.** The localization functor `Q : C(R) ⥤ D(R)` preserves direct
sums indexed by any type of the module universe: direct sums of modules are exact. -/
theorem derivedCategoryQ_preservesCoproducts_moduleCat (R : Type u) [Ring R]
    (ι : Type (max u v)) :
    PreservesColimitsOfShape (Discrete ι) (DerivedCategory.Q (C := ModuleCat.{max u v} R)) := by
  apply CochainComplex.KFlat.CoproductBridge.derivedCategory_Q_preservesCoproductsOfShape
  refine ⟨inferInstance, fun J => ?_⟩
  have : HasExactColimitsOfShape (Discrete J) (ModuleCat.{max u v} R) :=
    HasExactColimitsOfShape.domain_of_functor (Discrete J)
      (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})
  exact ⟨inferInstance, inferInstance⟩

/-- A direct sum of zero objects is zero. -/
lemma isZero_sigma_of_isZero {C : Type*} [Category C] [HasZeroMorphisms C] {ι : Type*}
    (f : ι → C) [HasCoproduct f] (h : ∀ i, IsZero (f i)) : IsZero (∐ f) :=
  (IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ fun i => (h i).eq_of_src _ _)

/-- **A direct sum of complexes with flat representatives in `[a, b]` has a flat representative
in `[a, b]`.** Equivalently, by Stacks 0654, Tor amplitude in `[a, b]` is stable under arbitrary
direct sums. The direct sum is any colimit cofan `c` of the family. -/
theorem hasFlatRepresentative_of_isColimit_cofan {R : Type u} [CommRing R] {ι : Type (max u v)}
    {K : ι → CochainComplex (ModuleCat.{max u v} R) ℤ} (c : Cofan K) (hc : IsColimit c)
    {a b : ℤ} (h : ∀ i, HasFlatRepresentative.{u, v} (DerivedCategory.Q.obj (K i)) a b) :
    HasFlatRepresentative.{u, v} (DerivedCategory.Q.obj c.pt) a b := by
  classical
  choose E hflat hGE hLE e using h
  have := derivedCategoryQ_preservesCoproducts_moduleCat.{u, v} R ι
  let eX (n : ℤ) := PreservesCoproduct.iso (HomologicalComplex.eval _ _ n) E
  refine ⟨∐ E, fun n => ?_, ?_, ?_, ?_⟩
  · have : ∀ j, Module.Flat R ((E j).X n) := fun j => hflat j n
    exact Module.Flat.of_linearEquiv
      (eX n ≪≫ ModuleCat.coprodIsoDirectSum fun j => (E j).X n).toLinearEquiv
  · rw [CochainComplex.isStrictlyGE_iff]
    exact fun n hn =>
      (isZero_sigma_of_isZero _ fun j => (E j).isZero_of_isStrictlyGE a n hn).of_iso (eX n)
  · rw [CochainComplex.isStrictlyLE_iff]
    exact fun n hn =>
      (isZero_sigma_of_isZero _ fun j => (E j).isZero_of_isStrictlyLE b n hn).of_iso (eX n)
  · exact ⟨IsColimit.coconePointsIsoOfNatIso (isColimitOfPreserves DerivedCategory.Q hc)
      (isColimitOfPreserves DerivedCategory.Q (colimit.isColimit (Discrete.functor E)))
      (Discrete.natIso fun j => (e j.as).some)⟩

/-- **Flat representatives through a direct sum of exact functors.** Let `S` be an exact functor
from an abelian category to `R`-modules which is the direct sum of a family of exact functors
`G_i`. If each `G_i` carries an object `K` of the derived category to an object with a flat
representative in `[a, b]`, then so does `S`.

Represent `K` by a complex `L`; then `S` applied to `L` is, termwise, the direct sum of the `G_i`
applied to `L`, so it is a direct sum of complexes, and
`StacksDraft.TorAmplitude.hasFlatRepresentative_of_isColimit_cofan` applies. -/
theorem hasFlatRepresentative_mapDerivedCategory_of_iso_sigma
    {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]
    {R : Type u} [CommRing R] {ι : Type (max u v)}
    (G : ι → 𝒜 ⥤ ModuleCat.{max u v} R) [hGa : ∀ i, (G i).Additive]
    [hGl : ∀ i, PreservesFiniteLimits (G i)] [hGc : ∀ i, PreservesFiniteColimits (G i)]
    (S : 𝒜 ⥤ ModuleCat.{max u v} R) [hSa : S.Additive] [hSl : PreservesFiniteLimits S]
    [hSc : PreservesFiniteColimits S] (eS : S ≅ Functor.pi' G ⋙ Sigma.functor ι)
    (K : DerivedCategory 𝒜) {a b : ℤ}
    (h : ∀ i, HasFlatRepresentative.{u, v} ((G i).mapDerivedCategory.obj K) a b) :
    HasFlatRepresentative.{u, v} (S.mapDerivedCategory.obj K) a b := by
  let L := DerivedCategory.Q.objPreimage K
  let eL : DerivedCategory.Q.obj L ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let C : ι → CochainComplex (ModuleCat.{max u v} R) ℤ :=
    fun i => ((G i).mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  let P := (S.mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  let τ : ∀ i, G i ⟶ S := fun i =>
    (Functor.pi'CompEval G i).inv ≫ Functor.whiskerLeft (Functor.pi' G) (Sigma.functorι i) ≫
      eS.inv
  have hτ : ∀ X : 𝒜, IsColimit (Cofan.mk (S.obj X) fun i => (τ i).app X) := fun X =>
    IsColimit.ofIsoColimit (coproductIsCoproduct ((Functor.pi' G).obj X))
      (Cofan.ext (eS.app X).symm fun i => by
        change _ = 𝟙 _ ≫ Sigma.ι ((Functor.pi' G).obj X) i ≫ eS.inv.app X
        rw [Category.id_comp]
        rfl)
  let ιP : ∀ i, C i ⟶ P := fun i =>
    { f := fun n => (τ i).app (L.X n)
      comm' := fun n m _ => ((τ i).naturality (L.d n m)).symm }
  have hc : IsColimit (Cofan.mk P ιP) :=
    HomologicalComplex.isColimitOfEval _ _ fun n =>
      (isColimitMapCoconeCofanMkEquiv (HomologicalComplex.eval _ _ n) C ιP).symm (hτ (L.X n))
  exact hasFlatRepresentative_of_iso
    ((S.mapDerivedCategoryFactors.app L).symm ≪≫ S.mapDerivedCategory.mapIso eL)
    (hasFlatRepresentative_of_isColimit_cofan (Cofan.mk P ιP) hc fun i =>
      hasFlatRepresentative_of_iso
        ((G i).mapDerivedCategory.mapIso eL.symm ≪≫ (G i).mapDerivedCategoryFactors.app L)
        (h i))

end StacksDraft.TorAmplitude
