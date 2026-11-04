module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoverTensorExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Flat covers and flatness of colimits, with the module universe free of the site

Let `(C, J)` be a site and `O` a sheaf of commutative rings on it, with the universe of the
sections of `O` independent of the two universes of the site. This file collects the flatness
facts about `O`-modules that hold in that generality: flatness read against the tensor
bifunctor of Stacks 06YM, invariance under isomorphism, flatness of a colimit of flat modules
along a small shape with exact colimits, flatness of the zero module and of a binary
biproduct, and the flat cover of Stacks 03EW (3) at the spelling
`Stacks.SheafOfModules.Tensor.ringSheaf` of the structure sheaf.

## Main results

* `Stacks.SheafOfModules.FlatCoproduct.isFlat_iff_exactFunctor_sheafTensor_ofSize`,
  `isFlat_of_iso_ofSize`, `isFlat_colimit_ofSize`,
  `isFlat_biprod_ofSize`, `containsZero_isFlat_ofSize`.
* `Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat_ofSize`: every sheaf of modules
  receives an epimorphism from a flat one, stated over `Tensor.ringSheaf`.

## Implementation notes

Each declaration generalises the sibling of the same name without the `OfSize` suffix:
`Stacks.SheafOfModules.FlatCoproduct.isFlat_iff_exactFunctor_sheafTensor` and
`isFlat_colimit` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FlatCoproduct.lean`,
`Stacks.DerivedTensor.FlatTransport.IsFlat.of_iso`,
`Stacks.SheafOfModules.FlatCoproduct.isFlat_biprod` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/DerivedPullbackOfRingedTopoi.lean`,
and `Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat`. The siblings fix the module
universe to `max u v`, or to `u` on a small site, because the colimit preservation of `⊗_O`
they rest on is read off the monoidal closed structure of `Mod(O)`, which Day's reflection
theorem supplies only where the internal hom of presheaves of modules lands in the module
universe. Here that colimit preservation is read off
`Stacks.SheafOfModules.preservesColimits_sheafTensorObj` instead, which is Stacks 05NB with
the section universe independent of the site.

The surviving universe relation is module universe = ring universe, with the object and
morphism universes of the site free. It is forced: the flat cover is the sheafification of the
free presheaf of modules on the presheaf of sets of sections, and a free module on a set in
`Type z` over a ring in `Type w` has carrier in `Type (max w z)`.

Only shapes in `Type 0` are treated, which covers a sequential colimit and the finite shapes
behind the zero object and the binary biproduct.
Mathlib's finite-biproduct instances then supply exactness of the finite shapes with no size
hypothesis, so no analogue of `FlatCoproduct.hasExactColimitsOfShape_discrete` is needed.

## References

* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 03EU](https://stacks.math.columbia.edu/tag/03EU)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u w

namespace Stacks.SheafOfModules.FlatCoproduct

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Flatness of a sheaf of modules, restated for `Stacks.SheafOfModules.Tensor.sheafTensor`
with the module universe independent of the site. -/
lemma isFlat_iff_exactFunctor_sheafTensor_ofSize (O : Sheaf J CommRingCat.{w})
    (F : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := O) F ↔
      exactFunctor (_root_.SheafOfModules.{w} (Tensor.ringSheaf O)) _
        ((Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj F) :=
  Iff.rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Flatness of a sheaf of modules is invariant under isomorphism. -/
lemma isFlat_of_iso_ofSize (O : Sheaf J CommRingCat.{w})
    {M N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (e : M ≅ N)
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := O) M) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := O) N := by
  rw [isFlat_iff_exactFunctor_sheafTensor_ofSize] at hM ⊢
  exact (exactFunctor _ _).prop_of_iso
    ((Tensor.sheafTensor.{u, v, w, w, w} O).flip.mapIso e) hM

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `· ⊗_O ·`, read as a functor of its right-hand argument into endofunctors of `Mod(O)`,
preserves colimits of any shape in `Type 0`: colimits in a functor category are pointwise, and
pointwise this is Stacks 05NB. -/
lemma preservesColimitsOfShape_sheafTensor_flip_ofSize (O : Sheaf J CommRingCat.{w})
    (K : Type) [SmallCategory K] :
    PreservesColimitsOfShape K
      (Tensor.sheafTensor.{u, v, w, w, w} O).flip :=
  preservesColimitsOfShape_of_evaluation _ K fun G ↦ by
    have : PreservesColimitsOfSize.{w, w} ((Tensor.sheafTensor.{u, v, w, w, w} O).obj G) :=
      Stacks.SheafOfModules.preservesColimits_sheafTensorObj O G
    have : PreservesColimitsOfSize.{0, 0} ((Tensor.sheafTensor.{u, v, w, w, w} O).obj G) :=
      preservesSmallestColimits_of_preservesColimits _
    rw [flip_comp_evaluation]
    exact this.preservesColimitsOfShape

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **A colimit of flat sheaves of modules along a shape in `Type 0` whose colimits are exact
is flat**, which is Stacks 03EU with the module universe independent of the site. -/
theorem isFlat_colimit_ofSize (O : Sheaf J CommRingCat.{w}) {I : Type} [SmallCategory I]
    [HasColimitsOfShape I (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
    [HasExactColimitsOfShape I
      (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
    (F : I ⥤ _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hF : ∀ i, AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := O) (F.obj i)) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := O) (colimit F) := by
  let := preservesColimitsOfShape_sheafTensor_flip_ofSize O I
  have hcol := exactFunctor_colimit (F ⋙ (Tensor.sheafTensor.{u, v, w, w, w} O).flip)
    fun i ↦ (isFlat_iff_exactFunctor_sheafTensor_ofSize O (F.obj i)).1 (hF i)
  have preservation : PreservesColimit (F : I ⥤ _root_.SheafOfModules.{w} (Tensor.ringSheaf O))
      (Tensor.sheafTensor.{u, v, w, w, w} O).flip :=
    (preservesColimitsOfShape_sheafTensor_flip_ofSize O I).preservesColimit
  have comparison := @preservesColimitIso _ _ _ _
    (Tensor.sheafTensor.{u, v, w, w, w} O).flip I _ F preservation
    (inferInstance : HasColimit F)
  rw [isFlat_iff_exactFunctor_sheafTensor_ofSize]
  exact (exactFunctor _ _).prop_of_iso comparison.symm hcol

/-- A colimit of flat sheaves of modules over a finite discrete shape is flat. -/
private theorem isFlat_of_isColimit_discrete_ofSize {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify J AddCommGrpCat.{w}] (O : Sheaf J CommRingCat.{w}) {ι : Type} [Finite ι]
    {F : Discrete ι ⥤ _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (hF : ∀ i, AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := O) (F.obj i))
    {c : Cocone F} (hc : IsColimit c) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := O) c.pt := by
  let : Abelian (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
    AlgebraicGeometry.SheafOfModules.instAbelianSheafOfModules _
  let : HasFiniteBiproducts
      (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have : Fintype ι := Fintype.ofFinite ι
  exact isFlat_of_iso_ofSize O (hc.coconePointUniqueUpToIso (colimit.isColimit F)).symm
    (isFlat_colimit_ofSize O F hF)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **A binary biproduct of flat sheaves of modules is flat**, being their coproduct. -/
theorem isFlat_biprod_ofSize (O : Sheaf J CommRingCat.{w})
    (M N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := O) M)
    (hN : AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := O) N) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := O) (M ⊞ N) := by
  have hpair : ∀ i : Discrete WalkingPair,
      AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := O) ((pair M N).obj i) := by
    rintro ⟨j⟩
    cases j
    exacts [hM, hN]
  have := isFlat_of_isColimit_discrete_ofSize O hpair (BinaryBiproduct.isColimit M N)
  exact this

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Flatness of sheaves of modules, as a property of objects of `Mod(O)`, holds of a zero
object, namely of the direct sum of the empty family. -/
theorem containsZero_isFlat_ofSize (O : Sheaf J CommRingCat.{w}) :
    ObjectProperty.ContainsZero
      ((fun F ↦ AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := O) F) :
        ObjectProperty (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))) := by
  exact ⟨_, initialIsInitial.isZero,
    isFlat_of_isColimit_discrete_ofSize O (c := asEmptyCocone (⊥_ _)) (fun i ↦ i.as.elim)
      initialIsInitial⟩

end Stacks.SheafOfModules.FlatCoproduct

namespace Stacks.SheafOfModules.FlatCover


attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **Stacks 03EW (3) over `Stacks.SheafOfModules.Tensor.ringSheaf`.** Every sheaf of modules
receives an epimorphism from a flat sheaf of modules, with the module universe equal to the
ring universe and the two site universes free. -/
theorem exists_epi_from_isFlat_ofSize (R : Sheaf J CommRingCat.{w})
    (M : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} R)) :
    ∃ (N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} R))
      (p : N ⟶ M), AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) N ∧ Epi p :=
  exists_epi_from_isFlat R M

end Stacks.SheafOfModules.FlatCover

end
