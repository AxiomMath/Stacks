module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorUnitSections
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.Defs
public import StacksFrontier.Homology.KFlat.BifunctorSingleSecondFactor
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove

/-! # Tensoring with the structure sheaf, with the module universe free of the site

Let `(C, O)` be a ringed site. `StacksFrontier/CategoryTheory/Sites/Modules/TensorUnit.lean` records
the unit law
`F ⊗_O O ≅ F` of Stacks 06YM and the three consequences a derived-category client needs, but
only for a structure sheaf whose sections lie in `max u v`, `u` and `v` being the object and
morphism universes of the site: it reads the unitor off the re-seated monoidal structure of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/MonoidalSheafTensor.lean`, which exists only
there.

This file proves the same four statements with the module universe independent of the site.
Nothing about the site changes; what changes is the source of the unitor. The isomorphism
`F ⊗_O O ≅ F` is `Stacks.SheafOfModules.tensorSheafUnitRightIso`, the presheaf right unitor
carried through sheafification, which is available at a free module universe; its naturality
in `F` — the one thing that file does not record, the unitor being built one object at a time
there — is `Stacks.SheafOfModules.tensorSheafUnitRightIso_naturality` below.

## Main definitions

* `Stacks.SheafOfModules.sheafTensorUnitNatIsoOfSize`: `- ⊗_O O ≅ 𝟭`, read off the bifunctor
  `Stacks.SheafOfModules.Tensor.sheafTensor`.
* `Stacks.SheafOfModules.rowComplexUnitIsoOfSize`: the termwise complex `p ↦ K^p ⊗_O O` is `K`.
* `Stacks.SheafOfModules.tensorComplexUnitIsoOfSize`: `Tot(K ⊗_O O[0]) ≅ K`.

## Main results

* `Stacks.SheafOfModules.tensorSheafUnitRightIso_naturality`: the right unitor is natural.
* `Stacks.SheafOfModules.isKFlat_single_unit_ofSize`: the structure sheaf placed in degree zero
  is a K-flat complex.

## Implementation notes

Each declaration generalises the sibling of the same name without the `OfSize` suffix in
`StacksFrontier/CategoryTheory/Sites/Modules/TensorUnit.lean`, whose consumers identify
`sheafTensorUnitNatIso` with the
right unitor of the re-seated monoidal structure and so cannot be served by the generalisation;
the two are kept side by side for that reason.

Naturality is proved in term form rather than by `rw`. The two spellings of the sheaf of rings
in play, `Stacks.SheafOfModules.ringSheaf R.obj h` and
`Stacks.SheafOfModules.TensorSheafification.structureSheaf R.obj h`, are definitionally equal
but the second is a plain `def`, so a rewrite whose motive mentions both fails the
type-correctness check at `implicit` transparency; `congrArg` has no motive to check.

## References

* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w v u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w})
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The sheaf condition on the underlying presheaf of rings of `O`, in the shape the right
unitor of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorUnitSections.lean` asks for. -/
abbrev structureRingIsSheaf : Presheaf.IsSheaf J
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf R.obj) :=
  ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).property

/-- **The right unitor `F ⊗_O O ≅ F` is natural in `F`.** Tensoring a morphism with the
identity of the structure sheaf and then applying the unitor is applying the unitor and then
the morphism: on underlying presheaves this is naturality of the presheaf right unitor, and
sheafification carries it, the identification of a sheafified sheaf of modules with itself
being the counit of the sheafification adjunction. -/
lemma tensorSheafUnitRightIso_naturality
    {A B : _root_.SheafOfModules.{w} (Tensor.ringSheaf R)} (g : A ⟶ B) :
    ((Tensor.sheafTensor.{u, v, w} R).map g).app
          (_root_.SheafOfModules.unit (Tensor.ringSheaf R)) ≫
        (tensorSheafUnitRightIso R.obj (structureRingIsSheaf R) B).hom =
      (tensorSheafUnitRightIso R.obj (structureRingIsSheaf R) A).hom ≫ g := by
  set F := sheafifyFunctor R.obj (structureRingIsSheaf R)
  have hc : F.map g.val ≫ (sheafifyValIso R.obj (structureRingIsSheaf R) B).hom =
      (sheafifyValIso R.obj (structureRingIsSheaf R) A).hom ≫ g :=
    (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction R.obj
      (structureRingIsSheaf R)).counit.naturality g
  have h : F.map (g.val ▷ (_root_.SheafOfModules.unit (Tensor.ringSheaf R)).val) ≫
      F.map (ρ_ B.val).hom = F.map (ρ_ A.val).hom ≫ F.map g.val :=
    (F.map_comp _ _).symm.trans
      ((congrArg F.map (MonoidalCategory.rightUnitor_naturality g.val)).trans (F.map_comp _ _))
  change F.map (g.val ▷ (_root_.SheafOfModules.unit (Tensor.ringSheaf R)).val) ≫
      (F.map (ρ_ B.val).hom ≫ (sheafifyValIso R.obj (structureRingIsSheaf R) B).hom) =
    (F.map (ρ_ A.val).hom ≫ (sheafifyValIso R.obj (structureRingIsSheaf R) A).hom) ≫ g
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hc).trans (Category.assoc _ _ _).symm)))

/-- **The structure sheaf is the unit of `⊗_O`:** `F ⊗_O O ≅ F`, naturally in the sheaf of
modules `F`, with the module universe independent of the site. -/
def sheafTensorUnitNatIsoOfSize :
    (Tensor.sheafTensor.{u, v, w} R).flip.obj
        (_root_.SheafOfModules.unit (Tensor.ringSheaf.{u, v, w} R)) ≅
      𝟭 (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u, v, w} R)) :=
  NatIso.ofComponents (fun A => tensorSheafUnitRightIso R.obj (structureRingIsSheaf R) A)
    (fun g => tensorSheafUnitRightIso_naturality R g)

variable [(Tensor.sheafTensor.{u, v, w} R).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, v, w} R).obj M).Additive]
  [∀ (K L : CochainComplex (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u, v, w} R)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Tensor.sheafTensor.{u, v, w} R) (ComplexShape.up ℤ)]

open CochainComplex.KFlatBifunctor in
/-- The termwise complex `p ↦ K^p ⊗_O O` is `K`. -/
def rowComplexUnitIsoOfSize
    (K : CochainComplex (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u, v, w} R)) ℤ) :
    rowComplex (Tensor.sheafTensor.{u, v, w} R) K
      (_root_.SheafOfModules.unit (Tensor.ringSheaf.{u, v, w} R)) ≅ K :=
  (NatIso.mapHomologicalComplex (sheafTensorUnitNatIsoOfSize R) (ComplexShape.up ℤ)).app K ≪≫
    (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).app K

open CochainComplex.KFlatBifunctor in
/-- **The structure sheaf placed in degree zero is a K-flat complex**, with the module universe
independent of the site. -/
theorem isKFlat_single_unit_ofSize :
    IsKFlat R ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (_root_.SheafOfModules.unit (Tensor.ringSheaf.{u, v, w} R))) :=
  kFlat_single_of_exact (Tensor.sheafTensor.{u, v, w} R) _ 0
    (fun G hG n => HomologicalComplex.ExactAt.of_iso (hG n) (rowComplexUnitIsoOfSize R G).symm)

/-- **The total tensor complex of `K` with the structure sheaf in degree zero is `K`**, with
the module universe independent of the site. -/
def tensorComplexUnitIsoOfSize
    (K : CochainComplex (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u, v, w} R)) ℤ) :
    ((Tensor.tensorComplex.{u, v, w} R).obj K).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          (_root_.SheafOfModules.unit (Tensor.ringSheaf.{u, v, w} R))) ≅ K :=
  CochainComplex.KFlatBifunctor.totalSingleIso (Tensor.sheafTensor.{u, v, w} R) K
      (_root_.SheafOfModules.unit (Tensor.ringSheaf.{u, v, w} R)) ≪≫
    rowComplexUnitIsoOfSize R K

end Stacks.SheafOfModules

end
