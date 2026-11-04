module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.KFlatComplexesDefinition
public import StacksFrontier.Homology.KFlat.BifunctorLocalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatTensorShortExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
import StacksCore.Tactic.StacksAttribute

/-!
# K-flatness in the two variables of the tensor product of `O`-modules

For a general bifunctor `F : A ⥤ B ⥤ D` the two K-flatness predicates
`CochainComplex.KFlatBifunctor.KFlat F` and `CochainComplex.KFlatBifunctor.KFlatLeft F`
constrain different arguments of `F` and are unrelated. For the tensor product `⊗_O` of
sheaves of modules on a ringed site they agree, because `⊗_O` is symmetric: a K-flat complex
is left K-flat.

## Main definitions

* `CochainComplex.KFlatBifunctor.mapBifunctorBicomplexIsoOfNatIso` and
  `mapBifunctorIsoOfNatIso`: an isomorphism of bifunctors induces an isomorphism of the
  bicomplexes, and hence of the total complexes, that they build from a pair of complexes.
* `Stacks.SheafOfModules.Tensor.sheafTensorFlipNatIso`: the symmetry of `⊗_O` as an isomorphism of
  bifunctors `⊗_O ≅ (⊗_O)ᶠˡᶦᵖ`.

## Main results

* `CochainComplex.KFlatBifunctor.kFlat_of_natIso`: K-flatness only depends on the bifunctor
  up to isomorphism.
* `Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat`: a K-flat complex of `O`-modules is left
  K-flat for
  `⊗_O`, so the one-sided results of `StacksTag06YUOneSided` and the generic comparison of
  `StacksTag06YUPieces`, whose hypothesis is left K-flatness, apply to the K-flat complexes
  of Stacks Tag 06YN.

## Implementation notes

Two steps, neither of which braids total complexes. First, K-flatness transports along an
isomorphism of bifunctors: the two bicomplexes `(i₁, i₂) ↦ F(K₁^{i₁}, K₂^{i₂})` and
`(i₁, i₂) ↦ F'(K₁^{i₁}, K₂^{i₂})` are isomorphic degreewise, with the two commutation
squares being the two naturalities of the isomorphism, and totalisation carries that to an
isomorphism of total complexes by `HomologicalComplex₂.total.mapIso`. No Koszul sign
appears: the signs live in the differentials of the total complex, which both sides compute
from the same complex shapes.

Second, `CochainComplex.KFlatBifunctor.kFlatLeft_iff_kFlat_flip` turns left K-flatness for
`⊗_O` into K-flatness for `(⊗_O)ᶠˡᶦᵖ`, and `Stacks.SheafOfModules.Tensor.sheafTensorFlipNatIso`
  compares
`(⊗_O)ᶠˡᶦᵖ` with `⊗_O`. That comparison is Mathlib's braiding of the symmetric monoidal
structure on `Mod(O)`, read through `SheafOfModules.sheafTensorNatIso` on both sides; its
value at a single module is `Stacks.SheafOfModules.FlatTensorShortExact.flipIso`, which is the same
  comparison used for
the base case of the left-hand K-flat resolutions.

The statement is given in the bifunctor spelling of K-flatness, which needs only
`HasWeakSheafify`, rather than in the spelling of Stacks Tag 06YN, which carries
`HasSheafify`. The two are definitionally equal by
  `Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor`,
so a hypothesis of the stronger spelling is accepted where this is used.

## References

* [Stacks Project, Tag 06YN](https://stacks.math.columbia.edu/tag/06YN)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

noncomputable section

namespace CochainComplex.KFlatBifunctor

section Congr

universe v v' v'' u u' u''

variable {A : Type u} {B : Type u'} {D : Type u''}
  [Category.{v} A] [Category.{v'} B] [Category.{v''} D]
  [HasZeroMorphisms A] [HasZeroMorphisms B] [Preadditive D]
  (F F' : A ⥤ B ⥤ D) [F.PreservesZeroMorphisms] [∀ X, (F.obj X).PreservesZeroMorphisms]
  [F'.PreservesZeroMorphisms] [∀ X, (F'.obj X).PreservesZeroMorphisms]

/-- An isomorphism of bifunctors induces an isomorphism of the bicomplexes they build from a
pair of complexes: degreewise it is the isomorphism itself, and the two commutation squares
are its naturality in the first and in the second variable. -/
def mapBifunctorBicomplexIsoOfNatIso (e : F ≅ F')
    (K₁ : CochainComplex A ℤ) (K₂ : CochainComplex B ℤ) :
    ((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K₁).obj K₂ ≅
      ((F'.mapBifunctorHomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K₁).obj K₂ :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i₁ ↦ HomologicalComplex.Hom.isoOfComponents
      (fun i₂ ↦ (e.app (K₁.X i₁)).app (K₂.X i₂))
      (fun i₂ i₂' _ ↦ ((e.hom.app (K₁.X i₁)).naturality (K₂.d i₂ i₂')).symm))
    (fun i₁ i₁' _ ↦ by
      ext i₂
      exact (NatTrans.congr_app (e.hom.naturality (K₁.d i₁ i₁')) (K₂.X i₂)).symm)

/-- **The total complex only depends on the bifunctor up to isomorphism.** -/
def mapBifunctorIsoOfNatIso (e : F ≅ F')
    (K₁ : CochainComplex A ℤ) (K₂ : CochainComplex B ℤ)
    [HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]
    [HomologicalComplex.HasMapBifunctor K₁ K₂ F' (ComplexShape.up ℤ)] :
    HomologicalComplex.mapBifunctor K₁ K₂ F (ComplexShape.up ℤ) ≅
      HomologicalComplex.mapBifunctor K₁ K₂ F' (ComplexShape.up ℤ) :=
  HomologicalComplex₂.total.mapIso
    (mapBifunctorBicomplexIsoOfNatIso F F' e K₁ K₂) (ComplexShape.up ℤ)

end Congr

section KFlatCongr

universe v v' v'' u u' u''

variable {A : Type u} {B : Type u'} {D : Type u''}
  [Category.{v} A] [Category.{v'} B] [Category.{v''} D]
  [Preadditive A] [Preadditive B] [Abelian D]
  (F F' : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [F'.Additive] [∀ X, (F'.obj X).Additive]
  [∀ (K₁ : CochainComplex A ℤ) (K₂ : CochainComplex B ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]
  [∀ (K₁ : CochainComplex A ℤ) (K₂ : CochainComplex B ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ F' (ComplexShape.up ℤ)]

/-- **K-flatness only depends on the bifunctor up to isomorphism.** -/
theorem kFlat_of_natIso (e : F ≅ F') {K : CochainComplex B ℤ} (hK : KFlat F K) :
    KFlat F' K :=
  fun G hG n ↦ (hK G hG n).of_iso (mapBifunctorIsoOfNatIso F F' e G K)

end KFlatCongr

end CochainComplex.KFlatBifunctor

universe u

namespace Stacks.SheafOfModules.Tensor

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (R : Sheaf J CommRingCat.{u})

attribute [local instance] Stacks.SheafOfModules.Tensor.ringSheafPresheafMonoidalCategory
  SheafOfModules.monoidalCategory _root_.SheafOfModules.monoidalCategory
  _root_.SheafOfModules.symmetricCategory

/-- **The tensor product of `O`-modules is symmetric**, as an isomorphism of bifunctors
`⊗_O ≅ (⊗_O)ᶠˡᶦᵖ`. It is Mathlib's braiding on `Mod(O)` conjugated by the comparison
`SheafOfModules.sheafTensorNatIso` of the monoidal structure's tensor product with `⊗_O`,
and its value at a module is `Stacks.SheafOfModules.FlatTensorShortExact.flipIso`. -/
def sheafTensorFlipNatIso :
    sheafTensor.{u, u, u, u, u} R ≅ (sheafTensor.{u, u, u, u, u} R).flip :=
  (SheafOfModules.sheafTensorNatIso R).symm ≪≫
    BraidedCategory.curriedBraidingNatIso (SheafOfModules.{u} (ringSheaf.{u, u, u} R)) ≪≫
      (flipFunctor _ _ _).mapIso (SheafOfModules.sheafTensorNatIso R)

/-- The symmetry of `⊗_O` at a single module is
  `Stacks.SheafOfModules.FlatTensorShortExact.flipIso`, the comparison
`ℱ ⊗_O - ≅ - ⊗_O ℱ` which carries the flatness criterion of Stacks Tag 03EU from one
variable to the other. -/
lemma sheafTensorFlipNatIso_app
    (M : SheafOfModules.{u} (ringSheaf.{u, u, u} R)) :
    (sheafTensorFlipNatIso R).app M = Stacks.SheafOfModules.FlatTensorShortExact.flipIso R M :=
  rfl

end Stacks.SheafOfModules.Tensor

namespace Stacks.DerivedTensor.RingedSite

universe v' u' w'

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{w'}] [J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (R : Sheaf J CommRingCat.{w'})
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} R).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', w'} R)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} R)
      (ComplexShape.up ℤ)]

/-- **A K-flat complex of `O`-modules is K-flat in the left variable of `⊗_O`.** The two
predicates constrain different arguments of the tensor bifunctor, and it is the symmetry
`Stacks.SheafOfModules.Tensor.sheafTensorBraiding` of `⊗_O` that identifies the conditions they
  impose:
left K-flatness for `⊗_O` is K-flatness for `(⊗_O)ᶠˡᶦᵖ`, and K-flatness is invariant under
an isomorphism of bifunctors.

The symmetry is read off `Stacks.SheafOfModules.Tensor.sheafTensorBraiding`, which braids the
sectionwise tensor product of *presheaves* of modules and carries that through sheafification,
rather than off `Stacks.SheafOfModules.Tensor.sheafTensorFlipNatIso` above, which is the
braiding of the monoidal closed structure on `Mod(O)` and so inherits Day reflection's
constraint that the module universe contain the site.  The two are the same isomorphism of
bifunctors where both are defined; only the first is available with the object, morphism and
module universes of the site independent, which is what lets this statement reach an
`AlgebraicGeometry.RingedTopos.{u, u + 1, u}`. -/
theorem kFlatLeft_of_kFlat
    {K : CochainComplex
      (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', w'} R)) ℤ}
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} R) K) :
    CochainComplex.KFlatBifunctor.KFlatLeft
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} R) K :=
  (CochainComplex.KFlatBifunctor.kFlatLeft_iff_kFlat_flip _ K).2
    (CochainComplex.KFlatBifunctor.kFlat_of_natIso _ _
      (Stacks.SheafOfModules.Tensor.sheafTensorBraiding R) hK)

end Stacks.DerivedTensor.RingedSite

end

end
