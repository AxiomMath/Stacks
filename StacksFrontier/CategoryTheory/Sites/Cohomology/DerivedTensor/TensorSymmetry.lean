module

public import StacksFrontier.CategoryTheory.Functor.Bifunctor
public import Mathlib.Algebra.Homology.BifunctorFlip
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import StacksFrontier.Algebra.Homology.MapBifunctorNatIso
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.Defs
import StacksCore.Tactic.StacksAttribute

/-!
# The tensor product of sheaves of modules is symmetric, and so is its total complex

Let `R` be a sheaf of commutative rings on a site `(C, J)`. The tensor product of sheaves of
`R`-modules is the sheafification of the sectionwise tensor product, and the sectionwise tensor
product is symmetric because the tensor product of modules over a commutative ring is. This
file carries that symmetry through the two constructions that build on it: the tensor
bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor` is isomorphic to its own flip, and
  consequently the
total tensor complex `Tot(K ⊗_R L)` is isomorphic to `Tot(L ⊗_R K)` — with the Koszul sign
`(-1)^{pq}` on the summand of bidegree `(p, q)`, which is the sign Mathlib's
`HomologicalComplex.mapBifunctorFlipIso` carries.

The consequence this is for is that K-flatness is a two-sided condition:
`Stacks.SheafOfModules.IsKFlat` says that `Tot(F ⊗_R K)` is acyclic for acyclic `F`, with the
K-flat complex in the *right* tensor slot, and
`Stacks.SheafOfModules.IsKFlat.acyclic_tensor_left` says that `Tot(K ⊗_R F)` is then acyclic
too. Every one-sided statement about tensoring with a K-flat complex therefore has its mirror
image, which is what the two one-sided comparison maps of the derived tensor product need.

## Main definitions

* `PresheafOfModules.tensorBifunctorBraiding`: the sectionwise tensor bifunctor of
  presheaves of
  modules is isomorphic to its flip.
* `Stacks.SheafOfModules.Tensor.sheafTensorBraiding`: the same for sheaves of modules.
* `Stacks.SheafOfModules.Tensor.tensorComplexFlipIso`: the Koszul symmetry
  `Tot(K ⊗_R L) ≅ Tot(L ⊗_R K)` of total tensor complexes.

## Main results

* `Stacks.SheafOfModules.IsKFlat.acyclic_tensor_left`: a K-flat complex tensors an acyclic
  complex to an acyclic complex on the left as well as on the right.

## Implementation notes

The braiding of presheaves of modules is Mathlib's `PresheafOfModules.symmetricCategory`,
whose equal-universe tensor agrees with the native `PresheafOfModules.tensorBifunctor`;
the isomorphism of bifunctors is `BraidedCategory.curriedBraidingNatIso`. Both the monoidal and
the braided instance have to be re-exhibited at the spelling
`PresheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf R).obj` rather than
`PresheafOfModules (R.obj ⋙ forget₂ CommRingCat RingCat)`, which is what
`presheafOfModulesMonoidal` and `presheafOfModulesBraided` do; they are the same instances,
found through the definitional equality of the two spellings of the ring presheaf, and they
are local instances to avoid installing duplicate global structures.

`sheafTensorBraiding` is then obtained by whiskering, since
  `Stacks.SheafOfModules.Tensor.sheafTensor` is
built from `PresheafOfModules.tensorBifunctor` by pre- and post-composition, which commute with
taking the flip of a bifunctor.

The symmetry of total complexes composes two steps: Mathlib's
`HomologicalComplex.mapBifunctorFlipIso`, which exchanges the two complexes at the cost of
replacing the bifunctor by its flip, and `HomologicalComplex.mapBifunctorNatIso`, which
transports along `sheafTensorBraiding` to get the bifunctor back. The existence of the total
complex for the flipped bifunctor is Mathlib's
`HomologicalComplex.hasMapBifunctor_flip_iff`, supplied here as an instance because instance
search otherwise unfolds `HasMapBifunctor` to a statement about coproducts and does not
recover it.

## References

* [Stacks Project, Tag 06Y9](https://stacks.math.columbia.edu/tag/06Y9)
* [Stacks Project, Tag 06YN](https://stacks.math.columbia.edu/tag/06YN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u v w

namespace Stacks.SheafOfModules.Tensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w})
  [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The monoidal structure on presheaves of modules over the ring presheaf of `R`, at the
spelling `(Stacks.SheafOfModules.Tensor.ringSheaf R).obj` of that ring presheaf. It is Mathlib's
  monoidal
structure on presheaves of modules over a presheaf of commutative rings, which is the one
`PresheafOfModules.tensorBifunctor` agrees with at equal module universes. -/
@[instance_reducible]
def presheafOfModulesMonoidal :
    MonoidalCategory (PresheafOfModules.{w} (ringSheaf.{u, v, w} R).obj) :=
  (inferInstance :
    MonoidalCategory (PresheafOfModules (R.obj ⋙ forget₂ CommRingCat RingCat)))

attribute [local instance] presheafOfModulesMonoidal

/-- The braiding of presheaves of modules over the ring presheaf of `R`: the tensor product of
modules over a commutative ring is symmetric, sectionwise. -/
@[instance_reducible]
def presheafOfModulesBraided :
    BraidedCategory (PresheafOfModules.{w} (ringSheaf.{u, v, w} R).obj) :=
  (inferInstance :
    BraidedCategory (PresheafOfModules (R.obj ⋙ forget₂ CommRingCat RingCat)))

attribute [local instance] presheafOfModulesBraided

/-- The sectionwise tensor bifunctor of presheaves of modules is isomorphic to its own flip,
by the braiding. -/
def presheafTensorBraiding :
    PresheafOfModules.tensorBifunctor.{v, u, w, w, w} R.obj ≅
      (PresheafOfModules.tensorBifunctor.{v, u, w, w, w} R.obj).flip :=
  BraidedCategory.curriedBraidingNatIso (PresheafOfModules (ringSheaf.{u, v, w} R).obj)

/-- The tensor bifunctor of sheaves of modules is isomorphic to its own flip. Sheafification
and the forgetful functor to presheaves are applied to both tensor factors alike, so the
braiding of the sectionwise tensor product survives them. -/
def sheafTensorBraiding :
    sheafTensor.{u, v, w, w, w} R ≅ (sheafTensor.{u, v, w, w, w} R).flip :=
  Functor.isoWhiskerLeft (SheafOfModules.forget (ringSheaf.{u, v, w} R))
    (Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (presheafTensorBraiding R)
        ((Functor.whiskeringRight _ _ _).obj (PresheafOfModules.sheafification.{w}
            (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
            (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj))))
      ((Functor.whiskeringLeft _ _ _).obj (SheafOfModules.forget (ringSheaf.{u, v, w} R))))

section

variable [HasBinaryBiproducts (SheafOfModules.{w} (ringSheaf.{u, v, w} R))]
  [(sheafTensor.{u, v, w, w, w} R).Additive]
  [∀ M, ((sheafTensor.{u, v, w, w, w} R).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{w} (ringSheaf.{u, v, w} R)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor R) (ComplexShape.up ℤ)]

/-- The flipped tensor bifunctor has the direct sums needed to form total complexes, since the
original one does and the summands are the same. -/
instance hasMapBifunctor_sheafTensor_flip
    (K L : CochainComplex (SheafOfModules.{w} (ringSheaf.{u, v, w} R)) ℤ) :
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, v, w, w, w} R).flip
      (ComplexShape.up ℤ) :=
  (HomologicalComplex.hasMapBifunctor_flip_iff L K (sheafTensor R) (ComplexShape.up ℤ)).mpr
    inferInstance

/-- The Koszul symmetry of the total tensor complex: `Tot(K ⊗_R L) ≅ Tot(L ⊗_R K)`, the
summand of bidegree `(p, q)` being carried to the summand of bidegree `(q, p)` by the
sectionwise symmetry times the sign `(-1)^{pq}`. -/
def tensorComplexFlipIso
    (K L : CochainComplex (SheafOfModules.{w} (ringSheaf.{u, v, w} R)) ℤ) :
    ((tensorComplex.{u, v, w} R).obj K).obj L ≅ ((tensorComplex.{u, v, w} R).obj L).obj K :=
  HomologicalComplex.mapBifunctorNatIso K L (ComplexShape.up ℤ) (sheafTensorBraiding R) ≪≫
    HomologicalComplex.mapBifunctorFlipIso L K (sheafTensor R) (ComplexShape.up ℤ)

end

end Stacks.SheafOfModules.Tensor

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w})
  [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} R)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

/-- K-flatness is a two-sided condition: if `K` is K-flat then `Tot(K ⊗_R F)` is acyclic for
every acyclic `F`, not only `Tot(F ⊗_R K)`. This is the symmetry of the tensor product of
sheaves of modules, carried to total complexes by
`Stacks.SheafOfModules.Tensor.tensorComplexFlipIso`. -/
theorem IsKFlat.acyclic_tensor_left
    {K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ}
    (hK : IsKFlat R K)
    (F : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (hF : F.Acyclic) :
    (((Stacks.SheafOfModules.Tensor.tensorComplex R).obj K).obj F).Acyclic :=
  fun i ↦ (hK F hF i).of_iso (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso R F K)

end Stacks.SheafOfModules

end
