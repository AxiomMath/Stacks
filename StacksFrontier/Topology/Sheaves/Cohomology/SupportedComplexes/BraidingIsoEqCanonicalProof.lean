module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.KoszulBraidingFlipIso
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ForgetSupportCupProductSquare

/-!
# The two spellings of the commutativity constraint of [Stacks, Tag 0FPT] agree

`Stacks.Cohomology.SupportedComplexes.BraidingIsoEqCanonical` is the equation

`canonicalBraidingHom W.sheaf A B = ((canonicalDerivedTensorProduct W.sheaf).braidingIso
  (AlgebraicGeometry.RingedSpace.ringedSite W) A B).hom`

between the braiding of the re-seated symmetric monoidal derived category of
[Stacks, Tag 0FPT] and the isomorphism obtained by descending the Koszul symmetry of complexes
through the K-flat comparisons of [Stacks, Tag 06YU], for every ringed space.  It is the first of
the two equations that `ForgetSupportCupProductSquare.lean` reduces the square of
[Stacks, Tag 0G77] to.

## Main results

* `Stacks.Cohomology.SupportedComplexes.braidingIso_eq_canonicalBraidingHom_of_kFlat`: the
  identification at the classes of a pair of K-flat complexes.
* `Stacks.Cohomology.SupportedComplexes.braidingIsoEqCanonical`: **the identification for
  arbitrary objects of `D(𝒪_W)`**, i.e. `BraidingIsoEqCanonical W` for every `W`, with no
  flatness, finiteness or quasi-coherence hypothesis.
* `Stacks.Cohomology.SupportedComplexes.shiftedUnitCorepresentingCompatible_of_transposeClean`
  and `Stacks.Cohomology.SupportedComplexes.forgetSupportSquare_of_transposeClean`: the
  two consequences, namely `shiftedUnitCorepresentingCompatible_of_clean` and
  `forgetSupportSquare_of_clean` with both `BraidingIsoEqCanonical` hypotheses discharged.  The
  square of Tag 0G77 now rests on the single hypothesis
  `Stacks.Cohomology.SupportedComplexes.ShiftedUnitTransposeClean`.

## Implementation notes

**Where the content is.**  Not here.  At a pair of K-flat complexes both sides read the *same*
K-flat comparison of Tag 06YU — `canonicalBraidingHom` by
`Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison_braiding`, and `braidingIso` by
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingIso_hom_eq` together with
`braidingTrans_app_app` — so the two differ exactly by one complex-level equation, between the
Koszul braiding of `Comp(Mod(𝒪_W))` and
`Stacks.SheafOfModules.Tensor.tensorComplexFlipIso`.  That equation is
`Stacks.SheafOfModules.Tensor.koszulBraiding_eq_tensorComplexFlipIso`, and it rests in turn on
`SheafOfModules.braiding_eq_sheafTensorBraiding`.  Both are proved in the two modules this one
imports; what is done here is the cancellation of the comparison off both sides and the descent
from K-flat representatives to all of `D(𝒪_W) × D(𝒪_W)`.

**Why the two spellings are not equal by `rfl`.**  `complexBraidingHom R K L` and
`DerivedCategory.Q.map (tensorComplexFlipIso R K L).hom` are morphisms of the same hom-set but
not definitionally equal — the kernel reports `Not a definitional equality` with the note that
`getColimitCocone` is not exposed.  The equation really is a theorem about the Koszul signs.

**The descent.**  Both sides are natural transformations
`- ⊗^𝐋 - ⟶ (- ⊗^𝐋 -) ∘ swap` — the left-hand one is
`Stacks.Cohomology.DerivedPullbackTensor.canonicalBraidingNatTrans`, the right-hand one is
`braidingIsoNatTrans` below, whose naturality is
`DerivedTensorProduct.braidingIso_hom_naturality` — and `D(𝒪_W)` is the localization of the
K-flat complexes at the quasi-isomorphisms (Tag 06YS), so they agree as soon as they agree at a
pair of K-flat representatives
(`Stacks.Cohomology.DerivedPullbackTensor.natTrans_ext_of_kFlat`).

**No tag attribute is attached to anything here.**  Every declaration below is an input to the
proof of Tag 0G77 — the identification of two spellings of one constraint — and not a clause of
any tag's statement.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Lemma 20.34.11 (Tag 0G77)](https://stacks.math.columbia.edu/tag/0G77)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.DerivedTensor.RingedSite
open Stacks.SheafOfModules.DerivedMonoidal
open scoped CategoryTheory.Prod

universe u

namespace CategoryTheory

/-- Two morphisms `B`, `A` into a common object agree when postcomposing with an isomorphism
`c₂` takes both to `c₁ ≫ w`, the second one being presented as the conjugate
`c₁ ≫ w ≫ c₂.inv`. -/
theorem eq_of_comp_iso_eq_of_conj {E : Type*} [Category E] {t₁ t₂ s₁ s₂ : E}
    (B A : t₁ ⟶ t₂) (c₁ : t₁ ⟶ s₁) (c₂ : t₂ ≅ s₂) (w : s₁ ⟶ s₂)
    (h₁ : B ≫ c₂.hom = c₁ ≫ w) (h₂ : A = c₁ ≫ w ≫ c₂.inv) : B = A := by
  refine (cancel_mono c₂.hom).1 ?_
  rw [h₁, h₂]
  simp

end CategoryTheory

namespace Stacks.Cohomology.SupportedComplexes

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] Stacks.Cohomology.DerivedPullbackTensor.abelianModulesSheafTensor
  Stacks.Cohomology.DerivedPullbackTensor.monoidalModules
  Stacks.Cohomology.DerivedPullbackTensor.symmetricModules
  Stacks.Cohomology.DerivedPullbackTensor.monoidalPreadditiveModules
  Stacks.Cohomology.DerivedPullbackTensor.monoidalClosedModules
  Stacks.Cohomology.DerivedPullbackTensor.hasTensorModules
  Stacks.Cohomology.DerivedPullbackTensor.monoidalComplexes
  CochainComplex.symmetricCategory

attribute [local implicit_reducible] structureSheafRing

section Space

variable (W : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The two spellings of the commutativity constraint of [Stacks, Tag 0FPT] agree at the
classes of a pair of K-flat complexes.**

Both sides become the same morphism after the K-flat comparison of [Stacks, Tag 06YU] at the
exchanged pair is composed onto them: the left-hand side by
`Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison_braiding`, the right-hand side
because `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingIso_hom_eq` and
`braidingTrans_app_app` present it as that comparison, the symmetry of total tensor complexes,
and the inverse of the comparison of the exchanged pair.  The two symmetries of complexes
appearing are identified by
`Stacks.SheafOfModules.Tensor.koszulBraiding_eq_tensorComplexFlipIso`. -/
theorem braidingIso_eq_canonicalBraidingHom_of_kFlat
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules W) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat W K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat W L) :
    canonicalBraidingHom W.sheaf (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) =
      ((canonicalDerivedTensorProduct W.sheaf).braidingIso
        (AlgebraicGeometry.RingedSpace.ringedSite W) (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj L)).hom := by
  have hw : complexBraidingHom W.sheaf K L =
      DerivedCategory.Q.map
        (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso W.sheaf K L).hom :=
    (complexBraidingHom_eq W.sheaf K L).trans
      (congrArg DerivedCategory.Q.map
        (Stacks.SheafOfModules.Tensor.koszulBraiding_eq_tensorComplexFlipIso W.sheaf K L))
  refine eq_of_comp_iso_eq_of_conj _ _
    ((canonicalDerivedTensorProduct W.sheaf).comparison K L hK hL).hom
    ((canonicalDerivedTensorProduct W.sheaf).comparison L K hL hK)
    (DerivedCategory.Q.map
      (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso W.sheaf K L).hom)
    ((canonicalComparison_braiding W.sheaf K L hK hL).trans
      (congrArg (fun z => canonicalComparisonHom W.sheaf K L hK hL ≫ z) hw))
    ((DerivedTensorProduct.braidingIso_hom_eq (AlgebraicGeometry.RingedSpace.ringedSite W)
          (canonicalDerivedTensorProduct W.sheaf) _ _).trans
      (DerivedTensorProduct.braidingTrans_app_app
        (AlgebraicGeometry.RingedSpace.ringedSite W)
        (canonicalDerivedTensorProduct W.sheaf) K L hK hL))

/-- The naturality of
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingIso` in the pair of variables,
with the bifunctor written uncurried — the shape a natural transformation out of
`Functor.uncurry.obj` needs, and the counterpart of
`Stacks.Cohomology.DerivedPullbackTensor.canonicalBraidingHom_naturality`. -/
theorem braidingIsoHom_naturality
    {G G' H H' : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules W)}
    (u : G ⟶ H) (v : G' ⟶ H') :
    (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).map (u ×ₘ v) ≫
        ((canonicalDerivedTensorProduct W.sheaf).braidingIso
          (AlgebraicGeometry.RingedSpace.ringedSite W) H H').hom =
      ((canonicalDerivedTensorProduct W.sheaf).braidingIso
          (AlgebraicGeometry.RingedSpace.ringedSite W) G G').hom ≫
        (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).map (v ×ₘ u) := by
  simpa only [Functor.uncurry_obj_map, Category.assoc] using
    DerivedTensorProduct.braidingIso_hom_naturality
      (AlgebraicGeometry.RingedSpace.ringedSite W)
      (canonicalDerivedTensorProduct W.sheaf) u v

/-- **The commutativity constraint of a derived tensor product, as a natural transformation** of
the uncurried derived tensor bifunctor into its composite with the swap of the two factors.  Its
components are `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingIso` and its
naturality is `braidingIsoHom_naturality`; this is the `braidingIso` counterpart of
`Stacks.Cohomology.DerivedPullbackTensor.canonicalBraidingNatTrans`, and packaging both this way
is what makes the descent from K-flat representatives a single extensionality step. -/
def braidingIsoNatTrans :
    Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf) ⟶
      CategoryTheory.Prod.swap _ _ ⋙
        Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf) where
  app MN := ((canonicalDerivedTensorProduct W.sheaf).braidingIso
    (AlgebraicGeometry.RingedSpace.ringedSite W) MN.1 MN.2).hom
  naturality _ _ g := braidingIsoHom_naturality W g.1 g.2

/-- **The two spellings of the commutativity constraint agree as natural transformations.**
`D(𝒪_W)` is the localization of the K-flat complexes at the quasi-isomorphisms, so the
identification at a pair of K-flat representatives,
`braidingIso_eq_canonicalBraidingHom_of_kFlat`, suffices. -/
theorem braidingIsoNatTrans_eq :
    Stacks.Cohomology.DerivedPullbackTensor.canonicalBraidingNatTrans W =
      braidingIsoNatTrans W :=
  Stacks.Cohomology.DerivedPullbackTensor.natTrans_ext_of_kFlat W _ _
    fun K L hK hL => braidingIso_eq_canonicalBraidingHom_of_kFlat W K L hK hL

/-- **`Stacks.Cohomology.SupportedComplexes.BraidingIsoEqCanonical` holds for every ringed
space**: the braiding of the re-seated symmetric monoidal derived category of
[Stacks, Tag 0FPT] *is* the isomorphism descended from the Koszul symmetry of complexes through
the K-flat comparisons of [Stacks, Tag 06YU], for arbitrary objects of `D(𝒪_W)`.
-/
theorem braidingIsoEqCanonical : BraidingIsoEqCanonical W :=
  fun A B => NatTrans.congr_app (braidingIsoNatTrans_eq W) (A, B)

end Space

section Residual

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z) (a b : ℤ)

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology (closedSubsetRingedSpace X Z).carrier)
    AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology (closedSubsetRingedSpace X Z).carrier).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [PreservesFiniteLimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteColimits (modulePushforward (closedSubsetInclusion X Z))]

/-- **The compatibility of the corepresenting objects of [Stacks, Tag 0G77] follows from
`ShiftedUnitTransposeClean`.**  This is
`Stacks.Cohomology.SupportedComplexes.shiftedUnitCorepresentingCompatible_of_clean` with both
of its `BraidingIsoEqCanonical` hypotheses discharged by `braidingIsoEqCanonical`, on the
ambient space and on the closed subset. -/
theorem shiftedUnitCorepresentingCompatible_of_transposeClean
    (hclean : ShiftedUnitTransposeClean X Z a b) :
    ShiftedUnitCorepresentingCompatible X Z hZ a b :=
  shiftedUnitCorepresentingCompatible_of_clean X Z hZ a b (braidingIsoEqCanonical X)
    (braidingIsoEqCanonical (closedSubsetRingedSpace X Z)) hclean

/-- **The square of [Stacks, Tag 0G77] follows from `ShiftedUnitTransposeClean`.**  This is
`Stacks.Cohomology.SupportedComplexes.forgetSupportSquare_of_clean` with both of its
`BraidingIsoEqCanonical` hypotheses discharged. -/
theorem forgetSupportSquare_of_transposeClean
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hclean : ShiftedUnitTransposeClean X Z a b)
    (ξ : Stacks.RingedSpace.shiftedUnitObject X a ⟶ K)
    (η : Stacks.RingedSpace.shiftedUnitObject (closedSubsetRingedSpace X Z) b ⟶
      (derivedSupportedSectionsOnClosed X Z hZ).obj M) :
    ForgetSupportSquare X Z hZ a b K M ξ η :=
  forgetSupportSquare_of_clean X Z hZ a b K M (braidingIsoEqCanonical X)
    (braidingIsoEqCanonical (closedSubsetRingedSpace X Z)) hclean ξ η

end Residual

section NoStandIns

/-- Sheafification of presheaves of abelian groups exists on the open-cover site of *every*
ringed space: the first instance binder of the statements above is not a hypothesis but a
theorem, on the ambient space and on the closed subset alike. -/
example (W : RingedSpace.{u, u}) :
    HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u} :=
  Stacks.AssociatedSheaf.hasModuleSheafify W

/-- Weak equivalences of presheaves of abelian groups on the open-cover site of a ringed space
are the locally bijective maps: the second instance binder is discharged unconditionally too. -/
example (W : RingedSpace.{u, u}) :
    (Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective W

end NoStandIns

end Stacks.Cohomology.SupportedComplexes

end
