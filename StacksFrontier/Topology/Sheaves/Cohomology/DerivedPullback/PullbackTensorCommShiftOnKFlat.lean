module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorCommShiftDerivedToTensor
public import StacksFrontier.Homology.KFlat.BifunctorComparisonOneVariable
public import StacksFrontier.Homology.KFlat.BifunctorOneSidedComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorCommShiftTwo
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Shift.CommShiftCompOfEqData

/-!
# The one obligation of Tag 079U, discharged on the K-flat cochain complexes

`Stacks.Cohomology.DerivedPullbackTensor.DerivedToTensorCommShiftOnKFlat` is the pair of
one-variable shift compatibilities that
`Stacks.Cohomology.DerivedPullbackTensor.derivedToTensorCommShift₂_of_kFlat` reduces the whole of
`DerivedToTensorCommShift₂` to, and `DerivedToTensorCommShift₂` is the single obligation the two
comparisons of [Stacks, Tag 079U] share.  This file proves it.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.derivedToTensorNatTrans_app_eq_comparison`: **on a pair
  of K-flat complexes the canonical map of [Stacks, Tag 06YU] is the K-flat comparison of
  `CochainComplex.KFlatBifunctor`, conjugated by the comparison of the two derived tensor
  bifunctors.**
* `Stacks.Cohomology.DerivedPullbackTensor.commShift_app_of_kFlat`: **the first of the two
  one-variable conditions over the K-flat cochain complexes.**  The second,
  `commShift_flipApp_of_kFlat`, and with it `derivedToTensorCommShiftOnKFlat` and
  `derivedToTensorCommShift₂` — the obligation of [Stacks, Tag 079U], over *all* pairs of cochain
  complexes — are proved in
  `StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/PullbackTensorCommShiftFlipApp.lean`
  out of the shift data proved here.  They were advertised in this list before they existed; that
  is corrected.

## Implementation notes

**The one equation the whole file rests on.**  On a pair of K-flat complexes the component of
`derivedToTensorNatTrans Z` is the `toTensor` field of the canonical derived tensor product of
[Stacks, Tag 06YU], which is made opaque with `irreducible_def` (defining equation
`Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct_def`).
`derivedToTensorNatTrans_app_eq_comparison` identifies it with the K-flat comparison of
`CochainComplex.KFlatBifunctor`: the structure's own `toTensor_eq_comparison` field turns
`toTensor` into the structure's `comparison`, and
`Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso_hom_app_app` says exactly that
the comparison of the two bifunctors carries one `comparison` to the other.  That proof is written
in term mode throughout: a `rw` re-checks the goal at `implicit` transparency, where
`Stacks.SheafOfModules.Tensor.ringSheaf` applied to the ringed space's structure sheaf is not
type-correct, and `CategoryTheory.Category.assoc` is then rejected for want of an occurrence of
`(f ≫ g) ≫ h` that is plainly there.

**The `irreducible_def` opacity is crossed by an isomorphism, not by an equality, and the shift
data on the two sides of it already agree.**  The commutation datum every statement in the Tag
079U chain reads on `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor` is
`Stacks.Cohomology.DerivedPullbackTensor.derivedTensorCommShift₂Int`, which *is*
`Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int`, which *is*
`CategoryTheory.Functor.CommShift₂.ofIsoInt` along
`Stacks.SheafOfModules.DerivedMonoidal.canonicalTensorIso`.  So the opaque `commShift₂` field of
the canonical structure is never read here, and the shift compatibility of `canonicalTensorIso`
holds for the datum actually in play *by construction*
(`CategoryTheory.Functor.CommShift₂.ofIsoInt_commShift₂`).  Nothing in this file needs the two to
be related.

**Why the two conditions are proved separately and not as one `NatTrans.CommShift₂`.**  Because at
one variable the toolbox is complete and at two it is not; that is the whole point of the
reduction, and the evidence behind it is recorded in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/PullbackTensorCommShiftComparisons.lean`
and in `StacksFrontier/Homology/KFlat/BifunctorComparisonOneVariable.lean`, which carries the two
one-variable chains.

**`Functor.flip`, never `flipFunctor.obj`.**  `CategoryTheory.Functor.CommShift₂.commShiftFlipObj`
concludes at `G.flip.obj X₂`, so that is the only spelling of a flipped bifunctor at which
instance search finds a commutation datum; `((flipFunctor _ _ _).obj G).obj X₂` is the same
functor and finds nothing, `flipFunctor` being a plain `def`.  Every flipped conjugating
isomorphism here is therefore *pinned in a `def` whose ascribed type uses `Functor.flip`*
(`derivedTensorFlipIsoOn`, `curryDerivedTensorFlip`, `curryTotalFlip`), even though its body is
`(flipFunctor _ _ _).mapIso` applied at an object.  With the unpinned spelling the
second condition fails with five `synthInstance` failures and `commShift_of_eq_conj` cannot even
be applied, because the goal's own source datum is unsynthesizable.

**Why each factor of each chain is a declaration of its own, closed by
`CategoryTheory.NatTrans.commShift_comp_of_eq_data`.**  A chain's junction presents one functor
with two equal but syntactically different commutation data — one a `CommShift.comp`, the other a
field of `CategoryTheory.Functor.CommShift₂.postcompInt` or of Mathlib's `precomp₁`/`precomp₂`,
none of which is `instance_reducible`.  `infer_instance` on the whole composite therefore fails
(at the second condition) or exhausts the 20000-heartbeat typeclass budget (at the first), while
the transport lemma discharges each junction by one `rfl` at default transparency.  Splitting the
first condition's chain into two legs of four and five factors keeps each declaration inside its
own budget.

**Why the first variable is restricted to the K-flat complexes and not to the left K-flat ones.**
Recorded at `DerivedToTensorCommShiftOnKFlat` itself: it asks for less, and it is the same pair of
categories as `ModelsComparisonCommShiftOnComplexes`.  The price is paid here, in `kFlatToLeftOn`:
the second condition's chain has to be whiskered along the inclusion of the K-flat complexes into
the left K-flat ones, which is `CategoryTheory.ObjectProperty.lift` of the inclusion along
`Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat` and is shift-compatible by
`CategoryTheory.Functor.CommShift.ofComp`, exactly as `kFlatQuotient` is.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedPullbackTensor

universe u

/-- The image under any functor of the component of
`CategoryTheory.ObjectProperty.liftCompιIso` is an identity.  Stated over an abstract category
with every object a variable, because at the concrete spelling of this file the `rfl` that proves
it exhausts the *kernel*'s budget: `ObjectProperty.liftCompιIso` is `CategoryTheory.Iso.refl`, but
unfolding it at `kFlatComplexesLeft (tensorOn Z)` forces the kernel through the whole instance
tower of `Mod(𝒪_Z)`.  Applied by name the kernel only instantiates. -/
private theorem liftCompι_map_inv_app {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (P : ObjectProperty D) (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) (G : D ⥤ E) (X : C) :
    G.map ((P.liftCompιIso F hF).inv.app X) = 𝟙 (G.obj (F.obj X)) :=
  G.map_id _

/-- Cancel the three identities of a five-factor chain, over an abstract category. -/
private theorem chainFive {C : Type*} [Category* C] {W X Y : C} (s : W ⟶ X) (m : X ⟶ Y) :
    𝟙 W ≫ 𝟙 W ≫ s ≫ 𝟙 X ≫ m = s ≫ m := by
  simp

/-- Cancel the three identities of the first leg's chain, with the inclusion comparison's own
component resolved in the same step.  Keeping the `ObjectProperty.liftCompιIso` inside the
statement is what keeps the defeq `(P.lift F hF ⋙ P.ι).obj X = F.obj X` at the *abstract* level,
where it is one delta step; asked at the concrete spelling of this file it exhausts the kernel's
budget. -/
private theorem chainFourLift {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (P : ObjectProperty D) (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) (G : D ⥤ E) (X : C)
    {W : E} (v : W ⟶ G.obj (F.obj X)) :
    𝟙 W ≫ v ≫ 𝟙 (G.obj (F.obj X)) ≫ G.map ((P.liftCompιIso F hF).inv.app X) = v := by
  rw [liftCompι_map_inv_app P F hF G X]
  simp

/-- Whiskering the inverse of a shift-compatible isomorphism on the left by a functor that
commutes with the shift gives a shift-compatible isomorphism. -/
private theorem isoWhiskerLeft_symm_hom_commShift {C D E : Type*} [Category* C] [Category* D]
    [Category* E] [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ] (H : C ⥤ D) [H.CommShift ℤ]
    {F G : D ⥤ E} [F.CommShift ℤ] [G.CommShift ℤ] (e : F ≅ G)
    (he : NatTrans.CommShift e.hom ℤ) :
    NatTrans.CommShift (Functor.isoWhiskerLeft H e.symm).hom ℤ := by
  dsimp only [Functor.isoWhiskerLeft_hom]
  infer_instance

attribute [local instance] HasDerivedCategory.standard

open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback (Modules)

attribute [local instance] derivedTensorCommShift₂Int
  curriedComplexesDerivedTensor_commShift₂Int curriedComplexesTotal_commShift₂Int
  curryComplexesDerivedTensor_commShift₂Int curryComplexesTotal_commShift₂Int

variable (Z : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The tensor product of `𝒪_Z`-modules, the bifunctor every K-flat notion here is taken at. -/
abbrev tensorOn : Modules Z ⥤ Modules Z ⥤ Modules Z :=
  Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf

/-- **`D(Mod(𝒪_Z))` is the localization of the K-flat objects of `K(Mod(𝒪_Z))`**, seated at the
ringed-space spelling.  The K-flat resolutions are an instance,
`Stacks.DerivedTensor.RingedSite.kFlatLocalizer_hasLeftResolutions`, for a ring
`R : Sheaf J CommRingCat`; but `Z.sheaf` is a `TopCat.Sheaf`, which instance search does not
unfold to that type, so it does not take `Z.sheaf` for `R`, and
`Stacks.DerivedTensor.RingedSite.kFlatQ_isLocalization` is applied by name here. -/
@[instance_reducible]
def kFlatQOn_isLocalization :
    (CochainComplex.KFlatBifunctor.kFlatQ (tensorOn Z)).IsLocalization
      (CochainComplex.KFlatBifunctor.kFlatQuasiIso (tensorOn Z)) :=
  Stacks.DerivedTensor.RingedSite.kFlatQ_isLocalization Z.sheaf

/-- The mirror of `kFlatQOn_isLocalization` for the *left* K-flat objects, which is the
localization `CochainComplex.KFlatBifunctor.derivedBifunctor` descends along in its first
variable. -/
@[instance_reducible]
def kFlatQLeftOn_isLocalization :
    (CochainComplex.KFlatBifunctor.kFlatQLeft (tensorOn Z)).IsLocalization
      (CochainComplex.KFlatBifunctor.kFlatQuasiIsoLeft (tensorOn Z)) :=
  Stacks.DerivedTensor.RingedSite.kFlatQLeft_isLocalization Z.sheaf

attribute [local instance] kFlatQOn_isLocalization kFlatQLeftOn_isLocalization

/-! ### The derived tensor product of `Z` is the generic derived bifunctor -/

/-- **`CochainComplex.KFlatBifunctor.derivedBifunctor` of the tensor product of `𝒪_Z`-modules is
the derived tensor product of [Stacks, Tag 06YU]**, at the ringed-space spelling of the structure
sheaf.  This is `Stacks.SheafOfModules.DerivedMonoidal.canonicalTensorIso`, whose own type is
written at `CategoryTheory.MonoidalCategory.curriedTensor` of the re-seated monoidal structure; the
two bifunctors agree by `rfl`
(`Stacks.SheafOfModules.DerivedMonoidal.curriedTensor_mod_eq_sheafTensor`), and ascribing the type
here is what makes the shift data of the source findable by instance search. -/
def derivedTensorIsoOn :
    CochainComplex.KFlatBifunctor.derivedBifunctor (tensorOn Z) ≅
      Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf :=
  Stacks.SheafOfModules.DerivedMonoidal.canonicalTensorIso Z.sheaf

/-- **The comparison of the two derived tensor bifunctors is compatible with the shifts in both
variables**, at the respelled type and for the datum `derivedTensorCommShift₂Int` in play here,
which is transported along `Stacks.SheafOfModules.DerivedMonoidal.canonicalTensorIso`: this is
`CategoryTheory.Functor.CommShift₂.ofIsoInt_commShift₂`. -/
theorem derivedTensorIsoOn_commShift₂ :
    NatTrans.CommShift₂Int (derivedTensorIsoOn Z).hom :=
  Functor.CommShift₂.ofIsoInt_commShift₂
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalTensorIso Z.sheaf)

/-- The inverse of `derivedTensorIsoOn` at a fixed object of the first variable is
shift-compatible: the `commShift_app` field, respelled through `CategoryTheory.Iso.app` and
inverted. -/
theorem derivedTensorIsoOn_app_inv_commShift (X : DerivedCategory (Modules Z)) :
    NatTrans.CommShift ((derivedTensorIsoOn Z).app X).inv ℤ := by
  have : NatTrans.CommShift ((derivedTensorIsoOn Z).app X).hom ℤ :=
    (derivedTensorIsoOn_commShift₂ Z).commShift_app X
  infer_instance

/-- **The comparison of the two derived tensor bifunctors at a fixed object of the *second*
variable**, pinned at the `CategoryTheory.Functor.flip` spelling.  The body is
`CategoryTheory.flipFunctor` applied at an object, which is the same functor; what the ascription
buys is that `CategoryTheory.Functor.CommShift₂.commShiftFlipObj` — stated at `G.flip.obj X` — is
then found for the source and the target. -/
def derivedTensorFlipIsoOn (X : DerivedCategory (Modules Z)) :
    (CochainComplex.KFlatBifunctor.derivedBifunctor (tensorOn Z)).flip.obj X ≅
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf).flip.obj X :=
  ((flipFunctor _ _ _).mapIso (derivedTensorIsoOn Z)).app X

/-- `derivedTensorFlipIsoOn` is the `commShift_flipApp` field of
`derivedTensorIsoOn_commShift₂`. -/
theorem derivedTensorFlipIsoOn_commShift (X : DerivedCategory (Modules Z)) :
    NatTrans.CommShift (derivedTensorFlipIsoOn Z X).hom ℤ :=
  (derivedTensorIsoOn_commShift₂ Z).commShift_flipApp X

/-- Hence its inverse is shift-compatible. -/
theorem derivedTensorFlipIsoOn_inv_commShift (X : DerivedCategory (Modules Z)) :
    NatTrans.CommShift (derivedTensorFlipIsoOn Z X).inv ℤ := by
  have := derivedTensorFlipIsoOn_commShift Z X
  infer_instance

/-! ### The canonical map on a pair of K-flat complexes -/

/-- **On a pair of K-flat cochain complexes the canonical map of [Stacks, Tag 06YU] is the K-flat
comparison of `CochainComplex.KFlatBifunctor`, conjugated by `derivedTensorIsoOn`.**  This is the
one equation connecting the opaque `toTensor` field of the canonical derived tensor product to
the descent whose shift compatibility is available. -/
theorem derivedToTensorNatTrans_app_eq_comparison
    (K L : CochainComplex (Modules Z) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (tensorOn Z) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat (tensorOn Z) L) :
    (derivedToTensorNatTrans Z).app (K, L) =
      (((derivedTensorIsoOn Z).app (DerivedCategory.Q.obj K)).app
          (DerivedCategory.Q.obj L)).inv ≫
        (CochainComplex.KFlatBifunctor.comparison (tensorOn Z) K L
          (Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat Z.sheaf hK) hL).hom := by
  have hcomp : (derivedToTensorNatTrans Z).app (K, L) =
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Z.sheaf).comparison
        K L hK hL).hom :=
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
      Z.sheaf).toTensor_eq_comparison K L hK hL
  have hiso : (((derivedTensorIsoOn Z).app (DerivedCategory.Q.obj K)).app
        (DerivedCategory.Q.obj L)).hom =
      (CochainComplex.KFlatBifunctor.comparisonRight (tensorOn Z) K L hL).hom ≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Z.sheaf).comparison
          K L hK hL).inv :=
    Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso_hom_app_app Z.sheaf
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Z.sheaf) K L hK hL
  refine hcomp.trans ((Iso.eq_inv_comp _).2 ?_)
  exact (congrArg (fun t => t ≫
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Z.sheaf).comparison
        K L hK hL).hom) hiso).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun t =>
          (CochainComplex.KFlatBifunctor.comparisonRight (tensorOn Z) K L hL).hom ≫ t)
          (Iso.inv_hom_id _)).trans
        ((Category.comp_id _).trans
          (congrArg Iso.hom (CochainComplex.KFlatBifunctor.comparisonRight_eq_comparison
            (tensorOn Z) K L
            (Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat Z.sheaf hK) hL)))))

/-! ### The K-flat complexes are left K-flat -/

/-- **The K-flat cochain complexes of `𝒪_Z`-modules sit inside the left K-flat ones**, as a functor
between the two full subcategories: this is
`Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat`, the symmetry of `⊗_{𝒪_Z}`, read as an
inclusion. -/
abbrev kFlatToLeftOn :
    (kFlatComplexesOn Z).FullSubcategory ⥤
      (CochainComplex.KFlatBifunctor.kFlatComplexesLeft (tensorOn Z)).FullSubcategory :=
  (CochainComplex.KFlatBifunctor.kFlatComplexesLeft (tensorOn Z)).lift
    (kFlatComplexesOn Z).ι
    (fun P ↦ Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat Z.sheaf P.2)

/-- **The inclusion of the K-flat complexes into the left K-flat ones commutes with the shift**, by
`CategoryTheory.Functor.CommShift.ofComp` through the fully faithful inclusion of the left K-flat
complexes, exactly as `CochainComplex.KFlatBifunctor.kFlatQuotient_commShift`. -/
@[instance_reducible]
def kFlatToLeftOn_commShift : (kFlatToLeftOn Z).CommShift ℤ :=
  Functor.CommShift.ofComp
    ((CochainComplex.KFlatBifunctor.kFlatComplexesLeft (tensorOn Z)).liftCompιIso
      (kFlatComplexesOn Z).ι
      (fun P ↦ Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat Z.sheaf P.2)) ℤ

attribute [local instance] kFlatToLeftOn_commShift

/-- The identification of that inclusion followed by the inclusion of the left K-flat complexes
with the inclusion of the K-flat complexes is shift-compatible, by
`CategoryTheory.Functor.CommShift.ofComp_compatibility`. -/
theorem kFlatToLeftOnCompι_commShift :
    NatTrans.CommShift
      ((CochainComplex.KFlatBifunctor.kFlatComplexesLeft (tensorOn Z)).liftCompιIso
        (kFlatComplexesOn Z).ι
        (fun P ↦ Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat Z.sheaf P.2)).hom ℤ :=
  Functor.CommShift.ofComp_compatibility _ _

/-- The inverse of that identification is shift-compatible too. -/
theorem kFlatToLeftOnCompι_inv_commShift :
    NatTrans.CommShift
      ((CochainComplex.KFlatBifunctor.kFlatComplexesLeft (tensorOn Z)).liftCompιIso
        (kFlatComplexesOn Z).ι
        (fun P ↦ Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat Z.sheaf P.2)).inv ℤ := by
  have := kFlatToLeftOnCompι_commShift Z
  infer_instance

variable (P : (kFlatComplexesOn Z).FullSubcategory)

/-! ### The first condition: the second variable, at a fixed K-flat first factor -/

/-- The reassociation of the source of the first condition: the pinned complex-level form of
`Q(-) ⊗^L Q(-)`, whiskered. -/
def sourceSecondIso :=
  Functor.isoWhiskerLeft (kFlatComplexesOn Z).ι
    ((curryComplexesDerivedTensorIso Z).app ((kFlatComplexesOn Z).ι.obj P)).symm

/-- `sourceSecondIso` is shift-compatible: `curryComplexesDerivedTensor_commShift₂Int` is a
transport along `curryComplexesDerivedTensorIso`, so that isomorphism is shift-compatible by
construction. -/
theorem sourceSecondIso_commShift : NatTrans.CommShift (sourceSecondIso Z P).hom ℤ :=
  isoWhiskerLeft_symm_hom_commShift _ _
    ((Functor.CommShift₂.ofIsoInt_commShift₂ (curryComplexesDerivedTensorIso Z)).commShift_app _)

/-- The reassociation of the target of the first condition. -/
def targetSecondIso :=
  Functor.isoWhiskerLeft (kFlatComplexesOn Z).ι
    ((curryComplexesTotalIso Z).app ((kFlatComplexesOn Z).ι.obj P)).symm

/-- `targetSecondIso` is shift-compatible, for the same reason as `sourceSecondIso`. -/
theorem targetSecondIso_commShift : NatTrans.CommShift (targetSecondIso Z P).hom ℤ :=
  isoWhiskerLeft_symm_hom_commShift _ _
    ((Functor.CommShift₂.ofIsoInt_commShift₂ (curryComplexesTotalIso Z)).commShift_app _)


/-- **The first condition, at the reassociated source and target**: the conjugate of
`CochainComplex.KFlatBifunctor.comparisonSecond` by `derivedTensorIsoOn`.  The three factors are
written inline rather than in `def`s of their own: an ascribed `def` fixes the commutation data of
its source and target at the spelling of its *type*, which at a junction is the spelling the
neighbour does not have, and then even the factor's own compatibility is unsynthesizable. -/
def thetaSecond :
    (kFlatComplexesOn Z).ι ⋙
        (curriedComplexesDerivedTensor Z).obj ((kFlatComplexesOn Z).ι.obj P) ⟶
      (kFlatComplexesOn Z).ι ⋙
        (curriedComplexesTotal Z).obj ((kFlatComplexesOn Z).ι.obj P) :=
  (Functor.associator (kFlatComplexesOn Z).ι DerivedCategory.Q
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf).obj
        (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj P)))).inv ≫
    Functor.whiskerLeft (CochainComplex.KFlatBifunctor.kFlatComplexQ (tensorOn Z))
        ((derivedTensorIsoOn Z).app
          (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj P))).inv ≫
      (CochainComplex.KFlatBifunctor.comparisonSecond (tensorOn Z)
        ((kFlatComplexesOn Z).ι.obj P)
        (Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat Z.sheaf P.2)).hom

/-- The first factor of `thetaSecond` is shift-compatible. -/
theorem secondAssoc_commShift :
    NatTrans.CommShift (Functor.associator (kFlatComplexesOn Z).ι DerivedCategory.Q
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf).obj
        (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj P)))).inv ℤ := by
  infer_instance

/-- The second factor of `thetaSecond` is shift-compatible. -/
theorem secondConj_commShift :
    NatTrans.CommShift (Functor.whiskerLeft
      (CochainComplex.KFlatBifunctor.kFlatComplexQ (tensorOn Z))
      ((derivedTensorIsoOn Z).app
        (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj P))).inv) ℤ := by
  have := derivedTensorIsoOn_app_inv_commShift Z
    (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj P))
  infer_instance

/-- `thetaSecond` is shift-compatible.  The two junctions present one functor with two equal but
syntactically different commutation data, so they are discharged by
`CategoryTheory.NatTrans.commShift_comp_of_eq_data` rather than by instance search. -/
theorem thetaSecond_commShift : NatTrans.CommShift (thetaSecond Z P) ℤ := by
  unfold thetaSecond
  exact CategoryTheory.NatTrans.commShift_comp_of_eq_data _ _ (secondAssoc_commShift Z P)
    (CategoryTheory.NatTrans.commShift_comp_of_eq_data _ _ (secondConj_commShift Z P)
      (CochainComplex.KFlatBifunctor.comparisonSecond_commShift (tensorOn Z)
        ((kFlatComplexesOn Z).ι.obj P)
        (Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat Z.sheaf P.2)))

/-- The component of the transformation the first condition is about. -/
theorem whiskerLeft_curry_app (L : (kFlatComplexesOn Z).FullSubcategory) :
    (Functor.whiskerLeft (kFlatComplexesOn Z).ι
        ((Functor.curry.map (derivedToTensorNatTrans Z)).app
          ((kFlatComplexesOn Z).ι.obj P))).app L =
      (derivedToTensorNatTrans Z).app
        ((kFlatComplexesOn Z).ι.obj P, (kFlatComplexesOn Z).ι.obj L) := rfl

/-- **The transformation of the first condition is the conjugate of `thetaSecond`.**  Both
reassociations are the identity on every object, so this is
`derivedToTensorNatTrans_app_eq_comparison` componentwise.  The proof is written in term mode:
`rw` and `simp` re-check the goal at `implicit` transparency, where `SheafedSpace.sheaf Z` is not
type-correct as a sheaf on the open-cover site, and even `CategoryTheory.Category.id_comp` is then
rejected for want of an occurrence of `𝟙 _ ≫ _` that is plainly there. -/
theorem thetaSecond_eq :
    Functor.whiskerLeft (kFlatComplexesOn Z).ι
        ((Functor.curry.map (derivedToTensorNatTrans Z)).app
          ((kFlatComplexesOn Z).ι.obj P)) =
      (sourceSecondIso Z P).hom ≫ thetaSecond Z P ≫ (targetSecondIso Z P).inv :=
  NatTrans.ext (funext fun L ↦
    ((whiskerLeft_curry_app Z P L).trans
        (derivedToTensorNatTrans_app_eq_comparison Z ((kFlatComplexesOn Z).ι.obj P)
          ((kFlatComplexesOn Z).ι.obj L) P.2 L.2)).trans
      (((Category.id_comp _).trans ((Category.comp_id _).trans (Category.id_comp _))).trans
          (congrArg
            (fun t ↦ ((((derivedTensorIsoOn Z).app
                (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj P))).inv.app
                  (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj L))) ≫ t))
            (CochainComplex.KFlatBifunctor.comparisonSecond_hom_app (tensorOn Z)
              ((kFlatComplexesOn Z).ι.obj P)
              (Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat Z.sheaf P.2) L))).symm)

/-- **The first of the two conditions of `DerivedToTensorCommShiftOnKFlat`**: at a fixed K-flat
complex in the first variable, the canonical map of [Stacks, Tag 06YU] restricted to the K-flat
complexes in the second is compatible with the shift. -/
theorem commShift_app_of_kFlat :
    NatTrans.CommShift (Functor.whiskerLeft (kFlatComplexesOn Z).ι
      ((Functor.curry.map (derivedToTensorNatTrans Z)).app
        ((kFlatComplexesOn Z).ι.obj P))) ℤ := by
  have := sourceSecondIso_commShift Z P
  have := targetSecondIso_commShift Z P
  have := thetaSecond_commShift Z P
  exact NatTrans.commShift_of_eq_conj (sourceSecondIso Z P) (targetSecondIso Z P)
    (thetaSecond Z P) (thetaSecond_eq Z P)

/-! ### The second condition: the first variable, at a fixed K-flat second factor -/

/-- The source reassociation of the second condition, flipped, pinned at the `Functor.flip`
spelling. -/
def curryDerivedTensorFlip (K : CochainComplex (Modules Z) ℤ) :
    (curriedComplexesDerivedTensor Z).flip.obj K ≅
      (Functor.curry.obj (DerivedCategory.Q.prod DerivedCategory.Q ⋙ Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf))).flip.obj K :=
  ((flipFunctor _ _ _).mapIso (curryComplexesDerivedTensorIso Z)).app K

/-- `curryDerivedTensorFlip` is shift-compatible, from the `commShift_flipApp` field of the
transport which defines `curryComplexesDerivedTensor_commShift₂Int`. -/
theorem curryDerivedTensorFlip_commShift (K : CochainComplex (Modules Z) ℤ) :
    NatTrans.CommShift (curryDerivedTensorFlip Z K).hom ℤ :=
  (Functor.CommShift₂.ofIsoInt_commShift₂
    (curryComplexesDerivedTensorIso Z)).commShift_flipApp K

/-- The target reassociation of the second condition, flipped, pinned. -/
def curryTotalFlip (K : CochainComplex (Modules Z) ℤ) :
    (curriedComplexesTotal Z).flip.obj K ≅
      (Functor.curry.obj
        (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf) ⋙
          DerivedCategory.Q)).flip.obj K :=
  ((flipFunctor _ _ _).mapIso (curryComplexesTotalIso Z)).app K

/-- `curryTotalFlip` is shift-compatible, for the same reason. -/
theorem curryTotalFlip_commShift (K : CochainComplex (Modules Z) ℤ) :
    NatTrans.CommShift (curryTotalFlip Z K).hom ℤ :=
  (Functor.CommShift₂.ofIsoInt_commShift₂ (curryComplexesTotalIso Z)).commShift_flipApp K

/-- The reassociation of the source of the second condition. -/
def sourceFirstIso :=
  Functor.isoWhiskerLeft (kFlatComplexesOn Z).ι
    (curryDerivedTensorFlip Z ((kFlatComplexesOn Z).ι.obj P)).symm

/-- `sourceFirstIso` is shift-compatible. -/
theorem sourceFirstIso_commShift : NatTrans.CommShift (sourceFirstIso Z P).hom ℤ :=
  isoWhiskerLeft_symm_hom_commShift _ _ (curryDerivedTensorFlip_commShift Z _)

/-- The reassociation of the target of the second condition. -/
def targetFirstIso :=
  Functor.isoWhiskerLeft (kFlatComplexesOn Z).ι
    (curryTotalFlip Z ((kFlatComplexesOn Z).ι.obj P)).symm

/-- `targetFirstIso` is shift-compatible. -/
theorem targetFirstIso_commShift : NatTrans.CommShift (targetFirstIso Z P).hom ℤ :=
  isoWhiskerLeft_symm_hom_commShift _ _ (curryTotalFlip_commShift Z _)

/-- **The first leg of the second condition's chain**: from the canonical derived tensor product
to the descent, and from the inclusion of the K-flat complexes to the inclusion of the left K-flat
ones.  Split from the second leg so that each is elaborated and checked on its own budget. -/
def thetaFirstLegOne :
    (kFlatComplexesOn Z).ι ⋙
        (curriedComplexesDerivedTensor Z).flip.obj ((kFlatComplexesOn Z).ι.obj P) ⟶
      (kFlatToLeftOn Z ⋙
          (CochainComplex.KFlatBifunctor.kFlatComplexesLeft (tensorOn Z)).ι) ⋙
        (DerivedCategory.Q ⋙
          (CochainComplex.KFlatBifunctor.derivedBifunctor (tensorOn Z)).flip.obj
            (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj P))) :=
  (Functor.associator (kFlatComplexesOn Z).ι DerivedCategory.Q
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf).flip.obj
        (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj P)))).inv ≫
    Functor.whiskerLeft (CochainComplex.KFlatBifunctor.kFlatComplexQ (tensorOn Z))
        (derivedTensorFlipIsoOn Z
          (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj P))).inv ≫
      (Functor.associator (kFlatComplexesOn Z).ι DerivedCategory.Q
          ((CochainComplex.KFlatBifunctor.derivedBifunctor (tensorOn Z)).flip.obj
            (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj P)))).hom ≫
        Functor.whiskerRight
          ((CochainComplex.KFlatBifunctor.kFlatComplexesLeft (tensorOn Z)).liftCompιIso
            (kFlatComplexesOn Z).ι
            (fun P ↦ Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat Z.sheaf P.2)).inv
          (DerivedCategory.Q ⋙
            (CochainComplex.KFlatBifunctor.derivedBifunctor (tensorOn Z)).flip.obj
              (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj P)))

/-- The first factor of `thetaFirstLegOne` is shift-compatible. -/
theorem firstAssocOne_commShift :
    NatTrans.CommShift (Functor.associator (kFlatComplexesOn Z).ι DerivedCategory.Q
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf).flip.obj
        (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj P)))).inv ℤ := by
  infer_instance

/-- The second factor of `thetaFirstLegOne` is shift-compatible. -/
theorem firstConj_commShift :
    NatTrans.CommShift (Functor.whiskerLeft
      (CochainComplex.KFlatBifunctor.kFlatComplexQ (tensorOn Z))
      (derivedTensorFlipIsoOn Z
        (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj P))).inv) ℤ := by
  have := derivedTensorFlipIsoOn_inv_commShift Z
    (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj P))
  infer_instance

/-- The third factor of `thetaFirstLegOne` is shift-compatible. -/
theorem firstAssocTwo_commShift :
    NatTrans.CommShift (Functor.associator (kFlatComplexesOn Z).ι DerivedCategory.Q
      ((CochainComplex.KFlatBifunctor.derivedBifunctor (tensorOn Z)).flip.obj
        (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj P)))).hom ℤ := by
  infer_instance

/-- The fourth factor of `thetaFirstLegOne` is shift-compatible. -/
theorem firstIncl_commShift :
    NatTrans.CommShift (Functor.whiskerRight
      ((CochainComplex.KFlatBifunctor.kFlatComplexesLeft (tensorOn Z)).liftCompιIso
        (kFlatComplexesOn Z).ι
        (fun P ↦ Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat Z.sheaf P.2)).inv
      (DerivedCategory.Q ⋙
        (CochainComplex.KFlatBifunctor.derivedBifunctor (tensorOn Z)).flip.obj
          (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj P)))) ℤ := by
  have := kFlatToLeftOnCompι_inv_commShift Z
  infer_instance

/-- `thetaFirstLegOne` is shift-compatible. -/
theorem thetaFirstLegOne_commShift : NatTrans.CommShift (thetaFirstLegOne Z P) ℤ := by
  unfold thetaFirstLegOne
  exact CategoryTheory.NatTrans.commShift_comp_of_eq_data _ _ (firstAssocOne_commShift Z P)
    (CategoryTheory.NatTrans.commShift_comp_of_eq_data _ _ (firstConj_commShift Z P)
      (CategoryTheory.NatTrans.commShift_comp_of_eq_data _ _ (firstAssocTwo_commShift Z P)
        (firstIncl_commShift Z P)))

/-- **The second leg of the second condition's chain**: `comparisonFirst`, whiskered along the
inclusion of the K-flat complexes into the left K-flat ones, with its two reassociations and the
passage back to the inclusion of the K-flat complexes. -/
def thetaFirstLegTwo :
    (kFlatToLeftOn Z ⋙
          (CochainComplex.KFlatBifunctor.kFlatComplexesLeft (tensorOn Z)).ι) ⋙
        (DerivedCategory.Q ⋙
          (CochainComplex.KFlatBifunctor.derivedBifunctor (tensorOn Z)).flip.obj
            (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj P))) ⟶
      (kFlatComplexesOn Z).ι ⋙
        (curriedComplexesTotal Z).flip.obj ((kFlatComplexesOn Z).ι.obj P) :=
  (Functor.associator (kFlatToLeftOn Z)
      (CochainComplex.KFlatBifunctor.kFlatComplexesLeft (tensorOn Z)).ι
      (DerivedCategory.Q ⋙
        (CochainComplex.KFlatBifunctor.derivedBifunctor (tensorOn Z)).flip.obj
          (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj P)))).hom ≫
    Functor.whiskerLeft (kFlatToLeftOn Z)
        (Functor.associator
          (CochainComplex.KFlatBifunctor.kFlatComplexesLeft (tensorOn Z)).ι DerivedCategory.Q
          ((CochainComplex.KFlatBifunctor.derivedBifunctor (tensorOn Z)).flip.obj
            (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj P)))).inv ≫
      Functor.whiskerLeft (kFlatToLeftOn Z)
          (CochainComplex.KFlatBifunctor.comparisonFirst (tensorOn Z)
            ((kFlatComplexesOn Z).ι.obj P) P.2).hom ≫
        (Functor.associator (kFlatToLeftOn Z)
            (CochainComplex.KFlatBifunctor.kFlatComplexesLeft (tensorOn Z)).ι
            ((CochainComplex.KFlatBifunctor.totalBifunctor (tensorOn Z)).flip.obj
              ((kFlatComplexesOn Z).ι.obj P) ⋙ DerivedCategory.Q)).inv ≫
          Functor.whiskerRight
            ((CochainComplex.KFlatBifunctor.kFlatComplexesLeft (tensorOn Z)).liftCompιIso
              (kFlatComplexesOn Z).ι
              (fun P ↦ Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat Z.sheaf P.2)).hom
            ((CochainComplex.KFlatBifunctor.totalBifunctor (tensorOn Z)).flip.obj
              ((kFlatComplexesOn Z).ι.obj P) ⋙ DerivedCategory.Q)

/-- The first factor of `thetaFirstLegTwo` is shift-compatible. -/
theorem firstAssocThree_commShift :
    NatTrans.CommShift (Functor.associator (kFlatToLeftOn Z)
      (CochainComplex.KFlatBifunctor.kFlatComplexesLeft (tensorOn Z)).ι
      (DerivedCategory.Q ⋙
        (CochainComplex.KFlatBifunctor.derivedBifunctor (tensorOn Z)).flip.obj
          (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj P)))).hom ℤ := by
  infer_instance

/-- The second factor of `thetaFirstLegTwo` is shift-compatible. -/
theorem firstAssocFour_commShift :
    NatTrans.CommShift (Functor.whiskerLeft (kFlatToLeftOn Z)
      (Functor.associator
        (CochainComplex.KFlatBifunctor.kFlatComplexesLeft (tensorOn Z)).ι DerivedCategory.Q
        ((CochainComplex.KFlatBifunctor.derivedBifunctor (tensorOn Z)).flip.obj
          (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj P)))).inv) ℤ := by
  infer_instance

/-- The third factor of `thetaFirstLegTwo` is shift-compatible, by
`CochainComplex.KFlatBifunctor.comparisonFirst_commShift`. -/
theorem firstComparison_commShift :
    NatTrans.CommShift (Functor.whiskerLeft (kFlatToLeftOn Z)
      (CochainComplex.KFlatBifunctor.comparisonFirst (tensorOn Z)
        ((kFlatComplexesOn Z).ι.obj P) P.2).hom) ℤ := by
  have := CochainComplex.KFlatBifunctor.comparisonFirst_commShift (tensorOn Z)
    ((kFlatComplexesOn Z).ι.obj P) P.2
  infer_instance

/-- The fourth factor of `thetaFirstLegTwo` is shift-compatible. -/
theorem firstAssocFive_commShift :
    NatTrans.CommShift (Functor.associator (kFlatToLeftOn Z)
      (CochainComplex.KFlatBifunctor.kFlatComplexesLeft (tensorOn Z)).ι
      ((CochainComplex.KFlatBifunctor.totalBifunctor (tensorOn Z)).flip.obj
        ((kFlatComplexesOn Z).ι.obj P) ⋙ DerivedCategory.Q)).inv ℤ := by
  infer_instance

/-- The fifth factor of `thetaFirstLegTwo` is shift-compatible. -/
theorem firstInclBack_commShift :
    NatTrans.CommShift (Functor.whiskerRight
      ((CochainComplex.KFlatBifunctor.kFlatComplexesLeft (tensorOn Z)).liftCompιIso
        (kFlatComplexesOn Z).ι
        (fun P ↦ Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat Z.sheaf P.2)).hom
      ((CochainComplex.KFlatBifunctor.totalBifunctor (tensorOn Z)).flip.obj
        ((kFlatComplexesOn Z).ι.obj P) ⋙ DerivedCategory.Q)) ℤ := by
  have := kFlatToLeftOnCompι_commShift Z
  infer_instance

/-- `thetaFirstLegTwo` is shift-compatible. -/
theorem thetaFirstLegTwo_commShift : NatTrans.CommShift (thetaFirstLegTwo Z P) ℤ := by
  unfold thetaFirstLegTwo
  exact CategoryTheory.NatTrans.commShift_comp_of_eq_data _ _ (firstAssocThree_commShift Z P)
    (CategoryTheory.NatTrans.commShift_comp_of_eq_data _ _ (firstAssocFour_commShift Z P)
      (CategoryTheory.NatTrans.commShift_comp_of_eq_data _ _ (firstComparison_commShift Z P)
        (CategoryTheory.NatTrans.commShift_comp_of_eq_data _ _ (firstAssocFive_commShift Z P)
          (firstInclBack_commShift Z P))))

/-- **The second condition, at the reassociated source and target.** -/
def thetaFirst :
    (kFlatComplexesOn Z).ι ⋙
        (curriedComplexesDerivedTensor Z).flip.obj ((kFlatComplexesOn Z).ι.obj P) ⟶
      (kFlatComplexesOn Z).ι ⋙
        (curriedComplexesTotal Z).flip.obj ((kFlatComplexesOn Z).ι.obj P) :=
  thetaFirstLegOne Z P ≫ thetaFirstLegTwo Z P

/-- `thetaFirst` is shift-compatible. -/
theorem thetaFirst_commShift : NatTrans.CommShift (thetaFirst Z P) ℤ := by
  unfold thetaFirst
  exact CategoryTheory.NatTrans.commShift_comp_of_eq_data _ _ (thetaFirstLegOne_commShift Z P)
    (thetaFirstLegTwo_commShift Z P)

/-- The component of the pinned flipped comparison is the component of the unflipped one. -/
theorem derivedTensorFlipIsoOn_inv_app (X Y : DerivedCategory (Modules Z)) :
    (derivedTensorFlipIsoOn Z X).inv.app Y =
      (((derivedTensorIsoOn Z).app Y).app X).inv := rfl

/-- The component of `thetaFirstLegOne`, factor by factor, with **both identities' objects
spelled as `chainFourLift` spells them** rather than as the body of `thetaFirstLegOne` does.
That is the whole point of this declaration: the two spellings are definitionally equal but
comparing them forces the kernel through `CochainComplex.KFlatBifunctor.derivedBifunctor`, a
`CategoryTheory.Localization.lift₂`, and doing that inside `thetaFirstLegOne_app` — together with
the cancellations — exceeds the kernel's deterministic limit.  Isolated here it has a budget of
its own, and the `Eq.trans` below is then syntactic. -/
theorem thetaFirstLegOne_app_factors (K : (kFlatComplexesOn Z).FullSubcategory) :
    (thetaFirstLegOne Z P).app K =
      𝟙 (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf).flip.obj
            (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj P))).obj
          (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj K))) ≫
        (derivedTensorFlipIsoOn Z
              (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj P))).inv.app
            (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj K)) ≫
          𝟙 ((DerivedCategory.Q ⋙
                (CochainComplex.KFlatBifunctor.derivedBifunctor (tensorOn Z)).flip.obj
                  (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj P))).obj
              ((kFlatComplexesOn Z).ι.obj K)) ≫
            (DerivedCategory.Q ⋙
                (CochainComplex.KFlatBifunctor.derivedBifunctor (tensorOn Z)).flip.obj
                  (DerivedCategory.Q.obj ((kFlatComplexesOn Z).ι.obj P))).map
              (((CochainComplex.KFlatBifunctor.kFlatComplexesLeft (tensorOn Z)).liftCompιIso
                (kFlatComplexesOn Z).ι
                (fun P ↦
                  Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat Z.sheaf P.2)).inv.app K) :=
  rfl

/-- The component of `thetaFirstLegTwo`, factor by factor. -/
theorem thetaFirstLegTwo_app_factors (K : (kFlatComplexesOn Z).FullSubcategory) :
    (thetaFirstLegTwo Z P).app K =
      𝟙 _ ≫ 𝟙 _ ≫ (CochainComplex.KFlatBifunctor.comparisonFirst (tensorOn Z)
            ((kFlatComplexesOn Z).ι.obj P) P.2).hom.app ((kFlatToLeftOn Z).obj K) ≫
        𝟙 _ ≫ ((CochainComplex.KFlatBifunctor.totalBifunctor (tensorOn Z)).flip.obj
            ((kFlatComplexesOn Z).ι.obj P) ⋙ DerivedCategory.Q).map
          (((CochainComplex.KFlatBifunctor.kFlatComplexesLeft (tensorOn Z)).liftCompιIso
            (kFlatComplexesOn Z).ι
            (fun P ↦ Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat Z.sheaf P.2)).hom.app
              K) := rfl

/-- The component of the second leg: `comparisonFirst` at the image of `K` in the left K-flat
complexes, followed by the image of the component of `ObjectProperty.liftCompιIso`.

That last factor is an identity and is deliberately *not* cancelled here.  Cancelling it makes the
statement identify `(kFlatComplexesLeft (tensorOn Z)).ι.obj ((kFlatToLeftOn Z).obj K)` with
`(kFlatComplexesOn Z).ι.obj K` inside the total complex of the target, and that is a kernel
deterministic timeout: the total complexes' existence instance
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.hasMapBifunctor_sheafTensor` is stated with
`HomologicalComplex.HasMapBifunctorReg`, whose regular kernel hint makes the kernel compare the two
complexes themselves, which is the crossing the note at the end of this file finds unaffordable.
`chainFourLiftCompEq` in `PullbackTensorCommShiftFlipApp.lean` cancels the factor at the abstract
level instead. -/
theorem thetaFirstLegTwo_app (K : (kFlatComplexesOn Z).FullSubcategory) :
    (thetaFirstLegTwo Z P).app K =
      (CochainComplex.KFlatBifunctor.comparisonFirst (tensorOn Z)
          ((kFlatComplexesOn Z).ι.obj P) P.2).hom.app ((kFlatToLeftOn Z).obj K) ≫
        ((CochainComplex.KFlatBifunctor.totalBifunctor (tensorOn Z)).flip.obj
            ((kFlatComplexesOn Z).ι.obj P) ⋙ DerivedCategory.Q).map
          (((CochainComplex.KFlatBifunctor.kFlatComplexesLeft (tensorOn Z)).liftCompιIso
            (kFlatComplexesOn Z).ι
            (fun P ↦ Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat Z.sheaf P.2)).hom.app
              K) :=
  (thetaFirstLegTwo_app_factors Z P K).trans (chainFive _ _)

/-- The component of the transformation the second condition is about. -/
theorem whiskerLeft_curry_flipApp (K : (kFlatComplexesOn Z).FullSubcategory) :
    (Functor.whiskerLeft (kFlatComplexesOn Z).ι
        ((Functor.curry.map (derivedToTensorNatTrans Z)).flipApp
          ((kFlatComplexesOn Z).ι.obj P))).app K =
      (derivedToTensorNatTrans Z).app
        ((kFlatComplexesOn Z).ι.obj K, (kFlatComplexesOn Z).ι.obj P) := rfl

/-- The component of the conjugate of `thetaFirst`, factor by factor. -/
theorem conjFirst_app_factors (K : (kFlatComplexesOn Z).FullSubcategory) :
    ((sourceFirstIso Z P).hom ≫ thetaFirst Z P ≫ (targetFirstIso Z P).inv).app K =
      𝟙 _ ≫ (thetaFirst Z P).app K ≫ 𝟙 _ := rfl

/-! ### The second condition, and where it is proved

Everything the second condition needs *about shifts* is proved above: `thetaFirst_commShift` says
the reassociated chain is shift-compatible, and `sourceFirstIso_commShift` /
`targetFirstIso_commShift` say its two conjugating isomorphisms are.  The remaining ingredient is
the purely *bookkeeping* identity that the transformation of the second condition is the conjugate
of `thetaFirst`, and that identity — together with the second condition itself, the whole of
`Stacks.Cohomology.DerivedPullbackTensor.DerivedToTensorCommShiftOnKFlat Z` and, through
`derivedToTensorCommShift₂_of_kFlat`, the whole of `DerivedToTensorCommShift₂ Z` — is
proved in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/PullbackTensorCommShiftFlipApp.lean`
as `thetaFirst_eq`, `commShift_flipApp_of_kFlat`, `derivedToTensorCommShiftOnKFlat` and
`derivedToTensorCommShift₂`.

**Where the cost lies; the details are recorded in that file.**  The obstruction is not the
kernel's budget on the single step that cancels the identity which
`(DerivedCategory.Q ⋙ derivedBifunctor (tensorOn Z)).flip.obj _` puts on the component of
`CategoryTheory.ObjectProperty.liftCompιIso`; it is not that `derivedBifunctor` is a
`CategoryTheory.Localization.lift₂` where `CochainComplex.KFlatBifunctor.totalBifunctor` is a
`map₂HomologicalComplex`; and splitting the cancellation into one declaration per step does not
help.  Instead:

* the crossing `(kFlatComplexesLeft (tensorOn Z)).ι.obj ((kFlatToLeftOn Z).obj K)` =
  `(kFlatComplexesOn Z).ι.obj K` is a kernel deterministic timeout **by `rfl` with nothing applied
  to it at all** — no `derivedBifunctor`, no `DerivedCategory.Q`;
* the same statement is free as `CategoryTheory.ObjectProperty.ι_obj_lift_obj` instantiated by
  name;
* under `(DerivedCategory.Q ⋙ derivedBifunctor (tensorOn Z)).flip.obj _` nothing gets worse: pure
  `Functor.comp` unfolding there is free, and the whole cancellation closes in one application of
  an all-variables lemma;
* what the kernel pays for is the two sides reducing in step: both reach a projection at the
  same time, of `(kFlatToLeftOn Z).obj K` and of `K`, and the kernel first tries to identify
  those two structures, which lie in different full subcategories.  Each of these closes by
  `rfl` in under 1.5 s: `((kFlatToLeftOn Z).obj K).obj = (kFlatComplexesOn Z).ι.obj K`, one
  projection ahead; `(kFlatComplexesOn Z).ι.obj ((𝟭 _).obj K) = (kFlatComplexesOn Z).ι.obj K`, in
  step inside one full subcategory; and the crossing itself with the left K-flat complexes
  replaced by the full subcategory of `fun _ ↦ True`, which the kernel tells apart from the K-flat
  complexes at once.

So the cost is that `rfl` at this file's concrete instantiation, whatever is or is not applied
to it, and the cure is to state every identification as an all-variables lemma and apply it by
name, the standing device of this chapter; a split of the cancellation that still asks for the
crossing by `rfl` does not reach it.  The second leg's mirror crossing is handled the same way. The total complexes' existence instance
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.hasMapBifunctor_sheafTensor` is stated with
`HomologicalComplex.HasMapBifunctorReg`, so `thetaFirstLegTwo_app` cannot cancel it in
place, and `chainFourLiftCompEq` cancels it together with the first leg's.

Four further formulations confirm that no reformulation of the *proof* along the direct route
closes this:
`thetaFirstLegOne_app` as `thetaFirstLegOne_app_factors |>.trans (chainFourLift …)`; the
cancellation split into one declaration per step,
whose `firstLiftCancel` step times out on its own; the whole four-factor chain lifted into one
all-variables lemma and applied by `exact`; and the componentwise `thetaFirst_app` stated alone,
lift-free on both ends.  All four are `(kernel) deterministic timeout`, and in every case the
error is reported at the declaration's *name* column — the kernel is typechecking the
declaration's **type**, with the proof term either absent or already failed.  That is the same
finding as the first bullet above: the crossing is unaffordable by `rfl` whatever is or is not
applied to it. -/

end Stacks.Cohomology.DerivedPullbackTensor

end
