module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IdealGeneratedByNonzerodivisor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerRestrictOpen
public import StacksFrontier.Algebra.Homology.StrictlyPerfectRestrictionOfLE
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedApproximation

/-!
# Restriction to an open of the ideal powers and of the décalage

Let `X` be a ringed space, `I` an invertible ideal sheaf on `X` whose restriction to an open
`U ⊆ X` is again invertible, and `M` a sheaf of `O_X`-modules.  Restriction to `U` carries the
integer ideal power `I^{⊗ n} ⊗ M` to the corresponding power formed on `U`:
`(I^{⊗ n} ⊗ M)|_U ≅ (I|_U)^{⊗ n} ⊗ M|_U` for every `n ∈ ℤ`.

Consequently a sheaf which restricts to zero on `U` has all of its ideal powers restricting to
zero there, and a degree of the décalage `η_I F` restricts to zero on `U` as soon as the two
degrees of `F` it is built from do.

## Main results

* `Stacks.IdealTorsion.Eta.restrictIdealPowerTermIso`: `(I^{⊗ n} ⊗ M)|_U ≅ (I|_U)^{⊗ n} ⊗ M|_U`,
  for every integer `n`.
* `Stacks.IdealTorsion.Eta.isZero_restrict_idealPowerTerm`: an ideal power of a sheaf vanishing
  on `U` vanishes on `U`.
* `Stacks.IdealTorsion.Eta.isZero_restrict_etaTerm`: the degree-`n` term of `η_I F` vanishes on
  `U` when `F^n` and `F^{n+1}` do.
* `Stacks.IdealTorsion.Eta.isZero_restrict_of_le`: a sheaf vanishing on an open vanishes on
  every smaller open.
* `Stacks.IdealTorsion.Eta.exists_nhd_isInvertible_moduleRestriction`: on a ringed space whose
  stalks are local rings, an invertible sheaf of modules restricts to an invertible sheaf of
  modules on every open inside a suitable neighbourhood of any given point.
* `Stacks.IdealTorsion.Eta.isLocallyBounded_etaObj`: the décalage of a locally bounded complex is
  locally bounded.

## Implementation notes

The integer power is the `n`-th power of the autoequivalence `· ⊗ I`, so the comparison is an
instance of `Stacks.Equivalence.powIntertwineObj`: the only input is the case `n = 1`, which is
`Stacks.SheafOfModules.TensorPower.restrictTensorSheafIso`.  The negative branch needs nothing
further, being the inverse of that equivalence.

Invertibility of the restriction of `I` is a hypothesis rather than a consequence, exactly as in
`Stacks.SheafOfModules.TensorPower.restrictTensorPowerIso`.  Both invertibility hypotheses are
passed explicitly and the ideal power is applied explicitly to them: the two spellings of the
structure sheaf of rings in play are the same sheaf, but identifying them unfolds
`CategoryTheory.sheafCompose`, which does not unfold at the transparency at which instances are
found, so instance search does not see the hypothesis for the restricted space.

That an equivalence carries a zero object to a zero object is proved from the hom-set
bijections, not from additivity, so that no additivity of restriction or of the tensor product
is needed.

The term of the décalage is a fibre product, and restriction to an open preserves it by
`AlgebraicGeometry.RingedSpace.restrictModules_preservesFiniteLimits`; a fibre product whose two
outer vertices vanish has vanishing identity by the uniqueness of maps into a fibre product.

## References

* [Stacks Project, Tag 0GT2](https://stacks.math.columbia.edu/tag/0GT2)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.Cohomology.HigherDirectImage
open Stacks.SheafOfModules.TensorPower (restrictTensorSheafIso ringedSpaceIsSheaf)
open Stacks.SheafOfModules.Invertible ( tensorRightFunctor_isEquivalence)
open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk)

universe u

namespace Stacks.IdealTorsion.Eta

/-- **An invertible sheaf of modules restricts to an invertible sheaf of modules.**  On a ringed
space whose stalks are local rings, every point has an open neighbourhood `W` such that the
restriction of an invertible sheaf of modules to any open `V ≤ W` is again invertible: on `W` the
sheaf is trivialized by a section, hence so is its restriction to any smaller open, and the unit
is invertible.

The hypothesis on the stalks is the one the trivialization needs and cannot be dropped: on a
general ringed space an invertible sheaf of modules need not be locally free of rank one, so it
need not be trivial on any neighbourhood. -/
public theorem exists_nhd_isInvertible_moduleRestriction (X : RingedSpace.{u, u})
    [∀ x : X.carrier, IsLocalRing (ringStalk X x)]
    (L : SheafOfModules.{u} (structureSheafRing X))
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf (structureSheafRing X).property L)
    (x : X.carrier) :
    ∃ W : Opens X.carrier, x ∈ W ∧ ∀ V : Opens X.carrier, V ≤ W →
      Stacks.SheafOfModules.IsInvertible (restrictToOpen X V).presheaf
        (structureSheafRing (restrictToOpen X V)).property
        ((moduleRestriction X V).obj L) := by
  let _ := hL
  obtain ⟨W, hxW, a, hbij⟩ := Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible L x
  refine ⟨W, hxW, fun V hVW => ?_⟩
  let e : L.over V ≅ SheafOfModules.unit ((structureSheafRing X).over V) :=
    Stacks.SheafOfModules.isoUnitOver L V
      ((ConcreteCategory.hom (L.val.map (homOfLE hVW).op)) a)
      (fun V' h => by
        have E2 : (ConcreteCategory.hom (L.val.map (homOfLE h).op))
              ((ConcreteCategory.hom (L.val.map (homOfLE hVW).op)) a)
            = (ConcreteCategory.hom (L.val.map (homOfLE (h.trans hVW)).op)) a :=
          (L.val.map_comp_apply (homOfLE hVW).op (homOfLE h).op a).symm.trans
            (L.val.congr_map_apply rfl a)
        rw [E2]
        exact hbij V' (h.trans hVW))
  exact @Stacks.SheafOfModules.isInvertible_of_iso _ _ _ _ _ _ _ _ _
    ((AlgebraicGeometry.RingedSpace.overToRestricted X V).mapIso e).symm
    (Stacks.SheafOfModules.isInvertible_unit _ _)

/-- **A sheaf vanishing on an open vanishes on every smaller open.**  Restricting to `U` and
then to `V ≤ U` is restricting to `V`, and the second restriction is additive, so it carries a
zero object to a zero object. -/
public theorem isZero_restrict_of_le {X : RingedSpace.{u, u}} {V U : Opens X.carrier}
    (h : V ≤ U) (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))
    (hM : IsZero ((moduleRestriction X U).obj M)) :
    IsZero ((moduleRestriction X V).obj M) :=
  IsZero.of_iso ((StrictlyPerfect.restrictModulesOfLE.{u} h).map_isZero hM)
    ((StrictlyPerfect.restrictModulesOfLEIso.{u} h).symm.app M)

variable (X : RingedSpace.{u, u}) (U : Opens X.carrier)

/-- **`(I^{⊗ n} ⊗ M)|_U ≅ (I|_U)^{⊗ n} ⊗ M|_U` for every integer `n`.**  Restriction to an open
subspace commutes with the integer ideal powers of an invertible ideal sheaf, provided the
restriction of the ideal sheaf is again invertible. -/
public noncomputable def restrictIdealPowerTermIso
    (I : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))
    (hI : Stacks.SheafOfModules.IsInvertible X.presheaf (ringedSpaceIsSheaf X) I)
    (hIU : Stacks.SheafOfModules.IsInvertible (restrictToOpen X U).presheaf
      (ringedSpaceIsSheaf (restrictToOpen X U)) ((moduleRestriction X U).obj I))
    (n : ℤ) (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))) :
    (moduleRestriction X U).obj (@idealPowerTerm X I hI n M) ≅
      @idealPowerTerm (restrictToOpen X U) ((moduleRestriction X U).obj I) hIU n
        ((moduleRestriction X U).obj M) :=
  letI := hI
  letI := hIU
  letI := hI.toAlgebraicGeometry
  letI := hIU.toAlgebraicGeometry
  letI _h1 : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj
      I).IsEquivalence :=
    tensorRightFunctor_isEquivalence X.presheaf (ringedSpaceIsSheaf X) I
  letI _h2 : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      (restrictToOpen X U).sheaf).flip.obj
        ((moduleRestriction X U).obj I)).IsEquivalence :=
    tensorRightFunctor_isEquivalence (restrictToOpen X U).presheaf
      (ringedSpaceIsSheaf (restrictToOpen X U)) ((moduleRestriction X U).obj I)
  Stacks.Equivalence.powIntertwineObj
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj I).asEquivalence
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} (restrictToOpen X U).sheaf).flip.obj
      ((moduleRestriction X U).obj I)).asEquivalence
    (moduleRestriction X U)
    (fun M => restrictTensorSheafIso X U M I) n M

/-- **An ideal power of a sheaf vanishing on `U` vanishes on `U`.**  The restriction of
`I^{⊗ n} ⊗ M` to `U` is the `n`-th power of an autoequivalence applied to `M|_U`, and an
equivalence carries a zero object to a zero object. -/
public theorem isZero_restrict_idealPowerTerm
    (I : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))
    (hI : Stacks.SheafOfModules.IsInvertible X.presheaf (ringedSpaceIsSheaf X) I)
    (hIU : Stacks.SheafOfModules.IsInvertible (restrictToOpen X U).presheaf
      (ringedSpaceIsSheaf (restrictToOpen X U)) ((moduleRestriction X U).obj I))
    (n : ℤ) (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))
    (hM : IsZero ((moduleRestriction X U).obj M)) :
    IsZero ((moduleRestriction X U).obj (@idealPowerTerm X I hI n M)) :=
  let := hI
  let := hIU
  let := hIU.toAlgebraicGeometry
  let _h2 : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      (restrictToOpen X U).sheaf).flip.obj
        ((moduleRestriction X U).obj I)).IsEquivalence :=
    tensorRightFunctor_isEquivalence (restrictToOpen X U).presheaf
      (ringedSpaceIsSheaf (restrictToOpen X U)) ((moduleRestriction X U).obj I)
  IsZero.of_iso
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        (restrictToOpen X U).sheaf).flip.obj
          ((moduleRestriction X U).obj I)).asEquivalence ^ n).functor.map_isZero hM)
    (restrictIdealPowerTermIso X U I hI hIU n M)

/-- A fibre product whose two outer vertices are zero objects is a zero object: a map into the
fibre product is determined by its two components, and both land in zero objects. -/
private theorem isZero_pullback {C : Type*} [Category C] [HasZeroMorphisms C] {A P B : C}
    (f : A ⟶ P) (g : B ⟶ P) [HasPullback f g] (hA : IsZero A) (hB : IsZero B) :
    IsZero (pullback f g) :=
  (IsZero.iff_id_eq_zero _).mpr (pullback.hom_ext (hA.eq_of_tgt _ _) (hB.eq_of_tgt _ _))

/-- **A term of the décalage vanishing on an open.**  The degree-`n` term of `η_I F` restricts to
zero on `U` as soon as `F^n` and `F^{n+1}` do: it is the fibre product of two ideal powers of
those two terms, restriction to an open preserves that fibre product, and both outer vertices
restrict to zero. -/
public theorem isZero_restrict_etaTerm
    (I : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))
    (ι : I ⟶ SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))
    (hI : Stacks.SheafOfModules.IsInvertible X.presheaf (ringedSpaceIsSheaf X) I)
    (hIU : Stacks.SheafOfModules.IsInvertible (restrictToOpen X U).presheaf
      (ringedSpaceIsSheaf (restrictToOpen X U)) ((moduleRestriction X U).obj I))
    (F : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))) ℤ)
    (n : ℤ)
    (hn : IsZero ((moduleRestriction X U).obj (F.X n)))
    (hn1 : IsZero ((moduleRestriction X U).obj (F.X (n + 1)))) :
    IsZero ((moduleRestriction X U).obj (@etaTerm X I ι hI F n)) := by
  let _ := hI
  let _ := hIU
  have : PreservesFiniteLimits (moduleRestriction X U) :=
    AlgebraicGeometry.RingedSpace.restrictModules_preservesFiniteLimits X U
  refine IsZero.of_iso ?_ (PreservesPullback.iso (moduleRestriction X U) _ _)
  exact isZero_pullback _ _
    (isZero_restrict_idealPowerTerm X U I hI hIU n (F.X n) hn)
    (isZero_restrict_idealPowerTerm X U I hI hIU (n + 1) (F.X (n + 1)) hn1)

/-- **The décalage of a locally bounded complex is locally bounded.**  If every point of `X` has
an open neighbourhood outside a finite range of degrees on which the terms of `F` restrict to
zero, then the same holds for `η_I F`, with the range extended by one degree downwards.

The neighbourhood is shrunk to meet one on which `I` is trivial, which is what makes the ideal
powers of the two terms of `F` restrict to zero there; this is the local-boundedness component of
`Stacks.Chow.IsLocallyBoundedFiniteLocallyFree`, stated for the décalage. -/
public theorem isLocallyBounded_etaObj (X : RingedSpace.{u, u})
    [∀ x : X.carrier, IsLocalRing (ringStalk X x)]
    (I : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))
    (ι : I ⟶ SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))) (hι : Mono ι)
    (hI : Stacks.SheafOfModules.IsInvertible X.presheaf (ringedSpaceIsSheaf X) I)
    (F : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))) ℤ)
    (htf : ∀ n : ℤ, Stacks.IdealTorsion.IsIdealTorsionFree X ι (F.X n))
    (hlb : ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧ ∃ lo hi : ℤ, ∀ n : ℤ,
      (n < lo ∨ hi < n) → IsZero ((moduleRestriction X U).obj (F.X n)))
    (x : X.carrier) :
    ∃ U : Opens X.carrier, x ∈ U ∧ ∃ lo hi : ℤ, ∀ n : ℤ,
      (n < lo ∨ hi < n) →
        IsZero ((moduleRestriction X U).obj ((@etaObj X I ι hι hI F htf).X n)) := by
  obtain ⟨U, hxU, lo, hi, hbd⟩ := hlb x
  obtain ⟨W, hxW, hinv⟩ := exists_nhd_isInvertible_moduleRestriction X I hI x
  exact ⟨W ⊓ U, ⟨hxW, hxU⟩, lo - 1, hi, fun n hn =>
    isZero_restrict_etaTerm X (W ⊓ U) I ι hI (hinv (W ⊓ U) inf_le_left) F n
      (isZero_restrict_of_le inf_le_right _ (hbd n (by omega)))
      (isZero_restrict_of_le inf_le_right _ (hbd (n + 1) (by omega)))⟩

end Stacks.IdealTorsion.Eta

end
