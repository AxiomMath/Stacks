module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallDerivedInternalHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.RaisedHomRestriction
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomQuasiIsoGeneral
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionKInjectiveEssentiallySmall
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit

/-!
# The internal Hom complex at the module universe, locally

Let `X` be a ringed site whose objects form a type in a universe `c` while its morphisms, its
structure sheaf and its modules live in `u`, with `X.C` essentially `u`-small.  This file
records the local behaviour of the internal Hom complex `SheafHom^•(A, B)` with sections in
`Type u` (`AlgebraicGeometry.RingedSite.sheafHomComplexSmall`):

* its restriction to the slice over an object `U` is the internal Hom complex of the
  restrictions (the chain-level half of Stacks 08JB);
* out of a strictly perfect source it carries quasi-isomorphisms of targets to
  quasi-isomorphisms (Stacks 08JH).

## Main definitions

* `AlgebraicGeometry.RingedSite.sheafHomComplexSmallRestrictIso`: the restriction isomorphism.

## Main results

* `AlgebraicGeometry.RingedSite.homMapSmall_quasiIso_of_isStrictlyPerfect`: Stacks 08JH at the
  module universe.
* `AlgebraicGeometry.RingedSite.prop_sheafHomComplexSmall_X`: the terms of the internal Hom
  complex out of a strictly perfect complex inherit the properties of the terms of the target
  closed under isomorphisms, finite coproducts and retracts.

## References

* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe c u

namespace CategoryTheory.Functor.FullyFaithful

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  {F : C ⥤ D} [F.Additive] (hF : F.FullyFaithful)

/-- A complex is isomorphic to the lift of its own image along a fully faithful additive
functor, with the identity identifications. -/
def liftCochainComplexSelfIso (K : CochainComplex C ℤ) :
    K ≅ hF.liftCochainComplex ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) K.X
      (fun _ => Iso.refl _) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (fun i j _ => by simp [liftCochainComplex])

/-- An isomorphism of complexes of the form of `liftCochainComplex`, read as an isomorphism of
the lifted complexes. -/
def liftCochainComplexIsoOfIso {K K' : CochainComplex D ℤ} {Y Y' : ℤ → C}
    (e : ∀ n, F.obj (Y n) ≅ K.X n) (e' : ∀ n, F.obj (Y' n) ≅ K'.X n) (φ : K ≅ K') :
    hF.liftCochainComplex K Y e ≅ hF.liftCochainComplex K' Y' e' where
  hom := hF.liftCochainComplexMap e e' φ.hom
  inv := hF.liftCochainComplexMap e' e φ.inv
  hom_inv_id := by
    rw [← liftCochainComplexMap_comp, φ.hom_inv_id, liftCochainComplexMap_id]
  inv_hom_id := by
    rw [← liftCochainComplexMap_comp, φ.inv_hom_id, liftCochainComplexMap_id]

end CategoryTheory.Functor.FullyFaithful

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C]

/-- A slice of an essentially `u`-small site is essentially `u`-small. -/
local instance essentiallySmall_over_C (U : X.C) : EssentiallySmall.{u} (X.over U).C :=
  Stacks.essentiallySmall_over.{u} U

/-- **The internal Hom complex at the module universe commutes with restriction to a slice**:
the degreewise restriction of `SheafHom^•(A, B)` to the site over `U` is
`SheafHom^•(A|_U, B|_U)`. -/
def sheafHomComplexSmallRestrictIso
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) :
    restrictComplex X (sheafHomComplexSmall X A B) U ≅
      sheafHomComplexSmall (X.over U) (restrictComplex X A U) (restrictComplex X B U) := by
  let hF := Stacks.SheafOfModules.moduleULiftFullyFaithful.{max c u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)
  let C := restrictComplex X (sheafHomComplexSmall X A B) U
  let φ : ((Stacks.SheafOfModules.moduleULift.{max c u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C ≅
      (sheafHomComplex (X.over U) (restrictComplex X A U) (restrictComplex X B U)).obj :=
    ((SheafOfModules.overFunctor.{max c u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso (sheafHomComplexSmallIso X A B) ≪≫
      AlgebraicGeometry.RingedSite.Raised.sheafHomRestrictionComplexIso X U A B
  exact hF.liftCochainComplexSelfIso C ≪≫ hF.liftCochainComplexIsoOfIso _ _ φ

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{max c u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max c u}]
  [X.J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

/-- **Stacks 08JH at the module universe.** The internal Hom complex with sections in `Type u` out
of a strictly perfect complex carries a quasi-isomorphism of targets to a quasi-isomorphism. -/
theorem homMapSmall_quasiIso_of_isStrictlyPerfect
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) P)
    {F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (g : F ⟶ G) [QuasiIso g] : QuasiIso (homMapSmall X (𝟙 P) g) := by
  have := preservesHomology_moduleULift X
  exact (Functor.FullyFaithful.quasiIso_liftCochainComplexMap_iff _ _ _ _).2
    (General.homMap_quasiIso_of_isFiniteFreeSummand X g P hP.bounded
      (fun i => General.IsDirectSummandOfFiniteFree.isFiniteFreeSummand X
        (hP.termDirectSummand i)))

omit [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The terms of the internal Hom complex at the module universe out of a strictly perfect
complex.**  For a property `Pr` of `O`-modules closed under isomorphisms, finite coproducts and
retracts, the degree-`n` term of `SheafHom^•(P, N)` has property `Pr` as soon as the terms
`N^{p + n}` do for the degrees `p` in which `P` does not vanish: it is a retract of a finite
direct sum of copies of those terms. -/
theorem prop_sheafHomComplexSmall_X
    (Pr : ObjectProperty (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [Pr.IsClosedUnderIsomorphisms] [Pr.IsClosedUnderFiniteCoproducts]
    (hret : ∀ {M D : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
      (i : M ⟶ D) (r : D ⟶ M), i ≫ r = 𝟙 M → Pr D → Pr M)
    (P N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) P) (n : ℤ)
    (hN : ∀ p, ¬ IsZero (P.X p) → Pr (N.X (p + n))) :
    Pr ((sheafHomComplexSmall X P N).X n) := by
  obtain ⟨D, hD, ⟨ρ⟩⟩ := General.RetractOfLiftWith.sheafHomComplex_X Pr P N hP.bounded
    (fun i => General.IsDirectSummandOfFiniteFree.isFiniteFreeSummand X
      (hP.termDirectSummand i)) n hN
  let e := (HomologicalComplex.eval _ (ComplexShape.up ℤ) n).mapIso
    (sheafHomComplexSmallIso X P N)
  let hF := Stacks.SheafOfModules.moduleULiftFullyFaithful.{max c u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  refine hret (hF.preimage (e.hom ≫ ρ.i)) (hF.preimage (ρ.r ≫ e.inv)) ?_ hD
  apply hF.map_injective
  rw [Functor.map_comp, Functor.FullyFaithful.map_preimage, Functor.FullyFaithful.map_preimage,
    Category.assoc, ← Category.assoc ρ.i, ρ.retract, Category.id_comp, e.hom_inv_id,
    CategoryTheory.Functor.map_id]
  rfl

end AlgebraicGeometry.RingedSite

end
