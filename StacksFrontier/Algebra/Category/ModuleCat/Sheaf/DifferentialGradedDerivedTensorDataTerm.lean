module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPullbackTensorFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedGoodModuleDataConstruction

/-!
# The derived pullback-tensor functor, with its value on a good module on the nose

`SheafOfModules.DifferentialGradedModule.DerivedTensorData` is the form in which the derived
tensor product and the derived pullback enter the statements of Tags 0FTG, 0FTH, 0FTI and the
quasi-coherence tags: a functor `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` of differential graded modules, a functor of
the derived categories, and the clause `ComputesOnGood` pinning the value of the second on a
good module to be the image of the first. That clause asks for an *equality* of objects of the
derived category, so a left derived functor — a right Kan extension, whose value is a limit and
therefore determined only up to canonical isomorphism — does not satisfy it as it stands, and no
term of `DerivedTensorData` existed.

This file builds one. The derived pullback-tensor functor of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedDerivedPullbackTensorFunctor.lean`
is isomorphic, at the image of a good module, to the image of `f^*𝒫 ⊗_𝒜 𝒩`; transporting the
functor along that isomorphism — `CategoryTheory.Functor.copyObj`, which replaces the object
map of a functor by any map isomorphic to it — produces an isomorphic functor whose value at
the image of a good module *is* the image of `f^*𝒫 ⊗_𝒜 𝒩`. Its compatibility with
homomorphisms of good modules is naturality of the counit, transported the same way.

The transport is available because an object of `derivedCategory A` is a right differential
graded `A`-module: formally inverting arrows leaves the objects alone, so
`derivedCategoryModule A X` reads the module off and `X` is the image of it on the nose. The
object map of the transported functor is therefore defined by a case split on whether the module
represented by the object is good.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.rigidDerivedPullbackTensor` is the derived
  pullback-tensor functor `D(ℬ, d) ⥤ D(𝒜', d)` with its value at the image of a good right
  differential graded `ℬ`-module `𝒫` taken to be the image of `f^*𝒫 ⊗_𝒜 𝒩` on the nose.
* `SheafOfModules.DifferentialGradedModule.derivedTensorData` is the resulting term of
  `DerivedTensorData`, for the flat-resolution theories carried on the two derived categories.

## Main results

* `SheafOfModules.DifferentialGradedModule.isoRigidDerivedPullbackTensor`: the transported
  functor is isomorphic to `derivedPullbackTensor`, so every result about the latter — that it
  is the left derived functor, the uniqueness up to a unique compatible isomorphism, the
  composition of Tag 0FTI — transfers to it.
* `SheafOfModules.DifferentialGradedModule.rigidDerivedPullbackTensor_obj_of_isGood` and
  `rigidDerivedPullbackTensor_map_of_isGood`: the two clauses of `ComputesOnGood`.
* `SheafOfModules.DifferentialGradedModule.computesOnGood_rigidDerivedPullbackTensor`: those two
  clauses assembled, for any flat-resolution theory carried on the derived category whose
  localization functor is the canonical one.

## Implementation notes

**Why a transport and not a different construction.** The value of a right Kan extension at an
object is a limit; there is no equality of objects of `D(𝒜', d)` to be had from it, and the
isomorphism it does give is the mathematical content. Rigidifying a functor by a choice of
object map isomorphic to its own is the standard way to turn such an isomorphism into an
equality, and it changes nothing: `isoRigidDerivedPullbackTensor` identifies the two functors.

**Why not `CategoryTheory.Localization.Construction.lift`.** The derived category here is
`(quasiIsomorphisms B).Localization`, Mathlib's strict quotient-of-paths construction, and for
a functor `G` out of `K(Mod(ℬ, d))` which inverts *every* quasi-isomorphism that construction
supplies a lift with `Construction.fac : W.Q ⋙ lift G hG = G` a strict equality of functors —
from which `ComputesOnGood.obj_eq` would follow on the nose, with no transport. That route is
unavailable here, and not by accident. `Construction.lift` asks for
`W.IsInvertedBy G`; what the functor of Tag 0FTE satisfies is
`isIso_pullbackTensor_map_of_objectProperty`, which needs *both* endpoints to be images of
good modules. A functor inverting every quasi-isomorphism would have nothing to derive — its
left derived functor would be that strict lift — so the gap between the two hypotheses is
exactly the reason a derived functor is being built at all. Nor can an everywhere-inverting
`G` agreeing with this one on good modules be manufactured: that needs a *functorial* good
resolution, and Tag 0FSH provides existence, not a functor. So the strict-lift technique and
the rigidification here apply to disjoint situations, and neither supersedes the other.

**Nothing new is assumed.** The inputs are those of Tag 0FTF — the pullback datum and its
differential graded extension, the tensor datum, the good resolutions and the exactness datum —
together with the flat-resolution theories of the two derived categories, which
`GoodModuleData.ofLeftTensor` builds from the same ingredients. In particular `DerivedTensorData`
is no longer an independent hypothesis of the tags that take it.

## References

* [Stacks Project, Tag 0FTF](https://stacks.math.columbia.edu/tag/0FTF)
* [Stacks Project, Tag 0FTG](https://stacks.math.columbia.edu/tag/0FTG)
* [Stacks Project, Tag 0FTE](https://stacks.math.columbia.edu/tag/0FTE)
* [Stacks Project, Tag 0FT5](https://stacks.math.columbia.edu/tag/0FT5)
-/

@[expose] public section

open CategoryTheory

universe t a a' m m' s z v u v' u'

namespace SheafOfModules

namespace DifferentialGradedModule

section Rigid

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}
  [HasSheafify J AddCommGrpCat.{s}] [J.WEqualsLocallyBijective AddCommGrpCat.{s}]
  [HasSheafify J' AddCommGrpCat.{m'}] [J'.WEqualsLocallyBijective AddCommGrpCat.{m'}]
  {u : C' ⥤ C} {σ : R'.obj ⟶ u.op ⋙ R.obj}
  {A A' : DifferentialGradedAlgebra.{t, a} R} {B : DifferentialGradedAlgebra.{t, a'} R'}
  {φ : DifferentialGradedAlgebra.SemilinearHom u σ B A}
  {N : DifferentialGradedBimodule.{t, a, z} A A'}
  {P : PullbackData.{t, a, m, v, u, a', m'} φ}
  {D : TensorFunctorData.{t, a, m, z, s} A A' N}
  {g : GoodResolutionData.{t, a', m', v', u'} B}
  [(quasiIsomorphisms.{t, a', m'} B).HasRightCalculusOfFractions]

/-- Naturality of the identification of the value of the derived pullback-tensor functor at a
good module, written as a conjugation: conjugating the derived functor by the identifications at
the two ends gives the image of `f^*ψ ⊗_𝒜 1`. -/
@[reassoc]
theorem derivedPullbackTensorObjIso_inv_map_hom (E : P.HomotopyExtension)
    (hE : PullbackTensorExactnessData P D g)
    {Q Q₂ : DifferentialGradedModule.{t, a', m'} B} (hQ : g.IsGood Q) (hQ₂ : g.IsGood Q₂)
    (ψ : Q ⟶ Q₂) :
    (derivedPullbackTensorObjIso E hE hQ).inv ≫
        (derivedPullbackTensor E hE).map
          ((toDerivedCategory B).map ((HomotopyCategory.quotient B).map ψ)) ≫
          (derivedPullbackTensorObjIso E hE hQ₂).hom =
      (toDerivedCategory.{t, a, s} A').map
        ((HomotopyCategory.quotient A').map ((pullbackTensorFunctor P D).map ψ)) := by
  rw [Iso.inv_comp_eq]
  exact derivedPullbackTensorObjIso_naturality E hE hQ hQ₂ ψ

/-- The object map of the rigidified derived pullback-tensor functor: at an object of
`D(ℬ, d)` representing a good right differential graded `ℬ`-module `𝒫` it is the image of
`f^*𝒫 ⊗_𝒜 𝒩`, and elsewhere it is the value of `derivedPullbackTensor`. -/
noncomputable def rigidDerivedPullbackTensorObj (E : P.HomotopyExtension)
    (hE : PullbackTensorExactnessData P D g)
    (Good : DifferentialGradedModule.{t, a', m'} B → Prop) :
    derivedCategory.{t, a', m'} B → derivedCategory.{t, a, s} A' := fun X =>
  @dite _ (Good (derivedCategoryModule B X)) (Classical.dec _)
    (fun _ => (toDerivedCategory.{t, a, s} A').obj ((HomotopyCategory.quotient A').obj
      ((pullbackTensorFunctor P D).obj (derivedCategoryModule B X))))
    (fun _ => (derivedPullbackTensor E hE).obj X)

/-- At the image of a good right differential graded `ℬ`-module the object map is the image of
`f^*𝒫 ⊗_𝒜 𝒩`. -/
theorem rigidDerivedPullbackTensorObj_of_good (E : P.HomotopyExtension)
    (hE : PullbackTensorExactnessData P D g)
    (Good : DifferentialGradedModule.{t, a', m'} B → Prop)
    {Q : DifferentialGradedModule.{t, a', m'} B} (hQ : Good Q) :
    rigidDerivedPullbackTensorObj E hE Good
        ((toDerivedCategory B).obj ((HomotopyCategory.quotient B).obj Q)) =
      (toDerivedCategory.{t, a, s} A').obj
        ((HomotopyCategory.quotient A').obj ((pullbackTensorFunctor P D).obj Q)) :=
  dif_pos hQ

/-- Away from the good modules the object map is the value of `derivedPullbackTensor`. -/
theorem rigidDerivedPullbackTensorObj_of_not_good (E : P.HomotopyExtension)
    (hE : PullbackTensorExactnessData P D g)
    (Good : DifferentialGradedModule.{t, a', m'} B → Prop)
    {X : derivedCategory.{t, a', m'} B} (hX : ¬ Good (derivedCategoryModule B X)) :
    rigidDerivedPullbackTensorObj E hE Good X = (derivedPullbackTensor E hE).obj X :=
  dif_neg hX

/-- The isomorphism between the derived pullback-tensor functor and the object map above: the
counit at a good module, and the identity elsewhere. -/
noncomputable def rigidDerivedPullbackTensorObjIso (E : P.HomotopyExtension)
    (hE : PullbackTensorExactnessData P D g)
    (Good : DifferentialGradedModule.{t, a', m'} B → Prop)
    (hGood : ∀ Q : DifferentialGradedModule.{t, a', m'} B, Good Q → g.IsGood Q)
    (X : derivedCategory.{t, a', m'} B) :
    (derivedPullbackTensor E hE).obj X ≅ rigidDerivedPullbackTensorObj E hE Good X :=
  @dite _ (Good (derivedCategoryModule B X)) (Classical.dec _)
    (fun h => derivedPullbackTensorObjIso E hE (hGood _ h) ≪≫
      eqToIso (rigidDerivedPullbackTensorObj_of_good E hE Good h).symm)
    (fun h => eqToIso (rigidDerivedPullbackTensorObj_of_not_good E hE Good h).symm)

/-- At the image of a good right differential graded `ℬ`-module that isomorphism is the
counit. -/
theorem rigidDerivedPullbackTensorObjIso_of_good (E : P.HomotopyExtension)
    (hE : PullbackTensorExactnessData P D g)
    (Good : DifferentialGradedModule.{t, a', m'} B → Prop)
    (hGood : ∀ Q : DifferentialGradedModule.{t, a', m'} B, Good Q → g.IsGood Q)
    {Q : DifferentialGradedModule.{t, a', m'} B} (hQ : Good Q) :
    rigidDerivedPullbackTensorObjIso E hE Good hGood
        ((toDerivedCategory B).obj ((HomotopyCategory.quotient B).obj Q)) =
      derivedPullbackTensorObjIso E hE (hGood _ hQ) ≪≫
        eqToIso (rigidDerivedPullbackTensorObj_of_good E hE Good hQ).symm :=
  dif_pos hQ

/-- **The rigidified derived pullback-tensor functor** `D(ℬ, d) ⥤ D(𝒜', d)`: the derived
pullback-tensor functor with its object map replaced by the isomorphic one above, so that its
value at the image of a good right differential graded `ℬ`-module `𝒫` is the image of
`f^*𝒫 ⊗_𝒜 𝒩` on the nose. -/
noncomputable def rigidDerivedPullbackTensor (E : P.HomotopyExtension)
    (hE : PullbackTensorExactnessData P D g)
    (Good : DifferentialGradedModule.{t, a', m'} B → Prop)
    (hGood : ∀ Q : DifferentialGradedModule.{t, a', m'} B, Good Q → g.IsGood Q) :
    derivedCategory.{t, a', m'} B ⥤ derivedCategory.{t, a, s} A' :=
  (derivedPullbackTensor E hE).copyObj (rigidDerivedPullbackTensorObj E hE Good)
    (rigidDerivedPullbackTensorObjIso E hE Good hGood)

/-- The rigidified functor is isomorphic to the derived pullback-tensor functor, so every
result about the latter transfers to it. -/
noncomputable def isoRigidDerivedPullbackTensor (E : P.HomotopyExtension)
    (hE : PullbackTensorExactnessData P D g)
    (Good : DifferentialGradedModule.{t, a', m'} B → Prop)
    (hGood : ∀ Q : DifferentialGradedModule.{t, a', m'} B, Good Q → g.IsGood Q) :
    derivedPullbackTensor E hE ≅ rigidDerivedPullbackTensor E hE Good hGood :=
  (derivedPullbackTensor E hE).isoCopyObj _ _

/-- The counit of the rigidified functor: the identification with `derivedPullbackTensor`
followed by that functor's counit. -/
noncomputable def rigidDerivedPullbackTensorCounit (E : P.HomotopyExtension)
    (hE : PullbackTensorExactnessData P D g)
    (Good : DifferentialGradedModule.{t, a', m'} B → Prop)
    (hGood : ∀ Q : DifferentialGradedModule.{t, a', m'} B, Good Q → g.IsGood Q) :
    toDerivedCategory B ⋙ rigidDerivedPullbackTensor E hE Good hGood ⟶
      HomotopyCategory.pullbackTensor E D ⋙ toDerivedCategory A' :=
  Functor.whiskerLeft (toDerivedCategory B)
      (isoRigidDerivedPullbackTensor E hE Good hGood).inv ≫
    derivedPullbackTensorCounit E hE

/-- At a good right differential graded `ℬ`-module the counit of the rigidified functor is an
isomorphism: it is an isomorphism of functors followed by the counit of
`derivedPullbackTensor`, which is invertible there. -/
theorem isIso_rigidDerivedPullbackTensorCounit_app_of_isGood (E : P.HomotopyExtension)
    (hE : PullbackTensorExactnessData P D g)
    (Good : DifferentialGradedModule.{t, a', m'} B → Prop)
    (hGood : ∀ Q : DifferentialGradedModule.{t, a', m'} B, Good Q → g.IsGood Q)
    {Q : DifferentialGradedModule.{t, a', m'} B} (hQ : g.IsGood Q) :
    IsIso ((rigidDerivedPullbackTensorCounit E hE Good hGood).app
      ((HomotopyCategory.quotient B).obj Q)) := by
  have := isIso_derivedPullbackTensorCounit_app_of_isGood E hE hQ
  rw [rigidDerivedPullbackTensorCounit]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  infer_instance

/-- The statement of Tag 0FTF for a pullback and a tensor product given by their universal
properties and an exactness package; the tag itself is registered on
`SheafOfModules.DifferentialGradedModule.isLeftDerived_derivedPullbackTensorRingedTopos`,
along a morphism of ringed topoi. The functor `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` of Tag 0FTE, followed by the
localization functor `K(Mod(𝒜', d)) → D(𝒜', d)`, has a left derived extension
`D(ℬ, d) ⥤ D(𝒜', d)` whose value on a good right differential graded `ℬ`-module `𝒫` is
`f^*𝒫 ⊗_𝒜 𝒩`. The extension is
`rigidDerivedPullbackTensor`, a right Kan extension along the localization functor
`K(Mod(ℬ, d)) → D(ℬ, d)`, and its value on a good module is that image on the nose. -/
theorem exists_leftDerivedExtension_pullbackTensor (E : P.HomotopyExtension)
    (hE : PullbackTensorExactnessData P D g) :
    ∃ (Λ : derivedCategory.{t, a', m'} B ⥤ derivedCategory.{t, a, s} A')
      (β : toDerivedCategory B ⋙ Λ ⟶
        HomotopyCategory.pullbackTensor E D ⋙ toDerivedCategory A'),
      Λ.IsLeftDerivedFunctor β (quasiIsomorphisms.{t, a', m'} B) ∧
        ∀ Q : DifferentialGradedModule.{t, a', m'} B, g.IsGood Q →
          Λ.obj ((toDerivedCategory B).obj ((HomotopyCategory.quotient B).obj Q)) =
            (toDerivedCategory.{t, a, s} A').obj ((HomotopyCategory.quotient A').obj
              ((pullbackTensorFunctor P D).obj Q)) :=
  ⟨rigidDerivedPullbackTensor E hE g.IsGood fun _ hQ => hQ,
    rigidDerivedPullbackTensorCounit E hE g.IsGood fun _ hQ => hQ,
    isLeftDerivedFunctor_of_isIso_app_of_isGood E hE _ _
      (fun _ hQ => isIso_rigidDerivedPullbackTensorCounit_app_of_isGood E hE _ _ hQ),
    fun _ hQ => rigidDerivedPullbackTensorObj_of_good E hE g.IsGood hQ⟩

/-- On arrows the rigidified functor is the derived pullback-tensor functor read through the
isomorphism of object maps. -/
theorem rigidDerivedPullbackTensor_map (E : P.HomotopyExtension)
    (hE : PullbackTensorExactnessData P D g)
    (Good : DifferentialGradedModule.{t, a', m'} B → Prop)
    (hGood : ∀ Q : DifferentialGradedModule.{t, a', m'} B, Good Q → g.IsGood Q)
    {X Y : derivedCategory.{t, a', m'} B} (f : X ⟶ Y) :
    (rigidDerivedPullbackTensor E hE Good hGood).map f =
      (rigidDerivedPullbackTensorObjIso E hE Good hGood X).inv ≫
        (derivedPullbackTensor E hE).map f ≫
          (rigidDerivedPullbackTensorObjIso E hE Good hGood Y).hom :=
  rfl

/-- **The compatibility clause of Tag 0FTF.** On the image of a homomorphism of good right
differential graded `ℬ`-modules the rigidified functor is the image of `f^*ψ ⊗_𝒜 1`, read
through the two identifications of its value. This is naturality of the counit. -/
theorem rigidDerivedPullbackTensor_map_of_isGood (E : P.HomotopyExtension)
    (hE : PullbackTensorExactnessData P D g)
    (Good : DifferentialGradedModule.{t, a', m'} B → Prop)
    (hGood : ∀ Q : DifferentialGradedModule.{t, a', m'} B, Good Q → g.IsGood Q)
    {Q Q₂ : DifferentialGradedModule.{t, a', m'} B} (hQ : Good Q) (hQ₂ : Good Q₂) (ψ : Q ⟶ Q₂) :
    (rigidDerivedPullbackTensor E hE Good hGood).map
          ((toDerivedCategory B).map ((HomotopyCategory.quotient B).map ψ)) =
      eqToHom (rigidDerivedPullbackTensorObj_of_good E hE Good hQ) ≫
        (toDerivedCategory.{t, a, s} A').map ((HomotopyCategory.quotient A').map
          ((pullbackTensorFunctor P D).map ψ)) ≫
          eqToHom (rigidDerivedPullbackTensorObj_of_good E hE Good hQ₂).symm := by
  show (rigidDerivedPullbackTensorObjIso E hE Good hGood _).inv ≫
      (derivedPullbackTensor E hE).map _ ≫
        (rigidDerivedPullbackTensorObjIso E hE Good hGood _).hom = _
  rw [rigidDerivedPullbackTensorObjIso_of_good E hE Good hGood hQ,
    rigidDerivedPullbackTensorObjIso_of_good E hE Good hGood hQ₂]
  simp only [Iso.trans_inv, Iso.trans_hom, eqToIso.inv, eqToIso.hom, Category.assoc,
    derivedPullbackTensorObjIso_inv_map_hom_assoc E hE (hGood _ hQ) (hGood _ hQ₂) ψ]

end Rigid

/-! ### The term of `DerivedTensorData` -/

section Term

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}
  [HasSheafify J AddCommGrpCat.{s}] [J.WEqualsLocallyBijective AddCommGrpCat.{s}]
  [HasSheafify J' AddCommGrpCat.{m'}] [J'.WEqualsLocallyBijective AddCommGrpCat.{m'}]
  {u : C' ⥤ C} {σ : R'.obj ⟶ u.op ⋙ R.obj}
  {A A' : DifferentialGradedAlgebra.{t, a} R} {B : DifferentialGradedAlgebra.{t, a'} R'}
  {φ : DifferentialGradedAlgebra.SemilinearHom u σ B A}
  {N : DifferentialGradedBimodule.{t, a, z} A A'}
  {P : PullbackData.{t, a, m, v, u, a', m'} φ}
  {D : TensorFunctorData.{t, a, m, z, s} A A' N}
  {g : GoodResolutionData.{t, a', m', v', u'} B}
  [(quasiIsomorphisms.{t, a', m'} B).HasRightCalculusOfFractions]
  {gB : GoodModuleData.{t, a', m', v', u'} B (derivedCategory.{t, a', m'} B)}
  {gA' : GoodModuleData.{t, a, s, v, u} A' (derivedCategory.{t, a, s} A')}

/-- **The two clauses of `ComputesOnGood` for the rigidified derived pullback-tensor functor.**
For flat-resolution theories carried on the two derived categories whose localization functors
are the canonical ones, the rigidified functor takes the image of a good right differential
graded `ℬ`-module `𝒫` to the image of `f^*𝒫 ⊗_𝒜 𝒩`, compatibly with homomorphisms. -/
theorem computesOnGood_rigidDerivedPullbackTensor
    (E : P.HomotopyExtension) (hE : PullbackTensorExactnessData P D g)
    (hlocB : gB.localization = toDerivedCategory.{t, a', m'} B)
    (hlocA' : gA'.localization = toDerivedCategory.{t, a, s} A')
    (hGood : ∀ Q : DifferentialGradedModule.{t, a', m'} B, gB.IsGood Q → g.IsGood Q) :
    ComputesOnGood gB gA' (pullbackTensorFunctor P D)
      (rigidDerivedPullbackTensor E hE gB.IsGood hGood) := by
  obtain ⟨locB, hiB, hmB, goodB, ltB, ltaB, egB⟩ := gB
  obtain ⟨locA', hiA', hmA', goodA', ltA', ltaA', egA'⟩ := gA'
  subst hlocB
  subst hlocA'
  exact
    { obj_eq := fun hQ => rigidDerivedPullbackTensorObj_of_good E hE _ hQ
      map_eq := fun hQ hQ₂ ψ => rigidDerivedPullbackTensor_map_of_isGood E hE _ hGood hQ hQ₂ ψ }

/-- **A term of `DerivedTensorData`**: the derived tensor product `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` of Tags
0FTF and 0FTG, as the structure in which the derived-category statements of this development
take it. The functor of differential graded modules is the functor of Tag 0FTE, the functor of
derived categories is the rigidified derived pullback-tensor functor, and the clause pinning the
value on a good module is proved. -/
noncomputable def derivedTensorData
    (E : P.HomotopyExtension) (hE : PullbackTensorExactnessData P D g)
    (hlocB : gB.localization = toDerivedCategory.{t, a', m'} B)
    (hlocA' : gA'.localization = toDerivedCategory.{t, a, s} A')
    (hGood : ∀ Q : DifferentialGradedModule.{t, a', m'} B, gB.IsGood Q → g.IsGood Q) :
    DerivedTensorData gB gA' where
  moduleFunctor := pullbackTensorFunctor P D
  derived := rigidDerivedPullbackTensor E hE gB.IsGood hGood
  computes := computesOnGood_rigidDerivedPullbackTensor E hE hlocB hlocA' hGood

/-- The functor of differential graded modules carried by `derivedTensorData` is the functor of
Tag 0FTE. -/
@[simp]
theorem derivedTensorData_moduleFunctor
    (E : P.HomotopyExtension) (hE : PullbackTensorExactnessData P D g)
    (hlocB : gB.localization = toDerivedCategory.{t, a', m'} B)
    (hlocA' : gA'.localization = toDerivedCategory.{t, a, s} A')
    (hGood : ∀ Q : DifferentialGradedModule.{t, a', m'} B, gB.IsGood Q → g.IsGood Q) :
    (derivedTensorData E hE hlocB hlocA' hGood).moduleFunctor = pullbackTensorFunctor P D :=
  rfl

/-- The functor of derived categories carried by `derivedTensorData` is the rigidified derived
pullback-tensor functor, hence isomorphic to `derivedPullbackTensor`. -/
@[simp]
theorem derivedTensorData_derived
    (E : P.HomotopyExtension) (hE : PullbackTensorExactnessData P D g)
    (hlocB : gB.localization = toDerivedCategory.{t, a', m'} B)
    (hlocA' : gA'.localization = toDerivedCategory.{t, a, s} A')
    (hGood : ∀ Q : DifferentialGradedModule.{t, a', m'} B, gB.IsGood Q → g.IsGood Q) :
    (derivedTensorData E hE hlocB hlocA' hGood).derived =
      rigidDerivedPullbackTensor E hE gB.IsGood hGood :=
  rfl

end Term

end DifferentialGradedModule

end SheafOfModules

end
