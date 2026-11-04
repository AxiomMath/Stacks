module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.ConeOfAMorphism
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnit
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Pullback of strictly perfect complexes along a morphism of ringed topoi

Stacks 08H3 says that the pullback of a strictly perfect complex along a morphism of ringed
topoi is strictly perfect. This file supplies the functorial half of that statement: a
colimit-preserving functor between categories of sheaves of modules which carries the
structure sheaf to the structure sheaf carries finite free modules to finite free modules
(`freeMapIso`), hence direct summands of finite free modules to direct summands of finite
free modules (`isDirectSummandOfFiniteFree_map`), hence strictly perfect complexes to
strictly perfect complexes (`isStrictlyPerfect_map`).

It then applies that to the pullback of sheaves of modules along a morphism of ringed topoi
(`Stacks.Sheaves.RingedToposModules.pullbackModules`, Stacks 03D6 part (2)): clause (1) of
Stacks 08H3, the additivity needed before a functor can be applied degreewise to a complex,
is `pullbackModules_preservesZeroMorphisms`, and clause (2) is
`isStrictlyPerfect_pullbackModules`.

## Main definitions

* `Stacks.Sheaves.StrictlyPerfectPullback.freeMapIso`: a colimit-preserving functor between
  categories of sheaves of modules which carries the structure sheaf to the structure sheaf
  carries `O^{⊕n}` to `O^{⊕n}`.

## Main results

* `Stacks.Sheaves.StrictlyPerfectPullback.isDirectSummandOfFiniteFree_map` and
  `Stacks.Sheaves.StrictlyPerfectPullback.isStrictlyPerfect_map`: such a functor preserves
  the two clauses of strict perfectness.
* `Stacks.Sheaves.StrictlyPerfectPullback.pullbackModules_preservesZeroMorphisms`: pullback
  of sheaves of modules along a morphism of ringed topoi preserves zero morphisms, being a
  left adjoint. This is clause (1) of Stacks 08H3.
* `Stacks.Sheaves.StrictlyPerfectPullback.isStrictlyPerfect_pullbackModules`: the degreewise
  pullback of a strictly perfect complex is strictly perfect. This is clause (2) of
  Stacks 08H3.

## Implementation notes

`IsStrictlyPerfect` and `IsDirectSummandOfFiniteFree` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/StrictlyPerfect/ConeOfAMorphism.lean`, which carry
Stacks 08FL, are stated for a sheaf of
rings in `RingCat.{0}` and sheaves of modules in the corresponding module universe, so the
statements below are at that universe; the sites themselves stay at arbitrary universes.

The one mathematical input of Stacks 08H3 that is not formal is the identification of the
pullback of the structure sheaf with the structure sheaf, `f^*O_Y ≅ O_X`. It is supplied by
`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso`, which proves it by
corepresentability: global sections are preserved by a direct image because the inverse image
of a morphism of topoi preserves the terminal sheaf.
-/

@[expose] public section

open CategoryTheory Limits

universe v u v' u'

namespace Stacks.Sheaves.StrictlyPerfectPullback

section Functorial

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  (R : Sheaf J RingCat.{0}) (S : Sheaf K RingCat.{0})
  [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  [HasWeakSheafify K AddCommGrpCat.{0}] [K.WEqualsLocallyBijective AddCommGrpCat.{0}]
  (F : SheafOfModules.{0} R ⥤ SheafOfModules.{0} S)
  (η : SheafOfModules.unit S ≅ F.obj (SheafOfModules.unit R))

/-- A colimit-preserving functor between categories of sheaves of modules which carries the
structure sheaf to the structure sheaf carries the finite free module `O^{⊕n}` to `O^{⊕n}`.
Both sides are the coproduct of `n` copies of the structure sheaf, and a left adjoint
commutes with that coproduct. -/
noncomputable def freeMapIso [PreservesColimitsOfSize.{0, 0} F] (n : ℕ) :
    SheafOfModules.free (R := S) (ULift.{0} (Fin n)) ≅
      F.obj (SheafOfModules.free (R := R) (ULift.{0} (Fin n))) :=
  (SheafOfModules.isColimitFreeCofan (R := S) (ULift.{0} (Fin n))).coconePointsIsoOfNatIso
    (isColimitOfPreserves F (SheafOfModules.isColimitFreeCofan (R := R) (ULift.{0} (Fin n))))
    (Discrete.natIso fun _ ↦ η)

include η in
/-- Such a functor carries a direct summand of a finite free module to a direct summand of a
finite free module: a retraction of `M` off `O^{⊕n}` is carried to a retraction of `F M` off
`F (O^{⊕n})`, which is `O^{⊕n}` by `freeMapIso`. -/
lemma isDirectSummandOfFiniteFree_map [PreservesColimitsOfSize.{0, 0} F]
    {M : SheafOfModules.{0} R} (hM : IsDirectSummandOfFiniteFree R M) :
    IsDirectSummandOfFiniteFree S (F.obj M) := by
  obtain ⟨n, i, r, hir⟩ := (isDirectSummandOfFiniteFree_iff_free R M).mp hM
  refine (isDirectSummandOfFiniteFree_iff_free S (F.obj M)).mpr
    ⟨n, F.map i ≫ (freeMapIso R S F η n).inv, (freeMapIso R S F η n).hom ≫ F.map r, ?_⟩
  rw [Category.assoc, ← Category.assoc (freeMapIso R S F η n).inv, Iso.inv_hom_id,
    Category.id_comp, ← F.map_comp, hir, F.map_id]

include η in
/-- Such a functor carries a strictly perfect complex to a strictly perfect complex. The
boundedness clause holds because a functor preserving zero morphisms carries a zero object to
a zero object, and the term clause is `isDirectSummandOfFiniteFree_map`. -/
lemma isStrictlyPerfect_map [PreservesColimitsOfSize.{0, 0} F] [F.PreservesZeroMorphisms]
    {E : CochainComplex (SheafOfModules.{0} R) ℤ} (hE : IsStrictlyPerfect R E) :
    IsStrictlyPerfect S ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj E) := by
  refine ⟨hE.bounded.subset fun i hi hzero ↦ hi ?_,
    fun i ↦ isDirectSummandOfFiniteFree_map R S F η (hE.termDirectSummand i)⟩
  simpa only [Functor.mapHomologicalComplex_obj_X] using F.map_isZero hzero

end Functorial

section RingedTopos

open Stacks.Sheaves.RingedToposModules AlgebraicGeometry

variable {X : RingedTopos.{v, u, 0}} {Y : RingedTopos.{v', u', 0}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{0} RingCat.{0})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{0} RingCat.{0})]
  [X.J.HasSheafCompose (forget RingCat.{0})] [Y.J.HasSheafCompose (forget RingCat.{0})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{0})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{0})]
  [HasWeakSheafify X.J AddCommGrpCat.{0}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  [HasWeakSheafify Y.J AddCommGrpCat.{0}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  (f : RingedToposHom X Y)

omit [HasWeakSheafify Y.J AddCommGrpCat.{0}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{0}] in
/-- **Stacks 08H3, the additivity clause.** Pullback of sheaves of modules along a morphism
of ringed topoi preserves zero morphisms, being a left adjoint. This is what lets the functor
be applied degreewise to a complex. -/
@[stacks 08H3 "additivity of pullback"]
theorem pullbackModules_preservesZeroMorphisms :
    (f.pullbackModules).PreservesZeroMorphisms := by
  have : (f.pullbackModules).IsLeftAdjoint := (pullbackAdjPushforwardModules f).isLeftAdjoint
  infer_instance

/-- **Stacks 08H3, the strict-perfectness clause.** The degreewise pullback of a strictly
perfect complex of `O_Y`-modules along a morphism of ringed topoi is a strictly perfect complex
of `O_X`-modules. -/
@[stacks 08H3 "strict perfectness of the pullback complex"]
theorem isStrictlyPerfect_pullbackModules
    (E : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hE : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) E) :
    letI := pullbackModules_preservesZeroMorphisms f
    IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (((f.pullbackModules).mapHomologicalComplex (ComplexShape.up ℤ)).obj E) := by
  let := pullbackModules_preservesZeroMorphisms f
  let : PreservesColimitsOfSize.{0, 0} (f.pullbackModules) :=
    (pullbackAdjPushforwardModules f).leftAdjoint_preservesColimits
  exact isStrictlyPerfect_map (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f.pullbackModules
    (pullbackModulesObjUnitIso f) hE

end RingedTopos

end Stacks.Sheaves.StrictlyPerfectPullback

end
