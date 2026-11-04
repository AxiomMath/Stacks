module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitStepThree
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitStepTwo
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleEtaleBaseChangeUnitSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardBaseChangeCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleSetSheafCommutation
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictExtensionByZero
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompTransport

/-!
# The forgetful functor on the unit of the étale module-pullback adjunction

Let `h : U ⟶ V` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  `AlgebraicGeometry.Space.etaleModulePullbackAdjunction` is the adjunction of
Stacks 03LU read through the identification of Stacks 03LW — étale restriction of modules is
left adjoint to the direct image — and
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` is the corresponding adjunction of
Stacks 03LP for sheaves of *sets* on the small étale sites.  The forgetful functor
`CategoryTheory.Sheaf.moduleSheafFunctor` carries the first pair of functors to the second on
the nose, by the two `rfl` lemmas of
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleSetSheafCommutation.lean`.  This file proves that it
also carries the **unit** of the first adjunction to the unit of the second.

That statement is what the modules-over-sets cube of
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleHigherPushforwardBaseChangeCanonical.lean` was
missing: with it the comparison of the two horizontal left adjoints of that cube has the
identity 2-square as its mate, and
`Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms` carries Stacks 03LR,
part (1) for sheaves of sets on the small étale sites to the module statement.

## Main results

* `AlgebraicGeometry.Space.moduleSheafFunctor_map_pullbackAdjPushforwardModules_unit_app`: the
  forgetful functor carries the unit of the Stacks 03D7 adjunction for the morphism of small
  étale ringed topoi to the transpose of its change-of-rings half.  The corresponding statement
  for the untransported adjunction of Stacks 03LU is
  `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePullbackAdjunction_unit_app`
  (`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackUnitStepTwo.lean`), which this file
  uses rather than restates; where the composite spelling of its `homEquiv` is wanted,
  `CategoryTheory.Adjunction.homEquiv_unit` supplies it at the point of use.
* `AlgebraicGeometry.Space.mateEquiv_moduleSheafFunctor_modulePullbackIso`: **the mate of the
  forgetful image of the comparison of Stacks 03LW is the identity 2-square**, which is the
  τ-face of the modules-over-sets cube.
* `AlgebraicGeometry.Space.pullbackScalarUnit_comp_moduleSheafFunctor_map_modulePullbackIso`:
  the change-of-rings half, followed by the comparison of Stacks 03LW on underlying sheaves of
  sets, is the comparison `AlgebraicGeometry.Space.smallToposMorphismTypeU_inverseImageIso` of
  Stacks 03LQ.  This is where
  `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_unit_app` — the canonicity of
  Stacks 03LW on sections — enters, and it is the only genuinely geometric input.

Two generalities are stated in `Stacks.Sheaves.RingedToposModules`, at a variable sheaf of
rings: `moduleSheafFunctor_map_comp_restrictScalars` and `moduleSheafFunctor_map_eq_of_val_app`.

## Implementation notes

**Every step is its own declaration, and the spelling of each intermediate composite is
pinned.**  The two commutation lemmas of
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleSetSheafCommutation.lean` make
`moduleSheafFunctor (modulePushforward h F)` and
`smallEtaleDirectImage h (moduleSheafFunctor F)` definitionally equal, so a composite `a ≫ b`
whose two factors are written in the two different spellings is type-correct — but the implicit
object argument of `CategoryTheory.CategoryStruct.comp` then records whichever spelling the
elaborator reached first, and gluing two such composites with `Eq.trans` makes the elaborator
reconcile them.  At these concrete functors that reconciliation exceeds the heartbeat budget.
So the chain below is written so that consecutive steps meet at *syntactically* identical terms:
`moduleSheafFunctor_map_etaleUnit_tailSet` carries an explicit type ascription for exactly this
reason, and the passage between the two spellings happens only inside single-step lemmas.

For the same reason the final statement is written with
`AlgebraicGeometry.Space.moduleSetSheaf` rather than with `moduleSheafFunctor … |>.obj`, which
are the same term up to unfolding a reducible abbreviation: at the second spelling the
assembling `Eq.trans` runs out of heartbeats.

`Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_eq_of_val_app` is applied with its
universes written out.  Left to the unifier they become metavariables, and the application does
not terminate.

No compiler options are set in this file, and no `@[stacks]` attribute: the statements here are
steps, not numbered assertions.  Stacks 03LW is carried by
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback` and Stacks 03LQ by
`AlgebraicGeometry.Space.smallToposMorphismTypeU_inverseImageIso`.

## The cube, and what is still missing

With the unit lemma, `AlgebraicGeometry.Space.mateEquiv_moduleSheafFunctor_modulePullbackIso`
closes the τ-faces of the modules-over-sets cube: the mate of the forgetful image of the
comparison of Stacks 03LW is the *identity* 2-square, because the forgetful functor carries the
direct image of modules to the direct image of sheaves of sets on the nose.  What
`Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms` then still asks for is the
`h`-face: that the forgetful functor carries
`AlgebraicGeometry.Space.modulePushforwardSquareComparison` — the comparison of the two composite
direct images of modules around the square, which is the 2-cell whose mate
`AlgebraicGeometry.Space.moduleBaseChangeMap` is — to the small étale comparison that
`AlgebraicGeometry.Space.isIso_mateEquiv_symm_smallSetPushforwardCompSquare` is stated with.

**Each of its three factors is settled below.  The assembly is done**, in
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleEtaleBaseChangeHFace.lean`:
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardSquareComparison` is the h-face,
proved on local sections, and
`AlgebraicGeometry.Space.cubeComponents_moduleSheafFunctor` is the cube's hypothesis at a module.
The square comparison is `(modulePushforwardCompIso i f).hom`, followed by the transport along the
equality of the two composite direct images, followed by `(modulePushforwardCompIso f' g).inv`;
read through `AlgebraicGeometry.Space.modulePushforwardCompIso_eq_compIsoCongr` the two outer
factors are transported comparisons, and

* `AlgebraicGeometry.Space.moduleSheafFunctor_map_compIsoCongr_hom_app_smallEtale` carries the
  first to `(smallEtaleDirectImageCompIso i f).hom`,
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_eqToHom_modulePushforward_app` carries the
  middle to the transport of the direct image of sheaves of sets,
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_compIsoCongr_inv_app_smallEtale` carries the
  third to `(smallEtaleDirectImageCompIso f' g).inv`.

`CategoryTheory.NatTrans.comp_app` for a composite one of whose factors carries a
`CategoryTheory.eqToHom` between functors does not diverge at `whnf`: splitting
`((eqToHom (congrArg modulePushforward w)) ≫ (compIsoCongr … ).inv).app N` into its two factors
by `rfl` takes 0.2 s.  Nor does the obstruction lie in the three-fold split as such.
What is expensive is the comparison of two *composites* of morphisms of sheaves whose
object arguments are written in the two different spellings of the same sheaf — the kernel
reduces `CategoryTheory.CategoryStruct.comp`, which at these sheaf categories unfolds into the
concrete composition and the comparison equivalence of Stacks 03G1, instead of comparing the
composites argument by argument.  The route that works is to leave the sheaf categories
altogether and compute on local sections, where there is no composition to reduce.

So `IsIso (AlgebraicGeometry.Space.moduleEtaleBaseChangeComparison …)` — the ordinary clause of
Stacks 03LX for the canonical map — is **not** proved here; what it is short of is not the h-face but
one definitional identification in the application of the cube; see the
section "What is not done" of
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleEtaleBaseChangeHFace.lean`, which records the
details.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LR](https://stacks.math.columbia.edu/tag/03LR)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback
open Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.GradedAlgebraEssentiallySmall

universe u

namespace Stacks.Sheaves.RingedToposModules

universe w v uu

variable {C : Type uu} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]

omit [J.HasSheafCompose (CategoryTheory.forget RingCat.{w})] in
/-- Restriction of scalars does not change the underlying morphism of sheaves of sets, so the
forgetful functor splits a composite whose second factor is a restriction of scalars across the
two forgetful functors involved. -/
theorem moduleSheafFunctor_map_comp_restrictScalars {R R' : Sheaf J RingCat.{w}} (β : R ⟶ R')
    {N : SheafOfModules.{w} R} {N' N'' : SheafOfModules.{w} R'}
    (u : N ⟶ (SheafOfModules.restrictScalars β).obj N') (φ : N' ⟶ N'') :
    (Sheaf.moduleSheafFunctor R).map (u ≫ (SheafOfModules.restrictScalars β).map φ) =
      (Sheaf.moduleSheafFunctor R).map u ≫ (Sheaf.moduleSheafFunctor R').map φ :=
  (Sheaf.moduleSheafFunctor R).map_comp u ((SheafOfModules.restrictScalars β).map φ)

omit [J.HasSheafCompose (CategoryTheory.forget RingCat.{w})] in
/-- A morphism of sheaves of modules has a prescribed underlying morphism of sheaves of sets as
soon as the two agree on sections.  Stated at a variable sheaf of rings, so that a consumer at a
concrete one pays no definitional unfolding beyond matching its own two morphisms. -/
theorem moduleSheafFunctor_map_eq_of_val_app {R : Sheaf J RingCat.{w}}
    {N N' : SheafOfModules.{w} R} (a : N ⟶ N')
    (b : Sheaf.moduleSheaf R N ⟶ Sheaf.moduleSheaf R N')
    (hb : ∀ (W : Cᵒᵖ) (x : N.val.obj W), a.val.app W x = b.hom.app W x) :
    (Sheaf.moduleSheafFunctor R).map a = b :=
  Sheaf.hom_ext_sections fun W x ↦ hb W x

end Stacks.Sheaves.RingedToposModules

namespace CategoryTheory.Functor

universe vv0 vv1 vv2 vv3 uu0 uu1 uu2 uu3

variable {A₀ : Type uu0} {A₁ : Type uu1} {A₂ : Type uu2} {E : Type uu3}
  [Category.{vv0} A₀] [Category.{vv1} A₁] [Category.{vv2} A₂] [Category.{vv3} E]

/-- A functor applied to the *inverse* of a composition comparison transported along equalities
of functors: the transports contribute nothing, so the image is the image of the untransported
comparison.  This is `CategoryTheory.Functor.map_compIsoCongr_hom_app` for the inverse, proved
the same way — by substituting the three equalities, after which the transport is the identity
and the two `HEq`s retype the answer. -/
theorem map_compIsoCongr_inv_app {p p' : A₀ ⥤ A₁} {q q' : A₁ ⥤ A₂} {pq pq' : A₀ ⥤ A₂}
    (hp : p = p') (hq : q = q') (hpq : pq = pq') (P : p ⋙ q ≅ pq) (F : A₂ ⥤ E) (M : A₀)
    {T₁ T₂ : E} {t : T₁ ⟶ T₂} (ht : HEq (F.map (P.inv.app M)) t)
    (u : F.obj (pq'.obj M) ⟶ F.obj ((p' ⋙ q').obj M)) (hu : HEq u t) :
    F.map ((compIsoCongr hp hq hpq P).inv.app M) = u := by
  subst hp
  subst hq
  subst hpq
  have h1 : F.map ((compIsoCongr (rfl : p = p) (rfl : q = q) (rfl : pq = pq) P).inv.app M) =
      F.map (P.inv.app M) := by simp [compIsoCongr]
  exact h1.trans (eq_of_heq (ht.trans hu.symm))

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Single

variable {U V : AlgebraicSpaces B S hS} (h : U ⟶ V) (hh : IsEtale B S hS h.hom)

/-! ### The unit of the Stacks 03LU adjunction on underlying sheaves of sets -/

/-- **The forgetful functor carries the unit of the Stacks 03D7 adjunction for the morphism of
small étale ringed topoi to the transpose of its change-of-rings half.**  This is
`Stacks.Sheaves.GradedAlgebraEssentiallySmall.moduleSheafFunctor_map_modulesPullbackUnit`, with
the transpose written out by the triangle description of a hom-set bijection. -/
theorem moduleSheafFunctor_map_pullbackAdjPushforwardModules_unit_app
    (M : Modules.{u, u} B S hS V.1 V.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS V)).map
        ((pullbackAdjPushforwardModules
          (smallEtaleRingedToposModulesHom B S hS h)).unit.app M) =
      (smallToposMorphismTypeU B S hS h).adj.unit.app (moduleSetSheaf B S hS V M) ≫
        (smallEtaleDirectImage B S hS h).map
          (pullbackScalarUnit (smallEtaleRingedToposHom B S hS h) M) :=
  (moduleSheafFunctor_map_modulesPullbackUnit (smallEtaleRingedToposHom B S hS h) M).trans
    ((smallToposMorphismTypeU B S hS h).adj.homEquiv_unit _ _ _)

/-! ### The change-of-rings half against the comparison of Stacks 03LW -/

/-- The comparison of the inverse image of modules with its transport along small étale
restriction has the comparison of Stacks 03LQ as its underlying morphism of sheaves of sets: the
transport is induced by that comparison and by nothing else. -/
theorem etaleModuleInverseImageIsoRestrictionTransport_hom_app_val_app
    (M : Modules.{u, u} B S hS V.1 V.2) (W : (SmallEtale B S hS U.1)ᵒᵖ)
    (x : ((inverseImageModules.{u, u, u, u + 1, u, u + 1}
      (smallEtaleRingedToposHom B S hS h).toToposHom
      (structureRingSheaf B S hS V)).obj M).val.obj W) :
    ((etaleModuleInverseImageIsoRestrictionTransport B S hS h hh).hom.app M).val.app W x =
      ((smallToposMorphismTypeU_inverseImageIso B S hS h hh).hom.app
        (moduleSetSheaf B S hS V M)).hom.app W x :=
  rfl

/-- The change-of-rings half of the unit, followed by the comparison of Stacks 03LW, is the
comparison of Stacks 03LQ — on sections.  This is
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_unit_app` read through the previous
lemma. -/
theorem extendScalarsFSharpAdjunction_unit_comp_val_app
    (M : Modules.{u, u} B S hS V.1 V.2) (W : (SmallEtale B S hS U.1)ᵒᵖ)
    (x : ((inverseImageModules.{u, u, u, u + 1, u, u + 1}
      (smallEtaleRingedToposHom B S hS h).toToposHom
      (structureRingSheaf B S hS V)).obj M).val.obj W) :
    ((extendScalarsFSharpAdjunction B S hS h).unit.app
          ((inverseImageModules.{u, u, u, u + 1, u, u + 1}
            (smallEtaleRingedToposHom B S hS h).toToposHom
            (structureRingSheaf B S hS V)).obj M) ≫
        (SheafOfModules.restrictScalars
          (smallEtaleRingedToposModulesHom B S hS h).fSharpInverseImage).map
            ((modulePullbackIsoEtaleModulePullback B S hS h hh).hom.app M)).val.app W x =
      ((smallToposMorphismTypeU_inverseImageIso B S hS h hh).hom.app
        (moduleSetSheaf B S hS V M)).hom.app W x :=
  (modulePullbackIsoEtaleModulePullback_unit_app B S hS h hh M W x).trans
    (etaleModuleInverseImageIsoRestrictionTransport_hom_app_val_app B S hS h hh M W x)

/-- **The change-of-rings half of the unit of Stacks 03LU, followed by the comparison of
Stacks 03LW on underlying sheaves of sets, is the comparison of Stacks 03LQ.**  Both are
morphisms `h⁻¹F ⟶ F|_{U_étale}` of sheaves of sets on the small étale site of `U`, and the
composite is the one `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_unit_app`
computes. -/
theorem pullbackScalarUnit_comp_moduleSheafFunctor_map_modulePullbackIso
    (M : Modules.{u, u} B S hS V.1 V.2) :
    pullbackScalarUnit (smallEtaleRingedToposHom B S hS h) M ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS U)).map
          ((modulePullbackIsoEtaleModulePullback B S hS h hh).hom.app M) =
      (smallToposMorphismTypeU_inverseImageIso B S hS h hh).hom.app
        (moduleSetSheaf B S hS V M) :=
  (moduleSheafFunctor_map_comp_restrictScalars
      (smallEtaleRingedToposModulesHom B S hS h).fSharpInverseImage
      ((extendScalarsFSharpAdjunction B S hS h).unit.app
        ((inverseImageModules.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS h).toToposHom (structureRingSheaf B S hS V)).obj M))
      ((modulePullbackIsoEtaleModulePullback B S hS h hh).hom.app M)).symm.trans
    (moduleSheafFunctor_map_eq_of_val_app.{u, u, u + 1} _ _
      (extendScalarsFSharpAdjunction_unit_comp_val_app B S hS h hh M))

/-! ### The mate of the comparison of the two inverse images -/

/-- The unit of the Stacks 03LU adjunction, followed by the direct image of the comparison of
Stacks 03LW, is the unit of the small étale set-restriction adjunction — with the composite read
at the direct image of sheaves of sets rather than at the direct image of modules.  The type
ascription is what keeps the two spellings apart; see this file's implementation notes. -/
private theorem moduleSheafFunctor_map_etaleUnit_tailSet
    (M : Modules.{u, u} B S hS V.1 V.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS V)).map
          ((modulePullbackAdjunction B S hS h).unit.app M) ≫
        (smallEtaleDirectImage B S hS h).map
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS U)).map
            ((modulePullbackIsoEtaleModulePullback B S hS h hh).hom.app M)) =
      (smallEtaleSetRestrictionAdjunction B S hS h hh).unit.app
        (moduleSetSheaf B S hS V M) :=
  (congrArg
        (fun p ↦ p ≫ (smallEtaleDirectImage B S hS h).map
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS U)).map
            ((modulePullbackIsoEtaleModulePullback B S hS h hh).hom.app M)))
        ((moduleSheafFunctor_map_modulePullbackAdjunction_unit_app B S hS h M).trans
          ((smallToposMorphismTypeU B S hS h).adj.homEquiv_unit _ _ _))).trans
    ((Category.assoc _ _ _).trans
      ((congrArg
            (fun q ↦ (smallToposMorphismTypeU B S hS h).adj.unit.app
              (moduleSetSheaf B S hS V M) ≫ q)
            ((((smallEtaleDirectImage B S hS h).map_comp _ _).symm).trans
              (congrArg (smallEtaleDirectImage B S hS h).map
                (pullbackScalarUnit_comp_moduleSheafFunctor_map_modulePullbackIso
                  B S hS h hh M)))).trans
        (Adjunction.unit_leftAdjointUniq_hom_app (smallToposMorphismTypeU B S hS h).adj
          (smallEtaleSetRestrictionAdjunction B S hS h hh) (moduleSetSheaf B S hS V M))))

/-- The comparison of Stacks 03LW and its inverse, taken through the forgetful functor and then
the direct image of sheaves of sets, cancel. -/
private theorem smallEtaleDirectImage_map_moduleSheafFunctor_map_hom_inv_id
    (M : Modules.{u, u} B S hS V.1 V.2) :
    (smallEtaleDirectImage B S hS h).map
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS U)).map
            ((modulePullbackIsoEtaleModulePullback B S hS h hh).hom.app M)) ≫
        (smallEtaleDirectImage B S hS h).map
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS U)).map
            ((modulePullbackIsoEtaleModulePullback B S hS h hh).inv.app M)) =
      CategoryStruct.id ((smallEtaleDirectImage B S hS h).obj
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS U)).obj
          ((modulePullback B S hS h).obj M))) :=
  (((smallEtaleDirectImage B S hS h).map_comp _ _).symm.trans
        (congrArg (smallEtaleDirectImage B S hS h).map
          (((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS U)).map_comp _ _).symm.trans
            (congrArg (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS U)).map
              ((modulePullbackIsoEtaleModulePullback B S hS h hh).hom_inv_id_app M))))).trans
    ((congrArg (smallEtaleDirectImage B S hS h).map
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS U)).map_id
            ((modulePullback B S hS h).obj M))).trans
      ((smallEtaleDirectImage B S hS h).map_id _))

/-- **The unit square of the forgetful functor.**  The unit of the small étale restriction
adjunction of Stacks 03LP, followed by the direct image of the forgetful image of the *inverse*
of the comparison of Stacks 03LW, is the forgetful image of the unit of Stacks 03LU.

This is `AlgebraicGeometry.Space.moduleSheafFunctor_map_etaleUnit_tailSet` with the comparison
moved to the other side. -/
theorem moduleSheafFunctor_unitSquare (M : Modules.{u, u} B S hS V.1 V.2) :
    (smallEtaleSetRestrictionAdjunction B S hS h hh).unit.app
          (moduleSetSheaf B S hS V M) ≫
        (smallEtaleDirectImage B S hS h).map
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS U)).map
            ((modulePullbackIsoEtaleModulePullback B S hS h hh).inv.app M)) =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS V)).map
        ((modulePullbackAdjunction B S hS h).unit.app M) :=
  (congrArg
        (fun p ↦ p ≫ (smallEtaleDirectImage B S hS h).map
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS U)).map
            ((modulePullbackIsoEtaleModulePullback B S hS h hh).inv.app M)))
        (moduleSheafFunctor_map_etaleUnit_tailSet B S hS h hh M).symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg
            (fun q ↦ (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS V)).map
              ((modulePullbackAdjunction B S hS h).unit.app M) ≫ q)
            (smallEtaleDirectImage_map_moduleSheafFunctor_map_hom_inv_id
              B S hS h hh M)).trans
        (Category.comp_id _)))

/-- **The mate of the forgetful functor's comparison of the two inverse images is the identity
2-square.**  The comparison of the two horizontal left adjoints of the modules-over-sets cube is
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`, backwards, whiskered by the
forgetful functor; its mate across the adjunctions of Stacks 03LU and of Stacks 03LP is the
comparison of the two vertical functors, which is the identity because the forgetful functor
carries the direct image of modules to the direct image of sheaves of sets on the nose.

`CategoryTheory.mateEquiv_eq_of_unit` reads that off the unit square
`AlgebraicGeometry.Space.moduleSheafFunctor_unitSquare`. -/
theorem mateEquiv_moduleSheafFunctor_modulePullbackIso :
    mateEquiv (modulePullbackAdjunction B S hS h)
        (smallEtaleSetRestrictionAdjunction B S hS h hh)
        (TwoSquare.mk (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS V))
          (modulePullback B S hS h) (smallEtaleSetRestriction B S hS h hh)
          (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS U))
          (Functor.whiskerRight (modulePullbackIsoEtaleModulePullback B S hS h hh).inv
            (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS U)))) =
      TwoSquare.mk (modulePushforward B S hS h)
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS U))
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS V))
        (smallEtaleDirectImage B S hS h)
        (CategoryStruct.id (modulePushforward B S hS h ⋙
          Sheaf.moduleSheafFunctor (structureRingSheaf B S hS V))) :=
 by
  refine mateEquiv_eq_of_unit _ _ _ _ fun M ↦ ?_
  exact (moduleSheafFunctor_unitSquare B S hS h hh M).trans (Category.comp_id _).symm

end Single


/-! ### The forgetful functor on the comparison of composite direct images -/

section Comp

variable {X Y Z : AlgebraicSpaces B S hS}

/-- The transport of `AlgebraicGeometry.Space.pushforwardModulesCompTransport`, backwards, is the
geometric comparison of Stacks 03G2, part (3), backwards, on underlying sheaves of sets.  This is
`AlgebraicGeometry.Space.moduleSheafFunctor_map_pushforwardModulesCompTransport_hom_app` for the
inverse. -/
theorem moduleSheafFunctor_map_pushforwardModulesCompTransport_inv_app (a : X ⟶ Y) (b : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
        ((pushforwardModulesCompTransport B S hS a b).inv.app F) =
      (smallToposMorphismTypeU_comp B S hS a b).inv.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) :=
  rfl

/-- The comparison `f_* ⋙ g_* ≅ (f ≫ g)_*` of direct images of modules for the honest composite
of the morphisms of ringed topoi is the identity on underlying sheaves of sets.  This is
`AlgebraicGeometry.Space.moduleSheafFunctor_map_pushforwardModulesCompIso_inv_app` for the
forward direction. -/
theorem moduleSheafFunctor_map_smallEtaleCompIso_hom_app (a : X ⟶ Y) (b : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
        ((RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS a)
          (smallEtaleRingedToposHom B S hS b)).hom.app F) =
      CategoryStruct.id ((smallToposMorphismTypeU B S hS b).pushforward.obj
        ((smallToposMorphismTypeU B S hS a).pushforward.obj
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F))) :=
  rfl

/-- **The comparison of direct images of modules at the level of the morphisms of ringed topoi,
backwards, is the geometric comparison of Stacks 03G2, part (3), backwards**, on underlying
sheaves of sets.  This is
`AlgebraicGeometry.Space.moduleSheafFunctor_map_pushforwardModulesCompAt_hom_app` for the
inverse: `AlgebraicGeometry.Space.pushforwardModulesCompAt` is a two-fold composite, the factor
coming from the honest composite of morphisms of ringed topoi is the identity on underlying
sheaves of sets, and the transport is the geometric comparison. -/
theorem moduleSheafFunctor_map_pushforwardModulesCompAt_inv_app (a : X ⟶ Y) (b : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
        ((pushforwardModulesCompAt B S hS a b).inv.app F) =
      (smallToposMorphismTypeU_comp B S hS a b).inv.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) :=
  ((congrArg (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
        (show (pushforwardModulesCompAt B S hS a b).inv.app F =
            (pushforwardModulesCompTransport B S hS a b).inv.app F ≫
              (RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS a)
                (smallEtaleRingedToposHom B S hS b)).hom.app F from rfl)).trans
      (((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map_comp _ _).trans
        (congrArg₂ (fun x y ↦ x ≫ y)
          (moduleSheafFunctor_map_pushforwardModulesCompTransport_inv_app B S hS a b F)
          (moduleSheafFunctor_map_smallEtaleCompIso_hom_app B S hS a b F)))).trans
    (Category.comp_id _)

/-- The geometric comparison of Stacks 03G2, part (3), backwards, read on the iterated direct
image of modules taken through the morphisms of ringed topoi of Stacks 03G8: the underlying sheaf
of sets is the iterated direct image, so this is reflexivity. -/
theorem heq_smallToposMorphismTypeU_comp_inv_app_pushforwardModules (a : X ⟶ Y) (b : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    HEq (show (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).obj
            ((smallEtaleRingedToposHom B S hS (a ≫ b)).pushforwardModules.obj F) ⟶
          (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).obj
            (((smallEtaleRingedToposHom B S hS a).pushforwardModules ⋙
              (smallEtaleRingedToposHom B S hS b).pushforwardModules).obj F) from
        (smallToposMorphismTypeU_comp B S hS a b).inv.app
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F))
      (show (smallToposMorphismTypeU B S hS (a ≫ b)).pushforward.obj
            ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) ⟶
          (smallToposMorphismTypeU B S hS b).pushforward.obj
            ((smallToposMorphismTypeU B S hS a).pushforward.obj
              ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F)) from
        (smallToposMorphismTypeU_comp B S hS a b).inv.app
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F)) :=
  HEq.refl _

/-- The geometric comparison of Stacks 03G2, part (3), backwards, read on the iterated direct
image of `𝒪`-modules: the underlying sheaf of sets is the iterated direct image, so this is
reflexivity. -/
theorem heq_smallToposMorphismTypeU_comp_inv_app_modulePushforward (a : X ⟶ Y) (b : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    HEq (show (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).obj
            ((modulePushforward B S hS (a ≫ b)).obj F) ⟶
          (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).obj
            ((modulePushforward B S hS a ⋙ modulePushforward B S hS b).obj F) from
        (smallToposMorphismTypeU_comp B S hS a b).inv.app
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F))
      (show (smallToposMorphismTypeU B S hS (a ≫ b)).pushforward.obj
            ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) ⟶
          (smallToposMorphismTypeU B S hS b).pushforward.obj
            ((smallToposMorphismTypeU B S hS a).pushforward.obj
              ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F)) from
        (smallToposMorphismTypeU_comp B S hS a b).inv.app
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F)) :=
  HEq.refl _

/-- **Stacks 03LU, the composition comparison for direct images, backwards.**  The forgetful
functor carries the inverse of the transported comparison of direct images of modules to the
inverse of the geometric comparison of Stacks 03G2, part (3).  This is
`AlgebraicGeometry.Space.moduleSheafFunctor_map_compIsoCongr_hom_app` for the inverse. -/
theorem moduleSheafFunctor_map_compIsoCongr_inv_app (a : X ⟶ Y) (b : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
        ((CategoryTheory.Functor.compIsoCongr
          (pushforwardModules_eq_modulePushforward B S hS a)
          (pushforwardModules_eq_modulePushforward B S hS b)
          (pushforwardModules_eq_modulePushforward B S hS (a ≫ b))
          (pushforwardModulesCompAt B S hS a b)).inv.app F) =
      (smallToposMorphismTypeU_comp B S hS a b).inv.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) :=
  CategoryTheory.Functor.map_compIsoCongr_inv_app
    (pushforwardModules_eq_modulePushforward B S hS a)
    (pushforwardModules_eq_modulePushforward B S hS b)
    (pushforwardModules_eq_modulePushforward B S hS (a ≫ b))
    (pushforwardModulesCompAt B S hS a b)
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)) F
    (heq_of_eq (moduleSheafFunctor_map_pushforwardModulesCompAt_inv_app B S hS a b F))
    ((smallToposMorphismTypeU_comp B S hS a b).inv.app
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F))
    ((heq_smallToposMorphismTypeU_comp_inv_app_modulePushforward B S hS a b F).trans
      (heq_smallToposMorphismTypeU_comp_inv_app_pushforwardModules B S hS a b F).symm)

/-- The same, with the geometric comparison written in the
`AlgebraicGeometry.Space.smallEtaleDirectImage` spelling of
`AlgebraicGeometry.Space.smallEtaleDirectImageCompIso`.  The retyping is
`AlgebraicGeometry.Space.smallEtaleDirectImageCompIso_def`, applied at the level of the
isomorphism. -/
theorem moduleSheafFunctor_map_compIsoCongr_hom_app_smallEtale (a : X ⟶ Y) (b : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
        ((CategoryTheory.Functor.compIsoCongr
          (pushforwardModules_eq_modulePushforward B S hS a)
          (pushforwardModules_eq_modulePushforward B S hS b)
          (pushforwardModules_eq_modulePushforward B S hS (a ≫ b))
          (pushforwardModulesCompAt B S hS a b)).hom.app F) =
      (smallEtaleDirectImageCompIso B S hS a b).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) :=
  moduleSheafFunctor_map_compIsoCongr_hom_app B S hS a b F

/-- `AlgebraicGeometry.Space.moduleSheafFunctor_map_compIsoCongr_inv_app` in the
`AlgebraicGeometry.Space.smallEtaleDirectImageCompIso` spelling. -/
theorem moduleSheafFunctor_map_compIsoCongr_inv_app_smallEtale (a : X ⟶ Y) (b : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
        ((CategoryTheory.Functor.compIsoCongr
          (pushforwardModules_eq_modulePushforward B S hS a)
          (pushforwardModules_eq_modulePushforward B S hS b)
          (pushforwardModules_eq_modulePushforward B S hS (a ≫ b))
          (pushforwardModulesCompAt B S hS a b)).inv.app F) =
      (smallEtaleDirectImageCompIso B S hS a b).inv.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) :=
  moduleSheafFunctor_map_compIsoCongr_inv_app B S hS a b F

/-- **The forgetful functor carries the transport of the direct image of modules along an
equality of morphisms to the transport of the direct image of sheaves of sets.**  Stated at a
variable equality of morphisms, so that `subst` makes both transports identities. -/
theorem moduleSheafFunctor_map_eqToHom_modulePushforward_app {k k' : X ⟶ Z} (w : k = k')
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
        ((eqToHom (congrArg (fun m : X ⟶ Z ↦ modulePushforward B S hS m) w)).app F) =
      (eqToHom (congrArg (fun m : X ⟶ Z ↦ smallEtaleDirectImage B S hS m) w)).app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) := by
  subst w
  exact (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map_id _

end Comp

end AlgebraicGeometry.Space

end
