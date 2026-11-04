module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.PresheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence
import StacksCore.Tactic.StacksAttribute

/-!
# Presheaves and sheaves of modules are Grothendieck abelian, at independent universes

Let `C` be a category, `J` a Grothendieck topology on it and `R` a sheaf of rings on `(C, J)`.
Then the category of sheaves of `R`-modules is Grothendieck abelian. The point of this file is
that the site, the ring and the module universes are **independent**: for `C : Type u` with
`Category.{v} C` and `R` valued in `RingCat.{r}`, the conclusion is obtained for
`SheafOfModules.{max u v r t}` with `t` arbitrary.

Mathlib proves the statement only on the diagonal — its instance assumes `[SmallCategory C]`
and puts the modules in the one universe `u` — so it does not apply to a site whose objects and
morphisms live in different universes from its modules, which is the situation of a general
ringed site.

Grothendieck abelian-ness is four conditions, and only the separator is work. Local smallness is
automatic, filtered colimits exist pointwise, and exactness of filtered colimits (AB5) descends
from presheaves of abelian groups along the forgetful functor, which preserves and reflects the
relevant limits and colimits; for sheaves, all three transfer along the sheafification
adjunction, whose left adjoint is exact.

For the separator, the generating family is the modules `R ⊗_ℤ ℤ[Hom(-, U)]` for `U` an object of
`C` — the free `R`-module on a representable. A map out of it into `M` is an additive map out of
the free abelian presheaf on `yoneda.obj U`, hence by freeness a section of `M` over `U`; so a
morphism `f : M ⟶ N` which agrees after composition with every such map agrees on every section,
i.e. the family is separating. Taking the coproduct of the family — legitimate because the family
is indexed by the objects of `C`, which the module universe contains — gives a separator. The
representable is lifted into the module universe with `ULift`, which is exactly what makes the
argument work away from the diagonal.

## Main definitions

* `Stacks.SheafOfModules.tensorPresheaf`: extension of scalars `R ⊗_ℤ (-)` from presheaves of
  abelian groups to presheaves of `R`-modules, with the ring and module universes independent.
* `Stacks.SheafOfModules.tensorPresheafLift`: the `R`-linear map out of `R ⊗_ℤ F` determined by
  an additive map out of `F`.
* `Stacks.SheafOfModules.freeRepresentable`: the free abelian presheaf on a representable,
  lifted into the module universe.

## Main results

* `Stacks.SheafOfModules.presheafModulesGrothendieck`: presheaves of modules are Grothendieck
  abelian.
* `Stacks.SheafOfModules.sheafModulesGrothendieck`: sheaves of modules are Grothendieck abelian.
* `Stacks.SheafOfModules.freeRepresentables_isSeparating`: the free modules on representables
  form a separating family.
* `Stacks.SheafOfModules.coefficientSheafification` and
  `Stacks.SheafOfModules.coefficientLocallyBijective`: sheafification of abelian presheaves
  exists, and is characterised by local bijectivity, in any coefficient universe containing the
  site. These are the instances that make the statements above typecheck away from the diagonal.

## Implementation notes

`tensorPresheaf` is stated with the module universe written as `max r u`, rather than as an
independent universe variable, because the carrier of `R.obj X ⊗[ℤ] F.obj X` lies in the maximum
of the ring and coefficient universes; writing it as a `max` is how the inequality `r ≤` module
universe is expressed to the elaborator.

`coefficientSheafification` and `coefficientLocallyBijective` are stated as instances guarded by
`UnivLE`, so they fire exactly when the coefficient universe contains the site. Roughly thirty
places in this library currently re-derive these two facts inline with `letI` and an explicit
`hasSheafifyEssentiallySmallSite`/`WEqualsLocallyBijective.ofEssentiallySmall` universe
instantiation; those are candidates for deletion in favour of these instances.

Two steps need a defeq between `M.presheaf.obj X` and `M.obj X` that the elaborator will not
take at its default transparency. Rather than lowering transparency, the defeq is isolated in the
`rfl`-lemma `presheaf_map_apply` and the two proofs are routed through it, which is why they
finish with an explicit term rather than a `rewrite`.

## References

* [Stacks Project, Tag 03DB](https://stacks.math.columbia.edu/tag/03DB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

namespace Stacks.SheafOfModules

section ExtendScalars

universe w v u r

variable {D : Type w} [Category.{v} D] (R : Dᵒᵖ ⥤ RingCat.{r})

/-- The semilinear restriction map of the presheaf `R ⊗_ℤ F`: on `R.obj X ⊗ F.obj X` it is the
tensor product of the restriction maps of `R` and of `F`, semilinear over `R.map f`. -/
noncomputable def tensorPresheafRestrict (F : Dᵒᵖ ⥤ Ab.{max r u}) {X Y : Dᵒᵖ} (f : X ⟶ Y) :
    (R.obj X ⊗[ℤ] F.obj X) →ₛₗ[(R.map f).hom] (R.obj Y ⊗[ℤ] F.obj Y) where
  toFun := TensorProduct.map (R.map f).hom.toAddMonoidHom.toIntLinearMap
    (F.map f).hom.toIntLinearMap
  map_add' := map_add _
  map_smul' a x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul b x => simp [TensorProduct.smul_tmul', smul_eq_mul]

/-- `tensorPresheafRestrict` on a pure tensor. -/
lemma tensorPresheafRestrict_tmul (F : Dᵒᵖ ⥤ Ab.{max r u}) {X Y : Dᵒᵖ} (f : X ⟶ Y)
    (a : R.obj X) (x : F.obj X) :
    tensorPresheafRestrict R F f (a ⊗ₜ[ℤ] x) = R.map f a ⊗ₜ[ℤ] F.map f x :=
  TensorProduct.map_tmul _ _ _ _

/-- **Extension of scalars** from presheaves of abelian groups to presheaves of `R`-modules:
`F ↦ R ⊗_ℤ F`, taken sectionwise. The ring universe `r` and the coefficient universe `u` are
independent; the modules land in `max r u`. -/
noncomputable def tensorPresheaf (F : Dᵒᵖ ⥤ Ab.{max r u}) : PresheafOfModules.{max r u} R where
  obj X := ModuleCat.of (R.obj X) (R.obj X ⊗[ℤ] F.obj X)
  map f := (ModuleCat.semilinearMapAddEquiv (R.map f).hom _ _) (tensorPresheafRestrict R F f)
  map_id X := by
    refine ModuleCat.hom_ext (AlgebraTensorModule.ext fun a x => ?_)
    change tensorPresheafRestrict R F (𝟙 X) (a ⊗ₜ[ℤ] x) = a ⊗ₜ[ℤ] x
    simp [tensorPresheafRestrict_tmul]
  map_comp f g := by
    refine ModuleCat.hom_ext (AlgebraTensorModule.ext fun a x => ?_)
    change tensorPresheafRestrict R F (f ≫ g) (a ⊗ₜ[ℤ] x) =
      tensorPresheafRestrict R F g (tensorPresheafRestrict R F f (a ⊗ₜ[ℤ] x))
    simp [tensorPresheafRestrict_tmul]

/-- The underlying abelian presheaf of a presheaf of modules restricts as the presheaf of modules
does. This is a definitional identity, isolated as a lemma because the elaborator will not take
it at its default transparency. -/
private lemma presheaf_map_apply {M : PresheafOfModules.{max r u} R} {X Y : Dᵒᵖ} (g : X ⟶ Y)
    (y : M.presheaf.obj X) : M.presheaf.map g y = M.map g y := rfl

/-- **Freeness of extension of scalars**: an additive map `F ⟶ M` out of an abelian presheaf
extends uniquely to an `R`-linear map `R ⊗_ℤ F ⟶ M`. -/
noncomputable def tensorPresheafLift {F : Dᵒᵖ ⥤ Ab.{max r u}}
    {M : PresheafOfModules.{max r u} R} (f : F ⟶ M.presheaf) : tensorPresheaf R F ⟶ M where
  app X := ModuleCat.ofHom
    (X := (tensorPresheaf R F).obj X) (Y := M.obj X)
    (AlgebraTensorModule.lift
      (LinearMap.toSpanSingleton (R.obj X) (F.obj X →ₗ[ℤ] M.obj X)
        (f.app X).hom.toIntLinearMap))
  naturality {X Y} g := by
    refine ModuleCat.hom_ext (AlgebraTensorModule.ext fun a x => ?_)
    change R.map g a • f.app Y (F.map g x) = M.map g (a • (show M.obj X from f.app X x))
    rw [PresheafOfModules.map_smul]
    congr 1
    exact (NatTrans.naturality_apply f g x).trans (presheaf_map_apply R g _)

/-- `tensorPresheafLift` on a pure tensor. -/
lemma tensorPresheafLift_app_tmul {F : Dᵒᵖ ⥤ Ab.{max r u}}
    {M : PresheafOfModules.{max r u} R} (f : F ⟶ M.presheaf) (X : Dᵒᵖ)
    (a : R.obj X) (x : F.obj X) :
    (tensorPresheafLift R f).app X (a ⊗ₜ[ℤ] x) = a • f.app X x := rfl

end ExtendScalars

section FreeRepresentable

universe u v t

variable {C : Type u} [Category.{v} C]

/-- The free abelian presheaf on the representable `yoneda.obj U`, with the representable lifted
into the coefficient universe. -/
noncomputable abbrev freeRepresentable (U : C) : Cᵒᵖ ⥤ Ab.{max u v t} :=
  yoneda.obj U ⋙ uliftFunctor.{max u v t} ⋙ AddCommGrpCat.free

/-- **The free abelian presheaf on a representable corepresents evaluation.** A section `m` of
`F` over `U` determines the map sending the generator indexed by `arrow : V ⟶ U` to the
restriction of `m` along `arrow`. -/
noncomputable def freeRepresentableToPresheaf (U : C) (F : Cᵒᵖ ⥤ Ab.{max u v t})
    (m : F.obj (op U)) : freeRepresentable.{u, v, t} U ⟶ F where
  app point := AddCommGrpCat.ofHom
    (FreeAbelianGroup.lift (fun arrow : ULift.{max u v t} (point.unop ⟶ U) =>
      F.map arrow.down.op m))
  naturality source target arrow := by
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro generator
    change ULift.{max u v t} (source.unop ⟶ U) at generator
    change FreeAbelianGroup.lift
        (fun a : ULift.{max u v t} (target.unop ⟶ U) => F.map a.down.op m)
        (FreeAbelianGroup.map (fun a : ULift.{max u v t} (source.unop ⟶ U) =>
          ULift.up (arrow.unop ≫ a.down)) (FreeAbelianGroup.of generator)) =
      F.map arrow (FreeAbelianGroup.lift
        (fun a : ULift.{max u v t} (source.unop ⟶ U) => F.map a.down.op m)
        (FreeAbelianGroup.of generator))
    rw [FreeAbelianGroup.map_of_apply, FreeAbelianGroup.lift_apply_of,
      FreeAbelianGroup.lift_apply_of, ← ConcreteCategory.comp_apply, ← F.map_comp]
    rfl

/-- `freeRepresentableToPresheaf` on a generator. -/
lemma freeRepresentableToPresheaf_app_of (U : C) (F : Cᵒᵖ ⥤ Ab.{max u v t})
    (m : F.obj (op U)) (point : Cᵒᵖ) (arrow : ULift.{max u v t} (point.unop ⟶ U)) :
    (freeRepresentableToPresheaf.{u, v, t} U F m).app point (FreeAbelianGroup.of arrow) =
      F.map arrow.down.op m :=
  FreeAbelianGroup.lift_apply_of _ _

end FreeRepresentable

section Grothendieck

universe u v r t

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- **Sheafification of abelian presheaves exists in any coefficient universe containing the
site.** The site is essentially small relative to such a universe, which is the hypothesis of
`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall`. -/
instance coefficientSheafification [UnivLE.{u, t}] [UnivLE.{v, t}] : HasSheafify J Ab.{t} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{t, v, u} J

/-- **Local bijectivity characterises the sheafification equivalences** in any coefficient
universe containing the site. -/
instance coefficientLocallyBijective [UnivLE.{u, t}] [UnivLE.{v, t}] :
    J.WEqualsLocallyBijective Ab.{t} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, t, u, t + 1, t} J

variable (Rp : Cᵒᵖ ⥤ RingCat.{r})

/-- **Every section is hit by a map from the free module on a representable.** Transposing the
section `m` of `M` over `U` through freeness of the abelian presheaf and then through extension
of scalars gives a map `R ⊗_ℤ ℤ[Hom(-, U)] ⟶ M` carrying the canonical generator to `m`. -/
lemma exists_tensorPresheafLift_eval (U : C) (M : PresheafOfModules.{max u v r t} Rp)
    (m : M.obj (op U)) :
    ∃ a : tensorPresheaf.{u, v, max u v t, r} Rp (freeRepresentable.{u, v, max r t} U) ⟶ M,
      a.app (op U) ((1 : Rp.obj (op U)) ⊗ₜ[ℤ]
        (FreeAbelianGroup.of (ULift.up (𝟙 U)) :
          (freeRepresentable.{u, v, max r t} U).obj (op U))) = m := by
  refine ⟨tensorPresheafLift.{u, v, max u v t, r} Rp
    (freeRepresentableToPresheaf.{u, v, max r t} U M.presheaf m), ?_⟩
  show (1 : Rp.obj (op U)) •
    (freeRepresentableToPresheaf.{u, v, max r t} U M.presheaf m).app (op U)
      (FreeAbelianGroup.of (ULift.up (𝟙 U))) = m
  rw [one_smul]
  exact (freeRepresentableToPresheaf_app_of.{u, v, max r t} U M.presheaf m (op U)
    (ULift.up (𝟙 U))).trans (ConcreteCategory.congr_hom (M.presheaf.map_id (op U)) m)

/-- **The free modules on representables separate.** Two maps out of `M` that agree after
composition with every map from a free module on a representable agree on every section of `M`,
by `exists_tensorPresheafLift_eval`. -/
lemma freeRepresentables_isSeparating :
    (ObjectProperty.ofObj (fun U : C => tensorPresheaf.{u, v, max u v t, r} Rp
      (freeRepresentable.{u, v, max r t} U))).IsSeparating := by
  intro M N f g h
  ext X m
  obtain ⟨a, hm⟩ := exists_tensorPresheafLift_eval.{u, v, r, t} Rp X.unop M m
  have ha := h _ ⟨X.unop⟩ a
  rw [← hm]
  exact ConcreteCategory.congr_hom (congr_arg (fun k => k.app X) ha) _

/-- **Presheaves of modules are Grothendieck abelian**, with the site, ring and module universes
independent. AB5 descends from abelian presheaves along the forgetful functor, which preserves
colimits and preserves and reflects finite limits; the separator is the coproduct of the free
modules on representables. -/
@[sga "3 I 3.2.1" "more general", sga "3 I 5.2" "special case"]
theorem presheafModulesGrothendieck :
    IsGrothendieckAbelian.{max u v r t} (PresheafOfModules.{max u v r t} Rp) where
  hasFilteredColimitsOfSize := ⟨fun _ => ⟨fun _ => inferInstance⟩⟩
  ab5OfSize := ⟨fun K _ _ => ⟨⟨fun L _ _ => ⟨fun {F} =>
    have : PreservesLimit F (colim (J := K) ⋙ PresheafOfModules.toPresheaf Rp) :=
      preservesLimit_of_natIso _ (preservesColimitNatIso (PresheafOfModules.toPresheaf Rp)).symm
    preservesLimit_of_reflects_of_preserves _ (PresheafOfModules.toPresheaf Rp)⟩⟩⟩⟩
  hasSeparator := ⟨_, (freeRepresentables_isSeparating.{u, v, r, t} Rp).isSeparator_coproduct⟩

/-- **Sheaves of modules are Grothendieck abelian**, with the site, ring and module universes
independent. All three nontrivial conditions transfer from presheaves of modules along the
sheafification adjunction, whose left adjoint is exact. -/
theorem sheafModulesGrothendieck (R : Sheaf J RingCat.{r}) :
    IsGrothendieckAbelian.{max u v r t} (SheafOfModules.{max u v r t} R) := by
  let _ : IsGrothendieckAbelian.{max u v r t} (PresheafOfModules.{max u v r t} R.obj) :=
    presheafModulesGrothendieck.{u, v, r, t} R.obj
  exact
    { hasFilteredColimitsOfSize := ⟨fun _ => ⟨fun _ => inferInstance⟩⟩
      ab5OfSize := ⟨fun K _ _ =>
        (PresheafOfModules.sheafificationAdjunction.{max u v r t}
          (𝟙 R.obj)).hasExactColimitsOfShape K⟩
      hasSeparator := .of_adjunction
        (PresheafOfModules.sheafificationAdjunction.{max u v r t} (𝟙 R.obj)) }

end Grothendieck

end Stacks.SheafOfModules

end
