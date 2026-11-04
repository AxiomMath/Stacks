module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.ModuleCohomologyAbelianComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology of a sheaf of modules is the cohomology of its underlying abelian sheaf, on any site

Let `(C, J)` be a site and let `R` be a sheaf of rings on it, with its sections and the module
sections in a universe containing the site. For every sheaf of `R`-modules `M` and every degree
`n`, the cohomology `Ext^n(R, M)` of `M` computed in the category of sheaves of `R`-modules —
`Stacks.Cohomology.BiggerSiteModules.moduleFunctorH` — is the cohomology `Ext^n(ℤ, M)` of its
underlying abelian sheaf — Mathlib's `CategoryTheory.Sheaf.H` — naturally in `M`. This is
Stacks 03FD for global sections.

`Stacks.Cohomology.ModuleAbelianComparison.moduleFunctorHIsoOfIsTerminal` is the same statement
for a site with a terminal object. A terminal object is used there only to identify the two
degree-zero functors, as sections over it; here they are identified with no terminal object, as
compatible families of sections. That is what is needed for the sites of an algebraic stack and
for its lisse-étale and flat-fppf subsites, which have no terminal object as soon as the stack
has a nontrivial automorphism
(`CategoryTheory.Functor.IsFiberedInGroupoids.not_isTerminal_of_faithful_of_ne_id`).

## Main definitions

* `Stacks.Cohomology.ModuleAbelianComparison.unitHomAddEquivConstantPresheafHom`: a morphism out
  of the unit sheaf of modules is an additive map out of the constant presheaf `ℤ` into the
  underlying abelian presheaf; both are the compatible families of sections.
* `Stacks.Cohomology.ModuleAbelianComparison.unitCoyonedaIso`: in degree zero, maps out of `R`
  and maps out of the constant sheaf `ℤ` into the underlying abelian sheaf agree.
* `Stacks.Cohomology.ModuleAbelianComparison.moduleFunctorHIso`: the comparison in every degree.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe w v u

namespace Stacks.Cohomology.ModuleAbelianComparison

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Sheaf J RingCat.{max u v w})

attribute [local instance] Stacks.Cohomology.BiggerSiteModules.hasSheafify_source
  Stacks.Cohomology.BiggerSiteModules.wEqualsLocallyBijective_source
  Stacks.Cohomology.ModuleAbelianComparison.hasExt
  Stacks.Cohomology.ModuleAbelianComparison.enoughInjectives

/-- The constant presheaf `ℤ` on a site, with values in the universe of the modules. Its
sheafification is `Stacks.Cohomology.ModuleAbelianComparison.constantZ`. -/
abbrev constantZPresheaf (C : Type u) [Category.{v} C] : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w} :=
  (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift ℤ))

/-- **A morphism out of the unit sheaf of modules is an additive map out of the constant presheaf
`ℤ`.** For a sheaf of `R`-modules `M`, both `Hom(R, M)` and `Hom(ℤ, M)`, the latter computed on
the underlying abelian presheaf, are the compatible families of sections of `M`: the first by
`CategoryTheory.SheafOfModules.unitHomEquiv`, the second by evaluation at the generator `1` of
`ℤ`. -/
def unitHomAddEquivConstantPresheafHom (M : SheafOfModules.{max u v w} R) :
    (SheafOfModules.unit R ⟶ M) ≃+
      (constantZPresheaf.{w} C ⟶ ((SheafOfModules.toSheaf R).obj M).obj) where
  toFun φ :=
    { app X := (AddCommGrpCat.uliftZMultiplesAddEquiv (M.val.presheaf.obj X)).symm
        ((M.unitHomEquiv φ).eval X)
      naturality := fun {X Y} f => by
        ext n
        change n.down • (M.unitHomEquiv φ).eval Y =
          M.val.presheaf.map f (n.down • (M.unitHomEquiv φ).eval X)
        exact (congrArg (n.down • ·) ((M.unitHomEquiv φ).property f).symm).trans
          (map_zsmul (M.val.presheaf.map f).hom n.down ((M.unitHomEquiv φ).eval X)).symm }
  invFun η := M.unitHomEquiv.symm (M.val.sectionsMk
    (fun X => AddCommGrpCat.uliftZMultiplesAddEquiv _ (η.app X))
    (fun {X Y} f => (ConcreteCategory.congr_hom (η.naturality f) (ULift.up (1 : ℤ))).symm))
  left_inv φ := M.unitHomEquiv.injective <| (Equiv.apply_symm_apply _ _).trans <|
    PresheafOfModules.sections_ext _ _ fun X =>
      (AddCommGrpCat.uliftZMultiplesAddEquiv _).apply_symm_apply _
  right_inv η := NatTrans.ext <| funext fun X => by
    change (AddCommGrpCat.uliftZMultiplesAddEquiv _).symm
      ((M.unitHomEquiv (M.unitHomEquiv.symm _)).val X) = η.app X
    rw [Equiv.apply_symm_apply]
    exact (AddCommGrpCat.uliftZMultiplesAddEquiv _).symm_apply_apply _
  map_add' φ ψ := NatTrans.ext <| funext fun X =>
    (AddCommGrpCat.uliftZMultiplesAddEquiv (M.val.presheaf.obj X)).symm.map_add
      ((M.unitHomEquiv φ).eval X) ((M.unitHomEquiv ψ).eval X)

/-- **Stacks 03FD in degree zero.** Morphisms out of the structure sheaf `R` and morphisms out of
the constant sheaf `ℤ` into the underlying abelian sheaf are the same functor of the sheaf of
`R`-modules: by `unitHomAddEquivConstantPresheafHom` and the sheafification adjunction, both are
the additive maps out of the constant presheaf `ℤ` into the underlying abelian presheaf. -/
def unitCoyonedaIso :
    preadditiveCoyoneda.obj (op (SheafOfModules.unit R)) ≅
      SheafOfModules.toSheaf.{max u v w} R ⋙ preadditiveCoyoneda.obj (op (constantZ.{w} J)) :=
  have : (presheafToSheaf J AddCommGrpCat.{max u v w}).Additive :=
    (sheafificationAdjunction J AddCommGrpCat.{max u v w}).left_adjoint_additive
  NatIso.ofComponents (G := SheafOfModules.toSheaf.{max u v w} R ⋙
      sheafToPresheaf J AddCommGrpCat.{max u v w} ⋙
        preadditiveCoyoneda.obj (op (constantZPresheaf.{w} C)))
    (fun M => (unitHomAddEquivConstantPresheafHom J R M).toAddCommGrpIso)
    (fun {M N} f => by
      ext φ : 2
      refine NatTrans.ext <| funext fun X => ?_
      ext n
      change n.down • (N.unitHomEquiv (φ ≫ f)).eval X =
        (f.val.app X).hom (n.down • (M.unitHomEquiv φ).eval X)
      exact (map_zsmul (f.val.app X).hom n.down ((M.unitHomEquiv φ).eval X)).symm) ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.toSheaf R)
      (Stacks.Cohomology.ObjectSections.coyonedaAdjunctionIso
        (sheafificationAdjunction J AddCommGrpCat.{max u v w}) (constantZPresheaf.{w} C))

/-- **Stacks 03FD, global cohomology.** On any site, for every degree `n` the cohomology
`Ext^n(R, M)` of a sheaf of `R`-modules is the cohomology `H^n(C, M)` of its underlying abelian
sheaf, naturally in `M`.

Both sides are `δ`-functors on sheaves of `R`-modules — the second because forgetting to abelian
sheaves is exact — they agree in degree zero by `unitCoyonedaIso`, and both are universal: the
second because the underlying abelian sheaf of an injective sheaf of modules has no higher `Ext`
out of the sectionwise torsion-free sheaf `ℤ`. This is
`Stacks.Cohomology.ModuleAbelianComparison.moduleFunctorHIsoOfIsTerminal` with the terminal object
removed. -/
@[sga "7 IX 9.4.3" "(a), special case"]
def moduleFunctorHIso (n : ℕ) :
    Stacks.Cohomology.BiggerSiteModules.moduleFunctorH.{w, v, u} J R n ≅
      SheafOfModules.toSheaf.{max u v w} R ⋙ Sheaf.functorH.{max u v w} J n := by
  haveI := Stacks.Cohomology.ObjectSections.toSheaf_preservesFiniteColimits (J := J) R
  have h : ∀ (I : SheafOfModules.{max u v w} R) [Injective I] (m : ℕ)
      (e : Ext (constantZ.{w} J) ((SheafOfModules.toSheaf R).obj I) (m + 1)), e = 0 :=
    fun I _ m e => Stacks.Cohomology.ObjectSections.ext_eq_zero_of_isTorsionFree J R I _
      (constantZ_isTorsionFree J) m e
  exact ModuleSheafCohomology.extComparisonIso (SheafOfModules.toSheaf R) (constantZ.{w} J)
    (SheafOfModules.unit R) h (unitCoyonedaIso J R) n

end Stacks.Cohomology.ModuleAbelianComparison

end
