module

public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroUnitSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriekAndPerfection.SliceUnitModule
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects

/-!
# The extension by zero of the structure sheaf at a final object is the structure sheaf

Let `(C, O)` be a ringed site and let `T` be a final object of `C`. Then the extension by zero
`j_{T!} O_T` of the structure sheaf of the localised site `C/T` is the structure sheaf `O`
itself, and this file proves it, both at the derived level and at the abelian one.

The argument is Yoneda's. Morphisms out of `j_{T!} O_T` are the sections of the target over
`T`, which is Stacks 0G1V; morphisms out of `O` are the global sections of the target
(`SheafOfModules.unitHomEquiv`), which for a site with a final object are again its sections
over that object
(`Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal`). Both bijections are natural
in the target, so the two objects corepresent the same functor and the mutually inverse
morphisms are the ones the two bijections attach to the two identities.

Two spellings of `j_{T!} O_T` are in use in this library and both are covered, because the two
clauses of Stacks 09JC — and hence of Stacks 09J7 — are stated with different ones:

* `Stacks.SheafOfModules.pullback` along `Over.forget T` applied to
  `SheafOfModules.unit (O.over T)`, the spelling of
  `Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv`; this one is proved with all three
  universes of the site and the ring independent.
* `Stacks.Sites.OverModules.extensionByZeroUnit`, the `ULift`ed construction of
  `Stacks.Sites.OverModules.extensionByZeroHomEquiv`; this one lives in the module universe
  `max u v w m` and so is proved where that universe is the ring universe, which is the
  instantiation `.{u, u, u, u}` its consumers use.

## Main results

* `Stacks.Sites.ExtensionByZero.unitHomEquivOfTerminal`: `Hom_O(O, F) = F(T)` for `T` final,
  with `Stacks.Sites.ExtensionByZero.unitHomEquivOfTerminal_naturality`.
* `Stacks.Sites.ExtensionByZero.extensionByZeroUnitIsoUnitOfTerminal`: `j_{T!} O_T ≅ O`, in the
  pullback spelling.
* `Stacks.Sites.OverModules.extensionByZeroUnitIsoUnitOfTerminal`: `j_{T!} O_T ≅ O`, in the
  `ULift`ed spelling.
* `AlgebraicGeometry.RingedSite.derivedExtensionByZeroUnitIsoStructureSheaf` and
  `AlgebraicGeometry.RingedSite.derivedOverExtensionByZeroUnitIsoStructureSheaf`: the two
  identifications in `D(O)`, which is the form in which they are consumed.

## No tag is carried

Nothing here is a clause of a Stacks statement. The identification of the source object is a
step of the proof of Stacks 09JC — it is what turns the bijection
`Hom_{D(O)}(K, N) = Hom_{D(O)}(O, K^∨ ⊗^L_O N)` of Stacks 08JJ into the bijection
`Hom_{D(O)}(K, N) = Hom_{D(O)}(j_{T!}O_T, K^∨ ⊗^L_O N)` that the hypothesis `hreduce` of
`Stacks.Cohomology.RingedSite.isCompactObject_of_isPerfect` and of
`Stacks.Cohomology.RingedSpaceCompact.isCompactObject_of_isPerfect` is stated with. Stacks 0G1V,
which the proof uses, is already registered on
`Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv`.

## References

* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
* [Stacks Project, Tag 09JC](https://stacks.math.columbia.edu/tag/09JC)
* [Stacks Project, Tag 09J7](https://stacks.math.columbia.edu/tag/09J7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sites.ExtensionByZero

universe w v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  (R : Sheaf J RingCat.{w}) (T : C)

/-- **Morphisms out of the structure sheaf are the sections over a final object.** Mathlib's
`SheafOfModules.unitHomEquiv` identifies them with the global sections, and a global section of
a sheaf of modules on a site with a final object is a section over that object. -/
noncomputable def unitHomEquivOfTerminal (hT : IsTerminal T) (F : SheafOfModules.{w} R) :
    (SheafOfModules.unit R ⟶ F) ≃ (F.val.obj (op T) : Type w) :=
  F.unitHomEquiv.trans
    (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal F hT)

/-- `unitHomEquivOfTerminal` is natural in the sheaf of modules: both of its factors read off a
value of the morphism on sections, so composing with `g` applies `g` on sections over `T`. -/
theorem unitHomEquivOfTerminal_naturality (hT : IsTerminal T) {F G : SheafOfModules.{w} R}
    (f : SheafOfModules.unit R ⟶ F) (g : F ⟶ G) :
    unitHomEquivOfTerminal J R T hT G (f ≫ g) =
      g.val.app (op T) (unitHomEquivOfTerminal J R T hT F f) := rfl

variable [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(SheafOfModules.pushforward.{w} (F := Over.forget T)
    (𝟙 (R.over T) : (R.over T) ⟶ (R.over T))).IsRightAdjoint]

/-- **The extension by zero of the structure sheaf of `C/T` at a final object `T` is the
structure sheaf.** Both objects corepresent the sections over `T`, by Stacks 0G1V and by
`unitHomEquivOfTerminal`, and both bijections are natural in the target; the two morphisms are
the ones those bijections attach to the two identity morphisms, and each composite is an
identity because applying either bijection to it gives the value it gives to the identity. -/
noncomputable def extensionByZeroUnitIsoUnitOfTerminal (hT : IsTerminal T) :
    (SheafOfModules.pullback.{w} (F := Over.forget T)
      (𝟙 (R.over T) : (R.over T) ⟶ (R.over T))).obj
        (SheafOfModules.unit (R.over T)) ≅ SheafOfModules.unit R where
  hom := (extensionByZeroUnitHomEquiv J R T (SheafOfModules.unit R)).symm
    (unitHomEquivOfTerminal J R T hT (SheafOfModules.unit R) (𝟙 _))
  inv := (unitHomEquivOfTerminal J R T hT _).symm
    (extensionByZeroUnitHomEquiv J R T _ (𝟙 _))
  hom_inv_id := by
    refine (extensionByZeroUnitHomEquiv J R T _).injective ?_
    rw [extensionByZeroUnitHomEquiv_naturality, Equiv.apply_symm_apply]
    have h := unitHomEquivOfTerminal_naturality J R T hT (𝟙 (SheafOfModules.unit R))
      ((unitHomEquivOfTerminal J R T hT _).symm
        (extensionByZeroUnitHomEquiv J R T _ (𝟙 _)))
    rw [Category.id_comp, Equiv.apply_symm_apply] at h
    exact h.symm
  inv_hom_id := by
    refine (unitHomEquivOfTerminal J R T hT _).injective ?_
    rw [unitHomEquivOfTerminal_naturality, Equiv.apply_symm_apply]
    have h := extensionByZeroUnitHomEquiv_naturality J R T (𝟙 _)
      ((extensionByZeroUnitHomEquiv J R T (SheafOfModules.unit R)).symm
        (unitHomEquivOfTerminal J R T hT (SheafOfModules.unit R) (𝟙 _)))
    rw [Category.id_comp, Equiv.apply_symm_apply] at h
    exact h.symm

end Stacks.Sites.ExtensionByZero

namespace Stacks.Sites.OverModules

universe u

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  (O : Sheaf J RingCat.{u}) (T : C)
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The extension by zero of the structure sheaf of `C/T` at a final object `T` is the
structure sheaf**, for the `ULift`ed construction of `extensionByZeroUnit`. This is the same
Yoneda argument as `Stacks.Sites.ExtensionByZero.extensionByZeroUnitIsoUnitOfTerminal`, run on
`extensionByZeroHomEquiv` instead; the module universe of `extensionByZeroUnit` is
`max u v w m`, so the statement is at the instantiation where that is the ring universe. -/
noncomputable def extensionByZeroUnitIsoUnitOfTerminal (hT : IsTerminal T) :
    extensionByZeroUnit.{u, u, u, u} J O T ≅ SheafOfModules.unit O where
  hom := (extensionByZeroHomEquiv.{u, u, u, u} J O T (SheafOfModules.unit O)).symm
    (Stacks.Sites.ExtensionByZero.unitHomEquivOfTerminal J O T hT
      (SheafOfModules.unit O) (𝟙 _))
  inv := (Stacks.Sites.ExtensionByZero.unitHomEquivOfTerminal J O T hT _).symm
    (extensionByZeroHomEquiv.{u, u, u, u} J O T _ (𝟙 _))
  hom_inv_id := by
    refine (extensionByZeroHomEquiv.{u, u, u, u} J O T _).injective ?_
    rw [extensionByZeroHomEquiv_naturality, Equiv.apply_symm_apply]
    have h := Stacks.Sites.ExtensionByZero.unitHomEquivOfTerminal_naturality J O T hT
      (𝟙 (SheafOfModules.unit O))
      ((Stacks.Sites.ExtensionByZero.unitHomEquivOfTerminal J O T hT _).symm
        (extensionByZeroHomEquiv.{u, u, u, u} J O T _ (𝟙 _)))
    rw [Category.id_comp, Equiv.apply_symm_apply] at h
    exact h.symm
  inv_hom_id := by
    refine (Stacks.Sites.ExtensionByZero.unitHomEquivOfTerminal J O T hT _).injective ?_
    rw [Stacks.Sites.ExtensionByZero.unitHomEquivOfTerminal_naturality, Equiv.apply_symm_apply]
    have h := extensionByZeroHomEquiv_naturality.{u, u, u, u} J O T (𝟙 _)
      ((extensionByZeroHomEquiv.{u, u, u, u} J O T (SheafOfModules.unit O)).symm
        (Stacks.Sites.ExtensionByZero.unitHomEquivOfTerminal J O T hT
          (SheafOfModules.unit O) (𝟙 _)))
    rw [Category.id_comp, Equiv.apply_symm_apply] at h
    exact h.symm

end Stacks.Sites.OverModules

namespace AlgebraicGeometry.RingedSite

open AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (T : X.C)

/-- **`j_{T!}O_T[0] ≅ O[0]` in `D(O)`, for `T` a final object of the site**, in the pullback
spelling. This is the identification that Stacks 09JC's hypothesis on the reduction of Stacks
08JJ is stated against: the bijection Stacks 08JJ produces has the structure sheaf as its
source, and clause (b) of Stacks 09JC asks for it with `j_{T!}O_T` there. -/
noncomputable def derivedExtensionByZeroUnitIsoStructureSheaf (hT : IsTerminal T) :
    (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        ((SheafOfModules.pullback.{u} (F := Over.forget T)
          (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over T))).obj
            (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over T))) ≅
      (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (DerivedCategory.singleFunctor _ 0).mapIso
    (Stacks.Sites.ExtensionByZero.extensionByZeroUnitIsoUnitOfTerminal X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) T hT)

/-- **`j_{T!}O_T[0] ≅ O[0]` in `D(O)`, for `T` a final object of the site**, in the `ULift`ed
spelling of `Stacks.Sites.OverModules.extensionByZeroUnit`. This is the one clause (a) of Stacks
09JC is stated against. -/
noncomputable def derivedOverExtensionByZeroUnitIsoStructureSheaf (hT : IsTerminal T) :
    (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        (Stacks.Sites.OverModules.extensionByZeroUnit.{u, u, u, u} X.J
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) T) ≅
      (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (DerivedCategory.singleFunctor _ 0).mapIso
    (Stacks.Sites.OverModules.extensionByZeroUnitIsoUnitOfTerminal X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) T hT)

end AlgebraicGeometry.RingedSite

end
