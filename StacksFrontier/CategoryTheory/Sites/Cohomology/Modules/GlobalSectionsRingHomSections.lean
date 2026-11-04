module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesCompIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnitValue
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.GlobalSectionsRingHomComposition

/-!
# The ring map on global sections, on an actual family of sections

**Stacks 0732** attaches to a morphism of ringed topoi `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)`
the ring map `Γ(D, O_D) ⟶ Γ(C, O_C)` on global sections,
`Stacks.Cohomology.SiteModules.globalSectionsRingHom`.  It is *constructed* from the action of a
global section of `O_D` on the free `O_D`-module of rank one, transported to the free
`O_C`-module of rank one, and before this file it was pinned down only by
`Stacks.Cohomology.SiteModules.unitEnd_globalSectionsRingHom` — that is, only through the
endomorphism of the free module of rank one it induces.  Nothing said what it does to a
compatible family of sections.

This file says it: **`globalSectionsRingHom f` is `Γ` of the structure morphism of `f`.**  A
global section `a` of `O_D` is read as a morphism `1 ⟶ O_D` out of the terminal sheaf
(`CategoryTheory.Sheaf.ringSectionHom`), and then

* composing with the *direct-image* form `f♯ : O_D ⟶ f_*O_C` of the structure map and reading
  the result back as a global section of `O_C` along the canonical identification
  `Γ(D, f_*O_C) = Γ(C, O_C)` gives `globalSectionsRingHom f a`
  (`Stacks.Cohomology.SiteModules.ringSectionHom_globalSectionsRingHom`);
* equivalently, taking the inverse image `f⁻¹a : 1 ⟶ f⁻¹O_D` and composing with the
  *inverse-image* form `f♯ : f⁻¹O_D ⟶ O_C` gives it on the nose, so that its value at an object
  `Z` of `C` is the one value `f♯` takes there
  (`Stacks.Cohomology.SiteModules.ringSectionHom_globalSectionsRingHom_inverseImage` and
  `Stacks.Cohomology.SiteModules.globalSectionsRingHom_val_apply`).

## Main definitions

* `CategoryTheory.Sheaf.ringSectionHom`: a compatible family of sections of a sheaf of rings,
  read as a morphism out of the terminal sheaf.

## Main results

* `Stacks.Cohomology.SiteModules.moduleSheafFunctor_map_pushforwardUnitSection`: **the canonical
  morphism `1_{O_D} ⟶ f_*1_{O_C}` is the structure map `f♯`**, on underlying sheaves of sets.
  This is the one step with content: `Stacks.Cohomology.SiteModules.pushforwardUnitSection` is
  built from the corepresentability comparison `f^*O_D ≅ O_C`, and identifying it with the
  structure map is the formula for that comparison.
* `Stacks.Cohomology.SiteModules.ringSectionHom_globalSectionsRingHom`: **the ring map on global
  sections is `Γ(f♯)`**, read through the canonical identification `Γ(D, f_*O_C) = Γ(C, O_C)`.
* `Stacks.Cohomology.SiteModules.ringSectionHom_globalSectionsRingHom_inverseImage`: the same in
  the inverse-image form, `a ↦ f♯ ∘ f⁻¹a`.
* `Stacks.Cohomology.SiteModules.globalSectionsRingHom_val_apply` and
  `Stacks.Cohomology.SiteModules.globalSectionsRingHom_val_apply_fSharpInverseImage`: **the value
  of `globalSectionsRingHom f a` at an object `Z` of `C`**, the second with the structure map
  applied as a ring homomorphism on sections over `Z`.

## Implementation notes

The derivation is the one the construction prescribes.  The ring map is pinned by the
endomorphism of the free module of rank one it induces
(`Stacks.Cohomology.SiteModules.unitEnd_globalSectionsRingHom`); that endomorphism is the
transpose of multiplication by the scalar followed by the canonical morphism
`Stacks.Cohomology.SiteModules.pushforwardUnitSection`
(`Stacks.Cohomology.SiteModules.pushforwardUnitEndMap_eq`); and the transposition is, on
underlying sheaves of sets, the purely geometric comparison of global sections
(`Stacks.Cohomology.SiteModules.unitTerminalHomEquiv_pushforwardUnitHomEquiv`).  Evaluating all
of this at the unit section — which is what
`CategoryTheory.Sheaf.unitTerminalHomEquiv_unitEnd` does, the free module of rank one being the
sheaf of rings itself — leaves exactly `Γ(f♯)`.

The one non-formal step is `moduleSheafFunctor_map_pushforwardUnitSection`.  The canonical
morphism `1_{O_D} ⟶ f_*1_{O_C}` is the transpose of the comparison `f^*O_D ≅ O_C` of
`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso`, which is produced by
corepresentability and so carries no formula of its own; the formula is
`moduleSheafFunctor_map_fSharpAdjunction_homEquiv_pullbackModulesObjUnitIso_inv` (in
`Stacks.Sheaves.RingedToposModules`), and it says that the comparison transposes to the
inverse-image form of the structure map.  That is why this file carries the two instances
`HasWeakSheafify Y.J AddCommGrpCat.{w'}` and `Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}`
beyond those of `Stacks.Cohomology.SiteModules.globalSectionsRingHom`: they are what the explicit
comparison `Stacks.Sheaves.FinitePresentation.pullbackModulesUnitIso`, through which that formula
is obtained, is stated with.  They are instance arguments of the cited machinery and not
mathematical hypotheses; at the small étale seating of an algebraic space both hold.

As elsewhere in this development the object universes of the two sites and the two coefficient
universes are independent.

## References

* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry (RingedTopos)
open Stacks.Sheaves.RingedToposModules
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe w w' v u v' u'

namespace CategoryTheory.Sheaf

section RingSection

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})]

/-- **A compatible family of sections of a sheaf of rings, as a morphism out of the terminal
sheaf.**  The terminal sheaf has exactly one section over every object of the site, so a
morphism out of it into the underlying sheaf of sets of `R` is the same thing as a global
section of `R`; this is that reading, for the sections of `R` presented as an element of
`RingCat.sectionsSubring`.

At `a = 1` it is `CategoryTheory.Sheaf.ringOneHom`, by `ringSectionHom_one`. -/
def ringSectionHom (R : Sheaf J RingCat.{w}) (a : RingCat.sectionsSubring R.obj) :
    ⊤_ (Sheaf J (Type w)) ⟶ ringSheaf R :=
  constHom (E := ringSheaf R) (fun Z ↦ a.1 Z) (fun g ↦ a.2 g)

/-- The unit section of a sheaf of rings, read as a morphism out of the terminal sheaf, is
`CategoryTheory.Sheaf.ringOneHom`. -/
@[simp]
lemma ringSectionHom_one (R : Sheaf J RingCat.{w}) : ringSectionHom R 1 = ringOneHom R :=
  rfl

/-- The morphism `CategoryTheory.Sheaf.ringSectionHom R a` sends the unique section of the
terminal sheaf over `Z` to the section `a` over `Z`. -/
@[simp]
lemma ringSectionHom_hom_app (R : Sheaf J RingCat.{w})
    (a : RingCat.sectionsSubring R.obj) (Z : Cᵒᵖ)
    (p : (⊤_ (Sheaf J (Type w))).obj.obj Z) :
    (ringSectionHom R a).hom.app Z p = a.1 Z :=
  rfl

variable [J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- **Multiplication by a global section, read as a global section, is that global section.**
Under the identification of morphisms out of the free sheaf of modules of rank one with global
sections of the underlying sheaf of sets, the endomorphism
`Stacks.Cohomology.SiteModules.unitEnd` of multiplication by `a` is `a` itself: its value at the
unit section is `1 * a = a`. -/
lemma unitTerminalHomEquiv_unitEnd (R : Sheaf J RingCat.{w})
    (a : RingCat.sectionsSubring R.obj) :
    unitTerminalHomEquiv R (SheafOfModules.unit R)
        (Stacks.Cohomology.SiteModules.unitEnd R a) = ringSectionHom R a :=
  hom_ext_sections fun Z _ ↦ one_mul (a.1 Z)

end RingSection

end CategoryTheory.Sheaf

namespace Stacks.Cohomology.SiteModules

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : RingedToposHom X Y)

/-- The canonical morphism `1_{O_D} ⟶ f_*1_{O_C}` of
`Stacks.Cohomology.SiteModules.pushforwardUnitSection` is the transpose, along the adjunction of
**Stacks 03D7**, of the comparison `f^*O_D ⟶ O_C` of **Stacks 03D6**, part (2).

The morphism is *defined* as the preimage of the identity under
`Stacks.Cohomology.SiteModules.pushforwardUnitHomEquiv`, which is that transposition followed by
precomposition with the comparison; so the comparison cancels against its own inverse. -/
lemma pushforwardUnitSection_eq :
    pushforwardUnitSection f =
      (pullbackAdjPushforwardModules f).homEquiv _ _ (pullbackModulesObjUnitIso f).inv := by
  rw [pushforwardUnitSection, Equiv.symm_apply_eq, pushforwardUnitHomEquiv_apply,
    Equiv.symm_apply_apply, Iso.hom_inv_id]

/-- **The canonical morphism `1_{O_D} ⟶ f_*1_{O_C}` is the structure map `f♯`**, on underlying
sheaves of sets.

This is the one step of this file that is not formal.  The morphism is the transpose of the
comparison `f^*O_D ≅ O_C`, which `Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso`
produces by corepresentability and so with no formula; the formula is
`Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_pullbackAdjPushforwardModules_homEquiv`,
which says the transpose of the comparison is the inverse-image form of the structure map on
underlying sheaves of sets.  The adjunctness field of the morphism of ringed topoi then turns
the inverse-image form into the direct-image form.

The proof is a term rather than a rewrite because the sheaf of rings `f⁻¹O_D` is reached by
three routes that agree by `rfl` but are not syntactically equal, so a goal carrying two of them
is not type-correct at `implicit` transparency; this is the discipline recorded in the
implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnitValue`. -/
lemma moduleSheafFunctor_map_pushforwardUnitSection :
    (Sheaf.moduleSheafFunctor (ringSheaf Y.O)).map (pushforwardUnitSection f) =
      fSharpSet f :=
  (congrArg (Sheaf.moduleSheafFunctor (ringSheaf Y.O)).map
      ((pushforwardUnitSection_eq f).trans
        (congrArg (fun e : SheafOfModules.unit (ringSheaf X.O) ≅
              (f.pullbackModules).obj (SheafOfModules.unit (ringSheaf Y.O)) ↦
            (pullbackAdjPushforwardModules f).homEquiv _ _ e.inv)
          (pullbackModulesObjUnitIso_eq f)))).trans
    ((moduleSheafFunctor_map_pullbackAdjPushforwardModules_homEquiv f).trans
      f.fSharp_adjunct.symm)

/-- **The ring map on global sections of Stacks 0732 is `Γ` of the structure morphism.**  For a
global section `a` of `O_D`, read as a morphism `1 ⟶ O_D` out of the terminal sheaf, the global
section `globalSectionsRingHom f a` of `O_C` is `a` composed with the direct-image form
`f♯ : O_D ⟶ f_*O_C` of the structure map, read back as a global section of `O_C` along the
canonical identification `Γ(D, f_*O_C) = Γ(C, O_C)` of
`MorphismOfTopoi.pushforwardTerminalHomEquiv`.

This is the description of `Stacks.Cohomology.SiteModules.globalSectionsRingHom` on an actual
family of sections.  Before it the map was pinned down only by
`Stacks.Cohomology.SiteModules.unitEnd_globalSectionsRingHom`, through the endomorphism of the
free module of rank one it induces. -/
theorem ringSectionHom_globalSectionsRingHom
    (a : RingCat.sectionsSubring (ringSheaf Y.O).obj) :
    Sheaf.ringSectionHom (ringSheaf X.O) (globalSectionsRingHom f a) =
      f.toToposHom.pushforwardTerminalHomEquiv (Sheaf.ringSheaf (ringSheaf X.O))
        (Sheaf.ringSectionHom (ringSheaf Y.O) a ≫ fSharpSet f) := by
  rw [← unitTerminalHomEquiv_unitEnd (ringSheaf X.O) (globalSectionsRingHom f a),
    unitEnd_globalSectionsRingHom, pushforwardUnitEndMap_eq,
    unitTerminalHomEquiv_pushforwardUnitHomEquiv]
  show f.toToposHom.pushforwardTerminalHomEquiv (Sheaf.ringSheaf (ringSheaf X.O))
      (unitTerminalHomEquiv (ringSheaf Y.O)
        ((pushforwardModules f).obj (SheafOfModules.unit (ringSheaf X.O)))
        (unitEnd (ringSheaf Y.O) a ≫ pushforwardUnitSection f)) = _
  rw [unitTerminalHomEquiv_comp, unitTerminalHomEquiv_unitEnd,
    moduleSheafFunctor_map_pushforwardUnitSection]
  rfl

/-- **The ring map on global sections, transposed: `f♯ ∘ a = f_*(globalSectionsRingHom f a)`.**
The global section `a` of `O_D` followed by the direct-image form `f♯ : O_D ⟶ f_*O_C` of the
structure map is the direct image of the global section `globalSectionsRingHom f a` of `O_C`,
precomposed with a morphism `1 ⟶ f_*1`.

This is the form in which the description is *computable*: neither side involves the
identification `Γ(D, f_*O_C) = Γ(C, O_C)` or any other bijection, only `f♯` and a direct image.
The morphism `α : 1 ⟶ f_*1` may be chosen at will — `f_*1` is terminal, a direct image being a
right adjoint, so there is only one — which is exactly the content of
`MorphismOfTopoi.pushforwardTerminalHomEquiv_symm_eq`. -/
theorem ringSectionHom_comp_fSharpSet
    (a : RingCat.sectionsSubring (ringSheaf Y.O).obj)
    (α : ⊤_ (Sheaf Y.J (Type w')) ⟶
      f.toToposHom.pushforward.obj (⊤_ (Sheaf X.J (Type w)))) :
    Sheaf.ringSectionHom (ringSheaf Y.O) a ≫ fSharpSet f =
      α ≫ f.toToposHom.pushforward.map
        (Sheaf.ringSectionHom (ringSheaf X.O) (globalSectionsRingHom f a)) :=
  ((Equiv.symm_apply_eq _).mpr (ringSectionHom_globalSectionsRingHom f a)).symm.trans
    (MorphismOfTopoi.pushforwardTerminalHomEquiv_symm_eq f.toToposHom _ _ α)

/-- **The ring map on global sections, in the inverse-image form of the structure map.**  The
global section `globalSectionsRingHom f a` of `O_C` is the inverse image `f⁻¹a` of the global
section `a` of `O_D` followed by the inverse-image form `f♯ : f⁻¹O_D ⟶ O_C` of the structure
map.

Unlike `Stacks.Cohomology.SiteModules.ringSectionHom_globalSectionsRingHom` this involves no
transposition: the canonical identification `Γ(D, f_*O_C) = Γ(C, O_C)` *is* the transposition
across `f⁻¹ ⊣ f_*`, and the direct-image form of the structure map is the transpose of the
inverse-image form, so the two cancel.  This is what makes the value at an object of `C`
readable off, in `Stacks.Cohomology.SiteModules.globalSectionsRingHom_val_apply`. -/
theorem ringSectionHom_globalSectionsRingHom_inverseImage
    (a : RingCat.sectionsSubring (ringSheaf Y.O).obj) :
    Sheaf.ringSectionHom (ringSheaf X.O) (globalSectionsRingHom f a) =
      (MorphismOfTopoi.inverseImageTerminalIso f.toToposHom).inv ≫
        f.toToposHom.inverseImage.map (Sheaf.ringSectionHom (ringSheaf Y.O) a) ≫
          (sheafCompose X.J (forget RingCat.{w})).map f.fSharpInverseImage := by
  refine (ringSectionHom_globalSectionsRingHom f a).trans ?_
  show (MorphismOfTopoi.inverseImageTerminalIso f.toToposHom).inv ≫
      (f.toToposHom.adj.homEquiv _ (Sheaf.ringSheaf (ringSheaf X.O))).symm
        (Sheaf.ringSectionHom (ringSheaf Y.O) a ≫ fSharpSet f) = _
  rw [show fSharpSet f = f.toToposHom.adj.homEquiv (Sheaf.ringSheaf (ringSheaf Y.O))
      (Sheaf.ringSheaf (ringSheaf X.O))
      ((sheafCompose X.J (forget RingCat.{w})).map f.fSharpInverseImage) from f.fSharp_adjunct,
    Adjunction.homEquiv_naturality_left_symm]
  exact congrArg (fun z ↦ (MorphismOfTopoi.inverseImageTerminalIso f.toToposHom).inv ≫
      f.toToposHom.inverseImage.map (Sheaf.ringSectionHom (ringSheaf Y.O) a) ≫ z)
    ((f.toToposHom.adj.homEquiv (Sheaf.ringSheaf (ringSheaf Y.O))
      (Sheaf.ringSheaf (ringSheaf X.O))).symm_apply_apply _)

/-- **The value of `globalSectionsRingHom f a` over an object `Z` of `C`.**  It is the value over
`Z` of the inverse image `f⁻¹a` of the global section `a`, pushed through the inverse-image form
`f♯ : f⁻¹O_D ⟶ O_C` of the structure map.

This is what lets a caller compute the ring map rather than only characterise it. -/
theorem globalSectionsRingHom_val_apply
    (a : RingCat.sectionsSubring (ringSheaf Y.O).obj) (Z : X.Cᵒᵖ) :
    (globalSectionsRingHom f a).1 Z =
      ((MorphismOfTopoi.inverseImageTerminalIso f.toToposHom).inv ≫
        f.toToposHom.inverseImage.map (Sheaf.ringSectionHom (ringSheaf Y.O) a) ≫
          (sheafCompose X.J (forget RingCat.{w})).map f.fSharpInverseImage).hom.app Z
        (Sheaf.terminalSheafSection X.J Z) := by
  rw [← ringSectionHom_globalSectionsRingHom_inverseImage, ringSectionHom_hom_app]

/-- **The value of `globalSectionsRingHom f a` over an object `Z` of `C`**, with the structure
map applied as a ring homomorphism on sections over `Z`: it is
`f♯_Z` of the value over `Z` of the inverse image of `a`.

Both sides evaluate the same three-fold composite of morphisms of sheaves of sets at the same
section, so the two differ by nothing but the bracketing of a function composition. -/
theorem globalSectionsRingHom_val_apply_fSharpInverseImage
    (a : RingCat.sectionsSubring (ringSheaf Y.O).obj) (Z : X.Cᵒᵖ) :
    (globalSectionsRingHom f a).1 Z =
      (f.fSharpInverseImage.hom.app Z).hom
        (((MorphismOfTopoi.inverseImageTerminalIso f.toToposHom).inv ≫
          f.toToposHom.inverseImage.map
            (Sheaf.ringSectionHom (ringSheaf Y.O) a)).hom.app Z
          (Sheaf.terminalSheafSection X.J Z)) :=
  (globalSectionsRingHom_val_apply f a Z).trans rfl

end Stacks.Cohomology.SiteModules

end
