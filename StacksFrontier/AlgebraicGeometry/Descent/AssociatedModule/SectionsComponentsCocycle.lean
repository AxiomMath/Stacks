module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SectionsComponentsInduced

/-!
# The comparison of sections of Stacks 03DV is induced by an arrow of the site

`AlgebraicGeometry.BigFppfOver.objRestrictSectionsIso` compares the two routes from a sheaf of
modules on the big fppf site of the scheme of `T` to an `𝒪_S`-module.  Its explicit form,
`AlgebraicGeometry.BigFppfOver.objRestrictSectionsIso_eq_explicit`, is a composite of eleven
factors each of which is given on sections by restriction along an arrow of the big fppf site.
This file performs the induction: both the comparison and its inverse are
`Stacks.SectionsComponents.Induced`, with source and target the two objects of the site through
which the two routes read sections.

## Main results

* `AlgebraicGeometry.BigFppfOver.induced_objRestrictSectionsIso_hom` and
  `AlgebraicGeometry.BigFppfOver.induced_objRestrictSectionsIso_inv`: **the comparison of
  sections, and its inverse, are restriction along an arrow of the big fppf site over the scheme
  of `T`** — from the fibre product of `T` with an open of `S` to the open of the scheme of `T`
  that is the preimage of that open.

## Implementation notes

Nothing here carries a `stacks` attribute.

The proofs are deterministic scripts following the shape of
`objRestrictSectionsIso_eq_explicit`: one `Stacks.SectionsComponents.Induced` combinator per
factor, applied by `apply` with `newGoals := .nonDependentOnly` so that the object of the site at
which the two halves of a composite meet is left to unification rather than becoming a goal.  No
step of the script ever *fails* — a failing unification against these composites costs tens of
thousands of heartbeats, which is why the script is written out rather than searched for.

The continuity hypotheses of the leaves are supplied as `@… ..`, all arguments left to
unification: at the point where instance search would run, the functor and the topology are still
metavariables, and `CategoryTheory.Functor.IsContinuous` is a proposition, so any witness will do.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u u₀ v₀

open Stacks.SectionsComponents in
local macro "indT" : tactic =>
  `(tactic| apply (config := { newGoals := .nonDependentOnly }) Induced.isoTransHom)
open Stacks.SectionsComponents in
local macro "indTi" : tactic =>
  `(tactic| apply (config := { newGoals := .nonDependentOnly }) Induced.isoTransInv)
open Stacks.SectionsComponents in
local macro "indS" : tactic =>
  `(tactic| apply (config := { newGoals := .nonDependentOnly }) Induced.isoSymmHom)
open Stacks.SectionsComponents in
local macro "indSi" : tactic =>
  `(tactic| apply (config := { newGoals := .nonDependentOnly }) Induced.isoSymmInv)
open Stacks.SectionsComponents in
local macro "indWR" : tactic =>
  `(tactic| apply (config := { newGoals := .nonDependentOnly }) Induced.isoWhiskerRightHom)
open Stacks.SectionsComponents in
local macro "indWRi" : tactic =>
  `(tactic| apply (config := { newGoals := .nonDependentOnly }) Induced.isoWhiskerRightInv)

namespace AlgebraicGeometry.BigFppfOver

open Stacks.SheafOfModules Stacks.SectionsComponents

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Two further leaves -/

/-- **The transport of a pushforward of modules on schemes along an equality of morphisms is
restriction along the induced equality of opens.** -/
public theorem induced_eqToIso_pushforward_hom {X Y : Scheme.{u}} (N : X.Modules) {k₁ k₂ : X ⟶ Y}
    (h : k₁ = k₂) (p : Scheme.Modules.pushforward k₁ = Scheme.Modules.pushforward k₂)
    (Z : Y.Opens) :
    Induced N ((eqToIso p).hom.app N) (op Z)
      ((TopologicalSpace.Opens.map k₁.base).obj Z)
      ((TopologicalSpace.Opens.map k₂.base).obj Z) :=
  ⟨eqToHom (congrArg
      (fun k : X ⟶ Y => (TopologicalSpace.Opens.map k.base).obj Z) h.symm), rfl, rfl,
    Stacks.SectionsComponents.eqToIso_schemePushforward_hom_app_val_app h N (op Z)⟩

/-- **The inverse transport of a pushforward of modules on schemes along an equality of
morphisms.** -/
public theorem induced_eqToIso_pushforward_inv {X Y : Scheme.{u}} (N : X.Modules) {k₁ k₂ : X ⟶ Y}
    (h : k₁ = k₂) (p : Scheme.Modules.pushforward k₁ = Scheme.Modules.pushforward k₂)
    (Z : Y.Opens) :
    Induced N ((eqToIso p).inv.app N) (op Z)
      ((TopologicalSpace.Opens.map k₂.base).obj Z)
      ((TopologicalSpace.Opens.map k₁.base).obj Z) :=
  ⟨eqToHom (congrArg (fun k : X ⟶ Y => (TopologicalSpace.Opens.map k.base).obj Z) h), rfl, rfl,
    Stacks.SectionsComponents.eqToIso_schemePushforward_inv_app_val_app h N (op Z)⟩

/-- **Restriction along equal arrows of a site agrees on sections**, by the induced equality of
base changes. -/
public theorem induced_overPullbackCongr_hom {C₀ : Type u₀} [Category.{v₀} C₀]
    [HasPullbacks C₀]
    {J₀ : GrothendieckTopology C₀} (R : Sheaf J₀ RingCat.{u}) {V W : C₀} {a b : V ⟶ W}
    (e : a = b) (N : SheafOfModules.{u} (R.over V)) (A : (Over W)ᵒᵖ) :
    Induced N ((Stacks.SheafOfModules.overPullbackCongr R e).hom.app N) A
      ((Over.pullback a).obj A.unop) ((Over.pullback b).obj A.unop) :=
  ⟨eqToHom (congrArg (fun k : V ⟶ W => (Over.pullback k).obj A.unop) e.symm), rfl, rfl,
    Stacks.SectionsComponents.overPullbackCongr_hom_app_val_app R e N A⟩

/-- **The inverse of the transport of a base change along an equality of arrows.** -/
public theorem induced_overPullbackCongr_inv {C₀ : Type u₀} [Category.{v₀} C₀]
    [HasPullbacks C₀]
    {J₀ : GrothendieckTopology C₀} (R : Sheaf J₀ RingCat.{u}) {V W : C₀} {a b : V ⟶ W}
    (e : a = b) (N : SheafOfModules.{u} (R.over V)) (A : (Over W)ᵒᵖ) :
    Induced N ((Stacks.SheafOfModules.overPullbackCongr R e).inv.app N) A
      ((Over.pullback b).obj A.unop) ((Over.pullback a).obj A.unop) :=
  ⟨eqToHom (congrArg (fun k : V ⟶ W => (Over.pullback k).obj A.unop) e), rfl, rfl,
    Stacks.SectionsComponents.overPullbackCongr_inv_app_val_app R e N A⟩

/-! ### The comparison of sections -/

/-- **The comparison of sections of Stacks 03DV is restriction along an arrow of the big fppf
site** over the scheme of `T`: from the fibre product of `T` with the open `Z` of `S` to the open
of the scheme of `T` lying over `Z`. -/
public theorem induced_objRestrictSectionsIso_hom (T : BigFppfOver B S hS)
    (M : SheafOfModules.{u} (structureSheaf B (objScheme B S hS T) (contains_objScheme B S hS T)))
    (Z : S.Opens) :
    Induced M ((objRestrictSectionsIso B S hS T).hom.app M) (op Z)
      ((Over.pullback T.hom).obj ((opensToBig B S hS).obj Z))
      ((opensToBig B (objScheme B S hS T) (contains_objScheme B S hS T)).obj
        ((TopologicalSpace.Opens.map (objHom B S hS T).base).obj Z)) := by
  rw [objRestrictSectionsIso_eq_explicit]
  indT
  · indWR
    indS
    indTi
    · indSi
      exact @Induced.pushforwardCongr₂Hom ..
    · exact @Induced.pushforwardCompInv ..
  · indT
    · exact @Induced.associatorHom ..
    · indT
      · apply (config := { newGoals := .nonDependentOnly })
          Induced.isoWhiskerLeftReindexHom (objEquiv B S hS T) ((structureSheaf B S hS).over T)
        indT
        · exact @Induced.pushforwardCompHom ..
        · indT
          · exact @Induced.pushforwardCongr₂Hom ..
          · indS
            exact @Induced.pushforwardCompInv ..
      · indT
        · indS
          exact @Induced.associatorInv ..
        · indS
          indWRi
          indTi
          · indTi
            · indTi
              · apply (config := { newGoals := .nonDependentOnly })
                  Induced.isoWhiskerLeftReindexInv (objEquiv B S hS T)
                    ((structureSheaf B S hS).over T)
                indTi
                · exact @Induced.pushforwardCongrInv ..
                · exact @Induced.pushforwardCompInv ..
              · exact @Induced.associatorInv ..
            · indWRi
              exact @Induced.reindexSymmUnitInv ..
          · indSi
            exact @Induced.leftUnitorHom ..

/-- **The inverse comparison of sections of Stacks 03DV is restriction along an arrow of the big
fppf site**, in the other direction. -/
public theorem induced_objRestrictSectionsIso_inv (T : BigFppfOver B S hS)
    (M : SheafOfModules.{u} (structureSheaf B (objScheme B S hS T) (contains_objScheme B S hS T)))
    (Z : S.Opens) :
    Induced M ((objRestrictSectionsIso B S hS T).inv.app M) (op Z)
      ((opensToBig B (objScheme B S hS T) (contains_objScheme B S hS T)).obj
        ((TopologicalSpace.Opens.map (objHom B S hS T).base).obj Z))
      ((Over.pullback T.hom).obj ((opensToBig B S hS).obj Z)) := by
  rw [objRestrictSectionsIso_eq_explicit]
  indTi
  · indTi
    · indTi
      · indTi
        · indSi
          indWR
          indT
          · indS
            exact @Induced.leftUnitorInv ..
          · indT
            · indWR
              exact @Induced.reindexSymmUnitHom ..
            · indT
              · exact @Induced.associatorHom ..
              · apply (config := { newGoals := .nonDependentOnly })
                  Induced.isoWhiskerLeftReindexHom (objEquiv B S hS T)
                    ((structureSheaf B S hS).over T)
                indT
                · exact @Induced.pushforwardCompHom ..
                · exact @Induced.pushforwardCongrHom ..
        · indSi
          exact @Induced.associatorHom ..
      · apply (config := { newGoals := .nonDependentOnly })
          Induced.isoWhiskerLeftReindexInv (objEquiv B S hS T) ((structureSheaf B S hS).over T)
        indTi
        · indTi
          · indSi
            exact @Induced.pushforwardCompHom ..
          · exact @Induced.pushforwardCongr₂Inv ..
        · exact @Induced.pushforwardCompInv ..
    · exact @Induced.associatorInv ..
  · indWRi
    indSi
    indT
    · exact @Induced.pushforwardCompHom ..
    · indS
      exact @Induced.pushforwardCongr₂Inv ..

/-- **Two morphisms of modules on a scheme that are induced by arrows between the same two
objects of a site agree on sections**, when there is at most one such arrow.  This is
`Stacks.SectionsComponents.Induced.eq` read through `AlgebraicGeometry.Scheme.Modules.Hom.app`. -/
public theorem induced_eq_app {C₀ : Type u₀} [Category.{v₀} C₀] {J₀ : GrothendieckTopology C₀}
    {R₀ : Sheaf J₀ RingCat.{u}} (N : SheafOfModules.{u} R₀) {X : Scheme.{u}}
    {M₁ M₂ : X.Modules} {f h : M₁ ⟶ M₂} {Z : X.Opens} {A A' : C₀} [Subsingleton (A' ⟶ A)]
    (hf : Induced N f (op Z) A A') (hh : Induced N h (op Z) A A') :
    ∀ y, f.app Z y = h.app Z y :=
  Induced.eq hf hh

/-- **Two isomorphisms of functors into the modules on a scheme agree as soon as both are, at
every sheaf of modules and every open, restriction along an arrow of a site with a subsingleton
hom-set.**  This is the form in which the cocycle is discharged: it performs the two
extensionality steps once and for all, in a context where they are cheap. -/
public theorem iso_eq_of_induced {C₀ : Type u₀} [Category.{v₀} C₀] {J₀ : GrothendieckTopology C₀}
    {R₀ : Sheaf J₀ RingCat.{u}} {X : Scheme.{u}}
    {F G : SheafOfModules.{u} R₀ ⥤ X.Modules} (α β : F ≅ G)
    (A A' : SheafOfModules.{u} R₀ → X.Opens → C₀)
    (hsub : ∀ N Z, Subsingleton (A' N Z ⟶ A N Z))
    (hα : ∀ N Z, Induced N (α.hom.app N) (op Z) (A N Z) (A' N Z))
    (hβ : ∀ N Z, Induced N (β.hom.app N) (op Z) (A N Z) (A' N Z)) : α = β := by
  refine Iso.ext ?_
  ext N : 2
  ext Z x
  have := hsub N Z
  exact induced_eq_app N (hα N Z) (hβ N Z) x

/-! ### The cocycle -/

variable {T T' : BigFppfOver B S hS}

/-- **The left-hand side of the cocycle for the comparison of sections is restriction along an
arrow of the big fppf site** over the scheme of `T'`. -/
public theorem induced_sectionsCocycle_lhs (g : T' ⟶ T)
    (M : SheafOfModules.{u}
      (structureSheaf B (objScheme B S hS T') (contains_objScheme B S hS T')))
    (Z : S.Opens) :
    Induced M
      ((Functor.isoWhiskerLeft
          (restrictModule B (objScheme B S hS T') (contains_objScheme B S hS T'))
          (eqToIso (congrArg
                (fun k : objScheme B S hS T' ⟶ S => Scheme.Modules.pushforward k)
                (objHom_comp B S hS g)).symm ≪≫
              (Scheme.Modules.pushforwardComp
                (objHom B (objScheme B S hS T) (contains_objScheme B S hS T) (Over.mk g.left))
                (objHom B S hS T)).symm).symm ≪≫
        (objRestrictSectionsIso B S hS T').symm).hom.app M) (op Z)
      (opensObj B (objScheme B S hS T') (contains_objScheme B S hS T')
        ((TopologicalSpace.Opens.map (objHom B (objScheme B S hS T)
            (contains_objScheme B S hS T) (Over.mk g.left)).base).obj
          ((TopologicalSpace.Opens.map (objHom B S hS T).base).obj Z)))
      ((Over.pullback T'.hom).obj ((opensToBig B S hS).obj Z)) := by
  indT
  · apply (config := { newGoals := .nonDependentOnly }) Induced.isoWhiskerLeftHom _
      (structureMap B (objScheme B S hS T') (contains_objScheme B S hS T'))
    indS
    indTi
    · indSi
      exact @Induced.pushforwardCompHom ..
    · exact induced_eqToIso_pushforward_inv _ (objHom_comp B S hS g).symm _ Z
  · indS
    exact induced_objRestrictSectionsIso_inv B S hS T' M Z

/-- **The right-hand side of the cocycle for the comparison of sections is restriction along an
arrow of the big fppf site**, between the same two objects. -/
public theorem induced_sectionsCocycle_rhs (g : T' ⟶ T)
    (M : SheafOfModules.{u}
      (structureSheaf B (objScheme B S hS T') (contains_objScheme B S hS T')))
    (Z : S.Opens) :
    Induced M
      (((Functor.associator
              (restrictModule B (objScheme B S hS T') (contains_objScheme B S hS T'))
              (Scheme.Modules.pushforward
                (objHom B (objScheme B S hS T) (contains_objScheme B S hS T) (Over.mk g.left)))
              (Scheme.Modules.pushforward (objHom B S hS T))).symm ≪≫
          Functor.isoWhiskerRight
              (objRestrictSectionsIso B (objScheme B S hS T) (contains_objScheme B S hS T)
                (Over.mk g.left)).symm
              (Scheme.Modules.pushforward (objHom B S hS T)) ≪≫
            (Functor.isoWhiskerRight
                  (Stacks.SheafOfModules.overPullbackCongr B.structureSheaf (Over.w g).symm ≪≫
                    Stacks.SheafOfModules.overPullbackComp B.structureSheaf T.hom g.left)
                  (restrictModule B S hS) ≪≫
                Functor.associator (SheafOfModules.overPullback.{u} B.structureSheaf g.left)
                    (SheafOfModules.overPullback.{u} B.structureSheaf T.hom)
                    (restrictModule B S hS) ≪≫
                  Functor.isoWhiskerLeft (SheafOfModules.overPullback.{u} B.structureSheaf g.left)
                      (objRestrictSectionsIso B S hS T) ≪≫
                    (Functor.associator (SheafOfModules.overPullback.{u} B.structureSheaf g.left)
                      (restrictModule B (objScheme B S hS T) (contains_objScheme B S hS T))
                      (Scheme.Modules.pushforward (objHom B S hS T))).symm).symm).hom.app M)
      (op Z)
      (opensObj B (objScheme B S hS T') (contains_objScheme B S hS T')
        ((TopologicalSpace.Opens.map (objHom B (objScheme B S hS T)
            (contains_objScheme B S hS T) (Over.mk g.left)).base).obj
          ((TopologicalSpace.Opens.map (objHom B S hS T).base).obj Z)))
      ((Over.pullback T'.hom).obj ((opensToBig B S hS).obj Z)) := by
  rw [Stacks.SheafOfModules.overPullbackComp_eq]
  indT
  · indS
    exact @Induced.associatorInv ..
  · indT
    · indWR
      indS
      exact induced_objRestrictSectionsIso_inv B (objScheme B S hS T)
        (contains_objScheme B S hS T) (Over.mk g.left) M _
    · indS
      indTi
      · indTi
        · indTi
          · indSi
            exact @Induced.associatorHom ..
          · apply (config := { newGoals := .nonDependentOnly }) Induced.isoWhiskerLeftInv _
              (B.structureSheaf.toPushforwardOverPullback g.left)
            exact induced_objRestrictSectionsIso_inv B S hS T _ Z
        · exact @Induced.associatorInv ..
      · indWRi
        indTi
        · indTi
          · indSi
            exact @Induced.pushforwardCompHom ..
          · exact @Induced.pushforwardCongr₂Inv ..
        · exact @induced_overPullbackCongr_inv ..

/-- **There is at most one arrow of the big fppf site over the scheme of `T'` from the fibre
product of `T'` with an open `Z` of `S` to the open of the scheme of `T'` lying over `Z`.**  This
is `AlgebraicGeometry.BigFppfOver.subsingleton_hom_opensObj` at the two objects through which the
two sides of the cocycle read sections. -/
public theorem subsingleton_hom_cocycle (g : T' ⟶ T) (Z : S.Opens) :
    Subsingleton ((Over.pullback T'.hom).obj ((opensToBig B S hS).obj Z) ⟶
      opensObj B (objScheme B S hS T') (contains_objScheme B S hS T')
        ((TopologicalSpace.Opens.map (objHom B (objScheme B S hS T)
            (contains_objScheme B S hS T) (Over.mk g.left)).base).obj
          ((TopologicalSpace.Opens.map (objHom B S hS T).base).obj Z))) :=
  subsingleton_hom_opensObj B (objScheme B S hS T') (contains_objScheme B S hS T') _ _

/-- **The cocycle for the comparison of sections, with both sides written out.**  This is
`AlgebraicGeometry.BigFppfOver.SectionsCocycle` with its abbreviation expanded, so that the
identification of the two sides with
`AlgebraicGeometry.BigFppfOver.induced_sectionsCocycle_lhs` and
`AlgebraicGeometry.BigFppfOver.induced_sectionsCocycle_rhs` and the unfolding of the
abbreviation are paid for in two separate declarations. -/
public theorem sectionsCocycle_expanded (g : T' ⟶ T) :
    Functor.isoWhiskerLeft
          (restrictModule B (objScheme B S hS T') (contains_objScheme B S hS T'))
          (eqToIso (congrArg
                (fun k : objScheme B S hS T' ⟶ S => Scheme.Modules.pushforward k)
                (objHom_comp B S hS g)).symm ≪≫
              (Scheme.Modules.pushforwardComp
                (objHom B (objScheme B S hS T) (contains_objScheme B S hS T) (Over.mk g.left))
                (objHom B S hS T)).symm).symm ≪≫
        (objRestrictSectionsIso B S hS T').symm =
      (Functor.associator
            (restrictModule B (objScheme B S hS T') (contains_objScheme B S hS T'))
            (Scheme.Modules.pushforward
              (objHom B (objScheme B S hS T) (contains_objScheme B S hS T) (Over.mk g.left)))
            (Scheme.Modules.pushforward (objHom B S hS T))).symm ≪≫
        Functor.isoWhiskerRight
            (objRestrictSectionsIso B (objScheme B S hS T) (contains_objScheme B S hS T)
              (Over.mk g.left)).symm
            (Scheme.Modules.pushforward (objHom B S hS T)) ≪≫
          (Functor.isoWhiskerRight
                (Stacks.SheafOfModules.overPullbackCongr B.structureSheaf (Over.w g).symm ≪≫
                  Stacks.SheafOfModules.overPullbackComp B.structureSheaf T.hom g.left)
                (restrictModule B S hS) ≪≫
              Functor.associator (SheafOfModules.overPullback.{u} B.structureSheaf g.left)
                  (SheafOfModules.overPullback.{u} B.structureSheaf T.hom)
                  (restrictModule B S hS) ≪≫
                Functor.isoWhiskerLeft (SheafOfModules.overPullback.{u} B.structureSheaf g.left)
                    (objRestrictSectionsIso B S hS T) ≪≫
                  (Functor.associator (SheafOfModules.overPullback.{u} B.structureSheaf g.left)
                    (restrictModule B (objScheme B S hS T) (contains_objScheme B S hS T))
                    (Scheme.Modules.pushforward (objHom B S hS T))).symm).symm :=
  iso_eq_of_induced _ _
    (fun _ Z => opensObj B (objScheme B S hS T') (contains_objScheme B S hS T')
      ((TopologicalSpace.Opens.map (objHom B (objScheme B S hS T)
          (contains_objScheme B S hS T) (Over.mk g.left)).base).obj
        ((TopologicalSpace.Opens.map (objHom B S hS T).base).obj Z)))
    (fun _ Z => (Over.pullback T'.hom).obj ((opensToBig B S hS).obj Z))
    (fun _ Z => subsingleton_hom_cocycle B S hS g Z)
    (induced_sectionsCocycle_lhs B S hS g)
    (induced_sectionsCocycle_rhs B S hS g)

/-- **The cocycle condition for the comparison of sections of Stacks 03DV**, the last residue of
Stacks 03DX (1) in this library.

Both sides are, on sections, restriction along an arrow of the big fppf site over the scheme of
`T'`, from the fibre product of `T'` with an open `Z` of `S` to the open of the scheme of `T'`
lying over `Z`; and every arrow of that site whose target is an open of the scheme is unique,
`AlgebraicGeometry.BigFppfOver.subsingleton_hom_opensObj`. -/
public theorem sectionsCocycle (g : T' ⟶ T) : SectionsCocycle B S hS g :=
  sectionsCocycle_expanded B S hS g

/-- **The comparison isomorphism of Stacks 03DV is pseudonatural.**  This is
`AlgebraicGeometry.BigFppfOver.LocalComparisonPseudonatural` — the hypothesis every consumer of
Stacks 03DX (1) in this library carries — discharged:
`AlgebraicGeometry.BigFppfOver.localComparisonPseudonatural_of_sectionsCocycle` reduces it to the
cocycle for the comparison of sections at every base, and
`AlgebraicGeometry.BigFppfOver.sectionsCocycle` proves that cocycle. -/
public theorem localComparisonPseudonatural
    (G : SheafOfModules.{u} (structureSheaf B S hS)) :
    LocalComparisonPseudonatural B S hS G :=
  localComparisonPseudonatural_of_sectionsCocycle B S hS
    (fun {X : Scheme.{u}} (hX : B.Contains X) {W W' : BigFppfOver B X hX} (g : W' ⟶ W) =>
      sectionsCocycle B X hX g) G

end AlgebraicGeometry.BigFppfOver

end
