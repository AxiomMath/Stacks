module

public import Mathlib.CategoryTheory.Sites.CompatibleSheafification
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksFrontier.Topology.Sheaves.AlgebraicStructure.Examples

/-!
# Sheafification of presheaves of algebraic structures on a site

Let `(A, s)` be a type of algebraic structure (Stacks 007L): a category `A` with a functor
`s : A ⥤ Type` which is faithful, reflects isomorphisms, and commutes with limits and with
filtered colimits. Let `(C, J)` be a site. Then the following hold.

* (α) A presheaf `P` with values in `A` is a sheaf if and only if `P ⋙ s` is a sheaf of sets.
* (β) The presheaf `P# = (P⁺)⁺` given by the plus construction is a sheaf.
* (γ) Sheafification commutes with `s`: `P# ⋙ s ≅ (P ⋙ s)#`, functorially in `P` and
  compatibly with the canonical maps from `P ⋙ s`; and the inclusions of sheaves into
  presheaves commute with `s`.
* (δ) The canonical map `P ⟶ P#` is an isomorphism if and only if `P` is a sheaf.
* (ε) Sheafification `P ↦ P#` is left adjoint to the inclusion of sheaves into presheaves, with
  unit the canonical map `P ⟶ P#`.
* (ζ) Sheafification is left exact.

We package these six statements as the structure `Stacks.Sites.SheafificationProperties J A`
and prove them for every type of algebraic structure whose underlying-set functor is the
forgetful functor of a concrete category, which covers the seven types listed in Stacks 00YV:
pointed sets, abelian groups, groups, monoids, commutative rings, modules over a fixed ring and
Lie algebras over a fixed field.

## Main definitions

* `Stacks.Sites.plusPlusSheafOf`: the functor `P ↦ P#` into sheaves, given that every `P#` is a
  sheaf.
* `Stacks.Sites.SheafificationProperties`: the properties (α)–(ζ) for `A`-valued presheaves on
  the site `(C, J)`.
* `Stacks.Sites.SheafificationProperties.ofIsTypeOfAlgebraicStructure`: (α)–(ζ) hold for a type
  of algebraic structure.
* `Stacks.Sites.SheafificationProperties.pointed`, `.addCommGrpCat`, `.grpCat`, `.monCat`,
  `.commRingCat`, `.moduleCat`, `.lieAlgCat`: the seven instances of Stacks 00YV.

## Implementation notes

The sheafification is Mathlib's plus construction `GrothendieckTopology.sheafify`, which is
`(P⁺)⁺` by definition. Its colimits are indexed by the opposite categories of covers, which are
filtered, so only filtered colimits in `A` are needed; this is what makes the construction
available for groups, pointed sets and Lie algebras, which do not have all colimits.

The site is `C : Type u` with `Category.{v} C`, and `A` has hom types in `Type (max u v)`;
for a small site (`u = v`) this is the usual setting of presheaves with values in `Type u`.

## References

* [Stacks: Sites and Sheaves, Section 00YR and Proposition 00YV][stacks-project]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe t u v

namespace Stacks.Sites

section Defs

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type t) [Category.{max u v} A] {FA : A → A → Type*} {CA : A → Type (max u v)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{max u v} A FA]
  [∀ (P : Cᵒᵖ ⥤ A) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
  [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ A]

/-- Given that `P# = (P⁺)⁺` is a sheaf for every presheaf `P`, the sheafification functor
`P ↦ P#` as a functor from presheaves to sheaves. -/
noncomputable abbrev plusPlusSheafOf (h : ∀ P : Cᵒᵖ ⥤ A, Presheaf.IsSheaf J (J.sheafify P)) :
    (Cᵒᵖ ⥤ A) ⥤ Sheaf J A :=
  ObjectProperty.lift _ (J.sheafification A) h

/-- The properties (α)–(ζ) of Stacks, Section 00YR, of sheafification of presheaves on the site
`(C, J)` with values in the concrete category `A`, with `s = forget A`. Here `P# = (P⁺)⁺` is
Mathlib's plus construction `J.sheafify P`. -/
structure SheafificationProperties where
  /-- (α) A presheaf is a sheaf iff its underlying presheaf of sets is a sheaf. -/
  isSheaf_iff_isSheaf_comp_forget (P : Cᵒᵖ ⥤ A) :
    Presheaf.IsSheaf J P ↔ Presheaf.IsSheaf J (P ⋙ forget A)
  /-- (β) The presheaf `P# = (P⁺)⁺` is a sheaf. -/
  isSheaf_sheafify (P : Cᵒᵖ ⥤ A) : Presheaf.IsSheaf J (J.sheafify P)
  /-- (γ) Sheafification commutes with taking underlying presheaves of sets, functorially in
  the presheaf. -/
  sheafificationCompForgetIso :
    J.sheafification A ⋙ (whiskeringRight Cᵒᵖ A (Type (max u v))).obj (forget A) ≅
      (whiskeringRight Cᵒᵖ A (Type (max u v))).obj (forget A) ⋙
        J.sheafification (Type (max u v))
  /-- (γ) The isomorphism `P# ⋙ s ≅ (P ⋙ s)#` is compatible with the canonical maps from
  `P ⋙ s`. -/
  whiskerRight_toSheafify_sheafificationCompForgetIso_hom (P : Cᵒᵖ ⥤ A) :
    whiskerRight (J.toSheafify P) (forget A) ≫ sheafificationCompForgetIso.hom.app P =
      J.toSheafify (P ⋙ forget A)
  /-- (γ) The inclusions of sheaves into presheaves commute with taking underlying sets: by
  (α), `s` sends sheaves to sheaves, and composing with `s` before or after the inclusion gives
  the same functor. -/
  sheafCompose_forget_comp_sheafToPresheaf :
    letI : J.HasSheafCompose (forget A) :=
      ⟨fun P hP => (isSheaf_iff_isSheaf_comp_forget P).1 hP⟩
    sheafCompose J (forget A) ⋙ sheafToPresheaf J (Type (max u v)) =
      sheafToPresheaf J A ⋙ (whiskeringRight Cᵒᵖ A (Type (max u v))).obj (forget A)
  /-- (δ) The canonical map `P ⟶ P#` is an isomorphism iff `P` is a sheaf. -/
  isIso_toSheafify_iff (P : Cᵒᵖ ⥤ A) : IsIso (J.toSheafify P) ↔ Presheaf.IsSheaf J P
  /-- (ε) Sheafification is left adjoint to the inclusion of sheaves into presheaves. -/
  adjunction : plusPlusSheafOf J A isSheaf_sheafify ⊣ sheafToPresheaf J A
  /-- (ε) The unit of the adjunction is the canonical map `P ⟶ P#`, so that a morphism
  `P ⟶ F` to a sheaf corresponds to the morphism `P# ⟶ F` through which it factors. -/
  adjunction_unit_app (P : Cᵒᵖ ⥤ A) : adjunction.unit.app P = J.toSheafify P
  /-- (ζ) Sheafification, as a functor from presheaves to sheaves, is left exact. -/
  preservesFiniteLimits_plusPlusSheafOf :
    PreservesFiniteLimits (plusPlusSheafOf J A isSheaf_sheafify)
  /-- (ζ) Sheafification, as a functor from presheaves to presheaves, is left exact. -/
  preservesFiniteLimits_sheafification : PreservesFiniteLimits (J.sheafification A)

end Defs

namespace SheafificationProperties

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

section Generic

variable {A : Type t} [Category.{max u v} A] {FA : A → A → Type*} {CA : A → Type (max u v)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{max u v} A FA]
  [∀ (P : Cᵒᵖ ⥤ A) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
  [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ A]

/-- The properties (α)–(ζ) of sheafification hold for presheaves with values in a type of
algebraic structure `(A, forget A)`. -/
noncomputable def ofIsTypeOfAlgebraicStructure
    (h : IsTypeOfAlgebraicStructure A (forget A)) : SheafificationProperties J A :=
  haveI := h.faithful
  haveI := h.hasLimits
  haveI := h.preservesLimits
  haveI := h.hasFilteredColimits
  haveI := h.preservesFilteredColimits
  haveI := h.reflectsIsomorphisms
  { isSheaf_iff_isSheaf_comp_forget := fun P => Presheaf.isSheaf_iff_isSheaf_forget J P (forget A)
    isSheaf_sheafify := fun P => J.sheafify_isSheaf P
    sheafificationCompForgetIso := J.sheafificationWhiskerRightIso (forget A)
    whiskerRight_toSheafify_sheafificationCompForgetIso_hom := fun P => by
      simp
    sheafCompose_forget_comp_sheafToPresheaf := rfl
    isIso_toSheafify_iff := fun P =>
      ⟨fun _ => (Presheaf.isSheaf_of_iso_iff (asIso (J.toSheafify P))).2 (J.sheafify_isSheaf P),
        fun hP => J.isIso_toSheafify hP⟩
    adjunction := plusPlusAdjunction J A
    adjunction_unit_app := fun P => Category.comp_id (J.toSheafify P)
    preservesFiniteLimits_plusPlusSheafOf :=
      inferInstanceAs (PreservesFiniteLimits (plusPlusSheaf J A))
    preservesFiniteLimits_sheafification := inferInstance }

end Generic

/-- (α)–(ζ) for presheaves of pointed sets. -/
noncomputable def pointed : SheafificationProperties J Pointed.{max u v} :=
  ofIsTypeOfAlgebraicStructure J isTypeOfAlgebraicStructure_pointed

/-- (α)–(ζ) for presheaves of abelian groups. -/
noncomputable def addCommGrpCat : SheafificationProperties J AddCommGrpCat.{max u v} :=
  ofIsTypeOfAlgebraicStructure J isTypeOfAlgebraicStructure_addCommGrpCat

/-- (α)–(ζ) for presheaves of groups. -/
noncomputable def grpCat : SheafificationProperties J GrpCat.{max u v} :=
  ofIsTypeOfAlgebraicStructure J isTypeOfAlgebraicStructure_grpCat

/-- (α)–(ζ) for presheaves of monoids. -/
noncomputable def monCat : SheafificationProperties J MonCat.{max u v} :=
  ofIsTypeOfAlgebraicStructure J isTypeOfAlgebraicStructure_monCat

/-- (α)–(ζ) for presheaves of (commutative) rings. -/
noncomputable def commRingCat : SheafificationProperties J CommRingCat.{max u v} :=
  ofIsTypeOfAlgebraicStructure J isTypeOfAlgebraicStructure_commRingCat

/-- (α)–(ζ) for presheaves of modules over a fixed ring `R`. -/
noncomputable def moduleCat (R : Type (max u v)) [Ring R] :
    SheafificationProperties J (ModuleCat.{max u v} R) :=
  ofIsTypeOfAlgebraicStructure J
    { faithful := inferInstance
      hasLimits := inferInstance
      preservesLimits := inferInstance
      hasFilteredColimits := inferInstance
      preservesFilteredColimits := inferInstance
      reflectsIsomorphisms := inferInstance }

/-- (α)–(ζ) for presheaves of Lie algebras over a fixed field `K`. -/
noncomputable def lieAlgCat (K : Type (max u v)) [Field K] :
    SheafificationProperties J (LieAlgCat.{max u v} K) :=
  ofIsTypeOfAlgebraicStructure J (isTypeOfAlgebraicStructure_lieAlgCat K)

end SheafificationProperties

end Stacks.Sites
