module

public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.Limits.VanKampen
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductSummand
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproductSpace
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfOverTypeSheafification
public import StacksFrontier.CategoryTheory.Limits.VanKampenCoproducts

/-!
# The clopen decomposition of a scheme by a section of a coproduct of sheaves: the refined forms

Strengthened forms of declarations of `StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproductSpace`,
and the declarations that belong with them. A declaration of that module whose statement is
strengthened keeps its original statement there; its strengthened form lives here under a
primed name.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u v

namespace AlgebraicGeometry

/-! ### Cartesian squares of sheaves of sets -/

section SheafSquares

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  {W X Y Z : Sheaf J (Type w)} {fst : W ⟶ X} {snd : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/-- A square of sheaves of sets which is cartesian in presheaves is cartesian in sheaves: the
inclusion of sheaves into presheaves is fully faithful, hence reflects limits.

The value universe of the sheaves is arbitrary: nothing here is tied to the universe of the
morphisms of the site. -/
theorem isPullback_sheaf_of_hom' (h : IsPullback fst.hom snd.hom f.hom g.hom) :
    IsPullback (C := Sheaf J (Type w)) fst snd f g :=
  IsPullback.of_map (sheafToPresheaf J (Type w)) (Sheaf.hom_ext h.w) h

/-- A cartesian square of sheaves of sets is cartesian in presheaves, provided the site admits
sheafification: the inclusion of sheaves into presheaves is then a right adjoint.

The value universe of the sheaves is arbitrary. -/
theorem isPullback_hom_of_sheaf' [HasSheafify J (Type w)] (h : IsPullback fst snd f g) :
    IsPullback fst.hom snd.hom f.hom g.hom :=
  h.map (sheafToPresheaf J (Type w))

end SheafSquares

/-! ### Sheafification and extensivity for the big fppf site of `S` -/

section Instances

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

end Instances

/-! ### Stacks 0F15 with the representing object, for an arbitrary index type -/

section Decomposition

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  [(BigFppfOver.topology B S hS).Subcanonical]
  {I : Type v} {Fi : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
  {G : Sheaf (BigFppfOver.topology B S hS) (Type u)} (ι : ∀ i, Fi i ⟶ G)

end Decomposition

/-! ### Surjectivity and étaleness out of a coproduct of the site -/

section Properties

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {I : Type v}
  [Small.{u} I] [B.AdmitsCoproductIndex I]

end Properties

/-! ### Stacks 02WQ -/

section Main

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  [(BigFppfOver.topology B S hS).Subcanonical]
  {I : Type v} [Small.{u} I] [B.AdmitsCoproductIndex I]
  {Fi : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
  {G : Sheaf (BigFppfOver.topology B S hS) (Type u)} (ι : ∀ i, Fi i ⟶ G)

end Main

end AlgebraicGeometry

end
