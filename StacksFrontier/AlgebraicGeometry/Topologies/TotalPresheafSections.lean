module

public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentReduction

/-!
# Sections of the total presheaf

`Stacks.Sites.totalPresheaf P` repackages a presheaf `P` on the slice `CategoryTheory.Over X` as a
presheaf on the ambient category, its value at `T` being the set of pairs `⟨f, s⟩` of a morphism
`f : T ⟶ X` and a section of `P` at `f`. This file is the elementary calculus of that
construction: how to read a section of `P` off an element of the total presheaf whose first
component is a structure morphism, and how that reading interacts with restriction.

## Main definitions

* `Stacks.Sites.totalSection`: the section of `P` at `A` carried by an element of the total
  presheaf whose first component is `A.hom`.

## Main results

* `Stacks.Sites.totalSigmaMkEq`: restrictions of one section along two morphisms of the slice with
  the same underlying morphism agree in the total presheaf.
* `Stacks.Sites.totalMkSection`: reassembling `totalSection` recovers the element.
* `Stacks.Sites.totalMapFst`: restricting such an element again gives one whose first component is
  a structure morphism.
* `Stacks.Sites.totalMapMk` and `Stacks.Sites.totalMapSection`: restriction in the total presheaf,
  read through `totalSection` in both directions.
* `Stacks.Sites.totalSigmaSndInj`: two elements with the same first component agree as soon as
  their second components do.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u

namespace Stacks.Sites

variable {C : Type u} [Category.{v} C] {X : C}

/-- Two elements of the total presheaf built from restrictions of one section along two morphisms
of the slice with the same underlying morphism agree. -/
public lemma totalSigmaMkEq {F : (Over X)ᵒᵖ ⥤ Type v} {V W : C} {φ : W ⟶ X}
    (s : F.obj (op (Over.mk φ))) {ψ ψ' : V ⟶ X} (e : Over.mk ψ ⟶ Over.mk φ)
    (e' : Over.mk ψ' ⟶ Over.mk φ) (h : e.left = e'.left) :
    (⟨ψ, F.map e.op s⟩ : Σ χ : V ⟶ X, F.obj (op (Over.mk χ))) = ⟨ψ', F.map e'.op s⟩ := by
  have h1 := Over.w e
  have h2 := Over.w e'
  simp only [Over.mk_hom, Over.mk_left] at h1 h2
  have hψ : ψ = ψ' := by rw [← h1, ← h2, h]
  subst hψ
  rw [Over.OverMorphism.ext h]

/-- The section of `F` at `A` carried by an element of the total presheaf whose first component is
the structure morphism of `A`. -/
public def totalSection {F : (Over X)ᵒᵖ ⥤ Type v} {A : Over X}
    (p : (totalPresheaf F).obj (op A.left)) (h : p.1 = A.hom) : F.obj (op A) :=
  F.map (Over.homMk (𝟙 A.left) (by simpa using h) : A ⟶ Over.mk p.1).op p.2

/-- The first component of a restriction of an element of the total presheaf whose first component
is a structure morphism is again a structure morphism. -/
public lemma totalMapFst {F : (Over X)ᵒᵖ ⥤ Type v} {A B : Over X} (b : B ⟶ A)
    {p : (totalPresheaf F).obj (op A.left)} (h : p.1 = A.hom)
    {q : (totalPresheaf F).obj (op B.left)}
    (hq : (totalPresheaf F).map b.left.op p = q) : q.1 = B.hom := by
  have hfst : b.left ≫ p.1 = q.1 := congrArg Sigma.fst hq
  rw [← hfst, h]
  exact Over.w b

/-- `Stacks.Sites.totalSection` recovers the element of the total presheaf it came from. -/
public lemma totalMkSection {F : (Over X)ᵒᵖ ⥤ Type v} {A : Over X}
    (p : (totalPresheaf F).obj (op A.left)) (h : p.1 = A.hom) :
    (⟨A.hom, totalSection p h⟩ : (totalPresheaf F).obj (op A.left)) = p := by
  have h1 := totalSigmaMkEq p.2
    (Over.homMk (𝟙 A.left) (by simpa using h) : Over.mk A.hom ⟶ Over.mk p.1)
    (𝟙 (Over.mk p.1)) (by simp)
  have h2 : (⟨p.1, F.map (𝟙 (Over.mk p.1)).op p.2⟩ :
      (totalPresheaf F).obj (op A.left)) = p := by
    cases p
    simp
  exact h1.trans h2

/-- Restriction in the total presheaf of an element assembled from a section of `F`. -/
public lemma totalMapMk {F : (Over X)ᵒᵖ ⥤ Type v} {A B : Over X} (b : B ⟶ A)
    (t : F.obj (op A)) :
    (totalPresheaf F).map b.left.op (⟨A.hom, t⟩ : (totalPresheaf F).obj (op A.left)) =
      ⟨B.hom, F.map b.op t⟩ := by
  change (⟨b.left ≫ A.hom,
    F.map (Over.homMk b.left rfl : Over.mk (b.left ≫ A.hom) ⟶ Over.mk A.hom).op t⟩ :
      (totalPresheaf F).obj (op B.left)) = ⟨B.hom, F.map b.op t⟩
  exact totalSigmaMkEq t
    (Over.homMk b.left rfl : Over.mk (b.left ≫ A.hom) ⟶ Over.mk A.hom) b rfl

/-- Two elements of the total presheaf with the same first component agree as soon as their second
components do. -/
public lemma totalSigmaSndInj {F : (Over X)ᵒᵖ ⥤ Type v} {V : C} {φ : V ⟶ X}
    {s t : F.obj (op (Over.mk φ))}
    (hst : (⟨φ, s⟩ : Σ ψ : V ⟶ X, F.obj (op (Over.mk ψ))) = ⟨φ, t⟩) : s = t := by
  simpa using hst

/-- `Stacks.Sites.totalSection` commutes with restriction. -/
public lemma totalMapSection {F : (Over X)ᵒᵖ ⥤ Type v} {A B : Over X} (b : B ⟶ A)
    {p : (totalPresheaf F).obj (op A.left)} (h : p.1 = A.hom)
    {q : (totalPresheaf F).obj (op B.left)}
    (hq : (totalPresheaf F).map b.left.op p = q) :
    F.map b.op (totalSection p h) = totalSection q (totalMapFst b h hq) :=
  totalSigmaSndInj <| (totalMapMk b (totalSection p h)).symm.trans <|
    ((congrArg (fun s => (totalPresheaf F).map b.left.op s) (totalMkSection p h)).trans hq).trans
      (totalMkSection q (totalMapFst b h hq)).symm

end Stacks.Sites

end
