module

public import StacksFrontier.AlgebraicGeometry.QcohAlgebraFPColimit.Sections
public import StacksFrontier.AlgebraicGeometry.Properties.QuasicoherentAlgebra
public import Mathlib.Order.ULift

/-!
# Presenting a quasi-coherent algebra as a directed colimit, from a sectionwise approximation

A directed system of quasi-coherent algebras of finite presentation mapping to a quasi-coherent
algebra `A` presents `A` as a directed colimit of quasi-coherent algebras of finite presentation as
soon as, over every affine open, the sections of the system exhaust those of `A` and separate no
more than `A` does.

## Main results

* `Stacks.QcohAlgebraFPColimit.exists_directedSystem_of_isColimit`: `A` is a directed colimit of
  quasi-coherent algebras of finite presentation, given a directed system of such algebras whose
  cocone over `A` is colimiting.
* `Stacks.QcohAlgebraFPColimit.exists_directedSystem_of_affineSections`: the same, given a
  directed system of quasi-coherent algebras of finite presentation that is jointly surjective and
  eventually injective on sections over every affine open.
* `Stacks.QcohAlgebraFPColimit.exists_directedSystem_of_affineSections_of_smallIndex`: the same
  with the index set in `Type u` rather than `Type (u + 1)`.

## References

* [The Stacks Project, Tag 05JS](https://stacks.math.columbia.edu/tag/05JS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.QuasiCompactColimit

universe u

namespace Stacks.QcohAlgebraFPColimit

variable {X : Scheme.{u}}

/-- A directed system of quasi-coherent algebras of finite presentation whose cocone over `A` is
colimiting presents `A` as a directed colimit of quasi-coherent algebras of finite presentation. -/
theorem exists_directedSystem_of_isColimit (A : X.QuasicoherentAlgebra)
    (I : Type (u + 1)) [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : Functor I X.QuasicoherentAlgebra) (φ : F ⟶ (Functor.const I).obj A)
    (hqc : ∀ i, Scheme.QuasicoherentAlgebra.IsQuasicoherent (F.obj i))
    (hfp : ∀ i, Scheme.QuasicoherentAlgebra.IsOfFinitePresentation (F.obj i))
    (hcolim : Nonempty (IsColimit (Cocone.mk A φ))) :
    ∃ (I : Type (u + 1)) (_ : PartialOrder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : Functor I X.QuasicoherentAlgebra) (φ : F ⟶ (Functor.const I).obj A),
      (∀ i, Scheme.QuasicoherentAlgebra.IsQuasicoherent (F.obj i) ∧
        Scheme.QuasicoherentAlgebra.IsOfFinitePresentation (F.obj i)) ∧
        Nonempty (IsColimit (Cocone.mk A φ)) :=
  ⟨I, inferInstance, inferInstance, inferInstance, F, φ, fun i => ⟨hqc i, hfp i⟩, hcolim⟩

/-- **A directed colimit from a sectionwise approximation over the affine opens.** A directed
system of quasi-coherent algebras of finite presentation mapping to `A` presents `A` as a directed
colimit of quasi-coherent algebras of finite presentation as soon as, over every affine open, every
section of `A` comes from a member of the system and two sections with the same image in `A`
already agree at a later index. -/
theorem exists_directedSystem_of_affineSections (A : X.QuasicoherentAlgebra)
    (I : Type (u + 1)) [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : Functor I X.QuasicoherentAlgebra) (φ : F ⟶ (Functor.const I).obj A)
    (hqc : ∀ i, Scheme.QuasicoherentAlgebra.IsQuasicoherent (F.obj i))
    (hfp : ∀ i, Scheme.QuasicoherentAlgebra.IsOfFinitePresentation (F.obj i))
    (hsurj : ∀ U : X.Opens, IsAffineOpen U → ∀ x : A.right.obj.obj (op U),
      ∃ (i : I) (y : (F.obj i).right.obj.obj (op U)),
        (φ.app i).right.hom.app (op U) y = x)
    (hinj : ∀ U : X.Opens, IsAffineOpen U → ∀ (i : I)
        (x y : (F.obj i).right.obj.obj (op U)),
        (φ.app i).right.hom.app (op U) x = (φ.app i).right.hom.app (op U) y →
          ∃ (j : I) (h : i ≤ j),
            (F.map (homOfLE h)).right.hom.app (op U) x =
              (F.map (homOfLE h)).right.hom.app (op U) y) :
    ∃ (I : Type (u + 1)) (_ : PartialOrder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : Functor I X.QuasicoherentAlgebra) (φ : F ⟶ (Functor.const I).obj A),
      (∀ i, Scheme.QuasicoherentAlgebra.IsQuasicoherent (F.obj i) ∧
        Scheme.QuasicoherentAlgebra.IsOfFinitePresentation (F.obj i)) ∧
        Nonempty (IsColimit (Cocone.mk A φ)) :=
  exists_directedSystem_of_isColimit A I F φ hqc hfp <|
    nonempty_isColimit_of_affineSections (Cocone.mk A φ) hsurj
      fun U hU i x y h => by
        obtain ⟨j, hij, hxy⟩ := hinj U hU i x y h
        exact ⟨j, homOfLE hij, hxy⟩

/-- **A directed colimit from a sectionwise approximation indexed by a set of `Type u`.** A
directed system, indexed by a set of `Type u`, of quasi-coherent algebras of finite presentation
mapping to `A` presents `A` as a directed colimit of quasi-coherent algebras of finite
presentation, indexed by a set of `Type (u + 1)`, as soon as, over every affine open, every
section of `A` comes from a member of the system and two sections with the same image in `A`
already agree at a later index. -/
theorem exists_directedSystem_of_affineSections_of_smallIndex (A : X.QuasicoherentAlgebra)
    (I : Type u) [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : Functor I X.QuasicoherentAlgebra) (φ : F ⟶ (Functor.const I).obj A)
    (hqc : ∀ i, Scheme.QuasicoherentAlgebra.IsQuasicoherent (F.obj i))
    (hfp : ∀ i, Scheme.QuasicoherentAlgebra.IsOfFinitePresentation (F.obj i))
    (hsurj : ∀ U : X.Opens, IsAffineOpen U → ∀ x : A.right.obj.obj (op U),
      ∃ (i : I) (y : (F.obj i).right.obj.obj (op U)),
        (φ.app i).right.hom.app (op U) y = x)
    (hinj : ∀ U : X.Opens, IsAffineOpen U → ∀ (i : I)
        (x y : (F.obj i).right.obj.obj (op U)),
        (φ.app i).right.hom.app (op U) x = (φ.app i).right.hom.app (op U) y →
          ∃ (j : I) (h : i ≤ j),
            (F.map (homOfLE h)).right.hom.app (op U) x =
              (F.map (homOfLE h)).right.hom.app (op U) y) :
    ∃ (I : Type (u + 1)) (_ : PartialOrder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : Functor I X.QuasicoherentAlgebra) (φ : F ⟶ (Functor.const I).obj A),
      (∀ i, Scheme.QuasicoherentAlgebra.IsQuasicoherent (F.obj i) ∧
        Scheme.QuasicoherentAlgebra.IsOfFinitePresentation (F.obj i)) ∧
        Nonempty (IsColimit (Cocone.mk A φ)) := by
  have hdown : Monotone (ULift.down : ULift.{u + 1} I → I) := fun _ _ h => h
  have : IsDirected (ULift.{u + 1} I) (· ≤ ·) :=
    ⟨fun a b => by
      obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a.down b.down
      exact ⟨⟨c⟩, hac, hbc⟩⟩
  refine exists_directedSystem_of_affineSections A (ULift.{u + 1} I) (hdown.functor ⋙ F)
    (Functor.whiskerLeft hdown.functor φ) (fun i => hqc i.down) (fun i => hfp i.down)
    (fun U hU x => ?_) (fun U hU i x y h => ?_)
  · obtain ⟨i, y, hy⟩ := hsurj U hU x
    exact ⟨⟨i⟩, y, hy⟩
  · obtain ⟨j, hij, hxy⟩ := hinj U hU i.down x y h
    exact ⟨⟨j⟩, hij, hxy⟩

end Stacks.QcohAlgebraFPColimit
