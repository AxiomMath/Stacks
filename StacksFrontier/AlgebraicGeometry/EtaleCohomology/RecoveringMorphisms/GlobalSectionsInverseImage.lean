module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingTerminalSections
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Morphisms

/-!
# A global function and its image under the inverse-image form of the structure map

Let `(f, f♯) : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪')` be a morphism of ringed topoi whose presenting sites
have terminal objects `T` and `T'`.  Its ring map on global functions,
`AlgebraicGeometry.RingedToposHom.globalSectionsMap`, is defined from the *direct-image* form
`f♯ : 𝒪' ⟶ f_*𝒪` of the structure map, evaluated over `T'`.  The structure map also has an
*inverse-image* form `f⁻¹𝒪' ⟶ 𝒪` on underlying sheaves of sets,
`AlgebraicGeometry.RingedToposHom.fSharpSet`, and a consumer of both needs to know that they
agree on global functions.

That is this file.  A global function is a morphism out of the terminal sheaf
(`CategoryTheory.Sheaf.terminalObjHomEquiv`), and `f⁻¹` carries the terminal sheaf to the
terminal sheaf (`MorphismOfTopoi.inverseImageTerminalIso`), so a global function `s` of `𝒪'` has
an inverse-image reading: transport `*` to `f⁻¹*`, apply `f⁻¹` to `s`, and follow with
`fSharpSet`.  The result is the global function `globalSectionsMap f s` of `𝒪`.

## Main results

* `AlgebraicGeometry.RingedToposHom.terminalObjHomEquiv_globalSectionsMap` — the identification
  just described.

## Implementation notes

The proof is the adjunction `f⁻¹ ⊣ f_*` and nothing else.  `globalSectionsMap` is by definition
`f♯` over `T'` followed by `MorphismOfTopoi.pushforwardCommRingTerminalSectionsIso`, whose
underlying bijection is `MorphismOfTopoi.pushforwardTerminalHomEquiv`, i.e. transposition across
that adjunction followed by `MorphismOfTopoi.inverseImageTerminalIso`; and `fSharpSet` is by
definition the transpose of `f♯` on underlying sheaves of sets.  So the statement is the
naturality of the hom-set bijection in its left argument,
`CategoryTheory.Adjunction.homEquiv_naturality_left_symm`, applied to the global function.
Equivalently it may be read with `AlgebraicGeometry.RingedToposHom.fSharpInverseImage` in place
of `fSharpSet`, the two being identified by
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv`.

The global function is given the type `(f.forgetRing.obj 𝒪').obj.obj (op T')` rather than
`ToType ((𝒪').obj.obj (op T'))`.  The two are the same type, but only the former spelling keeps
the statement type-correct at the `implicit` transparency level, which is what `rw` and
`congrArg` check their motives against; with the latter, rewriting inside the statement fails
with an application type mismatch on the global function itself.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RingedToposHom

universe v u w v' u'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (f : RingedToposHom X Y) {T : X.C} {T' : Y.C}

/-- **A global function of `𝒪'` and its image under the inverse-image form of the structure
map.**  Read a global function `s` of `𝒪'` as a morphism `* ⟶ 𝒪'` out of the terminal sheaf,
transport `*` to `f⁻¹*`, apply `f⁻¹` and follow with `f⁻¹𝒪' ⟶ 𝒪`.  The result is the global
function `AlgebraicGeometry.RingedToposHom.globalSectionsMap f s` of `𝒪`, read the same way.

This is the compatibility of the two forms of the structure map on global functions.  It is what
makes a system of equations with coefficients in the global functions of `𝒪'` push forward,
along `f⁻¹` followed by the structure map, to the system whose coefficients are pushed along
`globalSectionsMap` — the coefficient half of step (3) of the proof of
[Stacks Project, Tag 04I6]. -/
theorem terminalObjHomEquiv_globalSectionsMap (hT : IsTerminal T) (hT' : IsTerminal T')
    (s : (Y.forgetRing.obj Y.O).obj.obj (op T')) :
    Sheaf.terminalObjHomEquiv hT (X.forgetRing.obj X.O) ((f.globalSectionsMap hT hT').hom s) =
      (f.toToposHom.inverseImageTerminalIso).inv ≫
        f.toToposHom.inverseImage.map
          (Sheaf.terminalObjHomEquiv hT' (Y.forgetRing.obj Y.O) s) ≫ f.fSharpSet := by
  have hmid : Sheaf.terminalObjHomEquiv hT' (Y.forgetRing.obj Y.O) s ≫
        Y.forgetRing.map f.fSharp =
      Sheaf.terminalObjHomEquiv hT'
        (f.toToposHom.pushforward.obj (X.forgetRing.obj X.O))
        ((f.fSharp.hom.app (op T')).hom s) :=
    Sheaf.terminalObjHomEquiv_comp hT' s (Y.forgetRing.map f.fSharp)
  have key : f.toToposHom.inverseImage.map
        (Sheaf.terminalObjHomEquiv hT' (Y.forgetRing.obj Y.O) s) ≫ f.fSharpSet =
      (f.toToposHom.adj.homEquiv (⊤_ (Sheaf Y.J (Type w)))
          (X.forgetRing.obj X.O)).symm
        (Sheaf.terminalObjHomEquiv hT'
          (f.toToposHom.pushforward.obj (X.forgetRing.obj X.O))
          ((f.fSharp.hom.app (op T')).hom s)) :=
    ((f.toToposHom.adj.homEquiv_naturality_left_symm
        (Sheaf.terminalObjHomEquiv hT' (Y.forgetRing.obj Y.O) s)
        (Y.forgetRing.map f.fSharp)).symm).trans
      (congrArg (f.toToposHom.adj.homEquiv (⊤_ (Sheaf Y.J (Type w)))
        (X.forgetRing.obj X.O)).symm hmid)
  refine (Equiv.eq_symm_apply _).mp
    (Eq.trans ?_ (congrArg (Sheaf.terminalObjHomEquiv hT (X.forgetRing.obj X.O)).symm
      (congrArg (fun m => (f.toToposHom.inverseImageTerminalIso).inv ≫ m) key.symm)))
  rfl

end AlgebraicGeometry.RingedToposHom

end
