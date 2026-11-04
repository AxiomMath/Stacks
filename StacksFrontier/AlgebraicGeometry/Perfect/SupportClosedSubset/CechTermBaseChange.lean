module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.EquationsBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.GlobalEquationsComplexData
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.RestrictedDirectImageBaseChange

/-!
# Termwise locality of the extended alternating Čech complex

Let `X` be a scheme, `f₁, …, f_c ∈ Γ(X, 𝒪_X)` and `g : X' ⟶ X` an open immersion.  Write `f'ᵢ`
for the pullback of `fᵢ` along `g`.  The terms of the extended alternating Čech complex of
[Stacks, Tag 0G7I] are the direct images

`F_{i₀…i_p} = (U_{i₀…i_p} → X)_*(F|_{U_{i₀…i_p}})`,

and `AlgebraicGeometry.ExtendedAlternatingCech.equationsOpen_pullback` says the index opens are
compatible with restriction, `g ⁻¹ᵁ U_{i₀…i_p} = U'_{i₀…i_p}`.  This file supplies the comparison
that compatibility does not give: the restriction along `g` of the term `F_{i₀…i_p}` is the term
`(g^*F)'_{i₀…i_p}` of the extended alternating Čech complex of the restricted equations.

## Main definitions

* `Stacks.Perfect.PushforwardRestrict.restrictRestrictedModuleIso`: the comparison
  `g^*F_{i₀…i_p} ≅ (g^*F)'_{i₀…i_p}` of the terms.
* `Stacks.Perfect.PushforwardRestrict.restrictRestrictedModuleNatIso`: the same comparison as a
  natural isomorphism in the coefficient module, so that it is compatible with the maps the
  differentials of the complex are assembled from.

## Implementation notes

The comparison is `restrictPushforwardRestrictIso`, the termwise locality of a direct image along
an open immersion, read in the vocabulary of Tag 0G7I.  Three changes of spelling separate the
two: `AlgebraicGeometry.ExtendedAlternatingCech.restrictedModule` is written with
`AlgebraicGeometry.Scheme.Modules.pullback` where `restrictPushforwardRestrictIso` is written
with `AlgebraicGeometry.Scheme.Modules.restrictFunctor`, which
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` reconciles; the index open of the
restricted equations is `g ⁻¹ᵁ U_{i₀…i_p}` only after `equationsOpen_pullback`, which is an
equality of opens and so is transported with `eqToIso`; and the ambient open of the comparison is
an arbitrary open `U` of `X`, instantiated at the principal intersection.

Nothing here is a statement about the complex, its differentials, its augmentation, or the
fraction classes of [Stacks, Tag 0G7Q]: those need the comparison *of the complexes*, for which
this is the termwise input.  See the module docstring of `EquationsBaseChange` for what the
assembly still owes.

## References

* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Perfect.ExtendedAlternatingCech
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.PushforwardRestrict

variable {X X' : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤)) (g : X' ⟶ X)
  [IsOpenImmersion g]

/-- `restrictedFunctor` computes the terms of the extended alternating Čech complex. -/
public theorem restrictedFunctor_obj (F : X.Modules) (p : ℕ)
    (s : CechCochains.OrdIndex (I := Fin c) p) :
    (restrictedFunctor (equationsOpen f p s)).obj F = restrictedModule f F p s := rfl

/-- **Termwise locality of the extended alternating Čech complex.**  The restriction along an
open immersion `g` of the term `(U_{i₀…i_p} → X)_*(F|_{U_{i₀…i_p}})` is the corresponding term of
the extended alternating Čech complex of the restricted equations with coefficients in
`g^*F`. -/
public def restrictRestrictedModuleNatIso (p : ℕ)
    (s : CechCochains.OrdIndex (I := Fin c) p) :
    restrictedFunctor (equationsOpen f p s) ⋙ Scheme.Modules.restrictFunctor g ≅
      Scheme.Modules.restrictFunctor g ⋙
        restrictedFunctor (equationsOpen (fun j => g.appTop (f j)) p s) :=
  restrictedRestrictIso (equationsOpen f p s) g
    (AlgebraicGeometry.ExtendedAlternatingCech.equationsOpen_pullback g f p s)

/-- **Termwise locality of the extended alternating Čech complex**, at a fixed coefficient
module. -/
public def restrictRestrictedModuleIso (F : X.Modules) (p : ℕ)
    (s : CechCochains.OrdIndex (I := Fin c) p) :
    (Scheme.Modules.restrictFunctor g).obj (restrictedModule f F p s) ≅
      restrictedModule (fun j => g.appTop (f j))
        ((Scheme.Modules.restrictFunctor g).obj F) p s :=
  (restrictRestrictedModuleNatIso f g p s).app F

/-- **Degreewise locality of the extended alternating Čech complex.**  The restriction along an
open immersion `g` of the degree-`(p+1)` term `∏_{i₀<⋯<i_p} F_{i₀…i_p}` is the degree-`(p+1)` term
of the extended alternating Čech complex of the restricted equations with coefficients in `g^*F`:
restriction is left exact, so it carries the finite product to the product of the restrictions,
and each factor is compared by `restrictRestrictedModuleIso`. -/
public def restrictProdTermIso (F : X.Modules) (p : ℕ) :
    (Scheme.Modules.restrictFunctor g).obj
        (prodTerm f F p) ≅
      prodTerm (fun j => g.appTop (f j))
        ((Scheme.Modules.restrictFunctor g).obj F) p :=
  PreservesProduct.iso (Scheme.Modules.restrictFunctor g)
      (fun s : CechCochains.OrdIndex (I := Fin c) p => restrictedModule f F p s) ≪≫
    Pi.mapIso fun s => restrictRestrictedModuleIso f g F p s

/-- The degreewise comparison is the termwise comparison in each factor. -/
public theorem restrictProdTermIso_hom_comp_π (F : X.Modules) (p : ℕ)
    (s : CechCochains.OrdIndex (I := Fin c) p) :
    (restrictProdTermIso f g F p).hom ≫
        Pi.π (fun u : CechCochains.OrdIndex (I := Fin c) p =>
          restrictedModule (fun j => g.appTop (f j))
            ((Scheme.Modules.restrictFunctor g).obj F) p u) s =
      (Scheme.Modules.restrictFunctor g).map
          (Pi.π (fun u : CechCochains.OrdIndex (I := Fin c) p => restrictedModule f F p u) s) ≫
        (restrictRestrictedModuleIso f g F p s).hom := by
  change (PreservesProduct.iso (Scheme.Modules.restrictFunctor g)
        (fun u : CechCochains.OrdIndex (I := Fin c) p => restrictedModule f F p u) ≪≫
      Pi.mapIso fun u => restrictRestrictedModuleIso f g F p u).hom ≫ _ = _
  rw [Iso.trans_hom, Category.assoc, Pi.mapIso_hom_π, ← Category.assoc,
    PreservesProduct.iso_hom, piComparison_comp_π]

end Stacks.Perfect.PushforwardRestrict

end
