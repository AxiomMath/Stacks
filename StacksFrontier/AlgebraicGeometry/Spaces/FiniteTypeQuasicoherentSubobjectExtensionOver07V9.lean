module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs

/-!
# Extending a finite type quasi-coherent submodule, with a redundant Stacks 07V9 input

`AlgebraicGeometry.Space.exists_finiteTypeQuasicoherentSubobject_extension` in
`StacksFrontier/AlgebraicGeometry/Spaces/FiniteTypeQuasicoherentSubobjectExtension.lean` proves
Stacks 0853 — a quasi-coherent submodule of finite type of `ℱ|_U`, for `U` a quasi-compact open
of a quasi-compact quasi-separated algebraic space `X`, extends to one of `ℱ` — under exactly the
source's hypotheses.  This file keeps an earlier form of that statement which also takes
Stacks 07V9 for `X` as an argument; the argument is not used, Stacks 07V9 being
`AlgebraicGeometry.Space.exists_isFilteredColimit_isFinitePresentationOnSite`.

## Main results

* `AlgebraicGeometry.Space.exists_finiteTypeQuasicoherentSubobject_extension_of_07V9`:
  Stacks 0853 with an additional, unused, Stacks 07V9 argument.

## References

* [Stacks Project, Tag 0853](https://stacks.math.columbia.edu/tag/0853)
* [Stacks Project, Tag 07V9](https://stacks.math.columbia.edu/tag/07V9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Stacks 0853, with a redundant Stacks 07V9 argument.** Let `X` be a quasi-compact and
quasi-separated algebraic space, `U ⊂ X` a quasi-compact open, `ℱ` a quasi-coherent
`𝒪_X`-module and `𝒢 ⊂ ℱ|_U` a quasi-coherent `𝒪_U`-submodule of finite type.  Then there is a
quasi-coherent submodule `𝒢' ⊂ ℱ` of finite type with `𝒢'|_U = 𝒢`, the equality being an
isomorphism of `𝒢'|_U` with `𝒢` commuting with the inclusions into `ℱ|_U`.

The argument `_h07V9` (Stacks 07V9 for `X`) is not used: this is
`AlgebraicGeometry.Space.exists_finiteTypeQuasicoherentSubobject_extension`, which is the form
to prefer.  It carries no `stacks` attribute. -/
theorem exists_finiteTypeQuasicoherentSubobject_extension_of_07V9
    {U X : AlgebraicSpaces B S hS} (j : U ⟶ X)
    (hj : IsOpenImmersion B S hS j.hom)
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hUqc : IsQuasiCompactSpace B S hS U.1)
    (_h07V9 : IsQuasiCompactSpace B S hS X.1 → IsAbsolutelyQuasiSeparated B S hS hZ X.1 →
      ∀ M : Modules.{u, u} B S hS X.1 X.2, M.IsQuasicoherentOnSite →
        ∃ (I : Type u) (inst : SmallCategory I),
          let _ := inst
          ∃ (_ : IsFiltered I) (D : I ⥤ Modules.{u, u} B S hS X.1 X.2)
            (φ : D ⟶ (Functor.const I).obj M),
            (∀ i, (D.obj i).IsFinitePresentationOnSite) ∧
              Nonempty (IsColimit (Cocone.mk M φ)))
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (G : Subobject ((etaleModulePullback.{u, u} B S hS j
      (isEtale_of_isOpenImmersion B S hS hj)).obj F))
    [(G : Modules.{u, u} B S hS U.1 U.2).IsQuasicoherentOnSite]
    [(G : Modules.{u, u} B S hS U.1 U.2).IsFiniteType] :
    ∃ G' : Subobject F, (G' : Modules.{u, u} B S hS X.1 X.2).IsQuasicoherentOnSite ∧
      (G' : Modules.{u, u} B S hS X.1 X.2).IsFiniteType ∧
      ∃ e : (etaleModulePullback.{u, u} B S hS j
            (isEtale_of_isOpenImmersion B S hS hj)).obj
          (G' : Modules.{u, u} B S hS X.1 X.2) ≅ (G : Modules.{u, u} B S hS U.1 U.2),
        (etaleModulePullback.{u, u} B S hS j
            (isEtale_of_isOpenImmersion B S hS hj)).map G'.arrow = e.hom ≫ G.arrow :=
  exists_finiteTypeQuasicoherentSubobject_extension B S hS hZ j hj hXqc hXqs hUqc F G

end AlgebraicGeometry.Space

end
