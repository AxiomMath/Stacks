module

public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexBaseRing

/-!
# A ringed site over a base ring, from a ring map to the global sections

A ring map `ψ : R ⟶ Γ(C, O)` into the ring of global sections of a ringed site makes the category
of `O`-modules `R`-linear, a scalar acting through its image in `Γ(C, O)`, and this linear
structure satisfies `AlgebraicGeometry.RingedSite.ScalarSections`, with `ψ r` read over `U` as the
section by which `r` multiplies.

## Main definitions

* `AlgebraicGeometry.RingedSite.linearOfGlobalSections`: the `R`-linear structure on the sheaves
  of `O`-modules induced by `ψ`.
* `AlgebraicGeometry.RingedSite.scalarSectionsOfGlobalSections`: the scalars act by the sections
  `ψ r`.

## References

* [Stacks Project, Tag 0CS6](https://stacks.math.columbia.edu/tag/0CS6)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.RingedSite

universe u v w t s o

variable (X : AlgebraicGeometry.RingedSite.{u, v, w}) {R : Type o} [CommRing R]
  (ψ : R →+*
    ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- The `R`-linear structure induced by a ring map `ψ : R ⟶ Γ(C, O)`: a scalar `r` acts on
morphisms of sheaves of `O`-modules as its image `ψ r` does. -/
abbrev linearOfGlobalSections : Linear R (TensorModO.{u, v, w, t, s} X) :=
  Linear.ofRingHom ψ

/-- For the linear structure induced by `ψ : R ⟶ Γ(C, O)`, a scalar `r` multiplies by the
sections `ψ r`, making `(C, O)` a ringed site over `R`. -/
@[instance_reducible]
def scalarSectionsOfGlobalSections :
    letI := linearOfGlobalSections.{u, v, w, t, s} X ψ
    ScalarSections.{u, v, w, t, s, o} X R :=
  let := linearOfGlobalSections.{u, v, w, t, s} X ψ
  { scalarSection := fun r U => (ψ r).val U
    smul_app := fun r _ _ f U y =>
      (scalarSectionsGlobalSectionRing.{u, v, w, t, s} X).smul_app (ψ r) f U y }

end AlgebraicGeometry.RingedSite
