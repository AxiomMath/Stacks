module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DGA.Abelian

/-!
# Admissible morphisms and short exact sequences of differential graded modules

A homomorphism of right differential graded modules is an *admissible monomorphism* when it has
a retraction, and an *admissible epimorphism* when it has a section, in each case by a map of
the underlying *graded* right modules — a map which need not commute with the differentials. An
*admissible short exact sequence* is a short exact sequence `K → L → M` which is split in graded
modules.

## Main definitions

* `DifferentialGradedModule.GradedHom`: a degree-zero map of graded right `A`-modules, with no
  compatibility with the differentials.
* `DifferentialGradedModule.Hom.toGradedHom`: forget compatibility with the differential.
* `DifferentialGradedModule.IsAdmissibleMono` and
  `DifferentialGradedModule.IsAdmissibleEpi`: the two admissibility conditions.
* `DifferentialGradedModule.IsAdmissibleShortExact`: a short exact sequence split in graded
  modules.

## Main results

* `DifferentialGradedModule.IsAdmissibleMono.injective` and
  `DifferentialGradedModule.IsAdmissibleEpi.surjective`: admissibility implies injectivity,
  resp. surjectivity, of the underlying map.

## References

* [Stacks Project, Tag 09JT](https://stacks.math.columbia.edu/tag/09JT)
-/

@[expose] public section

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}

/-- A degree-zero map of graded right `A`-modules, not required to commute with the
differentials. -/
structure GradedHom (M N : DifferentialGradedModule A) where
  /-- The underlying `R`-linear map. -/
  toFun : M.M →ₗ[R] N.M
  /-- Compatibility with the right `A`-action. -/
  map_smul : ∀ (x : M.M) (a : A.A),
    toFun (MulOpposite.op a • x) = MulOpposite.op a • toFun x
  /-- Compatibility with the gradings. -/
  map_grading : ∀ (n : ℤ) (x : M.M), x ∈ M.grading n → toFun x ∈ N.grading n

/-- Forget compatibility with the differential. -/
def Hom.toGradedHom {M N : DifferentialGradedModule A} (f : Hom M N) : GradedHom M N where
  toFun := f.toFun
  map_smul := f.map_smul
  map_grading := f.map_grading

/-- A homomorphism of differential graded modules is an admissible monomorphism if it has a
retraction by a map of graded right modules. -/
@[stacks 09JT "part (1)"]
abbrev IsAdmissibleMono {K L : DifferentialGradedModule A} (f : Hom K L) : Prop :=
  ∃ π : GradedHom L K, ∀ x : K.M, π.toFun (f.toFun x) = x

/-- An admissible monomorphism is injective on the underlying module. -/
theorem IsAdmissibleMono.injective {K L : DifferentialGradedModule A} {f : Hom K L}
    (hf : IsAdmissibleMono f) : Function.Injective f.toFun :=
  Function.LeftInverse.injective hf.choose_spec

/-- A homomorphism of differential graded modules is an admissible epimorphism if it has a
section by a map of graded right modules. -/
@[stacks 09JT "part (2)"]
abbrev IsAdmissibleEpi {L M : DifferentialGradedModule A} (g : Hom L M) : Prop :=
  ∃ s : GradedHom M L, ∀ x : M.M, g.toFun (s.toFun x) = x

/-- An admissible epimorphism is surjective on the underlying module. -/
theorem IsAdmissibleEpi.surjective {L M : DifferentialGradedModule A} {g : Hom L M}
    (hg : IsAdmissibleEpi g) : Function.Surjective g.toFun :=
  Function.RightInverse.surjective hg.choose_spec

/-- A short exact sequence of differential graded modules that splits as a sequence of graded
modules. -/
@[stacks 09JT "part (3)"]
structure IsAdmissibleShortExact {K L M : DifferentialGradedModule A}
    (f : Hom K L) (g : Hom L M) : Prop where
  injective : Function.Injective f.toFun
  surjective : Function.Surjective g.toFun
  exact : LinearMap.range f.toFun = LinearMap.ker g.toFun
  admissibleMono : IsAdmissibleMono f
  admissibleEpi : IsAdmissibleEpi g

end DifferentialGradedModule
