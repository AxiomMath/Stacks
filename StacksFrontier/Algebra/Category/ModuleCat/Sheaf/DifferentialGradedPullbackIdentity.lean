module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullback

/-!
# The pullback of right differential graded modules along the identity morphism of ringed sites

The identity functor of a site, with the identity structure map of its sheaf of rings and the
identity homomorphism of a sheaf of differential graded algebras, is a morphism of ringed sites,
and along it every right differential graded module is its own pullback: a semilinear map out of
`M` along the identity is literally a morphism of right differential graded modules out of `M`,
so the identity semilinear map of `M` has the universal property of the unit.

## Main definitions

* `SheafOfModules.DifferentialGradedAlgebra.idSemilinearHom` is the identity, read as a
  semilinear homomorphism of sheaves of differential graded algebras along `𝟭 C`.
* `SheafOfModules.DifferentialGradedModule.idSemilinearUnit` is the identity, read as a
  semilinear map of right differential graded modules along `𝟭 C`.
* `SheafOfModules.DifferentialGradedModule.idPullbackData` is the resulting
  `SheafOfModules.DifferentialGradedModule.PullbackData`: a pullback of every right differential
  graded `A`-module at once along the identity.

## Main results

* `SheafOfModules.DifferentialGradedModule.homOfIdSemilinearHom`: a semilinear map along the
  identity is a morphism of right differential graded modules, on the same sections.

## Implementation notes

The term `idPullbackData` of `SheafOfModules.DifferentialGradedModule.PullbackData` carries no
hypotheses at all — no continuity, no sheafification, no smallness, and no relation between the
universe of the module sections and the universes of the site. Condition (3) of goodness, Tag 0FSA,
quantifies over a `PullbackData` along an arbitrary functor of sites and concludes flatness and
K-flatness of the pullback; this quantifier is therefore never empty, whatever the universes are.

Every field of the two semilinear maps is `rfl`: along `𝟭 C` the sections of a module over `V`
and over `(𝟭 C).op.obj V` are the same type, and the structure map is `𝟙`, so semilinearity is
linearity on the nose. What is not definitional is the passage from the semilinear map to a
morphism of modules, `homOfIdSemilinearHom`: the morphism of sheaves of modules has to be
assembled from the degreewise additive maps with `PresheafOfModules.homMk`.

## References

* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
* [Stacks Project, Tag 0FRU](https://stacks.math.columbia.edu/tag/0FRU)
-/

@[expose] public section

open CategoryTheory

universe t a m v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

namespace DifferentialGradedAlgebra

/-- **The identity morphism of ringed sites**, as a semilinear homomorphism of sheaves of
differential graded algebras along `𝟭 C` and the identity structure map. -/
def idSemilinearHom (A : DifferentialGradedAlgebra.{t, a} R) :
    SemilinearHom (𝟭 C) (𝟙 R.obj) A A where
  app _ _ := AddMonoidHom.id _
  map_smul _ _ _ _ := rfl
  naturality _ {_ _} _ _ := rfl
  comm_d _ _ _ := rfl
  map_mul _ _ _ _ _ := rfl
  map_one _ := rfl

/-- The identity semilinear homomorphism `idSemilinearHom A` is the identity on every local
section. -/
@[simp]
theorem idSemilinearHom_app (A : DifferentialGradedAlgebra.{t, a} R) (i : ℤ) (V : Cᵒᵖ)
    (x : (A.complex.X i).val.obj V) : (idSemilinearHom A).app i V x = x :=
  rfl

end DifferentialGradedAlgebra

namespace DifferentialGradedModule

variable {A : DifferentialGradedAlgebra.{t, a} R}

/-- **A semilinear map along the identity is a morphism of right differential graded modules**,
with the same maps on local sections. -/
noncomputable def homOfIdSemilinearHom {M N : DifferentialGradedModule.{t, a, m} A}
    (θ : SemilinearHom (DifferentialGradedAlgebra.idSemilinearHom A) M N) : M ⟶ N where
  toHomologicalComplex :=
    { f := fun i =>
        ⟨PresheafOfModules.homMk
          { app := fun V => AddCommGrpCat.ofHom (θ.app i V)
            naturality := fun {V W} k => by ext x; exact θ.naturality i k x }
          fun V r x => θ.map_smul i V r x⟩
      comm' := fun i j hij => by
        obtain rfl : i + 1 = j := hij
        ext V x
        exact (θ.comm_d i V x).symm }
  map_mul := θ.map_mul

/-- The morphism `homOfIdSemilinearHom θ` acts on local sections as `θ`. -/
@[simp]
theorem homOfIdSemilinearHom_app {M N : DifferentialGradedModule.{t, a, m} A}
    (θ : SemilinearHom (DifferentialGradedAlgebra.idSemilinearHom A) M N) (i : ℤ) (V : Cᵒᵖ)
    (x : (M.complex.X i).val.obj V) :
    ((homOfIdSemilinearHom θ).toHomologicalComplex.f i).val.app V x = θ.app i V x :=
  rfl

/-- **The identity semilinear map** of a right differential graded module along `𝟭 C`. -/
def idSemilinearUnit (M : DifferentialGradedModule.{t, a, m} A) :
    SemilinearHom (DifferentialGradedAlgebra.idSemilinearHom A) M M where
  app _ _ := AddMonoidHom.id _
  map_smul _ _ _ _ := rfl
  naturality _ {_ _} _ _ := rfl
  comm_d _ _ _ := rfl
  map_mul _ _ _ _ _ := rfl

/-- The identity semilinear map `idSemilinearUnit M` is the identity on every local section. -/
@[simp]
theorem idSemilinearUnit_app (M : DifferentialGradedModule.{t, a, m} A) (i : ℤ) (V : Cᵒᵖ)
    (x : (M.complex.X i).val.obj V) : (idSemilinearUnit M).app i V x = x :=
  rfl

/-- **The identity semilinear map exhibits a module as its own pullback along the identity.** -/
noncomputable def isPullback_idSemilinearUnit (M : DifferentialGradedModule.{t, a, m} A) :
    IsPullback (idSemilinearUnit M) where
  desc θ' := homOfIdSemilinearHom θ'
  fac _ := SemilinearHom.ext fun _ _ _ => rfl
  uniq θ' h hh := Hom.ext fun n => by
    ext V x
    exact congrArg (fun ρ => ρ.app n V x) hh

/-- **A pullback datum along the identity morphism of ringed sites**: every right differential
graded `A`-module is its own pullback, with the identity semilinear map as unit. -/
noncomputable def idPullbackData :
    PullbackData.{t, a, m, v, u, a, m, v, u} (DifferentialGradedAlgebra.idSemilinearHom A) where
  obj M := M
  unit M := idSemilinearUnit M
  isPullback M := isPullback_idSemilinearUnit M

/-- The pullback of `M` in `idPullbackData` is `M` itself. -/
@[simp]
theorem idPullbackData_obj (M : DifferentialGradedModule.{t, a, m} A) :
    (idPullbackData (A := A)).obj M = M :=
  rfl

end DifferentialGradedModule

end SheafOfModules
