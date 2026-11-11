module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedBimoduleTensorUniversal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedRestrictionAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedRestrictionSheafHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensorHomHomComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Base change `- ⊗_{A, φ} B` is left adjoint to restriction `res_φ`

Let `(C, O)` be a ringed site, let `A` and `B` be sheaves of differential graded `O`-algebras
and let `φ : A ⟶ B` be a homomorphism of differential graded `O`-algebras. Then `B`, viewed as
the differential graded `(A, B)`-bimodule `{}_A B_B`, gives the base change functor

`- ⊗_{A, φ} B : Mod(A, d) ⥤ Mod(B, d)`,

the tensor product with `{}_A B_B` constructed in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedBimoduleTensorUniversal.lean`,
and this file proves that it is left adjoint to restriction of scalars
`res_φ : Mod(B, d) ⥤ Mod(A, d)`, that is

`Hom_{Mod(B, d)}(M ⊗_{A, φ} B, L) = Hom_{Mod(A, d)}(M, res_φ L)`

functorially in `M` and `L`; this is the adjunction of
[Stacks, Tag 0FRP](https://stacks.math.columbia.edu/tag/0FRP).

## Main definitions

* `SheafOfModules.DifferentialGradedModule.baseChangeData`: the tensor product functor with
  `{}_A B_B`, with its values exhibited as tensor products.
* `SheafOfModules.DifferentialGradedModule.baseChange`: the functor `- ⊗_{A, φ} B`.

## Main results

* `SheafOfModules.DifferentialGradedModule.baseChangeRestrictionAdjunction`:
  `- ⊗_{A, φ} B ⊣ res_φ`.
* `SheafOfModules.DifferentialGradedModule.baseChangeRestrictionAdjunction_unit_app`: its unit
  is `x ↦ x ⊗ 1`.
* `SheafOfModules.DifferentialGradedModule.baseChangeHomogeneousEquiv`, with
  `baseChangeHomogeneousEquiv_add` and `baseChangeHomogeneousEquiv_delta`: the same identity
  on the hom complexes of the differential graded categories,
  `Hom_{Mod^dg(B, d)}(M ⊗_{A, φ} B, L) = Hom_{Mod^dg(A, d)}(M, res_φ L)`, over a ringed site
  whose universes agree, as the hom complexes are stated in
  `DifferentialGradedTensorHomHomComplex.lean`.

## Implementation notes

The adjunction is `SheafOfModules.DifferentialGradedModule.extensionRestrictionAdjunction`,
which is stated for any functor whose values are tensor products with `{}_A B_B`, applied to the
tensor product functor `SheafOfModules.RelativeTensor.tensorFunctorDataDgTensorRight` that the
library constructs.

A homomorphism of differential graded algebras is unital in the source, which is
`SheafOfModules.DifferentialGradedAlgebra.Hom.PreservesOne` here; without it `res_φ L` is not a
differential graded `A`-module.

The ringed site is `X : AlgebraicGeometry.RingedSite.{u, v, w}`, a site `C : Type u` with
`Category.{v} C` and a sheaf of commutative rings `O` on it; the algebras live over
`Stacks.SheafOfModules.Tensor.ringSheaf X.O`, its underlying sheaf of rings. The instance
`X.J.HasSheafCompose (forget₂ CommRingCat RingCat)` the tensor product needs is supplied by
`AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat` rather than by instance search,
which would find Mathlib's size-restricted instance and pin `w`. The homogeneous pieces of the
algebras and the modules live in the universe `max u v`, the universe at which the tensor
product is built (see the implementation notes of `DifferentialGradedBimoduleTensorUniversal.lean`).

The identities of 0FRP involving the internal hom are in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedRestrictionSheafHom.lean`.

## References

* [Stacks Project, Tag 0FRP](https://stacks.math.columbia.edu/tag/0FRP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf

universe w v u

namespace SheafOfModules.DifferentialGradedModule

variable {X : AlgebraicGeometry.RingedSite.{u, v, w}}
  {A B : DifferentialGradedAlgebra.{w, max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  (φ : A ⟶ B) (hφ : φ.PreservesOne)

/-- Base change along `φ` as a tensor product functor: the tensor product with the bimodule
`{}_A B_B` constructed by `SheafOfModules.RelativeTensor.tensorFunctorDataDgTensorRight`. -/
abbrev baseChangeData :
    TensorFunctorData.{w, max u v, max u v, max u v, max u v} A B (φ.toBimodule hφ) :=
  letI := X.hasSheafCompose_forget₂_ringCat
  RelativeTensor.tensorFunctorDataDgTensorRight
    (A := (A : DifferentialGradedAlgebra.{w, max u v} (toRingCat X.J X.O)))
    (B := (B : DifferentialGradedAlgebra.{w, max u v} (toRingCat X.J X.O))) (φ.toBimodule hφ)

/-- **Base change** `- ⊗_{A, φ} B : Mod(A, d) ⥤ Mod(B, d)` along a homomorphism `φ : A ⟶ B` of
sheaves of differential graded algebras on a ringed site: the tensor product with `B` viewed as
the differential graded `(A, B)`-bimodule `{}_A B_B`. Its value at `M` is a tensor product
`M ⊗_A {}_A B_B`, `(baseChangeData φ hφ).isTensorProduct M`. -/
@[stacks 0FRP "the base change functor - ⊗_{A,φ} B on differential graded modules"]
def baseChange :
    DifferentialGradedModule.{w, max u v, max u v} A ⥤
      DifferentialGradedModule.{w, max u v, max u v} B :=
  (baseChangeData φ hφ).functor

/-- **Stacks 0FRP.** Let `(C, O)` be a ringed site, let `A` and `B` be sheaves of differential
graded `O`-algebras and let `φ : A ⟶ B` be a homomorphism of differential graded `O`-algebras.
Then the base change functor `- ⊗_{A, φ} B : Mod(A, d) ⥤ Mod(B, d)`, the tensor product with the
differential graded `(A, B)`-bimodule `{}_A B_B`, is left adjoint to the restriction functor
`res_φ : Mod(B, d) ⥤ Mod(A, d)`:

`Hom_{Mod(B, d)}(M ⊗_{A, φ} B, L) = Hom_{Mod(A, d)}(M, res_φ L)`

functorially in `M` and `L`, the bijection sending `g` to `x ↦ g (x ⊗ 1)`. -/
@[stacks 0FRP "base change - ⊗_{A,φ} B is left adjoint to restriction res_φ"]
def baseChangeRestrictionAdjunction :
    baseChange φ hφ ⊣ restriction.{w, max u v, max u v} φ hφ :=
  extensionRestrictionAdjunction φ hφ (baseChangeData φ hφ)

/-- The unit of `- ⊗_{A, φ} B ⊣ res_φ` is `x ↦ x ⊗ 1`. -/
theorem baseChangeRestrictionAdjunction_unit_app
    (M : DifferentialGradedModule.{w, max u v, max u v} A) :
    (baseChangeRestrictionAdjunction φ hφ).unit.app M =
      extensionUnit φ hφ (baseChangeData φ hφ) M := by
  change extensionUnit φ hφ _ M ≫ (restriction φ hφ).map (𝟙 _) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

/-! ### The adjunction on hom complexes -/

section HomComplex

open CochainComplex.HomComplex

variable {Y : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A' B' : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
  (ψ : A' ⟶ B') (hψ : ψ.PreservesOne)

/-- **`Hom_{Mod^dg(B, d)}(M ⊗_{A, φ} B, L) = Hom_{Mod^dg(A, d)}(M, res_φ L)` in each degree**
([Stacks, Tag 0FRP](https://stacks.math.columbia.edu/tag/0FRP)): the degree-`n` homogeneous
right-linear maps `M ⊗_{A, φ} B → L` are the degree-`n` homogeneous right-linear maps
`M → res_φ L`. This is the tensor-hom identity of Tag 0FRS for the bimodule `{}_A B_B`, whose
internal hom into `L` is `res_φ L` by `isSheafHomRestrictionObj`. -/
@[stacks 0FRP "Hom_{Mod^dg(B,d)}(M ⊗_A B, L) = Hom_{Mod^dg(A,d)}(M, res_φ L), degreewise"]
noncomputable def baseChangeHomogeneousEquiv (M : DifferentialGradedModule.{u, u, u} A')
    (L : DifferentialGradedModule.{u, u, u} B') (n : ℤ) :
    HomogeneousMap B' ((baseChange ψ hψ).obj M) L n ≃
      HomogeneousMap A' M ((restriction.{u, u, u} ψ hψ).obj L) n :=
  tensorHomHomogeneousEquiv ((baseChangeData ψ hψ).isTensorProduct M)
    (isSheafHomRestrictionObj ψ hψ L) n

/-- The identification `baseChangeHomogeneousEquiv` is additive. -/
@[stacks 0FRP "Hom_{Mod^dg(B,d)}(M ⊗_A B, L) = Hom_{Mod^dg(A,d)}(M, res_φ L), additively"]
theorem baseChangeHomogeneousEquiv_add (M : DifferentialGradedModule.{u, u, u} A')
    (L : DifferentialGradedModule.{u, u, u} B') (n : ℤ)
    (f f' g : HomogeneousMap B' ((baseChange ψ hψ).obj M) L n) (hg : g.val = f.val + f'.val) :
    (baseChangeHomogeneousEquiv ψ hψ M L n g).val =
      (baseChangeHomogeneousEquiv ψ hψ M L n f).val +
        (baseChangeHomogeneousEquiv ψ hψ M L n f').val :=
  homogeneousEquiv_add _ _ n f f' g hg

/-- The identification `baseChangeHomogeneousEquiv` commutes with the differentials of the two
hom complexes, so it is an identification of hom complexes. -/
@[stacks 0FRP "Hom_{Mod^dg(B,d)}(M ⊗_A B, L) = Hom_{Mod^dg(A,d)}(M, res_φ L), with differentials"]
theorem baseChangeHomogeneousEquiv_delta (M : DifferentialGradedModule.{u, u, u} A')
    (L : DifferentialGradedModule.{u, u, u} B') (n : ℤ)
    (f : HomogeneousMap B' ((baseChange ψ hψ).obj M) L n)
    (g : HomogeneousMap B' ((baseChange ψ hψ).obj M) L (n + 1)) (hg : g.val = δ n (n + 1) f.val) :
    (baseChangeHomogeneousEquiv ψ hψ M L (n + 1) g).val =
      δ n (n + 1) (baseChangeHomogeneousEquiv ψ hψ M L n f).val :=
  homogeneousEquiv_delta _ _ n f g hg

end HomComplex

end SheafOfModules.DifferentialGradedModule
