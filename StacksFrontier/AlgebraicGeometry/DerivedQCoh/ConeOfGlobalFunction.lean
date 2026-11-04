module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseRingLinear
public import StacksFrontier.CategoryTheory.Triangulated.ConeOfScalar

/-!
# The cone of multiplication by a global function on a scheme

Let `X` be a scheme. A global function `r ∈ Γ(X, 𝒪_X)` acts on every sheaf of `𝒪_X`-modules by
multiplication, and that action makes the category of sheaves of modules — hence also its
derived category — linear over `Γ(X, 𝒪_X)`. This file transports the abstract statements of
`StacksFrontier.CategoryTheory.Triangulated.ConeOfScalar` to that setting, which is where
[Stacks, Tag 08EK] uses them: the cone of multiplication by `r` on an object of `D(𝒪_X)` is
annihilated by `r ^ 2`, and the top of a tower of such cones over `r₀, …, r_{s-1}` is
annihilated by a power of each `r_j`.

## Main definitions

* `Stacks.DerivedQCoh.globalSectionsLinear`: the `Γ(X, 𝒪_X)`-linear structure on sheaves of
  `𝒪_X`-modules, pinned at the module universe `u` of the scheme. It is
  `AlgebraicGeometry.Scheme.linearOfRingHom` at the identity ring map and must not be rebuilt:
  a second, parallel action of the same ring on the same category would make two objects out of
  one notion of scalar multiplication.

## Main results

* `Stacks.DerivedQCoh.sq_smul_id_eq_zero_of_cone_globalSection`: the cone of `r • 𝟙 E` in
  `D(𝒪_X)` is annihilated by `r ^ 2`.
* `Stacks.DerivedQCoh.exists_pow_smul_id_eq_zero_of_coneTower_globalSections`: in a tower
  `E₀, E₁ = Cone(r₀ • 𝟙 E₀), …, E_s = Cone(r_{s-1} • 𝟙 E_{s-1})` a power of each `r_j`
  annihilates `E_s`.

## Implementation notes

The linear structure is not and cannot be a global instance: the coefficient ring is not
determined by the category, so `AlgebraicGeometry.Scheme.linearOfRingHom` takes it as an
argument. Here it is specialized once, at `A = Γ(X, 𝒪_X)` and the identity ring map, and
declared as a `local instance` so that the statements below can be written with `•` and read
off the abstract lemmas with no transport. A consumer in another module reintroduces it with
`letI := Stacks.DerivedQCoh.globalSectionsLinear X`; the scalar multiplications then agree on
the nose, which they would not if the structure were rebuilt from
`Scheme.linearOfRingHom` with a differently spelled ring map.

The derived category is the standard model, as in the rest of the `DerivedQCoh` tree: the
`Γ(X, 𝒪_X)`-linearity of `DerivedCategory` and of its shift functors comes from Mathlib's
`DerivedCategory.instLinear` and `DerivedCategory.instLinearShiftFunctor`, which need the
abelian category to be linear and nothing else.

Nothing here is tagged: these are steps of the proof of [Stacks, Tag 08EK], whose other inputs
are [Stacks, Tag 08EH]
(`Stacks.DerivedQCoh.OpenLift.exists_isPerfect_derivedTensor_lift_of_isAffine`) and
[Stacks, Tag 08EJ] on a quasi-compact quasi-separated scheme
(`Stacks.DerivedQCoh.exists_pow_smul_eq_zero_of_isPerfect_of_cohomologySupportedOn`).

## References

* [Stacks Project, Tag 08EK](https://stacks.math.columbia.edu/tag/08EK)
* [Stacks Project, Tag 05QP](https://stacks.math.columbia.edu/tag/05QP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated AlgebraicGeometry Opposite

universe u

namespace Stacks.DerivedQCoh

attribute [local instance] HasDerivedCategory.standard

variable (X : Scheme.{u})

/-- **Sheaves of `𝒪_X`-modules are linear over the global functions.** This is
`AlgebraicGeometry.Scheme.linearOfRingHom` at `A = Γ(X, 𝒪_X)` and the identity ring map, with
the module universe pinned to the scheme's. -/
@[instance_reducible]
local instance globalSectionsLinear :
    CategoryTheory.Linear ↥Γ(X, ⊤) (SheafOfModules.{u} X.ringCatSheaf) :=
  Scheme.linearOfRingHom.{u, u} X Γ(X, ⊤) (RingHom.id _)

variable {X}

/-- **The cone of multiplication by a global function `r` is annihilated by `r ^ 2`.** For a
distinguished triangle `E --(r • 𝟙 E)--> E --g--> Z --h--> E⟦1⟧` in `D(𝒪_X)` one has
`r ^ 2 • 𝟙 Z = 0`.

This is the square-zero step of [Stacks, Tag 08EK], where `Z` is the complex `C₁` obtained as
the cone of multiplication by `g₁` on the perfect object `E`. -/
theorem sq_smul_id_eq_zero_of_cone_globalSection (r : Γ(X, ⊤))
    {E Z : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)} (g : E ⟶ Z)
    (h : Z ⟶ E⟦(1 : ℤ)⟧) (hT : Triangle.mk (r • 𝟙 E) g h ∈ distTriang _) :
    r ^ 2 • 𝟙 Z = 0 :=
  sq_smul_id_eq_zero_of_cone_smul_id r g h hT

/-- **The tower of cones of multiplications by global functions.** If `E (i + 1)` is a cone of
`a i • 𝟙 (E i)` for every `i < s`, then for every `j < s` a power of `a j` annihilates `E s`.

This is the iteration of [Stacks, Tag 08EK]: "continuing, setting `C_{i+1}` equal to the cone of
the map `g_i : C_i → C_i` we obtain a perfect complex `C_s` on `X` supported on `T`". The
nilpotence of each `g_j` on `C_s` is what the source then uses to confine the support of `C_s`
to `T = V(g_0, …, g_{s-1})`, and to carry that confinement across the tensor product
`C' = C_s ⊗^𝐋 I` of the last step. -/
theorem exists_pow_smul_id_eq_zero_of_coneTower_globalSections {s : ℕ} (a : ℕ → Γ(X, ⊤))
    (E : ℕ → DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (tri : ∀ i, i < s → ∃ (u : E i ⟶ E (i + 1)) (v : E (i + 1) ⟶ (E i)⟦(1 : ℤ)⟧),
      Triangle.mk (a i • 𝟙 (E i)) u v ∈ distTriang _)
    {j : ℕ} (hj : j < s) : ∃ k : ℕ, a j ^ k • 𝟙 (E s) = 0 :=
  exists_pow_smul_id_eq_zero_of_coneTower a E tri hj

end Stacks.DerivedQCoh

end
