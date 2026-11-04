module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTower
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionTwistCompat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Refinement

/-!
# Local terms at the boundary of an ℓ-adic sheaf on a curve, killed by a fixed power of `ℓ`

Let `j : U ⟶ X̄` be a compactification of `f : U ⟶ Spec k`, `k̄` an extension field of `k`,
`Y = X̄_k̄`, `j' : U_k̄ ⟶ Y` the base change of `j`, and `F` an ℓ-adic sheaf on `U` with levels
`Fₙ`. The *local terms of `F` at the boundary* are the restrictions to `Y ∖ U_k̄` of
`j'_* (Fₙ|_{U_k̄})` and of `R¹j'_* (Fₙ|_{U_k̄})`; at a geometric point `∞̄` of the boundary their
stalks are `H⁰` and `H¹` of the inertia group at `∞̄` with coefficients in the level module
(`H⁰_loc`, `H¹_loc` of Weil II 1.8). Since `j'_! Fₙ ⟶ j'_* Fₙ` is an isomorphism over `U_k̄` and
`R¹j'_*` vanishes there, they are the cokernel of `j'_! Fₙ ⟶ j'_* Fₙ` and `R¹j'_* Fₙ`.

`Stacks.EtaleCohomology.LAdicSheaf.LocalTermsKilledBy F K` says that both are killed by `ℓ^K`, for
every level `n`, with `K` independent of `n`. This is the hypothesis under which the compactly
supported and the ordinary cohomology of `F` in degree one agree up to bounded torsion, which is
what Poincaré duality on an affine curve needs to pair `H¹_c(U_k̄, F)` with `H¹_c(U_k̄, F^∨)`.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.LocalTermsKilledBy`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
  Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B U.1 U.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian U.1] [Fact ℓ.Prime]
  {k : Type u} [Field k] (f : U.1 ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **The local terms of an ℓ-adic sheaf at the boundary are killed by `ℓ^K`.** For every level
`n`, writing `Gₙ = Fₙ|_{U_k̄}` and `j' : U_k̄ ⟶ X̄_k̄` for the base change of the compactification,
`ℓ^K` kills the cokernel of `j'_! Gₙ ⟶ j'_* Gₙ` (the stalks of `j'_* Gₙ` at the boundary,
`H⁰_loc`) and `R¹j'_* Gₙ` (supported on the boundary, `H¹_loc`). -/
def LAdicSheaf.LocalTermsKilledBy (F : LAdicSheaf B U ℓ) (K : ℕ) : Prop :=
  ∀ n : ℕ,
    (ℓ ^ K) • 𝟙 (cokernel ((etaleModuleExtensionByZeroToDirectImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
      (fieldBaseChangeMap j.obj.hom kbar)).app
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk f) kbar)).obj (LAdicSheaf.etaleLevel B U ℓ F n)))) = 0 ∧
    (ℓ ^ K) • 𝟙 (((etaleModuleDirectImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
      (fieldBaseChangeMap j.obj.hom kbar)).rightDerived 1).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk f) kbar)).obj (LAdicSheaf.etaleLevel B U ℓ F n))) = 0

end Stacks.EtaleCohomology

end
