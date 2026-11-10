module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.EtaleModuleHomResolution
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RegularDescentHomEpi
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalCompactSupportFrobenius

/-!
# `Hom_{A[H]}(N, -)` on the complex computing `RΓ_c(U_k̄, D(A[H]))`

Let `D = D(A[H])` be the regular descent sheaf of a Galois covering of `U`, `A = ℤ/ℓⁿ`, and
`j : U ⟶ X̄` a compactification over `k`. The sheaf `F' = (j_! D)|_{X̄_k̄}` whose cohomology is
`RΓ_c(U_k̄, D)` is locally injective: `Hom(N₂, F') → Hom(N₁, F')` is an epimorphism for every
injection `N₁ → N₂` of finite `A[H]`-modules. Indeed this holds for `D` on `U`
(`AlgebraicGeometry.EtaleGaloisCovering.epi_etaleModuleHomPrecomp_regularDescentSheaf`), and
`Hom_{A[H]}(N, -)` commutes with the exact functors `j_!` and inverse image
(`Stacks.EtaleCohomology.isIso_coefficientMate_extensionByZero`,
`Stacks.EtaleCohomology.isIso_coefficientMate_inverseImage`).

## Main results

* `Stacks.EtaleCohomology.epi_homSheafPrecomp_of_coefficientMate`
* `Stacks.EtaleCohomology.epi_homSheafPrecomp_fieldBaseChange_extensionByZero_regularDescentSheaf`

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

variable {A : Type} [CommRing A] {R : Type} [Ring R] [Algebra A R]

/-- **Local injectivity is carried by an exact left adjoint** commuting with `Hom_R(N, -)`. -/
lemma epi_homSheafPrecomp_of_coefficientMate {S T : Scheme.{u}} (uf : S.Etale ⥤ T.Etale)
    [uf.IsContinuous S.smallEtaleTopology T.smallEtaleTopology]
    {L_R : EtaleModules.{u, 0} R S ⥤ EtaleModules.{u, 0} R T}
    (adj_R : L_R ⊣ uf.sheafPushforwardContinuous (ModuleCat.{u + 1} R) S.smallEtaleTopology
      T.smallEtaleTopology)
    {L_A : EtaleModules.{u, 0} A S ⥤ EtaleModules.{u, 0} A T}
    (adj_A : L_A ⊣ uf.sheafPushforwardContinuous (ModuleCat.{u + 1} A) S.smallEtaleTopology
      T.smallEtaleTopology)
    {N₁ N₂ : ModuleCat.{u + 1} R} (v : N₁ ⟶ N₂) (G : EtaleModules.{u, 0} R S)
    (h : Epi ((homSheafPrecomp (A := A) v S).app G))
    (h₁ : IsIso ((coefficientMate uf adj_R L_A adj_A
      (homFunctor N₁ (centralScalars (A := A) N₁))).app G))
    (h₂ : IsIso ((coefficientMate uf adj_R L_A adj_A
      (homFunctor N₂ (centralScalars (A := A) N₂))).app G)) :
    Epi ((homSheafPrecomp (A := A) v T).app (L_R.obj G)) := by
  have : (homSheafPrecomp (A := A) v T).app (L_R.obj G) =
      inv ((coefficientMate uf adj_R L_A adj_A
        (homFunctor N₂ (centralScalars (A := A) N₂))).app G) ≫
        L_A.map ((homSheafPrecomp (A := A) v S).app G) ≫
        (coefficientMate uf adj_R L_A adj_A
          (homFunctor N₁ (centralScalars (A := A) N₁))).app G := by
    rw [coefficientMate_naturality uf adj_R L_A adj_A (homFunctorPrecomp (A := A) v) G,
      IsIso.inv_hom_id_assoc]
  rw [this]
  have := adj_A.isLeftAdjoint
  infer_instance

section RegularDescent

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} [NeZero n] {H : Type} [Group H] [Finite H]
  (G : EtaleGaloisCovering X H)

omit [NeZero n] in
/-- **`(j_! D(A[H]))|_{X̄_k̄}` is locally injective**: `Hom(N₂, -) → Hom(N₁, -)` is an epimorphism
on it for every injection `N₁ → N₂` of finite `A[H]`-modules. -/
theorem epi_homSheafPrecomp_fieldBaseChange_extensionByZero_regularDescentSheaf
    {N₁ N₂ : ModuleCat.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ n)) H)}
    [Module.Finite (MonoidAlgebra (ZMod (ℓ ^ n)) H) N₁]
    [Module.Finite (MonoidAlgebra (ZMod (ℓ ^ n)) H) N₂] (v : N₁ ⟶ N₂) [Mono v] :
    Epi ((homSheafPrecomp (A := ZMod (ℓ ^ n)) v (fieldBaseChange (Over.mk j.toBase) kbar)).app
      ((etaleModuleInverseImage.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H)
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H) j.immersion).obj
          (G.regularDescentSheaf (A := ZMod (ℓ ^ n)))))) := by
  have := Fintype.ofFinite H
  let R := MonoidAlgebra (ZMod (ℓ ^ n)) H
  have : NeZero (ℓ ^ n) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  have : Finite R := Module.finite_of_finite (ZMod (ℓ ^ n))
  have : IsNoetherianRing R := isNoetherian_of_finite R R
  let D := G.regularDescentSheaf (A := ZMod (ℓ ^ n))
  have hj := epi_homSheafPrecomp_of_coefficientMate (Scheme.Etale.smallEtaleCompose j.immersion)
    (etaleModuleExtensionByZeroAdj.{u, 0} R j.immersion)
    (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod (ℓ ^ n)) j.immersion) v D
    (G.epi_etaleModuleHomPrecomp_regularDescentSheaf v)
    (isIso_coefficientMate_extensionByZero j.immersion N₁ D)
    (isIso_coefficientMate_extensionByZero j.immersion N₂ D)
  exact epi_homSheafPrecomp_of_coefficientMate
    (smallEtaleBaseChange (fieldBaseChangeProj (Over.mk j.toBase) kbar))
    (etaleModuleInverseImageAdj.{u, 0} R (fieldBaseChangeProj (Over.mk j.toBase) kbar))
    (etaleModuleInverseImageAdj.{u, 0} (ZMod (ℓ ^ n))
      (fieldBaseChangeProj (Over.mk j.toBase) kbar))
    v _ hj (isIso_coefficientMate_inverseImage _ N₁ _) (isIso_coefficientMate_inverseImage _ N₂ _)

end RegularDescent

end Stacks.EtaleCohomology
