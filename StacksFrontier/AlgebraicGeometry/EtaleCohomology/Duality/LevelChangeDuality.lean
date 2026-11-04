module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LevelChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleTorsionReduction
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunctionAcyclic
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.WayOutPairing

/-!
# Duality with coefficients `ℤ/pᵃ` read with coefficients `ℤ/pᵐ`

Let `p` be a prime, `a ≤ m`, `Λ = ℤ/pᵐ`, `Λ' = ℤ/pᵃ`, and write `R` for restriction of scalars
along `Λ ↠ Λ'` (sheaves of `Λ'`-modules read as sheaves of `Λ`-modules) and `R^!` for
coextension of scalars, `M ↦ Hom_Λ(Λ', M) = M[pᵃ]`, its right adjoint. For a *flat* sheaf `D` of
`Λ`-modules (`CategoryTheory.Abelian.PowExact`) the adjunction map

`Ext^n_{Λ'}(G, R^! D) ⟶ Ext^n_Λ(R G, D)`, `y ↦ R(y) ∘ ε_D`

is bijective for every sheaf `G` of `Λ'`-modules: the flat sheaves contain the injectives, are
stable under the cokernel of an injective presentation, and `R^!` keeps such a sequence short
exact (`Stacks.EtaleCohomology.shortExact_map_coextendScalars`), so the dimension shifting of
`Stacks.ExtAdjunction.extMap_bijective_of_acyclicClass` applies.

Together with the change of level on cohomology `Ext^n_{Λ'}(Λ', G) ≅ Ext^n_Λ(Λ, R G)`
(`Stacks.EtaleCohomology.LevelChange.extMap_bijective`), which is compatible with the Yoneda
product, this identifies the Yoneda pairing of `R G` in sheaves of `Λ`-modules,
`Ext^i_Λ(Λ, R G) × Ext^j_Λ(R G, D) → Ext^{i+j}_Λ(Λ, D)`, with the Yoneda pairing of `G` in
sheaves of `Λ'`-modules with dualizing object `R^! D`: Poincaré duality at a sheaf killed by `pᵃ`
may be checked with coefficients `ℤ/pᵃ` (`isDualityPerfect_restrict_iff`). This is the step from
duality with `ℤ/ℓ`-coefficients to duality with `ℤ/ℓⁿ`-coefficients, by dévissage of a flat
sheaf of `ℤ/ℓⁿ`-modules along `0 → ℓⁿ⁻¹ F → F → F/ℓⁿ⁻¹ F → 0`.

## Main results

* `Stacks.EtaleCohomology.LevelChange.extMap_coextendScalars_bijective`.
* `Stacks.EtaleCohomology.LevelChange.levelTrace`: the trace `z ↦ t(π ∘ R z ∘ ε_D)` on
  `Ext^N_{Λ'}(Λ', R^! D)` induced by a trace `t` on `Ext^N_Λ(Λ, D)`.
* `Stacks.EtaleCohomology.LevelChange.isDualityPerfect_restrict_iff`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.LevelChange

open ExtensionTorsor

variable {p : ℕ} [Fact p.Prime] {m : ℕ} (X : Scheme.{u}) {N : ℕ} (h : N ∣ p ^ m)

/-- Coextension of scalars along `ℤ/pᵐ ↠ ℤ/pᵃ`, `M ↦ Hom(ℤ/pᵃ, M) = M[pᵃ]`, the right adjoint of
`Stacks.EtaleCohomology.LevelChange.restrict`. -/
abbrev coextend : EtaleModules.{u, 0} (ZMod (p ^ m)) X ⥤ EtaleModules.{u, 0} (ZMod N) X :=
  etaleModuleCoextendScalars (ZMod.castHom h (ZMod N)) X

/-- `restrict ⊣ coextend`. -/
abbrev restrictCoextendAdj : restrict X h ⊣ coextend X h :=
  etaleModuleCoextendScalarsAdj (ZMod.castHom h (ZMod N)) X

/-- **`Ext^n_{ℤ/pᵃ}(G, D[pᵃ]) ≅ Ext^n_{ℤ/pᵐ}(R G, D)` for a flat sheaf `D` of `ℤ/pᵐ`-modules**:
the adjunction map `y ↦ R(y) ∘ ε_D` of `restrict ⊣ coextend` is bijective. -/
theorem extMap_coextendScalars_bijective {a : ℕ} (ha : a ≤ m) (hNa : N = p ^ a)
    (G : EtaleModules.{u, 0} (ZMod N) X) (D : EtaleModules.{u, 0} (ZMod (p ^ m)) X)
    (hD : PowExact p m D) (n : ℕ) :
    Function.Bijective (Stacks.ExtAdjunction.extMap (restrictCoextendAdj X h) G D n) :=
  Stacks.ExtAdjunction.extMap_bijective_of_acyclicClass (restrictCoextendAdj X h)
    (PowExact p m) (fun I _ => powExact_of_injective I)
    (fun S hS h₁ _ => ⟨PowExact.of_shortExact hS h₁ (powExact_of_injective S.X₂)
      (etaleModules_pow_nsmul_id _), shortExact_map_coextendScalars h ha hNa S hS h₁⟩) G D hD n

omit [Fact p.Prime] in
/-- The adjunction map of `restrict ⊣ coextend` is compatible with the Yoneda product:
`R(x ∘ y) ∘ ε = R x ∘ (R y ∘ ε)`. -/
theorem extMap_coextendScalars_comp {G G' : EtaleModules.{u, 0} (ZMod N) X}
    (D : EtaleModules.{u, 0} (ZMod (p ^ m)) X) {i j n : ℕ} (x : Ext G G' i)
    (y : Ext G' ((coextend X h).obj D) j) (hn : i + j = n) :
    Stacks.ExtAdjunction.extMap (restrictCoextendAdj X h) G D n (x.comp y hn) =
      (x.mapExactFunctor (restrict X h)).comp
        (Stacks.ExtAdjunction.extMap (restrictCoextendAdj X h) G' D j y) hn := by
  rw [Stacks.ExtAdjunction.extMap_apply, Stacks.ExtAdjunction.extMap_apply,
    Ext.mapExactFunctor_comp]
  exact Ext.comp_assoc _ _ _ hn (add_zero j) (by omega)

variable {A : Type*} [AddCommGroup A] {D : EtaleModules.{u, 0} (ZMod (p ^ m)) X} {n : ℕ}

/-- **The trace at level `pᵃ`** induced by a trace `t` on `Ext^n_{ℤ/pᵐ}(ℤ/pᵐ, D)`:
`z ↦ t (π ∘ R z ∘ ε_D)` on `Ext^n_{ℤ/pᵃ}(ℤ/pᵃ, D[pᵃ])`, with `π : ℤ/pᵐ ↠ R(ℤ/pᵃ)` the reduction
and `ε_D : R(D[pᵃ]) → D` the inclusion of the `pᵃ`-torsion. -/
def levelTrace (t : Ext (unitSheaf (X := X) (p ^ m)) D n →+ A) :
    Ext (unitSheaf (X := X) N) ((coextend X h).obj D) n →+ A :=
  t.comp ((((Ext.mk₀ (reduction X h)).precomp D (zero_add n))).comp
    (Stacks.ExtAdjunction.extMap (restrictCoextendAdj X h) (unitSheaf (X := X) N) D n))

omit [Fact p.Prime] in
/-- The level trace sends `z` to `t (π ∘ R z ∘ ε_D)`. -/
theorem levelTrace_apply (t : Ext (unitSheaf (X := X) (p ^ m)) D n →+ A)
    (z : Ext (unitSheaf (X := X) N) ((coextend X h).obj D) n) :
    levelTrace X h t z = t ((Ext.mk₀ (reduction X h)).comp
      (Stacks.ExtAdjunction.extMap (restrictCoextendAdj X h) (unitSheaf (X := X) N) D n z)
        (zero_add n)) :=
  rfl

omit [Fact p.Prime] in
/-- **The pairings correspond under the change of level.** For `x ∈ Ext^i_{ℤ/pᵃ}(ℤ/pᵃ, G)` and
`y ∈ Ext^j_{ℤ/pᵃ}(G, D[pᵃ])`, `levelTrace t (x ∘ y) = t (x♯ ∘ y♯)` with
`x♯ = π ∘ R x` and `y♯ = R y ∘ ε_D`. -/
theorem levelTrace_comp (t : Ext (unitSheaf (X := X) (p ^ m)) D n →+ A)
    (G : EtaleModules.{u, 0} (ZMod N) X) {i j : ℕ} (hn : i + j = n)
    (x : Ext (unitSheaf (X := X) N) G i) (y : Ext G ((coextend X h).obj D) j) :
    levelTrace X h t (x.comp y hn) = t ((extMap X h G i x).comp
      (Stacks.ExtAdjunction.extMap (restrictCoextendAdj X h) G D j y) hn) := by
  rw [levelTrace_apply, extMap_coextendScalars_comp, extMap_apply]
  congr 1
  exact (Ext.comp_assoc _ _ _ (zero_add i) hn (by omega)).symm

/-- **Duality at a sheaf killed by `pᵃ` may be checked with coefficients `ℤ/pᵃ`.** For a flat
sheaf `D` of `ℤ/pᵐ`-modules, a trace `t` on `Ext^n_{ℤ/pᵐ}(ℤ/pᵐ, D)` and a sheaf `G` of
`ℤ/pᵃ`-modules, duality holds at `R G` for `t` (in sheaves of `ℤ/pᵐ`-modules) if and only if it
holds at `G` for `levelTrace t` and the dualizing object `D[pᵃ]` (in sheaves of
`ℤ/pᵃ`-modules). -/
theorem isDualityPerfect_restrict_iff {a : ℕ} (ha : a ≤ m) (hNa : N = p ^ a) (hD : PowExact p m D)
    (t : Ext (unitSheaf (X := X) (p ^ m)) D n →+ A) (G : EtaleModules.{u, 0} (ZMod N) X) :
    Ext.IsDualityPerfect (unitSheaf (X := X) (p ^ m)) D n t ((restrict X h).obj G) ↔
      Ext.IsDualityPerfect (unitSheaf (X := X) N) ((coextend X h).obj D) n
        (levelTrace X h t) G := by
  have : NeZero (p ^ m) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  refine forall_congr' fun i => forall_congr' fun j => forall_congr' fun hn => ?_
  have hα := extMap_bijective X h G i
  let eβ := AddEquiv.ofBijective _ (extMap_coextendScalars_bijective X h ha hNa G D hD j)
  let pre : (Ext ((restrict X h).obj G) D j →+ A) ≃ (Ext G ((coextend X h).obj D) j →+ A) :=
    { toFun φ := φ.comp eβ.toAddMonoidHom
      invFun φ := φ.comp eβ.symm.toAddMonoidHom
      left_inv φ := by ext; simp
      right_inv φ := by ext; simp }
  have hcomp : (Ext.dualityPairing (unitSheaf (X := X) N) ((coextend X h).obj D) n
      (levelTrace X h t) G hn) =
      pre ∘ (Ext.dualityPairing (unitSheaf (X := X) (p ^ m)) D n t
        ((restrict X h).obj G) hn) ∘ extMap X h G i := by
    funext x
    ext y
    simp only [pre, Function.comp_apply, Equiv.coe_fn_mk, AddMonoidHom.comp_apply,
      Ext.dualityPairing_apply]
    exact levelTrace_comp X h t G hn x y
  rw [hcomp, Function.Bijective.of_comp_iff' pre.bijective, Function.Bijective.of_comp_iff _ hα]

end Stacks.EtaleCohomology.LevelChange

end
