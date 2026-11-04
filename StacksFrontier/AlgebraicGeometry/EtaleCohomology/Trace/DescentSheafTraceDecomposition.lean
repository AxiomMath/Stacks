module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseCurveTraceVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalTraceBoundedComplex
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalFrobeniusAdditivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.DescentSheafExactness

/-!
# Splitting a descent sheaf along a central idempotent

Let `G : V ⟶ X` be a Galois covering with group `H`, `Λ` a ring, `M` a `Λ`-module with an action
`ρ` of `H`, and `e` a central idempotent of `Λ`. Then `M = eM ⊕ (1 - e)M` as `Λ[H]`-modules, and
the descent sheaf splits accordingly: `0 → D(eM) → D(M) → D((1 - e)M) → 0` is split exact
(`AlgebraicGeometry.EtaleGaloisCovering.descentSheafSplitting`). Hence the trace of `π^*` on
`RΓ_c(X_k̄, D(M))` is the sum of the traces on the two summands. This is the primary
decomposition of the coefficients in Step 3 of the proof of [Stacks, Tag 03UG].

## Main definitions

* `AlgebraicGeometry.EtaleGaloisCovering.descentSheafShortComplex`: the short complex
  `D(eM) → D(M) → D((1 - e)M)`.
* `AlgebraicGeometry.EtaleGaloisCovering.descentSheafSplitting`: its splitting.

## Main results

* `AlgebraicGeometry.EtaleGaloisCovering.descentSheafShortComplex_shortExact`: the short complex
  `0 → D(eM) → D(M) → D((1 - e)M) → 0` is short exact.
* `Stacks.EtaleCohomology.canonicalCompactSupportLefschetzNumber_descentSheaf_eq_add`: the trace
  of `π^*` on `RΓ_c(U_k̄, D(M))` is the sum of the traces on `D(eM)` and `D((1 - e)M)`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 3.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.EtaleGaloisCovering

variable {X : Scheme.{u}} {H : Type} [Group H] (G : EtaleGaloisCovering X H) {Λ : Type} [Ring Λ]

section Map

variable {M M' M'' : Type (u + 1)} [AddCommGroup M] [Module Λ M] [AddCommGroup M'] [Module Λ M']
  [AddCommGroup M''] [Module Λ M''] {ρ : H →* Module.End Λ M} {ρ' : H →* Module.End Λ M'}
  {ρ'' : H →* Module.End Λ M''}

/-- On sections, the map of descent sheaves induced by an equivariant `f` is composition with
`f`. -/
lemma descentSheafMap_app (f : M →ₗ[Λ] M') (hf : ∀ h x, f (ρ h x) = ρ' h (f x)) (W : X.Etaleᵒᵖ)
    (c : (G.descentPresheaf Λ M ρ).obj W) (z : G.fiberProd W.unop) :
    (((G.descentSheafMap f hf).hom.app W).hom c).1 z = f (c.1 z) := rfl

/-- Two morphisms of descent sheaves are equal if they agree on every section at every point of
the fibre product. -/
lemma descentSheaf_hom_ext {φ ψ : G.descentSheaf.{u, 0, 0, u + 1} Λ M ρ ⟶
      G.descentSheaf.{u, 0, 0, u + 1} Λ M' ρ'}
    (h : ∀ W c z, ((φ.hom.app W).hom c).1 z = ((ψ.hom.app W).hom c).1 z) : φ = ψ := by
  apply Sheaf.hom_ext
  ext W c
  exact Subtype.ext (LocallyConstant.ext (h W c))

/-- The identity of `M` induces the identity of `D(M)`. -/
lemma descentSheafMap_id :
    G.descentSheafMap (ρ₁ := ρ) LinearMap.id (fun _ _ => rfl) = 𝟙 _ :=
  G.descentSheaf_hom_ext fun _ _ _ => rfl

/-- The map of descent sheaves induced by `f + g` is the sum of those induced by `f` and `g`. -/
lemma descentSheafMap_add (f g : M →ₗ[Λ] M') (hf : ∀ h x, f (ρ h x) = ρ' h (f x))
    (hg : ∀ h x, g (ρ h x) = ρ' h (g x)) :
    G.descentSheafMap f hf + G.descentSheafMap g hg =
      G.descentSheafMap (f + g) (fun h x => by simp [hf, hg]) :=
  G.descentSheaf_hom_ext fun _ _ _ => rfl

/-- The zero map induces the zero map of descent sheaves. -/
lemma descentSheafMap_eq_zero (f : M →ₗ[Λ] M') (hf : ∀ h x, f (ρ h x) = ρ' h (f x))
    (h0 : f = 0) : G.descentSheafMap f hf = 0 := by
  subst h0
  exact G.descentSheaf_hom_ext fun _ _ _ => rfl

/-- Equal equivariant maps induce equal maps of descent sheaves. -/
lemma descentSheafMap_congr {f g : M →ₗ[Λ] M'} (hf : ∀ h x, f (ρ h x) = ρ' h (f x))
    (hfg : f = g) :
    G.descentSheafMap f hf = G.descentSheafMap g (hfg ▸ hf) := by
  subst hfg
  rfl

end Map

section Idempotent

variable {M : Type (u + 1)} [AddCommGroup M] [Module Λ M] (ρ : H →* Module.End Λ M)
  (e : Λ) (hc : ∀ a : Λ, a * e = e * a) (he : IsIdempotentElem e)

/-- Multiplication by the central element `e`, as a `Λ`-linear endomorphism. -/
def eMul : M →ₗ[Λ] M where
  toFun x := e • x
  map_add' := smul_add e
  map_smul' a x := by
    change e • a • x = a • e • x
    rw [smul_smul, smul_smul, hc a]

/-- `eMul e hc` sends `x` to `e • x`. -/
lemma eMul_apply (x : M) : eMul e hc x = e • x := rfl

/-- Multiplication by `e` commutes with the action of `H`. -/
lemma rho_eMul (h : H) (x : M) : ρ h (eMul e hc x) = eMul e hc (ρ h x) :=
  (ρ h).map_smul e x

/-- The summand `eM = {x | e x = x}`. -/
abbrev fixPart : Submodule Λ M := LinearMap.ker (LinearMap.id - eMul e hc)

/-- The summand `(1 - e)M = {x | e x = 0}`. -/
abbrev killPart : Submodule Λ M := LinearMap.ker (eMul e hc)

/-- `x` lies in `eM` if and only if `e • x = x`. -/
lemma mem_fixPart {x : M} : x ∈ fixPart e hc ↔ e • x = x := by
  simp [eMul_apply, sub_eq_zero, eq_comm]

/-- `x` lies in `(1 - e)M` if and only if `e • x = 0`. -/
lemma mem_killPart {x : M} : x ∈ killPart e hc ↔ e • x = 0 := Iff.rfl

/-- The action of `H` on `eM`. -/
def fixRep : H →* Module.End Λ (fixPart (M := M) e hc) where
  toFun h := (ρ h).restrict fun x hx => by
    rw [mem_fixPart] at hx ⊢
    rw [← (ρ h).map_smul, hx]
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

/-- The action of `H` on `(1 - e)M`. -/
def killRep : H →* Module.End Λ (killPart (M := M) e hc) where
  toFun h := (ρ h).restrict fun x hx => by
    rw [mem_killPart] at hx ⊢
    rw [← (ρ h).map_smul, hx, map_zero]
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

/-- The action of `H` on `eM` is the restriction of `ρ`. -/
lemma fixRep_apply_coe (h : H) (x : fixPart (M := M) e hc) :
    ((fixRep ρ e hc h x : fixPart (M := M) e hc) : M) = ρ h x := rfl

/-- The action of `H` on `(1 - e)M` is the restriction of `ρ`. -/
lemma killRep_apply_coe (h : H) (x : killPart (M := M) e hc) :
    ((killRep ρ e hc h x : killPart (M := M) e hc) : M) = ρ h x := rfl

include he

/-- The projection `M → eM`, `x ↦ e x`. -/
def fixProj : M →ₗ[Λ] fixPart (M := M) e hc :=
  (eMul e hc).codRestrict _ fun x => by
    rw [mem_fixPart, eMul_apply, smul_smul, he.eq]

/-- The projection `M → (1 - e)M`, `x ↦ x - e x`. -/
def killProj : M →ₗ[Λ] killPart (M := M) e hc :=
  (LinearMap.id - eMul e hc).codRestrict _ fun x => by
    rw [mem_killPart]
    simp [eMul_apply, smul_sub, smul_smul, he.eq]

/-- The projection `M → eM` sends `x` to `e • x`. -/
lemma fixProj_apply (x : M) : (fixProj e hc he x : M) = e • x := rfl

/-- The projection `M → (1 - e)M` sends `x` to `x - e • x`. -/
lemma killProj_apply (x : M) : (killProj e hc he x : M) = x - e • x := rfl

/-- **The short complex `D(eM) → D(M) → D((1 - e)M)`.** -/
def descentSheafShortComplex : ShortComplex (Stacks.EtaleCohomology.EtaleModules.{u, 0} Λ X) where
  X₁ := G.descentSheaf.{u, 0, 0, u + 1} Λ (fixPart (M := M) e hc) (fixRep ρ e hc)
  X₂ := G.descentSheaf.{u, 0, 0, u + 1} Λ M ρ
  X₃ := G.descentSheaf.{u, 0, 0, u + 1} Λ (killPart (M := M) e hc) (killRep ρ e hc)
  f := G.descentSheafMap (ρ₁ := fixRep ρ e hc) (ρ₂ := ρ) (fixPart e hc).subtype
    (fixRep_apply_coe ρ e hc)
  g := G.descentSheafMap (ρ₁ := ρ) (ρ₂ := killRep ρ e hc) (killProj e hc he) fun h x =>
    Subtype.ext (by
    change ρ h x - e • ρ h x = ρ h (x - e • x)
    rw [map_sub, (ρ h).map_smul])
  zero := G.descentSheaf_hom_ext fun W c z => Subtype.ext (by
    change ((c.1 z : fixPart (M := M) e hc) : M) - e • ((c.1 z : fixPart (M := M) e hc) : M) = 0
    rw [(mem_fixPart e hc).1 (c.1 z).2, sub_self])

/-- The splitting of `D(eM) → D(M) → D((1 - e)M)`. -/
def descentSheafSplitting : (G.descentSheafShortComplex ρ e hc he).Splitting where
  r := G.descentSheafMap (ρ₁ := ρ) (ρ₂ := fixRep ρ e hc) (fixProj e hc he) fun h x =>
    Subtype.ext ((ρ h).map_smul e x).symm
  s := G.descentSheafMap (ρ₁ := killRep ρ e hc) (ρ₂ := ρ) (killPart e hc).subtype
    (killRep_apply_coe ρ e hc)
  f_r := G.descentSheaf_hom_ext fun W c z => Subtype.ext ((mem_fixPart e hc).1 (c.1 z).2)
  s_g := G.descentSheaf_hom_ext fun W c z => Subtype.ext ((by
      rw [(mem_killPart e hc).1 (c.1 z).2, sub_zero] :
      ((c.1 z : killPart (M := M) e hc) : M) - e • ((c.1 z : killPart (M := M) e hc) : M) =
        (c.1 z : M)))
  id := G.descentSheaf_hom_ext fun W c z =>
    (by abel : (e • c.1 z + (c.1 z - e • c.1 z) : M) = c.1 z)

/-- The short complex `0 → D(eM) → D(M) → D((1 - e)M) → 0` is short exact. -/
lemma descentSheafShortComplex_shortExact :
    (G.descentSheafShortComplex ρ e hc he).ShortExact :=
  (G.descentSheafSplitting ρ e hc he).shortExact

end Idempotent

end AlgebraicGeometry.EtaleGaloisCovering

namespace Stacks.EtaleCohomology

open AlgebraicGeometry.EtaleGaloisCovering

variable {k : Type u} [Field k] [Fintype k] {U : Scheme.{u}} {pU : U ⟶ Spec (.of k)}
  (J : CompactificationOf (Over.mk pU))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q) {Λ : Type} [Ring Λ] [Finite Λ]
  {H : Type} [Group H] (G : EtaleGaloisCovering U H)
  {M : Type (u + 1)} [AddCommGroup M] [Module Λ M] (ρ : H →* Module.End Λ M)
  (e : Λ) (hc : ∀ a : Λ, a * e = e * a) (he : IsIdempotentElem e)

include he in
/-- **The trace of `π^*` on `RΓ_c(U_k̄, D(M))` is the sum of the traces on `D(eM)` and
`D((1 - e)M)`**, for a central idempotent `e`, granted perfectness of the two summands. -/
theorem canonicalCompactSupportLefschetzNumber_descentSheaf_eq_add
    (h₁ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ pU J kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          (G.descentSheaf.{u, 0, 0, u + 1} Λ (fixPart (M := M) e hc) (fixRep ρ e hc))))))
    (h₃ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ pU J kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          (G.descentSheaf.{u, 0, 0, u + 1} Λ (killPart (M := M) e hc) (killRep ρ e hc)))))) :
    ∃ h₂ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} Λ pU J kbar
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            (G.descentSheaf.{u, 0, 0, u + 1} Λ M ρ)))),
      canonicalCompactSupportLefschetzNumber.{u, 0} Λ pU J kbar p q hcard
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            (G.descentSheaf.{u, 0, 0, u + 1} Λ M ρ)) h₂ =
        canonicalCompactSupportLefschetzNumber.{u, 0} Λ pU J kbar p q hcard
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            (G.descentSheaf.{u, 0, 0, u + 1} Λ (fixPart (M := M) e hc) (fixRep ρ e hc))) h₁ +
        canonicalCompactSupportLefschetzNumber.{u, 0} Λ pU J kbar p q hcard
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            (G.descentSheaf.{u, 0, 0, u + 1} Λ (killPart (M := M) e hc) (killRep ρ e hc))) h₃ := by
  let S := (G.descentSheafShortComplex ρ e hc he).map
    (HomologicalComplex.single (EtaleModules.{u, 0} Λ U) (ComplexShape.up ℤ) 0)
  have hS : S.ShortExact :=
    ((G.descentSheafSplitting ρ e hc he).map
      (HomologicalComplex.single (EtaleModules.{u, 0} Λ U) (ComplexShape.up ℤ) 0)).shortExact
  have p₁ : CochainComplex.plus _ S.X₁ :=
    ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
      (G.descentSheaf.{u, 0, 0, u + 1} Λ (fixPart (M := M) e hc) (fixRep ρ e hc))).property
  have p₂ : CochainComplex.plus _ S.X₂ :=
    ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
      (G.descentSheaf.{u, 0, 0, u + 1} Λ M ρ)).property
  have p₃ : CochainComplex.plus _ S.X₃ :=
    ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
      (G.descentSheaf.{u, 0, 0, u + 1} Λ (killPart (M := M) e hc) (killRep ρ e hc))).property
  have h₂ := isPerfect_compactSupportFrobeniusCohomology_X₂ Λ pU J kbar hS p₁ p₂ p₃ h₁ h₃
  exact ⟨h₂, canonicalCompactSupportLefschetzNumber_X₂_eq_add Λ pU J kbar p q hcard hS p₁ p₂ p₃
    h₁ h₂ h₃⟩

end Stacks.EtaleCohomology

end
