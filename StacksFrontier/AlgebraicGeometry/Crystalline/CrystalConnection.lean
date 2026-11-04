module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.DeRhamComplex
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.Connection

/-!
# The Leibniz rule for the crystalline de Rham differential

Fix a global crystalline situation `(p, (S, I, γ), X)`.  The de Rham complex
`𝒪_{X/S} → Ω¹_{X/S} → Ω²_{X/S} → ⋯` of [Stacks, Tag 07J4] is recorded in
`Crystalline.GlobalCrystallineSituation.crysDeRhamComplex` by four properties of its degreewise
differential: additivity, linearity over the global sections of the divided power base, the
formula `d (b₀ · d b₁ ∧ ⋯ ∧ d b_i) = d b₀ ∧ ⋯ ∧ d b_i` on the standard generators, naturality in
the object of the site, and the square-zero property.  Linearity over `𝒪_{X/S}` itself is false,
and what replaces it is the Leibniz rule

`d (c · ω) = c · d ω + d c ∧ ω`

for a section `c` of `𝒪_{X/S}` and a form `ω` of degree `i` over an object of `CRIS(X/S)`.  This
file proves that rule.  It is not one of the fields of
`Crystalline.GlobalCrystallineSituation.CrysDeRhamComplex`, and the complex is obtained by a
choice, so it has to be recovered from the fields that are recorded; the standard generators span
each exterior power already over the base ring, so the rule follows from the generator formula and
the ring-level Leibniz rule for the universal `S`-derivation `d_{X/S}`.

## Main results

* `Crystalline.GlobalCrystallineSituation.CrysDeRhamComplex.differential_smul` — the Leibniz rule
  for the degreewise de Rham differential on `CRIS(X/S)`.

## What is and is not proved

[Stacks, Tag 07J6] itself — a crystal on the small site `Cris(X/S)` has a canonical integrable
connection — is formalized, with no quasi-coherence hypothesis, in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CrystalIntegrableConnectionCris.lean`,
in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`: the connection
`crystalConnectionCris : F ⟶ F ⊗ Ω_{X/S}`, a morphism of abelian sheaves on `Cris(X/S)`, and the
theorem `crystalConnectionCris_isIntegrableConnection` (from `crystalConnectionCris_isConnection`
and `crystalConnectionCris_isIntegrable`) that it satisfies the Leibniz rule, is the canonical
`p₁^* s - p₀^* s` on every object, and is integrable; those two declarations carry the tag.  This
module is about the big site `CRIS(X/S)` and carries no attribute for that tag.

* [Stacks, Tag 07J6] — **proved on the small site as just said; no `stacks` attribute for it is
  placed in this file.**  Tag 07J6 says that a crystal in `𝒪_{X/S}`-modules on `Cris(X/S)` comes
  equipped with a *canonical* integrable connection, the connection being built from the
  comparison isomorphisms of the crystal along the two projections of the first-order universal
  thickening `(U, T', δ')` of [Stacks, Tag 07J2], and integrability being read off the cocycle
  condition on the second-order thickening `(U, T'', δ'')` of [Stacks, Tag 07J3].  That
  construction is carried out, for an arbitrary crystal, in
  `StacksFrontier/AlgebraicGeometry/Crystalline/CrystalConnectionGeneral.lean`, which builds
  `Crystalline.GlobalCrystallineSituation.crystalConnection` out of
  `Crystalline.GlobalCrystallineSituation.firstOrderThickeningObject`, the thickening
  `(U, T', δ')` as an object of the site; what remains open there is the identification of the
  ideal of the diagonal `i : T ⟶ T'` with `F_T ⊗_{𝒪_T} Ω_{T/S,δ}`, and with it integrability.
  The Leibniz rule proved here is the identity that the connection of 07J6 is required to satisfy,
  in the one case where the connection is known as a `Crystalline.Connection` into a tensor
  product, namely `F = 𝒪_{X/S}` with `∇ = d_{X/S}`; the connection built in the module above lands
  in the ideal of the diagonal instead, and the differential it produces for `F = 𝒪_{X/S}` is the
  universal derivation into the *sheaf* `Ω_{T/S,δ}`
  (`Crystalline.GlobalCrystallineSituation.crystalConnection_unit`), not into the presheaf
  `Ω_{X/S}` of [Stacks, Tag 07IX] in which the de Rham complex below is written.  So neither file
  identifies the connection of this file with the canonical one of 07J6, and the results below
  carry no 07J6 attribute.

## References

* [Stacks Project, Tag 07J4](https://stacks.math.columbia.edu/tag/07J4)
* [Stacks Project, Tag 07J5](https://stacks.math.columbia.edu/tag/07J5)
* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u})

/-- A section of `𝒪_{X/S}` multiplied into a standard generator is the standard generator of the
tuple whose leading entry has been multiplied by it. -/
theorem smul_crysGen (A : Thickening S) (i : ℕ) (c : crysFormRing S A)
    (b : Fin (i + 1) → crysFormRing S A) :
    c • crysGen S A i b = crysGen S A i (Fin.cons (c * b 0) (fun j ↦ b j.succ)) := by
  simp only [crysGen, Fin.cons_zero, Fin.cons_succ]
  exact smul_smul c (b 0) _

/-- **The Leibniz rule for the universal `S`-derivation `d_{X/S}`**, at the spelling
`Crystalline.GlobalCrystallineSituation.crysD` of the differential. -/
theorem crysD_mul (A : Thickening S) (x y : crysFormRing S A) :
    crysD S A (x * y) = x • crysD S A y + y • crysD S A x :=
  (crysSDerivation S).leibniz A x y

/-- **The Leibniz rule for the crystalline de Rham differential.**  Over an object of `CRIS(X/S)`
the differential of `c · ω` is `c · d ω + d c ∧ ω`; it is this identity, and not
`𝒪_{X/S}`-linearity, that the differential satisfies. -/
theorem CrysDeRhamComplex.differential_smul (C : CrysDeRhamComplex S) (i : ℕ) (A : Thickening S)
    (c : crysFormRing S A)
    (ω : ⋀[crysFormRing S A]^i ((crysDifferentials S).obj (op A))) :
    C.differential i A (c • ω) =
      c • C.differential i A ω + leftWedge i (crysD S A c) ω := by
  have hmem : ω ∈ Submodule.span ↥Γ(S.S.scheme, ⊤) (Set.range (crysGen S A i)) := by
    rw [crysGen_span]
    exact Submodule.mem_top
  induction hmem using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      rw [smul_crysGen, C.differential_generator, C.differential_generator]
      apply Subtype.ext
      rw [Submodule.coe_add, Submodule.coe_smul, leftWedge_coe, coe_ιMulti_succ,
        coe_ιMulti_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, crysGen, Submodule.coe_smul]
      rw [crysD_mul, map_add, map_smul, map_smul, add_mul, smul_mul_assoc, smul_mul_assoc,
        mul_smul_comm]
  | zero => simp only [smul_zero, map_zero, add_zero]
  | add x y _ _ ihx ihy =>
      rw [smul_add, map_add, ihx, ihy, map_add, smul_add, map_add]
      abel
  | smul a x _ ih =>
      have ha : (a • x : ⋀[crysFormRing S A]^i ((crysDifferentials S).obj (op A))) =
          crysBase S A a • x := (algebraMap_smul (crysFormRing S A) a x).symm
      rw [ha]
      rw [smul_comm c (crysBase S A a) x]
      rw [C.differential_base_smul]
      rw [ih]
      rw [smul_add]
      rw [C.differential_base_smul]
      simp only [map_smul]
      congr 1
      exact smul_comm _ _ _

end Crystalline.GlobalCrystallineSituation

end

end
