module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineDiffSectionsEquiv
public import StacksFrontier.AlgebraicGeometry.Crystalline.StructureSheafConnection

/-!
# The two spellings of `Ω` over an affine object of `CRIS(X/S)` agree

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF] and an object
`A = (U, T, δ)` of `CRIS(X/S)`.  The library carries two modules of one-forms over `A`, and they
are not the same object:

* the sections `Crystalline.GlobalCrystallineSituation.crysDiffSections A = Γ(T, Ω_{T/S,δ})` of
  the **sheaf** of divided power differentials of [Stacks, Tag 07IY].  This is the module in
  which the canonical connection of [Stacks, Tag 07J6] takes its values
  (`Crystalline.GlobalCrystallineSituation.crystalConnectionTensor`) and out of which the
  universal thickenings of [Stacks, Tag 07J2] and [Stacks, Tag 07J3] are built.
* the sections `(Crystalline.GlobalCrystallineSituation.crysDifferentials S).obj (op A)` of the
  **presheaf** `Ω_{X/S}` of [Stacks, Tag 07IX].  This is the module the de Rham complex of
  [Stacks, Tag 07J4] and the ring-level `Crystalline.Connection` of [Stacks, Tag 07I0] are stated
  over, through the presentation `Crystalline.GlobalCrystallineSituation.crysPi`.

`Crystalline.GlobalCrystallineSituation.restrictedToSheaf` is only a morphism from the second to
the first, and the implementation notes of
`StacksFrontier/AlgebraicGeometry/Crystalline/StructureSheafConnection.lean` record this mismatch as
the one thing standing between the ring-level connection machinery and the crystalline
connection of a general crystal.

**When the ambient scheme `T` is affine and lies over an affine open `V` of the divided power
base the two agree**, and this module says so: both are identified with the algebraic divided
power differentials `Ω¹_{Γ(T,𝒪_T)/Γ(V,𝒪_S),δ}` of the section ring — the sheaf's sections by
`Crystalline.GlobalCrystallineSituation.affineCrysDiffSectionsEquiv`, which is
[Stacks, Tag 07IY] clause (2), and the presheaf's by
`Crystalline.GlobalCrystallineSituation.affineCrysDifferentialsIso`, which is
[Stacks, Tag 07J0] — and the two identifications both carry the universal divided power
derivation to the universal divided power differential, so their composite carries
`d_{T/S,δ}` to `d_{X/S}`.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation`.

* `affineCrysDiffSectionsObjEquiv` — **`Γ(T, Ω_{T/S,δ}) ≅ Ω_{X/S}(U, T, δ)` for an object with
  affine ambient scheme lying over an affine open of the base**, over the ring
  `Γ(T, 𝒪_T)`.
* `affineCrysOmegaEquiv` — the same identification with its two sides spelled as the connection
  machinery spells them: a `crysFormRing S A`-linear equivalence onto
  `(crysDifferentials S).obj (op A)`.

## Main results

* `affineCrysDiffSectionsObjEquiv_crysDerivation` and `affineCrysOmegaEquiv_crysDerivation` —
  **the identification carries `d_{T/S,δ} b` to `d_{X/S} b`.**
* `affineCrysOmegaEquiv_symm_crysD` — and back.
* `affineCrysOmegaEquiv_crysPi_D` — the identification carries `d_{T/S,δ} b` to the image of the
  universal Kähler differential under the presentation `crysPi`, which is the shape the Leibniz
  rule of `Crystalline.Connection` asks for.

## Implementation notes

Two retypings are paid for once here, in the manner the implementation notes of
`StacksFrontier/AlgebraicGeometry/Crystalline/AffineObjectDifferentialForms.lean` record for this
area.

* The ring of sections of `𝒪_{X/S}` over an object has two names,
  `Crystalline.GlobalCrystallineSituation.crysSheafRing` (through the sheaf of rings
  `crystallineStructureSheaf`) and `crysFormRing` (through the presheaf of rings
  `structureRingCatPresheaf`).  Both unfold to `Γ(T, 𝒪_T)` and the two are equal by `rfl`, but
  they are different `DiscrTree` keys, so a `Module` instance registered at one is invisible at
  the other.  `moduleFormRingDiffSections` and `moduleFormRingSheafSections` register the two
  actions that the connection of [Stacks, Tag 07J6] needs at the `crysFormRing` spelling.
* For the same reason `LinearEquiv.trans` cannot bridge the two spellings inside unification —
  it asks for a `RingHomCompTriple` between the identity ring homomorphisms of two different
  terms — so `affineCrysDiffSectionsObjEquiv` is built at the `Γ(T, 𝒪_T)` spelling and
  `affineCrysOmegaEquiv` is a definition whose body is that term, retyped.

## References

* [Stacks Project, Tag 07IX](https://stacks.math.columbia.edu/tag/07IX)
* [Stacks Project, Tag 07IY](https://stacks.math.columbia.edu/tag/07IY)
* [Stacks Project, Tag 07IZ](https://stacks.math.columbia.edu/tag/07IZ)
* [Stacks Project, Tag 07J0](https://stacks.math.columbia.edu/tag/07J0)
* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

/-! ### The two spellings of the ring of sections -/

/-- The sections of `Ω_{T/S,δ}` over the ambient scheme of an object, as a module over the
sections of `𝒪_{X/S}` there in the `crysFormRing` spelling.  The two rings of scalars are both
`Γ(T, 𝒪_T)`. -/
instance moduleFormRingDiffSections (A : Thickening S) :
    Module (crysFormRing S A) (crysDiffSections A) :=
  inferInstanceAs (Module Γ(A.thickening.target.scheme, ⊤) (crysDiffSections A))

/-- The sections of a sheaf of `𝒪_{X/S}`-modules over an object, as a module over the sections of
`𝒪_{X/S}` there in the `crysFormRing` spelling. -/
instance moduleFormRingSheafSections (M : SheafOfModules.{u} (crystallineStructureSheaf S))
    (A : Thickening S) : Module (crysFormRing S A) (M.val.obj (op A)) :=
  inferInstanceAs (Module (crysSheafRing S A) (M.val.obj (op A)))

/-! ### The identification of the sheaf sections with the presheaf sections -/

variable (A : Thickening S) [IsAffine A.thickening.target.scheme] {V : S.S.scheme.Opens}
  (hVA : (⊤ : A.thickening.target.scheme.Opens) ≤ A.toBase.hom ⁻¹ᵁ V) (hV : IsAffineOpen V)

/-- **The sections of the sheaf `Ω_{T/S,δ}` over the ambient scheme of an affine object are the
sections of the presheaf `Ω_{X/S}` over the object.**

Both are the algebraic divided power differentials `Ω¹_{Γ(T,𝒪_T)/Γ(V,𝒪_S),δ}` of the section
ring: the left-hand side by `Crystalline.GlobalCrystallineSituation.affineCrysDiffSectionsEquiv`,
which is [Stacks, Tag 07IY] clause (2) read at the top open, and the right-hand side by
`Crystalline.GlobalCrystallineSituation.affineCrysDifferentialsIso`, which is
[Stacks, Tag 07J0]. -/
def affineCrysDiffSectionsObjEquiv :
    crysDiffSections A ≃ₗ[Γ(A.thickening.target.scheme, ⊤)] ↥(crysDifferentialsObj S A) :=
  (affineCrysDiffSectionsEquiv A hVA hV).trans
    (affineCrysDifferentialsIso S A hVA hV).toLinearEquiv.symm

/-- **The identification carries the universal divided power derivation `d_{T/S,δ}` of the
ambient scheme to the universal `S`-derivation `d_{X/S}` of the site.**  Both identifications it
is composed of carry the respective universal differential to the universal divided power
differential of the section ring. -/
theorem affineCrysDiffSectionsObjEquiv_crysDerivation (b : Γ(A.thickening.target.scheme, ⊤)) :
    affineCrysDiffSectionsObjEquiv A hVA hV (crysDerivation A b) =
      (crysDifferentialsD S A).d b := by
  change (affineCrysDifferentialsIso S A hVA hV).toLinearEquiv.symm
      (affineCrysDiffSectionsEquiv A hVA hV (crysDerivation A b)) = _
  rw [affineCrysDiffSectionsEquiv_crysDerivation]
  exact affineCrysDifferentialsIso_inv_dpd S A hVA hV b

/-- The identification read backwards on the universal `S`-derivation. -/
theorem affineCrysDiffSectionsObjEquiv_symm_d (b : Γ(A.thickening.target.scheme, ⊤)) :
    (affineCrysDiffSectionsObjEquiv A hVA hV).symm ((crysDifferentialsD S A).d b) =
      crysDerivation A b :=
  (affineCrysDiffSectionsObjEquiv A hVA hV).injective
    ((affineCrysDiffSectionsObjEquiv A hVA hV).apply_symm_apply _ |>.trans
      (affineCrysDiffSectionsObjEquiv_crysDerivation A hVA hV b).symm)

/-! ### The identification in the spelling of the connection machinery -/

/-- **The identification of `Γ(T, Ω_{T/S,δ})` with `Ω_{X/S}(U, T, δ)`, retyped**: the ring of
scalars is written `Crystalline.GlobalCrystallineSituation.crysFormRing` and the target is the
value of the presheaf of modules `Ω_{X/S}`, which is the spelling the presentation
`Crystalline.GlobalCrystallineSituation.crysPi` and the ring-level `Crystalline.Connection` of
[Stacks, Tag 07I0] use.  Its body is `affineCrysDiffSectionsObjEquiv`; see the implementation
notes for why the retyping is a separate definition. -/
def affineCrysOmegaEquiv :
    crysDiffSections A ≃ₗ[crysFormRing S A] ↥((crysDifferentials S).obj (op A)) :=
  affineCrysDiffSectionsObjEquiv A hVA hV

/-- **The retyped identification carries `d_{T/S,δ} b` to `d_{X/S} b`.** -/
theorem affineCrysOmegaEquiv_crysDerivation (b : crysFormRing S A) :
    affineCrysOmegaEquiv A hVA hV (crysDerivation A b) = crysD S A b :=
  affineCrysDiffSectionsObjEquiv_crysDerivation A hVA hV b

/-- The retyped identification read backwards on `d_{X/S} b`. -/
theorem affineCrysOmegaEquiv_symm_crysD (b : crysFormRing S A) :
    (affineCrysOmegaEquiv A hVA hV).symm (crysD S A b) = crysDerivation A b :=
  affineCrysDiffSectionsObjEquiv_symm_d A hVA hV b

/-- **The retyped identification carries `d_{T/S,δ} b` to the image of the universal Kähler
differential of `b` under the presentation of [Stacks, Tag 07HY].**  This is the shape in which
the Leibniz rule of `Crystalline.Connection` asks for the differential term. -/
theorem affineCrysOmegaEquiv_crysPi_D (b : crysFormRing S A) :
    affineCrysOmegaEquiv A hVA hV (crysDerivation A b) =
      crysPi S A (KaehlerDifferential.D ↥Γ(S.S.scheme, ⊤) (crysFormRing S A) b) :=
  affineCrysOmegaEquiv_crysDerivation A hVA hV b

end Crystalline.GlobalCrystallineSituation

end
