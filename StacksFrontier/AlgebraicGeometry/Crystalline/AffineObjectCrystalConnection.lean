module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineObjectSheafSectionsIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderIdealAffineIntegrable

/-!
# The canonical connection of a crystal as a ring-level connection, on an affine object

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], let `M` be a
locally quasi-coherent sheaf crystal in `𝒪_{X/S}`-modules and let `A = (U, T, δ)` be an object of
`CRIS(X/S)` whose ambient divided power scheme `T` is **affine**.  Write `D = Γ(T, 𝒪_T)`,
`Ω = Ω_{X/S}(U, T, δ)` and `M(A) = M(U, T, δ)`.

This module turns the crystalline connection of
`Crystalline.GlobalCrystallineSituation.crystalConnectionTensor` — the difference
`∇(s) = p₁^* s - p₀^* s` of [Stacks, Tag 07J6], read inside `Γ(T, Ω_{T/S,δ}) ⊗_D M(A)` — into a
term of the ring-level structure `Crystalline.Connection` of [Stacks, Tag 07I0], relative to the
presentation `Crystalline.GlobalCrystallineSituation.crysPi` of `Ω` as a quotient of the Kähler
differentials of `D` over `Γ(S, 𝒪_S)`.

Two things have to be reconciled, and both are reconciled here.

* **The order of the tensor factors.**  `crystalConnectionTensor` lands in `Ω ⊗_D M(A)` and
  `Crystalline.Connection` asks for `M(A) ⊗_D Ω`; `TensorProduct.comm` is the bridge, packaged
  with the next item as `affineCrysTensorFlip`.
* **The two spellings of `Ω`.**  `crystalConnectionTensor` is valued in the sections of the
  *sheaf* `Ω_{T/S,δ}` and `crysPi` presents the sections of the *presheaf* `Ω_{X/S}`.  On an
  affine object these agree, by
  `Crystalline.GlobalCrystallineSituation.affineCrysOmegaEquiv` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/AffineObjectSheafSectionsIso.lean`.

The payoff is that the whole of the ring-level de Rham machinery becomes available at a crystal:
the connection extends to all the exterior powers `M(A) ⊗_D ⋀^p Ω` in every degree, by
`Crystalline.extendedConnection`, with the formula `d(m ⊗ ω) = ∇(m) ∧ ω + m ⊗ d ω` of
[Stacks, Section 60.15, Tag 07J5] on pure tensors.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation`.

* `affineCrysTensorFlip` — the identification `Γ(T, Ω_{T/S,δ}) ⊗_D M(A) ≅ M(A) ⊗_D Ω` of the two
  readings of the target of the connection.
* `affineCrystalConnectionOf` — **the canonical connection of [Stacks, Tag 07J6] as a term of
  `Crystalline.Connection`**, from a degree-one identification datum
  `Crystalline.GlobalCrystallineSituation.FirstOrderIdealBaseChange`.
* `affineCrystalConnection` — **the same connection with the datum discharged from the crystal
  condition**, for a sheaf crystal on an affine object with quasi-coherent `M_T`.

## Main results

* `affineCrysTensorFlip_tmul` — the identification on a pure tensor.
* `affineCrystalConnectionOf_apply` and `affineCrystalConnection_apply` — the value of the
  connection: the crystalline connection read through the identification.
* `affineCrystalConnection_leibniz` — **the Leibniz rule of [Stacks, Tag 07I0]**,
  `∇(b s) = b ∇(s) + s ⊗ π(d b)`, which is the defining property of the structure and is
  recorded here in the shape the source states it.

## What is and is not proved

The construction below is [Stacks, Tag 07J6] for a locally quasi-coherent sheaf crystal on an
object with affine ambient scheme, in the ring-level spelling of [Stacks, Tag 07I0].  **No
`@[stacks]` attribute is placed.**  The tag is stated for *every* object of `CRIS(X/S)`, and
affineness of the object is a hypothesis the source does not impose; the reason this spelling
needs an affine one is the reason recorded in the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/SecondOrderIdealAffineIntegrable.lean` — at global
sections the identification `Ω ⊗_D M(A) ≅ ker(i^* : M(U, T', δ') ⟶ M(A))` which gives `∇` its
target is false on a non-affine object, so there is no connection at global sections there to
reconstruct.  Affineness enters a second time, through
`Crystalline.GlobalCrystallineSituation.affineCrysOmegaEquiv`, to identify the two spellings of
`Ω`; the sheaf one is the target of [Stacks, Tag 07J6] and the presheaf one is the target of
[Stacks, Tag 07J4], and `Crystalline.GlobalCrystallineSituation.restrictedToSheaf` is only a
morphism between them on a general object.

The instance `[(ambientSchemeModules M A).IsQuasicoherent]` is the ambient-scheme reading of the
source's own quasi-coherence clause; it is the hypothesis under which the affine chain of
`StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealAffine.lean` is stated, and nothing in
the tree produces it from `Crystalline.GlobalCrystallineSituation.IsLocallyQuasiCoherent`.

## References

* [Stacks Project, Lemma 60.15.1, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Section 60.15, Tag 07J5](https://stacks.math.columbia.edu/tag/07J5)
* [Stacks Project, Tag 07J4](https://stacks.math.columbia.edu/tag/07J4)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
* [Stacks Project, Tag 07HY](https://stacks.math.columbia.edu/tag/07HY)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry TensorProduct

universe u

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}
  (M : SheafOfModules.{u} (crystallineStructureSheaf S)) (A : Thickening S)
  [IsAffine A.thickening.target.scheme] {V : S.S.scheme.Opens}
  (hVA : (⊤ : A.thickening.target.scheme.Opens) ≤ A.toBase.hom ⁻¹ᵁ V) (hV : IsAffineOpen V)

/-! ### The two readings of the target of the connection -/

/-- **The two readings of the target of the canonical connection agree**, on an object with
affine ambient scheme lying over an affine open of the divided power base: the module
`Γ(T, Ω_{T/S,δ}) ⊗_D M(A)` in which
`Crystalline.GlobalCrystallineSituation.crystalConnectionTensor` takes its values is the module
`M(A) ⊗_D Ω_{X/S}(U, T, δ)` that `Crystalline.Connection` asks for.

The two factors are swapped by `TensorProduct.comm` and the two spellings of `Ω` are identified
by `Crystalline.GlobalCrystallineSituation.affineCrysOmegaEquiv`. -/
def affineCrysTensorFlip :
    crysDiffSections A ⊗[crysFormRing S A] M.val.obj (op A) ≃ₗ[crysFormRing S A]
      M.val.obj (op A) ⊗[crysFormRing S A] ↥((crysDifferentials S).obj (op A)) :=
  (TensorProduct.comm (crysFormRing S A) (crysDiffSections A) (M.val.obj (op A))).trans
    (TensorProduct.congr (LinearEquiv.refl (crysFormRing S A) (M.val.obj (op A)))
      (affineCrysOmegaEquiv A hVA hV))

/-- On a pure tensor `ω ⊗ s` the flip is `s ⊗ ω`, with `ω` read through `affineCrysOmegaEquiv`. -/
@[simp]
theorem affineCrysTensorFlip_tmul (ω : crysDiffSections A) (s : M.val.obj (op A)) :
    affineCrysTensorFlip M A hVA hV (ω ⊗ₜ[crysFormRing S A] s) =
      s ⊗ₜ[crysFormRing S A] affineCrysOmegaEquiv A hVA hV ω := rfl

/-- The identification carries the differential term of the Leibniz rule of [Stacks, Tag 07J6]
to the differential term of the Leibniz rule of [Stacks, Tag 07I0]. -/
theorem affineCrysTensorFlip_crysDerivation_tmul (b : crysFormRing S A)
    (s : M.val.obj (op A)) :
    affineCrysTensorFlip M A hVA hV
        (sheafApp A.thickening.target S.S.scheme A.toBase.hom ⊤ b ⊗ₜ[crysFormRing S A] s) =
      s ⊗ₜ[crysFormRing S A]
        crysPi S A (KaehlerDifferential.D ↥Γ(S.S.scheme, ⊤) (crysFormRing S A) b) :=
  congrArg (fun x ↦ s ⊗ₜ[crysFormRing S A] x) (affineCrysOmegaEquiv_crysPi_D A hVA hV b)

/-! ### The connection -/

/-- **Stacks Project, Lemma 60.15.1, Tag 07J6, in the ring-level spelling of
[Stacks, Tag 07I0].**  The canonical connection

`∇ : M(A) ⟶ M(A) ⊗_D Ω_{X/S}(U, T, δ)`

of a sheaf of `𝒪_{X/S}`-modules on an object with affine ambient scheme, as a term of
`Crystalline.Connection` relative to the presentation
`Crystalline.GlobalCrystallineSituation.crysPi` of the sections of `Ω_{X/S}`.

It is `Crystalline.GlobalCrystallineSituation.crystalConnectionTensor`, the difference
`p₁^* s - p₀^* s` of the restrictions along the two projections of the first-order universal
thickening of [Stacks, Tag 07J2], read through the identification
`Crystalline.GlobalCrystallineSituation.affineCrysTensorFlip` of the two readings of its target.
The Leibniz rule of the structure is the Leibniz rule
`Crystalline.GlobalCrystallineSituation.crystalConnectionTensor_smul` of the tag.

The degree-one identification datum is a hypothesis here; `affineCrystalConnection` discharges it
from the crystal condition. -/
def affineCrystalConnectionOf (h : FirstOrderIdealBaseChange M A) :
    Connection ↥Γ(S.S.scheme, ⊤) (crysFormRing S A) (crysPi S A) (M.val.obj (op A)) where
  toAddMonoidHom :=
    (affineCrysTensorFlip M A hVA hV).toAddEquiv.toAddMonoidHom.comp
      (crystalConnectionTensor M A h)
  leibniz' b s := by
    refine (congrArg (affineCrysTensorFlip M A hVA hV)
      (crystalConnectionTensor_smul M A h b s)).trans ?_
    refine ((affineCrysTensorFlip M A hVA hV).map_add _ _).trans ?_
    exact congrArg₂ (· + ·) ((affineCrysTensorFlip M A hVA hV).map_smul b _)
      (affineCrysTensorFlip_crysDerivation_tmul M A hVA hV b s)

/-- The connection `affineCrystalConnectionOf` is `crystalConnectionTensor` followed by the flip
`affineCrysTensorFlip`. -/
theorem affineCrystalConnectionOf_apply (h : FirstOrderIdealBaseChange M A)
    (s : M.val.obj (op A)) :
    affineCrystalConnectionOf M A hVA hV h s =
      affineCrysTensorFlip M A hVA hV (crystalConnectionTensor M A h s) := rfl

variable [(ambientSchemeModules M A).IsQuasicoherent]

/-- **Stacks Project, Lemma 60.15.1, Tag 07J6, in the ring-level spelling of
[Stacks, Tag 07I0], for a crystal.**  The canonical connection

`∇ : M(A) ⟶ M(A) ⊗_D Ω_{X/S}(U, T, δ)`

that a sheaf crystal in quasi-coherent `𝒪_{X/S}`-modules carries over an object with affine
ambient scheme, with the degree-one identification datum of the tag supplied by the crystal
condition through
`Crystalline.GlobalCrystallineSituation.firstOrderIdealBaseChangeOfIsSheafCrystal` rather than
assumed. -/
def affineCrystalConnection (hM : IsSheafCrystal M) :
    Connection ↥Γ(S.S.scheme, ⊤) (crysFormRing S A) (crysPi S A) (M.val.obj (op A)) :=
  affineCrystalConnectionOf M A hVA hV (firstOrderIdealBaseChangeOfIsSheafCrystal M A hM)

/-- The canonical connection of a crystal is `crystalConnectionTensor`, for the identification
datum `firstOrderIdealBaseChangeOfIsSheafCrystal`, followed by the flip `affineCrysTensorFlip`. -/
theorem affineCrystalConnection_apply (hM : IsSheafCrystal M) (s : M.val.obj (op A)) :
    affineCrystalConnection M A hVA hV hM s =
      affineCrysTensorFlip M A hVA hV
        (crystalConnectionTensor M A (firstOrderIdealBaseChangeOfIsSheafCrystal M A hM) s) :=
  rfl

/-- **The Leibniz rule of [Stacks, Tag 07I0] for the canonical connection of a crystal**,
`∇(b s) = b ∇(s) + s ⊗ π(d b)`.  It is the defining property of the structure
`Crystalline.Connection`, and it is the Leibniz rule
`Crystalline.GlobalCrystallineSituation.crystalConnectionTensor_smul` of [Stacks, Tag 07J6] read
through the identification of the two targets. -/
theorem affineCrystalConnection_leibniz (hM : IsSheafCrystal M) (b : crysFormRing S A)
    (s : M.val.obj (op A)) :
    affineCrystalConnection M A hVA hV hM (b • s) =
      b • affineCrystalConnection M A hVA hV hM s +
        s ⊗ₜ[crysFormRing S A]
          crysPi S A (KaehlerDifferential.D ↥Γ(S.S.scheme, ⊤) (crysFormRing S A) b) :=
  (affineCrystalConnection M A hVA hV hM).leibniz b s

end Crystalline.GlobalCrystallineSituation

end
