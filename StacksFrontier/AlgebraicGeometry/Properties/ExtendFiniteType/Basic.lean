module

public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeGeneration
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjectExtension
public import StacksCore.Tactic.StacksAttribute

/-!
# Extending a finite type quasi-coherent module from a quasi-compact open

Let `X` be a quasi-compact and quasi-separated scheme and let `U ⊆ X` be a quasi-compact open.
A quasi-coherent `𝒪_U`-module of finite type is the restriction to `U` of a quasi-coherent
`𝒪_X`-module of finite type. This is part (1) of Stacks 0G41.

The source proves it in two steps, and so do we. First the module is extended to `X` with no
control on finiteness, by the explicit extension of Stacks 01PE
(`AlgebraicGeometry.exists_quasicoherent_extension`) applied to the zero morphism into a free
module on the empty type; this only uses that `U → X` is quasi-compact, which quasi-compactness
of `U` supplies. Then finiteness is recovered by viewing the extension's own restriction as the
top subobject of itself and feeding that to Stacks 01PF
(`AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_extension`), which cuts the
extension down to a finite type quasi-coherent submodule without changing it over `U`.

Part (2) of Stacks 0G41, the statement for modules of finite presentation, is not proved here:
it is the case `ℱ = 0` of Stacks 01PI, which this tree does not yet have.

## Main results

* `AlgebraicGeometry.exists_finiteTypeQuasicoherent_extension`: part (1) of Stacks 0G41.

## References

* [Stacks Project, Tag 0G41](https://stacks.math.columbia.edu/tag/0G41)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme Scheme.Modules

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0G41 (1).** Let `X` be a quasi-compact and quasi-separated scheme and
let `U ⊆ X` be a quasi-compact open. A quasi-coherent `𝒪_U`-module of finite type extends to a
quasi-coherent `𝒪_X`-module of finite type. -/
@[stacks 0G41 "(1)", ega "I 9.4.8", ega "I 9.4.5"]
theorem exists_finiteTypeQuasicoherent_extension
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : X.Opens) (hU : IsCompact U.1)
    (G : U.toScheme.Modules) [G.IsQuasicoherent] [G.IsFiniteType] :
    ∃ (G' : X.Modules) (_ : G'.IsQuasicoherent) (_ : G'.IsFiniteType),
      Nonempty (G'.restrict U.ι ≅ G) := by
  -- `U` is quasi-compact, so the open immersion `U.ι` is a quasi-compact morphism.
  have hQC : QuasiCompact U.ι := quasiCompact_iff_isSpectralMap.mpr
    (IsRetrocompact_iff_isSpectralMap_subtypeVal.mp (hU.isRetrocompact U.2))
  -- Stacks 01PE, applied to the zero morphism into the free module on the empty type, extends
  -- `G` to a quasi-coherent module `H` on `X`, with no finiteness yet.
  obtain ⟨H, hH, ψ, e, he⟩ :=
    exists_quasicoherent_extension U.ι (freeOn X PEmpty.{u + 1}) G 0
  have hHqc : H.IsQuasicoherent := hH
  -- View `H|_U` as the top subobject of itself; it is quasi-coherent and of finite type
  -- because it is isomorphic to `G`.
  let eTop : ((⊤ : Subobject (H.restrict U.ι)) : U.toScheme.Modules) ≅ G :=
    asIso (⊤ : Subobject (H.restrict U.ι)).arrow ≪≫ e
  have : ((⊤ : Subobject (H.restrict U.ι)) : U.toScheme.Modules).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso eTop.symm inferInstance
  have : ((⊤ : Subobject (H.restrict U.ι)) : U.toScheme.Modules).IsFiniteType :=
    isFiniteType_of_iso_modules eTop inferInstance
  -- Stacks 01PF cuts `H` down to a finite type quasi-coherent submodule agreeing with `G`.
  obtain ⟨G', hG'qc, hG'ft, e', he'⟩ :=
    exists_finiteTypeQuasicoherentSubobject_extension H U hU ⊤
  exact ⟨(G' : X.Modules), hG'qc, hG'ft, ⟨e' ≪≫ eTop⟩⟩

end AlgebraicGeometry
