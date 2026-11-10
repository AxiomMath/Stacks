module

public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzNeighbourhoodSectionsComplete
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzCompletedStalkDepthCriterion
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.NeighbourhoodCompletion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ZeroSchemeOpenNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Variety.CohenMacaulayDepthDimensionBound
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.SheafRankOne.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleTensorPower.Basic

/-!
# Full faithfulness of completion along the zero scheme of an ample section

Let `k` be a field, `X` a proper scheme over `k`, `𝓛` an ample invertible `𝒪_X`-module,
`s ∈ Γ(X, 𝓛)` and `Y = Z(s)`. The full faithfulness half of [Stacks, Tag 0EL7] is the following
reduction, which this file carries out: by [Stacks, Tag 0EK2] it suffices that

`colim_𝒱 Γ(V, 𝓛^{⊗ m}) ⟶ lim Γ(Y_n, 𝓛^{⊗ m}|_{Y_n})`

be an isomorphism for all `m`, which is condition (2) of that lemma, and this follows from
[Stacks, Tag 0EL2] applied to the coherent modules `𝓛^{⊗ m}`, whose stalks have the depth of the
local rings.

## Main results

* `Stacks.Algebraization.isNeighbourhoodSectionsComplete_of_isIso_zeroSchemeComparison` — the
  comparison of [Stacks, Tag 0EL2] for a coherent `F` with `depth(F_x) + dim({x}‾) > 1` off `Y`, in
  the vocabulary of [Stacks, Tag 0EK2], given the degree-zero comparison of [Stacks, Tag 0EL1].
* `Stacks.Algebraization.completionFullyFaithfulComplete_zeroScheme` — condition (4) of
  [Stacks, Tag 0EK2] for `Y ⟶ X` from the comparison for all tensor powers of `𝓛`.

## References

* [Stacks Project, Tag 0EL7](https://stacks.math.columbia.edu/tag/0EL7)
* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
* [Stacks Project, Tag 0EL2](https://stacks.math.columbia.edu/tag/0EL2)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Algebraization

/-- **The depth bound `> 2` for `𝒪_{X,x}` gives the bound `> 1` for a module of larger depth**, in
the extended-integer spelling of [Stacks, Tag 0EL1]. -/
public theorem one_lt_enatToEInt_add_of_two_lt {d d' : ℕ∞} {c : WithBot ℕ∞} (hd : d ≤ d')
    (h : ((2 : ℕ) : WithBot ℕ∞) < (d : WithBot ℕ∞) + c) :
    enatToEInt d' + krullDimToEInt c > ((1 : ℤ) : EInt) := by
  have h2 : ((2 : ℕ) : WithBot ℕ∞) ≤ (d' : WithBot ℕ∞) + c :=
    h.le.trans (add_le_add_left (WithBot.coe_le_coe.mpr hd) _)
  have hm := krullDimToEInt_mono h2
  rw [krullDimToEInt_add, krullDimToEInt_coe] at hm
  refine lt_of_lt_of_le ?_ hm
  change ((1 : ℤ) : EInt) < ((2 : ℤ) : EInt)
  exact WithBotTop.coe_lt_coe.mpr (by norm_num)

/-- **[Stacks, Tag 0EL2] in the vocabulary of [Stacks, Tag 0EK2].** For `F` coherent with
`depth(F_x) + dim({x}‾) > 1` off `Y = Z(s)`, invertibility of the degree-zero comparison of
[Stacks, Tag 0EL1] gives `colim_𝒱 Γ(V, F) ≅ lim Γ(Y_n, F|_{Y_n})`: restriction `Γ(X, F) ⟶ Γ(V, F)`
is bijective for every open `V ⊇ Y`
(`Stacks.Algebraization.bijective_presheaf_map_of_depthAddDim_gt`), so the colimit is `Γ(X, F)`. -/
public theorem isNeighbourhoodSectionsComplete_of_isIso_zeroSchemeComparison (k : Type u) [Field k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsProper f] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L) (s : Γ(L, ⊤))
    (F : X.Modules) [F.IsCoherent] [F.IsQuasicoherent]
    (hdepth : ∀ x : X, x ∉ ((zeroScheme X L s).support : Set X) →
      enatToEInt (sheafDepthAt F x) + krullDimToEInt (dimClosureAt X x) > ((1 : ℤ) : EInt))
    (hiso : IsIso (zeroSchemeComparison X L s F 0)) :
    IsNeighbourhoodSectionsComplete (zeroScheme X L s).subschemeι F :=
  isNeighbourhoodSectionsComplete_of_isInfinitesimalSectionsComplete _ F
    (isInfinitesimalSectionsComplete_of_isIso_comparison _ F (zeroScheme X L s)
      (zeroSchemeTowerIdeal_succ_le X L s) (Scheme.IdealSheafData.ker_subschemeι _).symm hiso)
    fun V hV => bijective_presheaf_map_of_depthAddDim_gt k f L hL s F hdepth
      (by rwa [Scheme.IdealSheafData.range_subschemeι] at hV)

/-- The tensor powers of an invertible module are finite locally free (of rank one). -/
public theorem isFiniteLocallyFree_tensorPowerModules (X : Scheme.{u}) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (m : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Scheme.Modules.tensorPowerModules L m) :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    (R := X.ringCatSheaf) _ 1
    (hM := Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme X _)

/-- The tensor powers of an invertible module on a locally Noetherian scheme are coherent. -/
public theorem isCoherent_tensorPowerModules (X : Scheme.{u}) [IsLocallyNoetherian X]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (m : ℤ) :
    (Scheme.Modules.tensorPowerModules L m).IsCoherent :=
  Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible (X := X) _

/-- **Full faithfulness of completion along `Y = Z(s)`.** If `colim_𝒱 Γ(V, 𝓛^{⊗ m}) ⟶
lim Γ(Y_n, 𝓛^{⊗ m}|_{Y_n})` is an isomorphism for every `m`, then condition (2) of
[Stacks, Tag 0EK2] holds for the ample module `𝓛`, hence so does condition (4): the completion
functor `colim_𝒱 Coh(𝒪_V) ⟶ Coh(X, 𝓘)` is fully faithful on finite locally free objects. -/
public theorem completionFullyFaithfulComplete_zeroScheme (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (.of k)) [IsProper f] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (hL : Stacks.Ample.IsAmple X L) (s : Γ(L, ⊤))
    (hsec : ∀ m : ℕ, IsNeighbourhoodSectionsComplete (zeroScheme X L s).subschemeι
      (Scheme.Modules.tensorPowerModules L (m : ℤ))) :
    NeighbourhoodCompletion.CompletionFullyFaithfulComplete (zeroScheme X L s).subschemeι := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  have hample : AlgebraicGeometry.Scheme.Modules.IsAmple X L :=
    (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple X L).mpr hL
  refine (NeighbourhoodCompletion.implications_among_conditions _).2.2.1
    ((NeighbourhoodCompletion.implications_among_conditions _).2.1 ⟨L, inferInstance, hample, 0,
      fun m _ => (infTower_isSectionsComplete_iff _ _).mpr (hsec m)⟩)

end Stacks.Algebraization

end
