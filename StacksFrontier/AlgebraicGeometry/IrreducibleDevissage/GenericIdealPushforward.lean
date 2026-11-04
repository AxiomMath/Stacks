module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCoherentImage.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.GenericAnnihilator
public import StacksFrontier.AlgebraicGeometry.IntegralReduction.Transport
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.Coproduct
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.GenericFreeNeighbourhood
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.GenericIdealCoproduct

/-!
# Pushing an ideal sum forward along a closed immersion

Direct image along a closed immersion `i : Z ⟶ X` of locally Noetherian schemes is an
equivalence from coherent `𝒪_Z`-modules onto the coherent `𝒪_X`-modules annihilated by the
ideal sheaf of `Z` ([Stacks, Tag 087T]). This file records the two consequences the dévissage
of [Stacks, Tag 01YE] needs: that such a module *is* a direct image of a coherent module, and
that an isomorphism over an open of `Z` becomes an isomorphism over any open of `X` whose
preimage lies inside it.

## Main results

* `Stacks.ClosedImmersion.exists_coherent_pushforward_iso` — a coherent `𝒪_X`-module
  annihilated by the ideal sheaf of `Z` is the direct image of a coherent `𝒪_Z`-module.
* `Stacks.ClosedImmersion.isIso_restrictFunctor_map_pushforward` — direct image carries an
  isomorphism over `V ⊆ Z` to one over any open of `X` with preimage inside `V`.
* `Stacks.ClosedImmersion.exists_idealCoproduct_pushforward_of_annihilator` — the dévissage of
  [Stacks, Tag 01YE] assembled from its two inputs: the annihilator submodule of `ℱ`, and the
  integral case applied to the module it is the direct image of.
* `Stacks.ClosedImmersion.exists_idealCoproduct_pushforward_mono_isIso_near_genericPoint` —
  **[Stacks, Tag 01YE]**, with both inputs discharged.

## Implementation notes

The direct image of a module has, over an open `U` of `X`, the sections of the module over
`i ⁻¹ᵁ U`, and the direct image of a morphism acts on them as the morphism itself; both are
definitional (`AlgebraicGeometry.Scheme.Modules.pushforward_map_app`). So being an isomorphism
after restriction, which is bijectivity on the sections over every smaller open, transfers
along the preimage.

The open of `X` used downstream is the complement of the image of the complement, which is open
because a closed immersion is a closed map; it contains the image of every point of the given
open of `Z`, and its preimage lies inside that open.

## References

* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 01YE](https://stacks.math.columbia.edu/tag/01YE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.Tag01YEIntegralReduction (isIso_restrictFunctor_map_of_forall_app
  isIso_app_of_isIso_restrictFunctor_map)

universe u

namespace Stacks.ClosedImmersion

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {Z X : Scheme.{u}}

/-! ### Isomorphisms over an open, under direct image -/

/-- Being an isomorphism after restriction to an open passes to any smaller open. -/
theorem isIso_restrictFunctor_map_of_le {F G : X.Modules} (f : F ⟶ G) {U V : X.Opens}
    (h : V ≤ U) (hf : IsIso ((Scheme.Modules.restrictFunctor U.ι).map f)) :
    IsIso ((Scheme.Modules.restrictFunctor V.ι).map f) :=
  isIso_restrictFunctor_map_of_forall_app f V fun W hW =>
    isIso_app_of_isIso_restrictFunctor_map f U hf W (hW.trans h)

/-- **Direct image preserves being an isomorphism over an open.** If `f` is an isomorphism after
restriction to `V ⊆ Z`, then `i_* f` is one after restriction to any open of `X` whose preimage
lies in `V`: on sections over an open `W` of `X`, `i_* f` is `f` on sections over `i ⁻¹ᵁ W`. -/
theorem isIso_restrictFunctor_map_pushforward (i : Z ⟶ X) {F G : Z.Modules} (f : F ⟶ G)
    (VZ : Z.Opens) (hf : IsIso ((Scheme.Modules.restrictFunctor VZ.ι).map f))
    (V : X.Opens) (hV : i ⁻¹ᵁ V ≤ VZ) :
    IsIso ((Scheme.Modules.restrictFunctor V.ι).map
      ((Scheme.Modules.pushforward i).map f)) := by
  refine isIso_restrictFunctor_map_of_forall_app _ V fun W hW => ?_
  have h : ((Scheme.Modules.pushforward i).map f).app W = f.app (i ⁻¹ᵁ W) := rfl
  rw [h]
  exact isIso_app_of_isIso_restrictFunctor_map f VZ hf (i ⁻¹ᵁ W)
    ((i.preimage_mono hW).trans hV)

/-! ### An open of the ambient scheme cut out by an open of the closed subscheme -/

/-- The largest open of `X` whose preimage under a closed immersion `i` lies inside a given open
`VZ` of `Z`: the complement of the image of the complement of `VZ`, which is open because a
closed immersion is a closed map. -/
def pushforwardOpen (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i] (VZ : Z.Opens) :
    X.Opens :=
  ⟨(i.base '' (VZ : Set Z)ᶜ)ᶜ,
    (i.isClosedEmbedding.isClosedMap _ VZ.isOpen.isClosed_compl).isOpen_compl⟩

/-- The image of a point of `VZ` lies in `Stacks.ClosedImmersion.pushforwardOpen i VZ`. -/
theorem mem_pushforwardOpen (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i] (VZ : Z.Opens)
    {z : Z} (hz : z ∈ VZ) : i.base z ∈ pushforwardOpen i VZ := by
  rintro ⟨w, hw, he⟩
  exact hw (i.isClosedEmbedding.injective he ▸ hz)

/-- The preimage of `Stacks.ClosedImmersion.pushforwardOpen i VZ` lies in `VZ`. -/
theorem preimage_pushforwardOpen_le (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i]
    (VZ : Z.Opens) : i ⁻¹ᵁ pushforwardOpen i VZ ≤ VZ := by
  intro z hz
  by_contra hn
  exact hz ⟨z, hn, rfl⟩

/-! ### Writing an annihilated coherent module as a direct image -/

/-- **[Stacks, Tag 087T], essential surjectivity.** A coherent `𝒪_X`-module annihilated by the
ideal sheaf cutting out a closed subscheme `Z` is the direct image of a coherent
`𝒪_Z`-module. -/
theorem exists_coherent_pushforward_iso (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    (N : X.Modules) [N.IsCoherent] (hN : AnnihilatedByKer i N) :
    ∃ G : Z.Modules, G.IsCoherent ∧
      Nonempty ((Scheme.Modules.pushforward i).obj G ≅ N) := by
  let N' : (coherentAnnihilatedByKer i).FullSubcategory := ⟨N, ⟨inferInstance, hN⟩⟩
  let G₀ := (pushforwardCoh i).objPreimage N'
  exact ⟨G₀.obj, G₀.property,
    ⟨((coherentAnnihilatedByKer i).ι).mapIso ((pushforwardCoh i).objObjPreimageIso N')⟩⟩

/-! ### The dévissage of [Stacks, Tag 01YE], assembled -/

/-- **The dévissage of [Stacks, Tag 01YE], assembled from its two inputs.** Suppose `ℱ` has a
coherent submodule `𝒜` which is annihilated by the ideal sheaf cutting out `Z` and agrees with
`ℱ` over a neighbourhood `U` of `i ξ`, and suppose the integral case of the statement is
available on `Z`. Then there are an `r`, a coherent sheaf of ideals `ℐ ⊆ 𝒪_Z` and a
monomorphism `i_*(ℐ^{⊕ r}) ⟶ ℱ` of coherent modules which is an isomorphism on a
neighbourhood of `i ξ`.

`𝒜` is `i_* 𝒢` for a coherent `𝒢` by [Stacks, Tag 087T], the integral case gives a
monomorphism `ℐ^{⊕ r} ⟶ 𝒢` invertible over an open `V ∋ ξ`, and its direct image composed with
`𝒜 ⟶ ℱ` is invertible over `U` intersected with the largest open of `X` whose preimage lies in
`V`. -/
theorem exists_idealCoproduct_pushforward_of_annihilator [AlgebraicGeometry.IsNoetherian X]
    (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i] [IsLocallyNoetherian Z] (ξ : Z)
    (F : X.Modules) [F.IsCoherent]
    (A : F.Submodule) (hAcoh : A.toSheafOfModules.IsCoherent)
    (hAkill : AnnihilatedByKer i A.toSheafOfModules)
    (Uξ : X.Opens) (hUξ : i.base ξ ∈ Uξ)
    (hAiso : IsIso ((Scheme.Modules.restrictFunctor Uξ.ι).map A.ι))
    (hB : ∀ G : Z.Modules, G.IsCoherent →
      ∃ (r : ℕ) (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
        I.toSheafOfModules.IsCoherent ∧
        ∃ β : (∐ fun _ : Fin r => I.toSheafOfModules) ⟶ G, Mono β ∧
          ∃ V : Z.Opens, ξ ∈ V ∧
            IsIso ((Scheme.Modules.restrictFunctor V.ι).map β)) :
    ∃ (r : ℕ) (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      I.toSheafOfModules.IsCoherent ∧
      ((Scheme.Modules.pushforward i).obj
        (∐ fun _ : Fin r => I.toSheafOfModules)).IsCoherent ∧
      ∃ φ : (Scheme.Modules.pushforward i).obj
          (∐ fun _ : Fin r => I.toSheafOfModules) ⟶ F,
        Mono φ ∧ ∃ U : X.Opens, i.base ξ ∈ U ∧
          IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ) := by
  classical
  have hXln : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have hA := hAcoh
  obtain ⟨G, hGcoh, ⟨eG⟩⟩ := exists_coherent_pushforward_iso i A.toSheafOfModules hAkill
  obtain ⟨r, I, hIcoh, β, hβmono, VZ, hξVZ, hβiso⟩ := hB G hGcoh
  have hIqc : I.toSheafOfModules.IsQuasicoherent := by
    have := hIcoh
    exact isQuasicoherent_of_isCoherent _
  have hMI : ((Scheme.Modules.pushforward i).obj I.toSheafOfModules).IsCoherent :=
    AlgebraicGeometry.ClosedImmersionCoherentImage.isCoherent_pushforward_submodule_unit i I hIqc
  have hM : ((Scheme.Modules.pushforward i).obj
      (∐ fun _ : Fin r => I.toSheafOfModules)).IsCoherent :=
    Stacks.AlgebraicGeometry.IrreducibleDevissage.isCoherent_pushforward_coproduct_const i
      I.toSheafOfModules hMI r
  -- the morphism
  have hmβ : Mono ((Scheme.Modules.pushforward i).map β) :=
    @Functor.map_mono _ _ _ _ (Scheme.Modules.pushforward i) inferInstance _ _ β hβmono
  have hmG : Mono eG.hom := mono_of_mono_fac eG.hom_inv_id
  have hmA : Mono A.ι := inferInstance
  refine ⟨r, I, hIcoh, hM, (Scheme.Modules.pushforward i).map β ≫ eG.hom ≫ A.ι, ?_, ?_⟩
  · exact @mono_comp _ _ _ _ _ ((Scheme.Modules.pushforward i).map β) hmβ (eG.hom ≫ A.ι)
      (@mono_comp _ _ _ _ _ eG.hom hmG A.ι hmA)
  -- invertibility near `i ξ`
  refine ⟨Uξ ⊓ pushforwardOpen i VZ, ⟨hUξ, mem_pushforwardOpen i VZ hξVZ⟩, ?_⟩
  have h1 : IsIso ((Scheme.Modules.restrictFunctor (Uξ ⊓ pushforwardOpen i VZ).ι).map
      ((Scheme.Modules.pushforward i).map β)) :=
    isIso_restrictFunctor_map_pushforward i β VZ hβiso _
      ((i.preimage_mono inf_le_right).trans (preimage_pushforwardOpen_le i VZ))
  have h2 : IsIso ((Scheme.Modules.restrictFunctor (Uξ ⊓ pushforwardOpen i VZ).ι).map
      eG.hom) :=
    inferInstanceAs (IsIso
      ((Scheme.Modules.restrictFunctor (Uξ ⊓ pushforwardOpen i VZ).ι).mapIso eG).hom)
  have h3 : IsIso ((Scheme.Modules.restrictFunctor (Uξ ⊓ pushforwardOpen i VZ).ι).map A.ι) :=
    isIso_restrictFunctor_map_of_le A.ι inf_le_left hAiso
  have hc1 : (Scheme.Modules.restrictFunctor (Uξ ⊓ pushforwardOpen i VZ).ι).map
        ((Scheme.Modules.pushforward i).map β ≫ eG.hom ≫ A.ι) =
      (Scheme.Modules.restrictFunctor (Uξ ⊓ pushforwardOpen i VZ).ι).map
          ((Scheme.Modules.pushforward i).map β) ≫
        (Scheme.Modules.restrictFunctor (Uξ ⊓ pushforwardOpen i VZ).ι).map (eG.hom ≫ A.ι) :=
    Functor.map_comp _ _ _
  have hc2 : (Scheme.Modules.restrictFunctor (Uξ ⊓ pushforwardOpen i VZ).ι).map
        (eG.hom ≫ A.ι) =
      (Scheme.Modules.restrictFunctor (Uξ ⊓ pushforwardOpen i VZ).ι).map eG.hom ≫
        (Scheme.Modules.restrictFunctor (Uξ ⊓ pushforwardOpen i VZ).ι).map A.ι :=
    Functor.map_comp _ _ _
  have heq := hc1.trans (congrArg (fun k =>
    (Scheme.Modules.restrictFunctor (Uξ ⊓ pushforwardOpen i VZ).ι).map
      ((Scheme.Modules.pushforward i).map β) ≫ k) hc2)
  exact cast (congrArg (fun k => IsIso k) heq).symm
    (IsIso.comp_isIso' h1 (IsIso.comp_isIso' h2 h3))

/-! ### [Stacks, Tag 01YE] -/

open Stacks.AlgebraicGeometry.IrreducibleDevissage in
/-- **[Stacks, Tag 01YE].** Let `X` be a Noetherian scheme, let `i : Z ⟶ X` be an integral
closed subscheme with generic point `ξ`, and let `ℱ` be a coherent `𝒪_X`-module whose stalk at
`i ξ` is annihilated by the maximal ideal of the local ring there. Then there are an integer
`r ≥ 0`, a coherent sheaf of ideals `ℐ ⊆ 𝒪_Z` and an injective map of coherent sheaves
`i_*(ℐ^{⊕ r}) ⟶ ℱ` which is an isomorphism on a neighbourhood of `i ξ`.

The subsheaf of sections of `ℱ` annihilated by the ideal sheaf of `Z` has the same stalk at
`i ξ` as `ℱ` does, because that ideal generates the maximal ideal there, so it agrees with `ℱ`
on a neighbourhood of `i ξ`; being killed by the ideal it is `i_* 𝒢` for a coherent `𝒢` on `Z`
by [Stacks, Tag 087T]; and the case `Z = X`, applied to `𝒢`, supplies the sheaf of ideals and
the monomorphism. -/
@[stacks 01YE]
theorem exists_idealCoproduct_pushforward_mono_isIso_near_genericPoint
    [AlgebraicGeometry.IsNoetherian X] (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsIntegral Z]
    (ξ : Z) (hξ : IsGenericPoint ξ (Set.univ : Set Z))
    (F : X.Modules) [F.IsCoherent] (hF : StalkKilledByMaximalIdeal F (i ξ)) :
    ∃ (r : ℕ) (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      I.toSheafOfModules.IsCoherent ∧
      ((Scheme.Modules.pushforward i).obj
        (∐ fun _ : Fin r => I.toSheafOfModules)).IsCoherent ∧
      ∃ φ : (Scheme.Modules.pushforward i).obj
          (∐ fun _ : Fin r => I.toSheafOfModules) ⟶ F,
        Mono φ ∧ ∃ U : X.Opens, i ξ ∈ U ∧
          IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ) := by
  have hZln : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  have hZqc : QuasiCompact i := inferInstance
  have hZcs : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace i
  have hZn : AlgebraicGeometry.IsNoetherian Z := { toIsLocallyNoetherian := hZln }
  obtain ⟨A, hAcoh, hAkill, Uξ, hUξ, hAiso⟩ :=
    exists_coherent_annihilator_submodule_isIso_near_of_isLocallyNoetherian i ξ hξ F hF
  exact exists_idealCoproduct_pushforward_of_annihilator i ξ F A hAcoh hAkill Uξ hUξ hAiso
    fun G hG => by
      have := hG
      have := hZn
      exact exists_idealCoproduct_mono_isIso_near_genericPoint G ξ hξ

end Stacks.ClosedImmersion

end
