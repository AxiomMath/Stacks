module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCharacterization.Characterization
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDerivedHomDual
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectTensorPullbackBound

/-!
# [Stacks, Tag 0DJV]: the complex of [Stacks, Tag 0DJU] is characterized by relative `Ext`

Let `S` be quasi-compact and quasi-separated, `f : X ⟶ S` proper, flat and of finite
presentation, `E` perfect relative to `S` and `K` pseudo-coherent on `X`. The pseudo-coherent
complex `L` of [Stacks, Tag 0DJU] carries functorial isomorphisms
`Ext^i_{𝒪_S}(L, ℱ) ≃ Ext^i_{𝒪_X}(K, E ⊗^L Lf^*ℱ)`, `ℱ` quasi-coherent, compatible with boundary
maps; they come from a natural identification on `D^+_{QCoh}(𝒪_S)`, which characterizes `L` up to
an isomorphism inducing it.

## The module-level form of the uniqueness

The remark asserts uniqueness among pseudo-coherent `L'` admitting functorial isomorphisms of
`Ext`-groups on quasi-coherent modules compatible with boundary maps, i.e. from a `δ`-functor
isomorphism alone. That form is **not** proved here and is open as far as this development goes.
At `f = 𝟙`, `E = 𝒪` it says that a pseudo-coherent complex is determined by its `δ`-functor
`ℱ ↦ Ext^*(L, ℱ)` on quasi-coherent modules. When Yoneda and derived `Ext` agree (e.g. `S`
affine), this amounts to the restricted Yoneda functor `L ↦ Hom(L, -)` on the full subcategory of
shifted quasi-coherent modules reflecting isomorphism classes. That is a realization question for
the Adams spectral sequence relative to the injective class of shifted modules (J. D. Christensen,
*Ideals in triangulated categories: phantoms, ghosts and skeleta*, Adv. Math. 136 (1998)).
Building `L' ⟶ L` stage by stage along the truncations of `L` succeeds while the
k-invariants do not obstruct. It meets a Toda-bracket-type secondary obstruction from three
nonzero cohomology sheaves on. The source itself says "if we ever need this we will formulate a
precise result here", and the result above is the precise form proved.

## Main results

* `Stacks.AlgebraicGeometry.RelativeExtCharacterization.exists_unique_relativeExt_representative`:
  **[Stacks, Tag 0DJV]**.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open Opposite MonoidalCategory AlgebraicGeometry

universe u

attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

namespace Stacks.AlgebraicGeometry.RelativeExtCharacterization

open Stacks.SheafOfModules Stacks.AlgebraicGeometry.RelativeDerivedHomDual
open Stacks.Cohomology.RelativeExtCanonical

attribute [local instance] derivedMonoidalStructure derivedSymmetricStructure

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **[Stacks, Tag 0DJV].** Let `S` be quasi-compact and quasi-separated, `f : X ⟶ S` proper,
flat and of finite presentation, `E ∈ D(𝒪_X)` perfect relative to `S` and `K ∈ D(𝒪_X)`
pseudo-coherent. The pseudo-coherent complex `L` on `S` of [Stacks, Tag 0DJU], with
`Rf_*R𝓗om(K, E) ≅ R𝓗om(L, 𝒪_S)`, carries isomorphisms

`Ext^i_{𝒪_S}(L, ℱ) ≃ Ext^i_{𝒪_X}(K, E ⊗^L_{𝒪_X} Lf^*ℱ)`

for all `i` and all quasi-coherent `ℱ`, functorial in `ℱ` and compatible with the boundary maps
of short exact sequences of quasi-coherent modules (on the left, composition with the
connecting morphism `ℱ₃ ⟶ ℱ₁[1]`; on the right, composition with its image under
`E ⊗^L Lf^*(-)`, the third morphism of a distinguished triangle by
`tensorPull_mapTriangle_singleTriangle`). These isomorphisms are induced by a natural
identification `θ_N : Hom(L, N) ≃ Hom(K, E ⊗^L Lf^*N)` for `N` in `D^+_{QCoh}(𝒪_S)` (the `ℱ[i]`
being such `N`), and `L` is characterized by it: any pseudo-coherent `L'` carrying a natural
identification `θ'` of the same kind is isomorphic to `L`, by an isomorphism `φ` with
`θ'(φ ∘ x) = θ(x)`.

The source leaves the statement imprecise ("If we ever need this we will formulate a precise
result here"); the above is the precise form proved. Uniqueness from the module-level
`δ`-functor alone, i.e. from natural isomorphisms of the `Ext^i(-, ℱ)` on quasi-coherent `ℱ`
compatible with boundary maps but not coming from an identification on `D^+_{QCoh}(𝒪_S)`, is
**not** asserted: at `f = 𝟙` and `E = 𝒪` it is the statement that a pseudo-coherent complex on
a quasi-compact quasi-separated scheme is determined by its `δ`-functor `ℱ ↦ Ext^*(L, ℱ)` on
quasi-coherent modules, which is neither proved nor refuted here. -/
theorem exists_unique_relativeExt_representative [CompactSpace S] [QuasiSeparatedSpace S]
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] (E K : DStd X)
    (hE : IsRelPerfect f E) (hK : IsPseudoCoherentStd K) :
    ∃ L : DStd S, IsPseudoCoherentStd L ∧
      Nonempty ((pushStd f).obj (rhom K E) ≅ rhom L (unitObj S)) ∧
      ∃ θ : ShiftedHom.NaturalHomIdentification (𝟭 (DStd S)) (tensorPull f E) L K
          (boundedBelowQCoh S),
        (∀ {F F' : S.Modules} (hF : F.IsQuasicoherent) (hF' : F'.IsQuasicoherent)
            (g : F ⟶ F') (i : ℤ)
            (x : ShiftedHom L ((RelativeDerivedHomDual.singleStd S 0).obj F) i),
          extEquiv θ F' hF' i (x ≫ ((RelativeDerivedHomDual.singleStd S 0).map g)⟦i⟧') =
            extEquiv θ F hF i x ≫
              ((tensorPull f E).map ((RelativeDerivedHomDual.singleStd S 0).map g))⟦i⟧') ∧
        (∀ {T : ShortComplex S.Modules} (hT : T.ShortExact) (h₁ : T.X₁.IsQuasicoherent)
            (h₃ : T.X₃.IsQuasicoherent) (i j : ℤ) (hij : 1 + i = j)
            (x : ShiftedHom L ((RelativeDerivedHomDual.singleStd S 0).obj T.X₃) i),
          extEquiv θ T.X₁ h₁ j (ShiftedHom.comp x (singleδStd hT) hij) =
            (extEquiv θ T.X₃ h₃ i x).comp (ShiftedHom.map (singleδStd hT) (tensorPull f E))
              hij) ∧
        ∀ (L' : DStd S), IsPseudoCoherentStd L' →
          ∀ θ' : ShiftedHom.NaturalHomIdentification (𝟭 (DStd S)) (tensorPull f E) L' K
            (boundedBelowQCoh S),
          ∃ φ : L' ≅ L, ∀ (N : DStd S) (hN : boundedBelowQCoh S N) (x : L ⟶ N),
            θ'.equiv N hN (φ.hom ≫ x) = θ.equiv N hN x := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨FK, hcop, c, hK', hFK, htrc, hM, hcop', L, d, hL, hLpc, ⟨b, htrd⟩, hiso⟩ :=
    exists_construction_isPseudoCoherent f E K hE hK
  obtain ⟨a, ha⟩ := exists_isGE_derivedTensor_derivedPullback_of_isRelativelyPerfect f E hE
  have hqc : ∀ {Z : Scheme.{u}} (A : DStd Z), IsPseudoCoherentStd A →
      ∀ q : ℤ, ((HStd Z q).obj A).IsQuasicoherent := fun A hA q ↦
    @Stacks.PseudoCoherentHocolim.isQuasicoherent_homology_of_isPseudoCoherent _
      (HasDerivedCategory.standard _) A hA q
  have hstage : ∀ k : ℤ, ∃ n, IsIso (((tStd X).truncGE k).map (c n)) ∧
      IsIso (((tStd S).truncGE k).map (d n)) := by
    intro k
    refine ⟨(-k).toNat + b.toNat, ?_, ?_⟩ <;>
      refine (@Stacks.PseudoCoherentHocolim.isIso_truncGE_map_iff _ _ _
        (HasDerivedCategory.standard _) _ _ _ k).2 fun i hi ↦ ?_
    exacts [htrc _ i (by omega), htrd _ i (by omega)]
  obtain ⟨θ, h₁, h₂, h₃⟩ := characterization_of_presentation f E
    (hqc E (isPseudoCoherentStd_of_isRelPerfect hE)) FK hK' hFK (fun n ↦ hM n) hL hstage
    (hqc L hLpc) a ha
  exact ⟨L, hLpc, hiso, θ, h₁, h₂, fun L' hL' θ' ↦ h₃ L' (hqc L' hL') θ'⟩

end Stacks.AlgebraicGeometry.RelativeExtCharacterization
