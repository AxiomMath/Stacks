module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.PartB
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCanonical.ExtOfIdentification
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCanonical.RepresentativeUniquenessDStd
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
import StacksCore.Tactic.StacksAttribute

/-!
# The complex `L` of [Stacks, Tag 08IF] (B) is canonically associated to the situation

Let `S` be Noetherian, `f : X ⟶ S` locally of finite type, `E ∈ D^-_{Coh}(𝒪_X)` and `𝒢` a bounded
complex of coherent `𝒪_X`-modules, flat over `S`, with support proper over `S`; write
`Φ(N) = Lf^*N ⊗^L 𝒢`. The pseudo-coherent `L` of [Stacks, Tag 08IF] (B)
(`Stacks.Cohomology.RelativeExt.pseudoCoherentRepresentative`) comes with an identification

`θ_N : Hom(L, N) ≃ Hom(E, Φ(N))`, natural in `N ∈ D^+_{QCoh}(𝒪_S)`

(`Stacks.Cohomology.RelativeExt.pseudoCoherentRepresentativeHomEquiv`), which induces
isomorphisms `Ext^i_{𝒪_S}(L, ℱ) ≅ Ext^i_{𝒪_X}(E, 𝒢 ⊗ f^*ℱ)` as in (B) for quasi-coherent `ℱ`
(`Stacks.Cohomology.RelativeExtCanonical.extIsoOfIdentification`). The first assertion of
[Stacks, Tag 0DJS] is that `L` is canonical: any `L'` with quasi-coherent cohomology carrying such
an identification `θ'` is isomorphic to `L` by an isomorphism `φ : L' ≅ L` carrying `θ'` to `θ`,
and hence carrying the induced `Ext`-isomorphisms of `L'` to those of `L`.

## Main results

* `Stacks.Cohomology.RelativeExtCanonical.exists_iso_pseudoCoherentRepresentative`:
  [Stacks, Tag 0DJS], canonicity of `L`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Cohomology.RelativeExtCanonical

open Stacks.Cohomology.RelativeExt

attribute [local instance] hasSheafifyOpensSpace wEqualsLocallyBijectiveOpensSpace

/-- A pseudo-coherent object of `D(𝒪_S)` lies in `D_{QCoh}(𝒪_S)` ([Stacks, Tag 08E5]). -/
theorem qcohDerived_of_isPseudoCoherentObject {S : Scheme.{u}} (L : DStd S)
    (hL : IsPseudoCoherentObject L) : qcohDerived S L :=
  @isQuasicoherentDerived_of_isPseudoCoherent S (HasDerivedCategory.standard _) L hL

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [LocallyOfFiniteType f]

/-- **The pseudo-coherent complex `L` representing relative `Ext` is canonical.**
Let `S` be Noetherian, `f : X ⟶ S` locally of finite type, `E ∈ D^-_{Coh}(𝒪_X)` and `𝒢` a bounded
complex of coherent `𝒪_X`-modules, flat over `S`, with support proper over `S`; let `L` be the
pseudo-coherent complex `pseudoCoherentRepresentative f E hE G hG`, with its identification
`θ_N : Hom(L, N) ≃ Hom(E, Lf^*N ⊗^L 𝒢)`, natural in `N ∈ D^+_{QCoh}(𝒪_S)`, and the
isomorphisms `Ext^i_{𝒪_S}(L, ℱ) ≅ Ext^i_{𝒪_X}(E, 𝒢 ⊗ f^*ℱ)` it induces. Then these are
functorial in quasi-coherent `ℱ` and compatible with boundary maps, and for every `L'` with
quasi-coherent cohomology and every identification
`θ'_N : Hom(L', N) ≃ Hom(E, Lf^*N ⊗^L 𝒢)` natural in `N ∈ D^+_{QCoh}(𝒪_S)` there is an
isomorphism `φ : L' ≅ L` with `θ'(φ ∘ x) = θ(x)` for all such `N` and `x : L ⟶ N`; in particular
`φ` carries the `Ext`-isomorphisms induced by `θ'` to those of `L`. -/
@[stacks 0DJS "canonical"]
theorem exists_iso_pseudoCoherentRepresentative (E : DStd X) (hE : IsBoundedAboveCoherent E)
    (G : CochainComplex (TModules X.toRingedSpace) ℤ)
    (hG : Stacks.Cohomology.PerfectPushforward.FlatProperSupportComplex f G) :
    IsPseudoCoherentObject (pseudoCoherentRepresentative f E hE G hG) ∧
    (∀ (i : ℤ) (F F' : SheafOfModules.{u} (structureSheafRing S.toRingedSpace))
        (hF : F.IsQuasicoherent) (hF' : F'.IsQuasicoherent) (v : F ⟶ F')
        (z : baseExtGroup (pseudoCoherentRepresentative f E hE G hG) F i),
      extIsoOfIdentification (isBoundedFlatOver_of_flatProperSupportComplex hG)
          ((pseudoCoherentRepresentativeHomEquiv f E hE G hG).toIdentification
            (plusQCohDerived_biprod S)) i F' hF'
          (baseExtMap (pseudoCoherentRepresentative f E hE G hG) i v z) =
        relativeExtMap f G E i v
          (extIsoOfIdentification (isBoundedFlatOver_of_flatProperSupportComplex hG)
            ((pseudoCoherentRepresentativeHomEquiv f E hE G hG).toIdentification
              (plusQCohDerived_biprod S)) i F hF z)) ∧
    (∀ (A : ShortComplex (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)))
        (hA : A.ShortExact) (h₁ : A.X₁.IsQuasicoherent) (h₃ : A.X₃.IsQuasicoherent)
        (n m : ℤ) (h : 1 + n = m)
        (z : baseExtGroup (pseudoCoherentRepresentative f E hE G hG) A.X₃ n),
      extIsoOfIdentification (isBoundedFlatOver_of_flatProperSupportComplex hG)
          ((pseudoCoherentRepresentativeHomEquiv f E hE G hG).toIdentification
            (plusQCohDerived_biprod S)) m A.X₁ h₁
          (baseExtBoundaryMap (pseudoCoherentRepresentative f E hE G hG) hA n m h z) =
        relativeExtBoundaryMap E (isBoundedFlatOver_of_flatProperSupportComplex hG) hA n m h
          (extIsoOfIdentification (isBoundedFlatOver_of_flatProperSupportComplex hG)
            ((pseudoCoherentRepresentativeHomEquiv f E hE G hG).toIdentification
              (plusQCohDerived_biprod S)) n A.X₃ h₃ z)) ∧
    ∀ (L' : DStd S) (_ : qcohDerived S L')
      (θ' : ShiftedHom.NaturalHomEquiv (𝟭 (DStd S))
        (pullbackTensorDerivedFunctor (isBoundedFlatOver_of_flatProperSupportComplex hG)) L' E
        (plusQCohDerived S)),
      ∃ φ : L' ≅ pseudoCoherentRepresentative f E hE G hG,
        (∀ (N : DStd S) (hN : plusQCohDerived S N)
            (x : pseudoCoherentRepresentative f E hE G hG ⟶ N),
          θ'.equiv N hN (φ.hom ≫ x) =
            (pseudoCoherentRepresentativeHomEquiv f E hE G hG).equiv N hN x) ∧
        ∀ (i : ℤ) (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace))
          (hF : F.IsQuasicoherent)
          (z : baseExtGroup (pseudoCoherentRepresentative f E hE G hG) F i),
          extIsoOfIdentification (isBoundedFlatOver_of_flatProperSupportComplex hG)
              (θ'.toIdentification (plusQCohDerived_biprod S)) i F hF (φ.hom ≫ z) =
            extIsoOfIdentification (isBoundedFlatOver_of_flatProperSupportComplex hG)
              ((pseudoCoherentRepresentativeHomEquiv f E hE G hG).toIdentification
                (plusQCohDerived_biprod S)) i F hF z := by
  refine ⟨isPseudoCoherent_pseudoCoherentRepresentative f E hE G hG,
    fun i F F' hF hF' v z ↦ extIsoOfIdentification_naturality _ _ i hF hF' v z,
    fun A hA h₁ h₃ n m h z ↦ extIsoOfIdentification_boundary _ _ hA h₁ h₃ n m h z,
    fun L' hL' θ' ↦ ?_⟩
  have hL := qcohDerived_of_isPseudoCoherentObject _
    (isPseudoCoherent_pseudoCoherentRepresentative f E hE G hG)
  obtain ⟨φ, hφ⟩ := exists_iso_of_representing_dStd
    (pullbackTensorDerivedFunctor (isBoundedFlatOver_of_flatProperSupportComplex hG)) E
    (plusQCohDerived S) (fun _ hN ↦ hN.2) _ L' hL hL'
    (fun n ↦ plusQCohDerived_truncGE _ hL _) (fun n ↦ plusQCohDerived_truncGE _ hL' _)
    (pseudoCoherentRepresentativeHomEquiv f E hE G hG).equiv
    (pseudoCoherentRepresentativeHomEquiv f E hE G hG).naturality θ'.equiv θ'.naturality
  exact ⟨φ, hφ, extIsoOfIdentification_comp_of_iso _ _ θ' φ hφ⟩

end Stacks.Cohomology.RelativeExtCanonical

end
