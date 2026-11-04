module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCanonical.BaseChangeTotal
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCanonical.Canonicity
import StacksCore.Tactic.StacksAttribute

/-!
# Formation of the complex `L` of [Stacks, Tag 08IF] (B) commutes with base change

Let `S` be Noetherian, `f : X ⟶ S` locally of finite type, `E ∈ D^-_{Coh}(𝒪_X)` and `𝒢` a bounded
complex of coherent `𝒪_X`-modules, flat over `S`, with support proper over `S`, and let `L` be the
pseudo-coherent complex of (B). For a cartesian square

`X' --g'--> X`, `f' : X' ⟶ S'`, `f : X ⟶ S`, `S' --g--> S`

there are canonical isomorphisms

`Ext^i_{𝒪_{S'}}(Lg^*L, ℱ') ≅ Ext^i_{𝒪_{X'}}(L(g')^*E, (g')^*𝒢 ⊗_{𝒪_{X'}} (f')^*ℱ')`

for quasi-coherent `ℱ'` on `S'`, functorial in `ℱ'` and compatible with boundary maps, with the
ordinary (not derived) pullback `(g')^*𝒢` of the complex `𝒢` on the right. This is the second
assertion of [Stacks, Tag 0DJS]. They are induced by the identification
`Hom(Lg^*L, N) ≃ Hom(L(g')^*E, L(f')^*N ⊗^L (g')^*𝒢)`, natural in `N ∈ D^+_{QCoh}(𝒪_{S'})`, of
`Stacks.Cohomology.RelativeExtCanonical.baseChangeHomEquiv`.

## Main definitions

* `Stacks.Cohomology.RelativeExtCanonical.baseChangedRepresentative`: `Lg^*L`.
* `Stacks.Cohomology.RelativeExtCanonical.baseChangedSource`: `L(g')^*E`.
* `Stacks.Cohomology.RelativeExtCanonical.pseudoCoherentRepresentativeBaseChangeHomEquiv`: the
  identification on `D^+_{QCoh}(𝒪_{S'})`.
* `Stacks.Cohomology.RelativeExtCanonical.baseChangeExtIso`: the isomorphisms of `Ext`-groups.

## Main results

* `Stacks.Cohomology.RelativeExtCanonical.exists_baseChange_relativeExt_iso`:
  [Stacks, Tag 0DJS], base change.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Cohomology.RelativeExtCanonical

open Stacks.Cohomology.RelativeExt

attribute [local instance] hasSheafifyOpensSpace wEqualsLocallyBijectiveOpensSpace

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [LocallyOfFiniteType f]
  (E : DStd X) (hE : IsBoundedAboveCoherent E) (G : CochainComplex (TModules X.toRingedSpace) ℤ)
  (hG : Stacks.Cohomology.PerfectPushforward.FlatProperSupportComplex f G)
  {S' X' : Scheme.{u}} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X} (hsq : IsPullback g' f' f g)

variable (g) in
/-- **`Lg^*L`**, the derived pullback along `g : S' ⟶ S` of the complex `L` of
[Stacks, Tag 08IF] (B). -/
def baseChangedRepresentative : DStd S' :=
  (stdPullback g.toLRSHom.toShHom).obj (pseudoCoherentRepresentative f E hE G hG)

variable (g') in
/-- **`L(g')^*E`**, the derived pullback of `E` along `g' : X' ⟶ X`. -/
def baseChangedSource : DStd X' := (stdPullback g'.toLRSHom.toShHom).obj E

/-- **The base-change identification for the complex `L` of [Stacks, Tag 08IF] (B)**:
`Hom(Lg^*L, N) ≃ Hom(L(g')^*E, L(f')^*N ⊗^L (g')^*𝒢)`, naturally in `N ∈ D^+_{QCoh}(𝒪_{S'})`. -/
def pseudoCoherentRepresentativeBaseChangeHomEquiv :
    ShiftedHom.NaturalHomEquiv (𝟭 (DStd S'))
      (pullbackTensorDerivedFunctor (isBoundedFlatOver_total_pullback hsq hG))
      (baseChangedRepresentative f E hE G hG g)
      (baseChangedSource E g') (plusQCohDerived S') :=
  baseChangeHomEquiv hsq (partBWitness f E hE G hG)

/-- **The base-change isomorphisms of [Stacks, Tag 0DJS]**:
`Ext^i_{𝒪_{S'}}(Lg^*L, ℱ') ≃+ Ext^i_{𝒪_{X'}}(L(g')^*E, (g')^*𝒢 ⊗ (f')^*ℱ')` for quasi-coherent
`ℱ'`, induced by `pseudoCoherentRepresentativeBaseChangeHomEquiv`. -/
def baseChangeExtIso (i : ℤ) (F' : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (hF' : F'.IsQuasicoherent) :
    baseExtGroup (baseChangedRepresentative f E hE G hG g) F' i ≃+
      relativeExtGroup f'
        ((Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex g'.toLRSHom.toShHom).obj G)
        (baseChangedSource E g') F' i :=
  extIsoOfIdentification (isBoundedFlatOver_total_pullback hsq hG)
    ((pseudoCoherentRepresentativeBaseChangeHomEquiv f E hE G hG hsq).toIdentification
      (plusQCohDerived_biprod S')) i F' hF'

/-- **[Stacks, Tag 0DJS]: formation of the complex `L` of [Stacks, Tag 08IF] (B) is compatible
with base change.** Let `S` be Noetherian, `f : X ⟶ S` locally of finite type,
`E ∈ D^-_{Coh}(𝒪_X)` and `𝒢` a bounded complex of coherent `𝒪_X`-modules, flat over `S`, with
support proper over `S`, and let `L` be the pseudo-coherent complex of (B). For every cartesian
square of schemes with `g' : X' ⟶ X`, `f' : X' ⟶ S'`, `g : S' ⟶ S` there are isomorphisms

`Ext^i_{𝒪_{S'}}(Lg^*L, ℱ') ≅ Ext^i_{𝒪_{X'}}(L(g')^*E, (g')^*𝒢 ⊗_{𝒪_{X'}} (f')^*ℱ')`

for quasi-coherent `ℱ'` on `S'`, with `(g')^*𝒢` the ordinary termwise pullback of `𝒢`, which are
functorial in `ℱ'` and compatible with the boundary maps of short exact sequences. They are
canonical: they are the ones induced by an identification
`Hom(Lg^*L, N) ≃ Hom(L(g')^*E, L(f')^*N ⊗^L (g')^*𝒢)` natural in `N ∈ D^+_{QCoh}(𝒪_{S'})`. -/
@[stacks 0DJS "base change"]
theorem exists_baseChange_relativeExt_iso :
    ∃ β : ∀ (i : ℤ) (F' : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)),
        F'.IsQuasicoherent →
        (baseExtGroup (baseChangedRepresentative f E hE G hG g) F' i ≃+
          relativeExtGroup f'
            ((Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex g'.toLRSHom.toShHom).obj G)
            (baseChangedSource E g') F' i),
      (∀ (i : ℤ) (F F' : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
          (hF : F.IsQuasicoherent) (hF' : F'.IsQuasicoherent) (v : F ⟶ F')
          (z : baseExtGroup (baseChangedRepresentative f E hE G hG g) F i),
        β i F' hF' (baseExtMap _ i v z) =
          relativeExtMap f'
            ((Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex g'.toLRSHom.toShHom).obj G)
            (baseChangedSource E g') i v (β i F hF z)) ∧
      (∀ (A : ShortComplex (SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)))
          (hA : A.ShortExact) (h₁ : A.X₁.IsQuasicoherent) (h₃ : A.X₃.IsQuasicoherent)
          (n m : ℤ) (h : 1 + n = m)
          (z : baseExtGroup (baseChangedRepresentative f E hE G hG g) A.X₃ n),
        β m A.X₁ h₁ (baseExtBoundaryMap _ hA n m h z) =
          relativeExtBoundaryMap (baseChangedSource E g')
            (isBoundedFlatOver_total_pullback hsq hG) hA n m h (β n A.X₃ h₃ z)) ∧
      ∃ θ : ShiftedHom.NaturalHomEquiv (𝟭 (DStd S'))
          (pullbackTensorDerivedFunctor (isBoundedFlatOver_total_pullback hsq hG))
          (baseChangedRepresentative f E hE G hG g)
          (baseChangedSource E g') (plusQCohDerived S'),
        ∀ (i : ℤ) (F' : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
          (hF' : F'.IsQuasicoherent),
          β i F' hF' = extIsoOfIdentification (isBoundedFlatOver_total_pullback hsq hG)
            (θ.toIdentification (plusQCohDerived_biprod S')) i F' hF' :=
  ⟨baseChangeExtIso f E hE G hG hsq,
    fun i _ _ hF hF' v z ↦ extIsoOfIdentification_naturality _ _ i hF hF' v z,
    fun _ hA h₁ h₃ n m h z ↦ extIsoOfIdentification_boundary _ _ hA h₁ h₃ n m h z,
    pseudoCoherentRepresentativeBaseChangeHomEquiv f E hE G hG hsq, fun _ _ _ ↦ rfl⟩

end Stacks.Cohomology.RelativeExtCanonical

end
