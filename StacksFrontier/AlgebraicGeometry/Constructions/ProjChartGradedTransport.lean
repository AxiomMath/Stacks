module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartFullGraded
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartPullbackCotensorator
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTripleClassifyingMorphism

/-!
# Transporting a datum of graded sections along an isomorphism, and along a pullback

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring and `L` an invertible module on a scheme `T`. A datum of
graded sections `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections 𝒜 L` is the input of
[Stacks, Tag 01NK]: a degreewise family of additive maps `𝒜 n ⟶ Γ(L^{⊗ n}, ⊤)` which is
multiplicative for the product
`Stacks.AlgebraicGeometry.ProjChartFromRatios.mulSections` of the section ring of [Stacks,
Tag 01CV].

This file transports such a datum along an isomorphism `β : L ≅ L'` of invertible modules on
`T`, composing its components with the tensor powers `β^{⊗ n}`, and along a morphism of schemes
`j : T' ⟶ T`, composing its components with
`Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullSection`. The nonvanishing open of a
transported section is the corresponding open of the original one, respectively its preimage
under `j`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.congrModule`: the datum
  transported along an isomorphism of invertible modules.
* `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.pullback`: the datum
  transported along a morphism of schemes.

## Main results

* `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.nonvanishingOpenAt_congrModule`:
  transport along an isomorphism does not change the nonvanishing opens.
* `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.coveringOpen_congrModule`:
  transport along an isomorphism does not change `U(ψ)`.
* `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.nonvanishingOpenAt_pullback`:
  the nonvanishing opens of the inverse-image datum are the preimages of the original ones.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite MonoidalCategory
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjChartFromRatios (mulSections)
open Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator (pullSection_mulSections)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullSection nonvanishingOpen_pullSection)
open Stacks.AlgebraicGeometry.ProjTripleClassifying (mulSections_natTensorPowCongr)
open Stacks.AmplePullbackPart1 (natTensorPowCongr)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowers (natTensorPow)

universe u w

namespace Stacks.AlgebraicGeometry.ProjChartFullGraded

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

namespace GradedSections

/-! ### Transport along an isomorphism of invertible modules -/

section Congr

variable {T : Scheme.{u}} {L L' : T.Modules} (β : L ≅ L') (ψ : GradedSections 𝒜 L)

/-- The degree-`n` component of a datum of graded sections transported along an isomorphism
`β : L ≅ L'`: the original component followed by the `n`-th tensor power of `β` on global
sections. -/
def congrModuleHom (n : ℕ) : 𝒜 n →+ Γ(natTensorPow L' n, ⊤) :=
  AddMonoidHom.mk' (fun a => (natTensorPowCongr β n).hom.app ⊤ (ψ.toFun n a))
    (fun a b => by simp only [map_add])

/-- The value of `congrModuleHom β ψ n` at `a` is the image of `ψ(a)` under `β^{⊗ n}`. -/
@[simp] theorem congrModuleHom_apply (n : ℕ) (a : 𝒜 n) :
    congrModuleHom β ψ n a = (natTensorPowCongr β n).hom.app ⊤ (ψ.toFun n a) :=
  rfl

/-- A datum of graded sections for `L` transported along an isomorphism `β : L ≅ L'` of invertible
modules: its components are those of `ψ` followed by the tensor powers of `β`. -/
def congrModule : GradedSections 𝒜 L' where
  toFun := congrModuleHom β ψ
  map_mul n m a b ab hab := (congrArg _ (ψ.map_mul n m a b ab hab)).trans
    (mulSections_natTensorPowCongr β n m (ψ.toFun n a) (ψ.toFun m b))

/-- The degree-`n` component of `congrModule β ψ` sends `a` to the image of `ψ(a)` under
`β^{⊗ n}`. -/
@[simp] theorem congrModule_toFun (n : ℕ) (a : 𝒜 n) :
    (congrModule β ψ).toFun n a = (natTensorPowCongr β n).hom.app ⊤ (ψ.toFun n a) :=
  rfl

variable [Stacks.Ample.IsInvertibleModule T L] [Stacks.Ample.IsInvertibleModule T L']

/-- The nonvanishing open `T_{ψ(f)}` of a datum of graded sections is unchanged by transport
along an isomorphism of invertible modules. -/
theorem nonvanishingOpenAt_congrModule (e : ℕ) (f : 𝒜 e) :
    (congrModule β ψ).nonvanishingOpenAt e f = ψ.nonvanishingOpenAt e f :=
  TopologicalSpace.Opens.ext
    (Stacks.Ample.nonvanishingLocus_congr (natTensorPowCongr β e) (ψ.toFun e f))

/-- The open `U(ψ)` of a datum of graded sections is unchanged by transport along an isomorphism
of invertible modules. -/
theorem coveringOpen_congrModule : (congrModule β ψ).coveringOpen = ψ.coveringOpen :=
  iSup_congr fun p => nonvanishingOpenAt_congrModule β ψ (p.1 + 1) p.2

end Congr

/-! ### Transport along a morphism of schemes: the inverse-image datum -/

section Pullback

variable {T T' : Scheme.{u}} (j : T' ⟶ T) {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L)

/-- The degree-`n` component of the inverse image of a datum of graded sections along a morphism
of schemes `j : T' ⟶ T`: the original component followed by the pullback of a global section of
`L^{⊗ n}`, read as a global section of `(j^*L)^{⊗ n}`. -/
def pullbackHom (n : ℕ) :
    𝒜 n →+ Γ(natTensorPow ((Scheme.Modules.pullback j).obj L) n, ⊤) :=
  AddMonoidHom.mk' (fun a => pullSection j L n (ψ.toFun n a))
    (fun a b => by simp only [map_add, pullSection])

/-- The value of `pullbackHom j ψ n` at `a` is the pullback of `ψ(a)` along `j`. -/
@[simp] theorem pullbackHom_apply (n : ℕ) (a : 𝒜 n) :
    pullbackHom j ψ n a = pullSection j L n (ψ.toFun n a) :=
  rfl

/-- The inverse image of a datum of graded sections along a morphism of schemes `j : T' ⟶ T`: its
components are those of `ψ` followed by the pullback of global sections along `j`. -/
def pullback : GradedSections 𝒜 ((Scheme.Modules.pullback j).obj L) where
  toFun := pullbackHom j ψ
  map_mul n m a b ab hab := (congrArg _ (ψ.map_mul n m a b ab hab)).trans
    (pullSection_mulSections j L (ψ.toFun n a) (ψ.toFun m b))

/-- The degree-`n` component of `pullback j ψ` sends `a` to the pullback of `ψ(a)` along `j`. -/
@[simp] theorem pullback_toFun (n : ℕ) (a : 𝒜 n) :
    (pullback j ψ).toFun n a = pullSection j L n (ψ.toFun n a) :=
  rfl

variable [Stacks.Ample.IsInvertibleModule T' ((Scheme.Modules.pullback j).obj L)]

/-- The nonvanishing opens of the inverse-image datum are the preimages of the original ones. -/
theorem nonvanishingOpenAt_pullback (e : ℕ) (f : 𝒜 e) :
    (pullback j ψ).nonvanishingOpenAt e f = j ⁻¹ᵁ ψ.nonvanishingOpenAt e f :=
  nonvanishingOpen_pullSection j L e (ψ.toFun e f)

end Pullback

end GradedSections

end Stacks.AlgebraicGeometry.ProjChartFullGraded

end
