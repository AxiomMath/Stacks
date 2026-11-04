module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.BaseIsoTransport
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.C1018Assembly
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AffineLocalTransport
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ChowTransportResidual

/-!
# Stacks 088B, 088C, `hDev` and 088E through the transport of the base iso

`CompletionProper/C1018Assembly.lean` records that the two halves of the route to [Stacks, Tag
088C], `hDev` and [Stacks, Tag 088E] stand on opposite sides of **one** transport, and names the
two ways across. This file takes the second one — "route 2" of that docstring — and chains it into
the conclusions, so that `Stacks.Algebraization.HasAdicCompletionChartBaseChange`, the hypothesis
the first way needs, is not used at all.

## The chain

Over an affine open `V ⊆ X` of the base, with `B = Γ(X, V)`, `e = V.2.isoSpec : V ≅ Spec B` and
`π : X' ⟶ X` proper, the square

```
π ⁻¹ V  --- 𝟙 --->  π ⁻¹ V
   |                   |
(π ∣_ V) ≫ e.hom     π ∣_ V
   v                   v
 Spec B  -- e.inv -->   V
```

commutes (`Stacks.Algebraization.morphismRestrict_isoSpec_square`) and its two horizontal
morphisms are isomorphisms, so
`Stacks.Algebraization.exists_isDirectImageCharacterized_of_isoSquare` applies to it. Its input
`α₂` — the second paragraph of Stacks 088B for `(π ∣_ V) ≫ e.hom` over `Spec B`, at the base
change of `Stacks.Coherent.restrictDirectImageIso` along the square — is exactly what
`Stacks.Algebraization.exists_isDirectImageCharacterized_isKernelCokernel_of_adicBaseChangeGamma`
produces, and its output `α` is exactly what
`Stacks.Algebraization.hasAffineLocalDirectImageSolution_of_morphismRestrict` consumes. Three
things join them:

* **the ideal sheaf.** The producer states the paragraph at `J 𝒪_{Spec B}`
  (`Stacks.Algebraization.adicIdealSheaf`) and the transport asks for `(𝒥|_V)` pulled back along
  `e.inv`; the two agree by `Stacks.Algebraization.adicIdealSheaf_eq_comap_isoSpec_inv`, which is
  `Stacks.Algebraization.comap_adicIdealSheaf_isoSpec` read on the other side of `e`. The
  agreement is propositional, so the producer is restated with the ideal sheaf *and* the equation
  as binders (`…adicBaseChangeGamma_of_eq`) and the equation is substituted inside: putting a
  non-definitional transport into a statement one also proves in the same declaration is what the
  kernel cannot afford here.
* **the annihilation, carried back along `e.inv`.** The transport pins its `α` down by its
  pullback along `e.inv` being `α₂ ≫ ι`, and `ι` is an isomorphism
  (`Stacks.Algebraization.isIso_isoSquareCompletedComparison`), so the annihilation of `α₂` is the
  annihilation of `α₂ ≫ ι` (`Stacks.Coherent.isKernelCokernelAnnihilatedByPower_comp_iso_iff`) and
  comes home by `Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_of_pullback_app` at
  `e.inv`, whose flatness and faithfulness are both free for an isomorphism — pullback along an
  isomorphism is an equivalence
  (`AlgebraicGeometry.Scheme.Modules.isEquivalence_pullback_of_isIso`), hence faithful.
* **`hc`.** The source's own condition on the unit of the adjunction of the base change away from
  the support, which is a binder in every statement of this paragraph in the tree and in the
  source's own statement of 088B. It is the only hypothesis left.

## Main results

* `exists_isDirectImageCharacterized_isKernelCokernel_morphismRestrict_of_route2`
  — the local solution of Stacks 088B **for the restricted morphism `π ∣_ V`**, with `hc` as its
  only hypothesis. This is "the geometric half of piece 1" of
  `CompletionProper/AffineLocalTransport.lean`.
* `Stacks.Algebraization.HasAdicBaseChangeUnitCondition` — `hc`, quantified over the data of
  `Stacks.Algebraization.HasAffineLocalDirectImageSolution` and over the affine opens of the base.
* `Stacks.Algebraization.hasAffineLocalDirectImageSolution_of_adicBaseChangeUnitCondition` and
  `…isDirectImageComparison_of_adicBaseChangeUnitCondition` —
  `Stacks.Algebraization.HasAffineLocalDirectImageSolution` and
  `Stacks.Algebraization.IsDirectImageComparison` from `hc` alone.
* `Stacks.Algebraization.isEquivalence_completionFunctor_of_adicBaseChangeUnitCondition` —
  [Stacks, Tag 088C] from `hc` alone.
* `Stacks.Algebraization.hDev_of_adicBaseChangeUnitCondition` — the binder `hDev` of [Stacks, Tag
  088E] from `hc` alone.
* `Stacks.Algebraization.isEquivalence_completionFunctorProperOver_of_adicBaseChangeUnitCondition`
  — [Stacks, Tag 088E] from `hc` alone. **Both** named inputs of
  `Stacks.Algebraization.isEquivalence_completionFunctorProperOver_of_isDirectImageComparison` are
  discharged: `hDev` here, and `hTransport` by
  `Stacks.Algebraization.transport_of_isDirectImageComparison`, so the Chow residual is gone from
  this route too.

## What is no longer used

`Stacks.Algebraization.HasAdicCompletionChartBaseChange` — the base change of `π ∣_ V` along the
completion chart together with its two squares — is not a hypothesis of anything here. The
corresponding assemblies of `CompletionProper/C1018Assembly.lean` and
`CompletionProper/ChowTransportResidual.lean` remain as they are; this file reaches the same
conclusions from the second paragraph over an affine base, which is proved, plus `hc`.

No `stacks` attribute is attached anywhere in this file: every result is an assembly, a
restatement or a reduction of a hypothesis, and the tags of the statements involved are registered
on the declarations the docstrings below name.

## References

* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
* [Stacks Project, Tag 088E](https://stacks.math.columbia.edu/tag/088E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

open Stacks.Coherent

/-! ### Step 1: the second paragraph over an affine base, with the ideal sheaf as a binder -/

section Restatement

variable (B : Type u) [CommRing B] [IsNoetherianRing B] (Jid : Ideal B)
  {X' : Scheme.{u}} [IsNoetherian X'] (π : X' ⟶ Spec (.of B)) [IsProper π]
  (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)

/-- **[Stacks, Tag 088B] over an affine base — the characterization and the annihilation — stated
with the ideal sheaf as a binder.** Let `B` be Noetherian, `Jid ⊆ B` an ideal, `π : X' ⟶ Spec B`
proper with `X'` Noetherian and `𝓕` a coherent `𝒪_{X'}`-module, and let `𝒥 ⊆ 𝒪_{Spec B}` be an
ideal sheaf *equal to* `Jid 𝒪_{Spec B}`. Granted the source's condition `hc`, every
`β : π^*(𝒢_n) ≅ 𝓕 ^∧` over `𝒥` admits an `α` characterized in the source's sense with its
levelwise kernels and cokernels annihilated by a power of `𝒦`.

This is `exists_isDirectImageCharacterized_isKernelCokernel_of_adicBaseChangeGamma` and nothing
else: one `subst` of `hJ`.

**Why the equation is a binder.** The consumer of this statement has its system, its `β` and its
`𝒦` over `(𝒥|_V)` pulled back along `(V.2.isoSpec)⁻¹`, which is `Jid 𝒪_{Spec B}` only
propositionally (`Stacks.Algebraization.adicIdealSheaf_eq_comap_isoSpec_inv`). Rewriting that
transport into the statement of a declaration whose proof also has to elaborate exceeds the
elaboration budget; with the ideal sheaf and the equation as binders the
substitution happens before anything else does, and the caller supplies the equation. -/
public theorem exists_isDirectImageCharacterized_isKernelCokernel_adicBaseChangeGamma_of_eq
    {𝒥 : (Spec (.of B)).IdealSheafData} (hJ : adicIdealSheaf B Jid = 𝒥)
    (G : CoherentAdicSystems 𝒥)
    (β : (coherentAdicPullback π 𝒥).obj G ≅ (completionFunctor X' (𝒥.comap π)).obj 𝓕)
    (K : (Spec (.of B)).IdealSheafData)
    (hc : ∀ 𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules
        (Spec (.of (AdicCompletion Jid B))).ringCatSheaf,
      ((coherentAdicPullback (adicCompletionSpecMap B Jid) 𝒥).obj G ≅
          (completionFunctor (Spec (.of (AdicCompletion Jid B)))
            (𝒥.comap (adicCompletionSpecMap B Jid))).obj 𝒜) →
        IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι
            (K.comap (adicCompletionSpecMap B Jid)).support.compl)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            (adicBaseChangeMap B Jid π)).unit.app 𝒜.obj))) :
    ∃ α : G.obj ⟶ ((completionFunctor (Spec (.of B)) 𝒥).obj
        (properPushforwardCoherent π 𝓕)).obj,
      IsDirectImageCharacterized π 𝒥 G 𝓕 β α ∧
        IsKernelCokernelAnnihilatedByPower K α := by
  subst hJ
  exact exists_isDirectImageCharacterized_isKernelCokernel_of_adicBaseChangeGamma B Jid π 𝓕 G β
    K hc

end Restatement

/-! ### The ideal sheaf of `Spec Γ(X, V)` as the inverse image along `isoSpec.inv` -/

section IdealSheaf

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (J : X.IdealSheafData) {V : X.Opens}
  (hV : IsAffineOpen V)

/-- **The ideal sheaf `𝒥(V) 𝒪` of `Spec Γ(X, V)` is the inverse image of `𝒥|_V` along the
inverse of `AlgebraicGeometry.IsAffineOpen.isoSpec`.** For an affine open `V ⊆ X`,

`Stacks.Algebraization.adicIdealSheaf Γ(X, V) (𝒥(V)) = (𝒥|_V) ⁻¹` along `(isoSpec)⁻¹`.

`Stacks.Algebraization.comap_adicIdealSheaf_isoSpec` says the same on the other side of `e`, that
the inverse image along `e.hom` of the left-hand side is `𝒥|_V`; taking inverse images along
`e.inv` and collapsing `e.inv ≫ e.hom = 𝟙` gives this form, which is the one the transport of the
second paragraph along `e` consumes — its ideal sheaf on `Spec Γ(X, V)` is by construction an
inverse image along `e.inv`. **Unconditional.** -/
public theorem adicIdealSheaf_eq_comap_isoSpec_inv :
    adicIdealSheaf ↥Γ(X, V) (J.ideal ⟨V, hV⟩) = (J.comap V.ι).comap hV.isoSpec.inv := by
  rw [← comap_adicIdealSheaf_isoSpec J hV, ← Scheme.IdealSheafData.comap_comp,
    hV.isoSpec.inv_hom_id, Scheme.IdealSheafData.comap_id]

end IdealSheaf

/-! ### The comparison `ι` of the base-iso square is an isomorphism -/

section IsoComparison

variable {X X₂ Y Y₂ : Scheme.{u}} [IsNoetherian X] [IsNoetherian X₂] [IsNoetherian Y]
  [IsNoetherian Y₂] (f : X ⟶ Y) [IsProper f] (g : Y₂ ⟶ Y) [IsIso g] (f₂ : X₂ ⟶ Y₂)
  [IsProper f₂] (g' : X₂ ⟶ X) [IsIso g'] (w : g' ≫ f = f₂ ≫ g) (K : Y.IdealSheafData)
  (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)

include w

/-- **The comparison `ι` of the two completed direct images across a square whose horizontal
morphisms are isomorphisms is itself an isomorphism.**
`Stacks.Algebraization.isoSquareCompletedComparison` is by construction the completion of the
identification `Stacks.Algebraization.isoSquareProperPushforwardIso` of the two direct images —
which is an isomorphism because `Stacks.Algebraization.isIso_pushforwardBaseChange_of_isIso`
supplies the degree-zero base change with no flatness or cartesianness hypothesis — followed by
the identification `(g^*𝒜) ^∧ ≅ g^*(𝒜 ^∧)` of [Stacks, Tag 0887]
(`Stacks.Coherent.completionPullbackIso`); and the `.hom` of an isomorphism of coherent adic
systems is an isomorphism of the underlying inverse systems.

This is the `Stacks.Algebraization.isIso_adicBaseChangeCompletedComparison` of the base-iso square,
and it is what the annihilation half of Stacks 088B asks of `ι`: composing with a bare morphism
changes the levelwise kernels and cokernels, composing with an isomorphism does not
(`Stacks.Coherent.isKernelCokernelAnnihilatedByPower_comp_iso_iff`). -/
public theorem isIso_isoSquareCompletedComparison :
    IsIso (isoSquareCompletedComparison f g f₂ g' w K F) := by
  unfold isoSquareCompletedComparison
  infer_instance

end IsoComparison

/-! ### Route 2 at one affine open of the base -/

section Route2

variable {X' X : Scheme.{u}} [IsNoetherian X'] [IsNoetherian X] (π : X' ⟶ X) [IsProper π]
  (J K : X.IdealSheafData) (G : CoherentAdicSystems J)
  (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)
  (β : (coherentAdicPullback π J).obj G ≅ (completionFunctor X' (J.comap π)).obj 𝓕)
  (V : X.affineOpens) [IsNoetherianRing ↥Γ(X, V.1)]

/-- **The square of the affine open and its spectrum.** For `V ⊆ X` an affine open and
`e = V.2.isoSpec : V ≅ Spec Γ(X, V)`,

`𝟙 ≫ (π ∣_ V) = ((π ∣_ V) ≫ e.hom) ≫ e.inv`,

the commuting square whose two horizontal morphisms — `𝟙` upstairs and `e.inv` downstairs — are
isomorphisms, and which `Stacks.Algebraization.exists_isDirectImageCharacterized_of_isoSquare` is
read at. Nothing happens upstairs: the scheme `π ⁻¹ V` and the module on it are untouched by the
transport, only the base travels. -/
public theorem morphismRestrict_isoSpec_square :
    𝟙 (π ⁻¹ᵁ V.1).toScheme ≫ (π ∣_ V.1) =
      ((π ∣_ V.1) ≫ V.2.isoSpec.hom) ≫ V.2.isoSpec.inv := by
  rw [Category.id_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **Route 2 at one affine open: the local solution of [Stacks, Tag 088B] for the restricted
morphism, from the second paragraph over `Spec Γ(X, V)` carried back along
`AlgebraicGeometry.IsAffineOpen.isoSpec`.** Let `π : X' ⟶ X` be proper between Noetherian
schemes, `𝒥, 𝒦 ⊆ 𝒪_X` quasi-coherent, `(𝒢_n)` an object of `Coh(X, 𝒥)`, `𝓕` a coherent
`𝒪_{X'}`-module, `β : π^*(𝒢_n) ≅ 𝓕 ^∧` and `V ⊆ X` an affine open. Granted the source's
condition `hc` over the completion of `B = Γ(X, V)`, there is a morphism `ψ` over `V` which is

* characterized in the sense of `Stacks.Coherent.IsDirectImageCharacterized` for the **restricted**
  morphism `π ∣_ V`, the restricted system, the restricted module and
  `Stacks.Coherent.restrictDirectImageIso`, and
* has its levelwise kernels and cokernels annihilated by a power of `𝒦|_V`.

**This is the datum `Stacks.Algebraization.hasAffineLocalDirectImageSolution_of_morphismRestrict`
consumes**, i.e. a solution of the problem of Stacks 088B *for `π ∣_ V` over `V`*, which is what
the source's second paragraph produces, as against a solution of the restricted problem, which the
glueing of the first paragraph consumes.

The proof is the chain the module docstring describes.
`…exists_isDirectImageCharacterized_isKernelCokernel_adicBaseChangeGamma_of_eq` at `B`, at the
proper morphism `(π ∣_ V) ≫ e.hom`, at the ideal sheaf `(𝒥|_V)` pulled back along `e.inv` — the
equation being `Stacks.Algebraization.adicIdealSheaf_eq_comap_isoSpec_inv` — at the pulled-back
system, at `𝓕|_{π ⁻¹ V}` pulled back along `𝟙` and at the base change
`Stacks.Algebraization.isoSquareAlgebraizationIso` of `Stacks.Coherent.restrictDirectImageIso`
gives the `α₂` and its annihilation by the power of `(𝒦|_V)` pulled back along `e.inv`.
`Stacks.Algebraization.exists_isDirectImageCharacterized_of_isoSquare` descends it to `V`, its
`θ` discharged by `rfl` at the point of use as that file's implementation notes prescribe. The
annihilation crosses the isomorphism `ι` and returns along `e.inv`, which is flat and faithful on
all of `V.toScheme.Modules` because it is an isomorphism.

No `stacks` attribute is attached: the second paragraph of Stacks 088B is registered on
`Stacks.Coherent.directImageComparison` and on
`Stacks.Algebraization.exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_isAffine`,
and this is the transport of that statement along an isomorphism of the base. -/
public theorem exists_isDirectImageCharacterized_isKernelCokernel_morphismRestrict_of_route2
    (hc : ∀ 𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules
        (Spec (.of (AdicCompletion (J.ideal V) ↥Γ(X, V.1)))).ringCatSheaf,
      ((coherentAdicPullback (adicCompletionSpecMap ↥Γ(X, V.1) (J.ideal V))
              ((J.comap V.1.ι).comap V.2.isoSpec.inv)).obj
            ((coherentAdicPullback V.2.isoSpec.inv (J.comap V.1.ι)).obj
              ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G)) ≅
          (completionFunctor (Spec (.of (AdicCompletion (J.ideal V) ↥Γ(X, V.1))))
            (((J.comap V.1.ι).comap V.2.isoSpec.inv).comap
              (adicCompletionSpecMap ↥Γ(X, V.1) (J.ideal V)))).obj 𝒜) →
        IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι
            ((((K.comap V.1.ι).comap V.2.isoSpec.inv).comap
              (adicCompletionSpecMap ↥Γ(X, V.1) (J.ideal V))).support.compl))).map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            (adicBaseChangeMap ↥Γ(X, V.1) (J.ideal V)
              ((π ∣_ V.1) ≫ V.2.isoSpec.hom))).unit.app 𝒜.obj))) :
    ∃ ψ : ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G).obj ⟶
        ((completionFunctor V.1.toScheme (J.comap V.1.ι)).obj
          (properPushforwardCoherent (π ∣_ V.1)
            (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕))).obj,
      IsDirectImageCharacterized (π ∣_ V.1) (J.comap V.1.ι)
          ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G)
          (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)
          (restrictDirectImageIso π V.1 J G 𝓕 β) ψ ∧
        IsKernelCokernelAnnihilatedByPower (K.comap V.1.ι) ψ := by
  have sq := morphismRestrict_isoSpec_square π V
  have ι := isIso_isoSquareCompletedComparison _ _ _ _ sq (J.comap V.1.ι)
    (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)
  obtain ⟨α₂, hα₂, hann₂⟩ :=
    exists_isDirectImageCharacterized_isKernelCokernel_adicBaseChangeGamma_of_eq
      ↥Γ(X, V.1) (J.ideal V) ((π ∣_ V.1) ≫ V.2.isoSpec.hom)
      ((pullbackCoherentModules (𝟙 (π ⁻¹ᵁ V.1).toScheme)).obj
        (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕))
      (adicIdealSheaf_eq_comap_isoSpec_inv J V.2)
      ((coherentAdicPullback V.2.isoSpec.inv (J.comap V.1.ι)).obj
        ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G))
      (isoSquareAlgebraizationIso _ _ _ _ sq (J.comap V.1.ι)
        (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)
        ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G)
        (restrictDirectImageIso π V.1 J G 𝓕 β))
      ((K.comap V.1.ι).comap V.2.isoSpec.inv) hc
  obtain ⟨α, hα, hpb⟩ :=
    exists_isDirectImageCharacterized_of_isoSquare _ _ _ _ sq (J.comap V.1.ι)
      (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)
      ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G)
      (restrictDirectImageIso π V.1 J G 𝓕 β) (fun _ => rfl) α₂ hα₂
  obtain ⟨t, ht, hkc⟩ :=
    (isKernelCokernelAnnihilatedByPower_comp_iso_iff
      ((K.comap V.1.ι).comap V.2.isoSpec.inv) α₂ (@asIso _ _ _ _ _ ι)).2 hann₂
  refine ⟨α, hα, isKernelCokernelAnnihilatedByPower_of_pullback_app V.2.isoSpec.inv
    (J.comap V.1.ι)
    (fun {_ _} _ _ {_ _} huv =>
      (Scheme.Modules.pullback V.2.isoSpec.inv).map_injective huv)
    (K.comap V.1.ι) α t ht (fun k => ?_) (fun k => ?_)⟩
  · exact cast (congrArg (fun z => idealPowerMultiple
      ((K.comap V.1.ι).comap V.2.isoSpec.inv) t (kernel z) = ⊥) (hpb (op k))).symm (hkc k).1
  · exact cast (congrArg (fun z => idealPowerMultiple
      ((K.comap V.1.ι).comap V.2.isoSpec.inv) t (cokernel z) = ⊥) (hpb (op k))).symm (hkc k).2

end Route2

/-! ### The whole residue of route 2: the source's condition `hc`, and nothing else -/

section Residue

open Stacks.Cohomology.FormalFunctions

/-- **The whole residue of route 2: the source's own condition `hc`, asked over the completion of
`Spec Γ(X, V)` for each affine open `V` of the base.**

For every proper `π : X' ⟶ X` of Noetherian schemes, every pair `𝒥, 𝒦` of quasi-coherent ideal
sheaves on `X`, every object `(𝒢_n)` of `Coh(X, 𝒥)`, every coherent `𝒪_{X'}`-module `𝓕`, every
`β : π^*(𝒢_n) ≅ 𝓕 ^∧`, granted the source's hypothesis that `π` is an isomorphism over
`X ∖ V(𝒦)`, and for every affine open `V ⊆ X` with `B = Γ(X, V)`: the unit of the adjunction of
the base change

`π' = ((π ∣_ V) ≫ e.hom) ×_{Spec B} Spec (B ^∧)`

is an isomorphism away from the support of the pullback of `(𝒦|_V)`, at every coherent module on
`Spec (B ^∧)` that algebraizes the pulled-back system.

**This is the source's own hypothesis, not a gap of the formalization.** It is the condition
labelled `hc` in the second paragraph of the proof of Stacks 088B, and it is a binder of every
statement of that paragraph in this tree —
`Stacks.Algebraization.exists_isDirectImageCharacterized_of_adicBaseChangeSquares`,
`…exists_isDirectImageCharacterized_of_adicBaseChangeGamma` and
`…exists_isDirectImageCharacterized_isKernelCokernel_of_adicBaseChangeGamma` all carry it.
`Stacks.Algebraization.isIso_restrictFunctor_map_pullbackPushforwardAdjunction_unit` proves it
from `IsIso (π' ∣_ U)` with no further hypothesis, so what stands between it and
`IsIso (π ∣_ K.support.compl)` is only the transport of *that* hypothesis to the base change,
together with the identification of the support of an inverse image; neither is done here or
anywhere in the tree.

What is **not** in this hypothesis is any part of the second paragraph itself, of the first
paragraph, of the glueing, of the descent, or of the annihilation: all of those are proved. In
particular `Stacks.Algebraization.HasAdicCompletionChartBaseChange` — the base change at the
completion chart and its two squares, which the other way across the transport needs — is not
asked for at all.

No `stacks` attribute is attached: this is a hypothesis, not a statement of the source. -/
public def HasAdicBaseChangeUnitCondition : Prop :=
  ∀ {X' X : Scheme.{u}} [IsNoetherian X'] [IsNoetherian X] (π : X' ⟶ X) [IsProper π]
    (J K : X.IdealSheafData) (G : CoherentAdicSystems J)
    (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)
    (β : (coherentAdicPullback π J).obj G ≅ (completionFunctor X' (J.comap π)).obj 𝓕),
    IsIso (π ∣_ K.support.compl) → ∀ V : X.affineOpens,
      letI : IsNoetherianRing ↥Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
      ∀ 𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules
          (Spec (.of (AdicCompletion (J.ideal V) ↥Γ(X, V.1)))).ringCatSheaf,
        ((coherentAdicPullback (adicCompletionSpecMap ↥Γ(X, V.1) (J.ideal V))
                ((J.comap V.1.ι).comap V.2.isoSpec.inv)).obj
              ((coherentAdicPullback V.2.isoSpec.inv (J.comap V.1.ι)).obj
                ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G)) ≅
            (completionFunctor (Spec (.of (AdicCompletion (J.ideal V) ↥Γ(X, V.1))))
              (((J.comap V.1.ι).comap V.2.isoSpec.inv).comap
                (adicCompletionSpecMap ↥Γ(X, V.1) (J.ideal V)))).obj 𝒜) →
          IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι
              ((((K.comap V.1.ι).comap V.2.isoSpec.inv).comap
                (adicCompletionSpecMap ↥Γ(X, V.1) (J.ideal V))).support.compl))).map
            ((Scheme.Modules.pullbackPushforwardAdjunction
              (adicBaseChangeMap ↥Γ(X, V.1) (J.ideal V)
                ((π ∣_ V.1) ≫ V.2.isoSpec.hom))).unit.app 𝒜.obj))

/-- **`Stacks.Algebraization.HasAffineLocalDirectImageSolution` from the source's condition `hc`
alone.** The local solution of Stacks 088B over an affine open of the base — the single remaining
binder behind [Stacks, Tag 088C], the binder `hDev` of [Stacks, Tag 088E] and the first input of
`Stacks.Algebraization.isEquivalence_completionFunctorProperOver_of_isDirectImageComparison` —
holds granted `Stacks.Algebraization.HasAdicBaseChangeUnitCondition` and nothing else.

`Stacks.Algebraization.hasAffineLocalDirectImageSolution_of_morphismRestrict` at
`…exists_isDirectImageCharacterized_isKernelCokernel_morphismRestrict_of_route2`: the first turns
a solution for `π ∣_ V` into a solution of the restricted problem, the second produces the solution
for `π ∣_ V`. The Noetherian hypothesis on `Γ(X, V)` is automatic
(`AlgebraicGeometry.IsLocallyNoetherian.component_noetherian`).

No `stacks` attribute is attached: this is a reduction of a hypothesis, not a statement of the
source. -/
public theorem hasAffineLocalDirectImageSolution_of_adicBaseChangeUnitCondition
    (h : HasAdicBaseChangeUnitCondition.{u}) : HasAffineLocalDirectImageSolution.{u} := by
  refine hasAffineLocalDirectImageSolution_of_morphismRestrict ?_
  intro X' X _ _ π _ J K G 𝓕 β hiso V
  let : IsNoetherianRing ↥Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
  exact exists_isDirectImageCharacterized_isKernelCokernel_morphismRestrict_of_route2
    π J K G 𝓕 β V (h π J K G 𝓕 β hiso V)

/-- **[Stacks, Tag 088B] at a general base from the source's condition `hc` alone.**
`Stacks.Algebraization.IsDirectImageComparison` — the form of Stacks 088B that Stacks 088C,
`hDev` and `hSupp` consume, at an arbitrary Noetherian base and an arbitrary quasi-coherent ideal
sheaf — now has the single hypothesis
`Stacks.Algebraization.HasAdicBaseChangeUnitCondition`.

`Stacks.Algebraization.isDirectImageComparison_of_hasAffineLocalDirectImageSolution` read through
`…hasAffineLocalDirectImageSolution_of_adicBaseChangeUnitCondition`.

No `stacks` attribute is attached: the tag is registered on
`Stacks.Coherent.exists_isDirectImageCharacterized_isKernelCokernel_of_affineLocalSolutions`. -/
public theorem isDirectImageComparison_of_adicBaseChangeUnitCondition
    (h : HasAdicBaseChangeUnitCondition.{u}) : IsDirectImageComparison.{u} :=
  isDirectImageComparison_of_hasAffineLocalDirectImageSolution
    (hasAffineLocalDirectImageSolution_of_adicBaseChangeUnitCondition h)

/-- **[Stacks, Tag 088C] from the source's condition `hc` alone.** For `A` Noetherian and complete
along `I` and `f : Z ⟶ Spec A` proper, the completion functor `Coh(𝒪_Z) ⥤ Coh(Z, I 𝒪_Z)` of
[Stacks, Tag 0880] is an equivalence, granted
`Stacks.Algebraization.HasAdicBaseChangeUnitCondition` and nothing else.

`Stacks.Algebraization.isEquivalence_completionFunctor_of_isDirectImageComparison` at
`…isDirectImageComparison_of_adicBaseChangeUnitCondition`.

No `stacks` attribute is attached: Stacks 088C is registered on
`Stacks.Algebraization.isEquivalence_completionFunctor_of_devissage`. -/
public theorem isEquivalence_completionFunctor_of_adicBaseChangeUnitCondition
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    (h : HasAdicBaseChangeUnitCondition.{u})
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of A)) [IsProper f] :
    letI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian f
    (completionFunctor Z (baseIdealSheaf A I f)).IsEquivalence :=
  isEquivalence_completionFunctor_of_isDirectImageComparison A I
    (isDirectImageComparison_of_adicBaseChangeUnitCondition h) f

/-- **The hypothesis `hDev` of [Stacks, Tag 088E] from the source's condition `hc` alone.** The
inductive step of the Noetherian induction of Stacks 088C, asked on every closed subscheme of `Z`
proper over `A`, holds granted `Stacks.Algebraization.HasAdicBaseChangeUnitCondition` and nothing
else; it carries no antecedent of its own, the dévissage hypothesis being unused.

`Stacks.Algebraization.hDev_of_isDirectImageComparison` at
`…isDirectImageComparison_of_adicBaseChangeUnitCondition`.

No `stacks` attribute is attached: Stacks 088C is registered on
`Stacks.Algebraization.isEquivalence_completionFunctor_of_devissage`, and this is its conclusion
read on the closed subschemes. -/
public theorem hDev_of_adicBaseChangeUnitCondition
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of A))
    (h : HasAdicBaseChangeUnitCondition.{u}) :
    ∀ (K : Z.IdealSheafData) (hK : IsProper (K.subschemeι ≫ f)),
      letI : IsProper (K.subschemeι ≫ f) := hK
      letI : IsLocallyNoetherian K.subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian (K.subschemeι ≫ f)
      ∀ L : K.subscheme.IdealSheafData,
        (∀ L' : K.subscheme.IdealSheafData, L < L' →
            ∀ 𝓖 : Stacks.Coherent.CoherentAdicSystems
                (baseIdealSheaf A I (K.subschemeι ≫ f)),
              IsSystemAnnihilatedBy L' 𝓖.obj →
                (completionFunctor K.subscheme
                  (baseIdealSheaf A I (K.subschemeι ≫ f))).essImage 𝓖) →
          ∀ 𝓕 : Stacks.Coherent.CoherentAdicSystems
              (baseIdealSheaf A I (K.subschemeι ≫ f)),
            IsSystemAnnihilatedBy L 𝓕.obj →
              (completionFunctor K.subscheme
                (baseIdealSheaf A I (K.subschemeι ≫ f))).essImage 𝓕 :=
  hDev_of_isDirectImageComparison A I f
    (isDirectImageComparison_of_adicBaseChangeUnitCondition h)

/-- **[Stacks, Tag 088E], Grothendieck's existence theorem with proper support, from the source's
condition `hc` alone.** For `A` Noetherian and complete along `I` and `f : Z ⟶ Spec A` separated,
locally of finite type and quasi-compact, the functor of [Stacks, Tag 088D] is an equivalence,
granted `Stacks.Algebraization.HasAdicBaseChangeUnitCondition` and nothing else.

**Both named inputs are discharged here.**
`Stacks.Algebraization.isEquivalence_completionFunctorProperOver_of_isDirectImageComparison_alone`
is the 088E assembly with `hTransport` already discharged from 088B by
`Stacks.Algebraization.transport_of_isDirectImageComparison`, through its left disjunct; its
remaining input is `Stacks.Algebraization.IsDirectImageComparison`, which
`…isDirectImageComparison_of_adicBaseChangeUnitCondition` supplies. So neither the Chow residual
nor `Stacks.Algebraization.HasAdicCompletionChartBaseChange` appears, and `hc` is the only
hypothesis of Grothendieck existence on this route.

No `stacks` attribute is attached: Stacks 088E is registered on
`Stacks.Algebraization.isEquivalence_completionFunctorProperOver`. -/
public theorem isEquivalence_completionFunctorProperOver_of_adicBaseChangeUnitCondition
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (h : HasAdicBaseChangeUnitCondition.{u}) :
    (completionFunctorProperOver A I f).IsEquivalence :=
  isEquivalence_completionFunctorProperOver_of_isDirectImageComparison_alone A I f
    (isDirectImageComparison_of_adicBaseChangeUnitCondition h)

end Residue

end Stacks.Algebraization

end
