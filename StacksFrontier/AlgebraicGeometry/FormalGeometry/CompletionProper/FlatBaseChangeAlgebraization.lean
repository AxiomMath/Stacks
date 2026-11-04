module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorQuotient
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.PullbackEquivalence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.AffineExistenceDescent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.BaseAdicCompletion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.GeneralBaseAlgebraization
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.Comap
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.AdicCompletion.QuotientBijective
public import StacksFrontier.RingTheory.Localization.Glueing.IdealPowerTorsion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.CompletionProjectionQuotient

/-!
# Flat base change along `B ⟶ B ^∧`: the second paragraph of the proof of Stacks 088B

Stacks 088B produces, for a proper `π : X' ⟶ X` of Noetherian schemes, quasi-coherent sheaves of
ideals `𝒥, 𝒦 ⊆ 𝒪_X` and an object `(𝒢_n)` of `Coh(X, 𝒥)` with `β : π^*(𝒢_n) ≅ 𝓕 ^∧`, a morphism

`α : (𝒢_n) ⟶ (π_*𝓕) ^∧`

characterized by its composites with `Stacks.Coherent.directImageComparison`. Its proof has two
paragraphs. The first — *the condition characterizing `α` is local on `X`, so `α` may be built
over an open cover and glued* — is
`Stacks.Coherent.exists_isDirectImageCharacterized_of_openCover`
(`CompletionProper/GeneralBaseAlgebraization.lean`), a theorem; it leaves the local solutions as
binders. The second — *over an affine `U = Spec B` of the cover, replace `B` by its completion
`B ^∧`, solve there, and descend* — is what this file carries.

The replacement is forced: `Γ(U, 𝒪_U)` need not be complete along `𝒥(U)`, and Grothendieck
existence genuinely fails over such a `U`, as
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionCriteria/AffineExistenceDescent.lean`
shows at the local ring of a node. Nothing in this file descends an algebraization; what descends
are *morphisms* of systems and equations between them.

## Main results

* `Stacks.Algebraization.flat_adicCompletionSpecMap` — `Spec B ^∧ ⟶ Spec B` is flat
  (Algebra 00MB).
* `Stacks.Algebraization.isIso_pullback_snd_adicCompletionSpecMap` — its closed fibre over `V(J)`
  is `V(J)`, i.e. `B / J ≅ B ^∧ / J B ^∧`.
* `Stacks.Algebraization.coherentAdicPullback_adicCompletionSpecMap_isEquivalence` — **the flat
  base change itself**: pullback `Coh(Spec B, J 𝒪) ⟶ Coh(Spec B ^∧, J 𝒪)` is an *equivalence*.
  This is Stacks 0EHQ (`Stacks.Coherent.coherentAdicPullback_isEquivalence`) at the two facts
  above.
* `Stacks.Algebraization.comap_adicIdealSheaf_adicCompletionSpecMap` — the base-changed situation
  over `Spec B ^∧` is again of the same shape, at the extended ideal `J B ^∧`.
* `Stacks.Algebraization.exists_isDirectImageCharacterized_isKernelCokernel_adicCompletionBase` —
  **Stacks 088B with `α` characterized over `Spec B ^∧`, with no completeness hypothesis on `B`**:
  `B ^∧` is `J B ^∧`-adically complete, so the affine case
  `Stacks.Algebraization.exists_isDirectImageCharacterized_isKernelCokernel_of_isAffine` applies
  there.
* `Stacks.Algebraization.existsUnique_systemHom_of_adicCompletion` — **the descent**: a morphism
  of the pulled-back systems is the pullback of a unique morphism over `Spec B`.
* `Stacks.Algebraization.hom_baseChange_bijective_adicCompletion` and
  `Stacks.Algebraization.exists_primaryComponent_baseChange_equiv_adicCompletion` — More on
  Algebra 05EC along `B ⟶ B ^∧`: base change to `B ^∧` is bijective on maps out of a
  `J`-power-torsion module, and identifies the `J`-power-torsion submodule with the
  `J B ^∧`-power-torsion submodule of the base change. The second clause is what returns
  annihilation by a power of `J B ^∧` to annihilation by a power of `J`.
* `Stacks.Algebraization.coherentIdealPowerTorsionPullback_adicCompletionSpecMap_isEquivalence`
  and `Stacks.Algebraization.pullback_map_injective_of_coherentIdealPowerTorsion` — **05EC in
  sheaf form**: pullback along `Spec B ^∧ ⟶ Spec B` is an equivalence on the coherent modules
  annihilated by a power of `J 𝒪`, hence injective on morphisms between them.
* `Stacks.Algebraization.isDirectImageCharacterized_of_pullback_adicCompletionSpecMap` — **the
  characterizing equation of Stacks 088B descends along `B ⟶ B ^∧`**: both of its sides at
  level `n` are morphisms between modules annihilated by `J ⁿ⁺¹`.
* `Stacks.Algebraization.exists_isDirectImageCharacterized_of_adicCompletionPullback` — **the
  assembly**: a solution over `Spec B ^∧` of the *pulled-back* problem descends to a characterized
  `α` over `Spec B`. Unconditional.
* `Stacks.Algebraization.exists_isDirectImageCharacterized_of_baseChangeComparison` — **the
  second paragraph of the proof of Stacks 088B, reduced to two base-change squares.** The whole
  paragraph is assembled — the solution over `Spec B ^∧` and the descent of both the morphism and
  the characterizing equation — from a comparison of the two completed direct images and a
  comparison of the two direct images of the levels, subject to the two squares `hδ` and `hγ`
  which say that those comparisons carry the `δ` and the `γ` of the situation over `Spec B ^∧` to
  the pullbacks of the `δ` and the `γ` of the situation over `Spec B`. Those two squares are the
  only binders beyond the base-changed data itself.

## What is proved and what remains

Everything above is unconditional, including the whole descent: both the morphism and the
equation characterizing it come down from `Spec B ^∧` to `Spec B`.

What remains is the *other* half of the source's second paragraph, and it is geometry rather than
commutative algebra. The assembly consumes a solution of the equation written with the
*pullbacks along `Spec B ^∧ ⟶ Spec B`* of the `δ` and `γ` of the situation over `Spec B`, while
`exists_isDirectImageCharacterized_isKernelCokernel_adicCompletionBase` produces a solution of
the equation of a proper morphism *over* `Spec B ^∧`. Identifying the two needs the base change
of `π` to `Spec B ^∧`, the base changes of `𝓕` and of `β`, and the degree-zero flat base change
`g^*(π_*𝓕) ≅ π'_*(g'^*𝓕)` of Cohomology of Schemes 02KH — present in this library as
`Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat` and
`Stacks.AlgebraicGeometry.FlatBaseChange.isIso_pushforwardBaseChange_of_isAffine` — compatibly
with the quotient maps `δ` and `γ` are built from. None of that base-changed geometry is
assembled here.

`Stacks.Algebraization.exists_isDirectImageCharacterized_of_baseChangeComparison` says exactly
how much of it is needed and no more: the binder `hψ` of the assembly is discharged from two
squares, `hδ` for the quotient maps that `Stacks.Coherent.directImageQuotientComparison` descends
and `hγ` for the unit of `π^* ⊣ π_*`. What is still missing is therefore precisely these two
squares, and the base-changed morphism `π' = π ×_{Spec B} Spec B ^∧` identified as such which is
what makes them provable; the comparisons themselves exist in this library at the two 02KH
declarations above. Neither square is stated anywhere in this tree, and nothing here supplies a
model of the binders of
`exists_isDirectImageCharacterized_of_baseChangeComparison` for an actual base change.

**The rest of Stacks 088B is not assembled here either, and nothing below pretends otherwise.**
Feeding the local solutions into
`Stacks.Coherent.exists_isDirectImageCharacterized_of_openCover` also needs the binder `hψ` of
that theorem, the agreement of the local solutions on overlaps, which the source gets from the
*uniqueness* of the characterized `α`; uniqueness is
`Stacks.Coherent.eq_of_comp_directImageQuotientComparisonSystem_eq`, whose own binder `hmono` is
the theorem on formal functions in the relative form `lim ((π_*𝓕) ^∧) ≅ lim (π_*(𝓕 ^∧))`
(Stacks 02OC), which this library has only over a complete affine base. And the annihilation half
of the conclusion of Stacks 088B is not glued from a cover anywhere in this tree; see the module
docstring of `CompletionProper/GeneralBaseAlgebraization.lean`.

## Implementation notes

`Stacks.Algebraization.adicIdealSheaf B J` is `J 𝒪_{Spec B}`, presented as
`Scheme.IdealSheafData.ofIdealTop` of the image of `J` in `Γ(Spec B, 𝒪)`; it agrees with the
kernel of `Spec B / J ⟶ Spec B` (`adicIdealSheaf_eq_ker`, which is what Stacks 0EHQ's hypothesis
is stated against) and with `Stacks.Cohomology.FormalFunctions.baseIdealSheaf B J` at the identity
of `Spec B` (`adicIdealSheaf_eq_baseIdealSheaf`, which is what Stacks 088B is stated against).

One `stacks` attribute is attached, to
`Stacks.Algebraization.coherentAdicPullback_adicCompletionSpecMap_isEquivalence`; its note says
exactly which step of the source's second paragraph it is and what of that paragraph it is not.
The existing attributions for 088B, on `Stacks.Coherent.directImageComparison`,
`Stacks.Coherent.isKernelCokernelAnnihilatedByPower_directImageComparison_iff`,
`Stacks.Algebraization.exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_isAffine`
and `Stacks.Coherent.exists_isDirectImageCharacterized_of_openCover`, are unchanged.

## References

* [Stacks Project, Tag 00MB](https://stacks.math.columbia.edu/tag/00MB)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 05EC](https://stacks.math.columbia.edu/tag/05EC)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 0887](https://stacks.math.columbia.edu/tag/0887)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 0EHQ](https://stacks.math.columbia.edu/tag/0EHQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry TensorProduct

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

/-! The zero morphism out of a sheaf of modules presented without
`AlgebraicGeometry.Scheme.Modules` is supplied by this `local instance`, reactivated here rather
than restated: instance search does not see through `AlgebraicGeometry.Scheme.Modules`, a
semireducible definition, to find the zero morphisms of `X.Modules` for a source presented as a
bare `SheafOfModules X.ringCatSheaf`. -/
attribute [local instance] Stacks.Algebraization.zeroHomOfSheafOfModules

namespace Stacks.Algebraization

/-! ### The completion of an affine base -/

/-- The morphism `Spec B ^∧ ⟶ Spec B` induced by the completion map `B ⟶ B ^∧`. -/
public abbrev adicCompletionSpecMap (B : Type u) [CommRing B] (J : Ideal B) :
    Spec (.of (AdicCompletion J B)) ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom (algebraMap B (AdicCompletion J B)))

/-- The closed immersion `V(J) = Spec B / J ⟶ Spec B`. -/
public abbrev quotientSpecMap (B : Type u) [CommRing B] (J : Ideal B) :
    Spec (.of (B ⧸ J)) ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom (algebraMap B (B ⧸ J)))

/-- The ideal sheaf `J 𝒪_{Spec B}` of `Spec B`. -/
public abbrev adicIdealSheaf (B : Type u) [CommRing B] (J : Ideal B) :
    (Spec (.of B)).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (.of B)).inv.hom J)

/-- `J 𝒪_{Spec B}` is the kernel of the closed immersion `Spec B / J ⟶ Spec B`. -/
public theorem adicIdealSheaf_eq_ker (B : Type u) [CommRing B] (J : Ideal B) :
    adicIdealSheaf B J = (quotientSpecMap B J).ker :=
  (AlgebraicGeometry.ker_Spec_map_quotient_mk J).symm

/-- `J 𝒪_{Spec B}` is `Stacks.Cohomology.FormalFunctions.baseIdealSheaf` of `J` at the identity
of `Spec B`, which is the presentation Stacks 088B is stated in. -/
public theorem adicIdealSheaf_eq_baseIdealSheaf (B : Type u) [CommRing B] (J : Ideal B) :
    adicIdealSheaf B J =
      Stacks.Cohomology.FormalFunctions.baseIdealSheaf B J (𝟙 (Spec (.of B))) := by
  refine congrArg Scheme.IdealSheafData.ofIdealTop ?_
  refine congrArg (fun ψ : B →+* Γ(Spec (.of B), ⊤) => Ideal.map ψ J) ?_
  exact congrArg CommRingCat.Hom.hom (Category.comp_id _).symm

/-- **Algebra 00MB, geometrically.** The morphism `Spec B ^∧ ⟶ Spec B` is flat. -/
public theorem flat_adicCompletionSpecMap (B : Type u) [CommRing B] [IsNoetherianRing B]
    (J : Ideal B) : Flat (adicCompletionSpecMap B J) :=
  Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr (AdicCompletion.flat_of_isNoetherian J))

/-- The inclusion of `B / J` as the right tensor factor of `B ^∧ ⊗_B B / J` is the comparison
`B / J ⟶ B ^∧ / J B ^∧` read through `Algebra.TensorProduct.quotIdealMapEquivTensorQuot`. -/
public theorem includeRight_eq_quotientMap (B : Type u) [CommRing B] (J : Ideal B)
    (x : B ⧸ J) :
    (Algebra.TensorProduct.includeRight :
        (B ⧸ J) →ₐ[B] AdicCompletion J B ⊗[B] (B ⧸ J)) x =
      Algebra.TensorProduct.quotIdealMapEquivTensorQuot (AdicCompletion J B) J
        (Ideal.quotientMap (J.map (algebraMap B (AdicCompletion J B)))
          (algebraMap B (AdicCompletion J B)) Ideal.le_comap_map x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.quotientMap_mk, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
  show (1 : AdicCompletion J B) ⊗ₜ[B] (algebraMap B (B ⧸ J) a) = _
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

/-- **The closed fibre of `Spec B ^∧ ⟶ Spec B` over `V(J)` is `V(J)`.** The inclusion of
`B / J` as the right tensor factor of `B ^∧ ⊗_B B / J` is bijective. -/
public theorem bijective_includeRight_adicCompletion (B : Type u) [CommRing B]
    [IsNoetherianRing B] (J : Ideal B) :
    Function.Bijective (Algebra.TensorProduct.includeRight :
      (B ⧸ J) → AdicCompletion J B ⊗[B] (B ⧸ J)) := by
  have hfun : (Algebra.TensorProduct.includeRight :
        (B ⧸ J) → AdicCompletion J B ⊗[B] (B ⧸ J)) =
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (AdicCompletion J B) J) ∘
        (Ideal.quotientMap (J.map (algebraMap B (AdicCompletion J B)))
          (algebraMap B (AdicCompletion J B)) Ideal.le_comap_map) :=
    funext (includeRight_eq_quotientMap B J)
  rw [hfun]
  exact (Algebra.TensorProduct.quotIdealMapEquivTensorQuot
      (AdicCompletion J B) J).bijective.comp
    (AdicCompletion.quotientMap_bijective J (Ideal.fg_of_isNoetherianRing J))

/-- **The closed fibre of `Spec B ^∧ ⟶ Spec B` over `V(J)` is an isomorphism.** The fibre
product of `Spec B ^∧ ⟶ Spec B` with `V(J) ⟶ Spec B` is carried isomorphically onto `V(J)` by the
second projection.

The fibre product is `Spec (B ^∧ ⊗_B B / J)` by `AlgebraicGeometry.pullbackSpecIso`, and under
that identification the second projection is `Spec` of the inclusion of the right tensor factor,
which is bijective by `Stacks.Algebraization.bijective_includeRight_adicCompletion`. -/
public theorem isIso_pullback_snd_adicCompletionSpecMap (B : Type u) [CommRing B]
    [IsNoetherianRing B] (J : Ideal B) :
    IsIso (pullback.snd (adicCompletionSpecMap B J) (quotientSpecMap B J)) := by
  rw [← pullbackSpecIso_hom_snd B (AdicCompletion J B) (B ⧸ J)]
  exact IsIso.comp_isIso' inferInstance
    (isIso_SpecMap_iff.mpr (bijective_includeRight_adicCompletion B J))

/-- The morphism cut out by `J` is a closed immersion. -/
public instance isClosedImmersion_quotientSpecMap (B : Type u) [CommRing B] (J : Ideal B) :
    IsClosedImmersion (quotientSpecMap B J) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-! ### Flat base change along `B ⟶ B ^∧` on coherent adic systems -/

/-- The closed fibre of `Spec B ^∧ ⟶ Spec B` over `J 𝒪_{Spec B}` is an isomorphism. -/
private theorem isIso_pullback_snd_subschemeι_adicIdealSheaf (B : Type u) [CommRing B]
    [IsNoetherianRing B] (J : Ideal B) :
    IsIso (pullback.snd (adicCompletionSpecMap B J) (adicIdealSheaf B J).subschemeι) := by
  have := isIso_pullback_snd_adicCompletionSpecMap B J
  rw [adicIdealSheaf_eq_ker]
  exact Stacks.Algebraization.isIso_pullback_snd_ker_subschemeι _ _ _

/-- **Flat base change along `B ⟶ B ^∧` for coherent adic systems.** Let `B` be a Noetherian ring
and `J ⊆ B` an ideal. Pullback along `Spec B ^∧ ⟶ Spec B`

`Coh(Spec B, J 𝒪) ⟶ Coh(Spec B ^∧, J 𝒪)`

is an **equivalence** of categories.

This is the first half of the second paragraph of the proof of Stacks 088B: the whole of the
`J`-adic situation over `Spec B` may be replaced by the corresponding situation over
`Spec B ^∧`, losing nothing, and over `Spec B ^∧` the base is complete. It is Stacks 0EHQ
(`Stacks.Coherent.coherentAdicPullback_isEquivalence`) applied to `Spec B ^∧ ⟶ Spec B`, whose two
hypotheses are `Stacks.Algebraization.flat_adicCompletionSpecMap` (Algebra 00MB) and
`Stacks.Algebraization.isIso_pullback_snd_adicCompletionSpecMap`
(More on Algebra 05GG, `B / J ≅ B ^∧ / J B ^∧`).

**It does not say that Grothendieck existence descends**, and it must not be read that way: the
completion functors on the two sides are *not* matched by this equivalence, and
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionCriteria/AffineExistenceDescent.lean`
exhibits, at the local ring of a node, a system in the essential image over `Spec B ^∧` whose
descent along this equivalence is not in the essential image over `Spec B`. What descends along
it are *morphisms* of systems and equations between them, which is exactly what Stacks 088B
transports back. -/
public theorem coherentAdicPullback_adicCompletionSpecMap_isEquivalence (B : Type u) [CommRing B]
    [IsNoetherianRing B] (J : Ideal B) :
    (Stacks.Coherent.coherentAdicPullback (adicCompletionSpecMap B J)
      (adicIdealSheaf B J)).IsEquivalence := by
  have := flat_adicCompletionSpecMap B J
  have := isIso_pullback_snd_subschemeι_adicIdealSheaf B J
  exact Stacks.Coherent.coherentAdicPullback_isEquivalence _ _

/-- Pullback on the power-torsion coherent modules: the pullback of a coherent module annihilated
by a power of `𝒥` is coherent (Stacks 0EBF) and annihilated by the same power of `𝒥.comap f`
(`Stacks.Coherent.idealPowerMultiple_eq_bot_pullback`). -/
public def coherentIdealPowerTorsionPullback {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ Y) (J : Y.IdealSheafData) :
    (Stacks.Coherent.coherentIdealPowerTorsion J).FullSubcategory ⥤
      (Stacks.Coherent.coherentIdealPowerTorsion (J.comap f)).FullSubcategory :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Scheme.Modules.pullback f)
    (fun M => by
      obtain ⟨n, hcoh, hann⟩ := M.property
      haveI : M.obj.IsCoherent := hcoh
      exact ⟨n, AlgebraicGeometry.isCoherent_pullback f M.obj,
        Stacks.Coherent.idealPowerMultiple_eq_bot_pullback f J (n + 1) M.obj hann⟩)

/-- **Pullback along `Spec B ^∧ ⟶ Spec B` is an equivalence on the power-torsion coherent
modules.** Direct image is one by
`Stacks.Coherent.coherentIdealPowerTorsionPushforward_isEquivalence`, pullback is its left
adjoint by `CategoryTheory.Adjunction.restrictFullyFaithful`, and a left adjoint of an
equivalence is an equivalence. -/
public theorem coherentIdealPowerTorsionPullback_adicCompletionSpecMap_isEquivalence
    (B : Type u) [CommRing B] [IsNoetherianRing B] (J : Ideal B) :
    (coherentIdealPowerTorsionPullback (adicCompletionSpecMap B J)
      (adicIdealSheaf B J)).IsEquivalence := by
  have := flat_adicCompletionSpecMap B J
  have := isIso_pullback_snd_subschemeι_adicIdealSheaf B J
  have : (Stacks.Coherent.coherentIdealPowerTorsionPushforward (adicCompletionSpecMap B J)
      (adicIdealSheaf B J)).IsEquivalence :=
    Stacks.Coherent.coherentIdealPowerTorsionPushforward_isEquivalence _ _
  let R := Stacks.Coherent.coherentIdealPowerTorsionPushforward (adicCompletionSpecMap B J)
    (adicIdealSheaf B J)
  let adj : coherentIdealPowerTorsionPullback (adicCompletionSpecMap B J)
      (adicIdealSheaf B J) ⊣ R :=
    (Scheme.Modules.pullbackPushforwardAdjunction
      (adicCompletionSpecMap B J)).restrictFullyFaithful
      (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
      (Iso.refl _) (Iso.refl _)
  exact Functor.isEquivalence_of_iso
    (R.asEquivalence.symm.toAdjunction.leftAdjointUniq adj)

/-- **A morphism of coherent `𝒪_{Spec B}`-modules annihilated by a power of `J` is determined by
its pullback to `Spec B ^∧`.** This is More on Algebra 05EC in the shape the characterizing
equation of Stacks 088B needs: its two sides are morphisms out of `𝒢_n`, which is annihilated by
`J ⁿ⁺¹`.

Faithfulness of
`Stacks.Algebraization.coherentIdealPowerTorsionPullback_adicCompletionSpecMap_isEquivalence`. -/
public theorem pullback_map_injective_of_coherentIdealPowerTorsion (B : Type u) [CommRing B]
    [IsNoetherianRing B] (J : Ideal B) {M N : (Spec (.of B)).Modules}
    (hM : Stacks.Coherent.coherentIdealPowerTorsion (adicIdealSheaf B J) M)
    (hN : Stacks.Coherent.coherentIdealPowerTorsion (adicIdealSheaf B J) N) {u v : M ⟶ N}
    (h : (Scheme.Modules.pullback (adicCompletionSpecMap B J)).map u =
      (Scheme.Modules.pullback (adicCompletionSpecMap B J)).map v) : u = v := by
  let L := coherentIdealPowerTorsionPullback (adicCompletionSpecMap B J) (adicIdealSheaf B J)
  have : L.IsEquivalence :=
    coherentIdealPowerTorsionPullback_adicCompletionSpecMap_isEquivalence B J
  let M' : (Stacks.Coherent.coherentIdealPowerTorsion (adicIdealSheaf B J)).FullSubcategory :=
    ⟨M, hM⟩
  let N' : (Stacks.Coherent.coherentIdealPowerTorsion (adicIdealSheaf B J)).FullSubcategory :=
    ⟨N, hN⟩
  exact congrArg (fun k : M' ⟶ N' => k.hom) (L.map_injective (ObjectProperty.hom_ext _ h :
    L.map (ObjectProperty.homMk (X := M') (Y := N') u) =
      L.map (ObjectProperty.homMk (X := M') (Y := N') v)))

/-- **Direct image carries annihilation by `ℐ ᵐ` to annihilation by `𝒥 ᵐ`**, for an arbitrary
morphism of schemes and `ℐ = f^{-1}𝒥 𝒪_X`. The dual of
`Stacks.Coherent.idealPowerMultiple_eq_bot_pullback`, and the exponent is again unchanged.

When `ℐ ᵐ 𝓕 = 0` the projection `𝓕 ⟶ 𝓕 / ℐ ᵐ 𝓕` is an isomorphism, so its direct image is a
monomorphism, and `Stacks.Coherent.idealPowerMultiple_pushforward_comp_eq_zero_of_comap` — the
unconditional fact that `𝒥 ᵐ (f_*𝓕)` is killed by that direct image — forces the inclusion of
`𝒥 ᵐ (f_*𝓕)` to vanish. -/
public theorem idealPowerMultiple_eq_bot_pushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : Y.IdealSheafData) (m : ℕ) (F : X.Modules)
    (hF : idealPowerMultiple (J.comap f) m F = ⊥) :
    idealPowerMultiple J m ((Scheme.Modules.pushforward f).obj F) = ⊥ := by
  have hι : (idealPowerMultiple (J.comap f) m F).ι = 0 := (submodule_ι_eq_zero_iff _).mpr hF
  -- the projection onto the quotient is split by the identity, hence an isomorphism
  set d := cokernel.desc (C := X.Modules) (idealPowerMultiple (J.comap f) m F).ι (𝟙 F)
    ((Category.comp_id _).trans hι)
  have h1 : cokernel.π (C := X.Modules) (idealPowerMultiple (J.comap f) m F).ι ≫ d = 𝟙 F :=
    cokernel.π_desc (C := X.Modules) _ _ _
  have h2 : d ≫ cokernel.π (C := X.Modules) (idealPowerMultiple (J.comap f) m F).ι = 𝟙 _ := by
    refine (cancel_epi (cokernel.π (C := X.Modules)
      (idealPowerMultiple (J.comap f) m F).ι)).mp ?_
    rw [← Category.assoc, h1, Category.id_comp, Category.comp_id]
  have : IsIso (cokernel.π (C := X.Modules) (idealPowerMultiple (J.comap f) m F).ι) :=
    ⟨d, h1, h2⟩
  refine (submodule_ι_eq_zero_iff _).mp ?_
  refine (cancel_mono ((Scheme.Modules.pushforward f).map (cokernel.π (C := X.Modules)
    (idealPowerMultiple (J.comap f) m F).ι))).mp ?_
  exact (Stacks.Coherent.idealPowerMultiple_pushforward_comp_eq_zero_of_comap f J m F).trans
    zero_comp.symm

/-- **The target of the characterizing equation of Stacks 088B is a power-torsion coherent
module.** The level-`n` target is `π_*(𝓕 / ℐ ⁿ⁺¹𝓕)`, which is coherent because `π` is proper
(Stacks 02O5) and annihilated by `𝒥 ⁿ⁺¹` by
`Stacks.Algebraization.idealPowerMultiple_eq_bot_pushforward`. -/
public theorem coherentIdealPowerTorsion_pushforward_idealPowerQuotient {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [IsProper f] (J : Y.IdealSheafData) (n : ℕ)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    Stacks.Coherent.coherentIdealPowerTorsion J
      ((Scheme.Modules.pushforward f).obj
        (idealPowerQuotient (J.comap f) (n + 1) F.obj)) := by
  have : F.obj.IsCoherent := F.property
  obtain ⟨hcoh, hann⟩ :=
    Stacks.Coherent.coherentAnnihilatedBy_idealPowerQuotient (J.comap f) n F.obj F.property
  have : (idealPowerQuotient (J.comap f) (n + 1) F.obj).IsCoherent := hcoh
  exact ⟨n, AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f _,
    idealPowerMultiple_eq_bot_pushforward f J (n + 1) _ hann⟩

/-- **The characterization of `α` in Stacks 088B is detected after base change to `Spec B ^∧`.**
If the characterizing equation holds after pullback along `Spec B ^∧ ⟶ Spec B`, it holds.

This is More on Algebra 05EC in the shape the proof of Stacks 088B uses it. Both sides of the
equation at level `n` are morphisms from `𝒢_n`, annihilated by `J ⁿ⁺¹`, to `π_*(𝓕 / ℐ ⁿ⁺¹𝓕)`,
annihilated by `J ⁿ⁺¹` as well
(`Stacks.Algebraization.coherentIdealPowerTorsion_pushforward_idealPowerQuotient`), and pullback
along `Spec B ^∧ ⟶ Spec B` is injective on morphisms between such modules
(`Stacks.Algebraization.pullback_map_injective_of_coherentIdealPowerTorsion`). -/
public theorem isDirectImageCharacterized_of_pullback_adicCompletionSpecMap (B : Type u)
    [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    {X' : Scheme.{u}} [IsNoetherian X'] (π : X' ⟶ Spec (.of B)) [IsProper π]
    (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)
    (G : Stacks.Coherent.CoherentAdicSystems (adicIdealSheaf B J))
    (β : (Stacks.Coherent.coherentAdicPullback π (adicIdealSheaf B J)).obj G ≅
      (completionFunctor X' ((adicIdealSheaf B J).comap π)).obj 𝓕)
    (α : G.obj ⟶ ((completionFunctor (Spec (.of B)) (adicIdealSheaf B J)).obj
      (Stacks.Coherent.properPushforwardCoherent π 𝓕)).obj)
    (h : ∀ n : ℕ, (Scheme.Modules.pullback (adicCompletionSpecMap B J)).map
          (α.app (op n) ≫ eqToHom (completionFunctor_obj (Spec (.of B)) (adicIdealSheaf B J)
              (Stacks.Coherent.properPushforwardCoherent π 𝓕) n) ≫
            Stacks.Coherent.directImageQuotientComparison π (adicIdealSheaf B J) (n + 1) 𝓕.obj) =
        (Scheme.Modules.pullback (adicCompletionSpecMap B J)).map
          ((Stacks.Coherent.directImageComparison π (adicIdealSheaf B J) G 𝓕 β).app (op n) ≫
            eqToHom (Stacks.Coherent.pushforward_completion_obj π (adicIdealSheaf B J) 𝓕 n))) :
    Stacks.Coherent.IsDirectImageCharacterized π (adicIdealSheaf B J) G 𝓕 β α := fun n =>
  pullback_map_injective_of_coherentIdealPowerTorsion B J
    ⟨n, G.property.1 n, G.property.2.1 n⟩
    (coherentIdealPowerTorsion_pushforward_idealPowerQuotient π (adicIdealSheaf B J) n 𝓕) (h n)

/-! ### The base-changed situation over `Spec B ^∧` -/

/-- **The inverse image of `J 𝒪_{Spec B}` along `Spec B ^∧ ⟶ Spec B` is `J B ^∧ 𝒪`.** The
base-changed situation over `Spec B ^∧` is again of the same shape, with the ideal replaced by its
extension; the two sides are the ideal sheaves of ideals of global sections, and the ideals agree
by the naturality of `Scheme.ΓSpecIso`. -/
public theorem comap_adicIdealSheaf_adicCompletionSpecMap (B : Type u) [CommRing B]
    (J : Ideal B) :
    (adicIdealSheaf B J).comap (adicCompletionSpecMap B J) =
      adicIdealSheaf (AdicCompletion J B) (J.map (algebraMap B (AdicCompletion J B))) := by
  rw [Stacks.AlgebraicGeometry.comap_ofIdealTop]
  refine congrArg Scheme.IdealSheafData.ofIdealTop ?_
  rw [Ideal.map_map, Ideal.map_map]
  refine congrArg (fun ψ : B →+* Γ(Spec (.of (AdicCompletion J B)), ⊤) => Ideal.map ψ J) ?_
  exact (congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap B (AdicCompletion J B))))).symm

/-- **`B ^∧` is `J B ^∧`-adically complete.** `AdicCompletion.isAdicComplete_self`, in the form
the ideal sheaf `J B ^∧ 𝒪_{Spec B ^∧}` asks for. -/
public theorem isAdicComplete_map_algebraMap_adicCompletion (B : Type u) [CommRing B]
    [IsNoetherianRing B] (J : Ideal B) :
    IsAdicComplete (J.map (algebraMap B (AdicCompletion J B))) (AdicCompletion J B) :=
  AdicCompletion.isAdicComplete_self J (Ideal.fg_of_isNoetherianRing J)

/-- **Stacks 088B with `α` characterized, over an affine base presented by an arbitrary equal
ideal sheaf.**
`Stacks.Algebraization.exists_isDirectImageCharacterized_isKernelCokernel_of_isAffine` with the
ideal sheaf a binder constrained to equal `Stacks.Cohomology.FormalFunctions.baseIdealSheaf A I f`,
so that it can be applied at an ideal sheaf arising as the inverse image of another one. -/
public theorem exists_isDirectImageCharacterized_isKernelCokernel_of_eq_baseIdealSheaf
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X' X : Scheme.{u}} [IsNoetherian X'] [IsNoetherian X]
    (f : X ⟶ Spec (.of A)) (π : X' ⟶ X) [IsProper π] [IsProper f] [IsAffine X]
    (𝒥 : X.IdealSheafData)
    (h𝒥 : 𝒥 = Stacks.Cohomology.FormalFunctions.baseIdealSheaf A I f)
    (𝒦 : X.IdealSheafData)
    (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)
    (G : Stacks.Coherent.CoherentAdicSystems 𝒥)
    (β : (Stacks.Coherent.coherentAdicPullback π 𝒥).obj G ≅
      (completionFunctor X' (𝒥.comap π)).obj 𝓕)
    (hc : ∀ 𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
      (G ≅ (completionFunctor X 𝒥).obj 𝒜) →
        IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι 𝒦.support.compl)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app 𝒜.obj))) :
    ∃ α : G.obj ⟶ ((completionFunctor X 𝒥).obj
        (Stacks.Coherent.properPushforwardCoherent π 𝓕)).obj,
      Stacks.Coherent.IsDirectImageCharacterized π 𝒥 G 𝓕 β α ∧
        IsKernelCokernelAnnihilatedByPower 𝒦 α := by
  subst h𝒥
  exact exists_isDirectImageCharacterized_isKernelCokernel_of_isAffine A I f π 𝒦 𝓕 G β hc

/-- **Stacks 088B with `α` characterized, over the completed base `Spec B ^∧`.** Let `B` be a
Noetherian ring, `J ⊆ B` an ideal, `π : X' ⟶ Spec B ^∧` proper and `𝒦 ⊆ 𝒪_{Spec B ^∧}` a
quasi-coherent sheaf of ideals. For a coherent `𝒪_{X'}`-module `𝓕`, an object `G` of
`Coh(Spec B ^∧, J 𝒪)` — the inverse image of `J 𝒪_{Spec B}` — the source's isomorphism
`β : π^*G ≅ 𝓕 ^∧` and the condition `hc`, there is a morphism

`α : G ⟶ (π_*𝓕) ^∧`

which is characterized in the source's sense **and** has its levelwise kernels and cokernels
annihilated by a power of `𝒦`.

**No completeness hypothesis on `B`.** This is the step "over `Spec B ^∧` the base is complete, so
the affine case applies" of the second paragraph of the proof of Stacks 088B. The base ring
`B ^∧` is `J B ^∧`-adically complete by `AdicCompletion.isAdicComplete_self`, so the affine case
`Stacks.Algebraization.exists_isDirectImageCharacterized_isKernelCokernel_of_isAffine` applies at
`A = B ^∧`, `I = J B ^∧` and the identity of `Spec B ^∧`; the ideal sheaf matches by
`Stacks.Algebraization.comap_adicIdealSheaf_adicCompletionSpecMap` and
`Stacks.Algebraization.adicIdealSheaf_eq_baseIdealSheaf`.

No `stacks` attribute is attached: the affine-base form of Stacks 088B is already registered on
`Stacks.Algebraization.exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_isAffine`,
and this is that statement at a particular base, not coverage of a further part of the source. -/
public theorem exists_isDirectImageCharacterized_isKernelCokernel_adicCompletionBase
    (B : Type u) [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    {X' : Scheme.{u}} [IsNoetherian X']
    (π : X' ⟶ Spec (.of (AdicCompletion J B))) [IsProper π]
    (𝒦 : (Spec (.of (AdicCompletion J B))).IdealSheafData)
    (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)
    (G : Stacks.Coherent.CoherentAdicSystems
      ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J)))
    (β : (Stacks.Coherent.coherentAdicPullback π
        ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J))).obj G ≅
      (completionFunctor X'
        (((adicIdealSheaf B J).comap (adicCompletionSpecMap B J)).comap π)).obj 𝓕)
    (hc : ∀ 𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules
        (Spec (.of (AdicCompletion J B))).ringCatSheaf,
      (G ≅ (completionFunctor (Spec (.of (AdicCompletion J B)))
          ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J))).obj 𝒜) →
        IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι 𝒦.support.compl)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app 𝒜.obj))) :
    ∃ α : G.obj ⟶ ((completionFunctor (Spec (.of (AdicCompletion J B)))
        ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J))).obj
        (Stacks.Coherent.properPushforwardCoherent π 𝓕)).obj,
      Stacks.Coherent.IsDirectImageCharacterized π
          ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J)) G 𝓕 β α ∧
        IsKernelCokernelAnnihilatedByPower 𝒦 α := by
  have := isAdicComplete_map_algebraMap_adicCompletion B J
  exact exists_isDirectImageCharacterized_isKernelCokernel_of_eq_baseIdealSheaf
    (AdicCompletion J B) (J.map (algebraMap B (AdicCompletion J B)))
    (𝟙 (Spec (.of (AdicCompletion J B)))) π _
    ((comap_adicIdealSheaf_adicCompletionSpecMap B J).trans
      (adicIdealSheaf_eq_baseIdealSheaf (AdicCompletion J B)
        (J.map (algebraMap B (AdicCompletion J B)))))
    𝒦 𝓕 G β hc

/-! ### Descent of morphisms of systems along `B ⟶ B ^∧` -/

/-- **A morphism of coherent adic systems descends along `B ⟶ B ^∧`, uniquely.** Let `B` be a
Noetherian ring, `J ⊆ B` an ideal and `G`, `H` two objects of `Coh(Spec B, J 𝒪)`. Every morphism
of their pullbacks to `Spec B ^∧` is the pullback of a unique morphism `G ⟶ H`.

This is the descent step of the second paragraph of the proof of Stacks 088B: the `α` produced
over `Spec B ^∧` comes from a unique `α` over `Spec B`. It is full faithfulness of
`Stacks.Algebraization.coherentAdicPullback_adicCompletionSpecMap_isEquivalence`, and the
commutative algebra behind it is the bijectivity of
`Hom_B(M, N) ⟶ Hom_{B ^∧}(M ⊗_B B ^∧, N ⊗_B B ^∧)` for `J`-power-torsion modules, More on
Algebra 05EC (`Stacks.Algebraization.hom_baseChange_bijective_adicCompletion`). -/
public theorem existsUnique_systemHom_of_adicCompletion (B : Type u) [CommRing B]
    [IsNoetherianRing B] (J : Ideal B)
    (G H : Stacks.Coherent.CoherentAdicSystems (adicIdealSheaf B J))
    (b : (Stacks.Coherent.coherentAdicPullback (adicCompletionSpecMap B J)
        (adicIdealSheaf B J)).obj G ⟶
      (Stacks.Coherent.coherentAdicPullback (adicCompletionSpecMap B J)
        (adicIdealSheaf B J)).obj H) :
    ∃! a : G.obj ⟶ H.obj, ∀ n : ℕᵒᵖ,
      (Scheme.Modules.pullback (adicCompletionSpecMap B J)).map (a.app n) = b.hom.app n := by
  have := coherentAdicPullback_adicCompletionSpecMap_isEquivalence B J
  obtain ⟨a₀, ha₀⟩ :=
    (Stacks.Coherent.coherentAdicPullback (adicCompletionSpecMap B J)
      (adicIdealSheaf B J)).map_surjective b
  subst ha₀
  refine ⟨a₀.hom, fun _ => rfl, fun y hy => ?_⟩
  have h1 : (Stacks.Coherent.coherentAdicPullback (adicCompletionSpecMap B J)
        (adicIdealSheaf B J)).map (ObjectProperty.homMk y) =
      (Stacks.Coherent.coherentAdicPullback (adicCompletionSpecMap B J)
        (adicIdealSheaf B J)).map a₀ :=
    ObjectProperty.hom_ext _ (NatTrans.ext (funext fun n => hy n))
  exact congrArg (fun z : G ⟶ H => z.hom)
    ((Stacks.Coherent.coherentAdicPullback (adicCompletionSpecMap B J)
      (adicIdealSheaf B J)).map_injective h1)

/-! ### More on Algebra 05EC along `B ⟶ B ^∧` -/

/-- **More on Algebra 05EC along `B ⟶ B ^∧`, the `Hom` clause.** For `B` Noetherian, `J ⊆ B` an
ideal and `M`, `N` two `B`-modules one of which is `J`-power torsion, base change to `B ^∧` is a
bijection on `B`-linear maps `M ⟶ N`.

`IPowerTorsion.baseChange_equiv_of_quotientMap_bijective` at `S = B ^∧`, whose two hypotheses are
flatness of `B ⟶ B ^∧` (`AdicCompletion.flat_of_isNoetherian`, Algebra 00MB) and the bijectivity of
`B / J ⟶ B ^∧ / J B ^∧` (`AdicCompletion.quotientMap_bijective`). -/
public theorem hom_baseChange_bijective_adicCompletion (B : Type u) [CommRing B]
    [IsNoetherianRing B] (J : Ideal B) (M N : Type u) [AddCommGroup M] [Module B M]
    [AddCommGroup N] [Module B N]
    (hMN : IsIPowerTorsion B M J ∨ IsIPowerTorsion B N J) :
    Function.Bijective (fun f : M →ₗ[B] N =>
      (ModuleCat.extendScalars.{u, u, u} (algebraMap B (AdicCompletion J B))).map
        (ModuleCat.ofHom f)) :=
  (IPowerTorsion.baseChange_equiv_of_quotientMap_bijective.{u, u, u} B (AdicCompletion J B) J
      (Ideal.fg_of_isNoetherianRing J) (AdicCompletion.flat_of_isNoetherian J)
      (AdicCompletion.quotientMap_bijective J (Ideal.fg_of_isNoetherianRing J))).2.1
    M N hMN

/-- **More on Algebra 05EC along `B ⟶ B ^∧`, the torsion-submodule clause.** For `B` Noetherian
and `J ⊆ B` an ideal, base change to `B ^∧` identifies the `J`-power-torsion submodule of a
`B`-module `M` with the `J B ^∧`-power-torsion submodule of `M ⊗_B B ^∧`.

This is the clause that returns the annihilation of a module by a power of `J B ^∧` to its
annihilation by a power of `J`, which is what the second paragraph of the proof of Stacks 088B
transports back along `B ⟶ B ^∧`. -/
public theorem exists_primaryComponent_baseChange_equiv_adicCompletion (B : Type u) [CommRing B]
    [IsNoetherianRing B] (J : Ideal B) (M : Type u) [AddCommGroup M] [Module B M] :
    ∃ e : Ideal.primaryComponent M J ≃ₗ[B]
        Ideal.primaryComponent (TensorProduct B (AdicCompletion J B) M)
          (J.map (algebraMap B (AdicCompletion J B))),
      ∀ x, (e x : TensorProduct B (AdicCompletion J B) M) =
        (1 : AdicCompletion J B) ⊗ₜ[B] x.1 :=
  (IPowerTorsion.baseChange_equiv_of_quotientMap_bijective.{u, u, u} B (AdicCompletion J B) J
      (Ideal.fg_of_isNoetherianRing J) (AdicCompletion.flat_of_isNoetherian J)
      (AdicCompletion.quotientMap_bijective J (Ideal.fg_of_isNoetherianRing J))).1
    M

/-! ### The local solution over an affine base, from the solution over the completed base -/

open Stacks.Coherent in
/-- **The descent of the second paragraph of the proof of Stacks 088B over an affine base.**
Let `B` be a Noetherian ring, `J ⊆ B` an ideal, `π : X' ⟶ Spec B` proper, `𝓕` a coherent
`𝒪_{X'}`-module, `(𝒢_n)` an object of `Coh(Spec B, J 𝒪)` and `β : π^*(𝒢_n) ≅ 𝓕 ^∧`. Given

* `ψ`, a morphism of the systems pulled back to `Spec B ^∧`, and
* `hψ`, the statement that `ψ` satisfies the characterization of Stacks 088B *pulled back* along
  `Spec B ^∧ ⟶ Spec B`,

there is a morphism

`α : (𝒢_n) ⟶ (π_*𝓕) ^∧`

which satisfies `Stacks.Coherent.IsDirectImageCharacterized` over `Spec B` and whose pullback to
`Spec B ^∧` is `ψ`. **Unconditional.**

The descent of the morphism is full faithfulness of
`Stacks.Algebraization.coherentAdicPullback_adicCompletionSpecMap_isEquivalence`, through
`Stacks.Algebraization.existsUnique_systemHom_of_adicCompletion`; the descent of the
characterizing equation is
`Stacks.Algebraization.isDirectImageCharacterized_of_pullback_adicCompletionSpecMap`, i.e. More
on Algebra 05EC in sheaf form.

**What the hypothesis `hψ` costs, and why it is not the conclusion of
`Stacks.Algebraization.exists_isDirectImageCharacterized_isKernelCokernel_adicCompletionBase`.**
That theorem solves Stacks 088B over `Spec B ^∧` for a proper morphism *over `Spec B ^∧`* and the
`δ` and `γ` of that situation. `hψ` asks instead for a solution of the equation written with the
*pullbacks along `Spec B ^∧ ⟶ Spec B`* of the `δ` and `γ` of the situation over `Spec B`.
Identifying the two is the remaining content of the source's second paragraph: the base change of
`π` to `Spec B ^∧`, the base change of `𝓕` and of `β`, and the comparison

`g^*(π_*𝓕) ≅ π'_*(g'^*𝓕)`

of Cohomology of Schemes 02KH in degree zero — available in this library as
`Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat` and
`Stacks.AlgebraicGeometry.FlatBaseChange.isIso_pushforwardBaseChange_of_isAffine` — together with
the compatibility of that comparison with the quotient maps that `δ` and `γ` are built from. That
geometry, not the commutative algebra, is what remains. -/
public theorem exists_isDirectImageCharacterized_of_adicCompletionPullback
    (B : Type u) [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    {X' : Scheme.{u}} [IsNoetherian X'] (π : X' ⟶ Spec (.of B)) [IsProper π]
    (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)
    (G : CoherentAdicSystems (adicIdealSheaf B J))
    (β : (coherentAdicPullback π (adicIdealSheaf B J)).obj G ≅
      (completionFunctor X' ((adicIdealSheaf B J).comap π)).obj 𝓕)
    (ψ : ((coherentAdicPullback (adicCompletionSpecMap B J) (adicIdealSheaf B J)).obj G).obj ⟶
      ((coherentAdicPullback (adicCompletionSpecMap B J) (adicIdealSheaf B J)).obj
        ((completionFunctor (Spec (.of B)) (adicIdealSheaf B J)).obj
          (properPushforwardCoherent π 𝓕))).obj)
    (hψ : ∀ n : ℕ, ψ.app (op n) ≫
          (Scheme.Modules.pullback (adicCompletionSpecMap B J)).map
            (eqToHom (completionFunctor_obj (Spec (.of B)) (adicIdealSheaf B J)
                (properPushforwardCoherent π 𝓕) n) ≫
              directImageQuotientComparison π (adicIdealSheaf B J) (n + 1) 𝓕.obj) =
        (Scheme.Modules.pullback (adicCompletionSpecMap B J)).map
          ((directImageComparison π (adicIdealSheaf B J) G 𝓕 β).app (op n) ≫
            eqToHom (pushforward_completion_obj π (adicIdealSheaf B J) 𝓕 n))) :
    ∃ α : G.obj ⟶ ((completionFunctor (Spec (.of B)) (adicIdealSheaf B J)).obj
        (properPushforwardCoherent π 𝓕)).obj,
      IsDirectImageCharacterized π (adicIdealSheaf B J) G 𝓕 β α ∧
        ∀ n : ℕᵒᵖ,
          (Scheme.Modules.pullback (adicCompletionSpecMap B J)).map (α.app n) = ψ.app n := by
  obtain ⟨α, hα, -⟩ := existsUnique_systemHom_of_adicCompletion B J G
    ((completionFunctor (Spec (.of B)) (adicIdealSheaf B J)).obj
      (properPushforwardCoherent π 𝓕)) (ObjectProperty.homMk ψ)
  refine ⟨α, isDirectImageCharacterized_of_pullback_adicCompletionSpecMap B J π 𝓕 G β α
    fun n => ?_, hα⟩
  rw [Functor.map_comp, hα (op n)]
  exact hψ n

/-! ### `hψ` reduced to the compatibility of the base-change comparison with `δ` and with `γ` -/

open Stacks.Coherent in
/-- **The second paragraph of the proof of Stacks 088B, reduced to two base-change squares.**
Let `B` be a Noetherian ring, `J ⊆ B` an ideal, `π : X' ⟶ Spec B` proper, `𝓕` a coherent
`𝒪_{X'}`-module, `(𝒢_n)` an object of `Coh(Spec B, J 𝒪)` and `β : π^*(𝒢_n) ≅ 𝓕 ^∧`. Let
`π' : X'' ⟶ Spec B ^∧` be proper, `𝓕'` a coherent `𝒪_{X''}`-module and `β'` the corresponding
isomorphism over `Spec B ^∧` — in the intended application the base change of `π`, of `𝓕` and of
`β` along the flat morphism `g = Spec B ^∧ ⟶ Spec B`. Given

* `ι`, a comparison `(π'_*𝓕') ^∧ ⟶ g^*((π_*𝓕) ^∧)` of the two completed direct images,
* `θ_n`, a comparison `π'_*(𝓕'/ℐ' ⁿ⁺¹𝓕') ⟶ g^*(π_*(𝓕/ℐ ⁿ⁺¹𝓕))` of the two direct images of the
  levels, and
* the two squares `hδ` and `hγ` saying that these comparisons carry the `δ` and the `γ` of the
  situation over `Spec B ^∧` to the pullbacks along `g` of the `δ` and the `γ` of the situation
  over `Spec B`,

there is an `α : (𝒢_n) ⟶ (π_*𝓕) ^∧` characterized in the sense of Stacks 088B over `Spec B`.

This is the whole of the source's second paragraph apart from the two squares: the solution over
`Spec B ^∧` is
`Stacks.Algebraization.exists_isDirectImageCharacterized_isKernelCokernel_adicCompletionBase`
(no completeness hypothesis on `B`), and the descent back to `Spec B` is
`Stacks.Algebraization.exists_isDirectImageCharacterized_of_adicCompletionPullback`, whose binder
`hψ` is exactly what `ι`, `θ`, `hδ` and `hγ` supply: `ψ := α' ≫ ι`.

**What `hδ` and `hγ` are, and why they are binders.** `ι` and `θ` are the degree-zero flat base
change `g^*(π_*𝓔) ≅ π'_*(g'^*𝓔)` of Cohomology of Schemes 02KH, which this library has as
`Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat` and
`Stacks.AlgebraicGeometry.FlatBaseChange.isIso_pushforwardBaseChange_of_isAffine`; `hγ` is its
compatibility with the unit of `π^* ⊣ π_*`, and `hδ` its compatibility with the quotient maps
`𝓕 ⟶ 𝓕/ℐ ⁿ⁺¹𝓕` that `Stacks.Coherent.directImageQuotientComparison` is the descent of. Neither
square is available here: both are statements about the base-changed morphism
`π' = π ×_{Spec B} Spec B ^∧` identified as such, and nothing in this tree builds that base
change, its properness, or the identification `g'^*(𝓕/ℐ ⁿ⁺¹𝓕) ≅ 𝓕'/ℐ' ⁿ⁺¹𝓕'` of the levels. They
are stated here as morphisms rather than isomorphisms because that is all the descent uses, and
because it makes the two squares the only content asked for.

The annihilation half of the conclusion over `Spec B ^∧` is discarded: returning it to `Spec B`
is the torsion-submodule clause of More on Algebra 05EC
(`Stacks.Algebraization.exists_primaryComponent_baseChange_equiv_adicCompletion`) applied to
levelwise kernels and cokernels, which is a separate assembly. -/
public theorem exists_isDirectImageCharacterized_of_baseChangeComparison
    (B : Type u) [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    {X' : Scheme.{u}} [IsNoetherian X'] (π : X' ⟶ Spec (.of B)) [IsProper π]
    (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)
    (G : CoherentAdicSystems (adicIdealSheaf B J))
    (β : (coherentAdicPullback π (adicIdealSheaf B J)).obj G ≅
      (completionFunctor X' ((adicIdealSheaf B J).comap π)).obj 𝓕)
    {X'' : Scheme.{u}} [IsNoetherian X'']
    (π' : X'' ⟶ Spec (.of (AdicCompletion J B))) [IsProper π']
    (𝓕' : AlgebraicGeometry.SheafOfModules.CoherentModules X''.ringCatSheaf)
    (β' : (coherentAdicPullback π'
          ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J))).obj
        ((coherentAdicPullback (adicCompletionSpecMap B J) (adicIdealSheaf B J)).obj G) ≅
      (completionFunctor X''
        (((adicIdealSheaf B J).comap (adicCompletionSpecMap B J)).comap π')).obj 𝓕')
    (𝒦 : (Spec (.of (AdicCompletion J B))).IdealSheafData)
    (hc : ∀ 𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules
        (Spec (.of (AdicCompletion J B))).ringCatSheaf,
      ((coherentAdicPullback (adicCompletionSpecMap B J) (adicIdealSheaf B J)).obj G ≅
          (completionFunctor (Spec (.of (AdicCompletion J B)))
            ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J))).obj 𝒜) →
        IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι 𝒦.support.compl)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction π').unit.app 𝒜.obj)))
    (ι : ((completionFunctor (Spec (.of (AdicCompletion J B)))
          ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J))).obj
        (properPushforwardCoherent π' 𝓕')).obj ⟶
      ((coherentAdicPullback (adicCompletionSpecMap B J) (adicIdealSheaf B J)).obj
        ((completionFunctor (Spec (.of B)) (adicIdealSheaf B J)).obj
          (properPushforwardCoherent π 𝓕))).obj)
    (θ : ∀ n : ℕ, (Scheme.Modules.pushforward π').obj
          (idealPowerQuotient
            (((adicIdealSheaf B J).comap (adicCompletionSpecMap B J)).comap π')
            (n + 1) 𝓕'.obj) ⟶
      (Scheme.Modules.pullback (adicCompletionSpecMap B J)).obj
        ((Scheme.Modules.pushforward π).obj
          (idealPowerQuotient ((adicIdealSheaf B J).comap π) (n + 1) 𝓕.obj)))
    (hδ : ∀ n : ℕ, ι.app (op n) ≫
          (Scheme.Modules.pullback (adicCompletionSpecMap B J)).map
            (eqToHom (completionFunctor_obj (Spec (.of B)) (adicIdealSheaf B J)
                (properPushforwardCoherent π 𝓕) n) ≫
              directImageQuotientComparison π (adicIdealSheaf B J) (n + 1) 𝓕.obj) =
        (eqToHom (completionFunctor_obj (Spec (.of (AdicCompletion J B)))
              ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J))
              (properPushforwardCoherent π' 𝓕') n) ≫
            directImageQuotientComparison π'
              ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J)) (n + 1) 𝓕'.obj) ≫ θ n)
    (hγ : ∀ n : ℕ,
        (directImageComparison π' ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J))
              ((coherentAdicPullback (adicCompletionSpecMap B J) (adicIdealSheaf B J)).obj G)
              𝓕' β').app (op n) ≫
            eqToHom (pushforward_completion_obj π'
              ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J)) 𝓕' n) ≫ θ n =
          (Scheme.Modules.pullback (adicCompletionSpecMap B J)).map
            ((directImageComparison π (adicIdealSheaf B J) G 𝓕 β).app (op n) ≫
              eqToHom (pushforward_completion_obj π (adicIdealSheaf B J) 𝓕 n))) :
    ∃ α : G.obj ⟶ ((completionFunctor (Spec (.of B)) (adicIdealSheaf B J)).obj
        (properPushforwardCoherent π 𝓕)).obj,
      IsDirectImageCharacterized π (adicIdealSheaf B J) G 𝓕 β α := by
  obtain ⟨α', hα', -⟩ := exists_isDirectImageCharacterized_isKernelCokernel_adicCompletionBase
    B J π' 𝒦 𝓕'
    ((coherentAdicPullback (adicCompletionSpecMap B J) (adicIdealSheaf B J)).obj G) β' hc
  refine (exists_isDirectImageCharacterized_of_adicCompletionPullback B J π 𝓕 G β (α' ≫ ι)
    fun n => ?_).imp fun α hα => hα.1
  rw [NatTrans.comp_app]
  exact (Category.assoc (obj := (Spec (.of (AdicCompletion J B))).Modules) _ _ _).trans
    ((congrArg (fun z => α'.app (op n) ≫ z) (hδ n)).trans
      ((Category.assoc (obj := (Spec (.of (AdicCompletion J B))).Modules) _ _ _).symm.trans
        ((congrArg (fun z => z ≫ θ n) (hα' n)).trans
          ((Category.assoc (obj := (Spec (.of (AdicCompletion J B))).Modules) _ _ _).trans
            (hγ n)))))

end Stacks.Algebraization

end
