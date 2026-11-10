module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.LeftTensorNotation
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.RelativeEquivalenceBaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.IdentityKernelDisplayVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaStrictlyPerfect

/-!
# The negative-degree vanishing of step 1 of Tag 0G0E, on the product

Let `k` be a field, let `X` be smooth and proper over `k`, let `K` be an object of
`D(𝒪_{X ×_k X})` whose Fourier-Mukai functor induces on `D_perf(𝒪_X)` an endofunctor isomorphic
to the identity, and let `ℰ` and `𝒢` be finite locally free `𝒪_X`-modules.  Writing

`L = K ⊗^𝐋 (ℰ ⊠ 𝒢)[0]`

for the object on `X ×_k X` that the display of [Stacks, Tag 0G0E] computes, this file proves
that for `i < 0` every morphism

`𝒪_{X ×_k X}[0] ⟶ L⟦i⟧`

is zero.  That is the first term of the source's display, `H^i(X × X, K ⊗^𝐋 (ℰ ⊠ 𝒢))`, read as a
`Hom`-group on the product itself; what
`Stacks.Duality.hom_single_pushforward_kernel_box_eq_zero_of_neg` gives is the *second* term, the
same group on `X` after `R pr_{2,*}`.  The passage between them is the derived adjunction, not the
Leray identification: `𝒪_{X × X}[0]` is `L pr_2^*(𝒪_X[0])`, so the two `Hom`-groups are identified
by `Lpr_2^* ⊣ Rpr_{2,*}` of [Stacks, Tag 079W] together with the commutation of `Rpr_{2,*}` with
the shift.

## Main definitions

* `Stacks.Duality.homSingleUnitPushforwardEquiv` — the derived adjunction read on morphisms out of
  the structure sheaf: `Hom(𝒪_V[0], B⟦i⟧) ≃ Hom(𝒪_W[0], (R p_*B)⟦i⟧)` for an arbitrary morphism of
  schemes `p : V ⟶ W`, an arbitrary `B` and an arbitrary degree.

## Main results

* `Stacks.Duality.hom_singleUnit_kernel_box_eq_zero_of_neg` — **the negative-degree vanishing of
  the first term of the display of [Stacks, Tag 0G0E]**: for `i < 0` every morphism
  `𝒪_{X ×_k X}[0] ⟶ (K ⊗^𝐋 (ℰ ⊠ 𝒢)[0])⟦i⟧` is zero.

## Implementation notes

*Why the adjunction and not Leray.*  The source writes the first equality of the display as
`H^i(X × X, -) = H^i(X, Rpr_{2,*}(-))`, which is [Stacks, Tag 0D5W]; crossing it changes the
ambient scheme *and* the ring the sections are taken over.  In `Hom`-form the same identification
is the derived adjunction `Lpr_2^* ⊣ Rpr_{2,*}`, which is available unconditionally for an
arbitrary morphism of ringed spaces as
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction`, and the only extra input is
that `Lpr_2^*` carries `𝒪_X[0]` to `𝒪_{X × X}[0]` — which is
`AlgebraicGeometry.dpullStructureSheafIso`, the structure sheaf being flat.  Nothing has to be said
about cohomology groups at all.

*Why the chain is read as a bijection rather than an additive map.*  `Adjunction.homEquiv` is an
`Equiv`; its additivity is not recorded, and the `Iso` transports at either end are composed with
it.  A vanishing hypothesis is therefore transported by applying the bijection to the morphism in
question *and* to `0`, both images being zero because the target group vanishes identically, and
then using injectivity.  That is also how
`AlgebraicGeometry.eq_zero_of_forall_hom_unit_tensor_dual_eq_zero` is arranged.

*Why the ringed-space names are written out in full.*  The namespace `Stacks.Duality` has its own
`derivedPullback` and `derivedPushforward`, the quasi-coherent scheme-level ones of
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/QuasiCoherentPullback.lean` and
`StacksFrontier/AlgebraicGeometry/Duality/QuasiCoherentPushforwardAdjoint.lean`.  Being declarations
of the namespace these statements are made in, they shadow the ringed-space functors of
[Stacks, Tag 079W] that `dpull` and `dpush` abbreviate, so an unqualified `derivedAdjunction`
elaborates against the wrong pair.  The adjunction is therefore named in full and the two functors
are written as `dpull` and `dpush`.

*The shift datum on the pushforward.*
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift` is the unique shift
commutation compatible with the adjunction -- it is defined as
`Adjunction.rightAdjointCommShift` of that very adjunction -- so no coherence between the two is
needed beyond their both being read off the same adjunction.  It is bound by `letI` rather than
activated globally, since it is a `def` and not an instance.

*The model of the derived categories.*  `CategoryTheory.HasDerivedCategory.standard` is activated
as a local instance at high priority, as in
`StacksFrontier/AlgebraicGeometry/Duality/IdentityKernelDisplayVanishing.lean`.

*Why the bijection is factored out.*  `Stacks.Duality.homSingleUnitPushforwardEquiv` is stated for
an arbitrary `B` rather than being inlined at the kernel box.  Inlined, the three-step composite
has to be unified against the display's object -- a term containing the derived tensor product,
the box comparison and two derived pullbacks -- at every step, and the elaboration of the
composite does not terminate within the heartbeat limit.  Stated at a variable `B` the same
composite elaborates in a fraction of a second, and the specialisation is a single application.

## References

* [Stacks Project, Tag 0G0E](https://stacks.math.columbia.edu/tag/0G0E)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

attribute [local instance 100000] HasDerivedCategory.standard

/-- **The derived adjunction, read on morphisms out of the structure sheaf.**  For a morphism of
schemes `p : V ⟶ W`, an object `B` of `D(𝒪_V)` and a degree `i`,

`Hom_{D(𝒪_V)}(𝒪_V[0], B⟦i⟧) ≃ Hom_{D(𝒪_W)}(𝒪_W[0], (R p_*B)⟦i⟧)`.

Three inputs, each unconditional: the adjunction `Lp^* ⊣ Rp_*` of [Stacks, Tag 079W]; that `Lp^*`
carries `𝒪_W[0]` to `𝒪_V[0]`, which is `AlgebraicGeometry.dpullStructureSheafIso`, the structure
sheaf being flat; and that `Rp_*` commutes with the shift, which is
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift`, the shift datum
the adjunction itself induces on its right adjoint.

In cohomological terms this is the Leray identification `H^i(V, B) = H^i(W, R p_*B)` of
[Stacks, Tag 0D5W]; stated on `Hom`-groups it needs none of the apparatus of derived global
sections, only the adjunction. -/
def homSingleUnitPushforwardEquiv {V W : Scheme.{u}} (p : V ⟶ W)
    (B : DerivedCategory V.Modules) (i : ℤ) :
    ((DerivedCategory.singleFunctor V.Modules 0).obj
          (SheafOfModules.unit V.ringCatSheaf) ⟶ B⟦i⟧) ≃
      ((DerivedCategory.singleFunctor W.Modules 0).obj (SheafOfModules.unit W.ringCatSheaf) ⟶
        ((dpush p).obj B)⟦i⟧) :=
  letI := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift
    p.toLRSHom.toShHom
  (Iso.homCongr (dpullStructureSheafIso p) (Iso.refl (B⟦i⟧))).symm.trans
    (((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
          p.toLRSHom.toShHom).homEquiv _ _).trans
      (Iso.homToEquiv
        (((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          p.toLRSHom.toShHom).commShiftIso i).app B)))

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The negative-degree vanishing of the first term of the display of [Stacks, Tag 0G0E]**: for
`i < 0` every morphism

`𝒪_{X ×_k X}[0] ⟶ (K ⊗^𝐋 (ℰ ⊠ 𝒢)[0])⟦i⟧`

is zero, for a kernel `K` representing the identity on perfect complexes and finite locally free
`ℰ` and `𝒢`.  This is the group `H^i(X × X, K ⊗^𝐋 (ℰ ⊠ 𝒢))` the source's display starts from.

The derived adjunction `Lpr_2^* ⊣ Rpr_{2,*}` identifies it with the group
`Hom(𝒪_X[0], (R pr_{2,*}(K ⊗^𝐋 (ℰ ⊠ 𝒢)[0]))⟦i⟧)` on `X`, which vanishes by
`Stacks.Duality.hom_single_pushforward_kernel_box_eq_zero_of_neg`; the identification needs that
`Lpr_2^*` carries `𝒪_X[0]` to `𝒪_{X × X}[0]` and that `Rpr_{2,*}` commutes with the shift. -/
theorem hom_singleUnit_kernel_box_eq_zero_of_neg
    (K : DerivedCategory (Limits.pullback f f).Modules) (hΦ : RepresentsIdentityOnPerfect f K)
    (E G : X.Modules)
    (hE : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hG : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G)
    (i : ℤ) (hi : i < 0)
    (φ : (DerivedCategory.singleFunctor (Limits.pullback f f).Modules 0).obj
          (SheafOfModules.unit (Limits.pullback f f).ringCatSheaf) ⟶
        ((dtenLeft (Limits.pullback f f) K).obj
          ((DerivedCategory.singleFunctor (Limits.pullback f f).Modules 0).obj
            (externalTensorProduct f f E G)))⟦i⟧) :
    φ = 0 := by
  have hvan := hom_single_pushforward_kernel_box_eq_zero_of_neg f K hΦ E G hE hG
    (SheafOfModules.unit X.ringCatSheaf) i hi
  have e := homSingleUnitPushforwardEquiv (Limits.pullback.snd f f)
    ((dtenLeft (Limits.pullback f f) K).obj
      ((DerivedCategory.singleFunctor (Limits.pullback f f).Modules 0).obj
        (externalTensorProduct f f E G))) i
  exact e.injective ((hvan (e φ)).trans (hvan (e 0)).symm)

end Stacks.Duality

end
