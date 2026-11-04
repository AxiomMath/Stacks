module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackPresentationAssembly
public import StacksFrontier.Deformation.ToposThickening.IdealProductSequence

/-!
# Finite presentation across a first order thickening of ringed topoi

Let `(f, f')` be a morphism of first order thickenings of ringed topoi

```
  (Sh(C), O)   --i-->  (Sh(D), O')
      |                    |
      f                    f'
      v                    v
  (Sh(B), O_ℬ) --t-->  (Sh(B'), O_{ℬ'})
```

with square-zero ideals `I = Ker(i^♯) ⊂ O'` and `J = Ker(t^♯) ⊂ O_{ℬ'}`, let `ℱ'` be an
`O'`-module and set `ℱ = i^*ℱ'`. Stacks 08VU says that if `ℱ'` is flat over `O_{ℬ'}` and
`(f, f')` is strict, then `ℱ'` is of finite presentation over `O'` if and only if `ℱ` is of
finite presentation over `O`.

This file carries two steps of the proof which need neither flatness nor strictness; the
equivalence itself is
`Deformation.ToposThickening.isFinitePresentation_iff_pullbackModules_of_isFlat` in
`StacksFrontier/Deformation/ToposThickening/FinitePresentationFlatLift.lean`.

## Main results

* `Deformation.ToposThickening.isZero_of_isZero_pullbackModules`: **pullback along a first order
  thickening kills no nonzero module.** If `i^*𝒢' = 0` then `𝒢' = 0`.
* `Deformation.ToposThickening.epi_of_epi_map_pullbackModules`: **the surjectivity step of the
  proof of (2) ⇒ (1).** A map of `O'`-modules whose restriction `i^*φ` is surjective is itself
  surjective. The source's proof lifts a local presentation `O_U^{⊕n} ⟶ ℱ|_U ⟶ 0` to a map
  `(O'_U)^{⊕n} ⟶ ℱ'|_U`, and it is this lemma that makes the lift surjective — the lift reduces
  to the given surjection, since `i^*(O'_U)^{⊕n} = O_U^{⊕n}`.

## Implementation notes

Both results here rest on the ideal-product sequence

```
  0 ⟶ I·𝒢' ⟶ 𝒢' ⟶ i_*i^*𝒢' ⟶ 0
```

of `Deformation.ToposThickening.idealProductShortComplex_shortExact`, which is unconditional.
If `i^*𝒢' = 0` the sequence makes the inclusion `I·𝒢' ⟶ 𝒢'` invertible, and `I·𝒢'` is a direct
image (`Deformation.ToposThickening.essImage_idealProductSubmodule`, the essential-image
criterion of Stacks 08M3), so `𝒢' ≅ i_*𝒲` for some `𝒲`; transposing the inverse isomorphism
across the adjunction exhibits it as a morphism out of the zero object `i^*𝒢'`, hence as `0`,
so `𝟙 𝒢' = 0`.

Both uses of the adjunction take the same form: a morphism `𝒢' ⟶ i_*𝒯` is determined by its
transpose `i^*𝒢' ⟶ 𝒯`, and every morphism out of `i^*𝒢' = 0` is `0`. No additivity of the
direct image is needed for that, which is why the argument is phrased through
`CategoryTheory.Adjunction.homEquiv` rather than through a zero object of the target.

## Scope

The direction (1) ⇒ (2) of Stacks 08VU is Stacks 03DO,
`Stacks.Sheaves.FinitePresentation.isFinitePresentation_pullbackModules`. The exactness of the
lifted presentation in the converse, which is where flatness and strictness are used, is proved
in `StacksFrontier/Deformation/ToposThickening/FinitePresentationFlatLift.lean`, and the tag is
registered there.

## References

* [Stacks Project, Tag 08VU](https://stacks.math.columbia.edu/tag/08VU)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe v u v' u' w

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {i : RingedToposHom X Y}

/-- **Pullback along a first order thickening kills no nonzero module.** If the restriction
`i^*𝒢'` of a sheaf of `O'`-modules to the reduction is zero, then `𝒢'` is zero.

The ideal-product sequence `0 ⟶ I·𝒢' ⟶ 𝒢' ⟶ i_*i^*𝒢' ⟶ 0` has zero right-hand term, so the
inclusion of the ideal product is both a monomorphism and an epimorphism, hence invertible;
`I·𝒢'` is a direct image by the essential-image criterion of Stacks 08M3, so `𝒢' ≅ i_*𝒲` for
some `𝒲`, and the inverse of that isomorphism, transposed across the adjunction, is a morphism
out of the zero object `i^*𝒢'` and so vanishes. -/
theorem isZero_of_isZero_pullbackModules (hi : FirstOrderThickening i)
    (G' : SheafOfModules.{w} (ringSheaf Y.O))
    (hz : IsZero ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
      i.toRingedToposModulesHom).obj G')) :
    IsZero G' := by
  classical
  have hshort := idealProductShortComplex_shortExact hi G'
  have key : ∀ {T} (f : G' ⟶ i.pushforwardModules.obj T), f = 0 := fun {T} f =>
    (i.pullbackAdjPushforwardModulesViaComparison.homEquiv G' T).symm.injective
      (hz.eq_of_src _ _)
  have : Epi (idealProductSubmodule hi G').ι :=
    (ShortComplex.exact_iff_epi _ (key _)).mp hshort.exact
  have := hshort.mono_f
  have : IsIso (idealProductSubmodule hi G').ι := isIso_of_mono_of_epi _
  obtain ⟨W, ⟨e⟩⟩ : i.pushforwardModules.essImage G' :=
    Functor.essImage.ofIso (asIso (idealProductSubmodule hi G').ι)
      (essImage_idealProductSubmodule hi G')
  rw [IsZero.iff_id_eq_zero, ← e.inv_hom_id, key e.inv, zero_comp]

/-- **The surjectivity step of the proof of Stacks 08VU, (2) ⇒ (1).** A map of `O'`-modules whose
restriction to the reduction of a first order thickening is surjective is itself surjective.

In the source's proof a local surjection `O_U^{⊕n} ⟶ ℱ|_U` is lifted, after refining the
covering, to a map `(O'_U)^{⊕n} ⟶ ℱ'|_U`; since `i^*(O'_U)^{⊕n} = O_U^{⊕n}` the lift restricts
to the given surjection, and this lemma is what makes the lift itself surjective.

Pullback is a left adjoint, hence preserves the cokernel, so the cokernel of `φ` restricts to
the cokernel of `i^*φ`, which vanishes; `isZero_of_isZero_pullbackModules` then makes the
cokernel of `φ` itself vanish. -/
theorem epi_of_epi_map_pullbackModules (hi : FirstOrderThickening i)
    {G' H' : SheafOfModules.{w} (ringSheaf Y.O)} (φ : G' ⟶ H')
    (hφ : Epi ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
      i.toRingedToposModulesHom).map φ)) :
    Epi φ := by
  classical
  let : (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
      i.toRingedToposModulesHom).Additive := pullbackModules_additive
  let : PreservesColimitsOfSize.{0, 0}
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        i.toRingedToposModulesHom) :=
    i.pullbackAdjPushforwardModulesViaComparison.leftAdjoint_preservesColimits
  rw [Preadditive.epi_iff_isZero_cokernel]
  refine isZero_of_isZero_pullbackModules hi _ (IsZero.of_iso ?_
    (PreservesCokernel.iso (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
      i.toRingedToposModulesHom) φ))
  rw [← Preadditive.epi_iff_isZero_cokernel]
  exact hφ

end Deformation.ToposThickening

end
