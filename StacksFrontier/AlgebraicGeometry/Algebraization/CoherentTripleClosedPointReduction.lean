module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleClosedFibreVanishing
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.SubQuotient
public import StacksFrontier.AlgebraicGeometry.Divisors.EmbeddedPoints.SupportStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.EmbeddedPoints.SupportedSectionsQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Divisors.EmbeddedPoints.SupportedSectionsQuotient
public import StacksFrontier.AlgebraicGeometry.Divisors.EmbeddedPoints.SupportedSectionsStalk

/-!
# The opening reduction of the induction step of Tag 0F27

The induction step of [Stacks, Tag 0F27] opens by replacing a coherent triple `(F, F₀, α)` by
`(F, F₀/G₀, α)`, where `G₀ ⊆ F₀` is the submodule of sections supported at the closed point, and
comparing the two through the short exact sequence

`0 → (0, G₀, 0) → (F, F₀, α) → (F, F₀/G₀, α) → 0`

whose left member has vanishing punctured-spectrum member. This file builds that sequence.

Polynomiality of a given degree transfers across such a sequence by
`Stacks.Algebraization.exists_polynomial_eulerCharacteristic_twistZ_of_shortExact_isZero`, so
after this reduction the tag may assume that the closed point is not an associated point of the
closed-fibre member — which is the hypothesis of
`Stacks.Algebraization.CoherentTriple.isZero_F₀_of_isZero_F`, the vanishing clause of the
induction step. That the quotient really has no associated point at the closed point is proved
here too, from
`Stacks.AlgebraicGeometry.EmbeddedPoints.not_isAssociatedPoint_cokernel_supportedSections`.

## Main definitions

* `Stacks.Algebraization.CoherentTriple.closedPointSubmodule`: the submodule `G₀ ⊆ F₀` of
  sections supported at the closed point of the closed fibre.
* `Stacks.Algebraization.CoherentTriple.closedPointTriple`: the triple `(0, G₀, 0)`.
* `Stacks.Algebraization.CoherentTriple.quotientTriple`: the triple `(F, F₀/G₀, α)`.
* `Stacks.Algebraization.CoherentTriple.quotientPullbackIso`: the inverse image of the quotient
  map on the punctured closed fibre, as an isomorphism.
* `Stacks.Algebraization.CoherentTriple.closedPointHom` and
  `Stacks.Algebraization.CoherentTriple.quotientHom`: the two morphisms of the sequence.

## Main results

* `Stacks.Algebraization.isFTorsionFree_of_isZero`: a vanishing module on the punctured spectrum
  is `f`-torsion-free.
* `Stacks.Algebraization.CoherentTriple.notMem_supp_closedPointSubmodule`: the sections
  supported at the closed point have support in that point.
* `Stacks.Algebraization.CoherentTriple.isZero_pullback_closedPointSubmodule`: hence they
  restrict to zero on the punctured closed fibre, which is what makes `(0, G₀, 0)` a coherent
  triple.
* `Stacks.Algebraization.CoherentTriple.isIso_pullback_map_quotientπ`: the quotient map becomes
  an isomorphism on the punctured closed fibre, which is what makes `(F, F₀/G₀, α)` a coherent
  triple.
* `Stacks.Algebraization.CoherentTriple.shortExact_closedPointReduction`: **the short exact
  sequence of the opening reduction of the induction step of [Stacks, Tag 0F27].**
* `Stacks.Algebraization.CoherentTriple.exists_shortExact_isZero_F`: the same, packaged as
  the existence statement the first clause of
  `Stacks.Algebraization.HasHilbertInductionStep` asks for.
* `Stacks.Algebraization.CoherentTriple.not_isAssociatedPoint_closedPoint_quotientTriple`:
  **the payoff of the reduction, that the closed point is not an associated point of `F₀/G₀`.**
* `Stacks.Algebraization.CoherentTriple.eulerCharacteristic_quotientTriple_eq_zero_of_isZero_F`:
  hence the vanishing clause of the induction step holds for the quotient triple with no
  hypothesis left over.

## Implementation notes

The submodule of sections supported at the closed point is
`AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule` at the closed subset
`{𝔪}`; it is quasi-coherent by [Stacks, Tag 07ZP] and therefore coherent, being a quasi-coherent
submodule of a coherent module on a locally Noetherian scheme ([Stacks, Tag 01Y1]). Its stalk
vanishes away from the closed point, so its support is contained in that point and its
restriction to the punctured closed fibre is a zero object
(`AlgebraicGeometry.isZero_pullback_of_forall_notMem_supp`). That the punctured closed fibre is
the complement of the closed point is `f ∈ 𝔪`, through
`Stacks.Algebraization.puncturedClosedFibre_eq_puncturedSpectrum`.

Both gluing data of the new triples come from that vanishing: the one for `(0, G₀, 0)` is an
isomorphism of two zero objects — the punctured-spectrum member of `(0, G₀, 0)` is realised as
`Coker(id_F)`, so that its coherence is the coherence of a cokernel rather than a separate
instance — and the one for `(F, F₀/G₀, α)` is `α` followed by the inverse
image of the quotient map, which is an isomorphism because the inverse image is a left adjoint
and kills `G₀` (`Stacks.AlgebraicGeometry.EmbeddedPoints.isIso_map_cokernelπ_of_isZero`).

The payoff of the reduction is
`Stacks.AlgebraicGeometry.EmbeddedPoints.not_isAssociatedPoint_cokernel_supportedSections`, which
is proved for an arbitrary module on an arbitrary scheme and needs of the point only that it is
closed. It is **not** proved through depth: the usual argument, that a module of depth zero
becomes one of positive depth once its sections supported at the maximal ideal are divided out,
is available in the library at the level of modules
(`Dualizing.depth_quotientMaximalIdealPowerTorsion_pos`) but would have to be crossed to the
sheaf side, whereas the sheaf-level diagram chase is shorter and assumes nothing.

## References

* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
* [Stacks Project, Tag 07ZP](https://stacks.math.columbia.edu/tag/07ZP)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing Opposite
open scoped ZeroObject

universe u

namespace Stacks.Algebraization

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

/-! ### The zero module as a member of a coherent triple -/

/-- **A vanishing module on the punctured spectrum is `f`-torsion-free**, its sections over every
open being subsingleton. -/
public theorem isFTorsionFree_of_isZero (A : Type u) [CommRing A] [IsLocalRing A] (f : A)
    {F : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules} (hF : IsZero F) :
    IsFTorsionFree A f F := by
  intro V x y _
  have := subsingleton_sections_of_isZero hF V
  exact Subsingleton.elim x y

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {f : A}
  [IsLocalRing (A ⧸ Ideal.span {f})]

/-! ### The sections supported at the closed point -/

omit [IsLocalRing A] [IsNoetherianRing A] in
/-- **The closed point of the closed fibre is a closed subset of it**, its prime being the
maximal ideal. -/
public theorem isClosed_singleton_closedPoint_closedFibre :
    IsClosed ({IsLocalRing.closedPoint (A ⧸ Ideal.span {f})} :
      Set (closedFibre A f)) :=
  (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2
    (IsLocalRing.maximalIdeal.isMaximal (A ⧸ Ideal.span {f}))

/-- **The submodule `G₀ ⊆ F₀` of sections of the closed-fibre member supported at the closed
point**, the subobject the induction step of [Stacks, Tag 0F27] divides out. -/
public abbrev CoherentTriple.closedPointSubmodule (T : CoherentTriple A f) :
    _root_.SheafOfModules.Submodule T.F₀ :=
  Scheme.Modules.supportedSectionsSubmodule
    ({IsLocalRing.closedPoint (A ⧸ Ideal.span {f})} : Set (closedFibre A f)) T.F₀

/-- The sections supported at the closed point form a quasi-coherent submodule, by
[Stacks, Tag 07ZP]. -/
public theorem CoherentTriple.isQuasicoherent_closedPointSubmodule (T : CoherentTriple A f) :
    T.closedPointSubmodule.toSheafOfModules.IsQuasicoherent := by
  have := T.coherent_F₀
  have : T.F₀.IsQuasicoherent := isQuasicoherent_of_isCoherent _
  exact Stacks.AlgebraicGeometry.EmbeddedPoints.supportedSectionsSubmodule_isQuasicoherent _
    isClosed_singleton_closedPoint_closedFibre
    (Stacks.AlgebraicGeometry.EmbeddedPoints.isRetrocompact_of_isLocallyNoetherian _)
    T.F₀ inferInstance

/-- The sections supported at the closed point form a coherent submodule, being a quasi-coherent
submodule of a coherent module on a locally Noetherian scheme ([Stacks, Tag 01Y1]). -/
public theorem CoherentTriple.isCoherent_closedPointSubmodule (T : CoherentTriple A f) :
    T.closedPointSubmodule.toSheafOfModules.IsCoherent := by
  have := T.coherent_F₀
  have := T.isQuasicoherent_closedPointSubmodule
  exact @Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_of_mono_of_isQuasicoherent
    (closedFibre A f) _ T.F₀ T.closedPointSubmodule.toSheafOfModules _ _
    T.closedPointSubmodule.ι (SheafOfModules.Submodule.instMonoι _)

omit [IsNoetherianRing A] in
/-- **The sections supported at the closed point have support in that point.** -/
public theorem CoherentTriple.notMem_supp_closedPointSubmodule (T : CoherentTriple A f)
    {y : closedFibre A f}
    (hy : y ∉ ({IsLocalRing.closedPoint (A ⧸ Ideal.span {f})} : Set (closedFibre A f))) :
    y ∉ SheafOfModules.supp T.closedPointSubmodule.toSheafOfModules := by
  have h := Stacks.AlgebraicGeometry.EmbeddedPoints.isZero_stalkFunctor_obj_supportedSections
    _ T.F₀ hy
  intro hmem
  exact (not_nontrivial_iff_subsingleton.mpr
      (Stacks.AlgebraicGeometry.EmbeddedPoints.subsingleton_of_isZero h))
    ((SheafOfModules.mem_supp_iff_nontrivial_stalk _ y).mp hmem)

omit [IsNoetherianRing A] in
/-- **The sections supported at the closed point restrict to zero on the punctured closed
fibre.** For `f` in the maximal ideal the punctured closed fibre misses the closed point, and a
module whose support the image of an open immersion avoids has vanishing inverse image there. -/
public theorem CoherentTriple.isZero_pullback_closedPointSubmodule (hf : f ∈ maximalIdeal A)
    (T : CoherentTriple A f) :
    IsZero ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj
      T.closedPointSubmodule.toSheafOfModules) := by
  refine AlgebraicGeometry.isZero_pullback_of_forall_notMem_supp _ _ fun x => ?_
  refine T.notMem_supp_closedPointSubmodule ?_
  have hx : ((puncturedClosedFibre A f).ι x) ∈
      (puncturedClosedFibre A f : Set (closedFibre A f)) := x.2
  have hset : (puncturedClosedFibre A f : Set (closedFibre A f)) =
      ((Stacks.Divisors.puncturedSpectrum (A ⧸ Ideal.span {f}) :
        (closedFibre A f).Opens) : Set (closedFibre A f)) :=
    congrArg (fun U : (closedFibre A f).Opens => (U : Set (closedFibre A f)))
      (puncturedClosedFibre_eq_puncturedSpectrum A f hf)
  rw [hset] at hx
  exact hx

/-! ### The two triples of the reduction -/

/-- **The triple `(0, G₀, 0)`**, the left member of the short exact sequence with which the
induction step of [Stacks, Tag 0F27] opens. -/
@[reducible]
public def CoherentTriple.closedPointTriple (hf : f ∈ maximalIdeal A) (T : CoherentTriple A f) :
    CoherentTriple A f where
  F := cokernel (𝟙 T.F)
  F₀ := T.closedPointSubmodule.toSheafOfModules
  coherent_F := by
    have := T.coherent_F
    exact _root_.SheafOfModules.cokernel_isCoherent (𝟙 T.F)
  coherent_F₀ := T.isCoherent_closedPointSubmodule
  torsionFree := isFTorsionFree_of_isZero A f (isZero_cokernel_of_epi (𝟙 T.F))
  alpha := (isZero_obj_of_isZero _ (isZero_cokernel_of_epi (𝟙 T.F))).iso
    (T.isZero_pullback_closedPointSubmodule hf)

omit [IsNoetherianRing A] in
/-- **The quotient map becomes an isomorphism on the punctured closed fibre.** The inverse image
along the inclusion of the punctured closed fibre is a left adjoint, so it preserves cokernels,
and it kills the sections supported at the closed point. -/
public theorem CoherentTriple.isIso_pullback_map_quotientπ (hf : f ∈ maximalIdeal A)
    (T : CoherentTriple A f) :
    IsIso ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map
      (cokernel.π T.closedPointSubmodule.ι)) :=
  Stacks.AlgebraicGeometry.EmbeddedPoints.isIso_map_cokernelπ_of_isZero
    (Scheme.Modules.pullback (puncturedClosedFibre A f).ι) T.closedPointSubmodule.ι
    (T.isZero_pullback_closedPointSubmodule hf)

/-- The inverse image of the quotient map on the punctured closed fibre, as an isomorphism. -/
public def CoherentTriple.quotientPullbackIso (hf : f ∈ maximalIdeal A)
    (T : CoherentTriple A f) :
    (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀ ≅
      (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj
        (cokernel T.closedPointSubmodule.ι) :=
  @asIso _ _ _ _ _ (T.isIso_pullback_map_quotientπ hf)

/-- **The triple `(F, F₀/G₀, α)`**, the right member of the short exact sequence with which the
induction step of [Stacks, Tag 0F27] opens. Its punctured-spectrum member is that of the
original triple. -/
@[reducible]
public def CoherentTriple.quotientTriple (hf : f ∈ maximalIdeal A) (T : CoherentTriple A f) :
    CoherentTriple A f where
  F := T.F
  F₀ := cokernel T.closedPointSubmodule.ι
  coherent_F := T.coherent_F
  coherent_F₀ := by
    have := T.isCoherent_closedPointSubmodule
    have := T.coherent_F₀
    exact _root_.SheafOfModules.cokernel_isCoherent T.closedPointSubmodule.ι
  torsionFree := T.torsionFree
  alpha := T.alpha ≪≫ T.quotientPullbackIso hf

/-! ### The short exact sequence -/

/-- The inclusion of `(0, G₀, 0)` into the triple. -/
public def CoherentTriple.closedPointHom (hf : f ∈ maximalIdeal A) (T : CoherentTriple A f) :
    (T.closedPointTriple hf).Hom T where
  onPunctured := 0
  onClosedFibre := T.closedPointSubmodule.ι
  compatible := (isZero_obj_of_isZero
    (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
      (Stacks.Divisors.puncturedSpectrum A)))
    (isZero_cokernel_of_epi (𝟙 T.F))).eq_of_src _ _

/-- The quotient map onto `(F, F₀/G₀, α)`. -/
public def CoherentTriple.quotientHom (hf : f ∈ maximalIdeal A) (T : CoherentTriple A f) :
    T.Hom (T.quotientTriple hf) where
  onPunctured := 𝟙 T.F
  onClosedFibre := cokernel.π T.closedPointSubmodule.ι
  compatible := by
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
    rfl

/-- **The short exact sequence of the opening reduction of the induction step of
[Stacks, Tag 0F27].** On the punctured spectrum it is `0 → 0 → F → F → 0`; on the closed fibre
it is the sequence of the submodule of sections supported at the closed point and the quotient
by it. -/
public theorem CoherentTriple.shortExact_closedPointReduction (hf : f ∈ maximalIdeal A)
    (T : CoherentTriple A f) :
    CoherentTriple.ShortExact (T.closedPointHom hf) (T.quotientHom hf) := by
  have : Mono T.closedPointSubmodule.ι := SheafOfModules.Submodule.instMonoι _
  have hZ := isZero_cokernel_of_epi (𝟙 T.F)
  refine { zero_punctured := Limits.zero_comp
           zero_closedFibre := cokernel.condition _
           punctured := ShortComplex.ShortExact.mk' ?_ ⟨fun g h _ => hZ.eq_of_tgt g h⟩
             (inferInstanceAs (Epi (𝟙 T.F)))
           closedFibre := ShortComplex.shortExact_mk_cokernel_π T.closedPointSubmodule.ι }
  exact (ShortComplex.exact_iff_mono _ (hZ.eq_of_src _ _)).2 (inferInstanceAs (Mono (𝟙 T.F)))

/-- **The opening reduction of the induction step of [Stacks, Tag 0F27], as the existence
statement the first clause of `Stacks.Algebraization.HasHilbertInductionStep` asks for**: every
coherent triple sits in a short exact sequence whose left member has vanishing
punctured-spectrum member and whose right member has the same punctured-spectrum member. -/
public theorem CoherentTriple.exists_shortExact_isZero_F (hf : f ∈ maximalIdeal A)
    (T : CoherentTriple A f) :
    ∃ (K T' : CoherentTriple A f) (φ : K.Hom T) (ψ : T.Hom T'),
      IsZero K.F ∧ CoherentTriple.ShortExact φ ψ ∧ T'.F = T.F :=
  ⟨T.closedPointTriple hf, T.quotientTriple hf, T.closedPointHom hf, T.quotientHom hf,
    isZero_cokernel_of_epi (𝟙 T.F), T.shortExact_closedPointReduction hf, rfl⟩

/-! ### The payoff of the reduction -/

/-- **The payoff of the opening reduction of the induction step of [Stacks, Tag 0F27]: the closed
point of the closed fibre is not an associated point of `F₀/G₀`.**

This is
`Stacks.AlgebraicGeometry.EmbeddedPoints.not_isAssociatedPoint_cokernel_supportedSections` at the
closed point of the closed fibre, which is a closed subset of it by
`Stacks.Algebraization.isClosed_singleton_closedPoint_closedFibre`. It is exactly the hypothesis
of `Stacks.Algebraization.CoherentTriple.isZero_F₀_of_isZero_F`, so after this reduction the
vanishing clause of the induction step is available without further assumption. -/
public theorem CoherentTriple.not_isAssociatedPoint_closedPoint_quotientTriple
    (hf : f ∈ maximalIdeal A) (T : CoherentTriple A f) :
    ¬ Stacks.Divisors.IsAssociatedPoint (T.quotientTriple hf).F₀
      (IsLocalRing.closedPoint (A ⧸ Ideal.span {f})) := by
  have := T.coherent_F₀
  exact Stacks.AlgebraicGeometry.EmbeddedPoints.not_isAssociatedPoint_cokernel_supportedSections
    T.F₀ (isQuasicoherent_of_isCoherent _) isClosed_singleton_closedPoint_closedFibre

/-- **The vanishing clause of the induction step of [Stacks, Tag 0F27] for the quotient triple,
with no hypothesis left over.** A coherent triple obtained from the opening reduction and whose
punctured-spectrum member vanishes has Euler characteristic `0`: the reduction has removed the
associated point at the closed point, which is what
`Stacks.Algebraization.CoherentTriple.eulerCharacteristic_eq_zero_of_isZero_F` needs. -/
public theorem CoherentTriple.eulerCharacteristic_quotientTriple_eq_zero_of_isZero_F
    (hf : f ∈ maximalIdeal A) (hreg : IsRegular f) (T : CoherentTriple A f)
    (hT : IsZero (T.quotientTriple hf).F) :
    (T.quotientTriple hf).eulerCharacteristic hf hreg = 0 :=
  CoherentTriple.eulerCharacteristic_eq_zero_of_isZero_F hf hreg (T.quotientTriple hf) hT
    (T.not_isAssociatedPoint_closedPoint_quotientTriple hf)

end

end Stacks.Algebraization

end
