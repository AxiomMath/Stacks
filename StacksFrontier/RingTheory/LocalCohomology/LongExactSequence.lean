module

public import StacksFrontier.RingTheory.LocalCohomology.LongExactSequence.CrossUniverse

/-!
# The long exact sequence of local cohomology

Let `A` be a commutative ring, let `I = (f₁, …, f_r)` be a finitely generated ideal, let
`Y = V(I) ⊂ Spec A` and let

`0 → N → F → M → 0`

be a short exact sequence of `A`-modules. The induction in the proof of [Stacks, Tag 0DX7] needs
the long exact sequence

`⋯ → H^i_Y(N) → H^i_Y(F) → H^i_Y(M) → H^{i+1}_Y(N) → ⋯`

of local cohomology modules. Here it is obtained from the Čech model, with no triangulated
structure and no maps between local cohomology modules; the triangulated route is available
elsewhere, see the implementation notes below.

The sequence is obtained from the Čech model of
`StacksFrontier/RingTheory/LocalCohomology/CechModel.lean`. Localization is an exact functor and a
direct sum of exact sequences of modules is exact, so the extended alternating Čech complexes of
`N`, `F` and `M` form a short exact sequence of cochain complexes
(`Stacks.LocalCohomology.LongExactSequence.shortExact_map_extendedCechFunctor`); Mathlib's
snake lemma for complexes then produces the connecting map and the long exact sequence of their
cohomology modules, and the Čech model identifies those with the local cohomology modules.

## Main definitions

* `Stacks.LocalCohomology.cechConnecting` — the connecting map
  `H^i(C^•(f; M)) ⟶ H^{i+1}(C^•(f; N))`.

## Main results

* `Stacks.LocalCohomology.exists_cechHomology_of_cechConnecting_eq_zero` — **exactness of
  `H^i(C^•(f; F)) → H^i(C^•(f; M)) → H^{i+1}(C^•(f; N))`**, in elements.
* `Stacks.LocalCohomology.isZero_homology_localCohomology_of_shortExact` — **the form the
  descending induction of Tag 0DX7 consumes**: if `H^i_Y(F) = 0` and `H^{i+1}_Y(N) = 0` then
  `H^i_Y(M) = 0`.
* `Stacks.LocalCohomology.isZero_homology_localCohomology_middle_of_shortExact` and
  `Stacks.LocalCohomology.isZero_homology_localCohomology_sub_of_shortExact` — the two companion
  vanishing statements coming from the other two exactness assertions of the sequence.
* `Stacks.LocalCohomology.nonempty_iso_homology_localCohomology_succ_of_shortExact` — the
  isomorphism `H^i_Y(M) ≅ H^{i+1}_Y(N)` when `H^i_Y(F)` and `H^{i+1}_Y(F)` both vanish.
* `Stacks.LocalCohomology.isZero_homology_localCohomology_uliftModule_iff` — **local cohomology
  does not see a universe lift of its coefficient module**: `H^i_Y(M) = 0` for `M` in
  `ModuleCat.{u} A` if and only if `H^i_Y(ULift.{v} M) = 0` in `ModuleCat.{max u v} A`. The two
  sides of the equivalence (1) ⇔ (2) of Tag 0DX7 live in these two categories.

## Implementation notes

At the level of Čech complexes the long exact sequence is available with all of its maps: the
short exactness statement of `LongExactSequence/Functoriality.lean` feeds directly into
`CategoryTheory.ShortComplex.ShortExact.δ` and
`CategoryTheory.ShortComplex.ShortExact.homology_exact₁`, `…₂`, `…₃`.

At the level of *local cohomology* only the map-free consequences are stated: a vanishing, or the
existence of an isomorphism. These are exactly what the descending induction of Tag 0DX7 consumes,
and they transport along
`Stacks.LocalCohomology.nonempty_homology_localCohomology_iso_cechHomology`, which identifies the
two sides one module at a time.

The sequence *with* its maps is not stated here, but it is no longer missing from the library:
`StacksFrontier/RingTheory/LocalCohomology/LongExactSequence/Triangulated.lean` builds the
triangulated route. `Dualizing.localCohomologyFunctor` does carry a `CommShift ℤ` structure
(`Stacks.LocalCohomology.localCohomologyFunctorCommShift`) and is triangulated
(`Stacks.LocalCohomology.localCohomologyFunctor_isTriangulated`), because the derived objects with
`I`-power-torsion cohomology form a triangulated subcategory
(`Stacks.LocalCohomology.derivedPowerTorsionProperty_isTriangulated`) and `RΓ_{V(I)}` is the right
adjoint of its inclusion. That file supplies the map
`Stacks.LocalCohomology.localCohomologyModuleMap` induced by a map of modules, exactness at the
middle term (`Stacks.LocalCohomology.exact_localCohomologyModuleMap`) and the two surjectivity
criteria that come from exactness one step out.

The Čech route below is kept because it is the one the descending induction of Tag 0DX7 consumes:
it needs no triangulated structure, and the statements it proves are map-free vanishings and
isomorphisms, which transport along
`Stacks.LocalCohomology.nonempty_homology_localCohomology_iso_cechHomology` one module at a time.

No `@[stacks]` attribute is placed. The long exact sequence is not itself a tagged statement of
the Stacks project; it is used inside the proof of Tag 0DX7, and the part of that tag it unlocks —
the equivalence of its first two conditions — is proved in
`StacksFrontier/RingTheory/LocalCohomology/LongExactSequence/AllModules.lean`, which also carries no
attribute because the third condition of the tag is geometric and is not proved there.

## References

* [Stacks Project, Tag 0DX7](https://stacks.math.columbia.edu/tag/0DX7)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
* [Stacks Project, Tag 0111](https://stacks.math.columbia.edu/tag/0111)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
  (S : ShortComplex (ModuleCat.{max u v} R))

/-! ### The long exact sequence of the Čech complexes -/

/-- **The connecting map of the Čech long exact sequence.** For a short exact sequence
`0 → N → F → M → 0` of modules this is the map
`H^i(C^•(f₁, …, f_r; M)) ⟶ H^{i+1}(C^•(f₁, …, f_r; N))` produced by the snake lemma from the
short exact sequence of Čech complexes. -/
def cechConnecting (hS : S.ShortExact) (i : ℤ) :
    (extendedCechComplex f S.X₃).homology i ⟶
      (extendedCechComplex f S.X₁).homology (i + 1) :=
  (LongExactSequence.shortExact_map_extendedCechFunctor.{v} f S hS).δ i (i + 1) rfl

/-- **Exactness of `H^i(C^•(f; F)) → H^i(C^•(f; M)) → H^{i+1}(C^•(f; N))`.** A Čech cohomology
class of `M` in degree `i` killed by the connecting map is the image of a class of `F`. -/
theorem exists_cechHomology_of_cechConnecting_eq_zero (hS : S.ShortExact) (i : ℤ)
    (x : (extendedCechComplex f S.X₃).homology i)
    (hx : cechConnecting.{v} f S hS i x = 0) :
    ∃ y : (extendedCechComplex f S.X₂).homology i,
      HomologicalComplex.homologyMap
        ((extendedCechFunctor.{v} f).map S.g) i y = x :=
  (ShortComplex.moduleCat_exact_iff _).1
    ((LongExactSequence.shortExact_map_extendedCechFunctor.{v} f S hS).homology_exact₃
      i (i + 1) rfl) x hx

/-- **Exactness of `H^i(C^•(f; M)) → H^{i+1}(C^•(f; N)) → H^{i+1}(C^•(f; F))`.** A Čech
cohomology class of `N` in degree `i + 1` mapping to zero in `F` comes from the connecting map. -/
theorem exists_cechConnecting_eq (hS : S.ShortExact) (i : ℤ)
    (x : (extendedCechComplex f S.X₁).homology (i + 1))
    (hx : HomologicalComplex.homologyMap
      ((extendedCechFunctor.{v} f).map S.f) (i + 1) x = 0) :
    ∃ y : (extendedCechComplex f S.X₃).homology i, cechConnecting.{v} f S hS i y = x :=
  (ShortComplex.moduleCat_exact_iff _).1
    ((LongExactSequence.shortExact_map_extendedCechFunctor.{v} f S hS).homology_exact₁
      i (i + 1) rfl) x hx

/-- **Exactness of `H^i(C^•(f; N)) → H^i(C^•(f; F)) → H^i(C^•(f; M))`.** -/
theorem exists_cechHomology_of_homologyMap_eq_zero (hS : S.ShortExact) (i : ℤ)
    (x : (extendedCechComplex f S.X₂).homology i)
    (hx : HomologicalComplex.homologyMap
      ((extendedCechFunctor.{v} f).map S.g) i x = 0) :
    ∃ y : (extendedCechComplex f S.X₁).homology i,
      HomologicalComplex.homologyMap
        ((extendedCechFunctor.{v} f).map S.f) i y = x :=
  (ShortComplex.moduleCat_exact_iff _).1
    ((LongExactSequence.shortExact_map_extendedCechFunctor.{v} f S hS).homology_exact₂
      i) x hx

/-! ### Transport to local cohomology -/

/-- The Čech model identifies vanishing of Čech cohomology with vanishing of local cohomology. -/
theorem isZero_cechHomology_iff_isZero_homology_localCohomology
    (I : Ideal R) (hI : I.FG) (hIf : Ideal.span (Set.range f) = I)
    (M : ModuleCat.{max u v} R) (i : ℤ) :
    IsZero ((extendedCechComplex f M).homology i) ↔
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj
        ((Dualizing.derivedPowerTorsionProperty R I hI).ι.obj
          ((Dualizing.localCohomologyFunctor R I hI).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M)))) := by
  obtain ⟨e⟩ := nonempty_homology_localCohomology_iso_cechHomology f M I hI hIf i
  exact e.isZero_iff.symm

/-- **The long exact sequence of local cohomology, in the form the descending induction of
[Stacks, Tag 0DX7] uses.** Let `0 → N → F → M → 0` be a short exact sequence of `A`-modules and
`I = (f₁, …, f_r)`. If the local cohomology of `F` vanishes in degree `i` and that of `N` vanishes
in degree `i + 1`, then that of `M` vanishes in degree `i`.

This is exactness of `H^i_{V(I)}(F) → H^i_{V(I)}(M) → H^{i+1}_{V(I)}(N)`, applied with both outer
terms zero. The maps themselves cannot be named at this level: see the implementation notes. -/
theorem isZero_homology_localCohomology_of_shortExact
    (I : Ideal R) (hI : I.FG) (hIf : Ideal.span (Set.range f) = I) (hS : S.ShortExact) (i : ℤ)
    (hF : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj
      ((Dualizing.derivedPowerTorsionProperty R I hI).ι.obj
        ((Dualizing.localCohomologyFunctor R I hI).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj S.X₂)))))
    (hN : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) (i + 1)).obj
      ((Dualizing.derivedPowerTorsionProperty R I hI).ι.obj
        ((Dualizing.localCohomologyFunctor R I hI).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj S.X₁))))) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj
      ((Dualizing.derivedPowerTorsionProperty R I hI).ι.obj
        ((Dualizing.localCohomologyFunctor R I hI).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj S.X₃)))) := by
  rw [← isZero_cechHomology_iff_isZero_homology_localCohomology f I hI hIf] at hF hN ⊢
  exact ((LongExactSequence.shortExact_map_extendedCechFunctor.{v} f S hS).homology_exact₃
    i (i + 1) rfl).isZero_of_both_isZero hF hN

/-- **Exactness of `H^i_{V(I)}(N) → H^i_{V(I)}(F) → H^i_{V(I)}(M)`, with both outer terms zero.**
If the local cohomology of `N` and of `M` vanishes in degree `i`, so does that of `F`. -/
theorem isZero_homology_localCohomology_middle_of_shortExact
    (I : Ideal R) (hI : I.FG) (hIf : Ideal.span (Set.range f) = I) (hS : S.ShortExact) (i : ℤ)
    (hN : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj
      ((Dualizing.derivedPowerTorsionProperty R I hI).ι.obj
        ((Dualizing.localCohomologyFunctor R I hI).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj S.X₁)))))
    (hM : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj
      ((Dualizing.derivedPowerTorsionProperty R I hI).ι.obj
        ((Dualizing.localCohomologyFunctor R I hI).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj S.X₃))))) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj
      ((Dualizing.derivedPowerTorsionProperty R I hI).ι.obj
        ((Dualizing.localCohomologyFunctor R I hI).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj S.X₂)))) := by
  rw [← isZero_cechHomology_iff_isZero_homology_localCohomology f I hI hIf] at hN hM ⊢
  exact ((LongExactSequence.shortExact_map_extendedCechFunctor.{v} f S hS).homology_exact₂
    i).isZero_of_both_isZero hN hM

/-- **Exactness of `H^i_{V(I)}(M) → H^{i+1}_{V(I)}(N) → H^{i+1}_{V(I)}(F)`, with both outer terms
zero.** If the local cohomology of `M` vanishes in degree `i` and that of `F` vanishes in degree
`i + 1`, then that of `N` vanishes in degree `i + 1`. -/
theorem isZero_homology_localCohomology_sub_of_shortExact
    (I : Ideal R) (hI : I.FG) (hIf : Ideal.span (Set.range f) = I) (hS : S.ShortExact) (i : ℤ)
    (hM : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj
      ((Dualizing.derivedPowerTorsionProperty R I hI).ι.obj
        ((Dualizing.localCohomologyFunctor R I hI).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj S.X₃)))))
    (hF : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) (i + 1)).obj
      ((Dualizing.derivedPowerTorsionProperty R I hI).ι.obj
        ((Dualizing.localCohomologyFunctor R I hI).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj S.X₂))))) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) (i + 1)).obj
      ((Dualizing.derivedPowerTorsionProperty R I hI).ι.obj
        ((Dualizing.localCohomologyFunctor R I hI).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj S.X₁)))) := by
  rw [← isZero_cechHomology_iff_isZero_homology_localCohomology f I hI hIf] at hM hF ⊢
  exact ((LongExactSequence.shortExact_map_extendedCechFunctor.{v} f S hS).homology_exact₁
    i (i + 1) rfl).isZero_of_both_isZero hM hF

/-- **The connecting isomorphism `H^i_{V(I)}(M) ≅ H^{i+1}_{V(I)}(N)`.** If the local cohomology of
`F` vanishes in degrees `i` and `i + 1`, the long exact sequence degenerates and the connecting map
is an isomorphism. The identification is produced as a `Nonempty`, since the Čech model itself is
(see the implementation notes). -/
theorem nonempty_iso_homology_localCohomology_succ_of_shortExact
    (I : Ideal R) (hI : I.FG) (hIf : Ideal.span (Set.range f) = I) (hS : S.ShortExact) (i : ℤ)
    (hF : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj
      ((Dualizing.derivedPowerTorsionProperty R I hI).ι.obj
        ((Dualizing.localCohomologyFunctor R I hI).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj S.X₂)))))
    (hF' : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) (i + 1)).obj
      ((Dualizing.derivedPowerTorsionProperty R I hI).ι.obj
        ((Dualizing.localCohomologyFunctor R I hI).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj S.X₂))))) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj
        ((Dualizing.derivedPowerTorsionProperty R I hI).ι.obj
          ((Dualizing.localCohomologyFunctor R I hI).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj S.X₃))) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) (i + 1)).obj
        ((Dualizing.derivedPowerTorsionProperty R I hI).ι.obj
          ((Dualizing.localCohomologyFunctor R I hI).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj S.X₁)))) := by
  obtain ⟨eM⟩ := nonempty_homology_localCohomology_iso_cechHomology f S.X₃ I hI hIf i
  obtain ⟨eN⟩ := nonempty_homology_localCohomology_iso_cechHomology f S.X₁ I hI hIf (i + 1)
  rw [← isZero_cechHomology_iff_isZero_homology_localCohomology f I hI hIf] at hF hF'
  exact ⟨eM ≪≫ (LongExactSequence.shortExact_map_extendedCechFunctor.{v} f S hS).δIso
    i (i + 1) rfl hF hF' ≪≫ eN.symm⟩

/-! ### Local cohomology across universes -/

/-- Čech cohomology of a module and of its universe lift vanish in the same integer degrees. In
negative degrees both vanish because the extended Čech complex is zero there; in a degree coming
from `ℕ` this is
`Stacks.LocalCohomology.isZero_homology_cechComplex_uliftModule_iff`, transported along
`HomologicalComplex.extendHomologyIso`. -/
theorem isZero_homology_extendedCechComplex_uliftModule_iff (M : ModuleCat.{u} R) (i : ℤ) :
    IsZero ((extendedCechComplex f M).homology i) ↔
      IsZero ((extendedCechComplex f (ModuleCat.of R (ULift.{v} M))).homology i) := by
  rcases lt_or_ge i 0 with hneg | hpos
  · exact iff_of_true
      (HomologicalComplex.ExactAt.of_isZero
        (isZero_extendedCechComplex_X f M i (Or.inl hneg))).isZero_homology
      (HomologicalComplex.ExactAt.of_isZero (isZero_extendedCechComplex_X f
        (ModuleCat.of R (ULift.{v} (M : Type u))) i (Or.inl hneg))).isZero_homology
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n : ℤ) := ⟨i.toNat, by omega⟩
    have eM := HomologicalComplex.extendHomologyIso (Cech.cechComplex f (M : Type u))
      ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) (by simp)
    have eU := HomologicalComplex.extendHomologyIso
      (Cech.cechComplex f (ULift.{v} (M : Type u)))
      ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) (by simp)
    exact eM.isZero_iff.trans
      ((isZero_homology_cechComplex_uliftModule_iff f n).trans eU.isZero_iff.symm)

/-- **Local cohomology does not see a universe lift of its coefficient module.** For a module `M`
in `ModuleCat.{u} R` the local cohomology `H^i_{V(I)}(M)`, computed in the derived category of
`ModuleCat.{u} R`, vanishes exactly when the local cohomology of `ULift.{v} M`, computed in the
derived category of `ModuleCat.{max u v} R`, does.

Neither functor is comparable to the other directly — they are right adjoints on two different
derived categories — so the comparison is made through the Čech model, where it becomes a statement
about complexes of modules and `LinearEquiv`, which is universe-heterogeneous.

This is the comparison the equivalence (1) ⇔ (2) of [Stacks, Tag 0DX7] needs: condition (1) is a
vanishing for the module `A` in `ModuleCat.{u} A`, and condition (2) quantifies over
`ModuleCat.{max u v} A`. -/
theorem isZero_homology_localCohomology_uliftModule_iff
    (I : Ideal R) (hI : I.FG) (hIf : Ideal.span (Set.range f) = I)
    (M : ModuleCat.{u} R) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        ((Dualizing.derivedPowerTorsionProperty R I hI).ι.obj
          ((Dualizing.localCohomologyFunctor R I hI).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)))) ↔
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj
        ((Dualizing.derivedPowerTorsionProperty R I hI).ι.obj
          ((Dualizing.localCohomologyFunctor R I hI).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj
              (ModuleCat.of R (ULift.{v} M)))))) := by
  obtain ⟨eM⟩ := nonempty_homology_localCohomology_iso_cechHomology f M I hI hIf i
  obtain ⟨eU⟩ := nonempty_homology_localCohomology_iso_cechHomology f
    (ModuleCat.of R (ULift.{v} (M : Type u))) I hI hIf i
  exact eM.isZero_iff.trans
    ((isZero_homology_extendedCechComplex_uliftModule_iff f M i).trans eU.isZero_iff.symm)

end Stacks.LocalCohomology

end
