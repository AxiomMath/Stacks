module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.NeighbourhoodModules
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete

/-!
# Sections of an ideal-power quotient over a neighbourhood of the closed subscheme

Let `i : Z ⟶ X` be a closed immersion with ideal sheaf `J = i.ker`, let `Y_n ⊆ X` be the
infinitesimal neighbourhoods of `i` and let `F` be a quasi-coherent `𝒪_X`-module. The
comparison of [Stacks, Tag 0EL1] identifies `F / J^(n+1) F` with the direct image
`(ι_n)_* (ι_n)^* F` of the restriction of `F` to `Y_n`. Taking sections over an open `V ⊆ X`
containing the image of `i` therefore reads a section of `F / J^(n+1) F` over `V` as a section
of `F` on `Y_n`, because the preimage of `V` in `Y_n` is everything.

This file records that reading and its three compatibilities: with the quotient projection
`F ⟶ F / J^(n+1) F`, with shrinking `V`, and with the transition maps of the ideal-power tower.
Together they say that the comparison map of [Stacks, Tag 0EG2] — whose source is the colimit of
the sections of `F` over the neighbourhoods of the formal locus and whose target is the limit of
the sections of the quotients `F / Jⁿ F` on all of `X` — computes the comparison of
`Stacks.Algebraization.IsNeighbourhoodSectionsComplete`, whose target is the limit of the
sections of `F` on the `Y_n`.

Everything is stated for an ideal sheaf `J` and a closed immersion `i` together with an equation
`i.ker = J`, as [Stacks, Tag 0EL1] itself is stated in
`Stacks.Algebraization.idealQuotientPushforwardMap`, so that the ideal-power quotients below are
spelled with `J` and no transport along `i.ker = J` is needed by the consumers.

## Main definitions

* `Stacks.Algebraization.neighbourhoodQuotientMap` — the comparison `F / J^(n+1) F ⟶
  (ι_n)_* (ι_n)^* F` of [Stacks, Tag 0EL1] at the `n`-th infinitesimal neighbourhood.
* `Stacks.Algebraization.neighbourhoodQuotientSections` and
  `Stacks.Algebraization.neighbourhoodQuotientSectionsTop` — the induced map from the sections of
  `F / J^(n+1) F` over an open containing the image of `i`, and over the whole space, to the
  sections of `F` on `Y_n`.
* `Stacks.Algebraization.neighbourhoodQuotientSectionsTopEquiv` — the latter as a bijection.

## Main results

* `Stacks.Algebraization.ker_nthInfinitesimalNeighbourhoodι_of_ker_eq` — the `n`-th
  infinitesimal neighbourhood is cut out by `J ^ (n + 1)`.
* `Stacks.Algebraization.neighbourhoodQuotientSections_π` — the reduction of a section of `F`
  over `V` modulo `J^(n+1)` is carried to its restriction to `Y_n`.
* `Stacks.Algebraization.neighbourhoodQuotientSections_restrict` and
  `Stacks.Algebraization.neighbourhoodQuotientSections_top` — the map does not see a shrinking of
  the open, and over the whole space it is the map on global sections.
* `Stacks.Algebraization.neighbourhoodQuotientSectionsTop_transition` — any morphism of
  ideal-power quotients commuting with the quotient projections is carried to the canonical map
  on the sections over the neighbourhoods.

## Implementation notes

The identification `Γ(v_* ℳ, V) = Γ(ℳ, v ⁻¹ᵁ V)` holds by definition but only after unfolding a
semireducible definition, so a goal that crosses it is not type-correct at the transparency `rw`
and `simp` build their motives at. As in the neighbourhood files this one builds on, the steps
that cross it are therefore carried out in term mode, with `Eq.trans`, `congrArg` and
`CategoryTheory.ConcreteCategory.congr_hom` in place of a rewrite; this is why
`Stacks.Algebraization.neighbourhoodQuotientSections_top` is stated elementwise rather than as an
equality of two maps.

## References

* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Algebraization

section

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (J : X.IdealSheafData)
  (hi : i.ker = J) (F : X.Modules)

include hi

/-- The `n`-th infinitesimal neighbourhood of a closed immersion with ideal sheaf `J` is cut out
by `J ^ (n + 1)`. -/
public theorem ker_nthInfinitesimalNeighbourhoodι_of_ker_eq (n : ℕ) :
    (nthInfinitesimalNeighbourhoodι i n).ker = J ^ (n + 1) :=
  (ker_nthInfinitesimalNeighbourhoodι i n).trans (congrArg (fun K => K ^ (n + 1)) hi)

/-- **Stacks 0EL1 at the `n`-th infinitesimal neighbourhood of a closed immersion with ideal
sheaf `J`:** the canonical map `F / J^(n+1) F ⟶ (ι_n)_* (ι_n)^* F`. -/
public def neighbourhoodQuotientMap (n : ℕ) :
    idealPowerQuotient J (n + 1) F ⟶
      (Scheme.Modules.pushforward (nthInfinitesimalNeighbourhoodι i n)).obj
        ((Scheme.Modules.pullback (nthInfinitesimalNeighbourhoodι i n)).obj F) :=
  idealQuotientPushforwardMap J (n + 1) F (nthInfinitesimalNeighbourhoodι i n)
    (ker_nthInfinitesimalNeighbourhoodι_of_ker_eq i J hi n)

/-- The comparison is normalized by the adjunction unit. -/
public theorem neighbourhoodQuotientMap_π (n : ℕ) :
    cokernel.π (C := X.Modules) (idealPowerMultiple J (n + 1) F).ι ≫
        neighbourhoodQuotientMap i J hi F n =
      (Scheme.Modules.pullbackPushforwardAdjunction
        (nthInfinitesimalNeighbourhoodι i n)).unit.app F :=
  idealQuotientPushforwardMap_π J (n + 1) F (nthInfinitesimalNeighbourhoodι i n)
    (ker_nthInfinitesimalNeighbourhoodι_of_ker_eq i J hi n)

/-- The sections of `F / J^(n+1) F` over an open containing the `n`-th infinitesimal
neighbourhood, read as sections of `F` on that neighbourhood. -/
public def neighbourhoodQuotientSections (n : ℕ) {V : X.Opens}
    (hV : (nthInfinitesimalNeighbourhoodι i n) ⁻¹ᵁ V = ⊤) :
    Γ(idealPowerQuotient J (n + 1) F, V) ⟶
      Γ((Scheme.Modules.pullback (nthInfinitesimalNeighbourhoodι i n)).obj F,
        (⊤ : (nthInfinitesimalNeighbourhood i n).Opens)) :=
  (neighbourhoodQuotientMap i J hi F n).app V ≫
    ((Scheme.Modules.pullback (nthInfinitesimalNeighbourhoodι i n)).obj F).presheaf.map
      (eqToHom hV.symm).op

/-- The global sections of `F / J^(n+1) F`, read as sections of `F` on the `n`-th infinitesimal
neighbourhood. -/
public def neighbourhoodQuotientSectionsTop (n : ℕ) :
    Γ(idealPowerQuotient J (n + 1) F, (⊤ : X.Opens)) ⟶
      Γ((Scheme.Modules.pullback (nthInfinitesimalNeighbourhoodι i n)).obj F,
        (⊤ : (nthInfinitesimalNeighbourhood i n).Opens)) :=
  (neighbourhoodQuotientMap i J hi F n).app ⊤

/-- Unfolding `neighbourhoodQuotientSections` on an element. -/
private theorem neighbourhoodQuotientSections_apply (n : ℕ) {V : X.Opens}
    (hV : (nthInfinitesimalNeighbourhoodι i n) ⁻¹ᵁ V = ⊤)
    (x : Γ(idealPowerQuotient J (n + 1) F, V)) :
    neighbourhoodQuotientSections i J hi F n hV x =
      ((Scheme.Modules.pullback (nthInfinitesimalNeighbourhoodι i n)).obj F).presheaf.map
        (eqToHom hV.symm).op ((neighbourhoodQuotientMap i J hi F n).app V x) :=
  rfl

/-- **The comparison carries the reduction of a section modulo `J^(n+1)` to its restriction to
the `n`-th infinitesimal neighbourhood.** -/
public theorem neighbourhoodQuotientSections_π (n : ℕ) {V : X.Opens}
    (hV : (nthInfinitesimalNeighbourhoodι i n) ⁻¹ᵁ V = ⊤) (t : Γ(F, V)) :
    neighbourhoodQuotientSections i J hi F n hV
        ((cokernel.π (C := X.Modules) (idealPowerMultiple J (n + 1) F).ι).app V t) =
      pullbackSectionsAt (nthInfinitesimalNeighbourhoodι i n) F hV t := by
  refine (neighbourhoodQuotientSections_apply i J hi F n hV _).trans ?_
  refine Eq.trans ?_ (ConcreteCategory.comp_apply _ _ _).symm
  exact congrArg
    (fun y => ((Scheme.Modules.pullback (nthInfinitesimalNeighbourhoodι i n)).obj F).presheaf.map
      (eqToHom hV.symm).op y)
    (congrArg (fun χ => Scheme.Modules.Hom.app χ V t) (neighbourhoodQuotientMap_π i J hi F n))

/-- Shrinking the open does not change the induced section on the `n`-th infinitesimal
neighbourhood. -/
public theorem neighbourhoodQuotientSections_restrict (n : ℕ) {V V' : X.Opens} (h : V' ≤ V)
    (hV : (nthInfinitesimalNeighbourhoodι i n) ⁻¹ᵁ V = ⊤)
    (hV' : (nthInfinitesimalNeighbourhoodι i n) ⁻¹ᵁ V' = ⊤)
    (x : Γ(idealPowerQuotient J (n + 1) F, V)) :
    neighbourhoodQuotientSections i J hi F n hV'
        ((idealPowerQuotient J (n + 1) F).presheaf.map (homOfLE h).op x) =
      neighbourhoodQuotientSections i J hi F n hV x := by
  refine (neighbourhoodQuotientSections_apply i J hi F n hV' _).trans ?_
  refine Eq.trans ?_ (neighbourhoodQuotientSections_apply i J hi F n hV x).symm
  exact (congrArg _ (NatTrans.naturality_apply (neighbourhoodQuotientMap i J hi F n).mapPresheaf
    (homOfLE h).op x)).trans
    (ConcreteCategory.congr_hom (((Scheme.Modules.pullback
      (nthInfinitesimalNeighbourhoodι i n)).obj F).presheaf.map_comp _ _).symm _)

/-- Over the whole space the comparison is the one on global sections. -/
public theorem neighbourhoodQuotientSections_top (n : ℕ)
    (x : Γ(idealPowerQuotient J (n + 1) F, (⊤ : X.Opens))) :
    neighbourhoodQuotientSections i J hi F n
        (Opens.map_top (nthInfinitesimalNeighbourhoodι i n).base) x =
      neighbourhoodQuotientSectionsTop i J hi F n x := by
  have hid : ((Scheme.Modules.pullback (nthInfinitesimalNeighbourhoodι i n)).obj F).presheaf.map
      (eqToHom (Opens.map_top (nthInfinitesimalNeighbourhoodι i n).base).symm).op = 𝟙 _ := by
    rw [show (eqToHom (Opens.map_top (nthInfinitesimalNeighbourhoodι i n).base).symm).op =
      CategoryTheory.CategoryStruct.id
        (Opposite.op ((nthInfinitesimalNeighbourhoodι i n) ⁻¹ᵁ (⊤ : X.Opens))) from rfl]
    exact CategoryTheory.Functor.map_id _ _
  exact (ConcreteCategory.comp_apply _ _ _).trans
    (ConcreteCategory.congr_hom hid ((neighbourhoodQuotientMap i J hi F n).app ⊤ x))

/-- **The comparison is compatible with the transition maps of the ideal-power tower.** -/
public theorem neighbourhoodQuotientSectionsTop_transition {n m : ℕ} (h : n ≤ m)
    (τ : idealPowerQuotient J (m + 1) F ⟶ idealPowerQuotient J (n + 1) F)
    (hτ : cokernel.π (C := X.Modules) (idealPowerMultiple J (m + 1) F).ι ≫ τ =
      cokernel.π (C := X.Modules) (idealPowerMultiple J (n + 1) F).ι)
    (y : Γ(idealPowerQuotient J (m + 1) F, (⊤ : X.Opens))) :
    pullbackSectionsMap F (nthInfinitesimalNeighbourhoodTransition i h)
        (neighbourhoodQuotientSectionsTop i J hi F m y) =
      neighbourhoodQuotientSectionsTop i J hi F n
        (Scheme.Modules.Hom.app τ (⊤ : X.Opens) y) := by
  have hsq : neighbourhoodQuotientMap i J hi F m ≫
      pushforwardSectionComparison (nthInfinitesimalNeighbourhoodTransition i h).left
        (nthInfinitesimalNeighbourhoodι i m)
        (Over.w (nthInfinitesimalNeighbourhoodTransition i h)) F =
      τ ≫ neighbourhoodQuotientMap i J hi F n := by
    refine (cancel_epi
      (cokernel.π (C := X.Modules) (idealPowerMultiple J (m + 1) F).ι)).1 ?_
    rw [← Category.assoc, neighbourhoodQuotientMap_π, ← Category.assoc, hτ,
      neighbourhoodQuotientMap_π]
    exact unit_comp_pushforwardSectionComparison _ _ _ F
  exact (pullbackSectionsMap_eq_pushforwardSectionComparison
    (nthInfinitesimalNeighbourhoodTransition i h) F _).trans
    (congrArg (fun χ => Scheme.Modules.Hom.app χ (⊤ : X.Opens) y) hsq)

/-- The comparison at the whole space, as a bijection: this is [Stacks, Tag 0EL1]. -/
public def neighbourhoodQuotientSectionsTopEquiv [F.IsQuasicoherent] (n : ℕ) :
    Γ(idealPowerQuotient J (n + 1) F, (⊤ : X.Opens)) ≃
      Γ((Scheme.Modules.pullback (nthInfinitesimalNeighbourhoodι i n)).obj F,
        (⊤ : (nthInfinitesimalNeighbourhood i n).Opens)) :=
  sectionsEquivOfIso (idealQuotientPushforwardIso J (n + 1) F
    (nthInfinitesimalNeighbourhoodι i n)
    (ker_nthInfinitesimalNeighbourhoodι_of_ker_eq i J hi n)) ⊤

/-- The bijection is the comparison on global sections. -/
public theorem neighbourhoodQuotientSectionsTopEquiv_apply [F.IsQuasicoherent] (n : ℕ)
    (x : Γ(idealPowerQuotient J (n + 1) F, (⊤ : X.Opens))) :
    neighbourhoodQuotientSectionsTopEquiv i J hi F n x =
      neighbourhoodQuotientSectionsTop i J hi F n x :=
  rfl

end

end Stacks.Algebraization

end
