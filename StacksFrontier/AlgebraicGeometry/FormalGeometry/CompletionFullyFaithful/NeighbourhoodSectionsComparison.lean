module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonInjectivityClosed
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.NeighbourhoodQuotientSections

/-!
# The comparison of Stacks 0EG2 is the comparison of Stacks 0EK2

Let `A` be a Noetherian ring, let `I ⊆ 𝔞` be ideals, let `U = Spec(A) ∖ V(𝔞)` and let `𝒱` be the
open subschemes of `U` containing the formal locus `U ∩ V(I)`, ordered by reverse inclusion. Two
comparisons between the sections of a coherent `𝒪_U`-module `F` near the formal locus and its
infinitesimal data along it are in use in this library:

* `Stacks.Algebraization.comparisonMap`, the map `colim_𝒱 Γ(V, F) ⟶ lim_n Γ(U, F / Iⁿ F)` of
  [Stacks, Tag 0EG2], whose target is the sections of the ideal-power quotients on all of `U`;
* `Stacks.Algebraization.IsNeighbourhoodSectionsComplete`, the comparison
  `colim_𝒱 Γ(V, F) ⟶ lim_n Γ(Y_n, F|_{Y_n})` occurring in conditions (1)–(3) of
  [Stacks, Tag 0EK2], whose target is the sections of `F` on the infinitesimal neighbourhoods
  `Y_n` of the formal locus, and which is spelled out by the universal properties of the
  filtered colimit and the inverse limit.

This file proves that invertibility of the first gives the second. The two sides agree because
`F / I^(n+1) F` is the direct image of `F|_{Y_n}` ([Stacks, Tag 0EL1], available here through
`Stacks.Algebraization.neighbourhoodQuotientSectionsTop`) and because the neighbourhoods of the
formal locus in the sense of `Stacks.Algebraization.OpensNearVanishing` are exactly the opens of
`U` containing the image of the closed immersion of the formal locus.

## Main definitions

* `Stacks.Algebraization.opensNearVanishingOfRangeSubset` — an open of `U` containing the formal
  locus, as a member of `Stacks.Algebraization.OpensNearVanishing`.
* `Stacks.Algebraization.formalLimitSection` — the `n`-th section on `Y_n` read off an element of
  `lim_n Γ(U, F / Iⁿ F)`.
* `Stacks.Algebraization.limitOfNeighbourhoodFamily` — conversely, the element of
  `lim_n Γ(U, F / Iⁿ F)` attached to a compatible family of sections on the `Y_n`.

## Main results

* `Stacks.Algebraization.range_subschemeι_subset` — a neighbourhood of the formal locus contains
  the image of the closed immersion of the formal locus.
* `Stacks.Algebraization.formalLimitSection_comparisonMap` — the comparison map of
  [Stacks, Tag 0EG2] computes the restrictions to the infinitesimal neighbourhoods: the `n`-th
  section read off the image of a section `t` over `V ∈ 𝒱` is the restriction of `t` to `Y_n`.
* `Stacks.Algebraization.formalLimitSection_limitOfNeighbourhoodFamily` — the sections read off
  the element attached to a compatible family are the members of that family.
* `Stacks.Algebraization.isNeighbourhoodSectionsComplete_of_isIso_comparisonMap` — if the
  comparison map of [Stacks, Tag 0EG2] is an isomorphism for `F`, then `F` satisfies the
  comparison of conditions (1)–(3) of [Stacks, Tag 0EK2].

## Implementation notes

The index `n` of the infinitesimal neighbourhoods is the exponent `n + 1` of the ideal-power
tower, since `Y_n` is cut out by `I^(n+1)`; so the `n`-th section on the neighbourhoods is read
off the component of the limit at `n + 1`, and the component at `0` — where the quotient is
`F / F` — is reached from the one at `1` through `CategoryTheory.Limits.limit.w`. That is why the
compatible family fed to the limit is `j ↦ τ (w j)` for `w m` the member of `Γ(U, F / I^(m+1) F)`
and `τ` the transition to `F / I^m F`: one uniform formula, valid at `0` as well, whose
compatibility is the one computation `τ (w m) = w n` for `n ≤ m`.

The element of the limit attached to a compatible family is produced by
`CategoryTheory.Limits.Types.isLimitEquivSections` at the limit cone carried over by the
forgetful functor, which preserves it; the cone has to be supplied explicitly, since matching
`Cone.π` against `CategoryTheory.Limits.limit.π` is a higher-order unification the elaborator
does not solve. On the colimit side the elementwise description is the filtered-colimit API
`CategoryTheory.Limits.Concrete.colimit_exists_rep` and
`CategoryTheory.Limits.Concrete.colimit_exists_of_rep_eq`, for which
`Stacks.Algebraization.isFiltered_opensNearVanishing` supplies the filteredness of `𝒱`.

## References

* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 0EKV](https://stacks.math.columbia.edu/tag/0EKV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

variable (A : Type u) [CommRing A] (I a : Ideal A)
  (F : (complementZeroLocus A a : Scheme).Modules)

/-- The ideal sheaf of the formal locus is `I 𝒪_U`. -/
theorem ker_subschemeι_idealSheafNearVanishing :
    ((idealSheafNearVanishing A I a).subschemeι).ker = idealSheafNearVanishing A I a :=
  Scheme.IdealSheafData.ker_subschemeι _

/-- A neighbourhood of the formal locus in the sense of
`Stacks.Algebraization.OpensNearVanishing` contains the image of the closed immersion of the
formal locus. -/
theorem range_subschemeι_subset (V : OpensNearVanishing A I a) :
    Set.range ((idealSheafNearVanishing A I a).subschemeι).base ⊆
      (V.openSet : Set (complementZeroLocus A a : Scheme)) := by
  rw [Scheme.IdealSheafData.range_subschemeι]
  exact support_idealSheafNearVanishing_le A I a V

/-- An open of `U` containing the image of the closed immersion of the formal locus is a
neighbourhood of the formal locus in the sense of
`Stacks.Algebraization.OpensNearVanishing`. -/
def opensNearVanishingOfRangeSubset (V : (complementZeroLocus A a : Scheme).Opens)
    (hV : Set.range ((idealSheafNearVanishing A I a).subschemeι).base ⊆ V) :
    OpensNearVanishing A I a where
  openSet := V
  contains_vanishing x hx := by
    refine hV ?_
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact mem_support_baseIdealSheaf I (complementZeroLocus A a).ι hx

/-- The `n`-th component of a compatible family of sections of the quotients `F / Iⁿ F` on `U`,
read as a section of `F` on the `n`-th infinitesimal neighbourhood of the formal locus. -/
def formalLimitSection (z : ToType (limit (formalSections A I a F))) (n : ℕ) :
    Γ((Scheme.Modules.pullback (nthInfinitesimalNeighbourhoodι
        (idealSheafNearVanishing A I a).subschemeι n)).obj F, ⊤) :=
  neighbourhoodQuotientSectionsTop (idealSheafNearVanishing A I a).subschemeι
    (idealSheafNearVanishing A I a) (ker_subschemeι_idealSheafNearVanishing A I a) F n
    (limit.π (formalSections A I a F) (op (n + 1)) z)

/-- The sections read off an element of the limit form a compatible family on the infinitesimal
neighbourhoods. -/
theorem formalLimitSection_compatible (z : ToType (limit (formalSections A I a F)))
    {n m : ℕ} (h : n ≤ m) :
    pullbackSectionsMap F
        (nthInfinitesimalNeighbourhoodTransition (idealSheafNearVanishing A I a).subschemeι h)
        (formalLimitSection A I a F z m) =
      formalLimitSection A I a F z n := by
  refine (neighbourhoodQuotientSectionsTop_transition
    (idealSheafNearVanishing A I a).subschemeι (idealSheafNearVanishing A I a)
    (ker_subschemeι_idealSheafNearVanishing A I a) F h
    ((quotientSystemNearVanishing A I a F).map (homOfLE (Nat.succ_le_succ h)).op)
    (adicProj_comp_map (idealSheafNearVanishing A I a) F
      (homOfLE (Nat.succ_le_succ h)).op) _).trans ?_
  exact congrArg
    (neighbourhoodQuotientSectionsTop (idealSheafNearVanishing A I a).subschemeι
      (idealSheafNearVanishing A I a) (ker_subschemeι_idealSheafNearVanishing A I a) F n)
    (ConcreteCategory.congr_hom
      (limit.w (formalSections A I a F) (homOfLE (Nat.succ_le_succ h)).op) z)

/-- An element of the limit of the formal sections is determined by the sections it induces on
the infinitesimal neighbourhoods. -/
theorem eq_of_formalLimitSection_eq [F.IsQuasicoherent]
    {z z' : ToType (limit (formalSections A I a F))}
    (h : ∀ n, formalLimitSection A I a F z n = formalLimitSection A I a F z' n) : z = z' := by
  have hsucc : ∀ l : ℕ, limit.π (formalSections A I a F) (op (l + 1)) z =
      limit.π (formalSections A I a F) (op (l + 1)) z' := by
    intro l
    refine (neighbourhoodQuotientSectionsTopEquiv (idealSheafNearVanishing A I a).subschemeι
      (idealSheafNearVanishing A I a) (ker_subschemeι_idealSheafNearVanishing A I a) F
      l).injective ?_
    refine (neighbourhoodQuotientSectionsTopEquiv_apply
      (idealSheafNearVanishing A I a).subschemeι (idealSheafNearVanishing A I a)
      (ker_subschemeι_idealSheafNearVanishing A I a) F l _).trans ?_
    refine Eq.trans ?_ (neighbourhoodQuotientSectionsTopEquiv_apply
      (idealSheafNearVanishing A I a).subschemeι (idealSheafNearVanishing A I a)
      (ker_subschemeι_idealSheafNearVanishing A I a) F l _).symm
    exact h l
  have h0 : ∀ x : ToType (limit (formalSections A I a F)),
      limit.π (formalSections A I a F) (op 0) x =
        (formalSections A I a F).map (homOfLE (Nat.zero_le 1)).op
          (limit.π (formalSections A I a F) (op 1) x) := fun x =>
    (ConcreteCategory.congr_hom
      (limit.w (formalSections A I a F) (homOfLE (Nat.zero_le 1)).op) x).symm.trans
      (ConcreteCategory.comp_apply _ _ _)
  refine Concrete.limit_ext (formalSections A I a F) _ _ fun j => ?_
  rcases j with ⟨m⟩
  cases m with
  | zero => exact (h0 _).trans ((congrArg _ (hsucc 0)).trans (h0 _).symm)
  | succ l => exact hsucc l

/-- **The comparison map of [Stacks, Tag 0EG2] computes the restrictions to the infinitesimal
neighbourhoods.** The `n`-th section read off the image of a section `t` of `F` over a
neighbourhood `V` of the formal locus is the restriction of `t` to the `n`-th infinitesimal
neighbourhood. -/
theorem formalLimitSection_comparisonMap (V : OpensNearVanishing A I a)
    (t : ToType ((sectionsNearVanishing A I a F).obj V)) (n : ℕ) :
    formalLimitSection A I a F
        (comparisonMap A I a F (colimit.ι (sectionsNearVanishing A I a F) V t)) n =
      pullbackSectionsAt
        (nthInfinitesimalNeighbourhoodι (idealSheafNearVanishing A I a).subschemeι n) F
        (nthInfinitesimalNeighbourhoodι_preimage_eq_top
          (idealSheafNearVanishing A I a).subschemeι (range_subschemeι_subset A I a V) n) t := by
  have hres : ((quotientSystemNearVanishing A I a F).obj (op (n + 1))).presheaf.map
        (homOfLE (show V.openSet ≤ ⊤ from le_top)).op
        (limit.π (formalSections A I a F) (op (n + 1))
          (comparisonMap A I a F (colimit.ι (sectionsNearVanishing A I a F) V t))) =
      (adicProj (idealSheafNearVanishing A I a) F (op (n + 1))).app V.openSet t :=
    (ConcreteCategory.comp_apply _ _ _).symm.trans
      ((ConcreteCategory.comp_apply _ _ _).symm.trans
        ((ConcreteCategory.comp_apply _ _ _).symm.trans
          (ConcreteCategory.congr_hom (comparisonMap_restrict A I a F V (n + 1)) t)))
  refine Eq.trans ?_ (neighbourhoodQuotientSections_π
    (idealSheafNearVanishing A I a).subschemeι (idealSheafNearVanishing A I a)
    (ker_subschemeι_idealSheafNearVanishing A I a) F n _ t)
  refine Eq.trans ?_ (congrArg
    (neighbourhoodQuotientSections (idealSheafNearVanishing A I a).subschemeι
      (idealSheafNearVanishing A I a) (ker_subschemeι_idealSheafNearVanishing A I a) F n
      (nthInfinitesimalNeighbourhoodι_preimage_eq_top
        (idealSheafNearVanishing A I a).subschemeι (range_subschemeι_subset A I a V) n)) hres)
  exact ((neighbourhoodQuotientSections_restrict (idealSheafNearVanishing A I a).subschemeι
    (idealSheafNearVanishing A I a) (ker_subschemeι_idealSheafNearVanishing A I a) F n
    (show V.openSet ≤ ⊤ from le_top)
    (Opens.map_top
      (nthInfinitesimalNeighbourhoodι (idealSheafNearVanishing A I a).subschemeι n).base)
    (nthInfinitesimalNeighbourhoodι_preimage_eq_top
      (idealSheafNearVanishing A I a).subschemeι (range_subschemeι_subset A I a V) n) _).trans
    (neighbourhoodQuotientSections_top (idealSheafNearVanishing A I a).subschemeι
      (idealSheafNearVanishing A I a) (ker_subschemeι_idealSheafNearVanishing A I a) F n _)).symm

section Family

variable [F.IsQuasicoherent]
  (s : ∀ n : ℕ, Γ((Scheme.Modules.pullback (nthInfinitesimalNeighbourhoodι
    (idealSheafNearVanishing A I a).subschemeι n)).obj F, ⊤))

/-- The member of `Γ(U, F / I^(m+1) F)` corresponding to the `m`-th section of a family of
sections on the infinitesimal neighbourhoods of the formal locus. -/
def neighbourhoodFamilyQuot (m : ℕ) :
    Γ(idealPowerQuotient (idealSheafNearVanishing A I a) (m + 1) F, (⊤ :
      (complementZeroLocus A a : Scheme).Opens)) :=
  (neighbourhoodQuotientSectionsTopEquiv (idealSheafNearVanishing A I a).subschemeι
    (idealSheafNearVanishing A I a) (ker_subschemeι_idealSheafNearVanishing A I a) F m).symm (s m)

/-- The section of the `m`-th infinitesimal neighbourhood corresponding to
`neighbourhoodFamilyQuot A I a F s m` is `s m`. -/
theorem neighbourhoodQuotientSectionsTop_neighbourhoodFamilyQuot (m : ℕ) :
    neighbourhoodQuotientSectionsTop (idealSheafNearVanishing A I a).subschemeι
        (idealSheafNearVanishing A I a) (ker_subschemeι_idealSheafNearVanishing A I a) F m
        (neighbourhoodFamilyQuot A I a F s m) =
      s m :=
  (neighbourhoodQuotientSectionsTopEquiv_apply (idealSheafNearVanishing A I a).subschemeι
      (idealSheafNearVanishing A I a) (ker_subschemeι_idealSheafNearVanishing A I a) F m
      _).symm.trans
    (Equiv.apply_symm_apply _ _)

variable (hs : ∀ (n m : ℕ) (h : n ≤ m),
  pullbackSectionsMap F
      (nthInfinitesimalNeighbourhoodTransition (idealSheafNearVanishing A I a).subschemeι h)
      (s m) = s n)

include hs

/-- The family is compatible with the transition maps of the ideal-power tower. -/
theorem neighbourhoodFamilyQuot_transition {n m : ℕ} (h : n ≤ m) :
    Scheme.Modules.Hom.app ((quotientSystemNearVanishing A I a F).map
        (homOfLE (Nat.succ_le_succ h)).op) ⊤ (neighbourhoodFamilyQuot A I a F s m) =
      neighbourhoodFamilyQuot A I a F s n := by
  refine (neighbourhoodQuotientSectionsTopEquiv (idealSheafNearVanishing A I a).subschemeι
    (idealSheafNearVanishing A I a) (ker_subschemeι_idealSheafNearVanishing A I a) F n).injective ?_
  refine Eq.trans ?_ (neighbourhoodQuotientSectionsTop_neighbourhoodFamilyQuot
    A I a F s n).symm
  refine (neighbourhoodQuotientSectionsTop_transition
    (idealSheafNearVanishing A I a).subschemeι (idealSheafNearVanishing A I a)
    (ker_subschemeι_idealSheafNearVanishing A I a) F h
    ((quotientSystemNearVanishing A I a F).map (homOfLE (Nat.succ_le_succ h)).op)
    (adicProj_comp_map (idealSheafNearVanishing A I a) F
      (homOfLE (Nat.succ_le_succ h)).op) _).symm.trans ?_
  refine Eq.trans ?_ (hs n m h)
  exact congrArg (pullbackSectionsMap F
    (nthInfinitesimalNeighbourhoodTransition (idealSheafNearVanishing A I a).subschemeι h))
    (neighbourhoodQuotientSectionsTop_neighbourhoodFamilyQuot A I a F s m)

omit hs in
/-- The compatible family of sections of the quotients `F / Iⁿ F` on `U` attached to a family of
sections on the infinitesimal neighbourhoods: at `n` it is the `n`-th member of the family, read
in `F / I^(n+1) F` and transported to `F / Iⁿ F`. -/
def neighbourhoodFamilySection (j : ℕᵒᵖ) : ToType ((formalSections A I a F).obj j) :=
  (formalSections A I a F).map (homOfLE (Nat.le_succ j.unop)).op
    (neighbourhoodFamilyQuot A I a F s j.unop)

/-- `neighbourhoodFamilySection` is a compatible family of sections of the formal sections. -/
theorem neighbourhoodFamilySection_mem_sections :
    neighbourhoodFamilySection A I a F s ∈
      (formalSections A I a F ⋙ forget Ab.{u}).sections := by
  intro j j' f
  have hle : j'.unop ≤ j.unop := leOfHom f.unop
  have hfac : (homOfLE (Nat.le_succ j.unop)).op ≫ f =
      (homOfLE (Nat.succ_le_succ hle)).op ≫ (homOfLE (Nat.le_succ j'.unop)).op :=
    Subsingleton.elim _ _
  have h1 : (formalSections A I a F).map (homOfLE (Nat.le_succ j.unop)).op ≫
        (formalSections A I a F).map f =
      (formalSections A I a F).map (homOfLE (Nat.succ_le_succ hle)).op ≫
        (formalSections A I a F).map (homOfLE (Nat.le_succ j'.unop)).op := by
    rw [← Functor.map_comp, ← Functor.map_comp, hfac]
  refine ((ConcreteCategory.comp_apply _ _ _).symm.trans
    (ConcreteCategory.congr_hom h1 (neighbourhoodFamilyQuot A I a F s j.unop))).trans ?_
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  exact congrArg ((formalSections A I a F).map (homOfLE (Nat.le_succ j'.unop)).op)
    (neighbourhoodFamilyQuot_transition A I a F s hs hle)

/-- **A compatible family of sections on the infinitesimal neighbourhoods of the formal locus
comes from an element of the limit of the formal sections.** -/
def limitOfNeighbourhoodFamily : ToType (limit (formalSections A I a F)) :=
  (Types.isLimitEquivSections (isLimitOfPreserves (forget Ab.{u})
    (limit.isLimit (formalSections A I a F)))).symm
      ⟨neighbourhoodFamilySection A I a F s,
        neighbourhoodFamilySection_mem_sections A I a F s hs⟩

/-- The `j`-th projection of `limitOfNeighbourhoodFamily` is the `j`-th member of
`neighbourhoodFamilySection`. -/
theorem limit_π_limitOfNeighbourhoodFamily (j : ℕᵒᵖ) :
    limit.π (formalSections A I a F) j (limitOfNeighbourhoodFamily A I a F s hs) =
      neighbourhoodFamilySection A I a F s j :=
  Types.isLimitEquivSections_symm_apply
    (c := (forget Ab.{u}).mapCone (limit.cone (formalSections A I a F)))
    (isLimitOfPreserves (forget Ab.{u}) (limit.isLimit (formalSections A I a F))) _ j

/-- The sections read off `limitOfNeighbourhoodFamily` are the members of the family `s`. -/
theorem formalLimitSection_limitOfNeighbourhoodFamily (n : ℕ) :
    formalLimitSection A I a F (limitOfNeighbourhoodFamily A I a F s hs) n = s n := by
  refine Eq.trans ?_ (neighbourhoodQuotientSectionsTop_neighbourhoodFamilyQuot A I a F s n)
  refine congrArg (neighbourhoodQuotientSectionsTop
    (idealSheafNearVanishing A I a).subschemeι (idealSheafNearVanishing A I a)
    (ker_subschemeι_idealSheafNearVanishing A I a) F n) ?_
  refine (limit_π_limitOfNeighbourhoodFamily A I a F s hs (op (n + 1))).trans ?_
  exact neighbourhoodFamilyQuot_transition A I a F s hs (Nat.le_succ n)

end Family

/-- **The comparison map of [Stacks, Tag 0EG2] is the comparison of [Stacks, Tag 0EK2].**
Let `A` be Noetherian, let `I ⊆ 𝔞` be ideals, let `U = Spec(A) ∖ V(𝔞)` and let `F` be a
quasi-coherent `𝒪_U`-module. If the comparison map of [Stacks, Tag 0EG2] is an isomorphism for
`F`, then the colimit of the sections of `F` over the open neighbourhoods of the formal locus
`U ∩ V(I)` is the limit of the sections of `F` on the infinitesimal neighbourhoods of that
locus. -/
theorem isNeighbourhoodSectionsComplete_of_isIso_comparisonMap [IsNoetherianRing A]
    [F.IsQuasicoherent] (hiso : IsIso (comparisonMap A I a F)) :
    IsNeighbourhoodSectionsComplete (idealSheafNearVanishing A I a).subschemeι F := by
  have hforget : PreservesFilteredColimitsOfSize.{0, u} (forget Ab.{u}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u, u, 0, u} _
  have hbij := (ConcreteCategory.isIso_iff_bijective (comparisonMap A I a F)).1 hiso
  constructor
  · intro s hs
    obtain ⟨c, hc⟩ := hbij.2 (limitOfNeighbourhoodFamily A I a F s hs)
    obtain ⟨V, t, rfl⟩ := Concrete.colimit_exists_rep (sectionsNearVanishing A I a F) c
    refine ⟨V.openSet, range_subschemeι_subset A I a V, t, fun n => ?_⟩
    refine (formalLimitSection_comparisonMap A I a F V t n).symm.trans ?_
    refine Eq.trans ?_ (formalLimitSection_limitOfNeighbourhoodFamily A I a F s hs n)
    exact congrArg (fun z => formalLimitSection A I a F z n) hc
  · intro V W hV hW t u htu
    obtain ⟨k, g₁, g₂, hk⟩ := Concrete.colimit_exists_of_rep_eq
      (sectionsNearVanishing A I a F)
      (i := opensNearVanishingOfRangeSubset A I a V hV)
      (j := opensNearVanishingOfRangeSubset A I a W hW) t u
      (hbij.1 (eq_of_formalLimitSection_eq A I a F fun n =>
        (formalLimitSection_comparisonMap A I a F
          (opensNearVanishingOfRangeSubset A I a V hV) t n).trans
        ((htu n).trans (formalLimitSection_comparisonMap A I a F
          (opensNearVanishingOfRangeSubset A I a W hW) u n).symm)))
    exact ⟨k.openSet, range_subschemeι_subset A I a k, g₁.down, g₂.down, hk⟩

end Stacks.Algebraization

end
