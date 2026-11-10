module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CechEnvelopeCharts
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CechEnvelopeProducts

/-!
# Restricting smooth lifts to affine opens

Fix a global crystalline situation `(p, (S, I, γ), X)`, `A = Γ(S, ⊤)`, a scheme `U` over `X`
through `j : U ⟶ X` with `U` affine, and a smooth lift `B` of `U`
(`Crystalline.GlobalCrystallineSituation.CechEnvelope.SmoothLift`): a smooth `A`-algebra with
`Γ(U, ⊤) ≅ B/IB`.  For an étale map `i : V ⟶ U` from an affine scheme `V`, for instance the
inclusion of an affine open, this file restricts `B` to a smooth lift of `V` over `i ≫ j`.

## The construction

The ring map `Γ(U, ⊤) → Γ(V, ⊤)` is étale, and `B → Γ(U, ⊤)` is surjective with kernel `IB`.
Étale algebras lift along surjections ([Stacks, Tag 04D1], `etale_lift_along_surjection`): there is
an étale `B`-algebra `B'` with a surjection `B' → Γ(V, ⊤)` over `B` whose kernel is `(IB)B' = IB'`.
Then `B'` is smooth over `A`, being étale over the smooth `A`-algebra `B`, and `B'/IB' ≅ Γ(V, ⊤)`,
so `B'` is a smooth lift of `V`.  The étale map `B → B'` carries étale coordinates
`t₁, …, t_d ∈ B` (an étale `A[T₁, …, T_d] → B`, `Tᵢ ↦ tᵢ`) to étale coordinates on `B'`.

## Main definitions

* `CechEnvelope.SmoothLift.restrict` — **the smooth lift of `V` obtained from one of `U`** along an
  étale `i : V ⟶ U` of affine schemes; `CechEnvelope.SmoothLift.restrictOpen` for an affine open
  `V` of `U`.
* `CechEnvelope.SmoothLift.restrictAlgHom` — the étale map `B → B'` of `A`-algebras.

## Main results

* `CechEnvelope.SmoothLift.etale_restrictAlgHom` — `B → B'` is étale.
* `CechEnvelope.SmoothLift.restrict_equiv_restrictAlgHom` — it lifts the restriction
  `Γ(U, ⊤) → Γ(V, ⊤)`.
* `CechEnvelope.SmoothLift.etale_aeval_restrict` — étale coordinates restrict.
* `CechEnvelope.exists_smoothLift_etaleCoordinates_inter` — **every nonempty finite intersection of
  affine opens of a separated `X`, one of which carries a smooth lift with étale coordinates,
  carries a smooth lift with étale coordinates.**

## References

* [Stacks Project, Tag 04D1](https://stacks.math.columbia.edu/tag/04D1)
* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Crystalline.GlobalCrystallineSituation.CechEnvelope

open SmallSite

variable {S : GlobalCrystallineSituation.{u}} {U V : Scheme.{u}} {j : U ⟶ S.X}

/-- The structure map to the base of a scheme over `U` factors through that of `U`. -/
theorem comp_sourceToBase_overSituation (i : V ⟶ U) {j' : V ⟶ S.X} (hij : i ≫ j = j') :
    i ≫ sourceToBase (overSituation S j) = sourceToBase (overSituation S j') := by
  subst hij
  change i ≫ (j ≫ S.toClosedFiber) ≫ _ = ((i ≫ j) ≫ S.toClosedFiber) ≫ _
  simp only [Category.assoc]

namespace SmoothLift

variable (L : SmoothLift S j)

/-- The surjection `B → B/IB ≅ Γ(U, ⊤)` of a smooth lift. -/
def toSections : L.ring →+* Γ(U, ⊤) :=
  L.equiv.symm.toRingHom.comp (Ideal.Quotient.mk _)

/-- `B → Γ(U, ⊤)` is surjective. -/
theorem surjective_toSections : Function.Surjective L.toSections :=
  L.equiv.symm.surjective.comp Ideal.Quotient.mk_surjective

/-- The kernel of `B → Γ(U, ⊤)` is `IB`. -/
theorem ker_toSections : RingHom.ker L.toSections =
    (baseSectionsRing S).ideal.map (algebraMap (baseSectionsRing S) L.ring) := by
  ext x
  rw [RingHom.mem_ker, toSections, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe, map_eq_zero_iff _ L.equiv.symm.injective, Ideal.Quotient.eq_zero_iff_mem]

/-- `B → Γ(U, ⊤)` is compatible with the maps from `A`. -/
theorem toSections_algebraMap (a : baseSectionsRing S) :
    L.toSections (algebraMap (baseSectionsRing S) L.ring a) =
      (sourceToBase (overSituation S j)).appTop.hom a := by
  rw [toSections, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.symm_apply_eq, L.equiv_sourceToBase]

variable [IsAffine U] (i : V ⟶ U) [IsAffine V] [Etale i]

/-- **The étale lift of `Γ(V, ⊤)` along `B → Γ(U, ⊤)`** ([Stacks, Tag 04D1]): an étale
`B`-algebra `B'` with a surjection `B' → Γ(V, ⊤)` lifting the restriction `Γ(U, ⊤) → Γ(V, ⊤)`,
with kernel `(IB) B'`. -/
theorem exists_etaleLift :
    ∃ (C : CommAlgCat.{u} L.ring) (ψ : C →+* Γ(V, ⊤)), Algebra.Etale L.ring C ∧
      Function.Surjective ψ ∧ ψ.comp (algebraMap L.ring C) = i.appTop.hom.comp L.toSections ∧
        RingHom.ker ψ = ((baseSectionsRing S).ideal.map
          (algebraMap (baseSectionsRing S) L.ring)).map (algebraMap L.ring C) := by
  let : Algebra L.ring Γ(U, ⊤) := L.toSections.toAlgebra
  let : Algebra Γ(U, ⊤) Γ(V, ⊤) := i.appTop.hom.toAlgebra
  let : Algebra L.ring Γ(V, ⊤) := (i.appTop.hom.comp L.toSections).toAlgebra
  have : IsScalarTower L.ring Γ(U, ⊤) Γ(V, ⊤) := .of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.Etale Γ(U, ⊤) Γ(V, ⊤) := RingHom.etale_algebraMap.1
    ((HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp ‹Etale i›)
  obtain ⟨C, _, _, hC, ψ, hψ, hker⟩ :=
    etale_lift_along_surjection L.ring Γ(U, ⊤) Γ(V, ⊤) L.surjective_toSections
  refine ⟨CommAlgCat.of L.ring C, (ψ : C →+* Γ(V, ⊤)), hC, hψ, ψ.comp_algebraMap, ?_⟩
  rw [hker]
  exact congrArg (Ideal.map (algebraMap L.ring C)) L.ker_toSections

/-- The ring `B'` of `exists_etaleLift`. -/
def liftRing : CommAlgCat.{u} L.ring := (L.exists_etaleLift i).choose

/-- The surjection `B' → Γ(V, ⊤)` of `exists_etaleLift`. -/
def liftMap : L.liftRing i →+* Γ(V, ⊤) := (L.exists_etaleLift i).choose_spec.choose

/-- `B'` is étale over `B`. -/
instance etale_liftRing : Algebra.Etale L.ring (L.liftRing i) :=
  (L.exists_etaleLift i).choose_spec.choose_spec.1

/-- `B' → Γ(V, ⊤)` is surjective. -/
theorem surjective_liftMap : Function.Surjective (L.liftMap i) :=
  (L.exists_etaleLift i).choose_spec.choose_spec.2.1

/-- `B' → Γ(V, ⊤)` lifts the restriction `Γ(U, ⊤) → Γ(V, ⊤)`. -/
theorem liftMap_comp_algebraMap :
    (L.liftMap i).comp (algebraMap L.ring (L.liftRing i)) = i.appTop.hom.comp L.toSections :=
  (L.exists_etaleLift i).choose_spec.choose_spec.2.2.1

/-- The kernel of `B' → Γ(V, ⊤)` is `(IB) B'`. -/
theorem ker_liftMap : RingHom.ker (L.liftMap i) =
    ((baseSectionsRing S).ideal.map (algebraMap (baseSectionsRing S) L.ring)).map
      (algebraMap L.ring (L.liftRing i)) :=
  (L.exists_etaleLift i).choose_spec.choose_spec.2.2.2

/-- The `A`-algebra structure of `B'`, through `B`. -/
abbrev liftRingAlgebra : Algebra (baseSectionsRing S) (L.liftRing i) :=
  ((algebraMap L.ring (L.liftRing i)).comp (algebraMap (baseSectionsRing S) L.ring)).toAlgebra

attribute [local instance] liftRingAlgebra

/-- `A → B → B'` is a scalar tower. -/
instance isScalarTower_liftRing :
    IsScalarTower (baseSectionsRing S) L.ring (L.liftRing i) :=
  .of_algebraMap_eq fun _ ↦ rfl

/-- The kernel of `B' → Γ(V, ⊤)` is `IB'`. -/
theorem ker_liftMap' : RingHom.ker (L.liftMap i) =
    (baseSectionsRing S).ideal.map (algebraMap (baseSectionsRing S) (L.liftRing i)) := by
  rw [L.ker_liftMap i, Ideal.map_map]
  rfl

variable {i} {j' : V ⟶ S.X} (hij : i ≫ j = j')

/-- **The restriction of a smooth lift `B` of `U` along an étale map `i : V ⟶ U` of affine
schemes**: the étale `B`-algebra `B'` lifting `Γ(V, ⊤)` along `B → Γ(U, ⊤)` ([Stacks, Tag 04D1]),
a smooth lift of `V` over `j' = i ≫ j`. -/
def restrict : SmoothLift S j' where
  ring := L.liftRing i
  smooth :=
    haveI := L.smooth
    Algebra.Smooth.comp (baseSectionsRing S) L.ring (L.liftRing i)
  equiv := (RingHom.quotientKerEquivOfSurjective (L.surjective_liftMap i)).symm.trans
    (Ideal.quotEquivOfEq (L.ker_liftMap' i))
  equiv_sourceToBase a := by
    have h1 : (sourceToBase (overSituation S j')).appTop.hom a =
        L.liftMap i (algebraMap (baseSectionsRing S) (L.liftRing i) a) := by
      change _ = ((L.liftMap i).comp (algebraMap L.ring (L.liftRing i)))
        (algebraMap (baseSectionsRing S) L.ring a)
      rw [L.liftMap_comp_algebraMap i, RingHom.comp_apply, toSections_algebraMap,
        ← comp_sourceToBase_overSituation i hij, Scheme.Hom.comp_appTop]
      rfl
    rw [RingEquiv.trans_apply, h1, RingEquiv.symm_apply_eq _ |>.2
      (RingHom.quotientKerEquivOfSurjective_apply_mk (L.surjective_liftMap i) _).symm]
    exact Ideal.quotEquivOfEq_mk (L.ker_liftMap' i) _

/-- **The map `B → B'` of `A`-algebras** from a smooth lift to its restriction. -/
def restrictAlgHom : L.ring →ₐ[baseSectionsRing S] (L.restrict hij).ring :=
  AlgHom.mk (algebraMap L.ring (L.liftRing i)) fun _ ↦ rfl

/-- The underlying ring map of `B → B'` is the algebra map. -/
theorem restrictAlgHom_apply (b : L.ring) :
    L.restrictAlgHom hij b = algebraMap L.ring (L.liftRing i) b := rfl

/-- **`B → B'` is étale.** -/
theorem etale_restrictAlgHom : (L.restrictAlgHom hij).toRingHom.Etale :=
  show (algebraMap L.ring (L.liftRing i)).Etale from RingHom.etale_algebraMap.2 (L.etale_liftRing i)

/-- **`B → B'` lifts the restriction `Γ(U, ⊤) → Γ(V, ⊤)`**: for `b ∈ B`, the class of its image
in `B'/IB' ≅ Γ(V, ⊤)` is the restriction of the class of `b` in `B/IB ≅ Γ(U, ⊤)`. -/
theorem restrict_equiv_restrictAlgHom (b : L.ring) :
    (L.restrict hij).equiv (i.appTop.hom (L.equiv.symm (Ideal.Quotient.mk _ b))) =
      Ideal.Quotient.mk _ (L.restrictAlgHom hij b) := by
  have h : i.appTop.hom (L.equiv.symm (Ideal.Quotient.mk _ b)) =
      L.liftMap i (algebraMap L.ring (L.liftRing i) b) :=
    (RingHom.congr_fun (L.liftMap_comp_algebraMap i) b).symm
  rw [h]
  change (Ideal.quotEquivOfEq (L.ker_liftMap' i))
    ((RingHom.quotientKerEquivOfSurjective (L.surjective_liftMap i)).symm
      (L.liftMap i (algebraMap L.ring (L.liftRing i) b))) = _
  rw [RingEquiv.symm_apply_eq _ |>.2
    (RingHom.quotientKerEquivOfSurjective_apply_mk (L.surjective_liftMap i) _).symm]
  exact Ideal.quotEquivOfEq_mk (L.ker_liftMap' i) _

/-- **Étale coordinates restrict**: if `t₁, …, t_d ∈ B` are étale coordinates, i.e.
`A[T₁, …, T_d] → B`, `Tᵢ ↦ tᵢ`, is étale, so are their images in `B'`. -/
theorem etale_aeval_restrict {d : ℕ} {t : Fin d → L.ring}
    (ht : (MvPolynomial.aeval (R := baseSectionsRing S) t).toRingHom.Etale) :
    (MvPolynomial.aeval (R := baseSectionsRing S) (L.restrictAlgHom hij ∘ t)).toRingHom.Etale := by
  have h : (MvPolynomial.aeval (R := baseSectionsRing S) (L.restrictAlgHom hij ∘ t)).toRingHom =
      (L.restrictAlgHom hij).toRingHom.comp (MvPolynomial.aeval t).toRingHom :=
    (congrArg AlgHom.toRingHom (MvPolynomial.comp_aeval (f := t) (L.restrictAlgHom hij))).symm
  rw [h]
  exact RingHom.Etale.stableUnderComposition _ _ ht (L.etale_restrictAlgHom hij)

/-- **A smooth lift with étale coordinates restricts to one along an étale map of affine
schemes.** -/
theorem exists_etaleCoordinates_restrict {d : ℕ} {t : Fin d → L.ring}
    (ht : (MvPolynomial.aeval (R := baseSectionsRing S) t).toRingHom.Etale) :
    ∃ t' : Fin d → (L.restrict hij).ring,
      (MvPolynomial.aeval (R := baseSectionsRing S) t').toRingHom.Etale :=
  ⟨_, L.etale_aeval_restrict hij ht⟩

/-- **The restriction of a smooth lift of `U` to an affine open `V` of `U`**, a smooth lift of `V`
over `V ↪ U ⟶ X`. -/
abbrev restrictOpen (W : U.Opens) [IsAffine W.toScheme] : SmoothLift S (W.ι ≫ j) :=
  L.restrict (i := W.ι) rfl

end SmoothLift

/-- **Every nonempty finite intersection of affine opens of a separated `X`, one of which carries a
smooth lift with étale coordinates, carries a smooth lift with étale coordinates**: for affine
opens `U₀, …, U_n` of `X` and a smooth lift of `U_k` with étale coordinates `t₁, …, t_d`, the
affine open `U₀ ∩ ⋯ ∩ U_n` has a smooth lift with `d` étale coordinates, the restriction along
`U₀ ∩ ⋯ ∩ U_n ⊆ U_k`. -/
theorem exists_smoothLift_etaleCoordinates_inter [S.X.IsSeparated] {n : ℕ}
    (U : Fin (n + 1) → S.X.Opens) [∀ k, IsAffine (U k)] (k : Fin (n + 1))
    (L : SmoothLift S (U k).ι) {d : ℕ} {t : Fin d → L.ring}
    (ht : (MvPolynomial.aeval (R := baseSectionsRing S) t).toRingHom.Etale) :
    ∃ (L' : SmoothLift S (inter U).ι) (t' : Fin d → L'.ring),
      (MvPolynomial.aeval (R := baseSectionsRing S) t').toRingHom.Etale :=
  ⟨_, L.exists_etaleCoordinates_restrict (i := S.X.homOfLE (inter_le U k))
    (Scheme.homOfLE_ι _ _) ht⟩

/-- **The nonempty finite intersections of the charts of a separated `X` carry smooth lifts with
étale coordinates**: if each of the affine opens `U₀, …, U_n` of `X` carries a smooth lift with
étale coordinates, so does `U₀ ∩ ⋯ ∩ U_n`. -/
theorem exists_smoothLift_etaleCoordinates_inter_of_forall [S.X.IsSeparated] {n : ℕ}
    (U : Fin (n + 1) → S.X.Opens) [∀ k, IsAffine (U k)]
    (h : ∀ k, ∃ (L : SmoothLift S (U k).ι) (d : ℕ) (t : Fin d → L.ring),
      (MvPolynomial.aeval (R := baseSectionsRing S) t).toRingHom.Etale) :
    ∃ (L' : SmoothLift S (inter U).ι) (d : ℕ) (t' : Fin d → L'.ring),
      (MvPolynomial.aeval (R := baseSectionsRing S) t').toRingHom.Etale := by
  obtain ⟨L, d, t, ht⟩ := h 0
  exact (exists_smoothLift_etaleCoordinates_inter U 0 L ht).imp fun _ h' ↦ ⟨d, h'⟩

end Crystalline.GlobalCrystallineSituation.CechEnvelope
