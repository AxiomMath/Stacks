module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct
public import StacksFrontier.Deformation.Artin.FormalObject
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Full faithfulness of the approximation functor

Let `p : F ⥤ (big fppf site over S)` be a category fibred in groupoids. The approximation
functor of Stacks 07X6 sends an object of `F` lying over the spectrum of a Noetherian
complete local `S`-algebra to the system of its restrictions to the infinitesimal
thickenings of the closed point. Stacks 07X8 asserts that this functor is an equivalence
when `p` is an algebraic stack over a locally Noetherian scheme.

The source proves it in three cases. This file carries out the two halves of Cases I and II
that need no input beyond completeness of the base: a morphism from the spectrum of a
Noetherian complete local ring to a scheme is determined by, and can be assembled from, its
restrictions to the infinitesimal thickenings of the closed point. Both statements are
proved here directly, rather than quoted from Stacks 0AQG and 0AQH, because the
`𝔪`-adic case is the one where the compatible system of ring maps to the quotients
`R ⧸ 𝔪 ^ (n + 1)` is lifted by adic completeness alone.

From the first statement the approximation functor is **faithful** whenever `p` itself is
faithful, i.e. whenever `p` is fibred in setoids; this covers the categories fibred in
groupoids represented by a scheme and by an algebraic space, Cases I and II of the source
proof. From both statements the approximation functor is **full** for the category fibred
in groupoids represented by an object of the site, i.e. by a scheme over `S`, which is
Case I.

## Main definitions

None; this file only proves theorems about the functor of
`Deformation.Artin.approximationFunctorData`.

## Main results

* `Deformation.Artin.hom_ext_of_adicThickening` — a morphism out of the spectrum of a
  complete local ring is determined by its restrictions to the infinitesimal thickenings of
  the closed point.
* `Deformation.Artin.exists_lift_of_adicThickening` — a compatible family of morphisms from
  the infinitesimal thickenings to a scheme comes from a morphism on the whole spectrum.
* `Deformation.Artin.faithful_approximationFunctor` — **Stacks 07X8**, faithfulness, for a
  category fibred in setoids.
* `Deformation.Artin.full_approximationFunctor_representable` — **Stacks 07X8**, fullness,
  for the category fibred in groupoids represented by an object of the site.
* `Deformation.Artin.eq_closedPoint_of_adicThickening` — an infinitesimal thickening of the
  closed point has only the closed point.

## Implementation notes

The approximation functor is reached only through the equations of
`Deformation.Artin.IsApproximationFunctor`, so every statement here is proved for an
arbitrary functor satisfying them and then specialised; nothing depends on the particular
cartesian lifts chosen in its construction.

`Deformation.Artin.chosenBase` picks a complete local base for an object of `F` by
`Classical.choose`, while a formal object carries its own base, so the two are identified
only by the equation supplied with `Deformation.Artin.IsApproximationFunctor`. The
transports along that equation are the `eqToHom`s that pervade the proofs; they are
cancelled by substituting the equation, since the simp-normal form of a composite of
transports is not reached across the semireducible site functors.

The source's hypothesis that `S` is locally Noetherian is not needed for these two
statements and is therefore not imposed; the finite-type condition on the residue field,
which is where that hypothesis is used in the source, is already part of
`Deformation.Artin.FormalBase`.

What is **not** proved here, and what Stacks 07X8 needs beyond it:

* essential surjectivity, even in Case I. Lifting the compatible family of maps to `Xo` is
  exactly `Deformation.Artin.exists_lift_of_adicThickening`, but the resulting object lies
  over `Spec R` for the base `R` of the given formal object, and a formal object only
  records that each *thickening* `Spec (R ⧸ 𝔪 ^ (n + 1))` belongs to the chosen big fppf
  site. Membership of `Spec R` itself — automatic in the source's set-theoretic
  conventions, and true because the cutoff of a `AlgebraicGeometry.BigFppfSite` is a strong
  prelimit of uncountable cofinality — is not available as a lemma, and the base produced
  by `Deformation.Artin.chosenBase` for the new object need not be the given one, so the
  comparison isomorphism of formal objects has to be transported along an equality of
  spectra rather than of rings.
* Cases II and III: representability of `Isom(x, x')` by an algebraic space for an
  algebraic stack, the surjectivity half of Stacks 0AQH, the density of finitely separable
  points on a smooth algebraic space over a field, the infinitesimal lifting criterion of
  smoothness for algebraic spaces, and fppf descent along `Spec R' → Spec R` for a finite
  étale extension of complete local rings.

## References

* [Stacks Project, Tag 07X8](https://stacks.math.columbia.edu/tag/07X8)
* [Stacks Project, Tag 07X6](https://stacks.math.columbia.edu/tag/07X6)
-/

@[expose] public noncomputable section

namespace Deformation.Artin

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u v w

/-- A morphism from an affine scheme factors through an affine open containing its image. -/
private theorem isoSpec_hom_comp_fromSpec {X T : Scheme.{u}} [IsAffine X] {U : T.Opens}
    (hU : IsAffineOpen U) (a : X ⟶ T) (ia : ⊤ ≤ a ⁻¹ᵁ U) :
    (X.isoSpec.hom ≫ Spec.map (a.appLE U ⊤ ia)) ≫ hU.fromSpec = a := by
  rw [Category.assoc, hU.SpecMap_appLE_fromSpec a (isAffineOpen_top _) ia]
  simp [IsAffineOpen.fromSpec_top]

/-- A morphism from the spectrum of a complete local ring to a scheme is determined by its
restrictions to the infinitesimal thickenings of the closed point. -/
public theorem hom_ext_of_adicThickening {R : Type u} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] {T : Scheme.{u}}
    {a b : Spec (.of R) ⟶ T}
    (h : ∀ n, adicThickeningι R (maximalIdeal R) n ≫ a =
      adicThickeningι R (maximalIdeal R) n ≫ b) : a = b := by
  have : Nontrivial (R ⧸ maximalIdeal R ^ (0 + 1)) :=
    Ideal.Quotient.nontrivial_iff.mpr (by simpa only [zero_add, pow_one] using
      (maximalIdeal.isMaximal R).ne_top)
  have : IsLocalRing (R ⧸ maximalIdeal R ^ (0 + 1)) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hcp : adicThickeningι R (maximalIdeal R) 0
      (closedPoint (R ⧸ maximalIdeal R ^ (0 + 1))) = closedPoint R := by
    have : IsLocalHom (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1))) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    exact Spec_closedPoint
  have hab : a (closedPoint R) = b (closedPoint R) := by
    have h0 := congrArg (fun e => e (closedPoint (R ⧸ maximalIdeal R ^ (0 + 1)))) (h 0)
    change a ((adicThickeningι R (maximalIdeal R) 0)
      (closedPoint (R ⧸ maximalIdeal R ^ (0 + 1)))) =
      b ((adicThickeningι R (maximalIdeal R) 0)
      (closedPoint (R ⧸ maximalIdeal R ^ (0 + 1)))) at h0
    simpa only [hcp] using h0
  obtain ⟨_, ⟨U, hU, rfl⟩, haU, -⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (a (closedPoint R))) isOpen_univ
  change IsAffineOpen U at hU
  let ia := (Scheme.preimage_eq_top_of_closedPoint_mem (U := U) a haU).ge
  let ib := (Scheme.preimage_eq_top_of_closedPoint_mem (U := U) b (hab ▸ haU)).ge
  let aU : Spec (.of R) ⟶ Spec Γ(T, U) :=
    (Spec (.of R)).isoSpec.hom ≫ Spec.map (a.appLE U ⊤ ia)
  let bU : Spec (.of R) ⟶ Spec Γ(T, U) :=
    (Spec (.of R)).isoSpec.hom ≫ Spec.map (b.appLE U ⊤ ib)
  have ha : aU ≫ hU.fromSpec = a := isoSpec_hom_comp_fromSpec hU a ia
  have hb : bU ≫ hU.fromSpec = b := isoSpec_hom_comp_fromSpec hU b ib
  have habU : ∀ n, adicThickeningι R (maximalIdeal R) n ≫ aU =
      adicThickeningι R (maximalIdeal R) n ≫ bU :=
    fun n => (cancel_mono hU.fromSpec).mp (by simpa [ha, hb] using h n)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective aU
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective bU
  have heq : φ = ψ := by
    apply CommRingCat.hom_ext
    have hs : StrictMono (fun n : ℕ => n + 1) := fun _ _ hij => Nat.add_lt_add_right hij 1
    apply DFunLike.coe_injective
    apply IsHausdorff.StrictMono.funext' (maximalIdeal R) hs
    intro n x
    have hn := habU n
    rw [← hφ, ← hψ] at hn
    simpa [Spec.preimage_comp, adicThickeningι] using
      congrArg (fun k => k.hom x) (congrArg Spec.preimage hn)
  rw [← ha, ← hb, ← hφ, ← hψ, heq]

/-- A positive power of the maximal ideal is proper. -/
public instance nontrivial_quotient_pow_maximalIdeal {R : Type u} [CommRing R]
    [IsLocalRing R] (n : ℕ) : Nontrivial (R ⧸ maximalIdeal R ^ (n + 1)) :=
  Ideal.Quotient.nontrivial_iff.mpr fun h =>
    (maximalIdeal.isMaximal R).ne_top
      (top_le_iff.mp (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero n)))

/-- The quotient by a positive power of the maximal ideal is again local. -/
public instance isLocalRing_quotient_pow_maximalIdeal {R : Type u} [CommRing R]
    [IsLocalRing R] (n : ℕ) : IsLocalRing (R ⧸ maximalIdeal R ^ (n + 1)) :=
  IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective

/-- The reduction map between successive infinitesimal thickenings is local. -/
public instance isLocalHom_factorPow_maximalIdeal {R : Type u} [CommRing R]
    [IsLocalRing R] (n : ℕ) :
    IsLocalHom (Ideal.Quotient.factorPow (maximalIdeal R) (Nat.le_succ (n + 1))) :=
  IsLocalHom.of_surjective _ (Ideal.Quotient.factor_surjective _)

/-- The inclusion of the `n`-th infinitesimal thickening carries the closed point to the
closed point. -/
public theorem adicThickeningι_closedPoint {R : Type u} [CommRing R] [IsLocalRing R]
    (n : ℕ) :
    adicThickeningι R (maximalIdeal R) n
        (closedPoint (R ⧸ maximalIdeal R ^ (n + 1))) = closedPoint R := by
  have : IsLocalHom (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  exact Spec_closedPoint

/-- The inclusion of one infinitesimal thickening in the next carries the closed point to
the closed point. -/
public theorem adicThickeningSucc_closedPoint {R : Type u} [CommRing R] [IsLocalRing R]
    (n : ℕ) :
    adicThickeningSucc R (maximalIdeal R) n
        (closedPoint (R ⧸ maximalIdeal R ^ (n + 1))) =
      closedPoint (R ⧸ maximalIdeal R ^ (n + 1 + 1)) := by
  have : IsLocalHom (CommRingCat.ofHom
      (Ideal.Quotient.factorPow (maximalIdeal R) (Nat.le_succ (n + 1)))).hom :=
    isLocalHom_factorPow_maximalIdeal n
  exact Spec_closedPoint

/-- A compatible family of morphisms from the infinitesimal thickenings of the closed point
of the spectrum of a complete local ring to a scheme comes from a morphism on the whole
spectrum. -/
@[sga "3 XI 3.3" "partial", sga "3 XV 1.4" "Surjectivity of (∗)"]
public theorem exists_lift_of_adicThickening {R : Type u} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] {T : Scheme.{u}}
    (a : ∀ n, adicThickening R (maximalIdeal R) n ⟶ T)
    (ha : ∀ n, adicThickeningSucc R (maximalIdeal R) n ≫ a (n + 1) = a n) :
    ∃ b : Spec (.of R) ⟶ T, ∀ n, adicThickeningι R (maximalIdeal R) n ≫ b = a n := by
  -- every level carries the closed point to one and the same point of `T`
  have hpt : ∀ n, a n (closedPoint (R ⧸ maximalIdeal R ^ (n + 1))) =
      a 0 (closedPoint (R ⧸ maximalIdeal R ^ (0 + 1))) := by
    intro n
    induction n with
    | zero => rfl
    | succ k hk =>
      have h := congrArg (fun e : adicThickening R (maximalIdeal R) k ⟶ T =>
        e (closedPoint (R ⧸ maximalIdeal R ^ (k + 1)))) (ha k)
      change a (k + 1) (adicThickeningSucc R (maximalIdeal R) k
        (closedPoint (R ⧸ maximalIdeal R ^ (k + 1)))) = _ at h
      rw [adicThickeningSucc_closedPoint] at h
      exact h.trans hk
  obtain ⟨_, ⟨U, hU, rfl⟩, haU, -⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (a 0 (closedPoint (R ⧸ maximalIdeal R ^ (0 + 1))))) isOpen_univ
  change IsAffineOpen U at hU
  -- each level factors through the chosen affine open
  let ia := fun n =>
    (Scheme.preimage_eq_top_of_closedPoint_mem (U := U) (a n) ((hpt n) ▸ haU)).ge
  let aU : ∀ n, adicThickening R (maximalIdeal R) n ⟶ Spec Γ(T, U) := fun n =>
    (adicThickening R (maximalIdeal R) n).isoSpec.hom ≫
      Spec.map ((a n).appLE U ⊤ (ia n))
  have haUfac : ∀ n, aU n ≫ hU.fromSpec = a n := fun n =>
    isoSpec_hom_comp_fromSpec hU (a n) (ia n)
  -- the induced ring maps to the levels form a compatible family
  let f : ∀ n, Γ(T, U) →+* R ⧸ maximalIdeal R ^ (n + 1) := fun n =>
    (Spec.preimage (aU n)).hom
  have hsuccU : ∀ n, adicThickeningSucc R (maximalIdeal R) n ≫ aU (n + 1) = aU n :=
    fun n => (cancel_mono hU.fromSpec).mp (by rw [Category.assoc, haUfac, haUfac, ha n])
  have hf : ∀ {m : ℕ},
      (Ideal.Quotient.factorPow (maximalIdeal R) (Nat.le_succ (m + 1))).comp (f (m + 1)) =
        f m := by
    intro m
    have h := congrArg Spec.preimage (hsuccU m)
    rw [Spec.preimage_comp, adicThickeningSucc, Spec.preimage_map] at h
    apply RingHom.ext
    intro x
    simpa [f] using congrArg (fun k : Γ(T, U) ⟶
      CommRingCat.of (R ⧸ maximalIdeal R ^ (m + 1)) => k.hom x) h
  have hs : StrictMono (fun n : ℕ => n + 1) := fun _ _ hij => Nat.add_lt_add_right hij 1
  let φ : Γ(T, U) →+* R :=
    IsAdicComplete.StrictMono.liftRingHom (maximalIdeal R) hs f (fun {m} => hf)
  refine ⟨Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec, fun n => ?_⟩
  rw [← haUfac n, ← Category.assoc]
  congr 1
  calc adicThickeningι R (maximalIdeal R) n ≫ Spec.map (CommRingCat.ofHom φ)
      = Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk
          (maximalIdeal R ^ (n + 1))).comp φ)) := by
        rw [adicThickeningι, ← Spec.map_comp]
        rfl
    _ = Spec.map (Spec.preimage (aU n)) := by
        rw [IsAdicComplete.StrictMono.mk_comp_liftRingHom (maximalIdeal R) hs f (fun {m} => hf)]
        rfl
    _ = aU n := Spec.map_preimage (aU n)

/-- The inclusion of an infinitesimal thickening is a monomorphism. -/
public instance isClosedImmersion_adicThickeningι {R : Type u} [CommRing R] (I : Ideal R)
    (n : ℕ) : IsClosedImmersion (adicThickeningι R I n) :=
  (IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom
    (Ideal.Quotient.mk (I ^ (n + 1)))) Ideal.Quotient.mk_surjective :
      IsClosedImmersion (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1))))))

/-- The inclusion of an infinitesimal thickening is a monomorphism. -/
public instance mono_adicThickeningι {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) :
    Mono (adicThickeningι R I n) := inferInstance

/-- The spectrum of an infinitesimal thickening of the closed point has only the closed
point: the maximal ideal of `R ⧸ 𝔪 ^ (n + 1)` is nilpotent, hence contained in every
prime. -/
public theorem eq_closedPoint_of_adicThickening {R : Type u} [CommRing R] [IsLocalRing R]
    (n : ℕ) (z : adicThickening R (maximalIdeal R) n) :
    z = closedPoint (R ⧸ maximalIdeal R ^ (n + 1)) := by
  have key : ∀ w : PrimeSpectrum (R ⧸ maximalIdeal R ^ (n + 1)),
      w = closedPoint (R ⧸ maximalIdeal R ^ (n + 1)) := by
    intro w
    apply PrimeSpectrum.ext
    refine le_antisymm (le_maximalIdeal w.2.ne_top) ?_
    intro t ht
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective t
    have hs : s ∈ maximalIdeal R := by
      by_contra hsu
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hsu
      exact ((IsLocalRing.mem_maximalIdeal _).mp ht)
        (hsu.map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))))
    have hpow : (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))) s ^ (n + 1) = 0 := by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow hs (n + 1)
    exact w.2.mem_of_pow_mem (n + 1) (hpow ▸ w.asIdeal.zero_mem)
  exact key z

/-- Transport of the structure morphism of a complete local base along an equality of
bases. -/
public theorem eqToHom_formalBase_toS {S : Scheme.{u}} {A A' : FormalBase S} (h : A = A') :
    eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) h) ≫ A'.toS = A.toS := by
  subst h
  simp

/-- Transport carries the closed point to the closed point. -/
public theorem eqToHom_formalBase_closedPoint {S : Scheme.{u}} {A A' : FormalBase S}
    (h : A = A') :
    (eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) h) :
      Spec (.of A.R) ⟶ Spec (.of A'.R)) (closedPoint A.R) = closedPoint A'.R := by
  subst h
  rfl

/-- Two successive transport isomorphisms cancel. -/
private theorem eqToHom_cancel_assoc {C : Type*} [Category C] {X Y Z : C} (h : X = Y)
    (f : X ⟶ Z) : eqToHom h ≫ eqToHom h.symm ≫ f = f := by
  subst h
  simp

/-- Two successive transport isomorphisms cancel, in the other order. -/
private theorem eqToHom_cancel_assoc' {C : Type*} [Category C] {X Y Z : C} (h : X = Y)
    (f : Y ⟶ Z) : eqToHom h.symm ≫ eqToHom h ≫ f = f := by
  subst h
  simp

/-- Cancelling a transport isomorphism and its inverse between two composites. -/
private theorem comp_eqToHom_cancel_assoc {C : Type*} [Category C] {X Y Z W : C} (h : Y = Z)
    (f : X ⟶ Y) (g : Y ⟶ W) : (f ≫ eqToHom h) ≫ eqToHom h.symm ≫ g = f ≫ g := by
  subst h
  simp

/-- Cancelling a transport isomorphism on the right. -/
private theorem eqToHom_cancel_right {C : Type*} [Category C] {X Y Z : C} (h : Y = Z)
    {u v : X ⟶ Y} (huv : u ≫ eqToHom h = v ≫ eqToHom h) : u = v := by
  subst h
  simpa only [eqToHom_refl, Category.comp_id] using huv

/-- Transport carries the closed point to the closed point, in the reverse direction. -/
public theorem eqToHom_symm_formalBase_closedPoint {S : Scheme.{u}} {A A' : FormalBase S}
    (h : A = A') :
    (eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) h).symm :
      Spec (.of A'.R) ⟶ Spec (.of A.R)) (closedPoint A'.R) = closedPoint A.R := by
  subst h
  rfl

/-- Cancelling a transport isomorphism on the left. -/
private theorem eqToHom_cancel_left {C : Type*} [Category C] {X Y Z : C} (h : X = Y)
    {u v : Y ⟶ Z} (huv : eqToHom h ≫ u = eqToHom h ≫ v) : u = v := by
  subst h
  simpa only [eqToHom_refl, Category.id_comp] using huv

/-! ### Faithfulness of the approximation functor -/

section

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F] (p : F ⥤ BigFppfOver B S hS)

/-- The restriction maps of an approximation functor, read in schemes, are the inclusions
of the infinitesimal thickenings of the complete local base. -/
public theorem toScheme_restriction
    {G : CompleteLocalObjects B S hS p ⥤ FormalObject B S hS p}
    {r : ∀ (x : CompleteLocalObjects B S hS p) (n : ℕ), (G.obj x).level n ⟶ x.obj.1}
    {hb : ∀ x, (G.obj x).base = chosenBase B S hS p x.obj}
    (hι : ∀ x n,
      (BigFppfOver.toScheme B S hS).map
          (eqToHom ((G.obj x).level_eq n).symm ≫ p.map (r x n) ≫
            eqToHom (chosenBase_eq B S hS p x.obj)) =
        adicThickeningι (G.obj x).base.R (maximalIdeal (G.obj x).base.R) n ≫
          eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) (hb x)))
    (x : CompleteLocalObjects B S hS p)
    {Z : BigFppfOver B S hS} (u v : baseOver B S hS (chosenBase B S hS p x.obj)
      (chosenContains B S hS p x.obj) ⟶ Z)
    (huv : ∀ n, (eqToHom ((G.obj x).level_eq n).symm ≫ p.map (r x n) ≫
      eqToHom (chosenBase_eq B S hS p x.obj)) ≫ u =
      (eqToHom ((G.obj x).level_eq n).symm ≫ p.map (r x n) ≫
        eqToHom (chosenBase_eq B S hS p x.obj)) ≫ v) :
    u = v := by
  have : IsAdicComplete (maximalIdeal (G.obj x).base.R) (G.obj x).base.R :=
    (G.obj x).base.complete
  have hmap : (BigFppfOver.toScheme B S hS).map u = (BigFppfOver.toScheme B S hS).map v := by
    have hcancel :
        eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) (hb x)) ≫
            (BigFppfOver.toScheme B S hS).map u =
          eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) (hb x)) ≫
            (BigFppfOver.toScheme B S hS).map v := by
      apply hom_ext_of_adicThickening (R := (G.obj x).base.R)
      intro n
      have h := congrArg (fun z => (BigFppfOver.toScheme B S hS).map z) (huv n)
      simp only [Functor.map_comp, hι x n] at h
      exact ((Category.assoc _ _ _).symm.trans h).trans (Category.assoc _ _ _)
    exact eqToHom_cancel_left _ hcancel
  exact (BigFppfOver.toScheme B S hS).map_injective hmap

/-- **Faithfulness of the functor (Stacks 07X6)** for a category fibred in groupoids whose
structure functor is faithful, i.e. one fibred in setoids. A morphism out of the spectrum
of a Noetherian complete local ring is determined by its restrictions to the infinitesimal
thickenings of the closed point, and for a faithful structure functor a morphism of objects
is determined by the morphism it lies over. -/
public theorem faithful_of_isApproximationFunctor [p.Faithful]
    {G : CompleteLocalObjects B S hS p ⥤ FormalObject B S hS p}
    (hG : IsApproximationFunctor B S hS p G) : G.Faithful := by
  obtain ⟨r, hb, -, -, hnat, hι⟩ := hG
  refine ⟨fun {x y} f g hfg => ?_⟩
  refine (wideSubcategoryInclusion (localBaseMaps B S hS p)).map_injective ?_
  refine ObjectProperty.hom_ext (P := IsCompleteLocalObject B S hS p) ?_
  refine p.map_injective ?_
  show p.map f.1.1 = p.map g.1.1
  have key : ∀ n, (eqToHom ((G.obj x).level_eq n).symm ≫ p.map (r x n) ≫
      eqToHom (chosenBase_eq B S hS p x.obj)) ≫
        (eqToHom (chosenBase_eq B S hS p x.obj).symm ≫ p.map f.1.1) =
      (eqToHom ((G.obj x).level_eq n).symm ≫ p.map (r x n) ≫
        eqToHom (chosenBase_eq B S hS p x.obj)) ≫
        (eqToHom (chosenBase_eq B S hS p x.obj).symm ≫ p.map g.1.1) := by
    intro n
    have h : r x n ≫ f.1.1 = r x n ≫ g.1.1 := by
      rw [← hnat x y f n, ← hnat x y g n, hfg]
    have h' := congrArg (fun z => p.map z) h
    simp only [Functor.map_comp] at h'
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    simpa only [Category.assoc] using congrArg
      (fun z => eqToHom ((G.obj x).level_eq n).symm ≫ z) h'
  have hcancel := toScheme_restriction B S hS p (G := G) (r := r) (hb := hb) hι x _ _ key
  exact eqToHom_cancel_left _ hcancel

/-- **Stacks 07X8, faithfulness of the functor (Stacks 07X6)**, for a category fibred in
groupoids whose structure functor is faithful, i.e. one fibred in setoids. This covers the
category fibred in groupoids represented by an object of the big fppf site over `S`, i.e.
by a scheme over `S`, which is Case I of the source proof.

Faithfulness of `p` is a hypothesis the source does not impose; it holds exactly when `p`
is fibred in setoids, so it excludes a general algebraic stack. The source's hypothesis
that `S` is locally Noetherian is, on the other hand, not needed here. -/
@[stacks 07X8 "faithfulness of the functor only, and only for a category fibred in \
groupoids whose structure functor is faithful, i.e. one fibred in setoids, with the \
faithfulness of that functor as an added hypothesis the source lacks; this covers the \
category represented by an object of the site, but neither fullness, nor essential \
surjectivity, nor a general algebraic stack"]
public theorem faithful_approximationFunctor [p.Faithful]
    (hp : p.IsFiberedInGroupoids) :
    (approximationFunctor B S hS p hp).Faithful :=
  faithful_of_isApproximationFunctor B S hS p (approximationFunctorData B S hS p hp).2

end


/-! ### Fullness for a category fibred in groupoids represented by an object of the site -/

section Representable

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Fullness of the functor (Stacks 07X6)** for the category fibred in groupoids
represented by an object `Xo` of the big fppf site over `S`, i.e. by a scheme over `S`.

A morphism of formal objects induces a morphism of their complete local bases, and the
triangle over `Xo` commutes because it does so after restriction to every infinitesimal
thickening, which determines a morphism out of the spectrum of a complete local ring. -/
public theorem full_of_isApproximationFunctor_representable (Xo : BigFppfOver B S hS)
    {G : CompleteLocalObjects B S hS (Over.forget Xo) ⥤
      FormalObject B S hS (Over.forget Xo)}
    (hG : IsApproximationFunctor B S hS (Over.forget Xo) G) : G.Full := by
  obtain ⟨r, hb, -, -, hnat, hι⟩ := hG
  constructor
  intro x y Φ
  -- the base map of `Φ`, transported to the chosen complete local bases
  have hαS :
      (eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) (hb x)).symm ≫
          Φ.baseMap ≫
            eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) (hb y))) ≫
        (chosenBase B S hS (Over.forget Xo) y.obj).toS =
      (chosenBase B S hS (Over.forget Xo) x.obj).toS := by
    rw [Category.assoc, Category.assoc, eqToHom_formalBase_toS (hb y),
      Φ.baseMap_spec.1, ← eqToHom_formalBase_toS (hb x), ← Category.assoc,
      eqToHom_trans, eqToHom_refl, Category.id_comp]
  obtain ⟨ab, hab⟩ : ∃ ab : baseOver B S hS (chosenBase B S hS (Over.forget Xo) x.obj)
        (chosenContains B S hS (Over.forget Xo) x.obj) ⟶
      baseOver B S hS (chosenBase B S hS (Over.forget Xo) y.obj)
        (chosenContains B S hS (Over.forget Xo) y.obj),
      (BigFppfOver.toScheme B S hS).map ab =
        eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) (hb x)).symm ≫
          Φ.baseMap ≫
            eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) (hb y)) :=
    ⟨Over.homMk (ObjectProperty.homMk
        (X := B.obj (chosenContains B S hS (Over.forget Xo) x.obj))
        (Y := B.obj (chosenContains B S hS (Over.forget Xo) y.obj)) _)
      (by apply ObjectProperty.hom_ext; exact hαS), rfl⟩
  -- the level maps of `Φ` lie over the reductions of its base map
  have hψ : ∀ n, (BigFppfOver.toScheme B S hS).map
        (eqToHom ((G.obj x).level_eq n).symm ≫ (Over.forget Xo).map (Φ.app n) ≫
          eqToHom ((G.obj y).level_eq n)) ≫
        adicThickeningι (G.obj y).base.R (maximalIdeal (G.obj y).base.R) n =
      adicThickeningι (G.obj x).base.R (maximalIdeal (G.obj x).base.R) n ≫ Φ.baseMap :=
    fun n => Φ.baseMap_spec.2 n
  -- the restriction maps intertwine the base map with the level maps
  have hρab : ∀ n,
      (eqToHom ((G.obj x).level_eq n).symm ≫ (Over.forget Xo).map (r x n) ≫
          eqToHom (chosenBase_eq B S hS (Over.forget Xo) x.obj)) ≫ ab =
        (eqToHom ((G.obj x).level_eq n).symm ≫ (Over.forget Xo).map (Φ.app n) ≫
            eqToHom ((G.obj y).level_eq n)) ≫
          (eqToHom ((G.obj y).level_eq n).symm ≫ (Over.forget Xo).map (r y n) ≫
            eqToHom (chosenBase_eq B S hS (Over.forget Xo) y.obj)) := by
    intro n
    refine (BigFppfOver.toScheme B S hS).map_injective ?_
    rw [Functor.map_comp, hι x n, hab, Functor.map_comp, hι y n]
    refine (comp_eqToHom_cancel_assoc _ _ _).trans ?_
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) (hb y)))
        (hψ n).symm).trans (Category.assoc _ _ _))
  -- the triangle over `Xo` commutes
  have hw : ab ≫ (eqToHom (chosenBase_eq B S hS (Over.forget Xo) y.obj).symm ≫
        y.obj.1.hom) =
      eqToHom (chosenBase_eq B S hS (Over.forget Xo) x.obj).symm ≫ x.obj.1.hom := by
    refine toScheme_restriction B S hS (Over.forget Xo) (G := G) (r := r) (hb := hb)
      hι x _ _ ?_
    intro n
    have hΦw : (Over.forget Xo).map (Φ.app n) ≫ ((G.obj y).level n).hom =
        ((G.obj x).level n).hom := Over.w (Φ.app n)
    have hrxw : (Over.forget Xo).map (r x n) ≫ x.obj.1.hom =
        ((G.obj x).level n).hom := Over.w (r x n)
    have hryw : (Over.forget Xo).map (r y n) ≫ y.obj.1.hom =
        ((G.obj y).level n).hom := Over.w (r y n)
    rw [← Category.assoc, hρab n]
    simp only [Category.assoc, eqToHom_cancel_assoc]
    rw [hryw, hΦw, hrxw]
  -- the base map preserves the closed point
  have hΦcp : Φ.baseMap (closedPoint (G.obj x).base.R) =
      closedPoint (G.obj y).base.R := by
    have hpt : adicThickeningι (G.obj y).base.R (maximalIdeal (G.obj y).base.R) 0
          ((BigFppfOver.toScheme B S hS).map (eqToHom ((G.obj x).level_eq 0).symm ≫
            (Over.forget Xo).map (Φ.app 0) ≫ eqToHom ((G.obj y).level_eq 0))
            (closedPoint ((G.obj x).base.R ⧸ maximalIdeal (G.obj x).base.R ^ (0 + 1)))) =
        Φ.baseMap (adicThickeningι (G.obj x).base.R (maximalIdeal (G.obj x).base.R) 0
          (closedPoint ((G.obj x).base.R ⧸ maximalIdeal (G.obj x).base.R ^ (0 + 1)))) :=
      congrArg (fun e : adicThickening (G.obj x).base.R
          (maximalIdeal (G.obj x).base.R) 0 ⟶ Spec (.of (G.obj y).base.R) =>
        e (closedPoint ((G.obj x).base.R ⧸ maximalIdeal (G.obj x).base.R ^ (0 + 1))))
        (hψ 0)
    have hz : (BigFppfOver.toScheme B S hS).map
        (eqToHom ((G.obj x).level_eq 0).symm ≫ (Over.forget Xo).map (Φ.app 0) ≫
          eqToHom ((G.obj y).level_eq 0))
        (closedPoint ((G.obj x).base.R ⧸ maximalIdeal (G.obj x).base.R ^ (0 + 1))) =
        closedPoint ((G.obj y).base.R ⧸ maximalIdeal (G.obj y).base.R ^ (0 + 1)) :=
      eq_closedPoint_of_adicThickening 0 _
    rw [hz, adicThickeningι_closedPoint, adicThickeningι_closedPoint] at hpt
    exact hpt.symm
  -- the morphism of complete local objects
  obtain ⟨fm, hfm⟩ : ∃ fm : x.obj ⟶ y.obj, (Over.forget Xo).map fm.1 =
      eqToHom (chosenBase_eq B S hS (Over.forget Xo) x.obj) ≫ ab ≫
        eqToHom (chosenBase_eq B S hS (Over.forget Xo) y.obj).symm :=
    ⟨ObjectProperty.homMk (Over.homMk _ (by
      simp only [Category.assoc]
      rw [hw]
      exact eqToHom_cancel_assoc _ _)), rfl⟩
  have hbm : baseMap B S hS (Over.forget Xo) fm =
      (BigFppfOver.toScheme B S hS).map ab := by
    have hinner : eqToHom (chosenBase_eq B S hS (Over.forget Xo) x.obj).symm ≫
        (eqToHom (chosenBase_eq B S hS (Over.forget Xo) x.obj) ≫ ab ≫
          eqToHom (chosenBase_eq B S hS (Over.forget Xo) y.obj).symm) ≫
          eqToHom (chosenBase_eq B S hS (Over.forget Xo) y.obj) = ab := by
      simp only [Category.assoc, eqToHom_cancel_assoc', eqToHom_trans, eqToHom_refl,
        Category.comp_id]
    show (BigFppfOver.toScheme B S hS).map
      (eqToHom (chosenBase_eq B S hS (Over.forget Xo) x.obj).symm ≫
        (Over.forget Xo).map fm.1 ≫
        eqToHom (chosenBase_eq B S hS (Over.forget Xo) y.obj)) = _
    rw [hfm, hinner]
  have hloc : localBaseMaps B S hS (Over.forget Xo) fm := by
    show baseMap B S hS (Over.forget Xo) fm
        (closedPoint (chosenBase B S hS (Over.forget Xo) x.obj).R) =
      closedPoint (chosenBase B S hS (Over.forget Xo) y.obj).R
    rw [hbm, hab]
    show eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) (hb y))
        (Φ.baseMap (eqToHom
          (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) (hb x)).symm
          (closedPoint (chosenBase B S hS (Over.forget Xo) x.obj).R))) =
      closedPoint (chosenBase B S hS (Over.forget Xo) y.obj).R
    rw [eqToHom_symm_formalBase_closedPoint (hb x), hΦcp,
      eqToHom_formalBase_closedPoint (hb y)]
  refine ⟨⟨fm, hloc⟩, ?_⟩
  apply FormalObject.Hom.ext
  intro n
  apply Over.OverMorphism.ext
  -- the two level maps agree, because both lie over the same reduction of the base map
  have hstep :
      (eqToHom ((G.obj x).level_eq n).symm ≫
          (Over.forget Xo).map ((G.map (⟨fm, hloc⟩ : x ⟶ y)).app n) ≫
          eqToHom ((G.obj y).level_eq n)) ≫
        (eqToHom ((G.obj y).level_eq n).symm ≫ (Over.forget Xo).map (r y n) ≫
          eqToHom (chosenBase_eq B S hS (Over.forget Xo) y.obj)) =
      (eqToHom ((G.obj x).level_eq n).symm ≫ (Over.forget Xo).map (r x n) ≫
        eqToHom (chosenBase_eq B S hS (Over.forget Xo) x.obj)) ≫ ab := by
    have h : (Over.forget Xo).map ((G.map (⟨fm, hloc⟩ : x ⟶ y)).app n) ≫
        (Over.forget Xo).map (r y n) =
      (Over.forget Xo).map (r x n) ≫
        (eqToHom (chosenBase_eq B S hS (Over.forget Xo) x.obj) ≫ ab ≫
          eqToHom (chosenBase_eq B S hS (Over.forget Xo) y.obj).symm) := by
      rw [← hfm, ← Functor.map_comp, ← Functor.map_comp]
      exact congrArg _ (hnat x y ⟨fm, hloc⟩ n)
    calc (eqToHom ((G.obj x).level_eq n).symm ≫
            (Over.forget Xo).map ((G.map (⟨fm, hloc⟩ : x ⟶ y)).app n) ≫
            eqToHom ((G.obj y).level_eq n)) ≫
          (eqToHom ((G.obj y).level_eq n).symm ≫ (Over.forget Xo).map (r y n) ≫
            eqToHom (chosenBase_eq B S hS (Over.forget Xo) y.obj))
        = eqToHom ((G.obj x).level_eq n).symm ≫
            ((Over.forget Xo).map ((G.map (⟨fm, hloc⟩ : x ⟶ y)).app n) ≫
              (Over.forget Xo).map (r y n)) ≫
            eqToHom (chosenBase_eq B S hS (Over.forget Xo) y.obj) := by
          simp only [Category.assoc, eqToHom_cancel_assoc]
      _ = eqToHom ((G.obj x).level_eq n).symm ≫
            ((Over.forget Xo).map (r x n) ≫
              (eqToHom (chosenBase_eq B S hS (Over.forget Xo) x.obj) ≫ ab ≫
                eqToHom (chosenBase_eq B S hS (Over.forget Xo) y.obj).symm)) ≫
            eqToHom (chosenBase_eq B S hS (Over.forget Xo) y.obj) := by rw [h]
      _ = (eqToHom ((G.obj x).level_eq n).symm ≫ (Over.forget Xo).map (r x n) ≫
            eqToHom (chosenBase_eq B S hS (Over.forget Xo) x.obj)) ≫ ab := by
          simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  have hψ' : (BigFppfOver.toScheme B S hS).map
        (eqToHom ((G.obj x).level_eq n).symm ≫
          (Over.forget Xo).map ((G.map (⟨fm, hloc⟩ : x ⟶ y)).app n) ≫
          eqToHom ((G.obj y).level_eq n)) ≫
        adicThickeningι (G.obj y).base.R (maximalIdeal (G.obj y).base.R) n =
      adicThickeningι (G.obj x).base.R (maximalIdeal (G.obj x).base.R) n ≫ Φ.baseMap := by
    refine eqToHom_cancel_right
      (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) (hb y)) ?_
    have h : (BigFppfOver.toScheme B S hS).map
          (eqToHom ((G.obj x).level_eq n).symm ≫
            (Over.forget Xo).map ((G.map (⟨fm, hloc⟩ : x ⟶ y)).app n) ≫
            eqToHom ((G.obj y).level_eq n)) ≫
          (BigFppfOver.toScheme B S hS).map
            (eqToHom ((G.obj y).level_eq n).symm ≫ (Over.forget Xo).map (r y n) ≫
              eqToHom (chosenBase_eq B S hS (Over.forget Xo) y.obj)) =
        (BigFppfOver.toScheme B S hS).map
            (eqToHom ((G.obj x).level_eq n).symm ≫ (Over.forget Xo).map (r x n) ≫
              eqToHom (chosenBase_eq B S hS (Over.forget Xo) x.obj)) ≫
          (BigFppfOver.toScheme B S hS).map ab := by
      rw [← Functor.map_comp, ← Functor.map_comp, hstep]
    rw [hι x n, hι y n, hab] at h
    exact (Category.assoc _ _ _).trans
      (h.trans ((comp_eqToHom_cancel_assoc _ _ _).trans (Category.assoc _ _ _).symm))
  have hlevel : (eqToHom ((G.obj x).level_eq n).symm ≫
        (Over.forget Xo).map ((G.map (⟨fm, hloc⟩ : x ⟶ y)).app n) ≫
        eqToHom ((G.obj y).level_eq n)) =
      (eqToHom ((G.obj x).level_eq n).symm ≫ (Over.forget Xo).map (Φ.app n) ≫
        eqToHom ((G.obj y).level_eq n)) := by
    refine (BigFppfOver.toScheme B S hS).map_injective ?_
    exact (cancel_mono (adicThickeningι (G.obj y).base.R
      (maximalIdeal (G.obj y).base.R) n)).mp (hψ'.trans (hψ n).symm)
  have hfinal := congrArg (fun z => eqToHom ((G.obj x).level_eq n) ≫ z ≫
    eqToHom ((G.obj y).level_eq n).symm) hlevel
  simp only [Category.assoc, eqToHom_cancel_assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id] at hfinal
  exact hfinal

/-- **Stacks 07X8, fullness of the functor (Stacks 07X6)**, for the category fibred in
groupoids represented by an object `Xo` of the big fppf site over `S`, i.e. by a scheme
over `S`. This is the fullness half of Case I of the source proof.

The source's hypothesis that `S` is locally Noetherian is not needed. -/
@[stacks 07X8 "fullness of the functor only, and only for the category fibred in \
groupoids represented by an object of the big fppf site over S, i.e. by a scheme over S; \
this is half of Case I of the source proof, and covers neither essential surjectivity \
nor the algebraic space of Case II nor the general algebraic stack of Case III"]
public theorem full_approximationFunctor_representable (Xo : BigFppfOver B S hS) :
    (approximationFunctor B S hS (Over.forget Xo)
      (Functor.IsFiberedInGroupoids.over_forget Xo)).Full :=
  full_of_isApproximationFunctor_representable Xo
    (approximationFunctorData B S hS (Over.forget Xo)
      (Functor.IsFiberedInGroupoids.over_forget Xo)).2

/-- The approximation functor of the category fibred in groupoids represented by an object
of the big fppf site over `S` is fully faithful. -/
public theorem fullyFaithful_approximationFunctor_representable
    (Xo : BigFppfOver B S hS) :
    (approximationFunctor B S hS (Over.forget Xo)
        (Functor.IsFiberedInGroupoids.over_forget Xo)).Full ∧
      (approximationFunctor B S hS (Over.forget Xo)
        (Functor.IsFiberedInGroupoids.over_forget Xo)).Faithful :=
  ⟨full_approximationFunctor_representable Xo,
    faithful_approximationFunctor B S hS (Over.forget Xo)
      (Functor.IsFiberedInGroupoids.over_forget Xo)⟩

end Representable

end Deformation.Artin

end
