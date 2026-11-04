module

public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.Coproduct

/-!
# Annihilation confines the support, and step 4 of [Stacks, Tag 01YF] from [Stacks, Tag 01YE]

`Stacks.AlgebraicGeometry.IrreducibleDevissage.HasKilledIdealCoproductSubIn` is **stronger** than
the conclusion of [Stacks, Tag 01YE] in two ways, so that the reduction of step 4 of the proof of
[Stacks, Tag 01YF] to it is not lossless: it asks for the support of the cokernel rather than an
open on which the monomorphism is invertible, and it asks for coherence of `i_* I` rather than of
`i_*(I ^ {⊕ r})`. **Both are discharged here**, so step 4 — in the confined form
[Stacks, Tag 01YH] consumes — follows from the conclusion of [Stacks, Tag 01YE] with nothing
added.

The first is `supp_subset_of_smul_top_eq_bot`: a quasi-coherent module annihilated by the ideal
sheaf of a closed set is supported inside that set. With it,
`Stacks.AlgebraicGeometry.IrreducibleDevissage`'s
`supp_cokernel_ssubset_of_isIso_restrict_of_supp_subset` runs with no leftover hypothesis.

The second is `isCoherent_pushforward_of_isCoherent_pushforward_coproduct`: for `r ≥ 1` the
direct image `i_* I` is a direct summand of `i_*(I ^ {⊕ r})`, hence a finite-type subsheaf of a
coherent sheaf, hence coherent. At `r = 0` the sub is zero and the module itself is supported
strictly inside the closed set, which is a one-step filtration on its own, so no coherence of
`i_* I` is needed there either.

## Main definitions

* `Stacks.AlgebraicGeometry.ConfinedDevissage.HasKilledIdealGenericIsoSubIn`: **the conclusion of
  [Stacks, Tag 01YE], confined** — a coherent quasi-coherent module annihilated by the ideal
  sheaf of an irreducible closed set `Z` receives a monomorphism from the direct image, along a
  closed immersion from an integral scheme with range inside `Z`, of a finite coproduct of copies
  of a quasi-coherent ideal sheaf, and the monomorphism becomes invertible on an open
  neighbourhood of some point of `Z`.

## Main results

* `Stacks.AlgebraicGeometry.ConfinedDevissage.supp_subset_of_smul_top_eq_bot`: **a quasi-coherent
  module annihilated affine-locally by the ideal sheaf of a closed set is supported inside that
  set.**
* `Stacks.AlgebraicGeometry.ConfinedDevissage.supp_cokernel_ssubset_of_killed`: the full conversion
  from the shape [Stacks, Tag 01YE] delivers — an open on which the inclusion is invertible — to
  the strict support condition, with no hypothesis left over.
* `ConfinedDevissage.isCoherent_pushforward_of_isCoherent_pushforward_coproduct`:
  **coherence of `i_* I` from coherence of `i_*(I ^ {⊕ r})` for `r ≥ 1`.**
* `ConfinedDevissage.hasKilledIdealDevissageIn_of_hasKilledIdealGenericIsoSubIn`:
  **step 4 of the proof of [Stacks, Tag 01YF], confined, from the conclusion of
  [Stacks, Tag 01YE] alone.**
* `ConfinedDevissage.property_of_irreducible_support_of_topIdeals_of_genericIsoSub`:
  **the conclusion of [Stacks, Tag 01YH] from its hypotheses together with exactly two further
  assumptions**, `HasKilledIdealGenericIsoSubIn X` and the top-stratum ideals `htop`.

## Implementation notes

**The support containment needs only the affine-open dictionary.** For a point `x` outside
`Z`, pick any affine open `V` around it; `Stacks.AlgebraicGeometry.IdealPowerSmul.closedIdeal` is
the vanishing ideal of `Z`, so `x ∉ Z` produces by
`Stacks.AlgebraicGeometry.IdealPowerSmul.mem_closed_iff_vanishingIdeal_le` a section `f` of that
ideal over `V` outside the prime of `x`; annihilation kills `f • m` for every section `m` of the
module over `V`; and `AlgebraicGeometry.Scheme.Modules.mem_support_sections_iff_mem_supp` turns
that into `x ∉ supp`. `Stacks.AlgebraicGeometry.IdealPowerSmul.notMem_supp_of_smul_eq_zero` is
stated for a quasi-coherent *submodule* of a module; `notMem_supp_of_forall_smul_eq_zero` below is
the same two-line argument for the module itself, which is the form needed.

**The hypothesis `hsplit` of
`Stacks.AlgebraicGeometry.ConfinedDevissage.property_of_supp_subset` is a theorem.** It is
`Stacks.AlgebraicGeometry.IdealPowerSmul.hasSupportSplitting`, which holds for every Noetherian
scheme. The headline theorem below therefore carries neither `hsplit` nor `hirr`.

**What is left of [Stacks, Tag 01YH].** Exactly two assumptions:
`HasKilledIdealGenericIsoSubIn X`, which is the conclusion of [Stacks, Tag 01YE] with the
annihilation hypothesis read affine-locally — a *weaker* hypothesis than that of
[Stacks, Tag 01YE], which asks only that the stalk at the generic point be killed by the maximal
ideal, so [Stacks, Tag 01YE] delivers it as soon as affine-local annihilation is known to imply
that stalk condition — and `htop`, the top-stratum ideals. `htop` is where the length-one
condition of hypothesis (3) of [Stacks, Tag 01YH] and the intersection argument of the last
paragraph of its proof are consumed.

**No `@[stacks]` attribute is attached.** Every theorem below either carries
`HasKilledIdealGenericIsoSubIn X` or `htop`, which Stacks 01YH does not have, or is a fragment of
a Stacks statement.

## References

* [Stacks Project, Tag 01YE](https://stacks.math.columbia.edu/tag/01YE)
* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
* [Stacks Project, Tag 01YG](https://stacks.math.columbia.edu/tag/01YG)
* [Stacks Project, Tag 01YH](https://stacks.math.columbia.edu/tag/01YH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SheafOfModules TopologicalSpace
open Stacks.AlgebraicGeometry.CoherentDevissage
open Stacks.AlgebraicGeometry.DevissageBounded
open Stacks.AlgebraicGeometry.IrreducibleDevissage

universe u

namespace Stacks.AlgebraicGeometry.ConfinedDevissage

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

attribute [local instance] Stacks.AlgebraicGeometry.IrreducibleDevissage.hasFiniteBiproducts_modules

variable {X : Scheme.{u}}

/-! ### Annihilation by the ideal of a closed set confines the support -/

/-- **A point of an affine open at which a scalar outside the corresponding prime annihilates
every section is outside the support.** This is
`Stacks.AlgebraicGeometry.IdealPowerSmul.notMem_supp_of_smul_eq_zero` for the module itself rather
than for a quasi-coherent submodule of a module. -/
theorem notMem_supp_of_forall_smul_eq_zero (Q : X.Modules) (hQ : Q.IsQuasicoherent)
    (U : X.affineOpens) (x : X) (hx : x ∈ U.1) (r : Γ(X, U.1))
    (hr : r ∉ (U.2.primeIdealOf ⟨x, hx⟩).asIdeal)
    (hzero : ∀ m : Γ(Q, U.1), r • m = 0) : x ∉ SheafOfModules.supp Q := by
  have := hQ
  intro hmem
  obtain ⟨m, hm⟩ := Module.mem_support_iff'.mp
    ((Scheme.Modules.mem_support_sections_iff_mem_supp Q U x hx).mpr hmem)
  exact hm r hr (hzero m)

/-- **A quasi-coherent module annihilated affine-locally by the ideal sheaf of a closed set is
supported inside that set.** Neither irreducibility of the closed set nor coherence of the
module is used. -/
theorem supp_subset_of_smul_top_eq_bot (Z : Closeds X) (Q : X.Modules)
    (hQ : Q.IsQuasicoherent)
    (hkill : ∀ U : X.affineOpens, (IdealPowerSmul.closedIdeal Z).ideal U •
      (⊤ : Submodule Γ(X, U.1) Γ(Q, U.1)) = ⊥) :
    SheafOfModules.supp Q ⊆ (Z : Set X) := by
  intro x hx
  by_contra hxZ
  obtain ⟨V, hxV⟩ : ∃ V : X.affineOpens, x ∈ V.1 := by
    obtain ⟨-, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨⟨V, hV⟩, hxV⟩
  obtain ⟨f, hf, hfp⟩ : ∃ f ∈ (IdealPowerSmul.closedIdeal Z).ideal V,
      f ∉ (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal := by
    by_contra hcon
    push Not at hcon
    exact hxZ
      ((IdealPowerSmul.mem_closed_iff_vanishingIdeal_le Z V x hxV).mpr fun g hg => hcon g hg)
  refine notMem_supp_of_forall_smul_eq_zero Q hQ V x hxV f hfp (fun m => ?_) hx
  have hmem : f • m ∈ (IdealPowerSmul.closedIdeal Z).ideal V •
      (⊤ : Submodule Γ(X, V.1) Γ(Q, V.1)) := Submodule.smul_mem_smul hf Submodule.mem_top
  rw [hkill V, Submodule.mem_bot] at hmem
  exact hmem

/-- **The cokernel of a generically invertible morphism into a module annihilated by the ideal
sheaf of `Z` is supported strictly inside `Z`.** This is the conversion performed by
`Stacks.AlgebraicGeometry.IrreducibleDevissage`'s
`supp_cokernel_ssubset_of_isIso_restrict_of_supp_subset`, with its remaining hypothesis
discharged by `supp_subset_of_smul_top_eq_bot`: nothing is
assumed beyond what [Stacks, Tag 01YE] delivers and what step 4 of the proof of
[Stacks, Tag 01YF] already carries. -/
theorem supp_cokernel_ssubset_of_killed (Z : Closeds X) (Q : X.Modules)
    (hQ : Q.IsQuasicoherent)
    (hkill : ∀ U : X.affineOpens, (IdealPowerSmul.closedIdeal Z).ideal U •
      (⊤ : Submodule Γ(X, U.1) Γ(Q, U.1)) = ⊥)
    {A : X.Modules} (φ : A ⟶ Q) (V : X.Opens)
    (hiso : IsIso ((Scheme.Modules.restrictFunctor V.ι).map φ))
    (ξ : X) (hξV : ξ ∈ V) (hξ : ξ ∈ (Z : Set X)) :
    SheafOfModules.supp (cokernel φ) ⊂ (Z : Set X) :=
  supp_cokernel_ssubset_of_isIso_restrict_of_supp_subset φ V hiso ξ hξV hξ
    (supp_subset_of_smul_top_eq_bot Z Q hQ hkill)

/-! ### Coherence of one factor of a direct image of a coproduct -/

/-- **The direct image of a module is coherent as soon as the direct image of a nonempty finite
coproduct of copies of it is.** For `r ≥ 1` the direct image `i_* M` is a direct summand of
`i_*(M ^ {⊕ r})`: the biproduct projection onto a factor is a split epimorphism, so `i_* M` is of
finite type, and the inclusion of that factor is a monomorphism from a finite-type sheaf into a
coherent one, which is [Stacks, Tag 01BY] (1). -/
theorem isCoherent_pushforward_of_isCoherent_pushforward_coproduct {W : Scheme.{u}} (i : W ⟶ X)
    (M : W.Modules) (r : ℕ) (hr : 0 < r)
    (h : ((Scheme.Modules.pushforward i).obj (∐ fun _ : Fin r => M)).IsCoherent) :
    ((Scheme.Modules.pushforward i).obj M).IsCoherent := by
  have hbc : (⨁ fun _ : Fin r => (Scheme.Modules.pushforward i).obj M).IsCoherent :=
    isCoherent_of_iso' (pushforwardCoproductConstIso i M r).symm h
  have : Epi (C := SheafOfModules.{u} X.ringCatSheaf)
      (biproduct.π (fun _ : Fin r => (Scheme.Modules.pushforward i).obj M) ⟨0, hr⟩) :=
    inferInstanceAs (Epi
      (biproduct.π (fun _ : Fin r => (Scheme.Modules.pushforward i).obj M) ⟨0, hr⟩))
  have : Mono (C := SheafOfModules.{u} X.ringCatSheaf)
      (biproduct.ι (fun _ : Fin r => (Scheme.Modules.pushforward i).obj M) ⟨0, hr⟩) :=
    inferInstanceAs (Mono
      (biproduct.ι (fun _ : Fin r => (Scheme.Modules.pushforward i).obj M) ⟨0, hr⟩))
  have : ((Scheme.Modules.pushforward i).obj M).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_epi (R := X.ringCatSheaf)
      (biproduct.π (fun _ : Fin r => (Scheme.Modules.pushforward i).obj M) ⟨0, hr⟩)
      hbc.isFiniteType
  exact AlgebraicGeometry.CoherentAbelian.isCoherent_of_mono (R := X.ringCatSheaf)
    (hM := hbc) (biproduct.ι (fun _ : Fin r => (Scheme.Modules.pushforward i).obj M) ⟨0, hr⟩)

/-! ### Step 4 of [Stacks, Tag 01YF], confined, from [Stacks, Tag 01YE] -/

/-- **The conclusion of [Stacks, Tag 01YE], confined to `Z`.** A coherent quasi-coherent module
`Q` annihilated by the ideal sheaf of an irreducible closed set `Z` receives a monomorphism from
the direct image, along a closed immersion from an integral scheme whose range lies in `Z`, of a
finite coproduct of copies of a quasi-coherent ideal sheaf, and that monomorphism becomes
invertible on an open neighbourhood of some point of `Z`.

This is the conclusion of [Stacks, Tag 01YE] verbatim, except that the annihilation hypothesis
is read affine-locally rather than as a condition on the stalk at the generic point. Affine-local
annihilation by the ideal sheaf of `Z` is the stronger condition on `Q` — it implies that the
stalk at the generic point of `Z` is killed by the maximal ideal there — so this asks for the
conclusion at fewer modules than [Stacks, Tag 01YE] does, and [Stacks, Tag 01YE] delivers it as
soon as that one implication is available. The point of `Z` is not required to be the generic
point: the conversion below needs only that the open neighbourhood meets `Z`. -/
def HasKilledIdealGenericIsoSubIn (X : Scheme.{u}) : Prop :=
  ∀ Z : Closeds X, IsIrreducible (Z : Set X) →
    ∀ Q : X.Modules, Q.IsQuasicoherent → Q.IsCoherent →
      (∀ U : X.affineOpens, (IdealPowerSmul.closedIdeal Z).ideal U •
          (⊤ : Submodule Γ(X, U.1) Γ(Q, U.1)) = ⊥) →
      ∃ (W : Scheme.{u}) (i : W ⟶ X) (_ : IsClosedImmersion i) (_ : IsIntegral W) (r : ℕ)
        (I : (SheafOfModules.unit W.ringCatSheaf).Submodule),
        I.toSheafOfModules.IsQuasicoherent ∧
          Set.range i.base ⊆ (Z : Set X) ∧
          ((Scheme.Modules.pushforward i).obj
            (∐ fun _ : Fin r => I.toSheafOfModules)).IsCoherent ∧
          ∃ φ : (Scheme.Modules.pushforward i).obj (∐ fun _ : Fin r => I.toSheafOfModules) ⟶ Q,
            Mono φ ∧ ∃ (V : X.Opens) (ξ : X), ξ ∈ V ∧ ξ ∈ (Z : Set X) ∧
              IsIso ((Scheme.Modules.restrictFunctor V.ι).map φ)

/-- **Step 4 of the proof of [Stacks, Tag 01YF], confined, from the conclusion of
[Stacks, Tag 01YE] alone.** Nothing is added to what [Stacks, Tag 01YE] produces: the support of
the cokernel comes from `supp_cokernel_ssubset_of_killed`, the filtration of the sub by its `r`
factors from
`Stacks.AlgebraicGeometry.IrreducibleDevissage.hasDevissageWith_pushforward_coproduct_const`, and
the coherence that filtration needs from
`isCoherent_pushforward_of_isCoherent_pushforward_coproduct`.

At multiplicity `r = 0` the sub is a zero module, so the quotient map is an isomorphism and `Q`
itself is supported strictly inside `Z`; that is a one-step filtration on the right disjunct, and
no ideal sheaf is used at all. -/
theorem hasKilledIdealDevissageIn_of_hasKilledIdealGenericIsoSubIn
    (h : HasKilledIdealGenericIsoSubIn X) : HasKilledIdealDevissageIn X := by
  intro Z hZirr Q hQq hQc hkill
  obtain ⟨W, i, hi, hW, r, I, hIq, hrange, hAc, φ, hmono, V, ξ, hξV, hξZ, hiso⟩ :=
    h Z hZirr Q hQq hQc hkill
  have hsupp : SheafOfModules.supp (cokernel φ) ⊂ (Z : Set X) :=
    supp_cokernel_ssubset_of_killed Z Q hQq hkill φ V hiso ξ hξV hξZ
  have hCc : (cokernel φ).IsCoherent := isCoherent_cokernel' φ hAc hQc
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have hcz : IsZero (∐ fun _ : Fin 0 => I.toSheafOfModules) :=
      (IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ fun j => isEmptyElim j)
    have hAz : IsZero ((Scheme.Modules.pushforward i).obj
        (∐ fun _ : Fin 0 => I.toSheafOfModules)) :=
      Functor.map_isZero _ hcz
    have hφ0 : φ = 0 := hAz.eq_of_src φ 0
    have hπ : IsIso (cokernel.π φ) := by
      rw [hφ0, ← cokernelZeroIsoTarget_inv]
      infer_instance
    have hQsupp : SheafOfModules.supp Q ⊂ (Z : Set X) := by
      rw [supp_eq_of_iso (asIso (cokernel.π φ))]
      exact hsupp
    exact hasDevissageWith_single isIdealPushforwardIn_or_supp_ssubset_of_iso hQc
      (Or.inr hQsupp)
  · have hIc : ((Scheme.Modules.pushforward i).obj I.toSheafOfModules).IsCoherent :=
      isCoherent_pushforward_of_isCoherent_pushforward_coproduct i I.toSheafOfModules r hr hAc
    refine hasDevissageWith_trans' isIdealPushforwardIn_or_supp_ssubset_of_iso φ hQc ?_ ?_
    · exact hasDevissageWith_pushforward_coproduct_const
        isIdealPushforwardIn_or_supp_ssubset_of_iso i I.toSheafOfModules hIc
        (Or.inl (isIdealPushforwardIn_pushforward i hi hW I hIq hrange)) r
    · exact hasDevissageWith_single isIdealPushforwardIn_or_supp_ssubset_of_iso hCc
        (Or.inr hsupp)

/-- **The relativized irreducible step of [Stacks, Tag 01YF] from the conclusion of
[Stacks, Tag 01YE] alone.** Step 3 is `hasDevissageWith_of_killed`, step 4 is the theorem above. -/
theorem hasIrreducibleDevissageIn_of_hasKilledIdealGenericIsoSubIn [IsNoetherian X]
    (h : HasKilledIdealGenericIsoSubIn X) : HasIrreducibleDevissageIn X :=
  hasIrreducibleDevissageIn_of_hasKilledIdealDevissageIn
    (hasKilledIdealDevissageIn_of_hasKilledIdealGenericIsoSubIn h)

/-! ### [Stacks, Tag 01YH] on [Stacks, Tag 01YE] and the top-stratum ideals -/

variable (P : X.Modules → Prop)

/-- **[Stacks, Tag 01YH] on the conclusion of [Stacks, Tag 01YE] and the top-stratum ideals.**
Its conclusion — `P` on every coherent module supported inside `Z₀` — from its two-out-of-three
hypothesis `hexact`, its hypothesis `hproper` on integral closed subschemes strictly inside `Z₀`,
a single coherent module `G` satisfying `P` (all that is used of its hypothesis (3)), and exactly
two further assumptions:

* `hgeneric`, the conclusion of [Stacks, Tag 01YE] in the confined form step 4 consumes, and
* `htop`, `P` on the direct image of every quasi-coherent ideal sheaf on every integral closed
  subscheme whose range is **all** of `Z₀`.

Compared with
`Stacks.AlgebraicGeometry.ConfinedDevissage.property_of_irreducible_support_of_topIdeals`, the
support splitting of [Stacks, Tag 01YD] has been removed — it is
`Stacks.AlgebraicGeometry.IdealPowerSmul.hasSupportSplitting`, which holds for every Noetherian
scheme — and the irreducible step of [Stacks, Tag 01YF] has been replaced by the single statement
[Stacks, Tag 01YE] produces.

`htop` is where the length-one condition of hypothesis (3) of [Stacks, Tag 01YH] and the
intersection argument of the last paragraph of its proof are consumed. -/
theorem property_of_irreducible_support_of_topIdeals_of_genericIsoSub [IsNoetherian X]
    (hgeneric : HasKilledIdealGenericIsoSubIn X)
    {Z₀ : Set X}
    (hexact : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
      ((P S.X₁ ∧ P S.X₂ → P S.X₃) ∧ (P S.X₁ ∧ P S.X₃ → P S.X₂) ∧
        (P S.X₂ ∧ P S.X₃ → P S.X₁)))
    (hproper : ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
      [IsIntegral Z], Set.range i.base ⊂ Z₀ →
      ∀ (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
        [I.toSheafOfModules.IsQuasicoherent],
        P ((Scheme.Modules.pushforward i).obj I.toSheafOfModules))
    (htop : ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
      [IsIntegral Z], Set.range i.base = Z₀ →
      ∀ (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
        [I.toSheafOfModules.IsQuasicoherent],
        P ((Scheme.Modules.pushforward i).obj I.toSheafOfModules))
    (G : X.Modules) (hG : G.IsCoherent) (hPG : P G) :
    ∀ F : X.Modules, F.IsCoherent → SheafOfModules.supp F ⊆ Z₀ → P F :=
  property_of_irreducible_support_of_topIdeals P (IdealPowerSmul.hasSupportSplitting X)
    (hasIrreducibleDevissageIn_of_hasKilledIdealGenericIsoSubIn hgeneric)
    hexact hproper htop G hG hPG

end Stacks.AlgebraicGeometry.ConfinedDevissage

end
