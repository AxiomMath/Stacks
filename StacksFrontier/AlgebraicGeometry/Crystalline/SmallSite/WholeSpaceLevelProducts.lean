module

public import Mathlib.RingTheory.DividedPowers.Padic
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.AffineSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.LevelFamilyFinality
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineCosimplicialSystem
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineGlobalConnected
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineGlobalEquivalence
public import StacksFrontier.RingTheory.AdicCompletion.LiftToComplete

/-!
# The levels of the system of [Stacks, Tag 07JN] are products for affine test objects

Fix a global crystalline situation `(p, (S, I, γ), X)` with `X` and `S` affine and `p` nilpotent
on `Γ(X, ⊤)`, and let `T(n)_e` be the levels of the system
`Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceSystem`: the transport of the finite
level `D(n)/(p)^{N + e}` of the completed envelope `D(n)` of the `(n + 1)`-fold tensor power of
the tautological presentation of `Γ(X, ⊤)`.  This file proves, for every object `A` of `Cris(X/S)`
whose thickened and ambient schemes are affine (the open `U ⊆ X` of `A` is arbitrary):

1. `A` maps to `T(0)_e` for every large `e` — [Stacks, Tag 07HP] for the affine objects of
   `Cris(X/S)`, and not only for those over the whole of `X`;
2. the `n + 1` vertex maps `T(n)_e ⟶ T(0)_e` induce a bijection
   `Hom(A, T(n)_e) ≅ Hom(A, T(0)_e)^{n + 1}`: the level `T(n)_e` is the product of `n + 1` copies
   of `T(0)_e` as seen from the affine objects.

## The two steps

**Geometry.**  A morphism `A ⟶ T` of `Cris(X/S)` into an object `T` of the chaotic subsite `𝒞` is
the same thing as a morphism of divided power thickenings of `Γ(X, ⊤)/Γ(S, ⊤)` between the rings of
global sections, in the opposite direction: this is
`Crystalline.GlobalCrystallineSituation.homOfAffineSections` of
`StacksFrontier/AlgebraicGeometry/Crystalline/BigSite/AffineSections.lean`, read through the counit
of the equivalence `𝒞ᵒᵖ ≌ Cris(Γ(X, ⊤)/Γ(S, ⊤))`.  The object of `CRIS(Γ(X, ⊤)/Γ(S, ⊤))` attached
to `A` lies in the *big* category, since `Γ(X, ⊤) → Γ(U, ⊤)` is not bijective.

**Algebra.**  The finite level `D(n)/(p)^{N + e}` is the coproduct of `n + 1` copies of
`D(0)/(p)^{N + e}` for maps into an *arbitrary* object `B` of the big category
`CRIS(C/A)`, `Crystalline.bijective_levelVertices`.  This is reduced to [Stacks, Tag 07L4],
`Crystalline.completedEnvelope_isCoproduct`, which is about maps into objects of the completed
little category `Cris^∧(C/A)`, through the fibre product `B ×_{B/J} C`
(`Crystalline.DividedPowerThickening.fiberThickening`): it is an object of `Cris^∧(C/A)`, `p` being
nilpotent in it, and a morphism of `CRIS(C/A)` from a finite level `X/(p)^k` of an object `X` of
`Cris^∧(C/A)` to `B` is the same thing as a morphism `X ⟶ B ×_{B/J} C` of `Cris^∧(C/A)`, as soon
as `p^k` vanishes in `B` and in `C`.  The vanishing in `B` is automatic for the maps out of the
levels, `p^k` being zero on the level itself.

## Main definitions

* `Crystalline.prodDividedPowers` — the componentwise divided powers on a product of ideals.
* `Crystalline.DividedPowerThickening.fiberThickening` — the object `B ×_{B/J} C` of
  `Cris^∧(C/A)` attached to an object `B` of `CRIS(C/A)`.
* `Crystalline.DividedPowerThickening.levelToFiber` — the morphism `X ⟶ B ×_{B/J} C` attached to a
  morphism `X/(p)^k ⟶ B`.
* `Crystalline.levelVertex` — the `j`-th vertex `D(0)/(p)^{N + e} ⟶ D(n)/(p)^{N + e}`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.homToLevelSections` — a morphism `A ⟶ T` into
  the transport `T` of an object of `Cris(Γ(X, ⊤)/Γ(S, ⊤))`, read on global sections.
* `Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceVertex` — the `j`-th vertex
  `T(n)_e ⟶ T(0)_e`.

## Main results

* `Crystalline.bijective_levelVertices` — **the finite level `D(n)/(p)^{N + e}` is the coproduct
  of `n + 1` copies of `D(0)/(p)^{N + e}` for maps into any object of `CRIS(C/A)`.**
* `Crystalline.GlobalCrystallineSituation.SmallSite.bijective_homToLevelSections` — morphisms from
  an affine object into a transported object are morphisms of global sections.
* `Crystalline.GlobalCrystallineSituation.SmallSite.exists_forall_le_hom_wholeSpaceLevel` —
  **[Stacks, Tag 07HP] for the affine objects of `Cris(X/S)`**.
* `Crystalline.GlobalCrystallineSituation.SmallSite.bijective_wholeSpaceVertices` — **the level
  `T(n)_e` is the product of `n + 1` copies of `T(0)_e` as seen from the affine objects.**
* `...SmallSite.δ_app_comp_wholeSpaceVertex`, `...SmallSite.map_comp_wholeSpaceVertex` and
  `...SmallSite.σ_app_comp_wholeSpaceVertex` — the faces, the level maps and the degeneracy read
  on the vertices.

## References

* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07L4](https://stacks.math.columbia.edu/tag/07L4)
* [Stacks Project, Tag 07HP](https://stacks.math.columbia.edu/tag/07HP)
* [Stacks Project, Tag 07JK](https://stacks.math.columbia.edu/tag/07JK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Simplicial

universe u v

noncomputable section

namespace Crystalline

/-! ### Divided powers on a product of ideals -/

section ProdDividedPowers

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B] {I : Ideal A} {J : Ideal B}

/-- The componentwise divided power operations on a product of two rings, supported on the
product of the two divided power ideals. -/
def prodDpow (hI : DividedPowers I) (hJ : DividedPowers J) (n : ℕ) (x : A × B) : A × B :=
  open scoped Classical in
  if x ∈ I.prod J then (hI.dpow n x.1, hJ.dpow n x.2) else 0

/-- On the product ideal, `prodDpow` is computed componentwise. -/
theorem prodDpow_apply (hI : DividedPowers I) (hJ : DividedPowers J) (n : ℕ) {x : A × B}
    (hx : x ∈ I.prod J) : prodDpow hI hJ n x = (hI.dpow n x.1, hJ.dpow n x.2) := by
  simp [prodDpow, hx]

/-- **The componentwise divided powers on the product `I × J` of two divided power ideals.** -/
def prodDividedPowers (hI : DividedPowers I) (hJ : DividedPowers J) :
    DividedPowers (I.prod J) where
  dpow := prodDpow hI hJ
  dpow_null hx := by simp [prodDpow, hx]
  dpow_zero hx := by
    rw [prodDpow_apply _ _ _ hx]
    exact Prod.ext (hI.dpow_zero hx.1) (hJ.dpow_zero hx.2)
  dpow_one hx := by
    rw [prodDpow_apply _ _ _ hx]
    exact Prod.ext (hI.dpow_one hx.1) (hJ.dpow_one hx.2)
  dpow_mem hn hx := by
    rw [prodDpow_apply _ _ _ hx]
    exact ⟨hI.dpow_mem hn hx.1, hJ.dpow_mem hn hx.2⟩
  dpow_add {n x y} hx hy := by
    rw [prodDpow_apply _ _ _ ((I.prod J).add_mem hx hy)]
    simp only [prodDpow_apply _ _ _ hx, prodDpow_apply _ _ _ hy]
    exact Prod.ext (by simpa [Prod.fst_sum] using hI.dpow_add hx.1 hy.1)
      (by simpa [Prod.snd_sum] using hJ.dpow_add hx.2 hy.2)
  dpow_mul {n a x} hx := by
    rw [prodDpow_apply _ _ _ ((I.prod J).mul_mem_left a hx), prodDpow_apply _ _ _ hx]
    exact Prod.ext (hI.dpow_mul hx.1) (hJ.dpow_mul hx.2)
  mul_dpow {m n x} hx := by
    simp only [prodDpow_apply _ _ _ hx]
    exact Prod.ext (hI.mul_dpow hx.1) (hJ.mul_dpow hx.2)
  dpow_comp {m n x} hn hx := by
    have hnx : prodDpow hI hJ n x ∈ I.prod J := by
      rw [prodDpow_apply _ _ _ hx]
      exact ⟨hI.dpow_mem hn hx.1, hJ.dpow_mem hn hx.2⟩
    rw [prodDpow_apply _ _ _ hnx, prodDpow_apply _ _ _ hx, prodDpow_apply _ _ _ hx]
    exact Prod.ext (hI.dpow_comp hn hx.1) (hJ.dpow_comp hn hx.2)

/-- The divided powers on a product ideal are computed componentwise. -/
theorem prodDividedPowers_dpow (hI : DividedPowers I) (hJ : DividedPowers J) (n : ℕ)
    {x : A × B} (hx : x ∈ I.prod J) :
    (prodDividedPowers hI hJ).dpow n x = (hI.dpow n x.1, hJ.dpow n x.2) :=
  prodDpow_apply hI hJ n hx

end ProdDividedPowers

/-- The trivial divided powers on the zero ideal take the value `1` at `(0, 0)`. -/
theorem dividedPowersBot_dpow_zero_zero (C : Type u) [CommRing C] :
    (_root_.dividedPowersBot C).dpow 0 (0 : C) = 1 :=
  (_root_.dividedPowersBot C).dpow_zero (Ideal.zero_mem _)

/-- The trivial divided powers on the zero ideal vanish in positive degree. -/
theorem dividedPowersBot_dpow_zero_of_ne (C : Type u) [CommRing C] {n : ℕ} (hn : n ≠ 0) :
    (_root_.dividedPowersBot C).dpow n (0 : C) = 0 :=
  Ideal.mem_bot.mp ((_root_.dividedPowersBot C).dpow_mem hn (Ideal.zero_mem _))

/-- Morphisms of divided power rings are determined by their underlying functions. -/
theorem dpRingHom_ext {R R' : DividedPowerRing.{u}} {f g : R ⟶ R'}
    (h : ∀ x, f.toRingHom x = g.toRingHom x) : f = g :=
  DividedPowers.DPMorphism.ext (funext h)

/-- A map is bijective as soon as it is conjugate, through bijections, to a bijection. -/
theorem bijective_of_comm {α β γ δ : Sort*} {m : α → β} {F₁ : α → γ} {F₂ : β → δ}
    {m' : γ → δ} (h : ∀ a, F₂ (m a) = m' (F₁ a)) (hF₂ : Function.Bijective F₂)
    (hm' : Function.Bijective m') (hF₁ : Function.Bijective F₁) : Function.Bijective m := by
  refine (hF₂.of_comp_iff' m).mp ?_
  rw [show F₂ ∘ m = m' ∘ F₁ from funext h]
  exact hm'.comp hF₁

/-! ### The fibre product `B ×_{B/J} C` of an object of `CRIS(C/A)` -/

variable {s : AffineCrystallineSituation.{u, u}}

namespace DividedPowerThickening

variable (B : DividedPowerThickening.{u, u, u} s)

/-- **The fibre product `B ×_{B/J} C`** of an object `(B, J, δ)` of `CRIS(C/A)`, as a subring of
`B × C`: the pairs whose two images in `B/J` agree. -/
def fiberSubring : Subring (B.ring × s.C) :=
  ((Ideal.Quotient.mk B.ring.ideal).comp (RingHom.fst B.ring s.C)).eqLocus
    (B.toQuotient.comp (RingHom.snd B.ring s.C))

/-- Membership in the fibre product: the two images in `B/J` agree. -/
theorem mem_fiberSubring (x : B.ring × s.C) :
    x ∈ B.fiberSubring ↔ Ideal.Quotient.mk B.ring.ideal x.1 = B.toQuotient x.2 :=
  Iff.rfl

/-- The first projection `B ×_{B/J} C → B`. -/
def fiberFst : B.fiberSubring →+* B.ring :=
  (RingHom.fst B.ring s.C).comp B.fiberSubring.subtype

/-- The second projection `B ×_{B/J} C → C`. -/
def fiberSnd : B.fiberSubring →+* s.C :=
  (RingHom.snd B.ring s.C).comp B.fiberSubring.subtype

/-- The two projections of the fibre product agree in `B/J`. -/
theorem mk_fiberFst (x : B.fiberSubring) :
    Ideal.Quotient.mk B.ring.ideal (B.fiberFst x) = B.toQuotient (B.fiberSnd x) :=
  x.2

/-- The second projection `B ×_{B/J} C → C` is surjective, `B → B/J` being so. -/
theorem fiberSnd_surjective : Function.Surjective B.fiberSnd := fun c => by
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (B.toQuotient c)
  exact ⟨⟨(b, c), hb⟩, rfl⟩

/-- The divided power ideal `J ×_{B/J} 0` of the fibre product: the kernel of the second
projection. -/
abbrev fiberIdeal : Ideal B.fiberSubring :=
  RingHom.ker B.fiberSnd

/-- The first component of an element of `J ×_{B/J} 0` lies in `J`. -/
theorem fiberFst_mem_of_mem {x : B.fiberSubring} (hx : x ∈ B.fiberIdeal) :
    B.fiberFst x ∈ B.ring.ideal := by
  have h := B.mk_fiberFst x
  rw [show B.fiberSnd x = 0 from hx, map_zero] at h
  exact Ideal.Quotient.eq_zero_iff_mem.mp h

/-- The ideal `J ×_{B/J} 0`, read in `B × C`, is `J × 0`. -/
theorem map_subtype_fiberIdeal :
    B.fiberIdeal.map B.fiberSubring.subtype = B.ring.ideal.prod ⊥ := by
  apply le_antisymm
  · exact Ideal.map_le_iff_le_comap.mpr fun _ hx => ⟨B.fiberFst_mem_of_mem hx, Ideal.mem_bot.mpr hx⟩
  · rintro ⟨b, c⟩ ⟨hb, hc⟩
    obtain rfl : c = 0 := Ideal.mem_bot.mp hc
    have hmem : ((b, 0) : B.ring × s.C) ∈ B.fiberSubring := by
      rw [mem_fiberSubring, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hb
    exact Ideal.mem_map_of_mem B.fiberSubring.subtype
      (x := (⟨(b, 0), hmem⟩ : B.fiberSubring)) (RingHom.mem_ker.mpr rfl)

/-- The componentwise divided powers of an element of `J ×_{B/J} 0` lie in the fibre
product, and in `J ×_{B/J} 0` in positive degree. -/
theorem exists_fiber_dpow (n : ℕ) {x : B.fiberSubring} (hx : x ∈ B.fiberIdeal) :
    ∃ (y : B.fiberSubring) (_ : n ≠ 0 → y ∈ B.fiberIdeal),
      B.fiberSubring.subtype y =
        (prodDividedPowers B.ring.dividedPowers (_root_.dividedPowersBot s.C)).dpow n
          (B.fiberSubring.subtype x) := by
  have hx' : B.fiberSubring.subtype x ∈ B.ring.ideal.prod ⊥ :=
    B.map_subtype_fiberIdeal ▸ Ideal.mem_map_of_mem _ hx
  rw [prodDividedPowers_dpow _ _ _ hx']
  have h1 : (B.fiberSubring.subtype x).1 ∈ B.ring.ideal := B.fiberFst_mem_of_mem hx
  rw [show (B.fiberSubring.subtype x).2 = 0 from hx]
  rcases eq_or_ne n 0 with rfl | hn
  · refine ⟨1, fun h => absurd rfl h, ?_⟩
    rw [map_one, B.ring.dividedPowers.dpow_zero h1, dividedPowersBot_dpow_zero_zero]
    rfl
  · have hmem : ((B.ring.dividedPowers.dpow n (B.fiberSubring.subtype x).1, (0 : s.C)) :
        B.ring × s.C) ∈ B.fiberSubring := by
      rw [mem_fiberSubring, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (B.ring.dividedPowers.dpow_mem hn h1)
    refine ⟨⟨_, hmem⟩, fun _ => RingHom.mem_ker.mpr rfl, ?_⟩
    rw [dividedPowersBot_dpow_zero_of_ne _ hn]
    rfl

/-- The divided powers on the ideal `J ×_{B/J} 0` of the fibre product, induced from those of
`J` and the trivial ones on `0 ⊆ C`. -/
def fiberDividedPowers : DividedPowers B.fiberIdeal :=
  DividedPowers.ofInjective B.fiberIdeal (B.ring.ideal.prod ⊥) B.fiberSubring.subtype
    Subtype.val_injective
    (prodDividedPowers B.ring.dividedPowers (_root_.dividedPowersBot s.C))
    B.map_subtype_fiberIdeal B.exists_fiber_dpow

/-- The divided powers of the fibre product are computed componentwise. -/
theorem coe_fiberDividedPowers_dpow (n : ℕ) {x : B.fiberSubring} (hx : x ∈ B.fiberIdeal) :
    ((B.fiberDividedPowers.dpow n x : B.fiberSubring) : B.ring × s.C) =
      (B.ring.dividedPowers.dpow n (x : B.ring × s.C).1,
        (_root_.dividedPowersBot s.C).dpow n (x : B.ring × s.C).2) := by
  have hx' : B.fiberSubring.subtype x ∈ B.ring.ideal.prod ⊥ :=
    B.map_subtype_fiberIdeal ▸ Ideal.mem_map_of_mem _ hx
  rw [show B.fiberDividedPowers.dpow n x = Exists.choose (B.exists_fiber_dpow n hx) from
    dite_eq_left hx]
  exact (Exists.choose_spec (B.exists_fiber_dpow n hx)).2.trans (prodDividedPowers_dpow _ _ _ hx')

/-- The fibre product `B ×_{B/J} C` as a divided power ring. -/
abbrev fiberDPRing : DividedPowerRing.{u} :=
  ⟨B.fiberSubring, B.fiberIdeal, B.fiberDividedPowers⟩

/-- **The universal property of the fibre product**, for divided power rings: a morphism into
`B` and a ring map into `C` killing the divided power ideal, agreeing in `B/J`, define a morphism
into `B ×_{B/J} C`. -/
def fiberLift (R : DividedPowerRing.{u}) (φ : R ⟶ B.ring) (ψ : R →+* s.C)
    (hψ : ∀ x ∈ R.ideal, ψ x = 0)
    (hφψ : ∀ x, Ideal.Quotient.mk B.ring.ideal (φ.toRingHom x) = B.toQuotient (ψ x)) :
    R ⟶ B.fiberDPRing :=
  DividedPowers.DPMorphism.mk' (f := (φ.toRingHom.prod ψ).codRestrict B.fiberSubring hφψ)
    ⟨Ideal.map_le_iff_le_comap.mpr fun x hx => Ideal.mem_comap.mpr (RingHom.mem_ker.mpr (hψ x hx)),
      by
      intro n x hx
      have hmem : (φ.toRingHom.prod ψ).codRestrict B.fiberSubring hφψ x ∈ B.fiberIdeal :=
        RingHom.mem_ker.mpr (hψ x hx)
      apply Subtype.ext
      rw [B.coe_fiberDividedPowers_dpow n hmem]
      refine Prod.ext (φ.dpow_comp x hx) ?_
      change (_root_.dividedPowersBot s.C).dpow n (ψ x) = ψ (R.dividedPowers.dpow n x)
      rw [hψ x hx]
      rcases eq_or_ne n 0 with rfl | hn
      · rw [R.dividedPowers.dpow_zero hx, map_one, dividedPowersBot_dpow_zero_zero]
      · rw [hψ _ (R.dividedPowers.dpow_mem hn hx), dividedPowersBot_dpow_zero_of_ne _ hn]⟩

/-- The components of `fiberLift` are the two given maps. -/
@[simp]
theorem coe_fiberLift (R : DividedPowerRing.{u}) (φ : R ⟶ B.ring) (ψ : R →+* s.C)
    (hψ : ∀ x ∈ R.ideal, ψ x = 0)
    (hφψ : ∀ x, Ideal.Quotient.mk B.ring.ideal (φ.toRingHom x) = B.toQuotient (ψ x)) (x : R) :
    ((B.fiberLift R φ ψ hψ hφψ x : B.fiberSubring) : B.ring × s.C) = (φ.toRingHom x, ψ x) :=
  rfl

/-- The first projection `B ×_{B/J} C → B` as a morphism of divided power rings. -/
def fiberFstDP : B.fiberDPRing ⟶ B.ring :=
  DividedPowers.DPMorphism.mk' (f := B.fiberFst)
    ⟨Ideal.map_le_iff_le_comap.mpr fun _ hx => B.fiberFst_mem_of_mem hx,
      fun {n} _ hx => (congrArg Prod.fst (B.coe_fiberDividedPowers_dpow n hx)).symm⟩

/-- The quotient of the fibre product by its divided power ideal is `C`. -/
def fiberQuotientEquiv : (B.fiberDPRing ⧸ B.fiberDPRing.ideal) ≃+* s.C :=
  RingHom.quotientKerEquivOfSurjective B.fiberSnd_surjective

/-- The identification of the quotient of the fibre product with `C` is the second
projection. -/
@[simp]
theorem fiberQuotientEquiv_mk (x : B.fiberDPRing) :
    B.fiberQuotientEquiv (Ideal.Quotient.mk B.fiberDPRing.ideal x) = B.fiberSnd x :=
  rfl

/-- The prime is nilpotent in the fibre product, being nilpotent in `B` and in `C`. -/
theorem isNilpotent_prime_fiber : IsNilpotent (s.p : B.fiberDPRing) := by
  obtain ⟨m₁, h₁⟩ := B.prime_nilpotent
  obtain ⟨m₂, h₂⟩ := s.prime_nilpotent
  refine ⟨m₁ + m₂, Subtype.ext (Prod.ext ?_ ?_)⟩
  · simp [pow_add, h₁]
  · simp [pow_add, h₂]

/-- **The fibre product `B ×_{B/J} C` as an object of `Cris^∧(C/A)`.**  The prime is nilpotent in
it, so it is `p`-adically complete, and its quotient by its divided power ideal is `C`. -/
abbrev fiberThickening : CompletedCrystallineThickening.{u, u, u} s where
  ring := B.fiberDPRing
  fromBase := B.fiberLift s.A B.fromBase (algebraMap s.A s.C)
    (fun a ha => by
      have h := Ideal.mem_map_of_mem (algebraMap s.A s.C) ha
      rw [s.ideal_map_eq_bot] at h
      exact Ideal.mem_bot.mp h)
    (fun a => RingHom.congr_fun B.commutes a)
  isComplete := by
    refine IsAdicComplete.of_isNilpotent _ ?_
    obtain ⟨m, hm⟩ := B.isNilpotent_prime_fiber
    exact ⟨m, by
      rw [Ideal.span_singleton_pow, hm]
      simp⟩
  toQuotient := B.fiberQuotientEquiv.symm.toRingHom
  commutes := RingHom.ext fun a => B.fiberQuotientEquiv.injective (by
    rw [RingHom.comp_apply, RingHom.comp_apply, fiberQuotientEquiv_mk]
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply]
    rfl)
  toQuotient_bijective := B.fiberQuotientEquiv.symm.bijective

/-- The structural map `C → (B ×_{B/J} C)/(J ×_{B/J} 0)` is inverse to the second
projection. -/
theorem fiberQuotientEquiv_toQuotient (c : s.C) :
    B.fiberQuotientEquiv (B.fiberThickening.toQuotient c) = c :=
  B.fiberQuotientEquiv.apply_symm_apply c

end DividedPowerThickening

/-! ### Morphisms out of a finite level are morphisms into the fibre product -/

namespace CompletedCrystallineThickening

variable (X : CompletedCrystallineThickening.{u, u, u} s)

/-- The identification `X/J ≅ C` of an object of `Cris^∧(C/A)`, in the direction `X/J → C`. -/
def quotientEquiv : (X.ring ⧸ X.ring.ideal) ≃+* s.C :=
  (RingEquiv.ofBijective X.toQuotient X.toQuotient_bijective).symm

/-- `quotientEquiv` is a left inverse of the structural map. -/
@[simp]
theorem quotientEquiv_toQuotient (c : s.C) : X.quotientEquiv (X.toQuotient c) = c :=
  (RingEquiv.ofBijective X.toQuotient X.toQuotient_bijective).symm_apply_apply c

/-- `quotientEquiv` is a right inverse of the structural map. -/
@[simp]
theorem toQuotient_quotientEquiv (q : X.ring ⧸ X.ring.ideal) :
    X.toQuotient (X.quotientEquiv q) = q :=
  (RingEquiv.ofBijective X.toQuotient X.toQuotient_bijective).apply_symm_apply q

/-- A morphism of `Cris^∧(C/A)` is compatible with the identifications `X/J ≅ C`. -/
theorem quotientEquiv_quotientRingHom {Y : CompletedCrystallineThickening.{u, u, u} s}
    (u : X ⟶ Y) (q : X.ring ⧸ X.ring.ideal) :
    Y.quotientEquiv (DividedPowerRing.quotientRingHom u.hom q) = X.quotientEquiv q := by
  conv_lhs => rw [← X.toQuotient_quotientEquiv q]
  rw [← RingHom.comp_apply, u.toQuotient_comp, quotientEquiv_toQuotient]

end CompletedCrystallineThickening

namespace DividedPowerThickening

variable (B : DividedPowerThickening.{u, u, u} s)

/-- The second component of a morphism into the fibre product is the structural map `X → C`. -/
theorem fiberSnd_hom {X : CompletedCrystallineThickening.{u, u, u} s}
    (f : X ⟶ B.fiberThickening) (x : X.ring) :
    B.fiberSnd (f.hom.toRingHom x) = X.quotientEquiv (Ideal.Quotient.mk X.ring.ideal x) := by
  rw [← fiberQuotientEquiv_mk]
  change B.fiberQuotientEquiv (DividedPowerRing.quotientRingHom f.hom
    (Ideal.Quotient.mk X.ring.ideal x)) = _
  conv_lhs => rw [← X.toQuotient_quotientEquiv (Ideal.Quotient.mk X.ring.ideal x)]
  rw [← RingHom.comp_apply (DividedPowerRing.quotientRingHom f.hom), f.toQuotient_comp,
    fiberQuotientEquiv_toQuotient]

variable {X : CompletedCrystallineThickening.{u, u, u} s} {k : ℕ}
  (hX : IsPAdicLevel X.ring.ideal X.ring.dividedPowers s.p k)

/-- **The morphism `X ⟶ B ×_{B/J} C` of `Cris^∧(C/A)` attached to a morphism `X/(p)^k ⟶ B` of
`CRIS(C/A)`**: the first component is the projection onto the level followed by the morphism, the
second the structural map `X → X/J ≅ C`. -/
def levelToFiber (h : levelThickeningObj X k hX ⟶ B) : X ⟶ B.fiberThickening where
  hom := B.fiberLift X.ring (levelProj s.p X.ring k hX ≫ h.hom)
    (X.quotientEquiv.toRingHom.comp (Ideal.Quotient.mk X.ring.ideal))
    (fun x hx => by
      change X.quotientEquiv (Ideal.Quotient.mk X.ring.ideal x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero])
    (fun x => by
      have key := RingHom.congr_fun h.toQuotient_comp
        (X.quotientEquiv (Ideal.Quotient.mk X.ring.ideal x))
      refine Eq.trans ?_ key
      change _ = DividedPowerRing.quotientRingHom h.hom (levelQuotientMap s.p X.ring k hX
        (X.toQuotient (X.quotientEquiv (Ideal.Quotient.mk X.ring.ideal x))))
      rw [CompletedCrystallineThickening.toQuotient_quotientEquiv]
      rfl)
  fromBase_comp := by
    refine DFunLike.ext _ _ fun a => Subtype.ext (Prod.ext ?_ ?_)
    · exact DFunLike.congr_fun h.fromBase_comp a
    · change X.quotientEquiv (Ideal.Quotient.mk X.ring.ideal (X.fromBase.toRingHom a)) =
        algebraMap s.A s.C a
      rw [show Ideal.Quotient.mk X.ring.ideal (X.fromBase.toRingHom a) =
        X.toQuotient (algebraMap s.A s.C a) from RingHom.congr_fun X.commutes a,
        CompletedCrystallineThickening.quotientEquiv_toQuotient]
  toQuotient_comp := by
    refine RingHom.ext fun c => B.fiberQuotientEquiv.injective ?_
    rw [RingHom.comp_apply]
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (X.toQuotient c)
    rw [← hx, DividedPowerRing.quotientRingHom_mk, fiberQuotientEquiv_mk,
      fiberQuotientEquiv_toQuotient]
    change X.quotientEquiv (Ideal.Quotient.mk X.ring.ideal x) = c
    rw [hx, CompletedCrystallineThickening.quotientEquiv_toQuotient]

/-- The two components of `levelToFiber`. -/
@[simp]
theorem coe_levelToFiber_hom (h : levelThickeningObj X k hX ⟶ B) (x : X.ring) :
    (((B.levelToFiber hX h).hom.toRingHom x : B.fiberSubring) : B.ring × s.C) =
      (h.hom.toRingHom (Ideal.Quotient.mk _ x),
        X.quotientEquiv (Ideal.Quotient.mk X.ring.ideal x)) :=
  rfl

/-- `levelToFiber` is injective: a morphism out of `X/(p)^k` is determined by its first
component. -/
theorem levelToFiber_injective : Function.Injective (B.levelToFiber hX) := by
  intro h₁ h₂ e
  refine DividedPowerThickening.Hom.ext (dpRingHom_ext fun y => ?_)
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact congrArg (fun f : X ⟶ B.fiberThickening =>
    ((f.hom.toRingHom x : B.fiberSubring) : B.ring × s.C).1) e

/-- `(p)^k` dies in `B` under a morphism from the fibre product, as soon as `p^k = 0` in `B`. -/
theorem pAdicIdeal_pow_le_ker (hB : (s.p : B.ring) ^ k = 0) (f : X ⟶ B.fiberThickening) :
    DividedPowers.pAdicIdeal (A := X.ring) s.p ^ k ≤
      RingHom.ker (B.fiberFst.comp f.hom.toRingHom) := by
  intro a ha
  rw [DividedPowers.pAdicIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
  obtain ⟨r, rfl⟩ := ha
  rw [RingHom.mem_ker, map_mul, map_pow, map_natCast, hB, mul_zero]

/-- The ring map `X/(p)^k → B` induced by the first component of a morphism
`X ⟶ B ×_{B/J} C`, when `p^k = 0` in `B`. -/
def fiberToLevelRingHom (hB : (s.p : B.ring) ^ k = 0) (f : X ⟶ B.fiberThickening) :
    X.ring ⧸ DividedPowers.pAdicIdeal (A := X.ring) s.p ^ k →+* B.ring :=
  Ideal.Quotient.lift _ (B.fiberFst.comp f.hom.toRingHom)
    fun _ ha => RingHom.mem_ker.mp (B.pAdicIdeal_pow_le_ker hB f ha)

/-- `fiberToLevelRingHom` is a morphism of divided power rings. -/
theorem isDPMorphism_fiberToLevelRingHom (hB : (s.p : B.ring) ^ k = 0)
    (f : X ⟶ B.fiberThickening) :
    (dpQuotientLevelRing s.p X.ring k hX).dividedPowers.IsDPMorphism B.ring.dividedPowers
      (B.fiberToLevelRingHom hB f) := by
  refine DividedPowers.IsDPMorphism.of_comp X.ring.dividedPowers
    (dpQuotientLevelRing s.p X.ring k hX).dividedPowers B.ring.dividedPowers
    (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := X.ring) s.p ^ k))
    (B.fiberToLevelRingHom hB f) rfl (isDPMorphism_levelMk s.p X.ring k hX) ?_
  have e : (B.fiberToLevelRingHom hB f).comp
      (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := X.ring) s.p ^ k)) =
      B.fiberFst.comp f.hom.toRingHom :=
    Ideal.Quotient.lift_comp_mk _ _ _
  rw [e]
  exact DividedPowers.IsDPMorphism.comp B.ring.dividedPowers
    B.fiberFstDP.isDPMorphism f.hom.isDPMorphism

/-- The morphism `X/(p)^k ⟶ B` of `CRIS(C/A)` attached to a morphism `X ⟶ B ×_{B/J} C`, when
`p^k = 0` in `B`: the inverse of `levelToFiber`. -/
def fiberToLevel (hB : (s.p : B.ring) ^ k = 0) (f : X ⟶ B.fiberThickening) :
    levelThickeningObj X k hX ⟶ B where
  hom := DividedPowers.DPMorphism.mk' (B.isDPMorphism_fiberToLevelRingHom hX hB f)
  fromBase_comp := DFunLike.ext _ _ fun a =>
    congrArg (fun y : B.fiberSubring => (y : B.ring × s.C).1) (DFunLike.congr_fun f.fromBase_comp a)
  toQuotient_comp := by
    refine RingHom.ext fun c => ?_
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (X.toQuotient c)
    change DividedPowerRing.quotientRingHom _
      (levelQuotientMap s.p X.ring k hX (X.toQuotient c)) = B.toQuotient c
    rw [← hx]
    change Ideal.Quotient.mk B.ring.ideal (B.fiberFst (f.hom.toRingHom x)) = _
    rw [mk_fiberFst, fiberSnd_hom, hx, CompletedCrystallineThickening.quotientEquiv_toQuotient]

/-- `fiberToLevel` is a section of `levelToFiber`. -/
theorem levelToFiber_fiberToLevel (hB : (s.p : B.ring) ^ k = 0) (f : X ⟶ B.fiberThickening) :
    B.levelToFiber hX (B.fiberToLevel hX hB f) = f :=
  CompletedCrystallineThickening.Hom.ext
    (dpRingHom_ext fun x => Subtype.ext (Prod.ext rfl (B.fiberSnd_hom f x).symm))

/-- **Morphisms `X/(p)^k ⟶ B` of `CRIS(C/A)` are morphisms `X ⟶ B ×_{B/J} C` of
`Cris^∧(C/A)`**, as soon as `p^k = 0` in `B`. -/
theorem levelToFiber_bijective (hB : (s.p : B.ring) ^ k = 0) :
    Function.Bijective (B.levelToFiber hX) :=
  ⟨B.levelToFiber_injective hX, fun f =>
    ⟨B.fiberToLevel hX hB f, B.levelToFiber_fiberToLevel hX hB f⟩⟩

/-- **`levelToFiber` is natural** in the object of `Cris^∧(C/A)`, along the level maps. -/
theorem levelToFiber_levelThickeningMap {Y : CompletedCrystallineThickening.{u, u, u} s}
    (hY : IsPAdicLevel Y.ring.ideal Y.ring.dividedPowers s.p k) (v : X ⟶ Y) (hk : k ≤ k)
    (h : levelThickeningObj Y k hY ⟶ B) :
    B.levelToFiber hX ((levelThickeningMap hX hY v hk).hom ≫ h) = v ≫ B.levelToFiber hY h := by
  refine CompletedCrystallineThickening.Hom.ext
    (dpRingHom_ext fun x => Subtype.ext (Prod.ext rfl ?_))
  change X.quotientEquiv (Ideal.Quotient.mk X.ring.ideal x) =
    Y.quotientEquiv (Ideal.Quotient.mk Y.ring.ideal (v.hom.toRingHom x))
  exact (X.quotientEquiv_quotientRingHom v _).symm

end DividedPowerThickening

/-! ### The levels of `D(n)` are coproducts of the levels of `D(0)` -/

section Vertices

variable (s) {ι : Type u} (g : MvPolynomial ι s.A →ₐ[s.A] s.C) (hg : Function.Surjective g)

/-- **The `n + 1` vertex maps `D(0) ⟶ D(n)` exhibit `D(n)` as a coproduct in `Cris^∧(C/A)`**:
precomposition with them is a bijection on morphisms into any object.  This is
[Stacks, Tag 07L4] read on the cosimplicial object `D(•)`, whose degree-zero term `D(0)` is the
coproduct of a single copy of `D`. -/
theorem bijective_envelopeVertices (Y : CompletedCrystallineThickening.{u, u, u} s) (n : ℕ) :
    Function.Bijective (fun F : (envelopeCosimplicial s g hg).obj ⦋n⦌ ⟶ Y =>
      fun j : Fin (n + 1) =>
        (envelopeCosimplicial s g hg).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ j) ≫ F) := by
  set c := completedEnvelopeCoprojection s g hg 0 0
  have hc (j : Fin (n + 1)) : c ≫ (envelopeCosimplicial s g hg).map
      (SimplexCategory.const ⦋0⦌ ⦋n⦌ j) = completedEnvelopeCoprojection s g hg n j :=
    envelopeCosimplicial_coprojection_comp_map s g hg _ 0
  have hβ : Function.Bijective (fun F : (envelopeCosimplicial s g hg).obj ⦋0⦌ ⟶ Y => c ≫ F) := by
    refine ⟨fun F₁ F₂ e => envelopeCoproduct_hom_ext s g hg F₁ F₂ fun j => ?_, fun k => ?_⟩
    · rw [Fin.fin_one_eq_zero j]
      exact e
    · exact ⟨Cofan.IsColimit.desc (envelopeCoproductIsColimit s g hg 0) fun _ => k,
        coprojection_comp_desc s g hg _ 0⟩
  have hγ : Function.Bijective (fun F : (envelopeCosimplicial s g hg).obj ⦋n⦌ ⟶ Y =>
      fun j : Fin (n + 1) => completedEnvelopeCoprojection s g hg n j ≫ F) := by
    refine ⟨fun F₁ F₂ e => envelopeCoproduct_hom_ext s g hg F₁ F₂ fun j => congrFun e j,
      fun k => ⟨Cofan.IsColimit.desc (envelopeCoproductIsColimit s g hg n) k,
        funext fun j => coprojection_comp_desc s g hg k j⟩⟩
  refine (Function.Bijective.of_comp_iff' hβ.comp_left _).mp ?_
  convert hγ using 1
  funext F j
  simp only [Function.comp_apply]
  rw [← hc j]
  exact (Category.assoc _ _ _).symm

/-- **The `j`-th vertex `D(0)/(p)^{N + e} ⟶ D(n)/(p)^{N + e}`** of the cosimplicial system of
finite levels, the image of the constant map `⦋0⦌ ⟶ ⦋n⦌` with value `j`. -/
def levelVertex (n e : ℕ) (j : Fin (n + 1)) :
    ((affineLevelSystem s g hg).obj ⦋0⦌).obj (op e) ⟶
      ((affineLevelSystem s g hg).obj ⦋n⦌).obj (op e) :=
  ((affineLevelSystem s g hg).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ j)).app (op e)

/-- **The finite level `D(n)/(p)^{N + e}` is the coproduct of `n + 1` copies of
`D(0)/(p)^{N + e}` for maps into any object of the big category `CRIS(C/A)`**, the coprojections
being the vertices.  A morphism out of `D(n)/(p)^{N + e}` needs `p^{N + e} = 0` in its target,
and that is automatic for the target of a morphism out of `D(0)/(p)^{N + e}`; so no condition is
imposed on the target. -/
theorem bijective_levelVertices (B : DividedPowerThickening.{u, u, u} s) (n e : ℕ) :
    Function.Bijective (fun φ : (((affineLevelSystem s g hg).obj ⦋n⦌).obj (op e)).obj ⟶ B =>
      fun j : Fin (n + 1) => (levelVertex s g hg n e j).hom ≫ φ) := by
  classical
  set k := uniformLevel s + e
  by_cases hB : (s.p : B.ring) ^ k = 0
  · have hX (m : ℕ) := isPAdicLevel_uniformLevel_add
      (tensorPowerEnvelopeThickening s g hg m).thickening e
    have hΦ (m : ℕ) := B.levelToFiber_bijective (hX m) hB
    have hnat (φ : (((affineLevelSystem s g hg).obj ⦋n⦌).obj (op e)).obj ⟶ B)
        (j : Fin (n + 1)) :
        B.levelToFiber (hX 0) ((levelVertex s g hg n e j).hom ≫ φ) =
          (envelopeCosimplicial s g hg).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ j) ≫
            B.levelToFiber (hX n) φ :=
      B.levelToFiber_levelThickeningMap (hX 0) (hX n)
        ((envelopeCosimplicial s g hg).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ j)) le_rfl φ
    exact bijective_of_comm (fun φ => funext fun j => hnat φ j) (hΦ 0).comp_left
      (bijective_envelopeVertices s g hg B.fiberThickening n) (hΦ n)
  · have hempty (m : ℕ) (φ : (((affineLevelSystem s g hg).obj ⦋m⦌).obj (op e)).obj ⟶ B) :
        False :=
      hB (DividedPowerThickening.pow_natCast_eq_zero_of_hom φ
        (pow_natCast_eq_zero_levelRing s.p (tensorPowerEnvelopeThickening s g hg m).thickening.ring
          k (isPAdicLevel_uniformLevel_add _ e)))
    exact ⟨fun φ _ _ => (hempty n φ).elim, fun ψ => (hempty 0 (ψ 0)).elim⟩

end Vertices

/-! ### Morphisms out of an affine object of `CRIS(X/S)` into an object over the whole space -/

/-- The structure map to the ambient scheme of a transported object is an isomorphism. -/
private instance isIso_wholeι_obj_toX {S : GlobalCrystallineSituation.{u}} [IsAffine S.X]
    [IsAffine S.S.scheme] {hp : IsNilpotent (S.p : Γ(S.X, ⊤))}
    (L : (GlobalCrystallineSituation.affineIsCrystalline hp).FullSubcategory) :
    IsIso ((GlobalCrystallineSituation.SmallSite.wholeι S).obj
      ((GlobalCrystallineSituation.wholeSiteEquivLittleAffine hp).inverse.obj L).unop).obj.toX :=
  ((GlobalCrystallineSituation.wholeSiteEquivLittleAffine hp).inverse.obj L).unop.property

/-- The structure map of a transported object in the big site is an isomorphism. -/
private instance isIso_wholeToBig_obj_toX {S : GlobalCrystallineSituation.{u}} [IsAffine S.X]
    [IsAffine S.S.scheme] {hp : IsNilpotent (S.p : Γ(S.X, ⊤))}
    (L : (GlobalCrystallineSituation.affineIsCrystalline hp).FullSubcategory) :
    IsIso ((GlobalCrystallineSituation.wholeToBig S).obj
      ((GlobalCrystallineSituation.wholeSiteEquivLittleAffine hp).inverse.obj L).unop).toX :=
  ((GlobalCrystallineSituation.wholeSiteEquivLittleAffine hp).inverse.obj L).unop.property

namespace GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [SmallSite.WholeSpacePresentation S hp]

namespace SmallSite

variable (S)

/-- **A morphism from an object of `Cris(X/S)` with affine thickened scheme into the transport of
an object `L` of `Cris(Γ(X, ⊤)/Γ(S, ⊤))`, read on global sections**: the morphism of global
sections it induces, precomposed with the counit of the equivalence
`Crystalline.GlobalCrystallineSituation.wholeSiteEquivLittleAffine`. -/
def homToLevelSections (A : CrystallineThickening S) [IsAffine A.obj.thickening.source]
    (L : (affineIsCrystalline hp).FullSubcategory)
    (h : A ⟶ (wholeι S).obj ((wholeSiteEquivLittleAffine hp).inverse.obj L).unop) :
    L.obj ⟶ wholeThickeningToAffine hp A.obj :=
  haveI : IsIso ((wholeι S).obj ((wholeSiteEquivLittleAffine hp).inverse.obj L).unop).obj.toX :=
    ((wholeSiteEquivLittleAffine hp).inverse.obj L).unop.property
  haveI : IsIso ((wholeToBig S).obj ((wholeSiteEquivLittleAffine hp).inverse.obj L).unop).toX :=
    ((wholeSiteEquivLittleAffine hp).inverse.obj L).unop.property
  ((wholeSiteEquivLittleAffine hp).counitIso.inv.app L).hom ≫ wholeHomToAffine hp h.hom

omit [WholeSpacePresentation S hp] in
/-- **Morphisms from an object with affine thickened scheme into a transported object are
morphisms of global sections**: `homToLevelSections` is a bijection.  Injectivity is the
faithfulness `Crystalline.GlobalCrystallineSituation.wholeHomToAffine_injective`, surjectivity is
`Crystalline.GlobalCrystallineSituation.homOfAffineSections`. -/
theorem bijective_homToLevelSections (A : CrystallineThickening S)
    [IsAffine A.obj.thickening.source] (L : (affineIsCrystalline hp).FullSubcategory) :
    Function.Bijective (homToLevelSections S hp A L) := by
  refine ⟨fun h₁ h₂ e => ?_, fun ψ => ?_⟩
  · exact ObjectProperty.hom_ext _ (wholeHomToAffine_injective hp
      ((cancel_epi ((wholeSiteEquivLittleAffine hp).counitIso.inv.app L).hom).mp e))
  · refine ⟨ObjectProperty.homMk (homOfAffineSections hp
      (((wholeSiteEquivLittleAffine hp).counitIso.hom.app L).hom ≫ ψ)), ?_⟩
    have h1 : ((wholeSiteEquivLittleAffine hp).counitIso.inv.app L).hom ≫
        ((wholeSiteEquivLittleAffine hp).counitIso.hom.app L).hom = 𝟙 L.obj :=
      congrArg (fun f => InducedCategory.Hom.hom f)
        ((wholeSiteEquivLittleAffine hp).counitIso.inv_hom_id_app L)
    change ((wholeSiteEquivLittleAffine hp).counitIso.inv.app L).hom ≫
      wholeHomToAffine hp (homOfAffineSections hp
        (((wholeSiteEquivLittleAffine hp).counitIso.hom.app L).hom ≫ ψ)) = ψ
    rw [wholeHomToAffine_homOfAffineSections]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ ψ) h1).trans (Category.id_comp ψ))

omit [WholeSpacePresentation S hp] in
/-- **`homToLevelSections` is natural in the object of `Cris(Γ(X, ⊤)/Γ(S, ⊤))`.** -/
theorem homToLevelSections_comp (A : CrystallineThickening S) [IsAffine A.obj.thickening.source]
    {L L' : (affineIsCrystalline hp).FullSubcategory} (v : L ⟶ L')
    (h : A ⟶ (wholeι S).obj ((wholeSiteEquivLittleAffine hp).inverse.obj L').unop) :
    homToLevelSections S hp A L
        (h ≫ (wholeι S).map ((wholeSiteEquivLittleAffine hp).inverse.map v).unop) =
      v.hom ≫ homToLevelSections S hp A L' h := by
  have key : ((wholeSiteEquivLittleAffine hp).counitIso.inv.app L).hom ≫
      wholeHomToAffine hp
        ((wholeι S).map ((wholeSiteEquivLittleAffine hp).inverse.map v).unop).hom =
      v.hom ≫ ((wholeSiteEquivLittleAffine hp).counitIso.inv.app L').hom :=
    (congrArg (fun f => InducedCategory.Hom.hom f)
      ((wholeSiteEquivLittleAffine hp).counitIso.inv.naturality v)).symm
  change ((wholeSiteEquivLittleAffine hp).counitIso.inv.app L).hom ≫
      wholeHomToAffine hp (h.hom ≫
        ((wholeι S).map ((wholeSiteEquivLittleAffine hp).inverse.map v).unop).hom) =
    v.hom ≫ ((wholeSiteEquivLittleAffine hp).counitIso.inv.app L').hom ≫
      wholeHomToAffine hp h.hom
  rw [wholeHomToAffine_comp]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ wholeHomToAffine hp h.hom) key).trans (Category.assoc _ _ _))

/-! ### The vertices of the system `(X, T(n)_e, δ(n))` -/

/-- **The `j`-th vertex `T(n)_e ⟶ T(0)_e`** of the system of [Stacks, Tag 07JN]: the component at
`e` of the image of the constant map `⦋0⦌ ⟶ ⦋n⦌` with value `j`. -/
def wholeSpaceVertex (n e : ℕ) (j : Fin (n + 1)) :
    ((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e ⟶
      ((wholeSpaceSystem S hp).obj (op ⦋0⦌)).obj e :=
  ((wholeSpaceSystem S hp).map (op (SimplexCategory.const ⦋0⦌ ⦋n⦌ j))).app e

/-- The vertex `T(n)_e ⟶ T(0)_e` is the transport of the vertex
`D(0)/(p)^{N + e} ⟶ D(n)/(p)^{N + e}`. -/
theorem wholeSpaceVertex_eq (n e : ℕ) (j : Fin (n + 1)) :
    wholeSpaceVertex S hp n e j =
      (wholeι S).map ((wholeSiteEquivLittleAffine hp).inverse.map
        (levelVertex (affineSituation S hp) (wholeSpacePresentation S hp)
          (wholeSpacePresentation_surjective S hp) n e j)).unop :=
  rfl

variable {S}

/-- **[Stacks, Lemma 60.5.6, Tag 07HP] for the affine objects of `Cris(X/S)`**: an object
`(U, T, δ)` of `Cris(X/S)` with `U` and `T` affine admits a morphism to the level `T(0)_e` of the
system `(X, T(n)_e, δ(n))` of [Stacks, Tag 07JN] for every large `e`.  The open `U ⊆ X` is
arbitrary; `...SmallSite.exists_hom_to_wholeSpaceSystem_level` is the case `U = X`. -/
theorem exists_forall_le_hom_wholeSpaceLevel {A : CrystallineThickening S}
    (hA : IsAffineObject S A) :
    ∃ N, ∀ e, N ≤ e → Nonempty (A ⟶ ((wholeSpaceSystem S hp).obj (op ⦋0⦌)).obj e) := by
  have := hA.1
  obtain ⟨N, hN⟩ := exists_forall_le_levelThickening_hom
    (tensorPowerPresentation (affineSituation S hp) (wholeSpacePresentation S hp) 0)
    (tensorPowerPresentation_surjective _ _ (wholeSpacePresentation_surjective S hp) 0)
    (tensorPowerEnvelopeThickening (affineSituation S hp) (wholeSpacePresentation S hp)
      (wholeSpacePresentation_surjective S hp) 0)
    (wholeThickeningToAffine hp A.obj)
  refine ⟨N, fun e he => ?_⟩
  obtain ⟨_, ⟨φ⟩⟩ := hN (uniformLevel (affineSituation S hp) + e) (by omega)
  obtain ⟨h, -⟩ := (bijective_homToLevelSections S hp A
    (((affineLevelSystem (affineSituation S hp) (wholeSpacePresentation S hp)
      (wholeSpacePresentation_surjective S hp)).obj ⦋0⦌).obj (op e))).2 φ
  exact ⟨h⟩

/-- **The level `T(n)_e` is the product of `n + 1` copies of `T(0)_e` as seen from the affine
objects of `Cris(X/S)`**: for an object `A` with affine thickened and ambient schemes, composing
with the `n + 1` vertices `T(n)_e ⟶ T(0)_e` is a bijection
`Hom(A, T(n)_e) ≅ Hom(A, T(0)_e)^{n + 1}`.

On global sections this is `Crystalline.bijective_levelVertices`, the coproduct property of the
finite levels of the envelopes `D(n)` for maps into objects of the big category
`CRIS(Γ(X, ⊤)/Γ(S, ⊤))`; the passage to `Cris(X/S)` is
`...SmallSite.bijective_homToLevelSections` and its naturality. -/
theorem bijective_wholeSpaceVertices {A : CrystallineThickening S} (hA : IsAffineObject S A)
    (n e : ℕ) :
    Function.Bijective (fun h : A ⟶ ((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e =>
      fun j : Fin (n + 1) => h ≫ wholeSpaceVertex S hp n e j) := by
  have := hA.1
  set L := fun m : ℕ => ((affineLevelSystem (affineSituation S hp) (wholeSpacePresentation S hp)
    (wholeSpacePresentation_surjective S hp)).obj ⦋m⦌).obj (op e)
  have hΘ (m : ℕ) := bijective_homToLevelSections S hp A (L m)
  exact bijective_of_comm (fun h => funext fun j => homToLevelSections_comp S hp A _ h)
    (hΘ 0).comp_left (bijective_levelVertices (affineSituation S hp) (wholeSpacePresentation S hp)
      (wholeSpacePresentation_surjective S hp) (wholeThickeningToAffine hp A.obj) n e) (hΘ n)

/-- **The faces of the system read on the vertices**: the `i`-th face `T(n + 1)_e ⟶ T(n)_e`
followed by the `j`-th vertex is the `i.succAbove j`-th vertex. -/
@[reassoc (attr := simp)]
theorem δ_app_comp_wholeSpaceVertex (n e : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1)) :
    ((wholeSpaceSystem S hp).δ i).app e ≫ wholeSpaceVertex S hp n e j =
      wholeSpaceVertex S hp (n + 1) e (i.succAbove j) := by
  rw [wholeSpaceVertex, wholeSpaceVertex, SimplicialObject.δ, ← NatTrans.comp_app,
    ← Functor.map_comp]
  rfl

/-- **The level maps of the system read on the vertices**: the vertices commute with the
transition maps `T(n)_e ⟶ T(n)_{e'}`. -/
@[reassoc (attr := simp)]
theorem map_comp_wholeSpaceVertex (n : ℕ) {e e' : ℕ} (h : e ≤ e') (j : Fin (n + 1)) :
    ((wholeSpaceSystem S hp).obj (op ⦋n⦌)).map (homOfLE h) ≫ wholeSpaceVertex S hp n e' j =
      wholeSpaceVertex S hp n e j ≫ ((wholeSpaceSystem S hp).obj (op ⦋0⦌)).map (homOfLE h) :=
  ((wholeSpaceSystem S hp).map (op (SimplexCategory.const ⦋0⦌ ⦋n⦌ j))).naturality (homOfLE h)

/-- **The diagonal**: the degeneracy `T(0)_e ⟶ T(1)_e` followed by either vertex is the
identity. -/
@[reassoc (attr := simp)]
theorem σ_app_comp_wholeSpaceVertex (e : ℕ) (j : Fin 2) :
    ((wholeSpaceSystem S hp).σ 0).app e ≫ wholeSpaceVertex S hp 1 e j = 𝟙 _ := by
  rw [wholeSpaceVertex, SimplicialObject.σ, ← NatTrans.comp_app, ← Functor.map_comp]
  have h1 : (SimplexCategory.σ (0 : Fin 1)).op ≫ op (SimplexCategory.const ⦋0⦌ ⦋1⦌ j) =
      𝟙 (op ⦋0⦌) :=
    Quiver.Hom.unop_inj (SimplexCategory.Hom.ext_zero_left _ _ (Subsingleton.elim (α := Fin 1) _ _))
  rw [h1, CategoryTheory.Functor.map_id, NatTrans.id_app]

end SmallSite

end GlobalCrystallineSituation

end Crystalline

end

end
