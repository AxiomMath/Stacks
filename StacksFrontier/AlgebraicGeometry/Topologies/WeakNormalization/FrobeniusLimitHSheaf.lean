module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.RingTheory.Perfection
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorPullback
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpSheafCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Topologies.WeakNormalization.FrobeniusColimitHSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.WeakNormalization.TwoGeneratorKernel
public import StacksFrontier.AlgebraicGeometry.Topologies.WeakNormalization.TwoGeneratorCohomology

/-!
# The Frobenius-limit presheaf and the four conditions of the h sheaf criterion

For a ring `A` and a natural number `p` the set `lim_F A` is the limit of
`⋯ →^F A →^F A →^F A` along `F : a ↦ a ^ p`, that is, the set of sequences `(a_n)` of elements
of `A` with `a_n = a_{n+1} ^ p`.  This is Mathlib's `Perfection A p`.  On the big h site
`(Sch/S)_h` of Stacks 0EU1 the rule `X ↦ lim_F Γ(X, 𝒪_X)` is a presheaf of sets, and Stacks
0EVL asserts that for `S` over `𝔽_p` it is a sheaf.

This file builds that presheaf and verifies for it the four conditions of the h sheaf criterion
Stacks 0EVI.

## Main definitions

* `CategoryTheory.Presheaf.frobeniusLimit`: the presheaf `lim_F G` attached to a presheaf of
  commutative rings `G`.
* `AlgebraicGeometry.BigHOver.frobeniusLimitSections`: the presheaf `lim_F Γ(-, 𝒪)` on the big h
  category over `S`.

## Main results

* `Perfection.bijective_mapMonoidHom_of_surjective_of_pow_eq_zero`: a surjection of
  `𝔽_p`-algebras whose kernel is uniformly nilpotent induces a bijection of Frobenius limits.
* `AlgebraicGeometry.BigHOver.isZariskiSheaf_frobeniusLimitSections`: **condition (1)**, the
  Zariski sheaf condition.
* `AlgebraicGeometry.BigHOver.isAffineFlatProperFinitePresentationSheaf_frobeniusLimitSections`:
  **condition (2)**, descent for flat proper surjections of finite presentation over affines.
* `AlgebraicGeometry.BigHOver.isOneGeneratorAlmostBlowUpSheaf_frobeniusLimitSections`:
  **condition (3)**, cartesianness for the almost blowup squares of Example 0EVG.
* `AlgebraicGeometry.BigHOver.isTwoGeneratorAlmostBlowUpSheaf_frobeniusLimitSections`:
  **condition (4)**, cartesianness for the almost blowup squares of Example 0EVH.
* `AlgebraicGeometry.BigHOver.isSheaf_frobeniusLimitSections_of_criterion`: Stacks 0EVL, with the
  two unproved inputs of the sufficiency direction of the criterion carried as hypotheses.

## Implementation notes

**Why the last statement carries hypotheses.**  The source proves Stacks 0EVL by checking
conditions (1) to (4) of the h sheaf criterion Stacks 0EVI.  The sufficiency direction of that
criterion is not available in this development: it is
`AlgebraicGeometry.BigHOver.isSheaf_iff_zariski_and_affineFlatProperFP_and_generatorSquares`,
which carries `AlgebraicGeometry.AffineAlmostBlowUpHSheafCriterion` and
`AlgebraicGeometry.GeneratorAlmostBlowUpSquaresSuffice` as explicit unproved hypotheses.  The
four conditions below are proved unconditionally, so they are the whole content of Stacks 0EVL;
the assembly is stated with those hypotheses and carries no `@[stacks 0EVL]` attribute, because
nothing here proves the sheaf property.  The route of Stacks 0EVK — build the sheaf as
`X ↦ Γ(Xᵃʷⁿ, 𝒪)` and compare — is not available either: the Frobenius limit of a perfect ring
is the ring itself, so `lim_F Γ(-, 𝒪)` is not the absolute weak normalization sheaf, and Stacks
0EVL asserts the sheaf property of the rule itself rather than of a comparison.

**Conditions (1) and (2).**  Both are descent for the Frobenius limit along a covering for which
global functions already descend: global functions are the points of the affine line over `ℤ`
and the fpqc topology on all schemes is subcanonical
(`Stacks.Sites.isSheaf_fpqcTopology_globalSections`), and a Zariski covering, as well as a flat
proper surjection of finite presentation, is an fpqc covering.  Descent passes from a presheaf of
rings to its Frobenius limit coefficientwise:
`CategoryTheory.Presheaf.isSheafFor_frobeniusLimit`.

**Conditions (3) and (4).**  Here the content is algebraic.  For the square of Example 0EVG the
ring square is a pushout of commutative rings with both maps surjective and with the
intersection of the two kernels nilpotent, because the ideal `J` is annihilated by a power of
`f`; the Frobenius limit of a surjection with uniformly nilpotent kernel is bijective, which
turns the pushout into a cartesian square of sets.  For the square of Example 0EVH the map
`Γ(X, 𝒪) ⟶ Γ(X', 𝒪)` is a surjection whose kernel has square zero, which is Stacks 0EVJ, so the
Frobenius limit of that restriction is bijective, and the restriction to the exceptional corner
is injective on Frobenius limits because the exceptional corner is a projective line over the
centre and so admits a section over it.

## References

* [Stacks Project, Tag 0EVL](https://stacks.math.columbia.edu/tag/0EVL)
* [Stacks Project, Tag 0EVI](https://stacks.math.columbia.edu/tag/0EVI)
* [Stacks Project, Tag 0EVG](https://stacks.math.columbia.edu/tag/0EVG)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
* [Stacks Project, Tag 0EVJ](https://stacks.math.columbia.edu/tag/0EVJ)
* [Stacks Project, Tag 0EU1](https://stacks.math.columbia.edu/tag/0EU1)
* [Stacks Project, Tag 0EU5](https://stacks.math.columbia.edu/tag/0EU5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace CategoryTheory.Presheaf

/-- The Frobenius limit `lim_F G` of a presheaf of commutative rings: the presheaf of sets whose
sections over `X` are the sequences `(a_n)` of sections of `G` over `X` with `a_n = a_{n+1} ^ p`,
with the coefficientwise restriction maps. -/
public def frobeniusLimit {C : Type*} [Category* C] (G : Cᵒᵖ ⥤ CommRingCat.{u}) (p : ℕ) :
    Cᵒᵖ ⥤ Type u where
  obj X := Perfection (ToType (G.obj X)) p
  map f := TypeCat.ofHom (Perfection.mapMonoidHom p (G.map f).hom.toMonoidHom)
  map_id X := by
    ext a n
    change (G.map (𝟙 X)).hom (Perfection.coeffMonoidHom _ p n a) =
      Perfection.coeffMonoidHom _ p n a
    rw [G.map_id]
    rfl
  map_comp f g := by
    ext a n
    change (G.map (f ≫ g)).hom (Perfection.coeffMonoidHom _ p n a) =
      (G.map g).hom ((G.map f).hom (Perfection.coeffMonoidHom _ p n a))
    rw [G.map_comp]
    exact CommRingCat.comp_apply _ _ _

/-- The `n`-th coefficient of a restricted Frobenius limit section is the restriction of the
`n`-th coefficient. -/
public theorem coeffMonoidHom_frobeniusLimit_map {C : Type*} [Category* C]
    (G : Cᵒᵖ ⥤ CommRingCat.{u}) (p : ℕ) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (a : (frobeniusLimit G p).obj X) (n : ℕ) :
    Perfection.coeffMonoidHom _ p n ((frobeniusLimit G p).map f a) =
      (G.map f).hom (Perfection.coeffMonoidHom _ p n a) :=
  rfl

/-- Descent passes from a presheaf of commutative rings to its Frobenius limit: if every
compatible family of sections of `G` over a presieve has a unique amalgamation, so does every
compatible family of Frobenius limit sections, amalgamated coefficient by coefficient. -/
public theorem isSheafFor_frobeniusLimit {C : Type*} [Category* C] {X : C} (p : ℕ)
    (G : Cᵒᵖ ⥤ CommRingCat.{u}) (R : Presieve X)
    (hG : Presieve.IsSheafFor (G ⋙ CategoryTheory.forget CommRingCat.{u}) R) :
    Presieve.IsSheafFor (frobeniusLimit G p) R := by
  intro x hx
  let coord (n : ℕ) : R.FamilyOfElements (G ⋙ CategoryTheory.forget CommRingCat.{u}) :=
    fun Y f hf => Perfection.coeffMonoidHom _ p n (x f hf)
  have hcoord (n : ℕ) : (coord n).Compatible := fun _ _ _ g₁ g₂ _ _ h₁ h₂ hcomm =>
    congrArg (Perfection.coeffMonoidHom _ p n) (hx g₁ g₂ h₁ h₂ hcomm)
  let glued (n : ℕ) : ToType (G.obj (op X)) := (hG (coord n) (hcoord n)).choose
  have hglued (n : ℕ) : (coord n).IsAmalgamation (glued n) :=
    (hG (coord n) (hcoord n)).choose_spec.1
  have hstep (n : ℕ) : glued (n + 1) ^ p = glued n := by
    apply (hG (coord n) (hcoord n)).choose_spec.2
    intro Y f hf
    show (G.map f.op).hom (glued (n + 1) ^ p) = _
    rw [map_pow, show (G.map f.op).hom (glued (n + 1)) = coord (n + 1) f hf from
      hglued (n + 1) f hf]
    exact Perfection.coeffMonoidHom_pow_p' (x f hf) n
  exact ⟨⟨glued, hstep⟩, fun Y f hf => Perfection.extMonoid fun n => hglued n f hf,
    fun t' ht' => Perfection.extMonoid fun n => (hG (coord n) (hcoord n)).choose_spec.2 _
      fun Y f hf => congrArg (Perfection.coeffMonoidHom _ p n) (ht' f hf)⟩

end CategoryTheory.Presheaf

namespace Perfection

/-- **The Frobenius limit of a nilpotent thickening.** A surjection of commutative rings in which
the prime `p` vanishes, whose kernel is annihilated by a fixed power, induces a bijection on
Frobenius limits: a compatible tower of `p`-power roots downstairs lifts uniquely, because
raising a lift to a high enough `p`-power kills the ambiguity and the obstruction. -/
public theorem bijective_mapMonoidHom_of_surjective_of_pow_eq_zero {p : ℕ} (hp : p.Prime)
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective φ) (hcast : (p : R) = 0)
    (hker : ∃ m : ℕ, ∀ x : R, φ x = 0 → x ^ m = 0) :
    Function.Bijective (Perfection.mapMonoidHom p (φ : R →* S)) := by
  obtain ⟨m, hm⟩ := hker
  by_cases hR : Nontrivial R
  · let : Fact p.Prime := ⟨hp⟩
    have : CharP R p := by
      classical
      rw [← ringChar.eq_iff]
      exact ((Nat.dvd_prime hp).mp (ringChar.dvd hcast)).resolve_left CharP.ringChar_ne_one
    set N := m + 1
    have hN : m ≤ p ^ N :=
      (Nat.lt_pow_self hp.one_lt).le.trans (Nat.pow_le_pow_right hp.pos m.le_succ)
    constructor
    · intro a b hab
      apply Subtype.ext
      funext n
      have hn : φ (a.1 (n + N)) = φ (b.1 (n + N)) :=
        congrArg (Perfection.coeffMonoidHom S p (n + N)) hab
      have hzero : (a.1 (n + N) - b.1 (n + N)) ^ p ^ N = 0 :=
        pow_eq_zero_of_le hN (hm _ (by rw [map_sub, hn, sub_self]))
      rw [sub_pow_char_pow,
        show a.1 (n + N) ^ p ^ N = a.1 n from Perfection.coeffMonoidHom_pow_p_pow' a n N,
        show b.1 (n + N) ^ p ^ N = b.1 n from Perfection.coeffMonoidHom_pow_p_pow' b n N] at hzero
      exact sub_eq_zero.mp hzero
    · intro b
      classical
      let root : ℕ → R := fun n => Classical.choose (hφ (b.1 (n + N)))
      have hroot (n : ℕ) : φ (root n) = b.1 (n + N) :=
        Classical.choose_spec (hφ (b.1 (n + N)))
      refine ⟨⟨fun n => root n ^ (p ^ N), ?_⟩, ?_⟩
      · intro n
        have hd : φ (root (n + 1) ^ p - root n) = 0 := by
          simp only [map_sub, map_pow, hroot]
          rw [show n + 1 + N = n + N + 1 by omega, b.2 (n + N), sub_self]
        show (root (n + 1) ^ p ^ N) ^ p = _
        rw [← pow_mul, Nat.mul_comm, pow_mul, ← sub_eq_zero,
          ← sub_pow_char_pow (R := R) (root (n + 1) ^ p) (root n) N]
        exact pow_eq_zero_of_le hN (hm _ hd)
      · apply Subtype.ext
        funext n
        show φ (root n ^ p ^ N) = b.1 n
        rw [map_pow, hroot]
        exact Perfection.coeffMonoidHom_pow_p_pow' b n N
  · have : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    have : Subsingleton S := hφ.subsingleton
    exact ⟨fun a b _ => Subtype.ext (funext fun _ => Subsingleton.elim _ _), fun b =>
      ⟨⟨fun _ => 0, fun _ => Subsingleton.elim _ _⟩,
        Subtype.ext (funext fun _ => Subsingleton.elim _ _)⟩⟩

end Perfection

namespace CategoryTheory.Limits.Types

/-- A commuting square of types whose left edge is bijective and whose right edge is injective is
cartesian. -/
public theorem isPullback_of_bijective_snd_of_injective_fst {P X Y Z : Type u}
    (a : P → X) (b : P → Y) (f : X → Z) (g : Y → Z)
    (hcomm : ∀ x, f (a x) = g (b x)) (hb : Function.Bijective b) (hf : Function.Injective f) :
    IsPullback (TypeCat.ofHom a) (TypeCat.ofHom b) (TypeCat.ofHom f) (TypeCat.ofHom g) := by
  rw [Types.isPullback_iff]
  refine ⟨by ext x; exact hcomm x, fun x y h => hb.1 h.2, fun x₂ x₃ h => ?_⟩
  obtain ⟨x₁, hx₁⟩ := hb.2 x₃
  refine ⟨x₁, hf ?_, hx₁⟩
  show f (a x₁) = f x₂
  rw [hcomm x₁, hx₁]
  exact h.symm

end CategoryTheory.Limits.Types

namespace AlgebraicGeometry

/-- **A pushout of rings with nilpotent kernel intersection is a pullback of Frobenius limits.**
If a square of commutative rings is a pushout, the two maps out of the corner are surjective, the
prime `p` vanishes in the corner and the intersection of the two kernels is nilpotent, then the
square of Frobenius limits is cartesian: the map of the corner into the fibre product of the two
rings is then surjective with uniformly nilpotent kernel. -/
public theorem isPullback_mapMonoidHom_of_isPushout (p : ℕ) (hp : p.Prime)
    {R S T U : CommRingCat.{u}} (f : R ⟶ S) (g : R ⟶ T) (i : S ⟶ U) (j : T ⟶ U)
    (hpo : IsPushout f g i j) (hf : Function.Surjective f.hom)
    (hg : Function.Surjective g.hom) (hcast : (p : ToType R) = 0)
    (hnil : IsNilpotent (RingHom.ker f.hom ⊓ RingHom.ker g.hom)) :
    IsPullback (TypeCat.ofHom (Perfection.mapMonoidHom p f.hom.toMonoidHom))
      (TypeCat.ofHom (Perfection.mapMonoidHom p g.hom.toMonoidHom))
      (TypeCat.ofHom (Perfection.mapMonoidHom p i.hom.toMonoidHom))
      (TypeCat.ofHom (Perfection.mapMonoidHom p j.hom.toMonoidHom)) := by
  classical
  have hcomm (x : ToType R) : i.hom (f.hom x) = j.hom (g.hom x) :=
    congrArg (fun k : R ⟶ U => ConcreteCategory.hom k x) hpo.w
  let P : Subring (ToType S × ToType T) :=
    RingHom.eqLocus (i.hom.comp (RingHom.fst (ToType S) (ToType T)))
      (j.hom.comp (RingHom.snd (ToType S) (ToType T)))
  let lift : ToType R →+* P :=
    { toFun := fun x => ⟨(f.hom x, g.hom x), hcomm x⟩
      map_zero' := by apply Subtype.ext; simp
      map_one' := by apply Subtype.ext; simp
      map_add' := by intro x y; apply Subtype.ext; simp
      map_mul' := by intro x y; apply Subtype.ext; simp }
  have hliftfst (x : ToType R) : (lift x).1.1 = f.hom x := rfl
  have hliftsnd (x : ToType R) : (lift x).1.2 = g.hom x := rfl
  -- the lift is surjective, by the universal property of the pushout
  let K := RingHom.ker f.hom ⊔ RingHom.ker g.hom
  let qf := RingHom.liftOfSurjective f.hom hf
    ⟨Ideal.Quotient.mk K, by
      show RingHom.ker f.hom ≤ RingHom.ker (Ideal.Quotient.mk K)
      rw [Ideal.mk_ker]; exact le_sup_left⟩
  let qg := RingHom.liftOfSurjective g.hom hg
    ⟨Ideal.Quotient.mk K, by
      show RingHom.ker g.hom ≤ RingHom.ker (Ideal.Quotient.mk K)
      rw [Ideal.mk_ker]; exact le_sup_right⟩
  have hq : f ≫ CommRingCat.ofHom qf = g ≫ CommRingCat.ofHom qg := by
    ext x
    simp [qf, qg, RingHom.liftOfSurjective_comp_apply]
  have hqf (x : ToType R) : qf (f.hom x) = Ideal.Quotient.mk K x :=
    RingHom.liftOfSurjective_comp_apply f.hom hf _ x
  have hmem (x : ToType R) (hx : i.hom (f.hom x) = 0) : x ∈ K := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hk : (hpo.desc (CommRingCat.ofHom qf) (CommRingCat.ofHom qg) hq).hom
        (i.hom (f.hom x)) = qf (f.hom x) :=
      congrArg (fun h : S ⟶ CommRingCat.of (ToType R ⧸ K) => ConcreteCategory.hom h (f.hom x))
        (hpo.inl_desc (CommRingCat.ofHom qf) (CommRingCat.ofHom qg) hq)
    rw [hx, map_zero] at hk
    rw [← hqf x, ← hk]
  have hlift : Function.Surjective lift := by
    intro a
    obtain ⟨x, hx⟩ := hf a.1.1
    obtain ⟨y, hy⟩ := hg a.1.2
    have hxy : x - y ∈ K := by
      apply hmem
      simp only [map_sub]
      rw [hx, hcomm y, hy]
      exact sub_eq_zero.mpr a.2
    obtain ⟨xf, hxf, xg, hxg, heq⟩ := Submodule.mem_sup.mp hxy
    refine ⟨x - xf, Subtype.ext (Prod.ext ?_ ?_)⟩
    · show f.hom (x - xf) = a.1.1
      simpa [map_sub, RingHom.mem_ker.mp hxf] using hx
    · show g.hom (x - xf) = a.1.2
      have hdiff : x - xf = y + xg := by linear_combination -heq
      rw [hdiff, map_add, RingHom.mem_ker.mp hxg, add_zero, hy]
  obtain ⟨m, hm⟩ := hnil
  have hbij := Perfection.bijective_mapMonoidHom_of_surjective_of_pow_eq_zero hp lift hlift hcast
    ⟨m, fun x hx => by
      have hpow := Ideal.pow_mem_pow (show x ∈ RingHom.ker f.hom ⊓ RingHom.ker g.hom from
        ⟨congrArg (fun a : P => a.1.1) hx, congrArg (fun a : P => a.1.2) hx⟩) m
      rw [hm] at hpow
      exact Ideal.mem_bot.mp hpow⟩
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext a n
    exact hcomm (a.1 n)
  · rintro a b ⟨h₁, h₂⟩
    exact hbij.1 (Perfection.extMonoid fun n => Subtype.ext
      (Prod.ext (congrArg (Perfection.coeffMonoidHom (ToType S) p n) h₁)
        (congrArg (Perfection.coeffMonoidHom (ToType T) p n) h₂)))
  · intro α β hαβ
    have hcompat (n : ℕ) : i.hom (α.1 n) = j.hom (β.1 n) :=
      congrArg (Perfection.coeffMonoidHom (ToType U) p n) hαβ
    let γ : Perfection P p :=
      ⟨fun n => ⟨(α.1 n, β.1 n), hcompat n⟩, fun n => Subtype.ext (Prod.ext (α.2 n) (β.2 n))⟩
    obtain ⟨a, ha⟩ := hbij.2 γ
    refine ⟨a, Perfection.extMonoid fun n => ?_, Perfection.extMonoid fun n => ?_⟩
    · show f.hom (a.1 n) = α.1 n
      exact congrArg (fun c : P => c.1.1) (congrFun (congrArg Subtype.val ha) n)
    · show g.hom (a.1 n) = β.1 n
      exact congrArg (fun c : P => c.1.2) (congrFun (congrArg Subtype.val ha) n)

/-! ### The Frobenius limit of global functions on schemes -/

/-- The presheaf `lim_F Γ(-, 𝒪)` on the category of all schemes. -/
public abbrev frobeniusLimitGlobalSections (p : ℕ) : Scheme.{u}ᵒᵖ ⥤ Type u :=
  Presheaf.frobeniusLimit Scheme.Γ.{u} p

/-- A prime vanishing in the global functions of a scheme vanishes in the global functions of
every scheme over it. -/
public theorem natCast_eq_zero_appTop_of_hom {p : ℕ} {T T' : Scheme.{u}} (h : T ⟶ T')
    (hT' : (p : Γ(T', ⊤)) = 0) : (p : Γ(T, ⊤)) = 0 := by
  simpa only [map_natCast, map_zero] using congrArg (fun a : Γ(T', ⊤) => h.appTop.hom a) hT'

/-- **A square-zero thickening does not change the Frobenius limit of global functions.** If
restriction of global functions along `f : X ⟶ Y` is surjective with kernel of square zero and
the prime `p` vanishes on `Y`, then `f` induces a bijection of Frobenius limits of global
functions. -/
public theorem bijective_frobeniusLimit_of_surjective_of_ker_sq_eq_bot
    (p : ℕ) (hp : p.Prime) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hChar : (p : Γ(Y, ⊤)) = 0)
    (hsurj : Function.Surjective (Scheme.Γ.map f.op).hom)
    (hker : RingHom.ker (Scheme.Γ.map f.op).hom ^ 2 = ⊥) :
    Function.Bijective (Perfection.mapMonoidHom p (Scheme.Γ.map f.op).hom.toMonoidHom) := by
  refine Perfection.bijective_mapMonoidHom_of_surjective_of_pow_eq_zero hp
    (Scheme.Γ.map f.op).hom hsurj hChar ⟨2, fun x hx => ?_⟩
  simpa only [hker, Ideal.mem_bot] using Ideal.pow_mem_pow (RingHom.mem_ker.mpr hx) 2

/-- Cartesianness of the square of sections attached to a pair of morphisms with a common
target only depends on the pair up to isomorphism of the three schemes involved: a model pair
whose squares of sections are cartesian for every exceptional corner forces the same for the
pair itself.

Nothing about the Frobenius is used: the statement holds for an arbitrary presheaf of sets on
schemes, and both `AlgebraicGeometry.isPullback_frobeniusLimit_twoGeneratorModel` and the
corresponding Frobenius *colimit* statement consume it at their own presheaf. -/
public theorem isPullback_map_op_of_modelPair (F : Scheme.{u}ᵒᵖ ⥤ Type u)
    {X X' Z E Xm X'm Zm : Scheme.{u}}
    (b : X' ⟶ X) (z : Z ⟶ X) (d : E ⟶ X') (e : E ⟶ Z)
    (bm : X'm ⟶ Xm) (zm : Zm ⟶ Xm)
    (hpb : IsPullback e d z b)
    (iX : X ≅ Xm) (iX' : X' ≅ X'm) (iZ : Z ≅ Zm)
    (hb : b ≫ iX.hom = iX'.hom ≫ bm)
    (hz : z ≫ iX.hom = iZ.hom ≫ zm)
    (hm : ∀ (dm : E ⟶ X'm) (em : E ⟶ Zm), IsPullback em dm zm bm →
      IsPullback (F.map zm.op) (F.map bm.op) (F.map em.op) (F.map dm.op)) :
    IsPullback (F.map z.op) (F.map b.op) (F.map e.op) (F.map d.op) := by
  have hmodel : IsPullback (e ≫ iZ.hom) (d ≫ iX'.hom) zm bm :=
    hpb.of_iso (Iso.refl E) iZ iX' iX (by simp) (by simp) hz hb
  have ht := hm _ _ hmodel
  refine ht.of_iso (F.mapIso iX.op) (F.mapIso iZ.op)
    (F.mapIso iX'.op) (Iso.refl _) ?_ ?_ ?_ ?_ <;>
    simp only [Functor.mapIso_hom, Iso.op_hom, Iso.refl_hom, Category.comp_id]
  · simpa only [op_comp, Functor.map_comp] using congrArg F.map
      (congrArg Quiver.Hom.op hz.symm)
  · simpa only [op_comp, Functor.map_comp] using congrArg F.map
      (congrArg Quiver.Hom.op hb.symm)
  · exact F.map_comp iZ.hom.op e.op
  · exact F.map_comp iX'.hom.op d.op

/-- A commuting square of schemes which is bijective on sections along the modification and
injective along the exceptional corner of the centre has cartesian square of sections.

Nothing about the Frobenius is used; the presheaf of sets is arbitrary. -/
public theorem isPullback_map_op_of_bijective_of_injective (F : Scheme.{u}ᵒᵖ ⥤ Type u)
    {Xm X'm Zm E : Scheme.{u}} (bm : X'm ⟶ Xm) (zm : Zm ⟶ Xm) (dm : E ⟶ X'm) (em : E ⟶ Zm)
    (hw : em ≫ zm = dm ≫ bm)
    (hbij : Function.Bijective (F.map bm.op))
    (hinj : Function.Injective (F.map em.op)) :
    IsPullback (F.map zm.op) (F.map bm.op) (F.map em.op) (F.map dm.op) := by
  have hcomm := congrArg F.map (congrArg Quiver.Hom.op hw)
  simp only [op_comp, Functor.map_comp] at hcomm
  exact Limits.Types.isPullback_of_bijective_snd_of_injective_fst _ _ _ _
    (fun x => ConcreteCategory.congr_hom hcomm x) hbij hinj

/-- If a cartesian square of schemes has a second cartesian square over the same cospan whose
second leg has a section, then the second leg of the first square is injective on sections.

Nothing about the Frobenius is used; the presheaf of sets is arbitrary. -/
public theorem injective_map_op_of_isPullback_of_section (F : Scheme.{u}ᵒᵖ ⥤ Type u)
    {E W Z X X' : Scheme.{u}} {em : E ⟶ Z} {dm : E ⟶ X'} {zm : Z ⟶ X} {bm : X' ⟶ X}
    (hm : IsPullback dm em bm zm)
    {w₁ : W ⟶ X'} {w₂ : W ⟶ Z} (hw : IsPullback w₁ w₂ bm zm)
    (s : Z ⟶ W) (hs : s ≫ w₂ = 𝟙 Z) :
    Function.Injective (F.map em.op) := by
  have hcmp : (hm.isoIsPullback _ _ hw).hom ≫ w₂ = em := hm.isoIsPullback_hom_snd _ _ hw
  have hsplit : F.map w₂.op ≫ F.map s.op = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, ← op_comp, hs, op_id,
      CategoryTheory.Functor.map_id]
  have hfactor : F.map em.op =
      F.map w₂.op ≫ F.map (hm.isoIsPullback _ _ hw).hom.op := by
    rw [← CategoryTheory.Functor.map_comp, ← op_comp, hcmp]
  have hid (a : F.obj (op Z)) : F.map s.op (F.map w₂.op a) = a := by
    simpa using ConcreteCategory.congr_hom hsplit a
  rw [hfactor]
  exact (ConcreteCategory.bijective_of_isIso (F.map (hm.isoIsPullback _ _ hw).hom.op)).1.comp
    (Function.LeftInverse.injective hid)

/-- The intersection of a principal ideal with an ideal annihilated by a power of its generator
is nilpotent. -/
public theorem isNilpotent_principal_inf_of_pow_mul_eq_zero {A : Type u} [CommRing A]
    (f : A) (J : Ideal A) (h : ∃ n : ℕ, ∀ x ∈ J, f ^ n * x = 0) :
    IsNilpotent (Ideal.span {f} ⊓ J) := by
  obtain ⟨n, hn⟩ := h
  have hprod : (Ideal.span {f}) ^ n * J ≤ ⊥ := by
    rw [Ideal.span_singleton_pow]
    apply Ideal.mul_le.mpr
    intro x hx y hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    simp [mul_assoc, hn y hy]
  have hpow : (Ideal.span {f} ⊓ J) ^ (n + 1) ≤ (Ideal.span {f}) ^ n * J := by
    rw [pow_succ]
    exact Ideal.mul_mono (pow_le_pow_left' inf_le_left n) inf_le_right
  exact ⟨n + 1, le_antisymm (hpow.trans hprod) bot_le⟩

/-- A bijective ring map carries the intersection of two ideals to the intersection of their
images. -/
public theorem Ideal.map_inf_of_bijective {R T : Type*} [CommRing R] [CommRing T]
    (f : R →+* T) (hf : Function.Bijective f) (I J : Ideal R) :
    Ideal.map f (I ⊓ J) = Ideal.map f I ⊓ Ideal.map f J := by
  simpa only [Ideal.comap_map_of_bijective f hf] using
    Ideal.map_inf_comap_of_surjective f hf.2 (Ideal.map f I) (Ideal.map f J)

/-- On an affine scheme the kernel of the restriction of global functions to the closed
subscheme cut out by an ideal of global functions is that ideal. -/
public theorem ker_subschemeι_appTop_ofIdealTop {X : Scheme.{u}} [IsAffine X]
    (I : Ideal Γ(X, ⊤)) :
    RingHom.ker ((Scheme.IdealSheafData.ofIdealTop I).subschemeι.appTop).hom = I := by
  have hid (J : Ideal Γ(X, ⊤)) :
      (Scheme.IdealSheafData.ofIdealTop J).ideal ⟨⊤, isAffineOpen_top X⟩ = J :=
    (Scheme.IdealSheafData.equivOfIsAffine (X := X)).apply_symm_apply J
  have h := (Scheme.ker_of_isAffine
      (Scheme.IdealSheafData.ofIdealTop I).subschemeι).symm.trans
    (Scheme.IdealSheafData.ker_subschemeι (Scheme.IdealSheafData.ofIdealTop I))
  have h2 := congrArg (fun D : X.IdealSheafData => D.ideal ⟨⊤, isAffineOpen_top X⟩) h
  rwa [hid, hid] at h2

/-- The kernel of the restriction of global functions along the closed immersion of the spectrum
of a quotient ring is the image of the ideal under the canonical identification of the global
functions of a spectrum with the ring. -/
public theorem ker_quotientSpec_appTop (A : Type u) [CommRing A] (I : Ideal A) :
    RingHom.ker (Scheme.Hom.appTop
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).hom =
      Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom I := by
  have hnat (x : Γ(Spec (.of A), ⊤)) :
      (Scheme.ΓSpecIso (.of (A ⧸ I))).hom.hom
        ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop.hom x) =
      Ideal.Quotient.mk I ((Scheme.ΓSpecIso (.of A)).hom.hom x) :=
    ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk I))) x
  have hhi (x : Γ(Spec (.of A), ⊤)) :
      (Scheme.ΓSpecIso (.of A)).inv.hom ((Scheme.ΓSpecIso (.of A)).hom.hom x) = x :=
    ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of A)).hom_inv_id x
  have hih (a : A) :
      (Scheme.ΓSpecIso (.of A)).hom.hom ((Scheme.ΓSpecIso (.of A)).inv.hom a) = a :=
    ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of A)).inv_hom_id a
  ext x
  rw [RingHom.mem_ker, Ideal.mem_map_iff_of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv).2]
  constructor
  · intro hx
    refine ⟨(Scheme.ΓSpecIso (.of A)).hom.hom x, ?_, hhi x⟩
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← hnat x, hx, map_zero]
  · rintro ⟨a, ha, rfl⟩
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (A ⧸ I))).hom).1
    rw [hnat, hih a, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]

/-! ### The exceptional projective line of the two-generator square -/

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **The exceptional corner of the two-generator square has a section over the centre.** The
exceptional corner is the projective line over the centre, and the point `[1 : 1]` is a section
of it. -/
public theorem exists_section_exceptionalToCenter (A : Type u) [CommRing A] (f₁ f₂ : A) :
    ∃ s : Spec (.of (Stacks.AlmostBlowUp.centerRing A f₁ f₂)) ⟶
      Proj (Stacks.AlmostBlowUp.exceptionalGrading A f₁ f₂),
      s ≫ Stacks.AlmostBlowUp.exceptionalToCenter A f₁ f₂ = 𝟙 _ := by
  let grading := Stacks.AlmostBlowUp.exceptionalGrading A f₁ f₂
  let ev : MvPolynomial (Fin 2) (Stacks.AlmostBlowUp.centerRing A f₁ f₂) →+*
      Γ(Spec (.of (Stacks.AlmostBlowUp.centerRing A f₁ f₂)), ⊤) :=
    MvPolynomial.eval₂Hom
      (Scheme.ΓSpecIso (.of (Stacks.AlmostBlowUp.centerRing A f₁ f₂))).inv.hom (fun _ => 1)
  have hevX : ev (MvPolynomial.X (0 : Fin 2)) = 1 := by simp [ev]
  have hev : (HomogeneousIdeal.irrelevant grading).toIdeal.map ev = ⊤ := by
    have hx : MvPolynomial.X (0 : Fin 2) ∈ (HomogeneousIdeal.irrelevant grading).toIdeal :=
      HomogeneousIdeal.mem_irrelevant_of_mem grading Nat.one_pos
        (MvPolynomial.isHomogeneous_X (Stacks.AlmostBlowUp.centerRing A f₁ f₂) 0)
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem ev hx) (hevX ▸ isUnit_one)
  refine ⟨Proj.fromOfGlobalSections grading ev hev, ?_⟩
  have hcomp : (ev.comp (algebraMap (grading 0)
        (MvPolynomial (Fin 2) (Stacks.AlmostBlowUp.centerRing A f₁ f₂)))).comp
      (Stacks.AlmostBlowUp.twoGeneratorSquare A f₁ f₂).centerMap =
      (Scheme.ΓSpecIso (.of (Stacks.AlmostBlowUp.centerRing A f₁ f₂))).inv.hom := by
    ext a
    show ev ((Stacks.AlmostBlowUp.twoGeneratorSquare A f₁ f₂).centerMap a) = _
    rw [(Stacks.AlmostBlowUp.twoGeneratorSquare A f₁ f₂).centerMap_apply]
    exact MvPolynomial.eval₂_C _ _ _
  show Proj.fromOfGlobalSections grading ev hev ≫
    Proj.toSpecZero grading ≫
      Spec.map (CommRingCat.ofHom
        (Stacks.AlmostBlowUp.twoGeneratorSquare A f₁ f₂).centerMap) = 𝟙 _
  rw [← Category.assoc, Proj.fromOfGlobalSections_toSpecZero, Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, hcomp, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
  simp

/-- **The Frobenius limit square of the model square of Example 0EVH is cartesian.**

Restriction of global functions to the modification is surjective with square-zero kernel — the
two assertions of Stacks 0EVJ, `Stacks.AlmostBlowUp.surjective_Γ_modificationToBase` and
`Stacks.AlmostBlowUp.modificationToBase_ker_sq_eq_bot` — hence bijective on Frobenius limits,
and restriction to the exceptional corner is injective on Frobenius limits because that corner
is the projective line over the centre, which has a section. -/
public theorem isPullback_frobeniusLimit_twoGeneratorModel (p : ℕ) (hp : p.Prime)
    (A : Type u) [CommRing A] (f₁ f₂ : A)
    (hcast : (p : Γ(Spec (.of A), ⊤)) = 0) (E : Scheme.{u}) :
    letI := (Stacks.AlmostBlowUp.twoGeneratorSquare A f₁ f₂).modificationGraded
    ∀ (dm : E ⟶ Proj (Stacks.AlmostBlowUp.modificationGrading A f₁ f₂))
      (em : E ⟶ Spec (.of (Stacks.AlmostBlowUp.centerRing A f₁ f₂))),
      IsPullback em dm (Stacks.AlmostBlowUp.centerToBase A f₁ f₂)
          (Stacks.AlmostBlowUp.modificationToBase A f₁ f₂) →
        IsPullback
          ((frobeniusLimitGlobalSections p).map
            (Stacks.AlmostBlowUp.centerToBase A f₁ f₂).op)
          ((frobeniusLimitGlobalSections p).map
            (Stacks.AlmostBlowUp.modificationToBase A f₁ f₂).op)
          ((frobeniusLimitGlobalSections p).map em.op)
          ((frobeniusLimitGlobalSections p).map dm.op) := by
  let := (Stacks.AlmostBlowUp.twoGeneratorSquare A f₁ f₂).modificationGraded
  intro dm em hm
  have hbij := bijective_frobeniusLimit_of_surjective_of_ker_sq_eq_bot p hp
    (Stacks.AlmostBlowUp.modificationToBase A f₁ f₂) hcast
    (Stacks.AlmostBlowUp.surjective_Γ_modificationToBase A f₁ f₂)
    (Stacks.AlmostBlowUp.modificationToBase_ker_sq_eq_bot A f₁ f₂)
  obtain ⟨s, hs⟩ := exists_section_exceptionalToCenter A f₁ f₂
  exact isPullback_map_op_of_bijective_of_injective (frobeniusLimitGlobalSections p)
    _ _ _ _ hm.w hbij
    (injective_map_op_of_isPullback_of_section (frobeniusLimitGlobalSections p) hm.flip
      (Stacks.AlmostBlowUp.twoGenerator_isPullback A f₁ f₂) s hs)


namespace BigHOver

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The presheaf `lim_F Γ(-, 𝒪)` on the big h category over `S`: the Frobenius limit of the
presheaf of rings of global functions. -/
public abbrev frobeniusLimitSections (p : ℕ) : (BigHOver B S hS)ᵒᵖ ⥤ Type u :=
  Presheaf.frobeniusLimit (sectionsRingPresheaf B S hS) p

/-- The model-pair reduction of `isPullback_map_op_of_modelPair`, for the Frobenius limit sections
on the big h category over `S`. -/
private theorem isPullback_frobeniusLimitSections_of_modelPair (p : ℕ)
    {X X' Z E : BigHOver B S hS} {Xm X'm Zm : Scheme.{u}} (b : X' ⟶ X) (z : Z ⟶ X)
    (d : E ⟶ X') (e : E ⟶ Z) (bm : X'm ⟶ Xm) (zm : Zm ⟶ Xm)
    (hpb : IsPullback ((BigHOver.toScheme B S hS).map e) ((BigHOver.toScheme B S hS).map d)
      ((BigHOver.toScheme B S hS).map z) ((BigHOver.toScheme B S hS).map b))
    (iX : (BigHOver.toScheme B S hS).obj X ≅ Xm) (iX' : (BigHOver.toScheme B S hS).obj X' ≅ X'm)
    (iZ : (BigHOver.toScheme B S hS).obj Z ≅ Zm)
    (hb : (BigHOver.toScheme B S hS).map b ≫ iX.hom = iX'.hom ≫ bm)
    (hz : (BigHOver.toScheme B S hS).map z ≫ iX.hom = iZ.hom ≫ zm)
    (hm : ∀ (dm : (BigHOver.toScheme B S hS).obj E ⟶ X'm)
      (em : (BigHOver.toScheme B S hS).obj E ⟶ Zm), IsPullback em dm zm bm →
      IsPullback ((frobeniusLimitGlobalSections p).map zm.op)
        ((frobeniusLimitGlobalSections p).map bm.op)
        ((frobeniusLimitGlobalSections p).map em.op)
        ((frobeniusLimitGlobalSections p).map dm.op)) :
    IsPullback ((frobeniusLimitSections B S hS p).map z.op)
      ((frobeniusLimitSections B S hS p).map b.op) ((frobeniusLimitSections B S hS p).map e.op)
      ((frobeniusLimitSections B S hS p).map d.op) :=
  isPullback_map_op_of_modelPair (frobeniusLimitGlobalSections p) _ _ _ _ bm zm hpb iX iX' iZ
    hb hz hm

/-- Global functions on the objects of the big h category over `S` satisfy the sheaf condition
for every presieve whose image in the category of schemes generates an fpqc covering sieve:
global functions are the points of the affine line over `ℤ`, and the fpqc topology is
subcanonical. -/
public theorem isSheafFor_globalFunctions_of_fpqc {X : BigHOver B S hS} (R : Presieve X)
    (hR : Sieve.generate (R.map (BigHOver.toScheme B S hS)) ∈
      Scheme.fpqcTopology ((BigHOver.toScheme B S hS).obj X)) :
    Presieve.IsSheafFor (globalFunctions B S hS) R := by
  let := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  have _ : PreservesLimitsOfShape WalkingCospan (BigHOver.toScheme B S hS) := inferInstance
  rw [show globalFunctions B S hS =
    (BigHOver.toScheme B S hS).op ⋙ (Scheme.Γ.{u} ⋙ CategoryTheory.forget CommRingCat.{u}) from
      rfl, Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks]
  exact Stacks.Sites.isSheaf_fpqcTopology_globalSections.isSheafFor _ hR

/-- **Condition (1) of Stacks 0EVI for the Frobenius limit of global functions.** The presheaf
`lim_F Γ(-, 𝒪)` on the big h category over `S` is a sheaf for the Zariski topology. -/
public theorem isZariskiSheaf_frobeniusLimitSections (p : ℕ) :
    BigHOver.IsZariskiSheaf B S hS (frobeniusLimitSections B S hS p) := by
  intro X E hE
  refine Presheaf.isSheafFor_frobeniusLimit p (sectionsRingPresheaf B S hS) _ ?_
  refine isSheafFor_globalFunctions_of_fpqc B S hS E.presieve₀ ?_
  rw [← PreZeroHypercover.presieve₀_map]
  exact Precoverage.generate_mem_toGrothendieck
    (Scheme.zariskiPrecoverage_le_fpqcPrecoverage _ hE)

/-- **Condition (2) of Stacks 0EVI for the Frobenius limit of global functions.** The presheaf
`lim_F Γ(-, 𝒪)` on the big h category over `S` satisfies the sheaf condition for a morphism of
the site with affine target which is flat, proper, surjective and of finite presentation. -/
public theorem isAffineFlatProperFinitePresentationSheaf_frobeniusLimitSections (p : ℕ) :
    BigHOver.IsAffineFlatProperFinitePresentationSheaf B S hS
      (frobeniusLimitSections B S hS p) := by
  intro X Y f _ hflat hproper hsurj hfp
  refine Presheaf.isSheafFor_frobeniusLimit p (sectionsRingPresheaf B S hS) _ ?_
  let g := (BigHOver.toScheme B S hS).map f
  have _ : Flat g := hflat
  have _ : Surjective g := hsurj
  have _ : LocallyOfFinitePresentation g := hfp.1
  refine isSheafFor_globalFunctions_of_fpqc B S hS (Presieve.singleton f) ?_
  rw [Presieve.map_singleton]
  exact Precoverage.generate_mem_toGrothendieck
    (Scheme.fppfPrecoverage_le_fpqcPrecoverage _ (Scheme.Hom.singleton_mem_fppfPrecoverage g))

/-- **Condition (3) of Stacks 0EVI for the Frobenius limit of global functions.** The presheaf
`lim_F Γ(-, 𝒪)` on the big h category over a scheme in characteristic `p` sends an almost blowup
square of the site of the shape of Example 0EVG to a cartesian square of sets.

On the model square the ring square is a pushout with both maps out of `A` surjective, and the
intersection of the two kernels is the nilpotent ideal `fA ⊓ J`. -/
public theorem isOneGeneratorAlmostBlowUpSheaf_frobeniusLimitSections (p : ℕ) (hp : p.Prime)
    (hChar : Stacks.Frobenius.IsInCharacteristic S p) :
    BigHOver.IsOneGeneratorAlmostBlowUpSheaf B S hS (frobeniusLimitSections B S hS p) := by
  intro X X' Z E b z d e I₀ _ _ _ hpb hmodel
  obtain ⟨A, hA, hex⟩ := hmodel
  let := hA
  obtain ⟨f, J, hJ, hann, iX, iX', iZ, hb, hz⟩ := hex
  let D := Scheme.IdealSheafData.ofIdealTop
    (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (Ideal.span {f}))
  apply isPullback_frobeniusLimitSections_of_modelPair B S hS p b z d e
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) D.subschemeι hpb iX iX' iZ hb hz
  intro dm em hm
  have : IsAffine D.subscheme :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine D.subschemeι).1
  have hsurjD := (IsClosedImmersion.isAffine_surjective_of_isAffine D.subschemeι).2
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hsurjJ := (IsClosedImmersion.isAffine_surjective_of_isAffine
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).2
  have hcast : (p : Γ(Spec (.of A), ⊤)) = 0 :=
    natCast_eq_zero_appTop_of_hom iX.inv (natCast_eq_zero_of_isInCharacteristic hChar X)
  apply IsPullback.flip
  apply isPullback_mapMonoidHom_of_isPushout p hp
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop D.subschemeι.appTop
    dm.appTop em.appTop (isPushout_appTop_of_isPullback hm.flip) hsurjJ hsurjD hcast
  rw [ker_quotientSpec_appTop, ker_subschemeι_appTop_ofIdealTop (X := Spec (.of A)),
    ← Ideal.map_inf_of_bijective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv)]
  obtain ⟨power, hpower⟩ := isNilpotent_principal_inf_of_pow_mul_eq_zero f J hann
  exact ⟨power, by rw [← Ideal.map_pow, inf_comm J, hpower]; exact Ideal.map_bot⟩

/-- **Condition (4) of Stacks 0EVI for the Frobenius limit of global functions.** The presheaf
`lim_F Γ(-, 𝒪)` on the big h category over a scheme in characteristic `p` sends an almost blowup
square of the site of the shape of Example 0EVH to a cartesian square of sets.

On the model square the restriction of global functions to the modification is surjective with
square-zero kernel, which is Stacks 0EVJ, so it is bijective on Frobenius limits, and the
restriction to the exceptional corner is injective on Frobenius limits because that corner is
the projective line over the centre and so has a section over it.  A commuting square with
bijective left edge and injective right edge is cartesian. -/
public theorem isTwoGeneratorAlmostBlowUpSheaf_frobeniusLimitSections (p : ℕ) (hp : p.Prime)
    (hChar : Stacks.Frobenius.IsInCharacteristic S p) :
    BigHOver.IsTwoGeneratorAlmostBlowUpSheaf B S hS (frobeniusLimitSections B S hS p) := by
  intro X X' Z E b z d e I₀ _ _ _ hpb hmodel
  obtain ⟨A, hA, hex⟩ := hmodel
  let := hA
  obtain ⟨f₁, f₂, iX, iX', iZ, hb, hz⟩ := hex
  let := (Stacks.AlmostBlowUp.twoGeneratorSquare A f₁ f₂).modificationGraded
  exact isPullback_frobeniusLimitSections_of_modelPair B S hS p b z d e
    (Stacks.AlmostBlowUp.modificationToBase A f₁ f₂)
    (Stacks.AlmostBlowUp.centerToBase A f₁ f₂) hpb iX iX' iZ hb hz
    (isPullback_frobeniusLimit_twoGeneratorModel p hp A f₁ f₂
      (natCast_eq_zero_appTop_of_hom iX.inv (natCast_eq_zero_of_isInCharacteristic hChar X))
      ((BigHOver.toScheme B S hS).obj E))

/-- **Stacks 0EVL**, with the inputs this development lacks carried as explicit hypotheses: the
rule `X ↦ lim_F Γ(X, 𝒪_X)` is a sheaf on the big h site over a scheme in characteristic `p`.

The four conditions of the h sheaf criterion Stacks 0EVI hold for this presheaf —
`AlgebraicGeometry.BigHOver.isZariskiSheaf_frobeniusLimitSections`,
`AlgebraicGeometry.BigHOver.isAffineFlatProperFinitePresentationSheaf_frobeniusLimitSections`,
`AlgebraicGeometry.BigHOver.isOneGeneratorAlmostBlowUpSheaf_frobeniusLimitSections` and
`AlgebraicGeometry.BigHOver.isTwoGeneratorAlmostBlowUpSheaf_frobeniusLimitSections`, the last of
all four unconditional and at the source's own hypotheses — and that is the whole content of the
source's proof.  What is carried is everything else: `hcrit` and `hind` are the two unproved
inputs of the sufficiency direction of the criterion.

It carries no `@[stacks 0EVL]` attribute, because nothing here proves the sheaf property: once
`hcrit` and `hind` are discharged this statement is Stacks 0EVL, and nothing else is needed. -/
public theorem isSheaf_frobeniusLimitSections_of_criterion
    (hcrit : AffineAlmostBlowUpHSheafCriterion.{u, u})
    (hind : GeneratorAlmostBlowUpSquaresSuffice.{u, u})
    (p : ℕ) (hp : p.Prime) (hChar : Stacks.Frobenius.IsInCharacteristic S p) :
    Presheaf.IsSheaf (BigHOver.topology B S hS) (frobeniusLimitSections B S hS p) :=
  (BigHOver.isSheaf_iff_zariski_and_affineFlatProperFP_and_generatorSquares hcrit hind
      B S hS (frobeniusLimitSections B S hS p)).2
    ⟨isZariskiSheaf_frobeniusLimitSections B S hS p,
      isAffineFlatProperFinitePresentationSheaf_frobeniusLimitSections B S hS p,
      isOneGeneratorAlmostBlowUpSheaf_frobeniusLimitSections B S hS p hp hChar,
      isTwoGeneratorAlmostBlowUpSheaf_frobeniusLimitSections B S hS p hp hChar⟩

end BigHOver

end AlgebraicGeometry

end
