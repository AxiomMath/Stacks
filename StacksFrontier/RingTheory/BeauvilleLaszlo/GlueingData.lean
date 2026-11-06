module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Module
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.FlatModuleSheavesAndStalks
public import StacksFrontier.RingTheory.BeauvilleLaszlo.TorVanishing

@[expose] public section

/-!
# Exactness properties of a glueing datum

A *glueing datum* for a ring map `R → R'` and an element `f : R` consists of an `R'`-module
`M'`, an `R_f`-module `M₁`, and an isomorphism `α₁ : (M')_f ≅ M₁ ⊗[R] R'`; the `R`-module it
glues to is `M = ker(d)` for the difference map
`d : M' ⊕ M₁ → (M')_f`, `(x, y) ↦ x/1 - α₁⁻¹(y ⊗ 1)`.
This file proves the exactness statements that the proof of the Beauville--Laszlo theorem
extracts from such a datum: that `d` is surjective, that projection to `M₁` presents
`M₁` as an extension of `(M')_f/M'` by `M/M[f^∞]`, and that this extension stays exact after
extending scalars to `R'`.

## Main definitions

* `AwayCokernel R S f M'` is the cokernel `(M')_f / M'` of the canonical localization map of
  an `S`-module `M'`, localized away from the image of `f`.

## Main results

* `gluingDatum_difference_shortExact_of_quotientMap_surjective` (Stacks 0BP3): `d` is
  surjective, so `0 → M → M' ⊕ M₁ → (M')_f → 0` is a short exact sequence of `R`-modules.
  Only surjectivity of `R/fⁿR → R'/fⁿR'` for `n > 0` is needed, which a glueing pair
  supplies.
* `exists_exact_quotient_powerTorsion` (Stacks 0BP4): if `A → L` is localization away from
  `f`, the difference map `A × B → L` is surjective and `f` acts injectively on `B`, then for
  `M` the kernel of the difference map the projection to `B` induces an exact sequence
  `0 → M/M[f^∞] → B → L/range(A → L) → 0`, and the map out of `M/M[f^∞]` is uniquely
  determined by its compatibility with the projection.
* `gluingDatum_baseChange_localizationQuotient_shortExact` (Stacks 0BP5): the `R'`-base
  change of the previous sequence is again short exact, i.e.
  `0 → (M/M[f^∞]) ⊗_R R' → (M')_f → (M')_f/M' → 0`.

## Implementation notes

Both statements are formulated for the bare module-theoretic data rather than for the glueing
category, so that they can be applied to a glueing datum without first choosing an object of
that category: Stacks 0BP3 takes `M'`, `M₁` and `α₁` as explicit arguments, and Stacks 0BP4 is
stated for an arbitrary localization-away map `g : A →ₗ[R] L` (via `IsLocalizedModule.Away`)
and an arbitrary `h : B →ₗ[R] L`. The localization `(M')_f` is
`LocalizedModule.Away (algebraMap R R' f) M'`, and the base change `M₁ ⊗[R] R'` is
`TensorProduct R R' M₁`.

Stacks 0BP4 is stated existentially in the induced map `M/M[f^∞] → B`, together with the
compatibility that pins it down, rather than by naming a construction; this keeps the
statement independent of any choice of representative for the quotient. Stacks 0BP5 is stated
the same way, so that it also records the canonical construction of the left-hand map rather
than only the existence of some exact sequence with isomorphic terms.

The only nontrivial input to Stacks 0BP5 is the vanishing of `Tor₁ᴿ(R', (M')_f/M')`
(Stacks 0BP1), which makes the left-hand map stay injective after base change; the right-hand
term is `f`-power torsion, so base change does not change it (Stacks 0BNK).

## References

* [Beauville--Laszlo]
* [Stacks Project, Tag 0BP3](https://stacks.math.columbia.edu/tag/0BP3)
* [Stacks Project, Tag 0BP4](https://stacks.math.columbia.edu/tag/0BP4)
* [Stacks Project, Tag 0BP5](https://stacks.math.columbia.edu/tag/0BP5)
-/

namespace BeauvilleLaszlo
section

universe u v w x

end

section

universe u v w x

/-- An equivalence of `S`-modules sends `s ⊗ y` to `s` times the image of `1 ⊗ y`. -/
private theorem symm_tmul_eq_smul_symm_one_tmul
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    {N : Type w} [AddCommGroup N] [Module S N] {M₁ : Type x} [AddCommGroup M₁] [Module R M₁]
    (α : N ≃ₗ[S] TensorProduct R S M₁) (s : S) (y : M₁) :
    α.symm (s ⊗ₜ[R] y) = s • α.symm (1 ⊗ₜ[R] y) := by
  rw [← α.symm.map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The kernel of the difference map attached to a gluing datum fits into the short exact
sequence `0 → ker(d) → M' × M₁ → M'ₑ → 0`.

Here the difference map sends `(x, y)` to `x / 1 - α⁻¹(1 ⊗ y)`. It is surjective as
soon as `R → S` is surjective modulo every positive power of `f`; in particular the result
applies to a Beauville--Laszlo gluing pair. -/
@[stacks 0BP3]
public theorem gluingDatum_difference_shortExact_of_quotientMap_surjective
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (f : R)
    (hmod : ∀ n : ℕ, 0 < n →
      Function.Surjective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) ((Ideal.span {f}) ^ n))
          (algebraMap R S) Ideal.le_comap_map))
    (M' : Type w) [AddCommGroup M'] [Module R M'] [Module S M']
    [IsScalarTower R S M']
    (M₁ : Type x) [AddCommGroup M₁] [Module R M₁]
    [Module (Localization.Away f) M₁] [IsScalarTower R (Localization.Away f) M₁]
    (α : LocalizedModule.Away (algebraMap R S f) M' ≃ₗ[S]
      TensorProduct R S M₁) :
    let localizationMap : M' →ₗ[R] LocalizedModule.Away (algebraMap R S f) M' :=
      (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S f)) M').restrictScalars R
    let tensorMap : M₁ →ₗ[R] TensorProduct R S M₁ := TensorProduct.mk R S M₁ 1
    let d : (M' × M₁) →ₗ[R] LocalizedModule.Away (algebraMap R S f) M' :=
      localizationMap.comp (LinearMap.fst R M' M₁) -
        ((α.symm.toLinearMap.restrictScalars R).comp tensorMap).comp
          (LinearMap.snd R M' M₁)
    Function.Injective (LinearMap.ker d).subtype ∧
      Function.Exact (LinearMap.ker d).subtype d ∧
        Function.Surjective d := by
  dsimp only
  let loc : M' →ₗ[R] LocalizedModule.Away (algebraMap R S f) M' :=
    (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S f)) M').restrictScalars R
  let tm : M₁ →ₗ[R] TensorProduct R S M₁ := TensorProduct.mk R S M₁ 1
  let d : (M' × M₁) →ₗ[R] LocalizedModule.Away (algebraMap R S f) M' :=
    loc.comp (LinearMap.fst R M' M₁) -
      ((α.symm.toLinearMap.restrictScalars R).comp tm).comp (LinearMap.snd R M' M₁)
  refine ⟨Submodule.subtype_injective _, LinearMap.exact_subtype_ker_map d, ?_⟩
  intro z
  suffices h : ∀ t : TensorProduct R S M₁, ∃ p : M' × M₁, d p = α.symm t by
    simpa [d, loc, tm] using h (α z)
  intro t
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨(0, 0), by simp [d]⟩
  | add t₁ t₂ h₁ h₂ =>
      obtain ⟨p₁, hp₁⟩ := h₁
      obtain ⟨p₂, hp₂⟩ := h₂
      exact ⟨p₁ + p₂, by simp [hp₁, hp₂]⟩
  | tmul s y =>
      generalize hv : α.symm (1 ⊗ₜ y) = v
      induction v using LocalizedModule.induction_on with
      | h m q =>
        obtain ⟨n, hn⟩ := q.property
        by_cases hn0 : n = 0
        · subst n
          have hq : q = 1 := Subtype.ext (by simpa using hn.symm)
          subst q
          refine ⟨(s • m, 0), ?_⟩
          rw [symm_tmul_eq_smul_symm_one_tmul]
          simpa [d, loc, tm] using congrArg (s • ·) hv.symm
        · obtain ⟨a, ha⟩ :=
            hmod n (Nat.pos_of_ne_zero hn0) (Ideal.Quotient.mk _ s)
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
          obtain ⟨b, hb⟩ : ∃ b : S, s = algebraMap R S a + (algebraMap R S f) ^ n * b := by
            rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at ha
            rw [Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton,
              Ideal.mem_span_singleton] at ha
            obtain ⟨c, hc⟩ := ha
            refine ⟨-c, ?_⟩
            rw [map_pow] at hc
            rw [mul_neg, ← sub_eq_add_neg, ← hc]
            simp
          refine ⟨(b • m, -(algebraMap R (Localization.Away f) a) • y), ?_⟩
          have hcancel : b • LocalizedModule.mk m 1 =
              ((q : S) * b) • LocalizedModule.mk m q := by
            rw [LocalizedModule.smul'_mk, LocalizedModule.smul'_mk, mul_smul]
            exact (LocalizedModule.mk_cancel q (b • m)).symm
          have halpha : α.symm (1 ⊗ₜ[R] (-(algebraMap R (Localization.Away f) a) • y)) =
              -(a • LocalizedModule.mk m q) := by
            rw [neg_smul, TensorProduct.tmul_neg, map_neg, algebraMap_smul,
              TensorProduct.tmul_smul]
            congr 1
            rw [← algebraMap_smul S a (1 ⊗ₜ[R] y)]
            rw [α.symm.map_smul, hv, algebraMap_smul]
          rw [symm_tmul_eq_smul_symm_one_tmul, hv, hb]
          simp only [d, loc, tm, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply,
            LinearMap.snd_apply, LinearMap.coe_restrictScalars, LocalizedModule.mkLinearMap_apply,
            tm, add_smul, hn]
          change LocalizedModule.mk (b • m) 1 -
              α.symm (1 ⊗ₜ[R] (-(algebraMap R (Localization.Away f) a) • y)) = _
          rw [← LocalizedModule.smul'_mk, halpha, sub_neg_eq_add, hcancel, algebraMap_smul]
          exact add_comm _ _

end

section

universe u v w x

variable {R : Type u} {A : Type v} {B : Type w} {L : Type x}
  [CommRing R] [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup L] [Module R L]

end

section

universe u v w x

variable {R : Type u} {A : Type v} {B : Type w} {L : Type x}
  [CommRing R] [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup L] [Module R L]

/-- Suppose `A → L` is localization away from `f`, the difference map
`A × B → L`, `(a, b) ↦ g a - h b`, is surjective, and multiplication by `f` is
injective on `B`. If `M` is the kernel of the difference map, projection to `B` induces
the canonical short exact sequence
`0 → M / M[f^∞] → B → L / range(g) → 0`.

The displayed compatibility uniquely specifies the induced left-hand map. -/
@[stacks 0BP4]
public theorem exists_exact_quotient_powerTorsion
    (f : R) (g : A →ₗ[R] L) [IsLocalizedModule.Away f g] (h : B →ₗ[R] L)
    (hd : Function.Surjective
      (g.comp (LinearMap.fst R A B) - h.comp (LinearMap.snd R A B)))
    (hf : Function.Injective (fun b : B ↦ f • b)) :
    let d := g.comp (LinearMap.fst R A B) - h.comp (LinearMap.snd R A B)
    let M := LinearMap.ker d
    let T := Submodule.torsion' R M (Submonoid.powers f)
    let q := (Submodule.mkQ (LinearMap.range g)).comp h
    ∃ i : (M ⧸ T) →ₗ[R] B,
      (∀ m : M, i (Submodule.mkQ T m) = m.1.2) ∧
        Function.Injective i ∧ LinearMap.range i = LinearMap.ker q ∧
          Function.Surjective q := by
  dsimp only
  let d := g.comp (LinearMap.fst R A B) - h.comp (LinearMap.snd R A B)
  let M := LinearMap.ker d
  let T := Submodule.torsion' R M (Submonoid.powers f)
  let p : M →ₗ[R] B := (LinearMap.snd R A B).comp (LinearMap.ker d).subtype
  let q := (Submodule.mkQ (LinearMap.range g)).comp h
  have hf_pow (n : ℕ) : Function.Injective (fun b : B ↦ f ^ n • b) := by
    induction n with
    | zero => intro a b hab; simpa using hab
    | succ n ihn =>
        intro a b hab
        apply ihn
        apply hf
        simpa [pow_succ', mul_smul] using hab
  have hker : LinearMap.ker p = T := by
    apply le_antisymm
    · intro m hm
      rw [LinearMap.mem_ker] at hm
      change m.1.2 = 0 at hm
      rw [Submodule.mem_torsion'_iff]
      obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f)
        (f := g) (show g m.1.1 = g 0 by
          have hmM := m.2
          change g m.1.1 - h m.1.2 = 0 at hmM
          simpa [p, hm] using hmM)
      exact ⟨s, by
        apply Subtype.ext
        apply Prod.ext
        · simpa using hs
        · simp [hm]⟩
    · intro m hm
      rw [Submodule.mem_torsion'_iff] at hm
      obtain ⟨s, hs⟩ := hm
      obtain ⟨n, hn⟩ := s.2
      rw [LinearMap.mem_ker]
      apply hf_pow n
      simpa [p, hn, Submonoid.smul_def] using congr_arg (fun z : M ↦ z.1.2) hs
  have hpq : LinearMap.range p = LinearMap.ker q := by
    ext b
    constructor
    · rintro ⟨m, rfl⟩
      rw [LinearMap.mem_ker]
      change Submodule.mkQ (LinearMap.range g) (h m.1.2) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      refine ⟨m.1.1, ?_⟩
      have hm := m.2
      change g m.1.1 - h m.1.2 = 0 at hm
      simpa [p] using sub_eq_zero.mp hm
    · intro hb
      rw [LinearMap.mem_ker] at hb
      change Submodule.mkQ (LinearMap.range g) (h b) = 0 at hb
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hb
      obtain ⟨a, ha⟩ := hb
      refine ⟨⟨(a, b), ?_⟩, rfl⟩
      change g a - h b = 0
      exact sub_eq_zero.mpr ha
  have hq : Function.Surjective q := by
    intro z
    obtain ⟨l, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range g) z
    obtain ⟨⟨a, b⟩, hab⟩ := hd l
    refine ⟨-b, ?_⟩
    change Submodule.mkQ (LinearMap.range g) (h (-b)) =
      Submodule.mkQ (LinearMap.range g) l
    apply (Submodule.Quotient.eq _).2
    refine ⟨-a, ?_⟩
    change g (-a) = h (-b) - l
    change g a - h b = l at hab
    rw [map_neg, map_neg]
    calc
      -g a = -(l + h b) := congrArg Neg.neg (sub_eq_iff_eq_add.mp hab)
      _ = -h b - l := by abel
  let i : (M ⧸ T) →ₗ[R] B := T.liftQ p (hker ▸ le_rfl)
  refine ⟨i, fun _ => rfl, ?_, ?_, hq⟩
  · exact LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ hker.le)
  · change LinearMap.range (T.liftQ p _) = LinearMap.ker q
    rw [Submodule.range_liftQ]
    exact hpq

end

section

open CategoryTheory
open scoped TensorProduct

universe u v w x

/-- The quotient `(M')_f / M'` by the image of the canonical localization map. -/
public abbrev AwayCokernel (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] (f : R) (M' : Type w) [AddCommGroup M'] [Module S M'] :=
  LocalizedModule.Away (algebraMap R S f) M' ⧸
    LinearMap.range
      (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S f)) M')

end

section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

/-- If `Tor₁ᴿ(S, coker f) = 0` for an injective map `f : A → B`, then `- ⊗[R] S` keeps `f`
injective. -/
private theorem rTensor_injective_of_isZero_tor_coker
    (R : Type u) [CommRing R]
    {S A B : Type u} [AddCommGroup S] [Module R S]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (hf : Function.Injective f)
    (h : IsZero (((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R S)).obj
      (ModuleCat.of R (B ⧸ LinearMap.range f)))) :
    Function.Injective (LinearMap.rTensor S f) := by
  let fm : ModuleCat.of R A ⟶ ModuleCat.of R B := ModuleCat.ofHom f
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
    (MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R S)
  let e := ModuleCat.cokernelIsoRangeQuotient fm
  have : Mono fm := (ModuleCat.mono_iff_injective _).2 hf
  have hc : IsZero ((F.leftDerived 1).obj (cokernel fm)) := by
    dsimp [F, fm] at e ⊢
    exact IsZero.of_iso h (((Tor (ModuleCat.{u} R) 1).obj
      (ModuleCat.of R S)).mapIso e)
  have hm0 : Mono ((F.leftDerived 0).map fm) :=
    OXModule.additive_mono_of_isZero_leftDerived_one R F fm hc
  let e0 : F.leftDerived 0 ≅ F := Functor.leftDerivedZeroIsoSelf F
  have hm : Mono (F.map fm) := by
    rw [← IsIso.inv_hom_id_assoc (e0.hom.app (ModuleCat.of R A)) (F.map fm),
      ← e0.hom.naturality fm]
    infer_instance
  intro x y hxy
  apply (TensorProduct.comm R A S).injective
  apply (ModuleCat.mono_iff_injective (F.map fm)).1 hm
  have hnat : (TensorProduct.map (LinearMap.id (R := R) (M := S)) f).comp
      (TensorProduct.comm R A S).toLinearMap =
      (TensorProduct.comm R B S).toLinearMap.comp (LinearMap.rTensor S f) := by
    ext a s
    simp
  change ((TensorProduct.map (LinearMap.id (R := R) (M := S)) f).comp
      (TensorProduct.comm R A S).toLinearMap) x =
    ((TensorProduct.map (LinearMap.id (R := R) (M := S)) f).comp
      (TensorProduct.comm R A S).toLinearMap) y
  rw [hnat]
  exact congrArg (TensorProduct.comm R B S) hxy

universe uR uS uA uB uC

/-- The universe-independent form of `rTensor_injective_of_isZero_tor_coker`: the Tor
hypothesis is imposed on the canonical `ULift` copies of the data. -/
private theorem rTensor_injective_of_isZero_tor_of_exact
    {R : Type uR} [CommRing R]
    {S : Type uS} [AddCommGroup S] [Module R S]
    {A : Type uA} [AddCommGroup A] [Module R A]
    {B : Type uB} [AddCommGroup B] [Module R B]
    {C : Type uC} [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hex : Function.Exact f g)
    (hg : Function.Surjective g)
    (h : IsZero (((Tor (ModuleCat.{max uR uS uA uB uC}
      (ULift.{max uR uS uA uB uC} R)) 1).obj
      (ModuleCat.of _ (ULift.{max uR uS uA uB uC} S))).obj
      (ModuleCat.of _ (ULift.{max uR uS uA uB uC} C)))) :
    Function.Injective (LinearMap.rTensor S f) := by
  let R' := ULift.{max uR uS uA uB uC} R
  let S' := ULift.{max uR uS uA uB uC} S
  let A' := ULift.{max uR uS uA uB uC} A
  let B' := ULift.{max uR uS uA uB uC} B
  let C' := ULift.{max uR uS uA uB uC} C
  let f' : A' →ₗ[R'] B' :=
    ULift.moduleEquiv.symm.toLinearMap.comp
      ((f.restrictScalars R').comp ULift.moduleEquiv.toLinearMap)
  let g' : B' →ₗ[R'] C' :=
    ULift.moduleEquiv.symm.toLinearMap.comp
      ((g.restrictScalars R').comp ULift.moduleEquiv.toLinearMap)
  have hf' : Function.Injective f' := fun x y hxy ↦
    ULift.ext (hf (congrArg ULift.down hxy))
  have hg' : Function.Surjective g' := by
    intro z
    obtain ⟨y, hy⟩ := hg z.down
    exact ⟨ULift.up y, ULift.ext hy⟩
  have hex' : Function.Exact f' g' := by
    intro y
    change ULift.up (g y.down) = (0 : C') ↔ ∃ x : A', ULift.up (f x.down) = y
    constructor
    · intro hy
      obtain ⟨x, hx⟩ := (hex y.down).mp (congrArg ULift.down hy)
      exact ⟨ULift.up x, ULift.ext hx⟩
    · rintro ⟨x, hx⟩
      exact ULift.ext ((hex y.down).mpr ⟨x.down, congrArg ULift.down hx⟩)
  let e : (B' ⧸ LinearMap.range f') ≃ₗ[R'] C' :=
    (Submodule.quotEquivOfEq _ _ (LinearMap.exact_iff.mp hex').symm).trans
      (g'.quotKerEquivOfSurjective hg')
  have ht : IsZero (((Tor (ModuleCat R') 1).obj (ModuleCat.of R' S')).obj
      (ModuleCat.of R' (B' ⧸ LinearMap.range f'))) :=
    h.of_iso (((Tor (ModuleCat R') 1).obj (ModuleCat.of R' S')).mapIso
      e.toModuleIso)
  have hinj := rTensor_injective_of_isZero_tor_coker R' f' hf' ht
  let ea : ULift.{max uR uS uA uB uC} (A ⊗[R] S) ≃ₗ[R] A' ⊗[R'] S' :=
    TensorProduct.AlgebraTensorModule.uliftEquiv R R A S
  let eb : ULift.{max uR uS uA uB uC} (B ⊗[R] S) ≃ₗ[R] B' ⊗[R'] S' :=
    TensorProduct.AlgebraTensorModule.uliftEquiv R R B S
  have hn : ((LinearMap.rTensor S' f').restrictScalars R).comp
      (ea.toLinearMap.comp ULift.moduleEquiv.symm.toLinearMap) =
      (eb.toLinearMap.comp ULift.moduleEquiv.symm.toLinearMap).comp
        (LinearMap.rTensor S f) := by
    ext a s
    rfl
  intro x y hxy
  exact ULift.up_injective <| ea.injective <| hinj <| (LinearMap.congr_fun hn x).trans
    ((congrArg (fun z => eb (ULift.up z)) hxy).trans (LinearMap.congr_fun hn y).symm)

/-- Localization cokernels of isomorphic modules at the same submonoid are isomorphic. -/
private theorem nonempty_localizationCokernel_equiv
    {R : Type*} [CommRing R] (W : Submonoid R)
    {A B L K : Type*} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup L] [Module R L]
    [AddCommGroup K] [Module R K]
    (g : A →ₗ[R] L) (h : B →ₗ[R] K)
    [IsLocalizedModule W g] [IsLocalizedModule W h] (e : A ≃ₗ[R] B) :
    Nonempty ((L ⧸ LinearMap.range g) ≃ₗ[R] (K ⧸ LinearMap.range h)) := by
  let m := IsLocalizedModule.map W g h e.toLinearMap
  let l : L ≃ₗ[R] K := LinearEquiv.ofBijective m
    ⟨IsLocalizedModule.map_injective W g h e.toLinearMap e.injective,
      IsLocalizedModule.map_surjective W g h e.toLinearMap e.surjective⟩
  have hr : (LinearMap.range g).map l.toLinearMap = LinearMap.range h := by
    rw [← LinearMap.range_comp]
    change LinearMap.range (m.comp g) = LinearMap.range h
    rw [IsLocalizedModule.map_comp]
    exact LinearMap.range_comp_of_range_eq_top _ e.range
  exact ⟨Submodule.Quotient.equiv _ _ l hr⟩

universe uM uM₁

set_option maxHeartbeats 2000000 in
-- The identifications of lifted rings and modules require extra definitional reduction.
/-- Let `(R → S, f)` be a Beauville--Laszlo glueing pair and let `(M', M₁, α)` be a
glueing datum. If `M` is the kernel of
`M' × M₁ → (M')_f`, `(x, y) ↦ x / 1 - α⁻¹(y ⊗ 1)`, projection to `M₁`
induces a map `i : M / M[f^∞] → M₁`. After extending `i` to `S` and using
`α`, it is the left map of the canonical short exact sequence
`0 → (M / M[f^∞]) ⊗_R S → (M')_f → (M')_f / M' → 0`.

The first displayed condition characterizes the induced map `i`; thus the assertion
also records the canonical construction, rather than only the existence of some exact
sequence with isomorphic terms. -/
@[stacks 0BP5]
public theorem gluingDatum_baseChange_localizationQuotient_shortExact
    (R : Type uR) [CommRing R] (S : Type uS) [CommRing S] [Algebra R S]
    (f : R)
    (hmod : ∀ n : ℕ, 0 < n →
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) ((Ideal.span {f}) ^ n))
          (algebraMap R S) Ideal.le_comap_map))
    (hglue : (beauvilleLaszloSequence f (algebraMap R S)).ShortExact)
    (M' : Type uM) [AddCommGroup M'] [Module R M'] [Module S M']
    [IsScalarTower R S M']
    (M₁ : Type uM₁) [AddCommGroup M₁] [Module R M₁]
    [Module (Localization.Away f) M₁] [IsScalarTower R (Localization.Away f) M₁]
    (α : LocalizedModule.Away (algebraMap R S f) M' ≃ₗ[S]
      TensorProduct R S M₁) :
    let localizationMap : M' →ₗ[R] LocalizedModule.Away (algebraMap R S f) M' :=
      (LocalizedModule.mkLinearMap
        (Submonoid.powers (algebraMap R S f)) M').restrictScalars R
    let tensorMap : M₁ →ₗ[R] TensorProduct R S M₁ :=
      TensorProduct.mk R S M₁ 1
    let d : (M' × M₁) →ₗ[R] LocalizedModule.Away (algebraMap R S f) M' :=
      localizationMap.comp (LinearMap.fst R M' M₁) -
        ((α.symm.toLinearMap.restrictScalars R).comp tensorMap).comp
          (LinearMap.snd R M' M₁)
    let M := LinearMap.ker d
    let T := Submodule.torsion' R M (Submonoid.powers f)
    let q : LocalizedModule.Away (algebraMap R S f) M' →ₗ[R]
        AwayCokernel R S f M' :=
      ((LinearMap.range
        (LocalizedModule.mkLinearMap
          (Submonoid.powers (algebraMap R S f)) M')).mkQ).restrictScalars R
    ∃ i : (M ⧸ T) →ₗ[R] M₁,
      (∀ m : M, i (Submodule.mkQ T m) = m.1.2) ∧
        let iS :=
          (TensorProduct.map (LinearMap.id (R := R) (M := S)) i).comp
            (TensorProduct.comm R (M ⧸ T) S).toLinearMap
        let a := (α.symm.toLinearMap.restrictScalars R).comp iS
        Function.Injective a ∧ Function.Exact a q ∧ Function.Surjective q := by
  dsimp only
  let loc : M' →ₗ[R] LocalizedModule.Away (algebraMap R S f) M' :=
    (LocalizedModule.mkLinearMap
      (Submonoid.powers (algebraMap R S f)) M').restrictScalars R
  let tm : M₁ →ₗ[R] TensorProduct R S M₁ := TensorProduct.mk R S M₁ 1
  let h : M₁ →ₗ[R] LocalizedModule.Away (algebraMap R S f) M' :=
    (α.symm.toLinearMap.restrictScalars R).comp tm
  let d : (M' × M₁) →ₗ[R] LocalizedModule.Away (algebraMap R S f) M' :=
    loc.comp (LinearMap.fst R M' M₁) - h.comp (LinearMap.snd R M' M₁)
  let M := LinearMap.ker d
  let T := Submodule.torsion' R M (Submonoid.powers f)
  let q : LocalizedModule.Away (algebraMap R S f) M' →ₗ[R] AwayCokernel R S f M' :=
    ((LinearMap.range (LocalizedModule.mkLinearMap
      (Submonoid.powers (algebraMap R S f)) M')).mkQ).restrictScalars R
  change ∃ i : (M ⧸ T) →ₗ[R] M₁,
    (∀ m : M, i (Submodule.mkQ T m) = m.1.2) ∧
      Function.Injective ((α.symm.toLinearMap.restrictScalars R).comp
        ((TensorProduct.map (LinearMap.id (R := R) (M := S)) i).comp
          (TensorProduct.comm R (M ⧸ T) S).toLinearMap)) ∧
      Function.Exact ((α.symm.toLinearMap.restrictScalars R).comp
        ((TensorProduct.map (LinearMap.id (R := R) (M := S)) i).comp
          (TensorProduct.comm R (M ⧸ T) S).toLinearMap)) q ∧ Function.Surjective q
  have hd : Function.Surjective d := by
    simpa [d, loc, h, tm] using
      (gluingDatum_difference_shortExact_of_quotientMap_surjective
        R S f (fun n hn => (hmod n hn).2)
        M' M₁ α).2.2
  have hf : Function.Injective (fun z : M₁ ↦ f • z) := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away f) f).smul_eq_zero.mp
    simpa [smul_sub, sub_eq_zero, IsScalarTower.algebraMap_smul] using hxy
  let : IsLocalizedModule.Away f loc :=
    IsLocalizedModule.restrictScalars_powers f
      (LocalizedModule.mkLinearMap
        (Submonoid.powers (algebraMap R S f)) M')
  obtain ⟨i, hi, hii, hir, hqs⟩ :=
    exists_exact_quotient_powerTorsion f loc h hd hf
  change (M ⧸ T) →ₗ[R] M₁ at i
  change ∀ m : M, i (Submodule.mkQ T m) = m.1.2 at hi
  let locS : M' →ₗ[S] LocalizedModule.Away (algebraMap R S f) M' :=
    LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S f)) M'
  have hRange : LinearMap.range loc = (LinearMap.range locS).restrictScalars R := by
    ext x
    rfl
  let eQ : (LocalizedModule.Away (algebraMap R S f) M' ⧸ LinearMap.range loc) ≃ₗ[R]
      AwayCokernel R S f M' :=
    (Submodule.quotEquivOfEq _ _ hRange).trans
      (Submodule.Quotient.restrictScalarsEquiv R (LinearMap.range locS))
  have hmod' : ∀ n : ℕ, 0 < n →
      Function.Bijective (quotientPowMap f n (algebraMap R S)) := by
    intro n hn
    have he : Ideal.map (algebraMap R S) ((Ideal.span {f}) ^ n) =
        (Ideal.span {(algebraMap R S) f}) ^ n := by
      rw [Ideal.map_pow, Ideal.map_span]
      simp
    let e := Ideal.quotEquivOfEq he
    have heq : quotientPowMap f n (algebraMap R S) =
        e.toRingHom.comp
          (Ideal.quotientMap
            (Ideal.map (algebraMap R S) ((Ideal.span {f}) ^ n))
            (algebraMap R S) Ideal.le_comap_map) := by
      refine RingHom.ext fun x => ?_
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [quotientPowMap_mk]
      change Ideal.Quotient.mk _ ((algebraMap R S) r) =
        (Ideal.quotEquivOfEq he) (Ideal.Quotient.mk _ ((algebraMap R S) r))
      exact (Ideal.quotEquivOfEq_mk he _).symm
    rw [heq]
    exact e.bijective.comp (hmod n hn)
  let locU := LocalizedModule.mkLinearMap (Submonoid.powers f) (ULift.{uM₁} M')
  obtain ⟨eU⟩ := nonempty_localizationCokernel_equiv (Submonoid.powers f)
    locU loc (ULift.moduleEquiv : ULift.{uM₁} M' ≃ₗ[R] M')
  let eC := eU.trans eQ
  let g : M₁ →ₗ[R] AwayCokernel R S f M' := q.comp h
  have hg : Function.Surjective g := eQ.surjective.comp hqs
  have hex : Function.Exact i g := by
    intro y
    have he : g y = eQ (((LinearMap.range loc).mkQ.comp h) y) := rfl
    rw [he, ← eQ.map_zero, eQ.injective.eq_iff]
    exact (LinearMap.exact_iff.mpr hir.symm) y
  have hBase :=
    isZero_Tor_one_coker_localizationMap_of_beauvilleLaszlo_shortExact
      (M := ULift.{uM₁} M') f (algebraMap R S) hmod' hglue
  let RU := ULift.{max uR uS uM uM₁} R
  let SU := ULift.{max uR uS uM uM₁} S
  let CU := ULift.{max uR uS uM uM₁} (AwayCokernel R S f M')
  let eCU : ULift.{max uR uS uM uM₁}
      (LocalizedModule (Submonoid.powers f) (ULift.{uM₁} M') ⧸
        LinearMap.range locU) ≃ₗ[RU] CU :=
    ULift.moduleEquiv.trans ((eC.restrictScalars RU).trans ULift.moduleEquiv.symm)
  let S₀ := (ModuleCat.restrictScalars
    ((algebraMap R S).ulift.{max uR uS uM uM₁, max uR uS uM uM₁})).obj
      (ModuleCat.of SU SU)
  let eS : S₀ ≃ₗ[RU] SU :=
    { Equiv.refl _ with
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro r s
        change ULift.up ((algebraMap R S) r.down * s.down) = ULift.up (r.down • s.down)
        rw [Algebra.smul_def] }
  have hTor : IsZero (((Tor (ModuleCat RU) 1).obj
      (ModuleCat.of RU SU)).obj (ModuleCat.of RU CU)) := by
    have hBase' := hBase.of_iso
      (((Tor (ModuleCat RU) 1).mapIso eS.symm.toModuleIso).app
        (ModuleCat.of RU (ULift.{max uR uS uM uM₁}
          (LocalizedModule (Submonoid.powers f) (ULift.{uM₁} M') ⧸
            LinearMap.range locU))))
    exact hBase'.of_iso (((Tor (ModuleCat RU) 1).obj
      (ModuleCat.of RU SU)).mapIso eCU.symm.toModuleIso)
  have hiS : Function.Injective (LinearMap.rTensor S i) :=
    rTensor_injective_of_isZero_tor_of_exact i g hii hex hg hTor
  let β : M₁ ⊗[R] S ≃ₗ[R] LocalizedModule.Away (algebraMap R S f) M' :=
    (TensorProduct.comm R M₁ S).trans (α.symm.restrictScalars R)
  have ha : (α.symm.toLinearMap.restrictScalars R).comp
      ((TensorProduct.map (LinearMap.id (R := R) (M := S)) i).comp
        (TensorProduct.comm R (M ⧸ T) S).toLinearMap) =
      β.toLinearMap.comp (LinearMap.rTensor S i) := by
    ext x s
    rfl
  have hTors : ∀ c : AwayCokernel R S f M', ∃ n : ℕ,
      ∀ r ∈ (Ideal.span {f}) ^ n, r • c = 0 := by
    intro c
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range locS) c
    obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers f) loc z
    obtain ⟨n, hn⟩ := s.property
    refine ⟨n, fun r hr => ?_⟩
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hr
    obtain ⟨a, rfl⟩ := hr
    have hz : f ^ n • q z = 0 := by
      rw [← map_smul]
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      change (s : R) • z = loc m at hs
      rw [← hn] at hs
      exact ⟨m, hs.symm⟩
    change (f ^ n * a) • q z = 0
    rw [mul_comm, mul_smul, hz, smul_zero]
  have hunit := (_root_.tensorProduct_mk_bijective_of_ideal_power_torsion
    R (Ideal.span {f}) (AwayCokernel R S f M') hTors).1 S hmod
  let μ : (AwayCokernel R S f M') ⊗[R] S →ₗ[R] AwayCokernel R S f M' :=
    TensorProduct.lift (Algebra.lsmul R R (AwayCokernel R S f M')).toLinearMap.flip
  have hμ : Function.Injective μ := by
    intro x y hxy
    obtain ⟨x, rfl⟩ := hunit.2 x
    obtain ⟨y, rfl⟩ := hunit.2 y
    rw [show x = y by simpa [μ] using hxy]
  have hcomm : q.comp β.toLinearMap = μ.comp (LinearMap.rTensor S g) := by
    ext y s
    change q (α.symm (s ⊗ₜ[R] y)) = s • q (α.symm (1 ⊗ₜ[R] y))
    rw [symm_tmul_eq_smul_symm_one_tmul]
    exact (LinearMap.range locS).mkQ.map_smul s _
  refine ⟨i, hi, ?_, ?_, ?_⟩
  · rw [ha]
    exact β.injective.comp hiS
  · rw [ha]
    exact (LinearMap.exact_iff_of_surjective_of_bijective_of_injective
      (LinearMap.rTensor S i) (LinearMap.rTensor S g)
      (β.toLinearMap.comp (LinearMap.rTensor S i)) q
      LinearMap.id β.toLinearMap μ
      (by simp) hcomm Function.surjective_id β.bijective hμ).mp
        (rTensor_exact S hex hg)
  · exact Submodule.mkQ_surjective _

end

end BeauvilleLaszlo

end
