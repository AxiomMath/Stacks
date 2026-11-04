module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.RingTheory.Artinian.Ring
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.FormalObject.Basic
public import StacksFrontier.Deformation.FormalObject.Completion
public import StacksFrontier.Deformation.Predeformation.Basic

/-!
# Prorepresentable functors preserve finite limits (Stacks 06IC)

A functor on Artinian local `Λ`-algebras which is prorepresented by a Noetherian complete
local `Λ`-algebra `R` preserves finite limits. The reason is that a finite diagram `K` in
`𝒞_Λ` is killed by a single power of the maximal ideal: every object `K j` satisfies
`m ^ (n + 1) = 0` for the common exponent `n` obtained by summing the individual nilpotence
exponents. Hence every point of `K j` over `R` factors uniquely through the adic truncation
`R / m_R ^ (n + 1)`, and the limit of the hom-sets is computed by the hom-set out of that
single Artinian quotient, which is itself an object of `𝒞_Λ`.

The Stacks source says "arbitrary limits". Restriction from complete local algebras to
Artinian local algebras does not preserve infinite limits: over a field `k` the inverse
system `k[t]/(t ^ n)` has limit `k` inside `𝒞_Λ`, whereas the compatible substitutions
`t ↦ t` give a nonconstant point of the limit of the functor prorepresented by `k[[t]]`.
Finite limits are what the tangent-space construction of Tag 06IA uses.

## Main results

* `Deformation.restrictedCoyoneda_preservesFiniteLimits`: the restricted covariant
  representable functor of a complete local algebra preserves finite limits.
* `Deformation.isProrepresentable_preservesFiniteLimits`: **Stacks 06IC**, finite-limit
  preservation for a prorepresentable functor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing

namespace Deformation

universe u v w

section

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Two morphisms of complete local algebras with the same underlying algebra map
are equal. -/
private theorem completeLocalAlgHom_ext
    {A B : CompleteLocalAlgCat.{u, v, w} Λ k} {f g : A ⟶ B} (h : f.hom = g.hom) : f = g :=
  CompleteLocalAlgCat.Hom.ext h

/-- A single exponent killing the maximal ideals of every object of a finite diagram. -/
private noncomputable def finiteDiagramExponent {J : Type*} [Category J] [Fintype J]
    (K : J ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) : ℕ :=
  ∑ j, Nat.find (exists_pow_maximalIdeal_eq_bot (K.obj j))

private lemma finiteDiagramExponent_le {J : Type*} [Category J] [Fintype J]
    (K : J ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (j : J) :
    Nat.find (exists_pow_maximalIdeal_eq_bot (K.obj j)) ≤ finiteDiagramExponent K := by
  show Nat.find (exists_pow_maximalIdeal_eq_bot (K.obj j)) ≤
    ∑ i : J, Nat.find (exists_pow_maximalIdeal_eq_bot (K.obj i))
  simpa using (Finset.single_le_sum
    (fun i _ ↦ Nat.zero_le (Nat.find (exists_pow_maximalIdeal_eq_bot (K.obj i))))
    (Finset.mem_univ j))

private lemma finiteDiagramExponent_kills {J : Type*} [Category J] [Fintype J]
    (K : J ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (j : J) :
    IsLocalRing.maximalIdeal (K.obj j) ^ (finiteDiagramExponent K + 1) = ⊥ := by
  let e := Nat.find (exists_pow_maximalIdeal_eq_bot (K.obj j))
  have he : IsLocalRing.maximalIdeal (K.obj j) ^ (e + 1) = ⊥ := by
    simpa [e] using Nat.find_spec (exists_pow_maximalIdeal_eq_bot (K.obj j))
  exact le_antisymm
    ((Ideal.pow_le_pow_right (Nat.add_le_add_right (finiteDiagramExponent_le K j) 1)).trans
      he.le) bot_le

/-- A point of an Artinian local algebra `A` over `R` factors through the adic truncation
`R / m_R ^ (n + 1)` as soon as `m_A ^ (n + 1) = 0`. -/
public lemma exists_factorThroughAdicTruncation
    {R : CompleteLocalAlgCat.{u, v, w} Λ k} {A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (α : (restrictedCoyoneda R).obj A)
    {n : ℕ} (hn : IsLocalRing.maximalIdeal A ^ (n + 1) = ⊥) :
    ∃ a : AdicTruncation.obj R n ⟶ A,
      a.hom.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R n)) = α.hom := by
  have : IsLocalHom α.hom.toRingHom := α.isLocal
  let : Nontrivial (R ⧸ AdicTruncation.ideal R n) :=
    inferInstanceAs (Nontrivial (AdicTruncation.obj R n))
  let : IsLocalRing (R ⧸ AdicTruncation.ideal R n) :=
    inferInstanceAs (IsLocalRing (AdicTruncation.obj R n))
  have hker : AdicTruncation.ideal R n ≤ RingHom.ker α.hom.toRingHom := by
    show AdicTruncation.ideal R n ≤
      (⊥ : Ideal (artinianToComplete.obj A)).comap α.hom.toRingHom
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact (Ideal.pow_right_mono (map_maximalIdeal_le α.hom.toRingHom) _).trans_eq hn
  let f := Ideal.Quotient.liftₐ (AdicTruncation.ideal R n) α.hom hker
  have hf : IsLocalHom f.toRingHom := by
    constructor; intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (Ideal.Quotient.mk (AdicTruncation.ideal R n)).isUnit_map
      (α.isLocal.map_nonunit r hx)
  refine ⟨{ hom := f, isLocal := hf, residue_comm := ?_ }, ?_⟩
  · intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    show A.residueEquiv (residue A (α.hom r)) =
      AdicTruncation.residueEquiv R n (residue _ (Ideal.Quotient.mk _ r))
    rw [AdicTruncation.residueEquiv_residue_mk]
    exact α.residue_comm r
  · ext r; rfl

/-- Two morphisms out of an adic truncation of `R` are equal if they agree on `R`. -/
private theorem adicTruncation_hom_ext {R : CompleteLocalAlgCat.{u, v, w} Λ k} {n : ℕ}
    {A : ArtinianLocalAlgCat.{u, v, w} Λ k} {f g : AdicTruncation.obj R n ⟶ A}
    (h : f.hom.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R n)) =
      g.hom.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R n))) : f = g :=
  ArtinianLocalAlgCat.hom_ext (Ideal.Quotient.algHom_ext Λ h)

/-- The restricted covariant representable functor of a Noetherian complete local
`Λ`-algebra preserves finite limits. -/
theorem restrictedCoyoneda_preservesFiniteLimits
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    PreservesFiniteLimits (restrictedCoyoneda R) := by
  refine ⟨?_⟩
  intro J 𝒥 hJ
  let := 𝒥
  let := hJ
  refine ⟨fun {K} ↦ ?_⟩
  refine ⟨fun {c} hc ↦ ?_⟩
  classical
  let F := restrictedCoyoneda R
  let n := finiteDiagramExponent K
  let Q := AdicTruncation.obj R n
  let q : R ⟶ artinianToComplete.obj Q := quotientProjection R n
  let qhom : R →ₐ[Λ] Q := Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R n)
  let cF := F.mapCone c
  let secTo := Types.sectionOfCone cF
  have factorMap (A : ArtinianLocalAlgCat.{u, v, w} Λ k) (α : F.obj A) (a : Q ⟶ A)
      (ha : a.hom.comp qhom = α.hom) : F.map a q = α :=
    completeLocalAlgHom_ext ha
  have secTo_injective : Function.Injective secTo := by
    intro x y hxy
    apply completeLocalAlgHom_ext
    let N := Nat.find (exists_pow_maximalIdeal_eq_bot c.pt)
    let qN : R →ₐ[Λ] AdicTruncation.obj R N :=
      Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R N)
    obtain ⟨a, ha⟩ := exists_factorThroughAdicTruncation x
      (Nat.find_spec (exists_pow_maximalIdeal_eq_bot c.pt))
    obtain ⟨b, hb⟩ := exists_factorThroughAdicTruncation y
      (Nat.find_spec (exists_pow_maximalIdeal_eq_bot c.pt))
    have hab : a = b := by
      apply hc.hom_ext
      intro j
      apply adicTruncation_hom_ext
      have hj := congrArg (fun s : (K ⋙ F).sections => s.1 j) hxy
      have hj' : (F.map (c.π.app j) x).hom = (F.map (c.π.app j) y).hom :=
        congrArg (fun z => z.hom) hj
      change ((artinianToComplete.map (c.π.app j)).hom.comp x.hom) =
        ((artinianToComplete.map (c.π.app j)).hom.comp y.hom) at hj'
      rw [← ha, ← hb] at hj'
      exact hj'
    have hfinal := congrArg
      (fun f : AdicTruncation.obj R N ⟶ c.pt => f.hom.comp qN) hab
    rwa [ha, hb] at hfinal
  have hb : Function.Bijective (Types.sectionOfCone cF) := by
    refine ⟨secTo_injective, fun s => ?_⟩
    let α (j : J) : F.obj (K.obj j) := s.1 j
    let a (j : J) : Q ⟶ K.obj j :=
      Classical.choose
        (exists_factorThroughAdicTruncation (α j) (finiteDiagramExponent_kills K j))
    have ha (j : J) : (a j).hom.comp qhom = (α j).hom :=
      Classical.choose_spec
        (exists_factorThroughAdicTruncation (α j) (finiteDiagramExponent_kills K j))
    let d : Cone K := {
      pt := Q
      π := {
        app := a
        naturality := by
          intro i j f
          apply adicTruncation_hom_ext
          have hs := s.2 f
          change F.map (K.map f) (α i) = α j at hs
          have hs' := congrArg (fun z => z.hom) hs
          change (K.map f).hom.comp (α i).hom = (α j).hom at hs'
          exact (by rw [AlgHom.comp_assoc, ha i, hs', ← ha j] :
            ((K.map f).hom.comp (a i).hom).comp qhom = (a j).hom.comp qhom).symm
      }
    }
    let x : cF.pt := F.map (hc.lift d) q
    refine ⟨x, Subtype.ext (funext fun j => ?_)⟩
    show q ≫ artinianToComplete.map (hc.lift d ≫ c.π.app j) = s.1 j
    rw [hc.fac d j]
    exact factorMap (K.obj j) (α j) (a j) (ha j)
  exact (Types.isLimit_iff_bijective_sectionOfCone cF).2 hb

/-- **Stacks Project, Tag 06IC.** A prorepresentable functor on Artinian local
`Λ`-algebras preserves finite limits. -/
@[stacks 06IC "prorepresentable_preserves_limits"]
theorem isProrepresentable_preservesFiniteLimits
    (F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type v) (hF : IsProrepresentable F) :
    PreservesFiniteLimits F := by
  obtain ⟨R, hR⟩ := hF
  let : PreservesFiniteLimits (restrictedCoyoneda R) :=
    restrictedCoyoneda_preservesFiniteLimits R
  exact preservesFiniteLimits_of_natIso hR.some.symm

end

end Deformation

end
