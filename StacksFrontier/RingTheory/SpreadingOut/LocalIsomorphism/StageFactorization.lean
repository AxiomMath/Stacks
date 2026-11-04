module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Factoring through a single localization `R_f`

Let `S` be a finitely presented `R`-algebra and `q ⊆ S` a prime over `p ⊆ R` such that
`R_p → S_q` is bijective. We show that the composite `S → S_q ≅ R_p` factors through `R_f` for
some `f ∉ p`, using that `R_p` is the filtered colimit of the localizations `R_f`, `f ∉ p`.

## Main results

* `exists_stage_factorization`: the factorization `S → R_f → R_p`.
-/

@[expose] public section

universe u v v' w w'

@[expose] public section

open Localization

namespace StageFactor

open CategoryTheory CategoryTheory.Limits
variable (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]

/-- The complement of `p`, the index of the diagram of localizations `R_g`. -/
abbrev Idx (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime] :=
  p.primeCompl

/-- `Idx R p` is ordered by divisibility: `a ≤ b` when `a ∣ b`. -/
noncomputable instance : Preorder (Idx R p) where
  le a b := (a : R) ∣ (b : R)
  le_refl a := dvd_refl _
  le_trans a b c := dvd_trans

/-- The index is directed: `a` and `b` are both bounded by their product `a * b`. -/
instance : IsDirected (Idx R p) (· ≤ ·) := by
  constructor
  intro a b
  exact
    ⟨⟨(a : R) * (b : R), Submonoid.mul_mem _ a.property b.property⟩, dvd_mul_right _ _,
      dvd_mul_left _ _⟩

/-- The index is nonempty, `1` lying outside `p`. -/
instance : Nonempty (Idx R p) :=
  ⟨⟨1, p.primeCompl.one_mem⟩⟩

/-- The index is filtered, being directed and nonempty. -/
instance instFilt : CategoryTheory.IsFiltered (Idx R p) :=
  inferInstance

/-- For `a ≤ b` in the index, `a` is a unit in `R_b`. -/
theorem unit_of_le (a b : Idx R p) (h : a ≤ b) :
    IsUnit (algebraMap R (Localization.Away (b : R)) (a : R)) := by
  have hb : IsUnit (algebraMap R (Localization.Away (b : R)) (b : R)) :=
    IsLocalization.Away.algebraMap_isUnit (b : R)
  obtain ⟨c, hc⟩ := h
  have heq :
    algebraMap R (Localization.Away (b : R)) (b : R) =
      algebraMap R (Localization.Away (b : R)) (a : R) *
        algebraMap R (Localization.Away (b : R)) c := by
    rw [← map_mul, ← hc]
  exact isUnit_of_mul_isUnit_left (heq ▸ hb)

/-- Transition map `R_a → R_b` for `a ≤ b`. -/
@[ega "0 1.4.1" "special case",
  ega "0 1.6.2" "ring case M = A of ρ_{fg",
  ega "0 7.6.15" "special case",
  ega "0 7.6.7" "ρ^{T, special case"]
noncomputable def trans (a b : Idx R p) (h : a ≤ b) :
    Localization.Away (a : R) →+* Localization.Away (b : R) :=
  IsLocalization.Away.lift (S := Localization.Away (a : R)) (a : R) (unit_of_le R p a b h)

/-- The transition map `R_a → R_b` commutes with the structure maps from `R`. -/
@[ega "0 1.4.1" "Identity i_A^T = ρ_A^{T", ega "0 7.6.7" "compatibility of ρ^{T"]
theorem trans_algebraMap (a b : Idx R p) (h : a ≤ b) (r : R) :
    trans R p a b h (algebraMap R (Localization.Away (a : R)) r) =
      algebraMap R (Localization.Away (b : R)) r := by
  unfold trans; rw [IsLocalization.Away.lift_eq]

/-- Two ring maps `R_a → R_b` agreeing on the image of `R` are equal, `R_a` being a
localization of `R`. -/
theorem trans_comp_eq {a b : Idx R p}
    (φ ψ : Localization.Away (a : R) →+* Localization.Away (b : R))
    (hφ :
      ∀ r,
        φ (algebraMap R (Localization.Away (a : R)) r) =
          algebraMap R (Localization.Away (b : R)) r)
    (hψ :
      ∀ r,
        ψ (algebraMap R (Localization.Away (a : R)) r) =
          algebraMap R (Localization.Away (b : R)) r) :
    φ = ψ := by
  exact IsLocalization.ringHom_ext (Submonoid.powers (a : R))
    (RingHom.ext fun r => (hφ r).trans (hψ r).symm)

/-- The diagram functor `g ↦ R_g` over the index category. -/
noncomputable def diag : (Idx R p) ⥤ CommRingCat.{u} where
  obj a := CommRingCat.of (Localization.Away (a : R))
  map {a b} h := CommRingCat.ofHom (trans R p a b h.le)
  map_id a := by
    apply CommRingCat.hom_ext
    apply trans_comp_eq R p
    · intro r; exact trans_algebraMap R p a a (le_refl a) r
    · intro r; rfl
  map_comp {a b c} f g := by
    apply CommRingCat.hom_ext
    apply trans_comp_eq R p
    · intro r; exact trans_algebraMap R p a c (f.le.trans g.le) r
    · intro r
      change (trans R p b c g.le) ((trans R p a b f.le) _) = _
      rw [trans_algebraMap, trans_algebraMap]

/-- Colimit leg `R_a → R_p`. -/
noncomputable def leg (a : Idx R p) : Localization.Away (a : R) →+* Localization.AtPrime p :=
  IsLocalization.Away.lift (S := Localization.Away (a : R)) (a : R)
    (IsLocalization.map_units (Localization.AtPrime p) a)

/-- The cocone leg `R_a → R_p` commutes with the structure maps from `R`. -/
theorem leg_algebraMap (a : Idx R p) (r : R) :
    leg R p a (algebraMap R (Localization.Away (a : R)) r) =
      algebraMap R (Localization.AtPrime p) r := by
  unfold leg; rw [IsLocalization.Away.lift_eq]

/-- The cocone with vertex `R_p`. -/
noncomputable def cocp : CategoryTheory.Limits.Cocone (diag R p) where
  pt := CommRingCat.of (Localization.AtPrime p)
  ι :=
    { app := fun a => CommRingCat.ofHom (leg R p a)
      naturality := by
        intro a b h
        apply CommRingCat.hom_ext
        change (leg R p b).comp (trans R p a b h.le) = (leg R p a).comp (RingHom.id _)
        apply IsLocalization.ringHom_ext (Submonoid.powers (a : R))
        ext r
        change
          (leg R p b) ((trans R p a b h.le) (algebraMap R (Localization.Away (a : R)) r)) =
            (leg R p a) ((RingHom.id _) (algebraMap R (Localization.Away (a : R)) r))
        rw [trans_algebraMap, leg_algebraMap, RingHom.id_apply, leg_algebraMap] }

/-- The structure map `R → s.pt` of a cocone `s`, read off the leg at `1`. -/
noncomputable def coconeStr {s : CategoryTheory.Limits.Cocone (diag R p)} : R →+* s.pt :=
  (s.ι.app ⟨1, p.primeCompl.one_mem⟩).hom.comp
    (algebraMap R (Localization.Away ((⟨1, p.primeCompl.one_mem⟩ : Idx R p) : R)))

-- needed: `leg_app_str`'s `simp` makes no progress unless the structure-sheaf section
-- coercions unfold at `default` transparency
set_option backward.isDefEq.respectTransparency false in
/-- Leg `a` composed with `R → R_a` equals the structure map (cocone compatibility). -/
theorem leg_app_str {s : CategoryTheory.Limits.Cocone (diag R p)} (a : Idx R p) (r : R) :
    (s.ι.app a).hom (algebraMap R (Localization.Away (a : R)) r) = coconeStr R p (s := s) r := by
  set o : Idx R p := ⟨1, p.primeCompl.one_mem⟩ with ho
  have hoa : o ≤ a := one_dvd _
  have hnat : (s.ι.app a).hom.comp (trans R p o a hoa) = (s.ι.app o).hom := by
    have := s.ι.naturality (CategoryTheory.homOfLE hoa)
    simp only [CategoryTheory.Functor.const_obj_obj, CategoryTheory.Functor.const_obj_map,
      CategoryTheory.Category.comp_id] at this
    exact congrArg CommRingCat.Hom.hom this
  have hr := RingHom.congr_fun hnat (algebraMap R (Localization.Away (o : R)) r)
  simp only [RingHom.comp_apply] at hr
  change
    (s.ι.app a).hom (algebraMap R (Localization.Away (a : R)) r) =
      (s.ι.app o).hom (algebraMap R (Localization.Away (o : R)) r)
  rw [← trans_algebraMap R p o a hoa r]
  exact hr

/-- `coconeStr` inverts `p.primeCompl`. -/
theorem coconeStr_units {s : CategoryTheory.Limits.Cocone (diag R p)} (y : p.primeCompl) :
    IsUnit (coconeStr R p (s := s) (y : R)) := by
  rw [← leg_app_str R p (y : Idx R p) (y : R)]
  exact
    IsUnit.map (s.ι.app (y : Idx R p)).hom
      (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (y : R)) (y : R))

/-- Descent map `R_p → s.pt`. -/
noncomputable def descMap (s : CategoryTheory.Limits.Cocone (diag R p)) :
    Localization.AtPrime p →+* s.pt :=
  IsLocalization.lift (M := p.primeCompl) (g := coconeStr R p (s := s))
    (coconeStr_units R p (s := s))

/-- The map descended from a cocone `s` commutes with the structure maps from `R`. -/
theorem descMap_algebraMap (s : CategoryTheory.Limits.Cocone (diag R p)) (r : R) :
    descMap R p s (algebraMap R (Localization.AtPrime p) r) = coconeStr R p (s := s) r := by
  unfold descMap; rw [IsLocalization.lift_eq]

/-- The cocone `cocp` with vertex `R_p` is a colimit of the filtered diagram of localizations
`R_g` over `g ∈ p.primeCompl`. -/
@[ega "IV 8.1.2" "partial"]
noncomputable def cocpIsColimit : CategoryTheory.Limits.IsColimit (cocp R p) :=
  CategoryTheory.Limits.IsColimit.mk (fun s => CommRingCat.ofHom (descMap R p s))
    (by
      intro s a
      apply CommRingCat.hom_ext
      change (descMap R p s).comp (leg R p a) = (s.ι.app a).hom
      apply IsLocalization.ringHom_ext (Submonoid.powers (a : R))
      ext r
      change
        (descMap R p s) ((leg R p a) (algebraMap R (Localization.Away (a : R)) r)) =
          (s.ι.app a).hom (algebraMap R (Localization.Away (a : R)) r)
      rw [leg_algebraMap, descMap_algebraMap, leg_app_str])
    (by
      intro s m hm
      apply CommRingCat.hom_ext
      change m.hom = descMap R p s
      apply IsLocalization.ringHom_ext (M := p.primeCompl) (S := Localization.AtPrime p)
      ext r
      change
        m.hom (algebraMap R (Localization.AtPrime p) r) =
          (descMap R p s) (algebraMap R (Localization.AtPrime p) r)
      rw [descMap_algebraMap]
      have hmo := hm ⟨1, p.primeCompl.one_mem⟩
      have hmr :=
        RingHom.congr_fun (congrArg CommRingCat.Hom.hom hmo)
          (algebraMap R (Localization.Away ((⟨1, p.primeCompl.one_mem⟩ : Idx R p) : R)) r)
      simp only [] at hmr
      change m.hom ((leg R p ⟨1, p.primeCompl.one_mem⟩) _) = _ at hmr
      rw [leg_algebraMap] at hmr
      rw [hmr]
      rfl)

/-- The `R`-algebra structure natural transformation `const R ⟶ diag`. -/
noncomputable def alg :
    (CategoryTheory.Functor.const (Idx R p)).obj (CommRingCat.of R) ⟶ diag R p where
  app a := CommRingCat.ofHom (algebraMap R (Localization.Away (a : R)))
  naturality := by
    intro a b h
    apply CommRingCat.hom_ext
    change
      (algebraMap R (Localization.Away (b : R))).comp (RingHom.id _) =
        (trans R p a b h.le).comp (algebraMap R (Localization.Away (a : R)))
    ext r
    change
      algebraMap R (Localization.Away (b : R)) r =
        (trans R p a b h.le) (algebraMap R (Localization.Away (a : R)) r)
    rw [trans_algebraMap]

/-- The component of the structure natural transformation at `a` is `algebraMap R R_a`. -/
theorem alg_app (a : Idx R p) :
    (alg R p).app a = CommRingCat.ofHom (algebraMap R (Localization.Away (a : R))) :=
  rfl

/-- `forget CommRingCat` preserves the colimit of `diag`. -/
noncomputable instance preservesDiag :
    CategoryTheory.Limits.PreservesColimit (diag R p) (CategoryTheory.forget CommRingCat) := by
  have h : CategoryTheory.Limits.PreservesFilteredColimits (CategoryTheory.forget CommRingCat) :=
    inferInstance
  exact (h.preserves_filtered_colimits (Idx R p)).preservesColimit

/-- An `R`-algebra map `θ : T → R_p` from a finitely presented `R`-algebra `T` factors through a
stage `R_f` with `f ∉ p`. -/
theorem stage_factor_helper (T : Type u) [CommRing T] [Algebra R T]
    (hfp : (algebraMap R T).FinitePresentation) (θ : T →+* Localization.AtPrime p)
    (hθ : θ.comp (algebraMap R T) = algebraMap R (Localization.AtPrime p)) :
    ∃ f : R,
      f ∉ p ∧
        ∃ θf : T →+* Localization.Away f,
          θf.comp (algebraMap R T) = algebraMap R (Localization.Away f) ∧
            ∃ cf : Localization.Away f →+* Localization.AtPrime p,
              cf.comp (algebraMap R (Localization.Away f)) =
                  algebraMap R (Localization.AtPrime p) ∧
                cf.comp θf = θ := by
  have hcompat :
    ∀ i : Idx R p,
      (CommRingCat.ofHom (algebraMap R T)) ≫ (CommRingCat.ofHom θ) =
        (alg R p).app i ≫ (cocp R p).ι.app i := by
    intro i
    apply CommRingCat.hom_ext
    show θ.comp (algebraMap R T) = (leg R p i).comp (algebraMap R (Localization.Away (i : R)))
    rw [hθ]
    exact (RingHom.ext (leg_algebraMap R p i)).symm
  obtain ⟨i, g', hfg, hgcomp⟩ :=
    RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit (CommRingCat.of R) (diag R p) (alg R p)
      (CommRingCat.ofHom (algebraMap R T)) (cocp R p) (cocpIsColimit R p)
      (by
        rw [CommRingCat.hom_ofHom]; exact hfp)
      (CommRingCat.ofHom θ) hcompat
  refine ⟨(i : R), i.property, g'.hom, ?_, leg R p i, ?_, ?_⟩
  · have hthis := congrArg CommRingCat.Hom.hom hfg
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, alg_app] at hthis
    exact hthis
  · exact RingHom.ext (leg_algebraMap R p i)
  · have hthis := congrArg CommRingCat.Hom.hom hgcomp
    simp only [CommRingCat.hom_ofHom] at hthis
    exact hthis.symm

end StageFactor

/-- Let `S` be a finitely presented `R`-algebra and `q ⊆ S` a prime over `p ⊆ R` such that
`φ_p : R_p → S_q` is bijective. Then there are `f ∉ p`, an `R`-algebra map `θf : S → R_f` and an
`R`-algebra map `cf : R_f → R_p` such that `cf ∘ θf` is the composite of `S → S_q` with the
inverse of `φ_p`. -/
theorem exists_stage_factorization (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (p : Ideal
  R)
    [p.IsPrime] (q : Ideal S) [q.IsPrime] (hpq : p = q.comap (algebraMap R S))
    [Algebra.FinitePresentation R S]
    (hiso : Function.Bijective (Localization.localRingHom p q (algebraMap R S) hpq)) :
    ∃ f : R,
      f ∉ p ∧
        ∃ θf : S →+* Localization.Away f,
          θf.comp (algebraMap R S) = algebraMap R (Localization.Away f) ∧
            ∃ cf : Localization.Away f →+* Localization.AtPrime p,
              cf.comp (algebraMap R (Localization.Away f)) =
                  algebraMap R (Localization.AtPrime p) ∧
                (∀ s : S,
                  cf (θf s) =
                    (RingEquiv.ofBijective (Localization.localRingHom p q (algebraMap R S) hpq)
                          hiso).symm
                      ((algebraMap S (Localization.AtPrime q)) s)) := by
  set e := RingEquiv.ofBijective (Localization.localRingHom p q (algebraMap R S) hpq) hiso with he
  set θ : S →+* Localization.AtPrime p :=
    e.symm.toRingHom.comp (algebraMap S (Localization.AtPrime q)) with hθdef
  have hθ : θ.comp (algebraMap R S) = algebraMap R (Localization.AtPrime p) := by
    ext r
    simp only [hθdef, RingHom.comp_apply]
    have hkey :
      e (algebraMap R (Localization.AtPrime p) r) =
        algebraMap S (Localization.AtPrime q) (algebraMap R S r) :=
      Localization.localRingHom_to_map p q (algebraMap R S) hpq r
    show e.symm (algebraMap S (Localization.AtPrime q) (algebraMap R S r)) = _
    rw [← hkey]
    show e.symm (e _) = _
    rw [RingEquiv.symm_apply_apply]
  have hfp : (algebraMap R S).FinitePresentation :=
    (RingHom.finitePresentation_algebraMap).mpr inferInstance
  obtain ⟨f, hf, θf, hθf, cf, hcf, hcomp⟩ := StageFactor.stage_factor_helper R p S hfp θ hθ
  refine ⟨f, hf, θf, hθf, cf, hcf, ?_⟩
  intro s
  have hh := RingHom.congr_fun hcomp s
  simp only [RingHom.comp_apply] at hh
  rw [hh]
  rfl
