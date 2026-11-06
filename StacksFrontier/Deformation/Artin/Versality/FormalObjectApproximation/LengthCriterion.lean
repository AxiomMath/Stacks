module

public import StacksFrontier.Deformation.Artin.Versality.FormalObjectApproximation.CompletedFormalBase
import StacksFrontier.CategoryTheory.FiberedCategory.HomLift

/-!
# Algebraization of a versal formal object: bijectivity from lengths

A part of `StacksFrontier.Deformation.Artin.Versality.FormalObjectApproximation`: a map of
complete local bases, or of formal objects, which is surjective and preserves the lengths of
the adic quotients is bijective, respectively an isomorphism; the lengths are compared
through the associated graded pieces and the completed localization.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber.fiberInclusion
attribute [local implicit_reducible] Deformation.Artin.baseOver
attribute [local implicit_reducible] Deformation.Artin.truncationOver

namespace Deformation.Artin

open Deformation.Artin.Approximation

universe u v w

/-- Reducing modulo a higher power leaves a lower adic quotient unchanged. -/
private theorem isIso_truncation_formalBaseQuotient
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    (R : Deformation.CompleteLocalAlgCat Λ k) {n m : ℕ} (hmn : m ≤ n) :
    IsIso (Deformation.AdicTruncation.map (formalBaseQuotient R n) m) := by
  let S := Deformation.artinianToComplete.obj (Deformation.AdicTruncation.obj R n)
  let q : R →+* S := (formalBaseQuotient R n).hom.toRingHom
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  have hmax : maximalIdeal S = (maximalIdeal R).map q :=
    (map_maximalIdeal_of_surjective q hq).symm
  have hcomap : (maximalIdeal S ^ (m + 1)).comap q =
      maximalIdeal R ^ (m + 1) := by
    rw [hmax, ← Ideal.map_pow, Ideal.comap_map_of_surjective q hq]
    rw [show Ideal.comap q ⊥ = maximalIdeal R ^ (n + 1) from
      Ideal.mk_ker]
    exact sup_eq_left.mpr (Ideal.pow_le_pow_right (Nat.add_le_add_right hmn 1))
  apply isIso_of_bijective_artinianLocalHom
  exact ⟨Ideal.quotientMap_injective' (H := hcomap.ge) hcomap.le,
    Ideal.quotientMap_surjective (H := hcomap.ge) hq⟩

/-- A map of formal objects lifting a base quotient has that quotient as its base map up to
the codomain identification. -/
private theorem base_comp_eqToHom_eq_formalBaseQuotient
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type*} [Category F]
    {p : F ⥤ Deformation.ArtinianLocalAlgCat Λ k}
    {η ηn : Deformation.FormalObject p} (q : η ⟶ ηn) {n : ℕ}
    (hq : Deformation.FormalObject.projection.IsHomLift
      (formalBaseQuotient η.base n) q) :
    q.base ≫ eqToHom (IsHomLift.codomain_eq Deformation.FormalObject.projection
      (formalBaseQuotient η.base n) q) = formalBaseQuotient η.base n := by
  let := hq
  simpa only [Deformation.FormalObject.projection_map, eqToHom_refl, Category.id_comp] using
    (IsHomLift.commSq Deformation.FormalObject.projection (formalBaseQuotient η.base n) q).w

/-- A reduction of a formal object is unchanged at all lower levels. -/
private theorem isIso_app_of_formal_reduction
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type*} [Category F]
    {p : F ⥤ Deformation.ArtinianLocalAlgCat Λ k}
    (hp : Deformation.IsCofiberedInGroupoids p)
    {η ηn : Deformation.FormalObject p} (q : η ⟶ ηn) {n m : ℕ}
    (hq : Deformation.FormalObject.projection.IsHomLift
      (formalBaseQuotient η.base n) q) (hmn : m ≤ n) : IsIso (q.app m) := by
  let Q := Deformation.FormalObject.projection (p := p)
  let T := Deformation.AdicTruncation.functor (Λ := Λ) (k := k) m
  let := hq
  have heqT := congrArg T.map (base_comp_eqToHom_eq_formalBaseQuotient q hq)
  rw [Functor.map_comp] at heqT
  let : IsIso (T.map (formalBaseQuotient η.base n)) :=
    isIso_truncation_formalBaseQuotient η.base hmn
  have : IsIso (T.map q.base ≫ T.map (eqToHom
      (IsHomLift.codomain_eq Q (formalBaseQuotient η.base n) q))) :=
    heqT.symm ▸ inferInstance
  have : IsIso (T.map q.base) := IsIso.of_isIso_comp_right (T.map q.base)
    (T.map (eqToHom (IsHomLift.codomain_eq Q (formalBaseQuotient η.base n) q)))
  let : p.IsStronglyCocartesian (T.map q.base) (q.app m) :=
    isStronglyCocartesian_of_isCofiberedInGroupoids hp _ _ (q.app_lift m)
  exact Functor.IsStronglyCocartesian.isIso_of_base_isIso p (T.map q.base) (q.app m)

/-- A compatible tower of maps to reductions determines a map of formal objects
when the diagonal reduction maps are isomorphisms. -/
private theorem exists_formal_map_of_reduction_maps
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type*} [Category F]
    {p : F ⥤ Deformation.ArtinianLocalAlgCat Λ k}
    (ξ η : Deformation.FormalObject p)
    (ηn : ℕ → Deformation.FormalObject p)
    (q : ∀ n, η ⟶ ηn n) (g : ∀ n, ηn (n + 1) ⟶ ηn n)
    (hqg : ∀ n, q (n + 1) ≫ g n = q n)
    (hq : ∀ n, IsIso ((q n).app n))
    (an : ∀ n, ξ ⟶ ηn n) (han : ∀ n, an (n + 1) ≫ g n = an n)
    (a : ξ.base ⟶ η.base) (ha : ∀ n, a ≫ (q n).base = (an n).base) :
    ∃ f : ξ ⟶ η, f.base = a := by
  let (n : ℕ) := hq n
  let app n := (an n).app n ≫ inv ((q n).app n)
  refine ⟨⟨a, app, ?_, ?_⟩, rfl⟩
  · intro n
    let T := Deformation.AdicTruncation.functor (Λ := Λ) (k := k) n
    let := (q n).app_lift n
    let : IsIso (T.map (q n).base) :=
      IsHomLift.isIso_of_lift_isIso p _ ((q n).app n)
    let := (an n).app_lift n
    have heq : T.map (an n).base ≫ inv (T.map (q n).base) = T.map a := by
      rw [← ha n, Functor.map_comp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [← heq]
    exact IsHomLift.comp p _ _ _ _
  · intro n
    apply (cancel_mono ((q n).app n)).1
    dsimp only [app]
    have hqn := (q (n + 1)).naturality n
    have hqgn : (q (n + 1)).app n ≫ (g n).app n = (q n).app n :=
      congrArg (fun t => t.app n) (hqg n)
    have hann : (an (n + 1)).app n ≫ (g n).app n = (an n).app n :=
      congrArg (fun t => t.app n) (han n)
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [← hqgn, ← Category.assoc (η.transition n), hqn]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    rw [← Category.assoc, ← (an (n + 1)).naturality n]
    simp only [Category.assoc, hann]

/-- Surjectivity modulo the squares of the maximal ideals implies surjectivity. -/
private theorem surjective_of_surjective_second_truncation
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {R S : Deformation.CompleteLocalAlgCat Λ k} (f : R ⟶ S)
    (hf : Function.Surjective (Deformation.AdicTruncation.map f 1).hom) :
    Function.Surjective f.hom := by
  apply (Deformation.surjective_iff_surjective_cotangentSpaceMap f).2
  intro x
  obtain ⟨y, rfl⟩ := (maximalIdeal S).toCotangent_surjective x
  obtain ⟨r, hr⟩ := hf (Ideal.Quotient.mk (maximalIdeal S ^ 2) y.1)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  change Ideal.Quotient.mk (maximalIdeal S ^ 2) (f.hom r) =
    Ideal.Quotient.mk (maximalIdeal S ^ 2) y.1 at hr
  have hdiff : f.hom r - y.1 ∈ maximalIdeal S ^ 2 :=
    by simpa only [Ideal.Quotient.mk_eq_mk_iff_sub_mem] using hr
  have hrS : f.hom r ∈ maximalIdeal S := by
    have h := (maximalIdeal S).add_mem
      (Ideal.pow_le_self (by decide : 2 ≠ 0) hdiff) y.2
    simpa only [sub_add_cancel] using h
  have hrR : r ∈ maximalIdeal R := by
    let : IsLocalHom f.hom.toRingHom := f.isLocal
    change r ∈ (maximalIdeal S).comap f.hom.toRingHom at hrS
    simpa only [maximalIdeal_comap] using hrS
  refine ⟨(maximalIdeal R).toCotangent ⟨r, hrR⟩, ?_⟩
  rw [Ideal.mapCotangent_toCotangent, Ideal.toCotangent_eq]
  exact hdiff

/-- A second-order lift from a versal object extends compatibly and induces a
surjective map of complete bases. -/
private theorem exists_surjective_base_lift_extending_second_reduction
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type*} [Category F]
    {p : F ⥤ Deformation.ArtinianLocalAlgCat Λ k}
    (hp : Deformation.IsCofiberedInGroupoids p)
    (ξ η : Deformation.FormalObject p) (hξ : Deformation.IsVersal hp ξ)
    (ηn : ℕ → Deformation.FormalObject p)
    (hn : ∀ n, (ηn n).base =
      Deformation.artinianToComplete.obj (Deformation.AdicTruncation.obj η.base n))
    (g : ∀ n, ηn (n + 1) ⟶ ηn n)
    (hg : ∀ n, Deformation.FormalObject.projection.IsHomLift
      (Deformation.artinianToComplete.map
        (Deformation.AdicTruncation.transition η.base n)) (g n))
    (a₁ : ξ ⟶ ηn 1) (ha₁ : Function.Surjective (a₁.base ≫ eqToHom (hn 1)).hom) :
    ∃ (a : ξ.base ⟶ η.base) (an : ∀ n, ξ ⟶ ηn n),
      Function.Surjective a.hom ∧ an 1 = a₁ ∧
      (∀ n, an (n + 1) ≫ g n = an n) ∧
      ∀ n, a ≫ formalBaseQuotient η.base n = (an n).base ≫ eqToHom (hn n) := by
  obtain ⟨b, hb₀, hb⟩ := exists_compatible_artinian_lifts hp ξ hξ
    (fun n => Deformation.AdicTruncation.obj η.base (n + 1))
    (fun n => Deformation.AdicTruncation.transition η.base (n + 1))
    (fun n => Ideal.Quotient.factor_surjective
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 2))))
    (fun n => ηn (n + 1)) (fun n => g (n + 1)) (fun n => hg (n + 1)) a₁
  let an : ∀ n, ξ ⟶ ηn n
    | 0 => a₁ ≫ g 0
    | n + 1 => b n
  have han : ∀ n, an (n + 1) ≫ g n = an n := by
    intro n
    cases n with
    | zero => exact congrArg (fun t => t ≫ g 0) hb₀
    | succ n => exact hb n
  obtain ⟨a, ha⟩ := exists_base_map_of_reduction_maps ξ η ηn hn g hg an han
  have ha₂ : Function.Surjective (a ≫ formalBaseQuotient η.base 1).hom := by
    rw [ha 1, show an 1 = a₁ from hb₀]
    exact ha₁
  have hsurj : Function.Surjective a.hom := by
    apply surjective_of_surjective_second_truncation a
    intro y
    obtain ⟨r, hr⟩ := ha₂ y
    exact ⟨Ideal.Quotient.mk (maximalIdeal ξ.base ^ 2) r, hr⟩
  exact ⟨a, an, hsurj, hb₀, han, ha⟩

/-- Compatible Artinian lifts from a versal object assemble into a surjective
map of formal objects extending the prescribed second-order base map. -/
private theorem exists_surjective_formal_lift_of_second_reduction
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type*} [Category F]
    {p : F ⥤ Deformation.ArtinianLocalAlgCat Λ k}
    (hp : Deformation.IsCofiberedInGroupoids p)
    (ξ η : Deformation.FormalObject p) (hξ : Deformation.IsVersal hp ξ)
    (ηn : ℕ → Deformation.FormalObject p)
    (q : ∀ n, η ⟶ ηn n) (g : ∀ n, ηn (n + 1) ⟶ ηn n)
    (hq : ∀ n, Deformation.FormalObject.projection.IsHomLift
      (formalBaseQuotient η.base n) (q n))
    (hg : ∀ n, Deformation.FormalObject.projection.IsHomLift
      (Deformation.artinianToComplete.map
        (Deformation.AdicTruncation.transition η.base n)) (g n))
    (hqg : ∀ n, q (n + 1) ≫ g n = q n)
    (a₁ : ξ ⟶ ηn 1) (ha₁ : Function.Surjective a₁.base.hom) :
    ∃ a : ξ ⟶ η, Function.Surjective a.base.hom ∧ a.base ≫ (q 1).base = a₁.base := by
  let Q := Deformation.FormalObject.projection (p := p)
  let (n : ℕ) := hq n
  let hn (n : ℕ) := IsHomLift.codomain_eq Q (formalBaseQuotient η.base n) (q n)
  have ha₁' : Function.Surjective (a₁.base ≫ eqToHom (hn 1)).hom := by
    have he {R S : Deformation.CompleteLocalAlgCat Λ k} (h : R = S) :
        Function.Surjective (eqToHom h).hom := by
      subst S
      exact Function.surjective_id
    exact (he (hn 1)).comp ha₁
  obtain ⟨a, an, hsurj, han₁, han, ha⟩ :=
    exists_surjective_base_lift_extending_second_reduction hp ξ η hξ
      ηn hn g hg a₁ ha₁'
  have ha' (n : ℕ) : a ≫ (q n).base = (an n).base := by
    apply (cancel_mono (eqToHom (hn n))).1
    rw [Category.assoc, base_comp_eqToHom_eq_formalBaseQuotient (q n) (hq n), ha]
  obtain ⟨f, hf⟩ := exists_formal_map_of_reduction_maps ξ η ηn q g hqg
    (fun n => isIso_app_of_formal_reduction hp (q n) (hq n) le_rfl) an han a ha'
  refine ⟨f, hf.symm ▸ hsurj, ?_⟩
  rw [hf, ha', han₁]

/-- A surjection between modules of the same finite length is injective. -/
private theorem injective_of_surjective_of_length_eq
    {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [IsArtinian R M] [IsNoetherian R M]
    (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (hlen : Module.length R M = Module.length R N) : Function.Injective f := by
  apply LinearMap.ker_eq_bot.mp
  by_contra hk
  have hlt := f.ker.length_quotient_lt hk
  have heq := (f.quotKerEquivOfSurjective hf).length_eq
  rw [heq, ← hlen] at hlt
  exact lt_irrefl _ hlt

-- A semilinear equivalence over an isomorphism of scalar rings preserves length:
-- `Module.length_eq_of_semilinearEquiv`, non-private in
-- `StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.StalkRingComparison`. A `private`
-- re-declaration with the identical statement stood here and was never used.

/-- Injectivity on all positive truncations implies injectivity on a complete local base. -/
private theorem injective_of_injective_truncations
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {R S : Deformation.CompleteLocalAlgCat Λ k} (f : R ⟶ S)
    (hf : ∀ n, Function.Injective (Deformation.AdicTruncation.map f n).hom) :
    Function.Injective f.hom := by
  intro x y hxy
  have h : (fun _ : Unit => x) = fun _ => y := by
    apply IsHausdorff.StrictMono.funext' (maximalIdeal R)
      (show StrictMono (fun n : ℕ => n + 1) from fun _ _ h => Nat.add_lt_add_right h 1)
    intro n _
    apply hf n
    show Ideal.Quotient.mk (maximalIdeal S ^ (n + 1)) (f.hom x) =
      Ideal.Quotient.mk (maximalIdeal S ^ (n + 1)) (f.hom y)
    rw [hxy]
  exact congrFun h ()

/-- A bijective morphism of complete local algebras is an isomorphism. -/
private theorem isIso_of_bijective_completeLocalHom
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {R S : Deformation.CompleteLocalAlgCat Λ k} (f : R ⟶ S)
    (hf : Function.Bijective f.hom) : IsIso f := by
  let e := AlgEquiv.ofBijective f.hom hf
  let g : S ⟶ R := {
    hom := e.symm.toAlgHom
    isLocal := IsLocalHom.of_surjective _ e.symm.surjective
    residue_comm := fun s => by
      show R.residueEquiv (residue R (e.symm s)) = S.residueEquiv (residue S s)
      have h := f.residue_comm (e.symm s)
      change S.residueEquiv (residue S (e (e.symm s))) =
        R.residueEquiv (residue R (e.symm s)) at h
      simpa only [AlgEquiv.apply_symm_apply] using h.symm }
  let eC : R ≅ S := {
    hom := f
    inv := g
    hom_inv_id := by
      apply Deformation.CompleteLocalAlgCat.Hom.ext
      exact AlgHom.ext e.symm_apply_apply
    inv_hom_id := by
      apply Deformation.CompleteLocalAlgCat.Hom.ext
      exact AlgHom.ext e.apply_symm_apply }
  exact eC.isIso_hom

/-- A map of formal objects with bijective base map is an isomorphism. -/
private theorem isIso_of_bijective_base
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type*} [Category F]
    {p : F ⥤ Deformation.ArtinianLocalAlgCat Λ k}
    (hp : Deformation.IsCofiberedInGroupoids p)
    {ξ η : Deformation.FormalObject p} (a : ξ ⟶ η)
    (ha : Function.Bijective a.base.hom) : IsIso a := by
  let Q := Deformation.FormalObject.projection (p := p)
  have hQ := Deformation.formalObjectProjection_isCofiberedInGroupoids p hp
  have : IsIso a.base := isIso_of_bijective_completeLocalHom a.base ha
  have : Q.IsStronglyCocartesian a.base a :=
    isStronglyCocartesian_of_isCofiberedInGroupoids hQ a.base a (IsHomLift.map Q a)
  exact Functor.IsStronglyCocartesian.isIso_of_base_isIso Q a.base a

/-- A map of formal objects with bijective base map transports versality. -/
private theorem isVersal_of_bijective_base
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type*} [Category F]
    {p : F ⥤ Deformation.ArtinianLocalAlgCat Λ k}
    (hp : Deformation.IsCofiberedInGroupoids p)
    {ξ η : Deformation.FormalObject p} (a : ξ ⟶ η)
    (ha : Function.Bijective a.base.hom) (hξ : Deformation.IsVersal hp ξ) :
    Deformation.IsVersal hp η := by
  have := isIso_of_bijective_base hp a ha
  exact isVersal_of_iso hp (asIso a) hξ

/-- A surjection of Artinian rings with equal lengths as modules over themselves
is an isomorphism on the underlying sets. -/
private theorem bijective_of_surjective_of_ring_length_eq
    {R S : Type*} [CommRing R] [CommRing S] [IsArtinianRing R]
    (f : R →+* S) (hf : Function.Surjective f)
    (hlen : Module.length R R = Module.length S S) : Function.Bijective f := by
  let : Algebra R S := f.toAlgebra
  have hlen' : Module.length R R = Module.length R S := by
    rw [Module.length_eq_of_surjective (R := S) (M := S) (S := R) hf]
    exact hlen
  exact ⟨injective_of_surjective_of_length_eq (Algebra.linearMap R S) hf hlen', hf⟩

/-- Equal lengths of all adic quotients make a surjective complete-local map
bijective. -/
private theorem bijective_of_surjective_of_truncation_length_eq
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {R S : Deformation.CompleteLocalAlgCat Λ k} (f : R ⟶ S)
    (hf : Function.Surjective f.hom)
    (hlen : ∀ n,
      Module.length (Deformation.AdicTruncation.obj R n)
        (Deformation.AdicTruncation.obj R n) =
      Module.length (Deformation.AdicTruncation.obj S n)
        (Deformation.AdicTruncation.obj S n)) : Function.Bijective f.hom := by
  refine ⟨injective_of_injective_truncations f (fun n => ?_), hf⟩
  apply (bijective_of_surjective_of_ring_length_eq
    (Deformation.AdicTruncation.map f n).hom.toRingHom _ (hlen n)).1
  intro y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨x, hx⟩ := hf y
  exact ⟨Ideal.Quotient.mk _ x, congrArg (Ideal.Quotient.mk _) hx⟩

/-- A quotient ring has the same length over itself as over the original ring. -/
private theorem length_quotient_eq_length_self
    {R : Type*} [CommRing R] (I : Ideal R) :
    Module.length R (R ⧸ I) = Module.length (R ⧸ I) (R ⧸ I) :=
  Module.length_eq_of_surjective (S := R) (R := R ⧸ I) (M := R ⧸ I)
    Ideal.Quotient.mk_surjective

/-- Equal adic lengths upgrade the surjective map assembled from versal lifts
to an isomorphism of formal objects. -/
theorem exists_formal_iso_of_second_reduction_of_length_eq
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type*} [Category F]
    {p : F ⥤ Deformation.ArtinianLocalAlgCat Λ k}
    (hp : Deformation.IsCofiberedInGroupoids p)
    (ξ η : Deformation.FormalObject p) (hξ : Deformation.IsVersal hp ξ)
    (ηn : ℕ → Deformation.FormalObject p)
    (q : ∀ n, η ⟶ ηn n) (g : ∀ n, ηn (n + 1) ⟶ ηn n)
    (hq : ∀ n, Deformation.FormalObject.projection.IsHomLift
      (formalBaseQuotient η.base n) (q n))
    (hg : ∀ n, Deformation.FormalObject.projection.IsHomLift
      (Deformation.artinianToComplete.map
        (Deformation.AdicTruncation.transition η.base n)) (g n))
    (hqg : ∀ n, q (n + 1) ≫ g n = q n)
    (a₁ : ξ ⟶ ηn 1) (ha₁ : Function.Surjective a₁.base.hom)
    (hlen : ∀ n,
      Module.length (Deformation.AdicTruncation.obj ξ.base n)
        (Deformation.AdicTruncation.obj ξ.base n) =
      Module.length (Deformation.AdicTruncation.obj η.base n)
        (Deformation.AdicTruncation.obj η.base n)) :
    Nonempty (ξ ≅ η) ∧ Deformation.IsVersal hp η := by
  obtain ⟨a, ha, _⟩ := exists_surjective_formal_lift_of_second_reduction hp ξ η hξ
    ηn q g hq hg hqg a₁ ha₁
  have hab := bijective_of_surjective_of_truncation_length_eq a.base ha hlen
  have := isIso_of_bijective_base hp a hab
  exact ⟨⟨asIso a⟩, isVersal_of_iso hp (asIso a) hξ⟩

private theorem exists_degreewise_addEquiv
    {ι : Type*} [DecidableEq ι] {M N : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, AddCommGroup (N i)]
    (e : DirectSum ι M ≃+ DirectSum ι N)
    (he : ∀ i x, ∃ y, e (DirectSum.of M i x) = DirectSum.of N i y) :
    ∃ f : ∀ i, M i ≃+ N i,
      ∀ i x, DirectSum.of N i (f i x) = e (DirectSum.of M i x) := by
  let f (i : ι) : M i →+ N i :=
    (DirectSum.component ℤ ι N i).toAddMonoidHom.comp
      (e.toAddMonoidHom.comp (DirectSum.of M i))
  have hf (i : ι) (x : M i) : DirectSum.of N i (f i x) = e (DirectSum.of M i x) := by
    obtain ⟨y, hy⟩ := he i x
    simp only [f, AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe, LinearMap.toAddMonoidHom_coe]
    rw [hy]
    show DirectSum.of N i ((DirectSum.component ℤ ι N i)
      (DirectSum.lof ℤ ι N i y)) = _
    rw [DirectSum.component.lof_self]
  have hmap : DirectSum.map f = e.toAddMonoidHom := by
    apply DirectSum.addHom_ext
    intro i x
    exact (DirectSum.map_of f i x).trans (hf i x)
  have hfi : ∀ i, Function.Injective (f i) :=
    (DirectSum.map_injective f).1 (hmap.symm ▸ e.injective)
  have hfs : ∀ i, Function.Surjective (f i) :=
    (DirectSum.map_surjective f).1 (hmap.symm ▸ e.surjective)
  exact ⟨fun i => AddEquiv.ofBijective (f i) ⟨hfi i, hfs i⟩, hf⟩

private theorem associatedGraded_cast_mk
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) {i j : ℕ} (h : i = j)
    (a : AssociatedGraded.power (M := M) I i)
    (b : AssociatedGraded.power (M := M) I j) (hab : (a : M) = b) :
    cast (congrArg (AssociatedGraded.piece (M := M) I) h)
      (AssociatedGraded.mk I i a) = AssociatedGraded.mk I j b := by
  subst j
  have : a = b := Subtype.ext hab
  subst b
  rfl

private theorem associatedGraded_of_smul
    {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) (r : R)
    (z : AssociatedGraded.piece (M := R) I n) :
    DirectSum.of _ n (r • z) =
      DirectSum.of _ 0 (AssociatedGraded.mk I 0 ⟨r, by simp⟩) *
        DirectSum.of _ n z := by
  induction z using Quotient.inductionOn with
  | h z =>
    rw [AssociatedGraded.of_mul_of]
    show DirectSum.of _ n (AssociatedGraded.mk I n (r • z)) =
      DirectSum.of _ (0 + n) (AssociatedGraded.mk I (0 + n)
        ⟨r * z.val, AssociatedGraded.smul_mem_power I (by simp) z.property⟩)
    apply Eq.symm
    apply DirectSum.of_eq_of_gradedMonoid_eq
    exact Sigma.ext (zero_add n)
      (heq_of_cast_eq (congrArg (AssociatedGraded.piece (M := R) I) (zero_add n))
        (associatedGraded_cast_mk I (zero_add n) _ (r • z) rfl))

private theorem exists_gradedPiece_linearEquiv
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (J : Ideal S)
    (e : AssociatedGraded.gradedRing I ≃+* AssociatedGraded.gradedRing J)
    (he : ∀ n z, ∃ w, e (DirectSum.of _ n z) = DirectSum.of _ n w)
    (he₀ : ∀ r, e (DirectSum.of _ 0 (AssociatedGraded.mk I 0 ⟨r, by simp⟩)) =
      DirectSum.of _ 0 (AssociatedGraded.mk J 0 ⟨algebraMap R S r, by simp⟩)) :
    ∀ n, Nonempty (AssociatedGraded.piece (M := R) I n ≃ₗ[R]
      AssociatedGraded.piece (M := S) J n) := by
  obtain ⟨f, hf⟩ := exists_degreewise_addEquiv e.toAddEquiv he
  intro n
  refine ⟨{ f n with map_smul' := ?_ }⟩
  intro r z
  apply DirectSum.of_injective n
  show DirectSum.of _ n (f n (r • z)) = DirectSum.of _ n (r • f n z)
  rw [hf]
  show e (DirectSum.of _ n (r • z)) = _
  rw [associatedGraded_of_smul, map_mul, he₀]
  show _ * e.toAddEquiv (DirectSum.of _ n z) = _
  rw [← hf]
  simpa only [algebraMap_smul] using
    (associatedGraded_of_smul J n (algebraMap R S r) (f n z)).symm

private theorem length_quotient_eq_subquotient_add
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (P Q : Submodule R M) (hPQ : P ≤ Q) :
    Module.length R (M ⧸ P) =
      Module.length R (Q ⧸ P.comap Q.subtype) + Module.length R (M ⧸ Q) := by
  let i : (Q ⧸ P.comap Q.subtype) →ₗ[R] M ⧸ P :=
    (P.comap Q.subtype).liftQ (P.mkQ.comp Q.subtype) (by
      intro x hx
      exact (Submodule.Quotient.mk_eq_zero P).2 hx)
  let j : (M ⧸ P) →ₗ[R] M ⧸ Q := P.mapQ Q LinearMap.id hPQ
  apply Module.length_eq_add_of_exact i j
  · apply (injective_iff_map_eq_zero i).2
    intro x hx
    induction x using Quotient.inductionOn with
    | h x =>
      change Submodule.Quotient.mk (x : M) = 0 at hx
      exact (Submodule.Quotient.mk_eq_zero _).2 ((Submodule.Quotient.mk_eq_zero P).1 hx)
  · intro y
    induction y using Quotient.inductionOn with
    | h y => exact ⟨Submodule.Quotient.mk y, rfl⟩
  · intro y
    induction y using Quotient.inductionOn with
    | h y =>
      constructor
      · intro hy
        have hyQ : y ∈ Q := (Submodule.Quotient.mk_eq_zero Q).1 hy
        exact ⟨Submodule.Quotient.mk (⟨y, hyQ⟩ : Q), rfl⟩
      · rintro ⟨x, hx⟩
        rw [← hx]
        induction x using Quotient.inductionOn with
        | h x => exact (Submodule.Quotient.mk_eq_zero Q).2 x.property

private theorem length_quotient_pow_eq_sum
    {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    Module.length R (R ⧸ I ^ n) =
      ∑ i ∈ Finset.range n, Module.length R (AssociatedGraded.piece (M := R) I i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [length_quotient_eq_subquotient_add (I ^ (n + 1)) (I ^ n)
      (Ideal.pow_le_pow_right (Nat.le_succ n)), ih, Finset.sum_range_succ]
    rw [add_comm]
    congr 1
    have hcongr (P P' Q Q' : Submodule R R) (hP : P = P') (hQ : Q = Q') :
        Module.length R (P ⧸ Q.comap P.subtype) =
          Module.length R (P' ⧸ Q'.comap P'.subtype) := by
      subst P'
      subst Q'
      rfl
    exact hcongr _ _ _ _ (AssociatedGraded.ring_power_eq I n).symm
      (AssociatedGraded.ring_power_eq I (n + 1)).symm

private theorem length_quotient_pow_eq_of_graded_equiv
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (hsurj : Function.Surjective (algebraMap R S))
    (I : Ideal R) (J : Ideal S)
    (e : AssociatedGraded.gradedRing I ≃+* AssociatedGraded.gradedRing J)
    (he : ∀ n z, ∃ w, e (DirectSum.of _ n z) = DirectSum.of _ n w)
    (he₀ : ∀ r, e (DirectSum.of _ 0 (AssociatedGraded.mk I 0 ⟨r, by simp⟩)) =
      DirectSum.of _ 0 (AssociatedGraded.mk J 0 ⟨algebraMap R S r, by simp⟩))
    (n : ℕ) :
    Module.length R (R ⧸ I ^ n) = Module.length S (S ⧸ J ^ n) := by
  rw [length_quotient_pow_eq_sum, length_quotient_pow_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨ei⟩ := exists_gradedPiece_linearEquiv I J e he he₀ i
  rw [ei.length_eq]
  exact Module.length_eq_of_surjective hsurj

private theorem length_eq_of_addEquiv_of_smul
    {R S M N : Type*} [Ring R] [Ring S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (e : M ≃+ N)
    (hf : ∀ r : R, ∃ s : S, ∀ x, e (r • x) = s • e x)
    (hb : ∀ s : S, ∃ r : R, ∀ x, e (r • x) = s • e x) :
    Module.length R M = Module.length S N := by
  let f (P : Submodule R M) : Submodule S N := {
    carrier := {y | e.symm y ∈ P}
    zero_mem' := by simp
    add_mem' hx hy := by simpa using P.add_mem hx hy
    smul_mem' := by
      intro s y hy
      obtain ⟨r, hr⟩ := hb s
      have h : e.symm (s • y) = r • e.symm y := by
        apply e.injective
        simpa using (hr (e.symm y)).symm
      show e.symm (s • y) ∈ P
      rw [h]
      exact P.smul_mem r hy }
  let g (Q : Submodule S N) : Submodule R M := {
    carrier := {x | e x ∈ Q}
    zero_mem' := by simp
    add_mem' hx hy := by simpa using Q.add_mem hx hy
    smul_mem' := by
      intro r x hx
      obtain ⟨s, hs⟩ := hf r
      show e (r • x) ∈ Q
      rw [hs x]
      exact Q.smul_mem s hx }
  let E : Submodule R M ≃o Submodule S N := {
    toFun := f
    invFun := g
    left_inv P := by ext; simp [f, g]
    right_inv Q := by ext; simp [f, g]
    map_rel_iff' := by
      intro P Q
      constructor
      · intro h x hx
        have hh := h (show e x ∈ f P by simpa [f] using hx)
        simpa [f] using hh
      · intro h y hy
        exact h hy }
  rw [Module.length_eq_height, Module.length_eq_height, ← E.map_top]
  exact (Order.height_orderIso E ⊤).symm

private theorem length_gradedPiece_eq_of_graded_equiv
    {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S)
    (e : AssociatedGraded.gradedRing I ≃+* AssociatedGraded.gradedRing J)
    (he : ∀ n z, ∃ w, e (DirectSum.of _ n z) = DirectSum.of _ n w)
    (n : ℕ) :
    Module.length R (AssociatedGraded.piece (M := R) I n) =
      Module.length S (AssociatedGraded.piece (M := S) J n) := by
  obtain ⟨f, hf⟩ := exists_degreewise_addEquiv e.toAddEquiv he
  have hf (i : ℕ) (z : AssociatedGraded.piece (M := R) I i) :
      DirectSum.of _ i (f i z) = e (DirectSum.of _ i z) := hf i z
  have hscalar (r : R) (s : S)
      (h : e (DirectSum.of _ 0 (AssociatedGraded.mk I 0 ⟨r, by simp⟩)) =
        DirectSum.of _ 0 (AssociatedGraded.mk J 0 ⟨s, by simp⟩))
      (z : AssociatedGraded.piece (M := R) I n) :
      f n (r • z) = s • f n z := by
    apply DirectSum.of_injective n
    rw [hf, associatedGraded_of_smul, map_mul, h, ← hf]
    exact (associatedGraded_of_smul J n s (f n z)).symm
  apply length_eq_of_addEquiv_of_smul (f n)
  · intro r
    obtain ⟨w, hw⟩ := he 0 (AssociatedGraded.mk I 0 ⟨r, by simp⟩)
    induction w using Quotient.inductionOn with
    | h w => exact ⟨w.val, fun z => hscalar r w.val hw z⟩
  · intro s
    obtain ⟨z, hz⟩ := (f 0).surjective (AssociatedGraded.mk J 0 ⟨s, by simp⟩)
    induction z using Quotient.inductionOn with
    | h z =>
      refine ⟨z.val, fun w => hscalar z.val s ?_ w⟩
      rw [← hf]
      exact congrArg (DirectSum.of _ 0) hz

private theorem length_quotient_pow_eq_of_graded_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S)
    (e : AssociatedGraded.gradedRing I ≃+* AssociatedGraded.gradedRing J)
    (he : ∀ n z, ∃ w, e (DirectSum.of _ n z) = DirectSum.of _ n w)
    (n : ℕ) :
    Module.length R (R ⧸ I ^ n) = Module.length S (S ⧸ J ^ n) := by
  rw [length_quotient_pow_eq_sum, length_quotient_pow_eq_sum]
  exact Finset.sum_congr rfl (fun i _ => length_gradedPiece_eq_of_graded_equiv I J e he i)

/-- A surjective complete-local morphism compatible in degree zero with a graded
ring isomorphism is bijective. -/
private theorem bijective_of_surjective_of_graded_equiv
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {R S : Deformation.CompleteLocalAlgCat Λ k} (f : R ⟶ S)
    (hf : Function.Surjective f.hom)
    (gr : AssociatedGraded.gradedRing (maximalIdeal R) ≃+*
      AssociatedGraded.gradedRing (maximalIdeal S))
    (hgr : ∀ n z, ∃ w, gr (DirectSum.of _ n z) = DirectSum.of _ n w)
    (hgr₀ : ∀ r, gr (DirectSum.of _ 0
      (AssociatedGraded.mk (maximalIdeal R) 0 ⟨r, by simp⟩)) =
      DirectSum.of _ 0 (AssociatedGraded.mk (maximalIdeal S) 0 ⟨f.hom r, by simp⟩)) :
    Function.Bijective f.hom := by
  let : Algebra R S := f.hom.toRingHom.toAlgebra
  apply bijective_of_surjective_of_truncation_length_eq f hf
  intro n
  show Module.length (R ⧸ maximalIdeal R ^ (n + 1)) (R ⧸ maximalIdeal R ^ (n + 1)) =
    Module.length (S ⧸ maximalIdeal S ^ (n + 1)) (S ⧸ maximalIdeal S ^ (n + 1))
  calc
    _ = Module.length R (R ⧸ maximalIdeal R ^ (n + 1)) :=
      (length_quotient_eq_length_self _).symm
    _ = Module.length S (S ⧸ maximalIdeal S ^ (n + 1)) :=
      length_quotient_pow_eq_of_graded_equiv hf (maximalIdeal R) (maximalIdeal S)
        gr hgr hgr₀ (n + 1)
    _ = _ := length_quotient_eq_length_self _

/-- The completed localization at a maximal ideal has the original finite
maximal-ideal quotients. -/
noncomputable def completedLocalizationQuotientEquiv
    {R : Type*} [CommRing R] (m : Ideal R) [m.IsMaximal]
    (Rₘ : Type*) [CommRing Rₘ] [Algebra R Rₘ] [IsLocalization.AtPrime Rₘ m]
    [IsLocalRing Rₘ] [IsNoetherianRing Rₘ] (n : ℕ) :
    (AdicCompletion (maximalIdeal Rₘ) Rₘ ⧸
      maximalIdeal (AdicCompletion (maximalIdeal Rₘ) Rₘ) ^ n) ≃+* R ⧸ m ^ n :=
  (completionQuotientEquiv Rₘ n).trans
    (IsLocalization.AtPrime.equivQuotMaximalIdealPow m Rₘ n).symm.toRingEquiv

private theorem completedLocalizationQuotientEquiv_mk
    {R : Type*} [CommRing R] (m : Ideal R) [m.IsMaximal]
    (Rₘ : Type*) [CommRing Rₘ] [Algebra R Rₘ] [IsLocalization.AtPrime Rₘ m]
    [IsLocalRing Rₘ] [IsNoetherianRing Rₘ] (n : ℕ) (r : R) :
    completedLocalizationQuotientEquiv m Rₘ n (Ideal.Quotient.mk _
      (algebraMap Rₘ (AdicCompletion (maximalIdeal Rₘ) Rₘ) (algebraMap R Rₘ r))) =
        Ideal.Quotient.mk _ r := by
  simp only [completedLocalizationQuotientEquiv, RingEquiv.trans_apply,
    completionQuotientEquiv_mk]
  apply (IsLocalization.AtPrime.equivQuotMaximalIdealPow m Rₘ n).injective
  show (IsLocalization.AtPrime.equivQuotMaximalIdealPow m Rₘ n)
    ((IsLocalization.AtPrime.equivQuotMaximalIdealPow m Rₘ n).symm _) = _
  rw [AlgEquiv.apply_symm_apply,
    IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk]

theorem completedLocalizationQuotientEquiv_spec
    {R : Type u} [CommRing R] (m : Ideal R) [m.IsMaximal]
    (Rₘ : Type u) [CommRing Rₘ] [Algebra R Rₘ] [IsLocalization.AtPrime Rₘ m]
    [IsLocalRing Rₘ] [IsNoetherianRing Rₘ] (n : ℕ) :
    Spec.map (CommRingCat.ofHom (completedLocalizationQuotientEquiv m Rₘ n).symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (m ^ n))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (maximalIdeal (AdicCompletion (maximalIdeal Rₘ) Rₘ) ^ n))) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap Rₘ (AdicCompletion (maximalIdeal Rₘ) Rₘ))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R Rₘ)) := by
  simp only [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (completedLocalizationQuotientEquiv m Rₘ n).symm_apply_eq.mpr
    (completedLocalizationQuotientEquiv_mk m Rₘ n r).symm

theorem length_quotient_pow_eq_length_completedLocalization
    {R A : Type*} [CommRing R] [CommRing A]
    (I : Ideal R) (m : Ideal A) [m.IsMaximal]
    (L : Type*) [CommRing L] [Algebra A L] [IsLocalization.AtPrime L m]
    [IsLocalRing L] [IsNoetherianRing L]
    (e : AssociatedGraded.gradedRing I ≃+* AssociatedGraded.gradedRing m)
    (he : ∀ n z, ∃ w, e (DirectSum.of _ n z) = DirectSum.of _ n w) (n : ℕ) :
    Module.length (R ⧸ I ^ n) (R ⧸ I ^ n) =
      Module.length (AdicCompletion (maximalIdeal L) L ⧸
        maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n)
        (AdicCompletion (maximalIdeal L) L ⧸
          maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n) := by
  calc
    _ = Module.length R (R ⧸ I ^ n) := (length_quotient_eq_length_self _).symm
    _ = Module.length A (A ⧸ m ^ n) :=
      length_quotient_pow_eq_of_graded_ringEquiv I m e he n
    _ = Module.length (A ⧸ m ^ n) (A ⧸ m ^ n) := length_quotient_eq_length_self _
    _ = _ := (Module.length_eq_of_ringEquiv (completedLocalizationQuotientEquiv m L n)).symm

-- An adic completion has at most as many elements as the ring's sequences:
-- `AlgebraicGeometry.cardinal_mk_adicCompletion_le`, public in
-- `StacksFrontier.AlgebraicGeometry.Topologies.FppfCompletedLocalRing` (closure 18; +1 module
-- here). A `private` re-declaration in the same namespace, with the identical statement and
-- the identical proof save for one bound variable name, stood here.

/-- The size cutoff of a big fppf site is closed under adic completion of rings. -/
theorem contains_spec_adicCompletion
    (B : AlgebraicGeometry.BigFppfSite.{u}) {R : Type u} [CommRing R]
    (hR : B.Contains (Spec (.of R))) (I : Ideal R) :
    B.Contains (Spec (.of (AdicCompletion I R))) := by
  apply Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    (.of (AdicCompletion I R)) hR
  apply (cardinal_mk_adicCompletion_le I).trans
  apply Cardinal.power_le_power_right
  rw [Scheme.size_Spec]
  exact le_max_right _ _

/-- The map on complete local bases respects composition of formal-object maps. -/
theorem formalBaseMap_comp
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : Type v} [Category.{w} F]
    {p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS}
    {X Y Z : Deformation.Artin.FormalObject B S hS p}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).baseMap = f.baseMap ≫ g.baseMap := by
  let tmap {X Y : Deformation.Artin.FormalObject B S hS p}
      (h : X ⟶ Y) (n : ℕ) :=
    (eqToHom (X.level_eq n).symm ≫ p.map (h.app n) ≫
      eqToHom (Y.level_eq n)).left.hom
  have hmap (n : ℕ) : tmap (f ≫ g) n = tmap f n ≫ tmap g n := by
    dsimp [tmap]
    have h :
        (eqToHom (X.level_eq n).symm ≫
          p.map (f.app n ≫ g.app n) ≫ eqToHom (Z.level_eq n)) =
        (eqToHom (X.level_eq n).symm ≫ p.map (f.app n) ≫
          eqToHom (Y.level_eq n)) ≫
        (eqToHom (Y.level_eq n).symm ≫ p.map (g.app n) ≫
          eqToHom (Z.level_eq n)) := by
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp]
      rw [Functor.map_comp]
      simp [Category.assoc]
    exact congrArg (fun a => a.left.hom) h
  apply Eq.symm
  apply Deformation.Artin.FormalObject.Hom.baseMap_unique (f ≫ g)
    (f.baseMap ≫ g.baseMap)
  constructor
  · calc
      (f.baseMap ≫ g.baseMap) ≫ Z.base.toS =
          f.baseMap ≫ (g.baseMap ≫ Z.base.toS) := by rw [Category.assoc]
      _ = f.baseMap ≫ Y.base.toS := by
        rw [(Deformation.Artin.FormalObject.Hom.baseMap_spec g).1]
      _ = X.base.toS := (Deformation.Artin.FormalObject.Hom.baseMap_spec f).1
  · intro n
    have hf := (Deformation.Artin.FormalObject.Hom.baseMap_spec f).2 n
    have hg := (Deformation.Artin.FormalObject.Hom.baseMap_spec g).2 n
    dsimp only [Deformation.Artin.truncationOver, Deformation.Artin.FormalBase.truncation]
      at hf hg ⊢
    show tmap (f ≫ g) n ≫
      AlgebraicGeometry.adicThickeningι Z.base.R (maximalIdeal Z.base.R) n =
        AlgebraicGeometry.adicThickeningι X.base.R (maximalIdeal X.base.R) n ≫
          (f.baseMap ≫ g.baseMap)
    rw [hmap]
    calc
      (tmap f n ≫ tmap g n) ≫
          AlgebraicGeometry.adicThickeningι Z.base.R (maximalIdeal Z.base.R) n =
        tmap f n ≫ (tmap g n ≫
          AlgebraicGeometry.adicThickeningι Z.base.R (maximalIdeal Z.base.R) n) := by
            rw [Category.assoc]
      _ = tmap f n ≫ (AlgebraicGeometry.adicThickeningι Y.base.R
          (maximalIdeal Y.base.R) n ≫ g.baseMap) := by rw [hg]
      _ = (tmap f n ≫ AlgebraicGeometry.adicThickeningι Y.base.R
          (maximalIdeal Y.base.R) n) ≫ g.baseMap := by rw [Category.assoc]
      _ = (AlgebraicGeometry.adicThickeningι X.base.R (maximalIdeal X.base.R) n ≫
          f.baseMap) ≫ g.baseMap := by rw [hf]
      _ = AlgebraicGeometry.adicThickeningι X.base.R (maximalIdeal X.base.R) n ≫
          (f.baseMap ≫ g.baseMap) := by rw [Category.assoc]

theorem formalBaseMap_id
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : Type v} [Category.{w} F]
    {p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS}
    (X : Deformation.Artin.FormalObject B S hS p) :
    ((𝟙 X : X ⟶ X)).baseMap = 𝟙 _ := by
  apply Eq.symm
  apply Deformation.Artin.FormalObject.Hom.baseMap_unique (𝟙 X : X ⟶ X) (𝟙 _)
  constructor
  · simp
  · intro n
    show (eqToHom (X.level_eq n).symm ≫ p.map (𝟙 (X.level n)) ≫
      eqToHom (X.level_eq n)).left.hom ≫
        AlgebraicGeometry.adicThickeningι X.base.R (maximalIdeal X.base.R) n =
      AlgebraicGeometry.adicThickeningι X.base.R (maximalIdeal X.base.R) n
    simp

noncomputable def formalBaseMapIso
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : Type v} [Category.{w} F]
    {p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS}
    {X Y : Deformation.Artin.FormalObject B S hS p} (e : X ≅ Y) :
    Spec (.of X.base.R) ≅ Spec (.of Y.base.R) where
  hom := e.hom.baseMap
  inv := e.inv.baseMap
  hom_inv_id := by
    rw [← formalBaseMap_comp]
    rw [e.hom_inv_id, formalBaseMap_id]
  inv_hom_id := by
    rw [← formalBaseMap_comp]
    rw [e.inv_hom_id, formalBaseMap_id]

end Deformation.Artin

end
