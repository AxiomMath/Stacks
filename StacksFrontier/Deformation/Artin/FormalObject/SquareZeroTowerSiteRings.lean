module

public import StacksFrontier.Deformation.Artin.FormalObject.SquareZeroTower
public import StacksFrontier.Deformation.Artin.Infinitesimal.AugmentedLiftClasses

/-!
# The rings of a square-zero tower as augmented rings of the site

Let `⋯ → R₂ → R₁ → R₀ = A` be a tower of square-zero thickenings of `A` (see
`Deformation.Artin.SquareZeroTower`), all of whose spectra lie in the chosen big fppf site, and
all of which are algebras under a fixed augmented ring `R` of the site compatibly with the
transition maps. This file realizes the rings of the proof of Stacks 0CYF — the levels `Rₙ`, the
ring `R̃` of sequences with a common base, the inverse limit and the trivial square-zero
extension `A[∏ Mₙ]` — as augmented rings under `R`, together with the maps between them.

The only input beyond the algebra is a size bound: the spectrum of a countable product of rings
whose spectra lie in the site again lies in the site, because the cutoff of the site is a strong
limit of uncountable cofinality.

## Main definitions

* `Deformation.Artin.SquareZeroTower.level`, `Deformation.Artin.SquareZeroTower.transition` — the
  levels and the transition maps.
* `Deformation.Artin.SquareZeroTower.sameBaseRing`, `Deformation.Artin.SquareZeroTower.projMap` —
  the ring `R̃` and its projections.
* `Deformation.Artin.SquareZeroTower.limitRing`, `Deformation.Artin.SquareZeroTower.limitMap` —
  the inverse limit and its inclusion into `R̃`.

## Main results

* `Deformation.Artin.SquareZeroTower.contains_spec_pi` — the size bound.

## References

* [Stacks Project, Tag 0CYF](https://stacks.math.columbia.edu/tag/0CYF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Deformation.Artin.SquareZeroTower

/-- The spectrum of a countable product of rings whose spectra lie in the site lies in the
site. -/
public theorem contains_spec_pi (B : BigFppfSite.{u}) {R : ℕ → Type u} [∀ n, CommRing (R n)]
    (hR : ∀ n, B.Contains (Spec (.of (R n)))) : B.Contains (Spec (.of (∀ n, R n))) := by
  show (Spec (CommRingCat.of (∀ n, R n))).size < B.cutoff
  have hlt : ∀ n, max Cardinal.aleph0 (Cardinal.mk (R n)) < B.cutoff := fun n => by
    have h : (Spec (CommRingCat.of (R n))).size < B.cutoff := hR n
    rwa [Scheme.size_Spec] at h
  let lam : Cardinal.{u} := ⨆ n : ULift.{u} ℕ, max Cardinal.aleph0 (Cardinal.mk (R n.down))
  have hlam : lam < B.cutoff := by
    refine Cardinal.iSup_lt_of_lt_cof_ord (f := fun n : ULift.{u} ℕ =>
      max Cardinal.aleph0 (Cardinal.mk (R n.down))) ?_ (fun n => hlt n.down)
    simpa using B.aleph0_lt_cutoff_cof
  have hbdd : BddAbove (Set.range fun n : ULift.{u} ℕ =>
      max Cardinal.aleph0 (Cardinal.mk (R n.down))) :=
    ⟨B.cutoff, by rintro _ ⟨n, rfl⟩; exact (hlt n.down).le⟩
  have hle : ∀ n, Cardinal.mk (R n) ≤ lam := fun n =>
    (le_max_right _ _).trans (le_ciSup hbdd (ULift.up n))
  have hmk : Cardinal.mk (∀ n, R n) ≤ lam ^ Cardinal.aleph0 := by
    rw [Cardinal.mk_pi]
    calc Cardinal.prod (fun n => Cardinal.mk (R n))
        ≤ Cardinal.prod (fun _ : ℕ => lam) := Cardinal.prod_le_prod _ _ hle
      _ = lam ^ Cardinal.aleph0 := by
        rw [Cardinal.prod_const, Cardinal.mk_nat, Cardinal.lift_aleph0, Cardinal.lift_uzero]
  rw [Scheme.size_Spec]
  exact max_lt B.aleph0_lt_cutoff (hmk.trans_lt (Cardinal.power_aleph0_lt_of_isStrongPrelimit
    B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hlam))

section Rings

variable {R : ℕ → Type u} [∀ n, CommRing (R n)] (f : ∀ n, R (n + 1) →+* R n)
  (hf : ∀ n, Function.Surjective (f n)) (hsq : ∀ n, RingHom.ker (toBase f n) ^ 2 = ⊥)
  {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {toS : Spec (.of (R 0)) ⟶ S} {hA : B.Contains (Spec (.of (R 0)))}
  (Λ : AugmentedSiteRing (R 0) B S hS toS hA) (β : ∀ n, Λ.ring →+* R n)
  (hβ : ∀ n, (f n).comp (β (n + 1)) = β n) (hβ0 : β 0 = Λ.aug)
  (hR : ∀ n, B.Contains (Spec (.of (R n))))

include hβ hβ0 in
/-- The maps from `R` to the levels lie over the augmentation of `R`. -/
public theorem toBase_comp_eq : ∀ n, (toBase f n).comp (β n) = Λ.aug
  | 0 => by
    rw [← hβ0]
    rfl
  | n + 1 => by
    rw [← toBase_comp_eq n, ← hβ n]
    rfl

/-- The level `Rₙ` of the tower, as an augmented ring under `R`. -/
public def level (n : ℕ) : BasedSiteRing (R 0) B S hS toS hA Λ where
  toAugmentedSiteRing := AugmentedSiteRing.ofRing Λ (.of (R n)) (hR n) (toBase f n) (β n)
    (toBase_comp_eq f Λ β hβ hβ0 n)
  base := β n
  fac := toBase_comp_eq f Λ β hβ hβ0 n
  structure_fac := rfl

/-- The transition map `Rₙ₊₁ → Rₙ`. -/
public def transition (n : ℕ) :
    BasedSiteRing.RingMap (level f Λ β hβ hβ0 hR (n + 1)) (level f Λ β hβ hβ0 hR n) where
  hom := f n
  aug_fac := rfl
  base_fac := hβ n

/-- The augmentation `Rₙ → R₀`, as a map of augmented rings. -/
public def augMap (n : ℕ) :
    BasedSiteRing.RingMap (level f Λ β hβ hβ0 hR n) (level f Λ β hβ hβ0 hR 0) where
  hom := toBase f n
  aug_fac := RingHom.id_comp _
  base_fac := by
    change (toBase f n).comp (β n) = β 0
    rw [toBase_comp_eq f Λ β hβ hβ0 n, hβ0]

include hR in
/-- The spectrum of `R̃` lies in the site. -/
public theorem contains_sameBase : B.Contains (Spec (.of (sameBase f))) :=
  Scheme.size_Spec_lt_of_subring B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit (sameBase f)
    (contains_spec_pi B hR)

/-- The map from `R` to `R̃`, `r ↦ (β₀ r, β₁ r, …)`. -/
public def sameBaseBase : Λ.ring →+* sameBase f :=
  (Pi.ringHom β).codRestrict (sameBase f) fun l n => by
    change toBase f n (β n l) = β 0 l
    rw [← RingHom.comp_apply, toBase_comp_eq f Λ β hβ hβ0 n, hβ0]

/-- The ring `R̃` of sequences with a common base, as an augmented ring under `R`. -/
public def sameBaseRing : BasedSiteRing (R 0) B S hS toS hA Λ where
  toAugmentedSiteRing := AugmentedSiteRing.ofRing Λ (.of (sameBase f))
    (contains_sameBase f hR) (base f) (sameBaseBase f Λ β hβ hβ0) (by
      ext l
      change β 0 l = Λ.aug l
      rw [hβ0])
  base := sameBaseBase f Λ β hβ hβ0
  fac := by
    ext l
    change β 0 l = Λ.aug l
    rw [hβ0]
  structure_fac := rfl

/-- The projection `R̃ → Rₙ`. -/
public def projMap (n : ℕ) :
    BasedSiteRing.RingMap (sameBaseRing f Λ β hβ hβ0 hR) (level f Λ β hβ hβ0 hR n) where
  hom := proj f n
  aug_fac := toBase_comp_proj f n
  base_fac := rfl

/-- The kernel `Mₙ = Ker(Rₙ → R₀)` as a module of the site. -/
public def levelModule (n : ℕ) : SiteModule (R 0) B :=
  ⟨kerObj (toBase f n) (toBase_surjective f hf n) (hsq n), by
    let := Stacks.Smooth.kerModule (toBase_surjective f hf n) (hsq n)
    exact isSiteModule_kernel (R 0) B (hR n) (toBase f n) (toBase_surjective f hf n)⟩

include hR in
/-- The spectrum of `A[∏ Mₙ]` lies in the site. -/
public theorem isSiteModule_kernelProduct : IsSiteModule (R 0) B (kernelProduct f hf hsq) := by
  let := kernelModule f hf hsq
  let ι : squareZeroRing (R 0) (kernelProduct f hf hsq) → ∀ n, R n := fun z n =>
    if h : n = 0 then h ▸ TrivSqZeroExt.fst z else ((TrivSqZeroExt.snd z : ∀ n,
      RingHom.ker (toBase f n)) n : R n)
  have hι : Function.Injective ι := by
    intro z w hzw
    refine TrivSqZeroExt.ext ?_ (funext fun n => Subtype.ext ?_)
    · simpa [ι] using congrFun hzw 0
    · rcases n with _ | n
      · have h0 : ∀ m : RingHom.ker (toBase f 0), (m : R 0) = 0 := fun m => m.2
        rw [h0, h0]
      · have h := congrFun hzw (n + 1)
        simp only [ι, Nat.add_one_ne_zero, dite_false] at h
        exact h
  refine Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit _
    (contains_spec_pi B hR) ?_
  refine (Cardinal.mk_le_of_injective hι).trans ?_
  rw [Scheme.size_Spec]
  exact (le_max_right _ _).trans (Cardinal.self_le_power _ Cardinal.one_le_aleph0)

/-- The module `M = ∏ Mₙ` as a module of the site. -/
public def productModule : SiteModule (R 0) B :=
  ⟨kernelProduct f hf hsq, isSiteModule_kernelProduct f hf hsq hR⟩

/-- `A[∏ Mₙ]` as an augmented ring under `R`. -/
public abbrev productSquareZero : BasedSiteRing (R 0) B S hS toS hA Λ :=
  BasedSiteRing.squareZero Λ (productModule f hf hsq hR)

/-- `A[Mₙ]` as an augmented ring under `R`. -/
public abbrev levelSquareZero (n : ℕ) : BasedSiteRing (R 0) B S hS toS hA Λ :=
  BasedSiteRing.squareZero Λ (levelModule f hf hsq hR n)

/-- The difference map `R̃ → A[∏ Mₙ]`, as a map of augmented rings. -/
public def differenceMap :
    BasedSiteRing.RingMap (sameBaseRing f Λ β hβ hβ0 hR) (productSquareZero f hf hsq Λ hR) where
  hom := difference f hf hsq
  aug_fac := rfl
  base_fac := by
    refine RingHom.ext fun l => TrivSqZeroExt.ext ?_ (funext fun n => Subtype.ext ?_)
    · change β 0 l = Λ.aug l
      rw [hβ0]
    · change f n (β (n + 1) l) - β n l = 0
      rw [← RingHom.comp_apply, hβ, sub_self]

/-- The projection `∏ Mₙ → Mₙ`. -/
public def productProj (n : ℕ) : productModule f hf hsq hR ⟶ levelModule f hf hsq hR n :=
  letI := kernelModule f hf hsq
  ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.proj (R := R 0)
    (φ := fun n => RingHom.ker (toBase f n)) n))

/-- The map `A[∏ Mₙ] → A[Mₙ]` induced by the projection. -/
public abbrev squareZeroProj (n : ℕ) :
    BasedSiteRing.RingMap (productSquareZero f hf hsq Λ hR) (levelSquareZero f hf hsq Λ hR n) :=
  BasedSiteRing.squareZeroMap Λ (productProj f hf hsq hR n)

/-- The inclusion `A → A[∏ Mₙ]`. -/
public def inlMap :
    BasedSiteRing.RingMap (level f Λ β hβ hβ0 hR 0) (productSquareZero f hf hsq Λ hR) where
  hom := TrivSqZeroExt.inlHom (R 0) (kernelProduct f hf hsq)
  aug_fac := rfl
  base_fac := RingHom.ext fun l =>
    congrArg (TrivSqZeroExt.inlHom (R 0) _) (show β 0 l = Λ.aug l by rw [hβ0])

/-- The inclusion `A → A[Mₙ]`. -/
public def inlLevelMap (n : ℕ) :
    BasedSiteRing.RingMap (level f Λ β hβ hβ0 hR 0) (levelSquareZero f hf hsq Λ hR n) where
  hom := TrivSqZeroExt.inlHom (R 0) (kerObj (toBase f n) (toBase_surjective f hf n) (hsq n))
  aug_fac := rfl
  base_fac := RingHom.ext fun l =>
    congrArg (TrivSqZeroExt.inlHom (R 0) _) (show β 0 l = Λ.aug l by rw [hβ0])

/-- The fibre product `Rₙ ×_A Rₙ`. -/
public abbrev levelPair (n : ℕ) : BasedSiteRing (R 0) B S hS toS hA Λ :=
  BasedSiteRing.prod (level f Λ β hβ hβ0 hR n) (level f Λ β hβ hβ0 hR n)

/-- The diagonal `Rₙ → Rₙ ×_A Rₙ`. -/
public abbrev diagMap (n : ℕ) :
    BasedSiteRing.RingMap (level f Λ β hβ hβ0 hR n) (levelPair f Λ β hβ hβ0 hR n) :=
  BasedSiteRing.lift (BasedSiteRing.RingMap.id Λ _) (BasedSiteRing.RingMap.id Λ _)

/-- The map `R̃ → Rₙ ×_A Rₙ`, `r ↦ (fₙ(rₙ₊₁), rₙ)`. -/
public abbrev stepMap (n : ℕ) :
    BasedSiteRing.RingMap (sameBaseRing f Λ β hβ hβ0 hR) (levelPair f Λ β hβ hβ0 hR n) :=
  BasedSiteRing.lift ((transition f Λ β hβ hβ0 hR n).comp (projMap f Λ β hβ hβ0 hR (n + 1)))
    (projMap f Λ β hβ hβ0 hR n)

/-- The difference map `Rₙ ×_A Rₙ → A[Mₙ]`, `(s, t) ↦ (s̄, s − t)`. -/
public def levelDiffMap (n : ℕ) :
    BasedSiteRing.RingMap (levelPair f Λ β hβ hβ0 hR n) (levelSquareZero f hf hsq Λ hR n) where
  hom := diffHom (toBase f n) (toBase_surjective f hf n) (hsq n)
  aug_fac := rfl
  base_fac := by
    refine RingHom.ext fun l => Prod.ext ?_ (kerVal_injective _ _ _ (sub_self (β n l)))
    change toBase f n (β n l) = Λ.aug l
    rw [← RingHom.comp_apply, toBase_comp_eq f Λ β hβ hβ0 n]

/-- The fibre product `R̃ ×_A A[∏ Mₙ]`. -/
public abbrev sameBaseTwisted : BasedSiteRing (R 0) B S hS toS hA Λ :=
  BasedSiteRing.prod (sameBaseRing f Λ β hβ hβ0 hR) (productSquareZero f hf hsq Λ hR)

/-- The `n`-th component of an element of `∏ Mₙ`. -/
public def component (m : kernelProduct f hf hsq) (n : ℕ) : RingHom.ker (toBase f n) :=
  m n

/-- The inclusion `∏ Mₙ → R̃`. -/
@[implicit_reducible]
public def productIncl : kernelProduct f hf hsq →+ sameBase f where
  toFun m := ⟨fun n => (component f hf hsq m n : R n), fun n =>
    ((component f hf hsq m n).2).trans (component f hf hsq m 0).2.symm⟩
  map_zero' := rfl
  map_add' _ _ := rfl

public theorem proj_productIncl (m : kernelProduct f hf hsq) (n : ℕ) :
    proj f n (productIncl f hf hsq m) = component f hf hsq m n := rfl

public theorem base_productIncl (m : kernelProduct f hf hsq) :
    base f (productIncl f hf hsq m) = 0 :=
  (component f hf hsq m 0).2

public theorem productIncl_smul (d : sameBase f) (m : kernelProduct f hf hsq) :
    productIncl f hf hsq (base f d • m) = d * productIncl f hf hsq m := by
  let := kernelModule f hf hsq
  refine Subtype.ext (funext fun n => ?_)
  show (component f hf hsq (base f d • m) n : R n) = proj f n d * component f hf hsq m n
  have h := Stacks.Smooth.kerModule_smul (toBase_surjective f hf n) (hsq n)
    (proj f n d) (component f hf hsq m n)
  rw [proj_apply, d.2 n] at h
  exact congrArg Subtype.val h

public theorem productIncl_mul (m m' : kernelProduct f hf hsq) :
    productIncl f hf hsq m * productIncl f hf hsq m' = 0 := by
  refine Subtype.ext (funext fun n => ?_)
  exact mul_eq_zero_of_sq (hsq n) (component f hf hsq m n).2 (component f hf hsq m' n).2

/-- The twisting map `R̃ ×_A A[∏ Mₙ] → R̃`, `(r, (a, m)) ↦ r + m`. -/
public def sameBaseTwist :
    BasedSiteRing.RingMap (sameBaseTwisted f hf hsq Λ β hβ hβ0 hR)
      (sameBaseRing f Λ β hβ hβ0 hR) where
  hom := twistHom (base f) (productIncl f hf hsq) (productIncl_smul f hf hsq)
    (productIncl_mul f hf hsq)
  aug_fac := RingHom.ext fun z =>
    map_twistHom (base f) (productIncl f hf hsq) (base_productIncl f hf hsq)
      (productIncl_smul f hf hsq) (productIncl_mul f hf hsq) z
  base_fac := RingHom.ext fun _ => twistHom_eq_of_snd_eq_zero _ _
    (productIncl_smul f hf hsq) (productIncl_mul f hf hsq) _ rfl

/-- The fibre product `Rₙ ×_A A[Mₙ]`. -/
public abbrev levelTwisted (n : ℕ) : BasedSiteRing (R 0) B S hS toS hA Λ :=
  BasedSiteRing.prod (level f Λ β hβ hβ0 hR n) (levelSquareZero f hf hsq Λ hR n)

/-- The inclusion of `Mₙ` into `Rₙ`. -/
@[implicit_reducible]
public def levelIncl (n : ℕ) :
    kerObj (toBase f n) (toBase_surjective f hf n) (hsq n) →+ R n where
  toFun := kerVal _ _ _
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The twisting map `Rₙ ×_A A[Mₙ] → Rₙ`, `(s, (a, m)) ↦ s + m`. -/
public def levelTwist (n : ℕ) :
    BasedSiteRing.RingMap (levelTwisted f hf hsq Λ β hβ hβ0 hR n) (level f Λ β hβ hβ0 hR n) where
  hom := twistHom (toBase f n) (levelIncl f hf hsq n)
    (kerVal_smul (toBase f n) (toBase_surjective f hf n) (hsq n))
    (fun m m' => mul_eq_zero_of_sq (hsq n) (map_kerVal _ _ _ m) (map_kerVal _ _ _ m'))
  aug_fac := RingHom.ext fun z =>
    map_twistHom (toBase f n) (levelIncl f hf hsq n) (map_kerVal _ _ _)
      (kerVal_smul (toBase f n) (toBase_surjective f hf n) (hsq n))
      (fun m m' => mul_eq_zero_of_sq (hsq n) (map_kerVal _ _ _ m) (map_kerVal _ _ _ m')) z
  base_fac := RingHom.ext fun _ => twistHom_eq_of_snd_eq_zero _ _
    (kerVal_smul (toBase f n) (toBase_surjective f hf n) (hsq n))
    (fun m m' => mul_eq_zero_of_sq (hsq n) (map_kerVal _ _ _ m) (map_kerVal _ _ _ m')) _ rfl

/-- The map `Rₙ ×_A Rₙ → Rₙ ×_A A[Mₙ]`, `(s, t) ↦ (s, (s̄, t − s))`. -/
public def levelUntwist (n : ℕ) :
    BasedSiteRing.RingMap (levelPair f Λ β hβ hβ0 hR n)
      (levelTwisted f hf hsq Λ β hβ hβ0 hR n) where
  hom := untwistHom (toBase f n) (toBase_surjective f hf n) (hsq n)
  aug_fac := rfl
  base_fac := by
    refine RingHom.ext fun l => Subtype.ext (Prod.ext rfl (Prod.ext ?_
      (kerVal_injective _ _ _ (sub_self (β n l)))))
    change toBase f n (β n l) = Λ.aug l
    rw [← RingHom.comp_apply, toBase_comp_eq f Λ β hβ hβ0 n]

/-- The componentwise map `R̃ ×_A A[∏ Mₙ] → Rₙ ×_A A[Mₙ]`. -/
public abbrev twistedProj (n : ℕ) :
    BasedSiteRing.RingMap (sameBaseTwisted f hf hsq Λ β hβ hβ0 hR)
      (levelTwisted f hf hsq Λ β hβ hβ0 hR n) :=
  BasedSiteRing.lift ((projMap f Λ β hβ hβ0 hR n).comp (BasedSiteRing.fst _ _))
    ((squareZeroProj f hf hsq Λ hR n).comp (BasedSiteRing.snd _ _))

end Rings

end Deformation.Artin.SquareZeroTower
