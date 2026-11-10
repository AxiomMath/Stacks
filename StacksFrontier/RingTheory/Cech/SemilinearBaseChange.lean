module

public import StacksFrontier.RingTheory.Cech.Reindex
public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.Augmentation

/-!
# Change of rings on the extended alternating Čech complex, semilinearly

Let `φ : A → B` be a map of commutative rings, let `f₁, …, f_r` be elements of `A` and let
`g₁, …, g_r` be elements of `B` with `φ (f i) = g i`. This file constructs the comparison

`C^p(f₁, …, f_r; A) ⟶ C^p(g₁, …, g_r; B)`

as a **`φ`-semilinear** map, and proves that it is the identity for `φ = id`, that it composes,
that it commutes with the Čech differentials and with restriction to a subfamily, and that it
carries the degree-zero identification with `A` to `φ`.

`Stacks.CechRingBaseChange.termMap` of `RingBaseChange.lean` is the same comparison stated
`A`-linearly into the target restricted along `φ`, which is what [Stacks, Tag 099D] item (3)
asks for. The semilinear spelling here differs from it in two ways, both of which are what a
*presheaf* of Čech complexes needs. First, the target family is an argument, together with the
hypothesis `φ (f i) = g i`, rather than being `fun i => φ (f i)`: on a presheaf of rings the
family at an object is not literally the image of the family at a larger object, only equal to
it, and carrying the equality as a hypothesis avoids transporting along it. Second, the
identity-and-composition laws are then exactly the functoriality laws of a presheaf, which is
what `PresheafOfModules.ofPresheaf` consumes.

## Main definitions

* `Stacks.CechSemilinear.locMap`: the semilinear comparison `A_S ⟶ B_T` of two localizations
  along `φ`, for `S` mapped into `T`.
* `Stacks.CechSemilinear.termMap`: the semilinear comparison of the degree-`p` Čech terms.

## Main results

* `Stacks.CechSemilinear.termMap_id`, `Stacks.CechSemilinear.termMap_comp`,
  `Stacks.CechSemilinear.termMap_congr`: **the functoriality laws** — the comparison for the
  identity is the identity, the comparison for a composite is the composite, and the comparison
  depends on `φ` only through its value.
* `Stacks.CechSemilinear.termMap_cechD`: **the comparison commutes with the Čech
  differentials.**
* `Stacks.CechSemilinear.termMap_cechTermRestrict`: **the comparison commutes with restriction
  to a subfamily** — the degreewise map `Cech.cechTermRestrict` of `Reindex.lean`.
* `Stacks.CechSemilinear.cechTermZeroEquiv_termMap`: **in degree zero the comparison is `φ`**,
  under the identification `Stacks.LocalCohomology.cechTermZeroEquiv` of the degree-zero term
  with the ring.

## Implementation notes

The comparison on a single localization is `IsLocalization.map`, whose `map_id` and `map_map`
give the two functoriality laws at once; `Localization S` and `LocalizedModule S A` are the same
type, so no bridge is needed between the localization of the ring and the Čech modules, which
are localizations of `A` as an `A`-module.

Both `Cech.cechTerm` and the comparison are direct sums over the index sets of a fixed
cardinality, and the comparison is `DirectSum.map`, so every statement here is proved by
`DirectSum.ext`-style component comparison and reduces to the corresponding statement about one
localization. The two statements about one localization that are not formal — compatibility with
the transition maps `Cech.cechι` and with the reindexing `Cech.reindexLoc` — are proved by the
uniqueness of a semilinear map out of a localization, `Stacks.CechSemilinear.locHom_ext`, whose
hypothesis is that the image of the localizing submonoid acts invertibly on the target.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [Stacks Project, Tag 0G6I](https://stacks.math.columbia.edu/tag/0G6I)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w

namespace Stacks.CechSemilinear

section Loc

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- **The semilinear comparison of two localizations along a ring map.** For `φ : A → B` and a
submonoid `S` of `A` carried by `φ` into a submonoid `T` of `B`, the induced map
`A_S → B_T`, `a / s ↦ φ a / φ s`, read as a `φ`-semilinear map of the localizations of `A` and
`B` as modules over themselves. -/
def locMap (φ : A →+* B) (S : Submonoid A) (T : Submonoid B) (h : S ≤ T.comap φ) :
    LocalizedModule S A →ₛₗ[φ] LocalizedModule T B where
  toFun := IsLocalization.map (Localization T) φ h
  map_add' := map_add _
  map_smul' := fun a x => IsLocalization.map_smul h x a

/-- The comparison sends the fraction `a / s` to `φ a / φ s`. -/
theorem locMap_mk (φ : A →+* B) (S : Submonoid A) (T : Submonoid B) (h : S ≤ T.comap φ) (a : A)
    (s : S) :
    locMap φ S T h (LocalizedModule.mk a s) =
      LocalizedModule.mk (φ a) ⟨φ s, h s.property⟩ := by
  change IsLocalization.map (Localization T) φ h (Localization.mk a s) =
    Localization.mk (φ a) ⟨φ s, h s.property⟩
  simpa only [Localization.mk_eq_mk'] using
    IsLocalization.map_mk' (S := Localization S) (Q := Localization T) h a s

/-- On a fraction with denominator one the comparison is `φ` on the numerator. -/
theorem locMap_mkLinearMap (φ : A →+* B) (S : Submonoid A) (T : Submonoid B)
    (h : S ≤ T.comap φ) (a : A) :
    locMap φ S T h (LocalizedModule.mkLinearMap S A a) =
      LocalizedModule.mkLinearMap T B (φ a) := by
  rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.mkLinearMap_apply, locMap_mk]
  congr 1
  exact Subtype.ext (by simp)

/-- The comparison of a localization with itself along the identity ring map is the identity. -/
theorem locMap_id (S : Submonoid A) (h : S ≤ S.comap (RingHom.id A))
    (x : LocalizedModule S A) : locMap (RingHom.id A) S S h x = x :=
  IsLocalization.map_id x h

/-- The comparison along `ψ` after the comparison along `φ` is the comparison along `ψ ∘ φ`. -/
theorem locMap_comp {D : Type w} [CommRing D] (φ : A →+* B) (ψ : B →+* D) (S : Submonoid A)
    (T : Submonoid B) (P : Submonoid D) (hφ : S ≤ T.comap φ) (hψ : T ≤ P.comap ψ)
    (h : S ≤ P.comap (ψ.comp φ)) (x : LocalizedModule S A) :
    locMap ψ T P hψ (locMap φ S T hφ x) = locMap (ψ.comp φ) S P h x :=
  IsLocalization.map_map hφ hψ x

/-- **A semilinear map out of a localization is determined by its restriction to the fractions
with denominator one**, provided the images of the localizing submonoid act injectively on the
target. -/
theorem locHom_ext (φ : A →+* B) (S : Submonoid A) {M : Type*} [AddCommGroup M] [Module A M]
    {N : Type*} [AddCommGroup N] [Module B N] (l k : LocalizedModule S M →ₛₗ[φ] N)
    (hi : ∀ s : S, Function.Injective (fun x : N => φ s • x))
    (h : ∀ m, l (LocalizedModule.mk m 1) = k (LocalizedModule.mk m 1)) : l = k := by
  ext x
  induction x using LocalizedModule.induction_on with
  | _ m s =>
    apply hi s
    dsimp only
    rw [← l.map_smulₛₗ, ← k.map_smulₛₗ, LocalizedModule.smul'_mk]
    change l (LocalizedModule.mk (s • m) s) = k (LocalizedModule.mk (s • m) s)
    rw [LocalizedModule.mk_cancel]
    exact h m

end Loc

section Term

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] {r : ℕ}

/-- The localizing submonoid of an index set is carried by `φ` into the one of the image
family. -/
theorem cechSub_le_comap (φ : A →+* B) (f : Fin r → A) (g : Fin r → B) (h : ∀ i, φ (f i) = g i)
    (s : Finset (Fin r)) : Cech.cechSub f s ≤ (Cech.cechSub g s).comap φ := by
  rintro x ⟨n, rfl⟩
  exact ⟨n, by simp only [map_pow, map_prod, h]⟩

/-- **Change of rings on the degree-`p` term** of the extended alternating Čech complex, as a
`φ`-semilinear map: on the summand indexed by `s` it is the comparison `A_{f_s} → B_{g_s}` of
localizations. -/
def termMap (φ : A →+* B) (f : Fin r → A) (g : Fin r → B) (h : ∀ i, φ (f i) = g i) (p : ℕ) :
    Cech.cechTerm f A p →ₛₗ[φ] Cech.cechTerm g B p where
  __ := DirectSum.map fun (s : {s : Finset (Fin r) // s.card = p}) =>
    (locMap φ _ _ (cechSub_le_comap φ f g h s.1)).toAddMonoidHom
  map_smul' a x := by
    ext s
    exact (locMap φ _ _ (cechSub_le_comap φ f g h s.1)).map_smulₛₗ a (x s)

/-- The component of the comparison at the index set `s` is the comparison of the localizations
`A_{f_s} → B_{g_s}` applied to the component at `s`. -/
@[simp]
theorem termMap_apply (φ : A →+* B) (f : Fin r → A) (g : Fin r → B) (h : ∀ i, φ (f i) = g i)
    (p : ℕ) (x : Cech.cechTerm f A p) (s : {s : Finset (Fin r) // s.card = p}) :
    termMap φ f g h p x s = locMap φ _ _ (cechSub_le_comap φ f g h s.1) (x s) :=
  rfl

/-- The comparison sends the summand indexed by `s` into the summand indexed by `s`, by the
comparison of the localizations at `s`. -/
theorem termMap_lof (φ : A →+* B) (f : Fin r → A) (g : Fin r → B) (h : ∀ i, φ (f i) = g i)
    (p : ℕ) (s : {s : Finset (Fin r) // s.card = p}) (x : Cech.cechMod f A s.1) :
    termMap φ f g h p (DirectSum.lof A _ _ s x) =
      DirectSum.lof B _ _ s (locMap φ _ _ (cechSub_le_comap φ f g h s.1) x) :=
  DirectSum.map_of _ _ _

/-- **The comparison depends on `φ` only through its value.** -/
theorem termMap_congr {φ ψ : A →+* B} (e : φ = ψ) (f : Fin r → A) (g : Fin r → B)
    (hφ : ∀ i, φ (f i) = g i) (hψ : ∀ i, ψ (f i) = g i) (p : ℕ) (x : Cech.cechTerm f A p) :
    termMap φ f g hφ p x = termMap ψ f g hψ p x := by
  subst ψ
  rfl

/-- **The comparison for the identity ring map is the identity.** -/
theorem termMap_id (f : Fin r → A) (h : ∀ i, (RingHom.id A) (f i) = f i) (p : ℕ)
    (x : Cech.cechTerm f A p) : termMap (RingHom.id A) f f h p x = x := by
  ext s
  exact locMap_id _ (cechSub_le_comap (RingHom.id A) f f h s.1) (x s)

/-- **The comparisons compose.** -/
theorem termMap_comp {D : Type w} [CommRing D] (φ : A →+* B) (ψ : B →+* D) (f : Fin r → A)
    (g : Fin r → B) (k : Fin r → D) (hφ : ∀ i, φ (f i) = g i) (hψ : ∀ i, ψ (g i) = k i)
    (h : ∀ i, (ψ.comp φ) (f i) = k i) (p : ℕ) (x : Cech.cechTerm f A p) :
    termMap ψ g k hψ p (termMap φ f g hφ p x) = termMap (ψ.comp φ) f k h p x := by
  ext s
  exact locMap_comp φ ψ _ _ _ (cechSub_le_comap φ f g hφ s.1)
    (cechSub_le_comap ψ g k hψ s.1) (cechSub_le_comap (ψ.comp φ) f k h s.1) (x s)

/-- **The comparison commutes with the transition maps of the Čech complex.** Both sides are
semilinear maps out of `A_{f_s}`, the images of `f_s` act invertibly on `B_{g_t}` for `s ⊆ t`,
and on a fraction with denominator one both sides keep the numerator. -/
theorem locMap_cechι (φ : A →+* B) (f : Fin r → A) (g : Fin r → B) (h : ∀ i, φ (f i) = g i)
    {s t : Finset (Fin r)} (hst : s ⊆ t) (x : Cech.cechMod f A s) :
    locMap φ _ _ (cechSub_le_comap φ f g h t) (Cech.cechι f A hst x) =
      Cech.cechι g B hst (locMap φ _ _ (cechSub_le_comap φ f g h s) x) := by
  have he : (locMap φ _ _ (cechSub_le_comap φ f g h t)).comp (Cech.cechι f A hst) =
      (Cech.cechι g B hst).comp (locMap φ _ _ (cechSub_le_comap φ f g h s)) := by
    refine locHom_ext φ (Cech.cechSub f s) _ _ (fun d => ?_) (fun a => ?_)
    · exact ((Module.End.isUnit_iff _).mp (Cech.isUnit_algebraMap g B hst
        (LocalizedModule.mkLinearMap (Cech.cechSub g t) B)
        ⟨φ d, cechSub_le_comap φ f g h s d.property⟩)).injective
    · change locMap φ _ _ (cechSub_le_comap φ f g h t)
          (Cech.cechι f A hst (LocalizedModule.mk a 1)) =
        Cech.cechι g B hst (locMap φ _ _ (cechSub_le_comap φ f g h s) (LocalizedModule.mk a 1))
      rw [← LocalizedModule.mkLinearMap_apply, Cech.cechι_mk]
      simp only [LocalizedModule.mkLinearMap_apply, locMap_mk, Submonoid.coe_one, map_one]
      exact (Cech.cechι_mk g B hst (φ a)).symm
  exact LinearMap.congr_fun he x

/-- **Change of rings commutes with the Čech differentials.** -/
theorem termMap_cechD (φ : A →+* B) (f : Fin r → A) (g : Fin r → B) (h : ∀ i, φ (f i) = g i)
    (p : ℕ) (x : Cech.cechTerm f A p) :
    termMap φ f g h (p + 1) (Cech.cechD f A p x) =
      Cech.cechD g B p (termMap φ f g h p x) := by
  have he : (termMap φ f g h (p + 1)).comp (Cech.cechD f A p) =
      (Cech.cechD g B p).comp (termMap φ f g h p) := by
    refine DFunLike.ext _ _ fun y => ?_
    induction y using DirectSum.induction_on with
    | zero => simp
    | of s y =>
      change termMap φ f g h (p + 1) (Cech.cechD f A p (DirectSum.lof A _ _ s y)) =
        Cech.cechD g B p (termMap φ f g h p (DirectSum.lof A _ _ s y))
      simp only [Cech.cechD_lof, termMap_lof, map_sum, map_zsmul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [termMap_lof, locMap_cechι φ f g h]
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  exact LinearMap.congr_fun he x

end Term

section Zero

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] {r : ℕ}

/-- **In degree zero the comparison is `φ`.** The only index set of cardinality zero is the
empty one, on whose summand the degree-zero identification is the identification of the
localization at the empty product with the ring itself. -/
theorem cechTermZeroEquiv_termMap (φ : A →+* B) (f : Fin r → A) (g : Fin r → B)
    (h : ∀ i, φ (f i) = g i) (x : Cech.cechTerm f A 0) :
    Stacks.LocalCohomology.cechTermZeroEquiv g (ModuleCat.of B B) (termMap φ f g h 0 x) =
      φ (Stacks.LocalCohomology.cechTermZeroEquiv f (ModuleCat.of A A) x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | of s x =>
    obtain rfl : s = default := Subsingleton.elim _ _
    induction x using LocalizedModule.induction_on with
    | _ a d =>
      have hd : d = 1 := by
        refine Subtype.ext ?_
        obtain ⟨n, hn⟩ := d.property
        simpa only [Finset.card_eq_zero.mp (default : ExtendedAlternatingCech.Idx r 0).2,
          Finset.prod_empty, one_pow, Submonoid.coe_one] using hn.symm
      subst d
      change Stacks.LocalCohomology.cechTermZeroEquiv g (ModuleCat.of B B)
          (termMap φ f g h 0 (DirectSum.lof A (ExtendedAlternatingCech.Idx r 0)
            (fun s => Cech.cechMod f A s.1) default
            (LocalizedModule.mkLinearMap (Cech.cechSub f _) A a))) =
        φ (Stacks.LocalCohomology.cechTermZeroEquiv f (ModuleCat.of A A)
          (DirectSum.lof A (ExtendedAlternatingCech.Idx r 0)
            (fun s => Cech.cechMod f A s.1) default
            (LocalizedModule.mkLinearMap (Cech.cechSub f _) A a)))
      rw [termMap_lof, locMap_mkLinearMap, Stacks.LocalCohomology.cechTermZeroEquiv_lof,
        Stacks.LocalCohomology.cechTermZeroEquiv_lof]
      exact (Stacks.CechBaseChange.cechModEmptyEquiv_mk g B (φ a)).trans
        (congrArg φ (Stacks.CechBaseChange.cechModEmptyEquiv_mk f A a)).symm

end Zero

section Restrict

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] {r s : ℕ} (φ : A →+* B)
  (f : Fin r → A) (g : Fin s → A) (f' : Fin r → B) (g' : Fin s → B) (e : Fin r ↪o Fin s)
  (hf : ∀ i, φ (f i) = f' i) (hg : ∀ j, φ (g j) = g' j) (he : ∀ i, g (e i) = f i)
  (he' : ∀ i, g' (e i) = f' i)

/-- **Change of rings commutes with the reindexing of a localization along a subfamily.** Both
maps keep the numerator and apply `φ` to it, and read the denominator through the equality of
localizing submonoids `Cech.cechSub_reindex`, so on a fraction the two composites are the same
fraction. -/
theorem locMap_reindexLoc (S : Finset (Fin r))
    (x : Cech.cechMod g A (S.map e.toEmbedding)) :
    locMap φ _ _ (cechSub_le_comap φ f f' hf S) (Cech.reindexLoc f A g e he S x) =
      Cech.reindexLoc f' B g' e he' S
        (locMap φ _ _ (cechSub_le_comap φ g g' hg (S.map e.toEmbedding)) x) := by
  induction x using LocalizedModule.induction_on with
  | _ m t => simp only [Cech.reindexLoc_mk, locMap_mk]

/-- **Change of rings commutes with restriction to a subfamily.** -/
theorem termMap_cechTermRestrict (p : ℕ) (x : Cech.cechTerm g A p) :
    termMap φ f f' hf p (Cech.cechTermRestrict f A g e he p x) =
      Cech.cechTermRestrict f' B g' e he' p (termMap φ g g' hg p x) := by
  refine DirectSum.ext_component B fun S => ?_
  change locMap φ _ _ (cechSub_le_comap φ f f' hf S.1)
      (Cech.reindexLoc f A g e he S.1 (x (Cech.reindexIdx e S))) =
    Cech.reindexLoc f' B g' e he' S.1
      (locMap φ _ _ (cechSub_le_comap φ g g' hg (S.1.map e.toEmbedding))
        (x (Cech.reindexIdx e S)))
  exact locMap_reindexLoc φ f g f' g' e hf hg he he' S.1 (x (Cech.reindexIdx e S))

end Restrict

end Stacks.CechSemilinear

end
