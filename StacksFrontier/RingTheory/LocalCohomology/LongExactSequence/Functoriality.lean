module

public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.CechExact
public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.CechFunctor
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.DirectSums

/-!
# Exactness of the extended alternating Čech complex in its coefficient module

Let `A` be a commutative ring, let `f₁, …, f_r ∈ A` and let `M` be an `A`-module. The extended
alternating Čech complex `C^•(f₁, …, f_r; M)` is a functor of `M`
(`Stacks.LocalCohomology.cechFunctor`), and this file proves the one property of that functor
which the long exact sequence of local cohomology needs: it is *exact*. A short exact sequence of
`A`-modules `0 → N → F → M → 0` gives a short exact sequence of Čech complexes

`0 → C^•(f₁, …, f_r; N) → C^•(f₁, …, f_r; F) → C^•(f₁, …, f_r; M) → 0`.

Exactness is checked degreewise, where it reduces to two facts about modules: localization is an
exact functor (`IsLocalizedModule.map_exact`), and a direct sum of exact sequences is exact — the
latter because an element of a direct sum killed by the maps has finitely many nonzero components,
each of which has a preimage, and the chosen preimages supported on that finite set assemble to a
preimage.

The file also records the functoriality of a Čech *term* for a plain linear map of modules in
arbitrary universes. This is a strictly weaker statement than the functor
`Stacks.LocalCohomology.cechFunctor`, which is defined on `ModuleCat.{max u v} A` and therefore
cannot compare the Čech complexes of modules in two different universes; the universe-free form is
what `LongExactSequence/CrossUniverse.lean` needs.

## Main results

* `Stacks.LocalCohomology.LongExactSequence.exact_lmap` — a direct sum of exact sequences of
  modules is exact.
* `Stacks.LocalCohomology.LongExactSequence.cechTermLinearMap_id`,
  `Stacks.LocalCohomology.LongExactSequence.cechTermLinearMap_comp` and
  `Stacks.LocalCohomology.LongExactSequence.cechTermLinearMap_cechComplex_d` — functoriality of a
  Čech term for modules in arbitrary universes.
* `Stacks.LocalCohomology.LongExactSequence.shortExact_map_cechTerm` — degreewise short exactness
  of the Čech complexes of a short exact sequence of modules.
* `Stacks.LocalCohomology.LongExactSequence.shortExact_map_extendedCechFunctor` — **short
  exactness of the sequence of extended Čech complexes**, the input to the long exact sequence;
  an alias of `Stacks.LocalCohomology.shortExact_map_extendedCechFunctor`.

## Implementation notes

Two spellings of the map of Čech terms induced by a map of modules are already in the library:
`Stacks.LocalCohomology.cechTermMap`, built with `DirectSum.toModule` and taking a morphism of
`ModuleCat`, and `Stacks.LocalCohomology.cechTermLinearMap`, built with `DirectSum.lmap` and
taking a plain linear map between modules in arbitrary universes. They agree —
`Stacks.LocalCohomology.LongExactSequence.cechTermMap_eq_cechTermLinearMap` — and both are used
here: the first is what `cechFunctor` is defined from, the second is what survives a change of
universe.

## References

* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
* [Stacks Project, Tag 0DX7](https://stacks.math.columbia.edu/tag/0DX7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w' w v u

namespace Stacks.LocalCohomology.LongExactSequence

/-! ### Direct sums of exact sequences -/

section DirectSums

variable {R : Type u} [CommRing R] {ι : Type*} {M N P : ι → Type*}
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
  [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]

/-- **A direct sum of exact sequences of modules is exact.** An element of `⨁ᵢ Nᵢ` killed by the
second map has finitely many nonzero components, each of which is hit by the first map; the chosen
preimages, taken on that finite support and zero elsewhere, assemble to a preimage in `⨁ᵢ Mᵢ`. -/
theorem exact_lmap (g : ∀ i, M i →ₗ[R] N i) (h : ∀ i, N i →ₗ[R] P i)
    (hgh : ∀ i, Function.Exact (g i) (h i)) :
    Function.Exact (DirectSum.lmap g) (DirectSum.lmap h) := by
  classical
  intro y
  constructor
  · intro hy
    have hcomp : ∀ i, h i (y i) = 0 := fun i => by
      simpa only [DirectSum.lmap_apply, DFinsupp.coe_zero, Pi.zero_apply] using
        congrArg (fun z : DirectSum ι P => z i) hy
    choose w hw using fun i => (hgh i (y i)).1 (hcomp i)
    refine ⟨DFinsupp.mk (DFinsupp.support y) fun i => w i.1, DFinsupp.ext fun i => ?_⟩
    rw [DirectSum.lmap_apply, DFinsupp.mk_apply]
    by_cases hi : i ∈ DFinsupp.support y
    · rw [dite_eq_left hi]
      exact hw i
    · rw [dite_eq_right hi, map_zero, DFinsupp.notMem_support_iff.1 hi]
  · rintro ⟨x, rfl⟩
    exact DFinsupp.ext fun i => by
      simpa only [DirectSum.lmap_apply, DFinsupp.coe_zero, Pi.zero_apply] using
        (hgh i).apply_apply_eq_zero (x i)

end DirectSums

/-! ### Functoriality of a localization in the module -/

section Localization

variable {R : Type u} [CommRing R] (S : Submonoid R)

/-- The localization of an identity map is the identity. -/
theorem localizedModuleMap_id {N : Type*} [AddCommGroup N] [Module R N] :
    localizedModuleMap S (LinearMap.id (R := R) (M := N)) = LinearMap.id :=
  IsLocalizedModule.map_id S (LocalizedModule.mkLinearMap S N)

/-- The localization of a composite is the composite of the localizations. -/
theorem localizedModuleMap_comp {N P Q : Type*} [AddCommGroup N] [Module R N] [AddCommGroup P]
    [Module R P] [AddCommGroup Q] [Module R Q] (g : N →ₗ[R] P) (h : P →ₗ[R] Q) :
    localizedModuleMap S (h ∘ₗ g) = localizedModuleMap S h ∘ₗ localizedModuleMap S g :=
  IsLocalizedModule.map_comp' S (LocalizedModule.mkLinearMap S N)
    (LocalizedModule.mkLinearMap S P) (LocalizedModule.mkLinearMap S Q) g h

end Localization

/-! ### Functoriality of the Čech terms -/

section Terms

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)

/-- The map of Čech terms induced by an identity map is the identity. -/
theorem cechTermLinearMap_id {N : Type*} [AddCommGroup N] [Module R N] (p : ℕ) :
    cechTermLinearMap f (LinearMap.id (R := R) (M := N)) p = LinearMap.id := by
  simp only [cechTermLinearMap, localizedModuleMap_id, DirectSum.lmap_id]

/-- The map of Čech terms induced by a composite is the composite of the induced maps. The three
modules may live in three different universes, which is what makes this usable for a comparison
across universes. -/
theorem cechTermLinearMap_comp {N P Q : Type*} [AddCommGroup N] [Module R N] [AddCommGroup P]
    [Module R P] [AddCommGroup Q] [Module R Q] (g : N →ₗ[R] P) (h : P →ₗ[R] Q) (p : ℕ) :
    cechTermLinearMap f (h ∘ₗ g) p = cechTermLinearMap f h p ∘ₗ cechTermLinearMap f g p := by
  simp only [cechTermLinearMap, localizedModuleMap_comp, DirectSum.lmap_comp]

/-- The two spellings of the induced map on a Čech term agree: the one built with
`DirectSum.toModule` from a morphism of `ModuleCat` and the one built with `DirectSum.lmap` from a
linear map. -/
theorem cechTermMap_eq_cechTermLinearMap {M N : ModuleCat.{max u v} R} (g : M ⟶ N) (p : ℕ) :
    cechTermMap f g p = cechTermLinearMap f g.hom p := by
  refine DirectSum.linearMap_ext R fun s => LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, cechTermMap_lof, LinearMap.comp_apply, cechTermLinearMap,
    DirectSum.lmap_lof]
  rfl

/-- The zero map induces the zero map on the terms of the Čech complex. -/
@[simp] theorem cechTermMap_zero {M N : ModuleCat.{max u v} R} (p : ℕ) :
    cechTermMap f (0 : M ⟶ N) p = 0 := by
  rw [cechTermMap_eq_cechTermLinearMap, ModuleCat.hom_zero]
  refine LinearMap.ext fun x => DFinsupp.ext fun s => ?_
  show localizedModuleMap (Cech.cechSub f s.1)
    (0 : (M : Type (max u v)) →ₗ[R] (N : Type (max u v))) (x s) = 0
  rw [localizedModuleMap, map_zero]
  rfl

/-- The differential of the Čech complex, as a linear map between the Čech terms. -/
theorem cechComplex_d_hom {N : Type*} [AddCommGroup N] [Module R N] (i : ℕ) :
    ((Cech.cechComplex f N).d i (i + 1)).hom = Cech.cechD f N i := by
  simp only [Cech.cechComplex, CochainComplex.of_d, ModuleCat.hom_ofHom]
  rfl

/-- Outside the shape of `ComplexShape.up ℕ` the differential of the Čech complex vanishes. -/
theorem cechComplex_d_hom_eq_zero {N : Type*} [AddCommGroup N] [Module R N] (i j : ℕ)
    (hij : ¬ (ComplexShape.up ℕ).Rel i j) :
    ((Cech.cechComplex f N).d i j).hom = 0 := by
  rw [HomologicalComplex.shape _ _ _ hij, ModuleCat.hom_zero]

/-- The maps of Čech terms induced by a linear map commute with every differential of the Čech
complex, including the zero ones outside the shape. -/
theorem cechTermLinearMap_cechComplex_d {N P : Type*} [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (g : N →ₗ[R] P) (i j : ℕ)
    (x : (Cech.cechComplex f N).X i) :
    cechTermLinearMap f g j (((Cech.cechComplex f N).d i j).hom x) =
      ((Cech.cechComplex f P).d i j).hom (cechTermLinearMap f g i x) := by
  by_cases hij : (ComplexShape.up ℕ).Rel i j
  · obtain rfl : i + 1 = j := hij
    rw [cechComplex_d_hom, cechComplex_d_hom]
    exact cechTermLinearMap_cechD f g i x
  · rw [cechComplex_d_hom_eq_zero f i j hij, cechComplex_d_hom_eq_zero f i j hij]
    exact map_zero _

end Terms

/-! ### The Čech functors preserve zero morphisms -/

section Zero

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)

/-- The Čech complex functor sends zero morphisms of modules to zero morphisms of complexes. -/
instance : (cechFunctor.{v} f).PreservesZeroMorphisms where
  map_zero M N := HomologicalComplex.hom_ext _ _ fun p => by
    rw [cechFunctor_map, cechComplexMap_f, cechTermMap_zero, HomologicalComplex.zero_f,
      ModuleCat.ofHom_zero]
    rfl

/-- The extended Čech complex functor sends zero morphisms of modules to zero morphisms of
complexes. -/
instance : (extendedCechFunctor.{v} f).PreservesZeroMorphisms :=
  inferInstanceAs ((cechFunctor.{v} f ⋙
    ComplexShape.embeddingUpNat.extendFunctor
      (ModuleCat.{max u v} R)).PreservesZeroMorphisms)

end Zero

/-! ### Short exactness -/

section ShortExact

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
  (S : ShortComplex (ModuleCat.{max u v} R))

/-- Degreewise short exactness: localization is exact and direct sums of exact sequences are
exact, so a short exact sequence of modules induces a short exact sequence of degree-`p` Čech
terms. -/
theorem shortExact_map_cechTerm (hS : S.ShortExact) (p : ℕ) :
    (S.map (cechFunctor.{v} f ⋙
      HomologicalComplex.eval (ModuleCat.{max u v} R) (ComplexShape.up ℕ) p)).ShortExact := by
  have hex : Function.Exact S.f.hom S.g.hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · show Function.Exact (cechTermMap f S.f p) (cechTermMap f S.g p)
    rw [cechTermMap_eq_cechTermLinearMap, cechTermMap_eq_cechTermLinearMap]
    exact exact_lmap _ _ fun s =>
      IsLocalizedModule.map_exact (Cech.cechSub f s.1)
        (LocalizedModule.mkLinearMap (Cech.cechSub f s.1) S.X₁)
        (LocalizedModule.mkLinearMap (Cech.cechSub f s.1) S.X₂)
        (LocalizedModule.mkLinearMap (Cech.cechSub f s.1) S.X₃) S.f.hom S.g.hom hex
  · show Function.Injective (cechTermMap f S.f p)
    rw [cechTermMap_eq_cechTermLinearMap]
    exact (DirectSum.lmap_injective _).2 fun s =>
      IsLocalizedModule.map_injective (Cech.cechSub f s.1) _ _ _ hS.injective_f
  · show Function.Surjective (cechTermMap f S.g p)
    rw [cechTermMap_eq_cechTermLinearMap]
    exact (DirectSum.lmap_surjective _).2 fun s =>
      IsLocalizedModule.map_surjective (Cech.cechSub f s.1) _ _ _ hS.surjective_g

/-- A short complex of modules all three of whose terms are trivial is short exact. -/
theorem shortExact_of_subsingleton {R' : Type w} [CommRing R']
    (T : ShortComplex (ModuleCat.{w'} R')) (h₁ : Subsingleton T.X₁) (h₂ : Subsingleton T.X₂)
    (h₃ : Subsingleton T.X₃) : T.ShortExact :=
  ModuleCat.shortComplex_shortExact T
    (fun _ => ⟨fun _ => ⟨0, h₂.elim _ _⟩, fun _ => h₃.elim _ _⟩)
    (fun _ _ _ => h₁.elim _ _) (fun _ => ⟨0, h₃.elim _ _⟩)

/-- In a negative degree the integer-indexed Čech complexes all vanish, so the sequence there is
short exact for trivial reasons. -/
theorem shortExact_map_extendedCechTerm_of_neg (i : ℤ) (hi : i < 0) :
    (S.map (extendedCechFunctor.{v} f ⋙
      HomologicalComplex.eval (ModuleCat.{max u v} R) (ComplexShape.up ℤ) i)).ShortExact := by
  have hzero : ∀ M : ModuleCat.{max u v} R, Subsingleton ((extendedCechComplex f M).X i) :=
    fun M => ModuleCat.isZero_iff_subsingleton.1
      (isZero_extendedCechComplex_X f M i (Or.inl hi))
  exact shortExact_of_subsingleton _ (hzero S.X₁) (hzero S.X₂) (hzero S.X₃)

/-- **The Čech complexes of a short exact sequence of modules form a short exact sequence.**
Localization is an exact functor and direct sums preserve exactness, so the extended alternating
Čech complexes of `0 → N → F → M → 0` fit into a short exact sequence of cochain complexes. This
is the input from which the long exact sequence of local cohomology is obtained. -/
alias shortExact_map_extendedCechFunctor :=
  Stacks.LocalCohomology.shortExact_map_extendedCechFunctor

end ShortExact

end Stacks.LocalCohomology.LongExactSequence

end
