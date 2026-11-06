module

public import StacksFrontier.Algebra.Homology.InjectiveDimension.Criteria
public import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.CategoryTheory.Triangulated.Yoneda

/-!
# Finite injective dimension over a Noetherian ring

Let `R` be a Noetherian ring and let `I` be an ideal contained in the Jacobson radical. For a
bounded below complex with finite cohomology modules, finite injective dimension is equivalent to
uniform high-degree Ext vanishing against the quotients `R/J` for all ideals `J` containing `I`.
Over a Noetherian local ring one may take `I` to be the maximal ideal, so that testing against
the residue field alone suffices.

## Main definitions

This file introduces no new definitions.

## Main results

* `StacksDraft.InjectiveDimension.hasFiniteInjectiveDimension_iff_quotient_ext_vanishing`: the
  quotient-module criterion for finite injective dimension over a Noetherian ring.
* `StacksDraft.InjectiveDimension.hasFiniteInjectiveDimension_iff_residueField_ext_vanishing`:
  the residue-field criterion over a Noetherian local ring.

## Implementation notes

The bounded below derived category is represented by `DerivedCategory.Plus`. Finiteness of each
cohomology module is expressed by `Module.Finite`, and vanishing of an Ext group by its
underlying type being a subsingleton. Quotient modules, and the residue field, are shrunk into
the universe containing the target module.

Finiteness of the integer-graded Ext groups between finite modules is obtained from Mathlib's
`ModuleCat.finite_ext`, which covers the nonnegative degrees, together with the vanishing of the
negative degrees; see `finite_zExt_of_noetherian` below.

## References

* [Stacks Project, Tag 0DW2](https://stacks.math.columbia.edu/tag/0DW2)
* [Stacks Project, Tag 0AVJ](https://stacks.math.columbia.edu/tag/0AVJ)
-/

open CategoryTheory Limits Pretriangulated DerivedCategory

namespace StacksDraft.InjectiveDimension

universe u v

attribute [local instance] HasDerivedCategory.standard

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Over a Noetherian ring, a module in the middle of an exact sequence `A → N → B` of
finite modules is finite. -/
private lemma module_finite_of_exact {A N B : Type*} [AddCommGroup A] [Module R A]
    [AddCommGroup N] [Module R N] [AddCommGroup B] [Module R B]
    [Module.Finite R A] [Module.Finite R B] (φ₁ : A →ₗ[R] N) (φ₂ : N →ₗ[R] B)
    (h : ∀ x, φ₂ x = 0 → ∃ y, φ₁ y = x) : Module.Finite R N := by
  have hker : LinearMap.ker φ₂ ≤ LinearMap.range φ₁ := fun x hx => h x hx
  have : IsNoetherian R (LinearMap.ker φ₂) := isNoetherian_of_le hker
  have : Module.Finite R (N ⧸ LinearMap.ker φ₂) :=
    Module.Finite.equiv φ₂.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker φ₂)

/-- `Hom(X, -)` applied to a distinguished triangle: finiteness of the outer terms gives
finiteness of the middle term. -/
private lemma finite_hom_obj₂_of_distTriang (X : DerivedCategory (ModuleCat.{v} R))
    (T : Triangle (DerivedCategory (ModuleCat.{v} R))) (hT : T ∈ distTriang _)
    (h₁ : Module.Finite R (X ⟶ T.obj₁)) (h₃ : Module.Finite R (X ⟶ T.obj₃)) :
    Module.Finite R (X ⟶ T.obj₂) :=
  module_finite_of_exact (Linear.rightComp R X T.mor₁) (Linear.rightComp R X T.mor₂)
    (fun x hx => by
      obtain ⟨y, hy⟩ := Triangle.coyoneda_exact₂ T hT x hx
      exact ⟨y, hy.symm⟩)

/-- `Ext(M, X⟦j⟧)` is finite when it is finite for `τ_{≤ m} X` and `τ_{≥ m + 1} X`. -/
private lemma finite_hom_shift_of_truncLE_truncGE (M : ModuleCat.{v} R)
    (X : DerivedCategory (ModuleCat.{v} R)) (m j : ℤ)
    (h₁ : Module.Finite R ((singleFunctor (ModuleCat.{v} R) 0).obj M ⟶
      ((TStructure.t.truncLE m).obj X)⟦j⟧))
    (h₃ : Module.Finite R ((singleFunctor (ModuleCat.{v} R) 0).obj M ⟶
      ((TStructure.t.truncGE (m + 1)).obj X)⟦j⟧)) :
    Module.Finite R ((singleFunctor (ModuleCat.{v} R) 0).obj M ⟶ X⟦j⟧) :=
  finite_hom_obj₂_of_distTriang (T := (shiftFunctor _ j).obj
    ((TStructure.t.triangleLEGE m (m + 1) rfl).obj X)) _
    (Triangle.shift_distinguished _ (TStructure.t.triangleLEGE_distinguished m (m + 1) rfl X) j)
    h₁ h₃

/-- The truncation `τ_{≤ m}` preserves finiteness of cohomology modules. -/
private lemma finite_homology_truncLE (L : DerivedCategory (ModuleCat.{v} R))
    (hL : ∀ k, Module.Finite R ((homologyFunctor (ModuleCat.{v} R) k).obj L)) (m k : ℤ) :
    Module.Finite R ((homologyFunctor (ModuleCat.{v} R) k).obj
      ((TStructure.t.truncLE m).obj L)) := by
  by_cases hk : k ≤ m
  · let T := (TStructure.t.triangleLEGE m (m + 1) rfl).obj L
    have hT : T ∈ distTriang _ := TStructure.t.triangleLEGE_distinguished m (m + 1) rfl L
    have h3 : TStructure.t.IsGE ((TStructure.t.truncGE (m + 1)).obj L) (m + 1) :=
      inferInstance
    have hmono : Mono ((homologyFunctor _ k).map T.mor₁) := by
      rw [HomologySequence.mono_homologyMap_mor₁_iff T hT (k - 1) k (by omega)]
      exact (isZero_of_isGE (hX := h3) _ (m + 1) (k - 1) (by omega)).eq_of_src _ _
    have : IsNoetherian R ((homologyFunctor (ModuleCat.{v} R) k).obj T.obj₂) :=
      @isNoetherian_of_isNoetherianRing_of_finite R _ _ _ _ _ (hL k)
    exact Module.Finite.of_injective ((homologyFunctor _ k).map T.mor₁).hom
      ((ModuleCat.mono_iff_injective _).1 hmono)
  · have : Subsingleton ((homologyFunctor (ModuleCat.{v} R) k).obj
        ((TStructure.t.truncLE m).obj L)) :=
      ModuleCat.isZero_iff_subsingleton.mp (isZero_of_isLE _ m k (by omega))
    infer_instance

omit [IsNoetherianRing R] in
/-- The truncation `τ_{≥ m}` preserves finiteness of cohomology modules. -/
private lemma finite_homology_truncGE (L : DerivedCategory (ModuleCat.{v} R))
    (hL : ∀ k, Module.Finite R ((homologyFunctor (ModuleCat.{v} R) k).obj L)) (m k : ℤ) :
    Module.Finite R ((homologyFunctor (ModuleCat.{v} R) k).obj
      ((TStructure.t.truncGE m).obj L)) := by
  by_cases hk : m ≤ k
  · let T := (TStructure.t.triangleLEGE (m - 1) m (by omega)).obj L
    have hT : T ∈ distTriang _ := TStructure.t.triangleLEGE_distinguished (m - 1) m (by omega) L
    have h1 : TStructure.t.IsLE ((TStructure.t.truncLE (m - 1)).obj L) (m - 1) :=
      inferInstance
    have hepi : Epi ((homologyFunctor _ k).map T.mor₂) := by
      rw [HomologySequence.epi_homologyMap_mor₂_iff T hT k (k + 1) (by omega)]
      exact (isZero_of_isLE (hX := h1) _ (m - 1) (k + 1) (by omega)).eq_of_tgt _ _
    have : Module.Finite R ((homologyFunctor (ModuleCat.{v} R) k).obj T.obj₂) := hL k
    exact Module.Finite.of_surjective ((homologyFunctor _ k).map T.mor₂).hom
      ((ModuleCat.epi_iff_surjective _).1 hepi)
  · have : Subsingleton ((homologyFunctor (ModuleCat.{v} R) k).obj
        ((TStructure.t.truncGE m).obj L)) :=
      ModuleCat.isZero_iff_subsingleton.mp (isZero_of_isGE _ m k (by omega))
    infer_instance

/-- There are no nonzero maps from an object in degrees `≤ 0` to one in degrees `≥ n > 0`. -/
private lemma subsingleton_hom_of_isLE_of_isGE {S : Type u} [CommRing S]
    {X Y : DerivedCategory (ModuleCat.{v} S)}
    (n : ℤ) (hn : 0 < n) [X.IsLE 0] [Y.IsGE n] : Subsingleton (X ⟶ Y) :=
  subsingleton_of_forall_eq 0 fun f => TStructure.t.zero f 0 n hn

variable [Small.{v} R]

/-- The integer-graded `Ext` groups between two finite modules over a Noetherian ring are
finite. In nonnegative degrees this is Mathlib's `ModuleCat.finite_ext` transported along
`Abelian.Ext.homLinearEquiv`; in negative degrees the group vanishes. -/
private lemma finite_zExt_of_noetherian (M Y : ModuleCat.{v} R)
    [Module.Finite R M] [Module.Finite R Y] (i : ℤ) :
    Module.Finite R (DerivedCategory.Ext ((singleFunctor (ModuleCat.{v} R) 0).obj M)
      ((singleFunctor (ModuleCat.{v} R) 0).obj Y) i) := by
  rcases lt_or_ge i 0 with hi | hi
  · have : (((singleFunctor (ModuleCat.{v} R) 0).obj Y)⟦i⟧).IsGE (-i) :=
      TStructure.t.isGE_shift _ 0 i (-i) (by omega)
    have : Subsingleton (DerivedCategory.Ext ((singleFunctor (ModuleCat.{v} R) 0).obj M)
        ((singleFunctor (ModuleCat.{v} R) 0).obj Y) i) :=
      subsingleton_hom_of_isLE_of_isGE (-i) (by omega)
    infer_instance
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n : ℤ) := ⟨i.toNat, by omega⟩
    exact Module.Finite.equiv (Abelian.Ext.homLinearEquiv (R := R) (X := M) (Y := Y) (n := n))

/-- `Ext` between finite modules placed in arbitrary degrees is finite. -/
private lemma finite_hom_single_shift (M Y : ModuleCat.{v} R)
    [Module.Finite R M] [Module.Finite R Y] (n j : ℤ) :
    Module.Finite R ((singleFunctor (ModuleCat.{v} R) 0).obj M ⟶
      ((singleFunctor (ModuleCat.{v} R) n).obj Y)⟦j⟧) := by
  have e : ((singleFunctor (ModuleCat.{v} R) n).obj Y)⟦j⟧ ≅
      ((singleFunctor (ModuleCat.{v} R) 0).obj Y)⟦j - n⟧ :=
    ((singleFunctors _).shiftIso j (n - j) n (by omega)).app Y ≪≫
      (((singleFunctors _).shiftIso (j - n) (n - j) 0 (by omega)).app Y).symm
  have := finite_zExt_of_noetherian M Y (j - n)
  exact Module.Finite.equiv (Linear.homCongr R (Iso.refl _) e).symm

/-- `Ext(M, X)` is finite when `X` is concentrated in one degree with finite cohomology. -/
private lemma finite_hom_shift_of_isGE_of_isLE (M : ModuleCat.{v} R) [Module.Finite R M]
    (X : DerivedCategory (ModuleCat.{v} R)) (m : ℤ) [X.IsGE m] [X.IsLE m]
    (hX : Module.Finite R ((homologyFunctor (ModuleCat.{v} R) m).obj X)) (j : ℤ) :
    Module.Finite R ((singleFunctor (ModuleCat.{v} R) 0).obj M ⟶ X⟦j⟧) := by
  obtain ⟨Y, ⟨e⟩⟩ := X.exists_iso_singleFunctor_obj_of_isGE_of_isLE m
  have : Module.Finite R Y := Module.Finite.equiv
    ((homologyFunctor _ m).mapIso e ≪≫
      (singleFunctorCompHomologyFunctorIso _ m).app Y).toLinearEquiv
  have := finite_hom_single_shift M Y m j
  exact Module.Finite.equiv
    (Linear.homCongr R (Iso.refl _) ((shiftFunctor _ j).mapIso e)).symm

/-- `Ext(M, X)` is finite when `X` is bounded with finite cohomology, by induction on the
amplitude. -/
private lemma finite_hom_shift_of_bounded (M : ModuleCat.{v} R) [Module.Finite R M] (a : ℤ)
    (n : ℕ) : ∀ (X : DerivedCategory (ModuleCat.{v} R)) (_ : X.IsGE a) (_ : X.IsLE (a + n))
    (_ : ∀ k, Module.Finite R ((homologyFunctor (ModuleCat.{v} R) k).obj X)) (j : ℤ),
    Module.Finite R ((singleFunctor (ModuleCat.{v} R) 0).obj M ⟶ X⟦j⟧) := by
  induction n with
  | zero =>
    intro X _ h hX j
    have : X.IsLE a := by simpa using h
    exact finite_hom_shift_of_isGE_of_isLE M X a (hX a) j
  | succ n ih =>
    intro X hGE hLE hX j
    have hLE' : X.IsLE (a + n + 1) := by
      have := hLE; push_cast at this; simpa [add_assoc] using this
    exact finite_hom_shift_of_truncLE_truncGE M X (a + n) j
      (ih _ inferInstance inferInstance (finite_homology_truncLE X hX _) j)
      (finite_hom_shift_of_isGE_of_isLE M _ (a + n + 1) (finite_homology_truncGE X hX _ _) j)

/-- `Ext^i(M, L)` is finite for finite `M` and bounded below `L` with finite cohomology. -/
private lemma finite_ext_of_isGE (M : ModuleCat.{v} R) [Module.Finite R M]
    (L : DerivedCategory (ModuleCat.{v} R)) (a : ℤ) [L.IsGE a]
    (hL : ∀ k, Module.Finite R ((homologyFunctor (ModuleCat.{v} R) k).obj L)) (i : ℤ) :
    Module.Finite R (DerivedCategory.Ext ((singleFunctor (ModuleCat.{v} R) 0).obj M) L i) := by
  let m := max a i
  obtain ⟨n, hn⟩ : ∃ n : ℕ, m = a + n := ⟨(m - a).toNat, by omega⟩
  refine finite_hom_shift_of_truncLE_truncGE M L m i ?_ ?_
  · have : ((TStructure.t.truncLE m).obj L).IsLE (a + n) := hn ▸ inferInstance
    exact finite_hom_shift_of_bounded M a n _ inferInstance this
      (finite_homology_truncLE L hL _) i
  · have : (((TStructure.t.truncGE (m + 1)).obj L)⟦i⟧).IsGE (m + 1 - i) :=
      TStructure.t.isGE_shift _ (m + 1) i (m + 1 - i) (by omega)
    have := subsingleton_hom_of_isLE_of_isGE (X := (singleFunctor (ModuleCat.{v} R) 0).obj M)
      (Y := ((TStructure.t.truncGE (m + 1)).obj L)⟦i⟧) (m + 1 - i) (by omega)
    infer_instance

/-- Vanishing of `Ext^i(M, L)` for all `i > b`. -/
private abbrev ExtVanishesAbove (L : DerivedCategory (ModuleCat.{v} R)) (b : ℤ)
    (M : ModuleCat.{v} R) : Prop :=
  ∀ i : ℤ, b < i → Subsingleton ((singleFunctor (ModuleCat.{v} R) 0).obj M ⟶ L⟦i⟧)

omit [IsNoetherianRing R] [Small.{v} R] in
/-- High-degree `Ext` vanishing is invariant under isomorphism of the first argument. -/
private lemma extVanishesAbove_of_iso {L : DerivedCategory (ModuleCat.{v} R)} {b : ℤ}
    {M M' : ModuleCat.{v} R} (e : M ≅ M') (h : ExtVanishesAbove L b M') :
    ExtVanishesAbove L b M := fun i hi =>
  have := h i hi
  (Linear.homCongr R ((singleFunctor _ 0).mapIso e) (Iso.refl _)).injective.subsingleton

omit [IsNoetherianRing R] [Small.{v} R] in
/-- High-degree `Ext` vanishing is closed under extensions. -/
private lemma extVanishesAbove_of_shortExact {L : DerivedCategory (ModuleCat.{v} R)} {b : ℤ}
    {S : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact)
    (h₁ : ExtVanishesAbove L b S.X₁) (h₃ : ExtVanishesAbove L b S.X₃) :
    ExtVanishesAbove L b S.X₂ := fun i hi => by
  refine ⟨fun x y => ?_⟩
  have hx : ∀ z : (singleFunctor (ModuleCat.{v} R) 0).obj S.X₂ ⟶ L⟦i⟧, z = 0 := fun z => by
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ _ hS.singleTriangle_distinguished z
      ((h₁ i hi).elim _ _)
    rw [hg, (h₃ i hi).elim g 0, comp_zero]
  rw [hx x, hx y]

omit [IsNoetherianRing R] [Small.{v} R] in
/-- High-degree `Ext` vanishing holds for the zero module. -/
private lemma extVanishesAbove_of_subsingleton (L : DerivedCategory (ModuleCat.{v} R)) (b : ℤ)
    (M : ModuleCat.{v} R) [Subsingleton M] : ExtVanishesAbove L b M := fun _ _ =>
  ⟨fun x y => ((singleFunctor _ 0).map_isZero
    (ModuleCat.isZero_of_subsingleton M)).eq_of_src x y⟩

/-- Filtration argument: vanishing for the quotients `R/𝔮` with `J ≤ 𝔮` gives vanishing for all
finite modules annihilated by `J`. -/
private lemma extVanishesAbove_of_quotient_prime (L : DerivedCategory (ModuleCat.{v} R))
    (b : ℤ) (J : Ideal R)
    (h : ∀ q : Ideal R, q.IsPrime → J ≤ q →
      ExtVanishesAbove L b (ModuleCat.of R (Shrink.{v} (R ⧸ q))))
    (N : Type v) [AddCommGroup N] [Module R N] [Module.Finite R N]
    (hN : J ≤ Module.annihilator R N) : ExtVanishesAbove L b (ModuleCat.of R N) := by
  revert hN
  refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R ‹_›
    (motive := fun N _ _ _ => J ≤ Module.annihilator R N →
      ExtVanishesAbove L b (ModuleCat.of R N)) ?_ ?_ ?_
  · intro N _ _ _ _ _
    exact extVanishesAbove_of_subsingleton L b _
  · intro N _ _ _ q e hN
    rw [e.annihilator_eq, Ideal.annihilator_quotient] at hN
    exact extVanishesAbove_of_iso
      (e.trans (Shrink.linearEquiv R (R ⧸ q.asIdeal)).symm).toModuleIso
      (h q.asIdeal q.isPrime hN)
  · intro N₁ _ _ _ N₂ _ _ _ N₃ _ _ _ f g hf hg hfg h₁ h₃ hN
    let S := ModuleCat.shortComplexOfCompEqZero f g hfg.linearMap_comp_eq_zero
    have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S hfg hf hg
    exact extVanishesAbove_of_shortExact hS
      (h₁ (hN.trans (f.annihilator_le_of_injective hf)))
      (h₃ (hN.trans (g.annihilator_le_of_surjective hg)))

omit [IsNoetherianRing R] [Small.{v} R] in
/-- Shifting the source by `-1` identifies `Hom(X⟦-1⟧, Y⟦i⟧)` with `Hom(X, Y⟦i + 1⟧)`. -/
private lemma subsingleton_hom_shift_neg_one {X Y : DerivedCategory (ModuleCat.{v} R)} (i : ℤ)
    (h : Subsingleton (X ⟶ Y⟦i + 1⟧)) : Subsingleton (X⟦(-1 : ℤ)⟧ ⟶ Y⟦i⟧) := by
  refine ⟨fun x y => (shiftFunctor _ (1 : ℤ)).map_injective ?_⟩
  let e₁ := (shiftFunctorCompIsoId (DerivedCategory (ModuleCat.{v} R)) (-1 : ℤ) 1
    (by omega)).app X
  let e₂ := (shiftFunctorAdd' (DerivedCategory (ModuleCat.{v} R)) i 1 (i + 1) rfl).symm.app Y
  have := h.elim (e₁.inv ≫ x⟦(1 : ℤ)⟧' ≫ e₂.hom) (e₁.inv ≫ y⟦(1 : ℤ)⟧' ≫ e₂.hom)
  simpa using this

omit [IsNoetherianRing R] in
/-- The short exact sequence `0 → R/𝔭 → R/𝔭 → R/(𝔭 + (f)) → 0` given by multiplication by
`f ∉ 𝔭`, with all terms shrunk into the module universe. -/
private lemma exists_shortExact_mul (p : Ideal R) [p.IsPrime] (f : R) (hf : f ∉ p) :
    ∃ (S : ShortComplex (ModuleCat.{v} R)) (_ : S.ShortExact)
      (e₁ : S.X₁ ≅ ModuleCat.of R (Shrink.{v} (R ⧸ p)))
      (e₂ : S.X₂ ≅ ModuleCat.of R (Shrink.{v} (R ⧸ p)))
      (_ : S.X₃ ≅ ModuleCat.of R (Shrink.{v} (R ⧸ (p ⊔ Ideal.span {f})))),
      S.f = e₁.hom ≫ (f • 𝟙 _) ≫ e₂.inv := by
  let f' : (R ⧸ p) →ₗ[R] (R ⧸ p) := f • LinearMap.id
  let g' : (R ⧸ p) →ₗ[R] (R ⧸ (p ⊔ Ideal.span {f})) := Submodule.factor le_sup_left
  have hinj : Function.Injective f' := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H r =>
      have : f * r ∈ p := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
        simpa [f', Algebra.smul_def, Ideal.Quotient.algebraMap_eq] using hx
      exact (Submodule.Quotient.mk_eq_zero p).2
        ((Ideal.IsPrime.mem_or_mem ‹_› this).resolve_left hf)
  have hexact : Function.Exact f' g' := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H r =>
      simp only [g', Submodule.factor, Submodule.mapQ_apply, LinearMap.id_apply,
        Submodule.Quotient.mk_eq_zero, Set.mem_range, f']
      constructor
      · intro hr
        obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 hr
        obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hc
        refine ⟨Submodule.Quotient.mk d, ?_⟩
        rw [LinearMap.smul_apply, LinearMap.id_apply, ← Submodule.Quotient.mk_smul,
          Submodule.Quotient.eq]
        simpa [smul_eq_mul, mul_comm] using p.neg_mem ha
      · rintro ⟨y, hy⟩
        induction y using Submodule.Quotient.induction_on with
        | H d =>
          rw [LinearMap.smul_apply, LinearMap.id_apply, ← Submodule.Quotient.mk_smul,
            Submodule.Quotient.eq] at hy
          have : r = (r - f • d) + d • f := by simp [smul_eq_mul, mul_comm]
          rw [this]
          refine Submodule.add_mem_sup ?_
            (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self f))
          simpa using p.neg_mem hy
  have hsurj : Function.Surjective g' := Submodule.factor_surjective _
  refine ⟨_, ModuleCat.shortComplexOfConj_shortExact (Shrink.linearEquiv R (R ⧸ p))
    (Shrink.linearEquiv R (R ⧸ p)) (Shrink.linearEquiv R _) f' g' hexact hinj hsurj,
    Iso.refl _, Iso.refl _, Iso.refl _, ?_⟩
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun x => ?_
  simp [f', ModuleCat.hom_smul]

omit [IsNoetherianRing R] in
/-- A shrunk cyclic module `R/J` is finite. -/
private lemma finite_shrink_quotient (J : Ideal R) :
    Module.Finite R (Shrink.{v} (R ⧸ J)) :=
  Module.Finite.equiv (Shrink.linearEquiv R (R ⧸ J)).symm

omit [IsNoetherianRing R] in
/-- The annihilator of the shrunk module `R/J` is `J`. -/
private lemma annihilator_shrink_quotient (J : Ideal R) :
    Module.annihilator R (Shrink.{v} (R ⧸ J)) = J := by
  rw [(Shrink.linearEquiv R (R ⧸ J)).annihilator_eq, Ideal.annihilator_quotient]

/-- The Noetherian induction and Nakayama step of the source proof: vanishing against all `R/J`,
`J ⊇ I`, propagates to vanishing against every `R/𝔭`. -/
private lemma extVanishesAbove_quotient_prime (I : Ideal R)
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal R)) (L : DerivedCategory (ModuleCat.{v} R)) (a : ℤ)
    [L.IsGE a] (hL : ∀ k, Module.Finite R ((homologyFunctor (ModuleCat.{v} R) k).obj L))
    (b : ℤ)
    (h : ∀ J : Ideal R, I ≤ J → ExtVanishesAbove L b (ModuleCat.of R (Shrink.{v} (R ⧸ J))))
    (p : Ideal R) (hp : p.IsPrime) :
    ExtVanishesAbove L b (ModuleCat.of R (Shrink.{v} (R ⧸ p))) := by
  induction p using WellFoundedGT.induction with
  | _ p ih =>
  by_cases hIp : I ≤ p
  · exact h p hIp
  obtain ⟨f, hfI, hfp⟩ := Set.not_subset.1 hIp
  obtain ⟨S, hS, e₁, e₂, e₃, hSf⟩ := exists_shortExact_mul p f hfp
  have h₃ : ExtVanishesAbove L b (ModuleCat.of R (Shrink.{v} (R ⧸ (p ⊔ Ideal.span {f})))) :=
    extVanishesAbove_of_quotient_prime L b (p ⊔ Ideal.span {f})
      (fun q hq hpq => ih q (lt_of_le_of_ne (le_sup_left.trans hpq) (fun hpq' => hfp
        (hpq'.symm ▸ hpq (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))))) hq)
      _ (by rw [annihilator_shrink_quotient])
  intro i hi
  let Q := (singleFunctor (ModuleCat.{v} R) 0).obj (ModuleCat.of R (Shrink.{v} (R ⧸ p)))
  have := finite_shrink_quotient.{u, v} p
  have hfin : Module.Finite R (Q ⟶ L⟦i⟧) := finite_ext_of_isGE _ L a hL i
  have htop : (⊤ : Submodule R (Q ⟶ L⟦i⟧)) ≤ I • ⊤ := by
    intro z _
    let T := hS.singleTriangle
    have hT := inv_rot_of_distTriang _ hS.singleTriangle_distinguished
    let z' : (singleFunctor _ 0).obj S.X₁ ⟶ L⟦i⟧ := (singleFunctor _ 0).map e₁.hom ≫ z
    have h₃' := h₃ (i + 1) (by omega)
    have hsub : Subsingleton (T.obj₃⟦(-1 : ℤ)⟧ ⟶ L⟦i⟧) :=
      subsingleton_hom_shift_neg_one i
        (Linear.homCongr R ((singleFunctor _ 0).mapIso e₃) (Iso.refl _)).injective.subsingleton
    obtain ⟨g, hg'⟩ : ∃ g : (singleFunctor _ 0).obj S.X₂ ⟶ L⟦i⟧,
        z' = (singleFunctor _ 0).map S.f ≫ g :=
      Triangle.yoneda_exact₂ _ hT z' (hsub.elim _ _)
    have hz : z = f • ((singleFunctor _ 0).map e₂.inv ≫ g) := by
      have : (singleFunctor _ 0).map e₁.inv ≫ z' = z :=
        ((singleFunctor _ 0).mapIso e₁).inv_hom_id_assoc z
      rw [← this, hg', hSf]
      have h₁₂ := ((singleFunctor _ 0).mapIso e₁).inv_hom_id_assoc
        ((singleFunctor _ 0).map e₂.inv ≫ g)
      simp only [Functor.mapIso_hom, Functor.mapIso_inv] at h₁₂
      simp only [Functor.map_comp, Functor.map_smul, Category.id_comp,
        Linear.smul_comp, Linear.comp_smul, Category.assoc, h₁₂]
    rw [hz]
    exact Submodule.smul_mem_smul hfI Submodule.mem_top
  have := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I ⊤ Module.Finite.fg_top htop hI
  exact ⟨fun x y => by
    have hx : x ∈ (⊥ : Submodule R (Q ⟶ L⟦i⟧)) := this ▸ Submodule.mem_top
    have hy : y ∈ (⊥ : Submodule R (Q ⟶ L⟦i⟧)) := this ▸ Submodule.mem_top
    rw [Submodule.mem_bot] at hx hy
    rw [hx, hy]⟩

end

/-- The converse direction of Stacks 0DW2: uniform high-degree vanishing against the quotients
`R/J`, `J ⊇ I`, gives uniform high-degree vanishing against every quotient `R/J`. -/
private lemma quotient_ext_vanishing_of_le_jacobson
    {R : Type u} [CommRing R] [IsNoetherianRing R] [Small.{v} R]
    (I : Ideal R) (hI : I ≤ Ideal.jacobson (⊥ : Ideal R))
    (K : DerivedCategory.Plus (ModuleCat.{v} R))
    (hK : ∀ i : ℤ, Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj
        (DerivedCategory.Plus.ι.obj K)))
    (b : ℤ)
    (h : ∀ (J : Ideal R), I ≤ J → ∀ i : ℤ, b < i →
      Subsingleton
        (DerivedCategory.Ext
          ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj
            (ModuleCat.of R (Shrink.{v} (R ⧸ J))))
          (DerivedCategory.Plus.ι.obj K) i)) :
    ∃ c : ℤ, ∀ (J : Ideal R) (i : ℤ), c < i →
      Subsingleton
        (DerivedCategory.Ext
          ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj
            (ModuleCat.of R (Shrink.{v} (R ⧸ J))))
          (DerivedCategory.Plus.ι.obj K) i) := by
  obtain ⟨a, ha⟩ := K.2
  have : (DerivedCategory.Plus.ι.obj K).IsGE a := ha
  refine ⟨b, fun J => ?_⟩
  refine extVanishesAbove_of_quotient_prime _ b ⊥ (fun q hq _ => ?_) _ bot_le
  exact extVanishesAbove_quotient_prime I hI _ a hK b h q hq

/-- **Stacks 0DW2.** For a bounded below complex with finite cohomology over a Noetherian ring,
finite injective dimension can be tested by uniform high-degree Ext vanishing against the
quotients by all ideals containing an ideal in the Jacobson radical. -/
@[stacks 0DW2]
public lemma hasFiniteInjectiveDimension_iff_quotient_ext_vanishing
    {R : Type u} [CommRing R] [IsNoetherianRing R] [Small.{v} R]
    (I : Ideal R) (hI : I ≤ Ideal.jacobson (⊥ : Ideal R))
    (K : DerivedCategory.Plus (ModuleCat.{v} R))
    (hK : ∀ i : ℤ, Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj
        (DerivedCategory.Plus.ι.obj K))) :
    HasFiniteInjectiveDimension (DerivedCategory.Plus.ι.obj K) ↔
      ∃ b : ℤ, ∀ (J : Ideal R), I ≤ J → ∀ i : ℤ, b < i →
        Subsingleton
          (DerivedCategory.Ext
            ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj
              (ModuleCat.of R (Shrink.{v} (R ⧸ J))))
            (DerivedCategory.Plus.ι.obj K) i) := by
  let L := DerivedCategory.Plus.ι.obj K
  constructor
  · rintro ⟨a, b, hab⟩
    refine ⟨b, fun J _ i hi ↦ ?_⟩
    exact
      (hasInjectiveAmplitude_iff_ext_vanishing_iff_quotient_vanishing
        L a b).1.1 hab
        (ModuleCat.of R (Shrink.{v} (R ⧸ J))) i (Or.inr hi)
  · rintro ⟨b, hb⟩
    obtain ⟨a, ha⟩ := K.2
    obtain ⟨c, hc⟩ := quotient_ext_vanishing_of_le_jacobson I hI K hK b hb
    refine ⟨a, c, ?_⟩
    apply
      (hasInjectiveAmplitude_iff_ext_vanishing_iff_quotient_vanishing
        L a c).1.2
    apply
      (hasInjectiveAmplitude_iff_ext_vanishing_iff_quotient_vanishing
        L a c).2.2
    intro J i hi
    rcases hi with hi | hi
    · have : L.IsGE a := ha
      let Q := (DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj
        (ModuleCat.of R (Shrink.{v} (R ⧸ J)))
      have : Q.IsLE 0 := by dsimp [Q]; infer_instance
      have : (L⟦i⟧).IsGE (a - i) :=
        DerivedCategory.TStructure.t.isGE_shift L a i (a - i) (by omega)
      exact subsingleton_hom_of_isLE_of_isGE (a - i) (by omega)
    · exact hc J i hi

/-- **Stacks 0AVJ.** A bounded below complex with finite cohomology over a Noetherian local ring
has finite injective dimension if and only if its Ext groups from the residue field vanish in all
sufficiently high degrees. -/
@[stacks 0AVJ]
public lemma hasFiniteInjectiveDimension_iff_residueField_ext_vanishing
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R]
    (K : DerivedCategory.Plus (ModuleCat.{v} R))
    (hK : ∀ i : ℤ, Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj
        (DerivedCategory.Plus.ι.obj K))) :
    HasFiniteInjectiveDimension (DerivedCategory.Plus.ι.obj K) ↔
      ∃ b : ℤ, ∀ i : ℤ, b < i →
        Subsingleton
          (DerivedCategory.Ext
            ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj
              (ModuleCat.of R (Shrink.{v} (R ⧸ IsLocalRing.maximalIdeal R))))
            (DerivedCategory.Plus.ι.obj K) i) := by
  let m := IsLocalRing.maximalIdeal R
  have hmj : m ≤ Ideal.jacobson (⊥ : Ideal R) := by
    simpa [m] using
      (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top).ge
  rw [hasFiniteInjectiveDimension_iff_quotient_ext_vanishing m hmj K hK]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, fun i hi ↦ hb m le_rfl i hi⟩
  · rintro ⟨b, hb⟩
    refine ⟨b, fun J hmJ i hi ↦ ?_⟩
    by_cases hJ : J = ⊤
    · subst J
      have _ : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.mpr rfl
      have _ : Subsingleton (Shrink.{v} (R ⧸ (⊤ : Ideal R))) := (equivShrink _).symm.subsingleton
      exact extVanishesAbove_of_subsingleton _ b (ModuleCat.of R (Shrink.{v} (R ⧸ ⊤))) i hi
    · have hJm : J = m := ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hJ hmJ).symm
      subst J
      exact hb i hi

end StacksDraft.InjectiveDimension
