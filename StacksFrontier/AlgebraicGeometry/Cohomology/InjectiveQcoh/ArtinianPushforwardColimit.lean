module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.Essential
public import StacksFrontier.Algebra.Module.InjectiveHull.Basic
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.QcohPushforwardOpen.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.RingTheory.Dualizing.Artinian
public import StacksFrontier.RingTheory.Dualizing.ResidueFieldHull

/-!
# Injective quasi-coherent modules on a Noetherian affine scheme

Let `S` be a Noetherian affine scheme.  This file shows that every injective object of the
category of quasi-coherent `𝒪_S`-modules is a filtered colimit of modules of the form
`(Z → S)_* 𝒢` with `Z` the spectrum of an Artinian ring and `𝒢` a coherent module on `Z`.

The route is Matlis theory on the ring `R = Γ(S, ⊤)`.  Transporting along the equivalence
between quasi-coherent `𝒪_S`-modules and `R`-modules, an injective quasi-coherent module becomes
an injective `R`-module, hence a direct sum of indecomposable injectives.  Each indecomposable
injective is an injective hull of the residue field at a prime `p`, so it carries an `Rₚ`-action
and is exhausted by the submodules annihilated by the powers `𝔪ₚ^(n+1)`, each of which is finite
over the Artinian ring `Rₚ / 𝔪ₚ^(n+1)`.  Taking finite subsets of the index set of the direct sum
and a level in each filtration gives a filtered family of finite modules over finite products of
Artinian rings whose direct limit is the whole module; the associated sheaves of these modules are
coherent modules on Artinian affine schemes, and the transition back to `S` turns restriction of
scalars into pushforward.

## Main results

* `AlgebraicGeometry.exists_filtered_colimit_pushforwards_artinian`: an injective quasi-coherent
  module on a Noetherian affine scheme is a filtered colimit of pushforwards of coherent modules
  from spectra of Artinian rings.

## Implementation notes

The diagram is taken in the category of quasi-coherent modules, and each of its terms is
identified with a pushforward only up to isomorphism, which avoids choosing a particular Artinian
presentation of a diagram object.

The index category is the preorder of pairs consisting of a finite subset of the index set of the
direct sum decomposition and a level function; it is directed, which is what makes the colimit
filtered.  A finite product of Artinian rings is Artinian and a finite product of finite modules
over the factors is finite over the product, so a finite subset of the decomposition contributes a
single Artinian affine scheme rather than one for each summand.

## References

* [Stacks Project, Tag 09TI](https://stacks.math.columbia.edu/tag/09TI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The quotient of a Noetherian local ring by a positive power of its maximal ideal is
Artinian: the maximal ideal is the unique minimal prime over that power. -/
private alias localPowerQuotient_isArtinian := Dualizing.artinian_maximalIdeal_pow_quotient

/-- The quotient of a local ring by a positive power of its maximal ideal is again local; the
power is a proper ideal, so the quotient is nontrivial. -/
private alias localPowerQuotient_isLocal := Dualizing.local_maximalIdeal_pow_quotient

/-- A simple module over a local ring is isomorphic to the residue field, being a quotient of
the ring by a maximal ideal and hence by the maximal ideal. -/
private theorem simpleModuleEquivResidueField
    (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [IsSimpleModule R M] :
    Nonempty (M ≃ₗ[R] IsLocalRing.ResidueField R) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule R M›
  rw [IsLocalRing.eq_maximalIdeal hI] at e
  exact ⟨e⟩

/-- Essentiality of a monomorphism transfers along an isomorphism of its source. -/
private theorem isEssentialMono_of_iso_comp {R : Type u} [CommRing R]
    {X Y E : ModuleCat.{u} R} (e : X ≅ Y) (i : Y ⟶ E) (f : X ⟶ E) [Mono i] [Mono f]
    (w : e.hom ≫ i = f) (h : Module.IsEssentialMono i) : Module.IsEssentialMono f := by
  intro B hB
  rw [Subobject.mk_eq_mk_of_comm f i e w]
  exact h B hB

/-- An injective hull of a simple module over an Artinian local ring is a finite module: the
simple module is the residue field, for which finiteness of the hull is Matlis' theorem. -/
private theorem injectiveHull_finite_of_simple
    (R : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
    (K E : Type u) [AddCommGroup K] [Module R K]
    [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R K ⟶ ModuleCat.of R E) [Mono i]
    (hE : Module.IsInjectiveHull i) [IsSimpleModule R K] :
    Module.Finite R E := by
  let e : K ≃ₗ[R] IsLocalRing.ResidueField R := (simpleModuleEquivResidueField R K).some
  let eIso : ModuleCat.of R K ≅ ModuleCat.of R (IsLocalRing.ResidueField R) :=
    e.toModuleIso
  let i' : ModuleCat.of R (IsLocalRing.ResidueField R) ⟶ ModuleCat.of R E := eIso.inv ≫ i
  exact Dualizing.finite_of_isInjectiveHull_residueField R E i'
    ⟨hE.1, isEssentialMono_of_iso_comp eIso.symm i i' rfl hE.2⟩

/-- Let `E` be an injective hull of the residue field of a Noetherian local ring `R`.  The
submodule of `E` annihilated by `𝔪 ^ (n + 1)` is a finite module over `R / 𝔪 ^ (n + 1)`, being
an injective hull of the residue field over that Artinian local ring. -/
private theorem maximalIdealPowTorsion_finite
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : ModuleCat.{u} R) (i : ModuleCat.of R (IsLocalRing.ResidueField R) ⟶ E)
    [Mono i] (hE : Module.IsInjectiveHull i) (n : ℕ) :
    Module.Finite (R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1))
      (Dualizing.maximalIdealPowTorsion R E n) := by
  let B := R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1)
  let : IsLocalRing B := localPowerQuotient_isLocal R n
  let : IsArtinianRing B := localPowerQuotient_isArtinian R n
  let K := IsLocalRing.ResidueField R
  let hK := Dualizing.residueFieldModelIsTorsionByMaximalIdealPow R
    (ModuleCat.of R K) (LinearEquiv.refl R K) n
  let : Module B K := hK.module
  let : IsSimpleModule R K :=
    (isSimpleModule_iff_isCoatom).2
      (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal R))
  have : IsSimpleModule B K := {
    toIsSimpleOrder := {
      toNontrivial := ⟨⟨⊥, ⊤, bot_ne_top⟩⟩
      eq_bot_or_eq_top := by
        intro U
        by_cases hU : U = ⊥
        · exact Or.inl hU
        · obtain ⟨x, hxU, hx0⟩ := U.ne_bot_iff.mp hU
          let UR : Submodule R K :=
            { carrier := U
              zero_mem' := U.zero_mem
              add_mem' := U.add_mem
              smul_mem' := by
                intro r y hy
                rw [← Module.IsTorsionBySet.mk_smul hK r y]
                exact U.smul_mem (Ideal.Quotient.mk _ r) hy }
          have hspan : Submodule.span R ({x} : Set K) = ⊤ :=
            (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left
              (Submodule.span_singleton_eq_bot.not.mpr hx0)
          have hle : Submodule.span R ({x} : Set K) ≤ UR :=
            Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxU)
          have hUR : UR = ⊤ := top_le_iff.mp (hspan ▸ hle)
          exact Or.inr (top_le_iff.mp fun y _ => show y ∈ UR by rw [hUR]; exact Submodule.mem_top)
    }
  }
  let hHull := Dualizing.maximalIdealPowTorsion_isInjectiveHull R
    (ModuleCat.of R K) E (LinearEquiv.refl R K) i hE n
  have : Mono (ModuleCat.ofHom
      (Dualizing.residueFieldToMaximalIdealPowTorsion R
        (LinearEquiv.refl R K) i n)) :=
    (ModuleCat.mono_iff_injective _).mpr
      (Dualizing.residueFieldToMaximalIdealPowTorsion_injective R
        (LinearEquiv.refl R K) i
        ((ModuleCat.mono_iff_injective i).1 (by infer_instance)) n)
  exact injectiveHull_finite_of_simple B K
    (Dualizing.maximalIdealPowTorsion R E n)
    (ModuleCat.ofHom
      (Dualizing.residueFieldToMaximalIdealPowTorsion R (LinearEquiv.refl R K) i n))
    hHull

/-- Let `E` be an injective hull of `R ⧸ p` over a Noetherian ring `R`.  Then the action of `R`
on `E` extends to the localization `Rₚ`, making `E` an injective hull of the residue field
`κ(p)`; the submodules of `E` annihilated by the powers of the maximal ideal of `Rₚ` are finite
over the corresponding Artinian quotients of `Rₚ`, and they exhaust `E`. -/
private theorem localizedQuotientHull_has_artinian_stages
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) (hp : p.IsPrime)
    (E : ModuleCat.{u} R)
    (i : ModuleCat.of R (R ⧸ p) ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    ∃ (moduleStructure : Module (Localization.AtPrime p) E),
      ∃ (tower : IsScalarTower R (Localization.AtPrime p) E),
        letI := moduleStructure
        letI := tower
        ∃ (j : ModuleCat.of (Localization.AtPrime p) p.ResidueField ⟶
            ModuleCat.of (Localization.AtPrime p) E),
          ∃ (monoJ : Mono j),
            letI := monoJ
            Module.IsInjectiveHull j ∧
              (∀ n, Module.Finite
                (Localization.AtPrime p ⧸
                  (IsLocalRing.maximalIdeal (Localization.AtPrime p)) ^ (n + 1))
                (Dualizing.maximalIdealPowTorsion (Localization.AtPrime p)
                  (ModuleCat.of (Localization.AtPrime p) E) n)) ∧
              (⨆ n, Dualizing.maximalIdealPowTorsion (Localization.AtPrime p)
                (ModuleCat.of (Localization.AtPrime p) E) n) = ⊤ := by
  let : p.IsPrime := hp
  obtain ⟨moduleStructure, tower, j, monoJ, hjEq, hJ⟩ :=
    Module.exists_isInjectiveHull_residueField_localization p E i hi
  exact ⟨moduleStructure, tower, j, monoJ, hJ, fun n => maximalIdealPowTorsion_finite
    (Localization.AtPrime p) (ModuleCat.of (Localization.AtPrime p) E) j hJ n,
    Dualizing.iSup_maximalIdealPowTorsion_eq_top
      (Localization.AtPrime p) (ModuleCat.of (Localization.AtPrime p) p.ResidueField)
      (ModuleCat.of (Localization.AtPrime p) E) (LinearEquiv.refl _ _) j hJ⟩

/-- The inclusion of `R ⧸ p` into the residue field `κ(p)` at a prime ideal `p`. -/
private noncomputable def quotientToResidueField
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime] :
    ModuleCat.of R (R ⧸ p) ⟶ ModuleCat.of R p.ResidueField :=
  ModuleCat.ofHom ((Algebra.linearMap (R ⧸ p) p.ResidueField).restrictScalars R)

/-- The inclusion of `R ⧸ p` into `κ(p)` is an essential monomorphism: every nonzero element of
the residue field has a nonzero `R`-multiple lying in the image of `R ⧸ p`. -/
private theorem quotientToResidueField_isEssential
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime] :
    let f := quotientToResidueField R p
    letI : Mono f := (ModuleCat.mono_iff_injective f).mpr
      p.injective_algebraMap_quotient_residueField
    Module.IsEssentialMono f := by
  classical
  let f := quotientToResidueField R p
  have hf : Function.Injective f.hom := p.injective_algebraMap_quotient_residueField
  let : Mono f := (ModuleCat.mono_iff_injective f).mpr hf
  have hess : Module.IsEssentialMono f := by
    let M : Submodule R p.ResidueField := f.hom.range
    let kSub : ModuleCat.of R M ⟶ ModuleCat.of R p.ResidueField :=
      ModuleCat.ofHom M.subtype
    have : Mono kSub := (ModuleCat.mono_iff_injective kSub).mpr M.subtype_injective
    have hSub : Module.IsEssentialMono kSub := by
      rw [Module.isEssentialMono_subtype_iff]
      intro x hx
      obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (R ⧸ p) x
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
      refine ⟨r, ?_, ?_⟩
      · show r • x ∈ f.hom.range
        refine ⟨a, ?_⟩
        show (algebraMap (R ⧸ p) p.ResidueField a) = r • x
        rw [Algebra.smul_def]
        show algebraMap (R ⧸ p) p.ResidueField a =
          algebraMap R p.ResidueField r * x
        rw [← hab, ← Ideal.algebraMap_quotient_residueField_mk (I := p) r,
          div_eq_mul_inv, mul_comm
            (algebraMap (R ⧸ p) p.ResidueField (Ideal.Quotient.mk p r)),
          mul_assoc,
          inv_mul_cancel₀
            (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb), mul_one]
      · intro hz
        have hr : algebraMap R p.ResidueField r ≠ 0 := by
          rw [← Ideal.algebraMap_quotient_residueField_mk]
          exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
        have hz' : algebraMap R p.ResidueField r * x = 0 := by
          simpa [Algebra.smul_def] using hz
        exact hx ((mul_eq_zero.mp hz').resolve_left hr)
    exact isEssentialMono_of_iso_comp (LinearEquiv.ofInjective f.hom hf).toModuleIso kSub f
      (by ext; rfl) hSub
  exact hess

/-- An injective hull of a module identified with the residue field `κ(p)` is also an injective
hull of `R ⧸ p`, because `R ⧸ p ⟶ κ(p)` is itself an essential monomorphism. -/
private theorem residueFieldHull_to_quotientHull
    (R : Type u) [CommRing R] (p : Ideal R) (hp : p.IsPrime)
    (E K : ModuleCat.{u} R) (e : K ≃ₗ[R] p.ResidueField)
    (j : K ⟶ E) [Mono j] (hE : Module.IsInjectiveHull j) :
    ∃ (i : ModuleCat.of R (R ⧸ p) ⟶ E),
      ∃ (monoI : Mono i), letI := monoI; Module.IsInjectiveHull i := by
  let : p.IsPrime := hp
  let f := quotientToResidueField R p
  let : Mono f := (ModuleCat.mono_iff_injective f).mpr
    p.injective_algebraMap_quotient_residueField
  have hfEss : Module.IsEssentialMono f :=
    quotientToResidueField_isEssential R p
  let q : ModuleCat.of R (R ⧸ p) ⟶ K :=
    ModuleCat.ofHom (e.symm.toLinearMap.comp f.hom)
  have hq : Function.Injective q.hom := fun x y hxy =>
    (ModuleCat.mono_iff_injective f).mp inferInstance (by simpa [q] using congrArg e hxy)
  let : Mono q := (ModuleCat.mono_iff_injective q).mpr hq
  have hqEss : Module.IsEssentialMono q := by
    let o := (Subobject.mapIso e.symm.toModuleIso).toOrderIso
    have hmk : o (Subobject.mk f) = Subobject.mk q := rfl
    intro B hB
    have hB' : o.symm B ≠ ⊥ := fun h =>
      hB ((o.apply_symm_apply B).symm.trans ((congrArg o h).trans o.map_bot))
    have h := hfEss (o.symm B) hB'
    have hm : o (o.symm B ⊓ Subobject.mk f) ≠ ⊥ := fun hbot =>
      h (o.injective (hbot.trans o.map_bot.symm))
    rw [o.map_inf, o.apply_symm_apply, hmk] at hm
    exact hm
  exact ⟨q ≫ j, inferInstance, hE.1, Module.isEssentialMono_comp q j hqEss hE.2⟩

/-- An indecomposable injective module `E` over a Noetherian ring is an injective hull of the
residue field `κ(p)` at some prime `p` over the localization `Rₚ`, and is exhausted by the
submodules annihilated by the powers of the maximal ideal of `Rₚ`, each of them finite over the
corresponding Artinian quotient. -/
private theorem indecomposable_injective_has_artinian_stages
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (E : ModuleCat.{u} R) [Injective E] (hE : Indecomposable E) :
    ∃ (p : Ideal R) (hp : p.IsPrime),
      letI := hp
      ∃ (moduleStructure : Module (Localization.AtPrime p) E),
        ∃ (tower : IsScalarTower R (Localization.AtPrime p) E),
          letI := moduleStructure
          letI := tower
          ∃ (j : ModuleCat.of (Localization.AtPrime p) p.ResidueField ⟶
              ModuleCat.of (Localization.AtPrime p) E),
            ∃ (monoJ : Mono j),
              letI := monoJ
              Module.IsInjectiveHull j ∧
                (∀ n, Module.Finite
                  (Localization.AtPrime p ⧸
                    (IsLocalRing.maximalIdeal (Localization.AtPrime p)) ^ (n + 1))
                  (Dualizing.maximalIdealPowTorsion (Localization.AtPrime p)
                    (ModuleCat.of (Localization.AtPrime p) E) n)) ∧
                (⨆ n, Dualizing.maximalIdealPowTorsion (Localization.AtPrime p)
                  (ModuleCat.of (Localization.AtPrime p) E) n) = ⊤ := by
  obtain ⟨p, hp, K, e, i, hi, hHull⟩ :=
    Module.exists_residueField_injectiveHull R E hE
  let : p.IsPrime := hp
  let : Mono i := hi
  obtain ⟨i0, mono0, hHull0⟩ :=
    residueFieldHull_to_quotientHull R p hp E K e i hHull
  let : Mono i0 := mono0
  exact ⟨p, hp,
    localizedQuotientHull_has_artinian_stages R p hp E i0 hHull0⟩

/-- A finite product of Artinian rings is Artinian: each factor is a quotient of the product,
hence Artinian as a module over it. -/
private theorem finiteProductArtinian
    {ι : Type u} [Finite ι] (A : ι → Type u)
    [∀ i, CommRing (A i)] [∀ i, IsArtinianRing (A i)] :
    IsArtinianRing (∀ i, A i) := by
  classical
  let (i : ι) : Algebra (∀ j, A j) (A i) :=
    RingHom.toAlgebra (Pi.evalRingHom A i)
  let (i : ι) : Module (∀ j, A j) (A i) :=
    Module.compHom (A i) (algebraMap (∀ j, A j) (A i))
  let (i : ι) : IsScalarTower (∀ j, A j) (A i) (A i) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hsurj (i : ι) : Function.Surjective (algebraMap (∀ j, A j) (A i)) := by
    show Function.Surjective (Pi.evalRingHom A i)
    exact fun x => ⟨Pi.single i x, by simp⟩
  have (i : ι) : IsArtinian (∀ j, A j) (A i) :=
    isArtinian_of_surjective_algebraMap (hsurj i)
  exact inferInstance

/-- A finite product of modules, each finite over its own factor ring, is finite over the
product ring; each factor ring is a quotient of the product. -/
private theorem finitePiModule
    {ι : Type u} [Finite ι] (A : ι → Type u) (M : ι → Type u)
    [∀ i, CommRing (A i)] [∀ i, AddCommGroup (M i)] [∀ i, Module (A i) (M i)]
    [∀ i, Module.Finite (A i) (M i)] :
    Module.Finite (∀ i, A i) (∀ i, M i) := by
  classical
  let (i : ι) : Algebra (∀ j, A j) (A i) :=
    RingHom.toAlgebra (Pi.evalRingHom A i)
  let (i : ι) : Module (∀ j, A j) (M i) :=
    Module.compHom (M i) (algebraMap (∀ j, A j) (A i))
  let (i : ι) : IsScalarTower (∀ j, A j) (A i) (M i) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hsurj (i : ι) : Function.Surjective (algebraMap (∀ j, A j) (A i)) := by
    show Function.Surjective (Pi.evalRingHom A i)
    exact fun x => ⟨Pi.single i x, by simp⟩
  have (i : ι) : Module.Finite (∀ j, A j) (M i) :=
    Module.finite_def.mpr ((Module.finite_def.mp (inferInstance : Module.Finite (A i) (M i)))
      |>.restrictScalars_of_surjective (hsurj i))
  let : Module (∀ i, A i) (∀ i, M i) := Pi.module _ _ _
  exact Module.Finite.pi

/-- A stage of the filtration: a finite set of summands of a direct sum decomposition together
with a level in the filtration of each summand. -/
private abbrev StageIndex (α : Type u) := Finset α × (α → ℕ)

/-- One stage dominates another when its finite set contains the other's and its levels are
pointwise at least as large. -/
private abbrev stageIndexLE {α : Type u} : LE (StageIndex α) :=
  ⟨fun i j => i.1 ⊆ j.1 ∧ ∀ a, i.2 a ≤ j.2 a⟩

attribute [local instance] stageIndexLE

/-- Domination of stages is reflexive and transitive. -/
private abbrev stageIndexPreorder {α : Type u} : Preorder (StageIndex α) where
  le_refl i := ⟨Set.Subset.rfl, fun _ => le_rfl⟩
  le_trans i j k hij hjk :=
    ⟨Set.Subset.trans hij.1 hjk.1, fun a => le_trans (hij.2 a) (hjk.2 a)⟩

attribute [local instance] stageIndexPreorder

/-- The empty set of summands at level zero is a stage. -/
private theorem stageIndexNonempty {α : Type u} : Nonempty (StageIndex α) :=
  ⟨(∅, fun _ => 0)⟩

attribute [local instance] stageIndexNonempty

/-- Any two stages are dominated by a common one, formed from the union of the finite sets and
the pointwise maximum of the levels. -/
private theorem stageIndexDirected {α : Type u} : IsDirectedOrder (StageIndex α) :=
  ⟨fun i j => by
    classical
    exact ⟨(i.1 ∪ j.1, fun a => max (i.2 a) (j.2 a)),
      ⟨Finset.subset_union_left, fun a => le_max_left _ _⟩,
      ⟨Finset.subset_union_right, fun a => le_max_right _ _⟩⟩⟩

attribute [local instance] stageIndexDirected

/-- The module attached to a stage: the direct sum, over the summands the stage names, of the
filtration steps at the levels it prescribes. -/
private abbrev ArtinianStage (R : Type u) [CommRing R] (α : Type u)
    (E : α → Type u) [∀ a, AddCommGroup (E a)] [∀ a, Module R (E a)]
    (P : ∀ a, ℕ → Submodule R (E a)) (i : StageIndex α) :=
  DirectSum {a // a ∈ (i.1 : Set α)} fun a => P a.1 (i.2 a.1)

/-- The transition map between the modules of two stages, given on each summand by the
inclusion of filtration steps followed by the inclusion into the larger direct sum. -/
private noncomputable def artinianStageMap
    {R : Type u} [CommRing R] {α : Type u} [DecidableEq α]
    (E : α → Type u) [∀ a, AddCommGroup (E a)] [∀ a, Module R (E a)]
    (P : ∀ a, ℕ → Submodule R (E a))
    (hP : ∀ a n m, n ≤ m → P a n ≤ P a m)
    (i j : StageIndex α) (hij : i ≤ j) :
    ArtinianStage R α E P i →ₗ[R] ArtinianStage R α E P j :=
  DirectSum.toModule R {a // a ∈ (i.1 : Set α)} (ArtinianStage R α E P j) fun a =>
    DirectSum.lof R {a // a ∈ (j.1 : Set α)} (fun b => P b.1 (j.2 b.1)) ⟨a.1, hij.1 a.2⟩ ∘ₗ
      (Submodule.inclusion (hP a.1 (i.2 a.1) (j.2 a.1) (hij.2 a.1)) :
        P a.1 (i.2 a.1) →ₗ[R] P a.1 (j.2 a.1))

/-- The map from the module of a stage into the whole direct sum, given on each summand by the
inclusion of the filtration step into that summand. -/
private noncomputable def artinianStageToTotal
    {R : Type u} [CommRing R] {α : Type u} [DecidableEq α]
    (E : α → Type u) [∀ a, AddCommGroup (E a)] [∀ a, Module R (E a)]
    (P : ∀ a, ℕ → Submodule R (E a)) (i : StageIndex α) :
    ArtinianStage R α E P i →ₗ[R] DirectSum α E :=
  DirectSum.toModule R {a // a ∈ (i.1 : Set α)} (DirectSum α E) fun a =>
    DirectSum.lof R α E a.1 ∘ₗ (P a.1 (i.2 a.1)).subtype

/-- The maps of the stages into the whole direct sum are compatible with the transition
maps. -/
private theorem artinianStageToTotal_compat
    {R : Type u} [CommRing R] {α : Type u} [DecidableEq α]
    (E : α → Type u) [∀ a, AddCommGroup (E a)] [∀ a, Module R (E a)]
    (P : ∀ a, ℕ → Submodule R (E a))
    (hP : ∀ a n m, n ≤ m → P a n ≤ P a m)
    (i j : StageIndex α) (hij : i ≤ j) :
    artinianStageToTotal E P j ∘ₗ artinianStageMap E P hP i j hij =
      artinianStageToTotal E P i := by
  refine LinearMap.ext fun x => ?_
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | of a x =>
      dsimp [artinianStageToTotal, artinianStageMap]
      rw [← DirectSum.lof_eq_of R, DirectSum.toModule_lof, DirectSum.toModule_lof]
      simp [Submodule.inclusion_apply]

/-- The map of a stage into the whole direct sum carries the component at a summand `a` to the
component at `a`. -/
private theorem artinianStageToTotal_lof
    {R : Type u} [CommRing R] {α : Type u} [DecidableEq α]
    (E : α → Type u) [∀ a, AddCommGroup (E a)] [∀ a, Module R (E a)]
    (P : ∀ a, ℕ → Submodule R (E a)) (i : StageIndex α)
    (a : {a // a ∈ (i.1 : Set α)}) (x : P a.1 (i.2 a.1)) :
    artinianStageToTotal E P i
      (DirectSum.lof R {a // a ∈ (i.1 : Set α)} (fun a => P a.1 (i.2 a.1)) a x) =
      DirectSum.lof R α E a.1 x.1 := by
  dsimp [artinianStageToTotal]
  rw [DirectSum.toModule_lof]
  rfl

/-- The map of a stage into the whole direct sum is injective, since it is injective on each
component. -/
private theorem artinianStageToTotal_injective
    {R : Type u} [CommRing R] {α : Type u} [DecidableEq α]
    (E : α → Type u) [∀ a, AddCommGroup (E a)] [∀ a, Module R (E a)]
    (P : ∀ a, ℕ → Submodule R (E a)) (i : StageIndex α) :
    Function.Injective (artinianStageToTotal E P i) := by
  classical
  have hcomp (a : {a // a ∈ (i.1 : Set α)}) :
      (DirectSum.component R α E a.1).comp (artinianStageToTotal E P i) =
        (P a.1 (i.2 a.1)).subtype.comp
          (DirectSum.component R {a // a ∈ (i.1 : Set α)}
            (fun a => P a.1 (i.2 a.1)) a) := by
    apply DirectSum.linearMap_ext
    intro b
    ext x
    simp only [LinearMap.comp_apply]
    rw [artinianStageToTotal_lof]
    by_cases hba : b.1 = a.1
    · have : b = a := Subtype.ext hba
      subst b
      simp
    · have hba' : b ≠ a := fun h => hba (congrArg Subtype.val h)
      simp [DirectSum.component.of, hba, hba']
  intro x y h
  refine DirectSum.ext_component R fun a => (P a.1 (i.2 a.1)).subtype_injective ?_
  simpa only [← LinearMap.comp_apply, hcomp a] using congrArg (DirectSum.component R α E a.1) h

/-- The image of the module of a stage in the whole direct sum, as a submodule. -/
private noncomputable abbrev ArtinianStageSubmodule
    {R : Type u} [CommRing R] {α : Type u} [DecidableEq α]
    (E : α → Type u) [∀ a, AddCommGroup (E a)] [∀ a, Module R (E a)]
    (P : ∀ a, ℕ → Submodule R (E a)) (i : StageIndex α) :
    Submodule R (DirectSum α E) :=
  LinearMap.range (artinianStageToTotal E P i)

/-- The images of the stages increase along the domination relation. -/
private theorem artinianStageSubmodule_mono
    {R : Type u} [CommRing R] {α : Type u} [DecidableEq α]
    (E : α → Type u) [∀ a, AddCommGroup (E a)] [∀ a, Module R (E a)]
    (P : ∀ a, ℕ → Submodule R (E a))
    (hP : ∀ a n m, n ≤ m → P a n ≤ P a m)
    (i j : StageIndex α) (hij : i ≤ j) :
    ArtinianStageSubmodule E P i ≤ ArtinianStageSubmodule E P j := by
  rintro x ⟨y, rfl⟩
  rw [← artinianStageToTotal_compat E P hP i j hij]
  exact LinearMap.mem_range_self _ _

/-- If the filtration of each summand exhausts it, then the direct limit of the images of the
stages, along the inclusions, is the whole direct sum. -/
private theorem filteredStageDirectSumEquiv
    {R : Type u} [CommRing R] {α : Type u} [DecidableEq α]
    (E : α → Type u) [∀ a, AddCommGroup (E a)] [∀ a, Module R (E a)]
    (P : ∀ a, ℕ → Submodule R (E a))
    (hP : ∀ a n m, n ≤ m → P a n ≤ P a m)
    (hExhaust : ∀ a, (⨆ n, P a n) = ⊤) :
    let f : ∀ i j, i ≤ j →
        ArtinianStageSubmodule E P i →ₗ[R] ArtinianStageSubmodule E P j :=
      fun i j hij => Submodule.inclusion (artinianStageSubmodule_mono E P hP i j hij)
    letI : DecidableEq (StageIndex α) := Classical.decEq _
    letI : DirectedSystem (fun i => ArtinianStageSubmodule E P i)
        (fun {i j} hij => f i j hij) := by
      constructor
      · intro i x
        dsimp [f]
        exact Subtype.ext rfl
      · intro k j i hij hjk x
        dsimp [f]
        exact Subtype.ext rfl
    Nonempty (Module.DirectLimit (fun i => ArtinianStageSubmodule E P i) f ≃ₗ[R]
      DirectSum α E) := by
  classical
  let f : ∀ i j, i ≤ j →
      ArtinianStageSubmodule E P i →ₗ[R] ArtinianStageSubmodule E P j :=
    fun i j hij => Submodule.inclusion (artinianStageSubmodule_mono E P hP i j hij)
  let : DecidableEq (StageIndex α) := Classical.decEq _
  let : DirectedSystem (fun i => ArtinianStageSubmodule E P i)
      (fun {i j} hij => f i j hij) := by
    constructor <;> intros <;> exact Subtype.ext rfl
  let G : StageIndex α → Type u := fun i => ArtinianStageSubmodule E P i
  let q : Module.DirectLimit G f →ₗ[R] DirectSum α E :=
    Module.DirectLimit.lift R (StageIndex α) G f
      (fun i => (ArtinianStageSubmodule E P i).subtype)
      (fun _ _ _ _ => rfl)
  have hqinj : Function.Injective q :=
    Module.DirectLimit.lift_injective
      (fun i => (ArtinianStageSubmodule E P i).subtype)
      (fun _ _ _ _ => rfl)
      (fun i => (ArtinianStageSubmodule E P i).subtype_injective)
  have hqsurj : Function.Surjective q := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => exact ⟨0, by simp [q]⟩
    | add x y hx hy =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        exact ⟨a + b, map_add q a b⟩
    | of a x =>
        have hx : x ∈ (⨆ n, P a n) := by rw [hExhaust a]; simp
        have hdir : Directed (· ≤ ·) (P a) := Monotone.directed_le fun n m h => hP a n m h
        obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed (P a) hdir).mp hx
        let i : StageIndex α := ({a}, fun _ => n)
        let ai : {a // a ∈ (i.1 : Set α)} := ⟨a, by simp [i]⟩
        let z : ArtinianStage R α E P i :=
          DirectSum.lof R {a // a ∈ (i.1 : Set α)} (fun a => P a.1 (i.2 a.1))
            ai ⟨x, hn⟩
        let zi : ArtinianStageSubmodule E P i :=
          ⟨artinianStageToTotal E P i z, LinearMap.mem_range_self _ z⟩
        refine ⟨Module.DirectLimit.of R (StageIndex α) G f i zi, ?_⟩
        show Module.DirectLimit.lift R (StageIndex α) G f
          (fun i => (ArtinianStageSubmodule E P i).subtype)
          (by
            intro i j hij x
            show ((f i j hij x : ArtinianStageSubmodule E P j) : DirectSum α E) = x.1
            rfl)
          (Module.DirectLimit.of R (StageIndex α) G f i zi) = _
        rw [Module.DirectLimit.lift_of]
        show artinianStageToTotal E P i z = DirectSum.lof R α E a x
        rw [artinianStageToTotal_lof]
  exact ⟨LinearEquiv.ofBijective q ⟨hqinj, hqsurj⟩⟩

/-- An indecomposable injective module over a Noetherian ring carries an increasing filtration
exhausting it, each step of which is, after restriction of scalars, a finite module over an
Artinian ring. -/
private theorem indecomposable_filtration
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (E : ModuleCat.{u} R) [Injective E] (hE : Indecomposable E) :
    ∃ P : ℕ → Submodule R E, Monotone P ∧ (⨆ n, P n) = ⊤ ∧
      ∀ n, ∃ (B : CommRingCat.{u}) (φ : R →+* B) (N : ModuleCat.{u} B),
        IsArtinianRing B ∧ Module.Finite B N ∧
          Nonempty (ModuleCat.of R (P n) ≅ (ModuleCat.restrictScalars φ).obj N) := by
  classical
  obtain ⟨p, hp, ms, tower, j, hj, hHull, hfin, hex⟩ :=
    indecomposable_injective_has_artinian_stages R E hE
  let := hp
  let := ms
  let := tower
  let A := Localization.AtPrime p
  let Q (n : ℕ) := Dualizing.maximalIdealPowTorsion A (ModuleCat.of A E) n
  let P (n : ℕ) : Submodule R E := (Q n).restrictScalars R
  have hmono : Monotone P := by
    intro n m hnm x hx
    show x ∈ Q m
    rw [Submodule.mem_torsionBySet_iff]
    intro a
    exact ((Submodule.mem_torsionBySet_iff _ _).mp hx)
      ⟨a.val, Ideal.pow_le_pow_right (Nat.add_le_add_right hnm 1) a.property⟩
  refine ⟨P, hmono, ?_, ?_⟩
  · apply top_le_iff.mp
    intro x _
    have hx : x ∈ (⨆ n, Q n) := by rw [hex]; trivial
    obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed Q hmono.directed_le).mp hx
    exact (le_iSup P n) hn
  · intro n
    let B := A ⧸ (IsLocalRing.maximalIdeal A) ^ (n + 1)
    let φ : R →+* B := (Ideal.Quotient.mk _).comp (algebraMap R A)
    let N := ModuleCat.of B (Q n)
    refine ⟨CommRingCat.of B, φ, N, localPowerQuotient_isArtinian A n, hfin n, ?_⟩
    let e : P n ≃ₗ[R] (ModuleCat.restrictScalars φ).obj N :=
      { toEquiv := Equiv.refl _
        map_add' := fun _ _ => rfl
        map_smul' := fun r x => Subtype.ext (IsScalarTower.algebraMap_smul A r (x : E)).symm }
    exact ⟨e.toModuleIso⟩

/-- A finite direct sum of modules, each a restriction of scalars of a finite module over an
Artinian ring, is the restriction of scalars of a finite module over the product of those
Artinian rings, which is again Artinian. -/
private theorem finite_sum_restrictScalars
    (R : Type u) [CommRing R] {ι : Type u} [Finite ι]
    (M : ι → ModuleCat.{u} R)
    (hM : ∀ i, ∃ (B : CommRingCat.{u}) (φ : R →+* B) (N : ModuleCat.{u} B),
      IsArtinianRing B ∧ Module.Finite B N ∧
        Nonempty (M i ≅ (ModuleCat.restrictScalars φ).obj N)) :
    ∃ (B : CommRingCat.{u}) (φ : R →+* B) (N : ModuleCat.{u} B),
      IsArtinianRing B ∧ Module.Finite B N ∧
        Nonempty (ModuleCat.of R (DirectSum ι fun i => M i) ≅
          (ModuleCat.restrictScalars φ).obj N) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose B φ N hB hN e using hM
  let (i : ι) := hB i
  let (i : ι) := hN i
  let A := ∀ i, B i
  let ψ : R →+* A := RingHom.pi φ
  let L := ModuleCat.of A (∀ i, N i)
  let e₁ := DirectSum.congrLinearEquiv (fun i => (e i).some.toLinearEquiv)
  let e₂ := DirectSum.linearEquivFunOnFintype R ι
    (fun i => (ModuleCat.restrictScalars (φ i)).obj (N i))
  let e₃ : (∀ i, (ModuleCat.restrictScalars (φ i)).obj (N i)) ≃ₗ[R]
      (ModuleCat.restrictScalars ψ).obj L :=
    { toEquiv := Equiv.refl _
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact ⟨CommRingCat.of A, ψ, L, finiteProductArtinian (fun i => B i),
    finitePiModule (fun i => B i) (fun i => N i),
    ⟨(e₁.trans (e₂.trans e₃)).toModuleIso⟩⟩

/-- An injective module over a Noetherian ring is a filtered colimit of modules which are, after
restriction of scalars, finite modules over Artinian rings.  The index category is the preorder
of stages of the filtrations of the indecomposable summands. -/
private theorem injective_module_colimit
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (J : ModuleCat.{u} R) [Injective J] :
    ∃ (I : Type u) (inst : SmallCategory I), letI := inst
      ∃ (_ : IsFiltered I) (D : I ⥤ ModuleCat.{u} R) (c : Cocone D),
        Nonempty (c.pt ≅ J) ∧ Nonempty (IsColimit c) ∧
        ∀ i, ∃ (B : CommRingCat.{u}) (φ : R →+* B) (N : ModuleCat.{u} B),
          IsArtinianRing B ∧ Module.Finite B N ∧
            Nonempty (D.obj i ≅ (ModuleCat.restrictScalars φ).obj N) := by
  classical
  obtain ⟨α, E, e, hinj, hind⟩ := Module.exists_iso_directSum_of_injective R J
  let (a : α) := hinj a
  choose P hmono hex hstage using fun a => indecomposable_filtration R (E a) (hind a)
  let T := StageIndex α
  let : DecidableEq T := Classical.decEq _
  let G (i : T) : Type u := ArtinianStageSubmodule (fun a => E a) P i
  let f : ∀ i j : T, i ≤ j → G i →ₗ[R] G j :=
    fun i j h => Submodule.inclusion
      (artinianStageSubmodule_mono (fun a => E a) P (fun a _ _ h => hmono a h) i j h)
  let : DirectedSystem G (fun {i j} h => f i j h) := by
    constructor <;> intros <;> exact Subtype.ext rfl
  let eL := (filteredStageDirectSumEquiv (fun a => E a) P
    (fun a _ _ h => hmono a h) hex).some
  let : SmallCategory T := Preorder.smallCategory T
  refine ⟨T, Preorder.smallCategory T, inferInstance, ModuleCat.directLimitDiagram G f,
    ModuleCat.directLimitCocone G f, ⟨eL.toModuleIso ≪≫ e.symm⟩,
    ⟨ModuleCat.directLimitIsColimit G f⟩, ?_⟩
  intro i
  obtain ⟨B, φ, N, hB, hN, ⟨eN⟩⟩ := finite_sum_restrictScalars R
    (fun a : {a // a ∈ (i.1 : Set α)} => ModuleCat.of R (P a.val (i.2 a.val)))
    (fun a => hstage a.val (i.2 a.val))
  let eG := LinearEquiv.ofInjective (artinianStageToTotal (fun a => E a) P i)
    (artinianStageToTotal_injective (fun a => E a) P i)
  exact ⟨B, φ, N, hB, hN, ⟨eG.symm.toModuleIso ≪≫ eN⟩⟩

/-- An isomorphism of schemes induces, by direct image, an equivalence between the categories of
quasi-coherent modules on them. -/
private noncomputable def quasicoherentPushforwardIso {X Y : Scheme.{u}}
    (e : X ≅ Y) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory := by
  let QX := SheafOfModules.isQuasicoherent X.ringCatSheaf
  let QY := SheafOfModules.isQuasicoherent Y.ringCatSheaf
  let F := QY.lift (QX.ι ⋙ Scheme.Modules.pushforward e.hom) (fun M => by
    let := M.property
    exact AlgebraicGeometry.pushforward_isQuasicoherent
      e.hom M.obj)
  let G := QX.lift (QY.ι ⋙ Scheme.Modules.pushforward e.inv) (fun M => by
    let := M.property
    exact AlgebraicGeometry.pushforward_isQuasicoherent
      e.inv M.obj)
  let η := (Scheme.Modules.pushforwardComp e.hom e.inv ≪≫
    Scheme.Modules.pushforwardCongr e.hom_inv_id ≪≫ Scheme.Modules.pushforwardId X).symm
  let ε := Scheme.Modules.pushforwardComp e.inv e.hom ≪≫
    Scheme.Modules.pushforwardCongr e.inv_hom_id ≪≫ Scheme.Modules.pushforwardId Y
  exact CategoryTheory.Equivalence.mk F G
    (NatIso.ofComponents (fun M => ObjectProperty.isoMk QX (η.app M.obj))
      fun f => ObjectProperty.hom_ext _ (η.hom.naturality f.hom))
    (NatIso.ofComponents (fun M => ObjectProperty.isoMk QY (ε.app M.obj))
      fun f => ObjectProperty.hom_ext _ (ε.hom.naturality f.hom))

/-- **Stacks Project, Tag 09TI.** An injective quasi-coherent module on a
Noetherian affine scheme is a filtered colimit of pushforwards of coherent
modules from Artinian affine schemes. -/
@[stacks 09TI]
public theorem exists_filtered_colimit_pushforwards_artinian
    (S : Scheme.{u}) [IsAffine S] [IsLocallyNoetherian S]
    (J : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory)
    [Injective J] :
    ∃ (I : Type u) (inst : SmallCategory I),
      letI := inst
      ∃ (_ : IsFiltered I)
        (D : I ⥤ (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory)
        (φ : D ⟶ (Functor.const I).obj J),
        (∀ i, ∃ (R : CommRingCat.{u}) (hR : IsArtinianRing R),
          letI := hR
          ∃ (f : Spec R ⟶ S) (G : (Spec R).Modules),
            G.IsCoherent ∧
              Nonempty ((D.obj i).obj ≅ (Scheme.Modules.pushforward f).obj G)) ∧
          Nonempty (IsColimit (Cocone.mk J φ)) := by
  classical
  let R := Γ(S, ⊤)
  let eS : Spec R ≅ S := S.isoSpec.symm
  let e := (tildeEquiv (R := R)).trans (quasicoherentPushforwardIso eS)
  have : IsNoetherianRing R :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  let M := e.inverse.obj J
  have : Injective M := e.inverse.injective_obj J
  obtain ⟨I, inst, hf, D, c, ⟨ec⟩, ⟨hc⟩, hD⟩ := injective_module_colimit R M
  let := inst
  let := hf
  let c' := e.functor.mapCocone c
  let ec' : c'.pt ≅ J := e.functor.mapIso ec ≪≫ e.counitIso.app J
  let c'' := c'.extend ec'.hom
  refine ⟨I, inst, hf, D ⋙ e.functor, c''.ι, ?_, ?_⟩
  · intro i
    obtain ⟨B, ψ, N, hB, hN, ⟨eN⟩⟩ := hD i
    let := hB
    let := hN
    let φ : R ⟶ B := CommRingCat.ofHom ψ
    refine ⟨B, hB, Spec.map φ ≫ eS.hom, tilde N,
      AlgebraicGeometry.tilde_isCoherent_of_finite (R := B) N, ?_⟩
    let h := (tilde.functor R).mapIso eN ≪≫
      ((pushforwardTildeIso R B φ).app N).symm
    exact ⟨(Scheme.Modules.pushforward eS.hom).mapIso h ≪≫
      (Scheme.Modules.pushforwardComp (Spec.map φ) eS.hom).app (tilde N)⟩
  · exact ⟨(isColimitOfPreserves e.functor hc).ofIsoColimit (c'.extendIso ec')⟩

end AlgebraicGeometry

end
