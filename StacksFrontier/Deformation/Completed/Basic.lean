module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.RingTheory.CompleteLocalRing.Noetherian
public import StacksFrontier.RingTheory.Flat.CompleteLocal
public import StacksFrontier.RingTheory.Smooth.CotangentAtMaximalIdeal

/-!
# The completed base category

The completed base category `𝒞^_Λ` has as objects the Noetherian complete local
`Λ`-algebras with residue field identified with `k`. This file constructs it and records when a
morphism is surjective, in terms of cotangent spaces and in terms of derivations.

## Main definitions

* `CompleteLocalAlgCat` is the category of Noetherian complete local
  `Λ`-algebras with residue field identified with `k`.
* `CompleteLocalAlgCat.Hom` is its type of compatible local algebra maps.
* `relativeCotangentSpaceOverBase` is
  `m_A / (m_Λ A + m_A²)`, where `m_Λ` is the kernel of the fixed map `Λ → k`.
* `relativeCotangentSpaceMap` is the canonical map on these quotients induced by
  a morphism of complete local algebras.
* `residueAlgHom` is the structural map from a complete local algebra to its
  chosen residue field.
* `ResidueDerivation` is the type of derivations into that residue field.
* `ResidueDerivation.comap` restricts such a derivation along a morphism.

## Main results

* `CompleteLocalAlgCat.residue_comm_iff` identifies the pointwise
  compatibility condition on a morphism with commutativity of the induced triangle on
  residue fields.
* `derivation_module_finite` states that the space of relative derivations into
  the residue field is finite-dimensional for any Noetherian local algebra.
* `surjective_iff_surjective_cotangentSpaceMap` gives the equivalence between
  surjectivity of a morphism and surjectivity on ordinary cotangent spaces.
* `surjective_iff_surjective_relativeCotangentSpaceMap` gives the corresponding
  equivalence for cotangent spaces relative to the fixed base.
* `surjective_of_residueDerivation_comap_injective` says that injectivity of
  restriction on residue-field-valued derivations forces the morphism to be surjective.

## Implementation notes

### Noetherian complete local algebras with fixed residue field

Completeness means completeness for the maximal-ideal-adic topology. Compatibility of a
morphism with the residue-field identifications is recorded after precomposition with the
surjective residue map; this is equivalent to commutativity of the triangle on residue
fields by `CompleteLocalAlgCat.residue_comm_iff`, and makes identities and
composition definitionally direct. The category is defined without Noetherian or finiteness
assumptions on `Λ → k`, since those assumptions are not needed to form it.

### Finiteness of derivations from a Noetherian local algebra

The action of `S` on `k` used in `Derivation Λ S k` is induced by the residue homomorphism.
Finite-dimensionality is expressed by `Module.Finite`. Completeness is not needed for
this finiteness result; Noetherianity of the local source suffices.

### Surjectivity from cotangent spaces

The chapter-wide notation `m_Λ` denotes `ker(Λ → k)`, even though `Λ` need not itself be a
local ring.  Thus the relative cotangent space is written directly as a quotient of `m_A`.
The induced map is constructed on the underlying additive quotients; this is sufficient for
its surjectivity and records its canonical action on representatives.  The two equivalences
together state all three equivalent conditions of the source.

### Surjectivity detected by derivations

The notation `Der_Λ(A, k)` in the source uses the `A`-module structure on `k` induced by
the chosen identification of the residue field of `A` with `k`.  We make that structure
explicit through `residueAlgHom`.  Compatibility of a morphism with the chosen residue
fields makes restriction of derivations well-defined.

## References

* [Stacks Project, Tag 06GW](https://stacks.math.columbia.edu/tag/06GW)
* [Stacks Project, Tag 06GZ](https://stacks.math.columbia.edu/tag/06GZ)
* [Stacks Project, Tag 06SC](https://stacks.math.columbia.edu/tag/06SC)
* [Stacks Project, Tag 06SD](https://stacks.math.columbia.edu/tag/06SD)
-/

@[expose] public section

namespace Deformation

/-! ### Noetherian complete local algebras with fixed residue field -/

section
open CategoryTheory
open IsLocalRing
universe u v w

/-- A Noetherian complete local `Λ`-algebra together with a specified `Λ`-algebra
isomorphism from its residue field to `k`. These are the objects of
`\widehat{\mathcal C}_Λ` in Stacks Project, Tag 06GW. -/
@[stacks 06GW "objects", sga "7 VI 1.15" "objects, K a field"]
structure CompleteLocalAlgCat (Λ : Type u) (k : Type w) [CommRing Λ] [Field k]
    [Algebra Λ k] where
  /-- The underlying type of the algebra. -/
  carrier : Type v
  [commRing : CommRing carrier]
  [algebra : Algebra Λ carrier]
  /-- The underlying ring is Noetherian, local, and complete for its maximal-ideal-adic
  topology. -/
  completeLocal : IsNoetherianCompleteLocalRing carrier
  /-- The chosen identification of the residue field with `k`. -/
  residueEquiv :
    letI : IsLocalRing carrier := completeLocal.isLocal
    ResidueField carrier ≃ₐ[Λ] k

namespace CompleteLocalAlgCat

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

attribute [instance] commRing algebra

instance : CoeSort (CompleteLocalAlgCat.{u, v, w} Λ k) (Type v) := ⟨carrier⟩

attribute [coe] carrier

instance (A : CompleteLocalAlgCat.{u, v, w} Λ k) : IsNoetherianRing A :=
  A.completeLocal.isNoetherian

instance (A : CompleteLocalAlgCat.{u, v, w} Λ k) : IsLocalRing A :=
  A.completeLocal.isLocal

instance (A : CompleteLocalAlgCat.{u, v, w} Λ k) :
    IsAdicComplete (maximalIdeal A) A :=
  A.completeLocal.isComplete

/-- A morphism of Noetherian complete local `Λ`-algebras with fixed residue field is a
local `Λ`-algebra homomorphism whose induced map on residue fields respects the specified
identifications with `k`. -/
@[ext, stacks 06GW "morphisms", sga "7 VI 1.15" "morphisms, K a field"]
structure Hom (A B : CompleteLocalAlgCat.{u, v, w} Λ k) where
  /-- The underlying `Λ`-algebra homomorphism. -/
  hom : A →ₐ[Λ] B
  /-- The underlying ring homomorphism is local. -/
  isLocal : IsLocalHom hom.toRingHom
  /-- Compatibility with the specified identifications of the residue fields. -/
  residue_comm : ∀ a : A,
    B.residueEquiv (residue B (hom a)) = A.residueEquiv (residue A a)

/-- A bundled morphism supplies the locality instance needed to form its induced map on
residue fields. -/
instance {A B : CompleteLocalAlgCat.{u, v, w} Λ k} (f : Hom A B) :
    IsLocalHom f.hom where
  map_nonunit := f.isLocal.map_nonunit

/-- The pointwise compatibility condition used to define morphisms is equivalent to
commutativity of the triangle formed by the induced map on residue fields and the chosen
residue-field identifications. -/
theorem residue_comm_iff {A B : CompleteLocalAlgCat.{u, v, w} Λ k}
    (f : A →ₐ[Λ] B) [IsLocalHom f] :
    (∀ a : A, B.residueEquiv (residue B (f a)) = A.residueEquiv (residue A a)) ↔
      B.residueEquiv.toAlgHom.comp (ResidueField.mapAlgHom f) =
        A.residueEquiv.toAlgHom := by
  refine ⟨?_, fun h a => DFunLike.congr_fun h (residue A a)⟩
  intro h; ext x; obtain ⟨a, rfl⟩ := residue_surjective x; exact h a

/-- The category structure on Noetherian complete local `Λ`-algebras with fixed residue
field. Composition is composition of the underlying local algebra homomorphisms. -/
@[stacks 06GW "category structure"]
instance instCategory : Category (CompleteLocalAlgCat.{u, v, w} Λ k) where
  Hom := Hom
  id A :=
    { hom := AlgHom.id Λ A
      isLocal := isLocalHom_id A
      residue_comm := fun _ ↦ rfl }
  comp f g :=
    { hom := g.hom.comp f.hom
      isLocal := by
        let _ : IsLocalHom f.hom.toRingHom := f.isLocal
        let _ : IsLocalHom g.hom.toRingHom := g.isLocal
        exact RingHom.isLocalHom_comp g.hom.toRingHom f.hom.toRingHom
      residue_comm := fun a ↦ (g.residue_comm (f.hom a)).trans (f.residue_comm a) }
  id_comp := by
    intro A B f
    ext
    rfl
  comp_id := by
    intro A B f
    ext
    rfl
  assoc := by
    intro A B C D f g h
    ext
    rfl

/-- The underlying algebra homomorphism of the identity is the identity. -/
@[simp]
theorem id_hom (A : CompleteLocalAlgCat.{u, v, w} Λ k) :
    (𝟙 A : A ⟶ A).hom = AlgHom.id Λ A := rfl

/-- The underlying algebra homomorphism of a composite is the composite of the underlying
maps. -/
@[simp]
theorem comp_hom {A B C : CompleteLocalAlgCat.{u, v, w} Λ k} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

end CompleteLocalAlgCat

end

/-! ### Finiteness of derivations from a Noetherian local algebra -/

section
open IsLocalRing

universe u v w

/-- **Stacks Project, Tag 06SC.** The `k`-vector space of `Λ`-derivations from a
Noetherian local `Λ`-algebra with residue field `k` to `k` is finite-dimensional. -/
@[stacks 06SC]
theorem derivation_module_finite
    {Λ : Type u} {S : Type v} {k : Type w} [CommRing Λ] [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] [Field k] [Algebra Λ S] [Algebra Λ k]
    [Module.Finite Λ k] (e : ResidueField S ≃ₐ[Λ] k) :
    letI : Algebra S k :=
      (e.toAlgHom.comp (IsScalarTower.toAlgHom Λ S (ResidueField S))).toRingHom.toAlgebra
    Module.Finite k (Derivation Λ S k) := by
  classical
  let : Algebra S k :=
    (e.toAlgHom.comp (IsScalarTower.toAlgHom Λ S (ResidueField S))).toRingHom.toAlgebra
  obtain ⟨n, x, hx⟩ :=
    (Submodule.fg_iff_exists_fin_generating_family).mp
      (maximalIdeal S).fg_of_isNoetherianRing
  obtain ⟨m, y₀, hy₀⟩ := Module.Finite.exists_fin (R := Λ) (M := k)
  let y : Fin m → S := fun j => Classical.choose (IsLocalRing.residue_surjective (e.symm (y₀ j)))
  have hy : ∀ j, e (residue S (y j)) = y₀ j := by
    intro j
    dsimp [y]
    rw [Classical.choose_spec (IsLocalRing.residue_surjective (e.symm (y₀ j)))]
    exact e.apply_symm_apply _
  have hkill (D : Derivation Λ S k) (hDx : ∀ i, D (x i) = 0)
      (hDy : ∀ j, D (y j) = 0) : D = 0 := by
    have hspanKill : ∀ z : S, z ∈ Submodule.span S (Set.range x) → D z = 0 := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hmem =>
          obtain ⟨i, rfl⟩ := Set.mem_range.mp hmem
          exact hDx i
      | zero => simp
      | add z₁ z₂ hz₁ hz₂ ih₁ ih₂ => simp [ih₁, ih₂]
      | smul c z hz ih =>
          have hzm : z ∈ maximalIdeal S := by rw [← hx]; exact hz
          have hres : algebraMap S k z = 0 := by
            change e (residue S z) = 0
            simp [(residue_eq_zero_iff z).2 hzm]
          change D (c * z) = 0
          simp [Derivation.leibniz, ih, Algebra.smul_def, hres]
    have hmax : ∀ z : S, z ∈ maximalIdeal S → D z = 0 := by
      intro z hz; exact hspanKill z (by rw [hx]; exact hz)
    have hlift : ∀ z ∈ Submodule.span Λ (Set.range y₀),
        ∃ p : S, e (residue S p) = z ∧ D p = 0 := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
          obtain ⟨j, rfl⟩ := Set.mem_range.mp hz
          exact ⟨y j, hy j, hDy j⟩
      | zero => exact ⟨0, by simp, by simp⟩
      | add z₁ z₂ hz₁ hz₂ ih₁ ih₂ =>
          obtain ⟨p₁, hp₁, hD₁⟩ := ih₁
          obtain ⟨p₂, hp₂, hD₂⟩ := ih₂
          exact ⟨p₁ + p₂, by simp [hp₁, hp₂], by simp [hD₁, hD₂]⟩
      | smul c z hz ih =>
          obtain ⟨p, hp, hD⟩ := ih
          refine ⟨algebraMap Λ S c * p, ?_, ?_⟩
          · change e (residue S (algebraMap Λ S c * p)) = c • z
            have hbase : e (residue S (algebraMap Λ S c)) = algebraMap Λ k c := by
              change (e.toAlgHom.comp (IsScalarTower.toAlgHom Λ S (ResidueField S)))
                (algebraMap Λ S c) = algebraMap Λ k c
              exact (e.toAlgHom.comp (IsScalarTower.toAlgHom Λ S (ResidueField S))).commutes c
            calc
              e (residue S (algebraMap Λ S c * p)) =
                  e (residue S (algebraMap Λ S c)) * e (residue S p) := by simp
              _ = (algebraMap Λ k c) * z := by rw [hbase, hp]
              _ = c • z := by simp [Algebra.smul_def]
          · simp [Derivation.leibniz, Derivation.map_algebraMap, hD]
    -- For each element, first lift its residue by a polynomial in the chosen residue generators.
    ext a
    have ha : e (residue S a) ∈ Submodule.span Λ (Set.range y₀) := by simp [hy₀]
    obtain ⟨p, hp, hDp⟩ := hlift (e (residue S a)) ha
    have hres : residue S (a - p) = 0 := by
      apply e.injective
      simpa only [map_zero, map_sub, sub_eq_zero] using hp.symm
    have hdiff : a - p ∈ maximalIdeal S := (residue_eq_zero_iff (a - p)).mp hres
    have hsum : p + (a - p) = a := by abel
    rw [← hsum, map_add, hDp, hmax _ hdiff, add_zero]
    simp
  let eval : Derivation Λ S k →ₗ[k] ((Fin n → k) × (Fin m → k)) :=
    { toFun := fun D => (fun i => D (x i), fun j => D (y j))
      map_add' := by intro D E; ext <;> simp
      map_smul' := by intro c D; ext <;> simp [Derivation.smul_apply] }
  have heval : Function.Injective eval := by
    intro D E h
    have h' : eval (D - E) = 0 := by rw [map_sub, h, sub_self]
    apply sub_eq_zero.mp
    apply hkill (D - E)
    · intro i
      have hi := congrFun (congrArg Prod.fst h') i
      simpa [eval] using hi
    · intro j
      have hj := congrFun (congrArg Prod.snd h') j
      simpa [eval] using hj
  exact Module.Finite.of_injective eval heval

end

/-! ### Surjectivity from cotangent spaces -/

section
open CategoryTheory
open IsLocalRing
universe u v w

open CompleteLocalAlgCat

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The submodule `m_Λ A + m_A²` of `m_A`, where the distinguished ideal `m_Λ` is
`ker(Λ → k)`. -/
abbrev relativeCotangentSubmodule
    (A : CompleteLocalAlgCat.{u, v, w} Λ k) : Submodule A (maximalIdeal A) :=
  Submodule.comap (maximalIdeal A).subtype
    ((RingHom.ker (algebraMap Λ k)).map (algebraMap Λ A) + maximalIdeal A ^ 2 : Ideal A)

/-- For a complete local `Λ`-algebra `A` with residue field `k`, the relative cotangent
space `m_A / (m_Λ A + m_A²)`, where `m_Λ = ker(Λ → k)`. -/
abbrev relativeCotangentSpaceOverBase
    (A : CompleteLocalAlgCat.{u, v, w} Λ k) : Type v :=
  maximalIdeal A ⧸ relativeCotangentSubmodule A

/-- The additive map between maximal ideals induced by a morphism of complete local
algebras. -/
def maximalIdealMap {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S) :
    maximalIdeal R →+ maximalIdeal S where
  toFun x := ⟨f.hom x, by
    let _ : IsLocalHom f.hom.toRingHom := f.isLocal
    change (x : R) ∈ (maximalIdeal S).comap f.hom.toRingHom
    simpa only [maximalIdeal_comap] using x.2⟩
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' := by
    intro x y
    apply Subtype.ext
    simp

/-- The canonical map
`m_R / (m_Λ R + m_R²) → m_S / (m_Λ S + m_S²)` induced by a morphism `R ⟶ S`. -/
def relativeCotangentSpaceMap
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S) :
    relativeCotangentSpaceOverBase R →+ relativeCotangentSpaceOverBase S := by
  apply QuotientAddGroup.map _ _ (maximalIdealMap f)
  let _ : IsLocalHom f.hom.toRingHom := f.isLocal
  intro x hx
  change f.hom x ∈ (RingHom.ker (algebraMap Λ k)).map (algebraMap Λ S) +
    maximalIdeal S ^ 2
  change (x : R) ∈ (RingHom.ker (algebraMap Λ k)).map (algebraMap Λ R) +
    maximalIdeal R ^ 2 at hx
  have h : (RingHom.ker (algebraMap Λ k)).map (algebraMap Λ R) +
      maximalIdeal R ^ 2 ≤
      ((RingHom.ker (algebraMap Λ k)).map (algebraMap Λ S) +
        maximalIdeal S ^ 2).comap f.hom.toRingHom := by
    rw [← Ideal.map_le_iff_le_comap]
    change (((RingHom.ker (algebraMap Λ k)).map (algebraMap Λ R) ⊔
      maximalIdeal R ^ 2).map f.hom.toRingHom) ≤
        (RingHom.ker (algebraMap Λ k)).map (algebraMap Λ S) ⊔ maximalIdeal S ^ 2
    rw [Ideal.map_sup]
    apply add_le_add
    · rw [Ideal.map_map]
      have hfcomp : f.hom.toRingHom.comp (algebraMap Λ R) = algebraMap Λ S := by
        ext a
        exact f.hom.commutes a
      rw [hfcomp]
    · rw [Ideal.map_pow]
      exact pow_le_pow_left' (map_maximalIdeal_le f.hom.toRingHom) 2
  exact h hx

private lemma surjective_residue {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S) :
    Function.Surjective ((residue S).comp f.hom.toRingHom) := by
  intro y
  obtain ⟨x, hx⟩ := R.residueEquiv.surjective (S.residueEquiv y)
  obtain ⟨a, ha⟩ := residue_surjective x
  refine ⟨a, S.residueEquiv.injective ?_⟩
  calc
    S.residueEquiv (residue S (f.hom a)) = R.residueEquiv (residue R a) := f.residue_comm a
    _ = S.residueEquiv y := by rw [ha]; exact hx

private lemma preimage_mem_maximalIdeal {R S : CompleteLocalAlgCat.{u, v, w} Λ k}
    (f : R ⟶ S) {r : R} (hr : f.hom r ∈ maximalIdeal S) : r ∈ maximalIdeal R := by
  let _ : IsLocalHom f.hom.toRingHom := f.isLocal
  rw [← maximalIdeal_comap f.hom.toRingHom]
  exact hr

/-- A morphism is surjective once the image of `m_R` generates `m_S`. -/
private lemma surjective_of_maximalIdeal_le_map {R S : CompleteLocalAlgCat.{u, v, w} Λ k}
    (f : R ⟶ S) (h : maximalIdeal S ≤ Ideal.map f.hom.toRingHom (maximalIdeal R)) :
    Function.Surjective f.hom := by
  let _ : IsLocalHom f.hom.toRingHom := f.isLocal
  have hmap : Ideal.map f.hom.toRingHom (maximalIdeal R) = maximalIdeal S :=
    le_antisymm (map_maximalIdeal_le _) h
  have hquot : Function.Surjective
      ((Ideal.Quotient.mk (Ideal.map f.hom.toRingHom (maximalIdeal R))).comp f.hom.toRingHom) := by
    rw [hmap]
    exact surjective_residue f
  have : IsHausdorff (Ideal.map f.hom.toRingHom (maximalIdeal R)) S := hmap.symm ▸ inferInstance
  exact surjective_of_mk_map_comp_surjective (I := maximalIdeal R) f.hom.toRingHom hquot

/-- A morphism is surjective if `m_S ≤ m_R S + m_S²`, by Nakayama. -/
private lemma surjective_of_maximalIdeal_le_map_add_sq {R S : CompleteLocalAlgCat.{u, v, w} Λ k}
    (f : R ⟶ S)
    (h : maximalIdeal S ≤ Ideal.map f.hom.toRingHom (maximalIdeal R) + maximalIdeal S ^ 2) :
    Function.Surjective f.hom := by
  refine surjective_of_maximalIdeal_le_map f ?_
  apply Submodule.le_of_le_smul_of_le_jacobson_bot
    (IsNoetherian.noetherian _) (IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top).ge
  simpa only [Ideal.add_eq_sup, Ideal.smul_eq_mul, pow_two] using h

private lemma surjective_of_cotangent {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S)
    (h : Function.Surjective
      (Ideal.mapCotangent (maximalIdeal R) (maximalIdeal S) f.hom
        (by
          let _ : IsLocalHom f.hom.toRingHom := f.isLocal
          intro x hx
          change x ∈ (maximalIdeal S).comap f.hom.toRingHom
          simpa only [maximalIdeal_comap] using hx))) :
    Function.Surjective f.hom := by
  let mR := maximalIdeal R
  let mS := maximalIdeal S
  let s : Set mS := Set.range (fun x : mR =>
    (⟨f.hom x, by
      let _ : IsLocalHom f.hom.toRingHom := f.isLocal
      change (x : R) ∈ (maximalIdeal S).comap f.hom.toRingHom
      simpa only [maximalIdeal_comap] using x.2⟩ : mS))
  have hspan : Submodule.span S s = ⊤ := by
    apply CotangentSpace.span_image_eq_top_iff.mp
    apply top_unique
    intro y _
    obtain ⟨x, rfl⟩ := h y
    obtain ⟨z, rfl⟩ := mR.toCotangent_surjective x
    exact Submodule.subset_span ⟨_, ⟨z, rfl⟩, by
      change (maximalIdeal S).toCotangent ⟨f.hom z, _⟩ =
        (Ideal.mapCotangent (maximalIdeal R) (maximalIdeal S) f.hom _)
          ((maximalIdeal R).toCotangent z)
      convert (Ideal.mapCotangent_toCotangent
        (maximalIdeal R) (maximalIdeal S) f.hom _ z).symm using 1
      let _ : IsLocalHom f.hom.toRingHom := f.isLocal
      intro x hx; change x ∈ (maximalIdeal S).comap f.hom.toRingHom
      simpa only [maximalIdeal_comap] using hx⟩
  have hmap_ge : mS ≤ Ideal.map f.hom.toRingHom mR := by
    intro x hx
    let M : Submodule S mS :=
      Submodule.comap mS.subtype ((Ideal.map f.hom.toRingHom mR : Ideal S) : Submodule S S)
    have hs_le : Submodule.span S s ≤ M :=
      Submodule.span_le.mpr (by rintro y ⟨z, rfl⟩; exact Ideal.mem_map_of_mem f.hom.toRingHom z.2)
    have htop : M = ⊤ := top_unique (hspan ▸ hs_le)
    exact (htop.symm ▸ Submodule.mem_top : (⟨x, hx⟩ : mS) ∈ M)
  exact surjective_of_maximalIdeal_le_map f hmap_ge

private lemma baseIdeal_le_map_maximalIdeal
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S) :
    (RingHom.ker (algebraMap Λ k)).map (algebraMap Λ S) ≤
      Ideal.map f.hom.toRingHom (maximalIdeal R) := by
  have hbaseR : (RingHom.ker (algebraMap Λ k)).map (algebraMap Λ R) ≤
      maximalIdeal R := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha; change algebraMap Λ R a ∈ maximalIdeal R
    rw [← residue_eq_zero_iff]
    apply R.residueEquiv.injective
    simp only [map_zero]
    calc
      R.residueEquiv (residue R (algebraMap Λ R a)) =
          R.residueEquiv (algebraMap Λ (ResidueField R) a) := by
        congr 1
      _ = algebraMap Λ k a := R.residueEquiv.commutes a
      _ = 0 := ha
  have hcomp : f.hom.toRingHom.comp (algebraMap Λ R) = algebraMap Λ S := by
    ext a; exact f.hom.commutes a
  rw [← hcomp, ← Ideal.map_map]
  exact Ideal.map_mono hbaseR

private lemma surjective_of_relativeCotangent
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S)
    (h : Function.Surjective (relativeCotangentSpaceMap f)) :
    Function.Surjective f.hom := by
  let mR := maximalIdeal R
  let mS := maximalIdeal S
  let I := Ideal.map f.hom.toRingHom mR
  have hsub : (RingHom.ker (algebraMap Λ k)).map (algebraMap Λ S) + mS ^ 2 ≤
      I + mS ^ 2 := add_le_add (baseIdeal_le_map_maximalIdeal f) le_rfl
  have hrel : mS ≤ I + mS ^ 2 := by
    intro y hy
    let yy : mS := ⟨y, hy⟩
    obtain ⟨q, hq⟩ := h (Submodule.Quotient.mk yy)
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have heq : (Submodule.Quotient.mk yy : relativeCotangentSpaceOverBase S) =
        Submodule.Quotient.mk (maximalIdealMap f x) := hq.symm
    have hd : (y - f.hom x : S) ∈
        (RingHom.ker (algebraMap Λ k)).map (algebraMap Λ S) + mS ^ 2 :=
      (Submodule.Quotient.eq (relativeCotangentSubmodule S)).mp heq
    have hfx : f.hom x ∈ I := Ideal.mem_map_of_mem f.hom.toRingHom x.2
    have hy' := (I + mS ^ 2).add_mem (hsub hd)
      ((show I ≤ I + mS ^ 2 from le_sup_left) hfx)
    convert hy' using 1; ring
  exact surjective_of_maximalIdeal_le_map_add_sq f hrel

/-- A morphism of Noetherian complete local algebras is surjective if and only if its
canonical map `m_R / m_R² → m_S / m_S²` is surjective. -/
@[stacks 06GZ "conditions (1) and (2)"]
theorem surjective_iff_surjective_cotangentSpaceMap
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S) :
    Function.Surjective f.hom ↔
      Function.Surjective
        (Ideal.mapCotangent (maximalIdeal R) (maximalIdeal S) f.hom
          (by
            let _ : IsLocalHom f.hom.toRingHom := f.isLocal
            intro x hx
            change x ∈ (maximalIdeal S).comap f.hom.toRingHom
            simpa only [maximalIdeal_comap] using hx)) := by
  constructor
  · intro hf y
    obtain ⟨x, rfl⟩ := (maximalIdeal S).toCotangent_surjective y
    obtain ⟨r, hr⟩ := hf x
    have hmr : r ∈ maximalIdeal R := preimage_mem_maximalIdeal f (hr ▸ x.2)
    exact ⟨(maximalIdeal R).toCotangent ⟨r, hmr⟩, by
      simp only [Ideal.mapCotangent_toCotangent, hr]⟩
  · exact surjective_of_cotangent f

/-- A morphism of Noetherian complete local algebras is surjective if and only if its map
`m_R / (m_Λ R + m_R²) → m_S / (m_Λ S + m_S²)` is surjective. -/
@[stacks 06GZ "conditions (1) and (3)"]
theorem surjective_iff_surjective_relativeCotangentSpaceMap
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S) :
    Function.Surjective f.hom ↔ Function.Surjective (relativeCotangentSpaceMap f) :=
  by
    constructor
    · intro hf y
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨r, hr⟩ := hf x
      have hmr : r ∈ maximalIdeal R := preimage_mem_maximalIdeal f (hr ▸ x.2)
      exact ⟨Submodule.Quotient.mk (⟨r, hmr⟩ : maximalIdeal R), by
        change (Submodule.Quotient.mk (maximalIdealMap f ⟨r, hmr⟩) :
          relativeCotangentSpaceOverBase S) = Submodule.Quotient.mk x
        congr 1
        exact Subtype.ext hr⟩
    · exact surjective_of_relativeCotangent f

end

/-! ### Surjectivity detected by derivations -/

section
open CategoryTheory IsLocalRing
universe u v w

open CompleteLocalAlgCat

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]




private def obstructionIdeal {R S : CompleteLocalAlgCat.{u, v, w} Λ k}
    (f : R ⟶ S) : Ideal S :=
  Ideal.map f.hom.toRingHom (maximalIdeal R) + maximalIdeal S ^ 2

private theorem obstructionIdeal_le_maximalIdeal
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S) :
    obstructionIdeal f ≤ maximalIdeal S := by
  let _ : IsLocalHom f.hom.toRingHom := f.isLocal
  apply sup_le
  · exact map_maximalIdeal_le f.hom.toRingHom
  · exact Ideal.pow_le_self (by omega)

/-- The structural map from a complete local algebra with chosen residue field to that
residue field. -/
public noncomputable def residueAlgHom (A : CompleteLocalAlgCat.{u, v, w} Λ k) : A →ₐ[Λ] k :=
  A.residueEquiv.toAlgHom.comp (Ideal.Quotient.mkₐ Λ (maximalIdeal A))

@[simp]
public theorem residueAlgHom_apply (A : CompleteLocalAlgCat.{u, v, w} Λ k) (x : A) :
    residueAlgHom A x = A.residueEquiv (residue A x) := rfl

public theorem residueAlgHom_ker (A : CompleteLocalAlgCat.{u, v, w} Λ k) :
    RingHom.ker (residueAlgHom A).toRingHom = maximalIdeal A := by
  ext x
  simp [RingHom.mem_ker, residueAlgHom_apply, residue_eq_zero_iff]

public theorem residueAlgHom_surjective (A : CompleteLocalAlgCat.{u, v, w} Λ k) :
    Function.Surjective (residueAlgHom A) := by
  intro y
  obtain ⟨x, hx⟩ := A.residueEquiv.surjective y
  obtain ⟨a, ha⟩ := residue_surjective x
  exact ⟨a, by simp [residueAlgHom_apply, ha, hx]⟩

/-- Derivations from a complete local algebra into its chosen residue field.  The module
structure on the target is induced by the residue map. -/
public abbrev ResidueDerivation (A : CompleteLocalAlgCat.{u, v, w} Λ k) :=
  letI : Algebra A k := (residueAlgHom A).toRingHom.toAlgebra
  Derivation Λ A k

namespace ResidueDerivation

/-- Restriction of a residue-field-valued derivation along a morphism of complete local
algebras with fixed residue field. -/
public noncomputable def comap {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S) :
    ResidueDerivation S → ResidueDerivation R := by
  letI : Algebra S k := (residueAlgHom S).toRingHom.toAlgebra
  letI : Algebra R k := (residueAlgHom R).toRingHom.toAlgebra
  intro D
  refine
    { toLinearMap :=
        { toFun := fun x ↦ D (f.hom x)
          map_add' := fun x y ↦ by simp
          map_smul' := fun r x ↦ by simp }
      map_one_eq_zero' := by simp
      leibniz' := fun x y ↦ ?_ }
  change D (f.hom (x * y)) = _
  calc
    D (f.hom (x * y)) = D (f.hom x * f.hom y) :=
      congrArg D (f.hom.map_mul x y)
    _ = f.hom x • D (f.hom y) + f.hom y • D (f.hom x) := D.leibniz _ _
    _ = x • D (f.hom y) + y • D (f.hom x) := by
      change residueAlgHom S (f.hom x) * D (f.hom y) +
          residueAlgHom S (f.hom y) * D (f.hom x) =
        residueAlgHom R x * D (f.hom y) + residueAlgHom R y * D (f.hom x)
      rw [residueAlgHom_apply, residueAlgHom_apply, residueAlgHom_apply,
        residueAlgHom_apply]
      rw [f.residue_comm x, f.residue_comm y]

@[simp]
public theorem comap_apply {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S)
    (D : ResidueDerivation S) (x : R) : comap f D x = D (f.hom x) := by
  simp [comap]

end ResidueDerivation

/-- A morphism of Noetherian complete local algebras with fixed residue field is
surjective if restriction of residue-field-valued derivations along it is injective. -/
@[stacks 06SD]
public theorem surjective_of_residueDerivation_comap_injective
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S)
    (h : Function.Injective (ResidueDerivation.comap f)) :
    Function.Surjective f.hom := by
  classical
  by_contra hnot
  let J := obstructionIdeal f
  let T := S ⧸ J
  let q : S →ₐ[Λ] T := Ideal.Quotient.mkₐ Λ J
  have hJker : RingHom.ker q.toRingHom ≤ RingHom.ker (residueAlgHom S).toRingHom := by
    calc
      RingHom.ker q.toRingHom = J := by exact Ideal.mk_ker
      _ ≤ maximalIdeal S := obstructionIdeal_le_maximalIdeal f
      _ = RingHom.ker (residueAlgHom S).toRingHom := (residueAlgHom_ker S).symm
  let rho : T →ₐ[Λ] k :=
    AlgHom.liftOfSurjective q Ideal.Quotient.mk_surjective (residueAlgHom S) hJker
  have hrho_comp : rho.comp q = residueAlgHom S :=
    AlgHom.liftOfSurjective_comp q Ideal.Quotient.mk_surjective
      (residueAlgHom S) hJker
  have hrho_surj : Function.Surjective rho := by
    intro y
    obtain ⟨s, hs⟩ := residueAlgHom_surjective S y
    refine ⟨q s, ?_⟩
    change (rho.comp q) s = y
    rw [hrho_comp]
    exact hs
  let I : Ideal T := RingHom.ker rho.toRingHom
  have hIeq : I = Ideal.map q.toRingHom (maximalIdeal S) := by
    rw [← Ideal.map_comap_of_surjective q.toRingHom Ideal.Quotient.mk_surjective I]
    congr 1
    ext s
    change rho (q s) = 0 ↔ s ∈ maximalIdeal S
    rw [show rho (q s) = residueAlgHom S s from congrArg (fun g : S →ₐ[Λ] k => g s) hrho_comp]
    rw [← residueAlgHom_ker]
    rfl
  have hI2 : I ^ 2 = ⊥ := by
    rw [hIeq, ← Ideal.map_pow]
    apply (Ideal.map_eq_bot_iff_le_ker q.toRingHom).mpr
    intro x hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((le_sup_right : maximalIdeal S ^ 2 ≤ J) hx)
  let g : R →ₐ[Λ] T := q.comp f.hom
  have hgker : RingHom.ker (residueAlgHom R).toRingHom ≤ RingHom.ker g.toRingHom := by
    rw [residueAlgHom_ker]
    intro x hx
    change q (f.hom x) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change f.hom x ∈ J
    exact (le_sup_left : Ideal.map f.hom.toRingHom (maximalIdeal R) ≤ J)
      (Ideal.mem_map_of_mem f.hom.toRingHom hx)
  let sigma : k →ₐ[Λ] T :=
    AlgHom.liftOfSurjective (residueAlgHom R) (residueAlgHom_surjective R) g hgker
  have hsigma_comp : sigma.comp (residueAlgHom R) = g :=
    AlgHom.liftOfSurjective_comp (residueAlgHom R) (residueAlgHom_surjective R) g hgker
  have hrhosigma : rho.comp sigma = AlgHom.id Λ k := by
    ext c
    obtain ⟨r, hr⟩ := residueAlgHom_surjective R c
    rw [← hr]
    change rho (sigma (residueAlgHom R r)) = residueAlgHom R r
    rw [show sigma (residueAlgHom R r) = q (f.hom r) by
      change (sigma.comp (residueAlgHom R)) r = _
      rw [hsigma_comp]
      rfl]
    change (rho.comp q) (f.hom r) = _
    rw [hrho_comp]
    simp [residueAlgHom_apply, f.residue_comm r]
  let : Algebra k T := sigma.toRingHom.toAlgebra
  let : IsScalarTower Λ k T := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (sigma.commutes a).symm)
  have hI_nontrivial : ¬ Subsingleton I.Cotangent := by
    intro hsub
    have hidem := (Ideal.cotangent_subsingleton_iff (I := I)).mp hsub
    have hzero : I = ⊥ := by
      have hidem' : I ^ 2 = I := by simpa [IsIdempotentElem, pow_two] using hidem
      rw [hI2] at hidem'
      exact hidem'.symm
    apply hnot
    exact surjective_of_maximalIdeal_le_map_add_sq f (by
      intro x hx
      have hxI : q x ∈ I := by
        rw [hIeq]
        exact Ideal.mem_map_of_mem q.toRingHom hx
      have hxq : q x = 0 := by simpa [hzero] using hxI
      exact (Ideal.Quotient.eq_zero_iff_mem).mp hxq)
  let : Nontrivial I.Cotangent := not_subsingleton_iff_nontrivial.mp hI_nontrivial
  let K := T ⧸ I
  let : I.IsMaximal := RingHom.ker_isMaximal_of_surjective rho.toRingHom hrho_surj
  let : CommRing K := Ideal.Quotient.commRing I
  let e : K ≃ₐ[Λ] k := Ideal.quotientKerAlgEquivOfSurjective hrho_surj
  have he_apply (t : T) : e (Ideal.Quotient.mk I t) = rho t := by
    exact Ideal.quotientKerAlgEquivOfSurjective_mk (f := rho) hrho_surj t
  let : Algebra k K := ((Ideal.Quotient.mk I).comp sigma.toRingHom).toAlgebra
  let : IsScalarTower k T K := IsScalarTower.of_algebraMap_eq' rfl
  let eK : K ≃ₐ[k] k :=
    { toRingEquiv := e.toRingEquiv
      commutes' := by
        intro c
        change e ((Ideal.Quotient.mk I) (sigma c)) = c
        rw [he_apply]
        exact DFunLike.congr_fun hrhosigma c }
  let sigmaK : k →ₐ[k] T := Algebra.ofId k T
  let sigmaI : K →ₐ[k] T := sigmaK.comp eK.toAlgHom
  have hsigmaI : ∀ c, Ideal.Quotient.mk I (sigmaI c) = c := by
    intro c
    apply e.injective
    have hval : rho (sigma (eK c)) = eK c := by
      have := congrArg (fun F : k →ₐ[Λ] k => F (eK c)) hrhosigma
      simpa using this
    calc
      e (Ideal.Quotient.mk I (sigmaI c)) = rho (sigma (eK c)) := by
        change e (Ideal.Quotient.mk I (sigmaK (eK c))) = _
        rw [he_apply]
        change rho (sigma (eK c)) = _
        rfl
      _ = eK c := hval
      _ = e c := rfl
  let Dsection : Derivation k T I.Cotangent :=
    cotangentDerivationOfSection (k := k) (S := T) (I := I) sigmaI hsigmaI
  have hDsection_apply (t : T) :
      Dsection t = I.toCotangent ⟨t - sigmaI (Ideal.Quotient.mk I t),
        sub_quotientSection_mem sigmaI hsigmaI t⟩ := by
    exact cotangentDerivationOfSection_apply (k := k) (S := T) sigmaI hsigmaI t
  let : Field K := Ideal.Quotient.field I
  let : Nontrivial (I.Cotangent →ₗ[K] K) := (Module.nontrivial_dual_iff K).mpr inferInstance
  let hlinK : ∃ ℓ : I.Cotangent →ₗ[K] K, ℓ ≠ 0 := exists_ne 0
  let ellK := Classical.choose hlinK
  have hellK : ellK ≠ 0 := Classical.choose_spec hlinK
  let : Algebra T k := rho.toRingHom.toAlgebra
  let eT : K →ₗ[T] k := {
    toFun := eK
    map_add' := fun x y => map_add eK x y
    map_smul' := by
      intro t x
      change eK ((Ideal.Quotient.mk I t) * x) = rho t * eK x
      have ht : eK (Ideal.Quotient.mk I t) = rho t := he_apply t
      rw [map_mul, ht] }
  let ellT : I.Cotangent →ₗ[T] k := eT.comp (ellK.restrictScalars T)
  have hlinK_exists : ∃ z : I, ellK (I.toCotangent z) ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hellK
    ext x
    obtain ⟨z, rfl⟩ := I.toCotangent_surjective x
    exact hn z
  let z := Classical.choose hlinK_exists
  have hz : ellK (I.toCotangent z) ≠ 0 := Classical.choose_spec hlinK_exists
  have hellT : ellT (I.toCotangent z) ≠ 0 := by
    simp only [ellT, LinearMap.comp_apply, eT]
    exact fun heq => hz (eK.injective (by simpa using heq))
  let D : Derivation Λ T k :=
    (ellT.compDer (Dsection.restrictScalars Λ))
  let : Algebra S T := q.toRingHom.toAlgebra
  let : IsScalarTower Λ S T := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (q.commutes a).symm)
  let : Algebra S k := (residueAlgHom S).toRingHom.toAlgebra
  let : Algebra R k := (residueAlgHom R).toRingHom.toAlgebra
  let hSTk : IsScalarTower S T k := IsScalarTower.of_algebraMap_eq' (by
    ext s
    exact (DFunLike.congr_fun hrho_comp s).symm)
  let : IsScalarTower Λ T k := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (rho.commutes a).symm)
  let d : ResidueDerivation S := @Derivation.compAlgebraMap Λ S T k
    (inferInstance : CommSemiring Λ) (inferInstance : CommSemiring S)
    (inferInstance : CommSemiring T) (inferInstance : AddCommMonoid k)
    (inferInstance : Algebra Λ S) (inferInstance : Algebra Λ T)
    (inferInstance : Module S k) (inferInstance : Module T k)
    (inferInstance : Module Λ k) (inferInstance : Algebra S T)
    (inferInstance : IsScalarTower Λ S T) hSTk D
  have hcomap : ResidueDerivation.comap f d = 0 := by
    ext r
    change ellT (Dsection (Ideal.Quotient.mk J (f.hom r))) = 0
    rw [show Ideal.Quotient.mk J (f.hom r) = sigma (residueAlgHom R r) by
      change (q.comp f.hom) r = (sigma.comp (residueAlgHom R)) r
      rw [hsigma_comp]]
    change ellT (Dsection (algebraMap k T (residueAlgHom R r))) = 0
    simp [Dsection, Derivation.map_algebraMap]
  have hzD : Dsection (z : T) = I.toCotangent z := by
    rw [hDsection_apply]
    congr 1
    apply Subtype.ext
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr z.property]
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (z : T)
  have hdval : d s = ellT (I.toCotangent z) := by
    change D (q s) = _
    rw [show q s = Ideal.Quotient.mk J s by rfl, hs]
    change ellT (Dsection (z : T)) = _
    rw [hzD]
  have hdne : d ≠ 0 := by
    intro hz
    have hval := congrArg (fun d : Derivation Λ S k => d s) hz
    exact hellT (by simpa [hdval] using hval)
  have hd0 : d = 0 := h (by
    rw [hcomap]
    apply Derivation.ext
    intro r
    rfl)
  exact hdne hd0

end

end Deformation
